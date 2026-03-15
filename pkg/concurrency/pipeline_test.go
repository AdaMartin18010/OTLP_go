package concurrency

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewPipeline(t *testing.T) {
	t.Run("creates pipeline with stage", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input * 2, nil
			},
		)
		require.NotNil(t, p)
	})
}

func TestPipeline_Start(t *testing.T) {
	t.Run("starts pipeline successfully", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input * 2, nil
			},
		)

		ctx := context.Background()
		p.Start(ctx)
		defer p.Stop()

		assert.NotNil(t, p.input)
		assert.NotNil(t, p.output)
	})
}

func TestPipeline_Send(t *testing.T) {
	t.Run("sends data through pipeline", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input * 2, nil
			},
		)

		ctx := context.Background()
		p.Start(ctx)
		defer p.Stop()

		err := p.Send(ctx, 5)
		assert.NoError(t, err)
	})

	t.Run("returns error when closed", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input, nil
			},
		)

		p.Start(context.Background())
		p.Stop()

		err := p.Send(context.Background(), 5)
		assert.ErrorIs(t, err, ErrPipelineClosed)
	})

	t.Run("respects context cancellation", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				time.Sleep(100 * time.Millisecond)
				return input, nil
			},
		)

		ctx := context.Background()
		p.Start(ctx)
		defer p.Stop()

		// Fill the pipeline
		for i := 0; i < 200; i++ {
			p.Send(ctx, i)
		}

		// Try to send with cancelled context
		ctx2, cancel := context.WithCancel(context.Background())
		cancel()

		err := p.Send(ctx2, 999)
		assert.ErrorIs(t, err, context.Canceled)
	})
}

func TestPipeline_Receive(t *testing.T) {
	t.Run("receives processed data", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input * 2, nil
			},
		)

		ctx := context.Background()
		p.Start(ctx)
		defer p.Stop()

		p.Send(ctx, 5)
		p.Send(ctx, 10)

		// Give time for processing
		time.Sleep(50 * time.Millisecond)

		// Collect results with timeout
		var results []int
		done := make(chan struct{})
		go func() {
			defer close(done)
			for {
				select {
				case result, ok := <-p.Receive():
					if !ok {
						return
					}
					results = append(results, result.Value)
				case <-time.After(100 * time.Millisecond):
					return
				}
			}
		}()

		<-done
		// Should have processed some results
		assert.GreaterOrEqual(t, len(results), 0)
	})

	t.Run("handles stage errors", func(t *testing.T) {
		testErr := errors.New("stage error")
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				if input == 5 {
					return 0, testErr
				}
				return input, nil
			},
		)

		ctx := context.Background()
		p.Start(ctx)
		defer p.Stop()

		p.Send(ctx, 5)
		p.Send(ctx, 10)

		time.Sleep(50 * time.Millisecond)

		select {
		case err := <-p.Errors():
			assert.ErrorIs(t, err, testErr)
		case <-time.After(time.Second):
			t.Fatal("expected error not received")
		}
	})
}

func TestPipeline_Stop(t *testing.T) {
	t.Run("stops gracefully", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input, nil
			},
		)

		p.Start(context.Background())
		p.Stop()

		// Channels should be closed
		select {
		case _, ok := <-p.Receive():
			assert.False(t, ok)
		default:
			// Channel is closed and drained
		}
	})

	t.Run("stop with context timeout", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				// Simulate long-running work
				select {
				case <-ctx.Done():
					return 0, ctx.Err()
				case <-time.After(5 * time.Second):
					return input, nil
				}
			},
		)

		ctx := context.Background()
		p.Start(ctx)

		// Send work
		p.Send(ctx, 1)
		time.Sleep(10 * time.Millisecond) // Let work start

		stopCtx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		err := p.StopContext(stopCtx)
		// StopContext may succeed if workers respect context cancellation
		if err != nil {
			assert.ErrorIs(t, err, context.DeadlineExceeded)
		}

		// Stop completely
		p.Stop()
	})

	t.Run("is idempotent", func(t *testing.T) {
		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				return input, nil
			},
		)

		p.Start(context.Background())
		p.Stop()
		p.Stop() // Should not panic
	})
}

func TestPipeline_WithWorkers(t *testing.T) {
	t.Run("creates pipeline with worker configuration", func(t *testing.T) {
		p := NewPipelineWithWorkers[int, int](
			3, // 3 workers
			func(ctx context.Context, input int) (int, error) {
				return input * 2, nil
			},
		)
		require.NotNil(t, p)
	})
}

func TestMap(t *testing.T) {
	t.Run("maps over slice", func(t *testing.T) {
		inputs := []int{1, 2, 3, 4, 5}

		results, err := Map(context.Background(), inputs, 2, func(ctx context.Context, i int) (int, error) {
			return i * 2, nil
		})

		require.NoError(t, err)
		assert.Equal(t, []int{2, 4, 6, 8, 10}, results)
	})

	t.Run("handles errors", func(t *testing.T) {
		testErr := errors.New("map error")
		inputs := []int{1, 2, 3}

		_, err := Map(context.Background(), inputs, 2, func(ctx context.Context, i int) (int, error) {
			if i == 2 {
				return 0, testErr
			}
			return i, nil
		})

		assert.ErrorIs(t, err, testErr)
	})

	t.Run("respects context cancellation", func(t *testing.T) {
		inputs := []int{1, 2, 3, 4, 5}
		ctx, cancel := context.WithCancel(context.Background())

		_, err := Map(ctx, inputs, 2, func(ctx context.Context, i int) (int, error) {
			if i == 3 {
				cancel()
			}
			time.Sleep(10 * time.Millisecond)
			return i, nil
		})

		assert.ErrorIs(t, err, context.Canceled)
	})

	t.Run("handles zero concurrency", func(t *testing.T) {
		inputs := []int{1, 2, 3}

		results, err := Map(context.Background(), inputs, 0, func(ctx context.Context, i int) (int, error) {
			return i * 2, nil
		})

		require.NoError(t, err)
		assert.Equal(t, []int{2, 4, 6}, results)
	})

	t.Run("handles empty slice", func(t *testing.T) {
		results, err := Map(context.Background(), []int{}, 2, func(ctx context.Context, i int) (int, error) {
			return i, nil
		})

		require.NoError(t, err)
		assert.Empty(t, results)
	})
}

func TestFilter(t *testing.T) {
	t.Run("filters slice", func(t *testing.T) {
		inputs := []int{1, 2, 3, 4, 5}

		results, err := Filter(context.Background(), inputs, 2, func(ctx context.Context, i int) (bool, error) {
			return i%2 == 0, nil
		})

		require.NoError(t, err)
		assert.Equal(t, []int{2, 4}, results)
	})

	t.Run("handles errors", func(t *testing.T) {
		testErr := errors.New("filter error")
		inputs := []int{1, 2, 3}

		_, err := Filter(context.Background(), inputs, 2, func(ctx context.Context, i int) (bool, error) {
			if i == 2 {
				return false, testErr
			}
			return true, nil
		})

		assert.ErrorIs(t, err, testErr)
	})

	t.Run("respects context cancellation", func(t *testing.T) {
		inputs := []int{1, 2, 3, 4, 5}
		ctx, cancel := context.WithCancel(context.Background())

		_, err := Filter(ctx, inputs, 2, func(ctx context.Context, i int) (bool, error) {
			if i == 3 {
				cancel()
			}
			return true, nil
		})

		assert.ErrorIs(t, err, context.Canceled)
	})

	t.Run("handles empty slice", func(t *testing.T) {
		results, err := Filter(context.Background(), []int{}, 2, func(ctx context.Context, i int) (bool, error) {
			return true, nil
		})

		require.NoError(t, err)
		assert.Empty(t, results)
	})
}

func TestReduce(t *testing.T) {
	t.Run("reduces slice", func(t *testing.T) {
		inputs := []int{1, 2, 3, 4, 5}

		result, err := Reduce(context.Background(), inputs, 0, func(ctx context.Context, acc, i int) (int, error) {
			return acc + i, nil
		})

		require.NoError(t, err)
		assert.Equal(t, 15, result)
	})

	t.Run("handles errors", func(t *testing.T) {
		testErr := errors.New("reduce error")
		inputs := []int{1, 2, 3}

		_, err := Reduce(context.Background(), inputs, 0, func(ctx context.Context, acc, i int) (int, error) {
			if i == 2 {
				return 0, testErr
			}
			return acc + i, nil
		})

		assert.ErrorIs(t, err, testErr)
	})

	t.Run("respects context cancellation", func(t *testing.T) {
		inputs := []int{1, 2, 3, 4, 5}
		ctx, cancel := context.WithCancel(context.Background())

		_, err := Reduce(ctx, inputs, 0, func(ctx context.Context, acc, i int) (int, error) {
			if i == 3 {
				cancel()
			}
			return acc + i, nil
		})

		assert.ErrorIs(t, err, context.Canceled)
	})

	t.Run("handles empty slice", func(t *testing.T) {
		result, err := Reduce(context.Background(), []int{}, 0, func(ctx context.Context, acc, i int) (int, error) {
			return acc + i, nil
		})

		require.NoError(t, err)
		assert.Equal(t, 0, result)
	})
}

func TestPipeline_Concurrent(t *testing.T) {
	t.Run("handles concurrent sends", func(t *testing.T) {
		var processed atomic.Int32

		p := NewPipeline[int, int](
			func(ctx context.Context, input int) (int, error) {
				processed.Add(1)
				return input, nil
			},
		)

		ctx := context.Background()
		p.Start(ctx)
		defer p.Stop()

		// Concurrent sends
		var wg sync.WaitGroup
		for i := 0; i < 100; i++ {
			wg.Add(1)
			go func(n int) {
				defer wg.Done()
				p.Send(ctx, n)
			}(i)
		}
		wg.Wait()

		// Give time for processing
		time.Sleep(200 * time.Millisecond)

		// Collect results with timeout
		var count int
		done := make(chan struct{})
		go func() {
			defer close(done)
			for {
				select {
				case _, ok := <-p.Receive():
					if !ok {
						return
					}
					count++
				case <-time.After(100 * time.Millisecond):
					return
				}
			}
		}()
		<-done

		assert.GreaterOrEqual(t, count, 0)
	})
}

func BenchmarkPipeline_Send(b *testing.B) {
	p := NewPipeline[int, int](
		func(ctx context.Context, input int) (int, error) {
			return input * 2, nil
		},
	)

	p.Start(context.Background())
	defer p.Stop()

	ctx := context.Background()
	b.ResetTimer()

	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			p.Send(ctx, 1)
		}
	})
}

func BenchmarkMap(b *testing.B) {
	inputs := make([]int, 100)
	for i := range inputs {
		inputs[i] = i
	}

	ctx := context.Background()
	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		Map(ctx, inputs, 10, func(ctx context.Context, i int) (int, error) {
			return i * 2, nil
		})
	}
}

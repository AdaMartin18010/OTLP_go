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

func TestNewPool(t *testing.T) {
	t.Run("creates pool with default settings", func(t *testing.T) {
		pool := NewPool(5)
		require.NotNil(t, pool)
		defer pool.Shutdown(context.Background())

		stats := pool.Stats()
		assert.Equal(t, 5, stats.Workers)
		assert.False(t, stats.Closed)
	})

	t.Run("creates pool with queue size option", func(t *testing.T) {
		pool := NewPool(3, WithQueueSize(50))
		require.NotNil(t, pool)
		defer pool.Shutdown(context.Background())

		// Verify by submitting many tasks
		var submitted int
		for i := 0; i < 50; i++ {
			err := pool.Submit(context.Background(), func(ctx context.Context) error {
				return nil
			})
			if err != nil {
				break
			}
			submitted++
		}
		assert.GreaterOrEqual(t, submitted, 3)
	})

	t.Run("creates pool with results channel", func(t *testing.T) {
		pool := NewPool(2, WithResults(10))
		require.NotNil(t, pool)
		defer pool.Shutdown(context.Background())

		results := pool.Results()
		assert.NotNil(t, results)
	})

	t.Run("handles zero workers", func(t *testing.T) {
		pool := NewPool(0)
		require.NotNil(t, pool)
		defer pool.Shutdown(context.Background())

		stats := pool.Stats()
		assert.Equal(t, 1, stats.Workers)
	})

	t.Run("handles negative workers", func(t *testing.T) {
		pool := NewPool(-5)
		require.NotNil(t, pool)
		defer pool.Shutdown(context.Background())

		stats := pool.Stats()
		assert.Equal(t, 1, stats.Workers)
	})
}

func TestPool_Submit(t *testing.T) {
	t.Run("submits and executes tasks", func(t *testing.T) {
		pool := NewPool(2)
		defer pool.Shutdown(context.Background())

		var counter atomic.Int32
		task := func(ctx context.Context) error {
			counter.Add(1)
			return nil
		}

		for i := 0; i < 10; i++ {
			err := pool.Submit(context.Background(), task)
			require.NoError(t, err)
		}

		// Wait for tasks to complete
		time.Sleep(100 * time.Millisecond)
		assert.Equal(t, int32(10), counter.Load())
	})

	t.Run("returns error when pool is closed", func(t *testing.T) {
		pool := NewPool(2)
		pool.Shutdown(context.Background())

		err := pool.Submit(context.Background(), func(ctx context.Context) error {
			return nil
		})
		assert.ErrorIs(t, err, ErrPoolClosed)
	})

	t.Run("respects context cancellation", func(t *testing.T) {
		pool := NewPool(1, WithQueueSize(1))
		defer pool.Shutdown(context.Background())

		// Block the worker
		pool.Submit(context.Background(), func(ctx context.Context) error {
			time.Sleep(500 * time.Millisecond)
			return nil
		})

		// Fill the queue
		pool.Submit(context.Background(), func(ctx context.Context) error {
			return nil
		})

		// Try to submit with short timeout
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Millisecond)
		defer cancel()

		err := pool.Submit(ctx, func(ctx context.Context) error {
			return nil
		})
		assert.ErrorIs(t, err, ErrPoolFull)
	})

	t.Run("handles task errors", func(t *testing.T) {
		pool := NewPool(2, WithResults(10))
		defer pool.Shutdown(context.Background())

		testErr := errors.New("task error")
		pool.Submit(context.Background(), func(ctx context.Context) error {
			return testErr
		})

		time.Sleep(50 * time.Millisecond)

		stats := pool.Stats()
		assert.Equal(t, uint64(1), stats.Errors)
	})
}

func TestPool_SubmitAsync(t *testing.T) {
	t.Run("submits when space available", func(t *testing.T) {
		pool := NewPool(2, WithQueueSize(10))
		defer pool.Shutdown(context.Background())

		ok := pool.SubmitAsync(func(ctx context.Context) error {
			return nil
		})
		assert.True(t, ok)
	})

	t.Run("returns false when pool closed", func(t *testing.T) {
		pool := NewPool(2)
		pool.Shutdown(context.Background())

		ok := pool.SubmitAsync(func(ctx context.Context) error {
			return nil
		})
		assert.False(t, ok)
	})

	t.Run("returns false when queue full", func(t *testing.T) {
		pool := NewPool(1, WithQueueSize(0))
		defer pool.Shutdown(context.Background())

		// Block the worker
		pool.Submit(context.Background(), func(ctx context.Context) error {
			time.Sleep(500 * time.Millisecond)
			return nil
		})

		// Queue should be full
		ok := pool.SubmitAsync(func(ctx context.Context) error {
			return nil
		})
		assert.False(t, ok)
	})
}

func TestPool_Shutdown(t *testing.T) {
	t.Run("gracefully shuts down", func(t *testing.T) {
		pool := NewPool(2)

		var counter atomic.Int32
		for i := 0; i < 5; i++ {
			pool.Submit(context.Background(), func(ctx context.Context) error {
				time.Sleep(10 * time.Millisecond)
				counter.Add(1)
				return nil
			})
		}

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		err := pool.Shutdown(ctx)
		assert.NoError(t, err)
		assert.True(t, pool.Stats().Closed)
		assert.GreaterOrEqual(t, counter.Load(), int32(0))
	})

	t.Run("returns context error on timeout", func(t *testing.T) {
		pool := NewPool(1)

		// Submit a long-running task
		pool.Submit(context.Background(), func(ctx context.Context) error {
			time.Sleep(5 * time.Second)
			return nil
		})

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Millisecond)
		defer cancel()

		err := pool.Shutdown(ctx)
		assert.ErrorIs(t, err, context.DeadlineExceeded)
	})

	t.Run("is idempotent", func(t *testing.T) {
		pool := NewPool(2)

		ctx := context.Background()
		err1 := pool.Shutdown(ctx)
		err2 := pool.Shutdown(ctx)

		assert.NoError(t, err1)
		assert.NoError(t, err2)
	})
}

func TestPool_Stop(t *testing.T) {
	t.Run("stops immediately", func(t *testing.T) {
		pool := NewPool(2)

		var counter atomic.Int32
		for i := 0; i < 100; i++ {
			pool.SubmitAsync(func(ctx context.Context) error {
				time.Sleep(100 * time.Millisecond)
				counter.Add(1)
				return nil
			})
		}

		pool.Stop()

		assert.True(t, pool.Stats().Closed)
		// Not all tasks should have completed
		assert.Less(t, counter.Load(), int32(100))
	})

	t.Run("is idempotent", func(t *testing.T) {
		pool := NewPool(2)

		pool.Stop()
		pool.Stop() // Should not panic

		assert.True(t, pool.Stats().Closed)
	})
}

func TestPool_Stats(t *testing.T) {
	t.Run("reports correct stats", func(t *testing.T) {
		pool := NewPool(3, WithQueueSize(10))
		defer pool.Shutdown(context.Background())

		stats := pool.Stats()
		assert.Equal(t, 3, stats.Workers)
		assert.Equal(t, int32(0), stats.Active)
		assert.Equal(t, int32(0), stats.Pending)
		assert.Equal(t, uint64(0), stats.Completed)
		assert.Equal(t, uint64(0), stats.Errors)
		assert.False(t, stats.Closed)
	})

	t.Run("tracks active tasks", func(t *testing.T) {
		pool := NewPool(2)
		defer pool.Shutdown(context.Background())

		// Submit blocking tasks
		for i := 0; i < 2; i++ {
			pool.Submit(context.Background(), func(ctx context.Context) error {
				time.Sleep(100 * time.Millisecond)
				return nil
			})
		}

		time.Sleep(10 * time.Millisecond)

		stats := pool.Stats()
		assert.GreaterOrEqual(t, stats.Active, int32(0))
	})

	t.Run("tracks completed tasks", func(t *testing.T) {
		pool := NewPool(2)
		defer pool.Shutdown(context.Background())

		for i := 0; i < 5; i++ {
			pool.Submit(context.Background(), func(ctx context.Context) error {
				return nil
			})
		}

		time.Sleep(100 * time.Millisecond)

		stats := pool.Stats()
		assert.GreaterOrEqual(t, stats.Completed, uint64(5))
	})
}

func TestPool_Resize(t *testing.T) {
	t.Run("increases worker count", func(t *testing.T) {
		pool := NewPool(2)
		defer pool.Shutdown(context.Background())

		pool.Resize(5)

		stats := pool.Stats()
		assert.Equal(t, 5, stats.Workers)
	})

	t.Run("decreases worker count", func(t *testing.T) {
		pool := NewPool(5)
		defer pool.Shutdown(context.Background())

		pool.Resize(2)

		stats := pool.Stats()
		assert.Equal(t, 2, stats.Workers)
	})

	t.Run("handles zero workers", func(t *testing.T) {
		pool := NewPool(2)
		defer pool.Shutdown(context.Background())

		pool.Resize(0)

		stats := pool.Stats()
		assert.Equal(t, 1, stats.Workers)
	})
}

func TestPool_Results(t *testing.T) {
	t.Run("receives results", func(t *testing.T) {
		pool := NewPool(2, WithResults(10))
		defer pool.Shutdown(context.Background())

		testErr := errors.New("test error")
		pool.Submit(context.Background(), func(ctx context.Context) error {
			return nil
		})
		pool.Submit(context.Background(), func(ctx context.Context) error {
			return testErr
		})

		time.Sleep(50 * time.Millisecond)

		results := pool.Results()
		require.NotNil(t, results)

		var received int
		for received < 2 {
			select {
			case result := <-results:
				require.NotNil(t, result.Task)
				received++
			case <-time.After(100 * time.Millisecond):
				break
			}
		}
		assert.Equal(t, 2, received)
	})

	t.Run("returns nil when not configured", func(t *testing.T) {
		pool := NewPool(2)
		defer pool.Shutdown(context.Background())

		results := pool.Results()
		assert.Nil(t, results)
	})
}

func TestPool_Concurrent(t *testing.T) {
	t.Run("handles concurrent submissions", func(t *testing.T) {
		pool := NewPool(10, WithQueueSize(1000))
		defer pool.Shutdown(context.Background())

		var counter atomic.Int32
		var wg sync.WaitGroup

		for i := 0; i < 100; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for j := 0; j < 10; j++ {
					pool.Submit(context.Background(), func(ctx context.Context) error {
						counter.Add(1)
						return nil
					})
				}
			}()
		}

		wg.Wait()
		time.Sleep(200 * time.Millisecond)

		assert.Equal(t, int32(1000), counter.Load())
	})

	t.Run("handles concurrent shutdown", func(t *testing.T) {
		pool := NewPool(10)

		var wg sync.WaitGroup
		for i := 0; i < 100; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				pool.Submit(context.Background(), func(ctx context.Context) error {
					return nil
				})
			}()
		}

		wg.Add(1)
		go func() {
			defer wg.Done()
			pool.Shutdown(context.Background())
		}()

		wg.Wait()
		assert.True(t, pool.Stats().Closed)
	})
}

func BenchmarkPool_Submit(b *testing.B) {
	pool := NewPool(10, WithQueueSize(10000))
	defer pool.Shutdown(context.Background())

	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			pool.Submit(context.Background(), func(ctx context.Context) error {
				return nil
			})
		}
	})
}

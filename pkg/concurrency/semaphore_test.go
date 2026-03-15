package concurrency

import (
	"context"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewSemaphore(t *testing.T) {
	t.Run("creates semaphore with valid capacity", func(t *testing.T) {
		sem, err := NewSemaphore(10)
		require.NoError(t, err)
		require.NotNil(t, sem)
		defer sem.Close()

		assert.Equal(t, 10, sem.Capacity())
		assert.Equal(t, 10, sem.Available())
	})

	t.Run("returns error for zero capacity", func(t *testing.T) {
		sem, err := NewSemaphore(0)
		assert.ErrorIs(t, err, ErrInvalidCapacity)
		assert.Nil(t, sem)
	})

	t.Run("returns error for negative capacity", func(t *testing.T) {
		sem, err := NewSemaphore(-5)
		assert.ErrorIs(t, err, ErrInvalidCapacity)
		assert.Nil(t, sem)
	})

	t.Run("MustNewSemaphore panics on error", func(t *testing.T) {
		assert.Panics(t, func() {
			MustNewSemaphore(0)
		})
	})

	t.Run("MustNewSemaphore succeeds with valid capacity", func(t *testing.T) {
		sem := MustNewSemaphore(5)
		require.NotNil(t, sem)
		defer sem.Close()
		assert.Equal(t, 5, sem.Capacity())
	})
}

func TestSemaphore_Acquire(t *testing.T) {
	t.Run("acquires permit", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		err := sem.Acquire(ctx)
		assert.NoError(t, err)
		assert.Equal(t, 0, sem.Available())
		assert.Equal(t, 1, sem.Acquired())
	})

	t.Run("blocks when no permits available", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		// Acquire the only permit
		err := sem.Acquire(context.Background())
		require.NoError(t, err)

		// Try to acquire with short timeout
		ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		err = sem.Acquire(ctx)
		assert.ErrorIs(t, err, context.DeadlineExceeded)
	})

	t.Run("respects context cancellation", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		// Acquire the only permit
		err := sem.Acquire(context.Background())
		require.NoError(t, err)

		// Cancel context while waiting
		ctx, cancel := context.WithCancel(context.Background())
		go func() {
			time.Sleep(10 * time.Millisecond)
			cancel()
		}()

		err = sem.Acquire(ctx)
		assert.ErrorIs(t, err, context.Canceled)
	})

	t.Run("returns error when closed", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		sem.Close()

		err := sem.Acquire(context.Background())
		assert.Error(t, err)
	})
}

func TestSemaphore_TryAcquire(t *testing.T) {
	t.Run("acquires when permit available", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		ok := sem.TryAcquire()
		assert.True(t, ok)
		assert.Equal(t, 0, sem.Available())
	})

	t.Run("returns false when no permits", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		// Acquire the only permit
		sem.TryAcquire()

		ok := sem.TryAcquire()
		assert.False(t, ok)
	})

	t.Run("returns false when closed", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		sem.Close()

		ok := sem.TryAcquire()
		assert.False(t, ok)
	})
}

func TestSemaphore_Release(t *testing.T) {
	t.Run("releases permit", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		sem.Acquire(context.Background())
		assert.Equal(t, 0, sem.Available())

		sem.Release()
		assert.Equal(t, 1, sem.Available())
	})

	t.Run("handles release without acquire", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		// Should not panic or block
		sem.Release()
		assert.Equal(t, 1, sem.Available())
	})

	t.Run("handles multiple releases", func(t *testing.T) {
		sem, _ := NewSemaphore(1)
		defer sem.Close()

		sem.Acquire(context.Background())
		sem.Release()
		sem.Release() // Extra release should be ignored

		assert.Equal(t, 1, sem.Available())
	})
}

func TestSemaphore_Concurrent(t *testing.T) {
	t.Run("handles concurrent acquires", func(t *testing.T) {
		sem, _ := NewSemaphore(10)
		defer sem.Close()

		var counter atomic.Int32
		var wg sync.WaitGroup

		for i := 0; i < 100; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				err := sem.Acquire(context.Background())
				if err == nil {
					counter.Add(1)
					sem.Release()
				}
			}()
		}

		wg.Wait()
		assert.Equal(t, int32(100), counter.Load())
	})

	t.Run("enforces capacity limit", func(t *testing.T) {
		sem, _ := NewSemaphore(5)
		defer sem.Close()

		var maxAcquired atomic.Int32
		var wg sync.WaitGroup

		for i := 0; i < 50; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()

				sem.Acquire(context.Background())
				current := sem.Acquired()
				if int32(current) > maxAcquired.Load() {
					maxAcquired.Store(int32(current))
				}
				time.Sleep(time.Millisecond)
				sem.Release()
			}()
		}

		wg.Wait()
		assert.LessOrEqual(t, maxAcquired.Load(), int32(5))
	})
}

func TestWeightedSemaphore(t *testing.T) {
	t.Run("creates with valid capacity", func(t *testing.T) {
		sem, err := NewWeightedSemaphore(10)
		require.NoError(t, err)
		require.NotNil(t, sem)
		defer sem.Close()
	})

	t.Run("returns error for invalid capacity", func(t *testing.T) {
		sem, err := NewWeightedSemaphore(0)
		assert.ErrorIs(t, err, ErrInvalidCapacity)
		assert.Nil(t, sem)
	})

	t.Run("acquires weight", func(t *testing.T) {
		sem, _ := NewWeightedSemaphore(10)
		defer sem.Close()

		err := sem.Acquire(context.Background(), 5)
		assert.NoError(t, err)

		err = sem.Acquire(context.Background(), 3)
		assert.NoError(t, err)
	})

	t.Run("blocks when weight exceeds capacity", func(t *testing.T) {
		sem, _ := NewWeightedSemaphore(10)
		defer sem.Close()

		err := sem.Acquire(context.Background(), 6)
		require.NoError(t, err)

		ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		err = sem.Acquire(ctx, 5)
		assert.ErrorIs(t, err, context.DeadlineExceeded)
	})

	t.Run("returns error for weight exceeding capacity", func(t *testing.T) {
		sem, _ := NewWeightedSemaphore(5)
		defer sem.Close()

		err := sem.Acquire(context.Background(), 10)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "exceeds")
	})

	t.Run("releases weight", func(t *testing.T) {
		sem, _ := NewWeightedSemaphore(10)
		defer sem.Close()

		sem.Acquire(context.Background(), 5)
		sem.Release(5)

		// Should be able to acquire again
		err := sem.Acquire(context.Background(), 10)
		assert.NoError(t, err)
	})

	t.Run("try acquire", func(t *testing.T) {
		sem, _ := NewWeightedSemaphore(10)
		defer sem.Close()

		ok := sem.TryAcquire(5)
		assert.True(t, ok)

		ok = sem.TryAcquire(6)
		assert.False(t, ok)
	})
}

func TestRateLimiter(t *testing.T) {
	t.Run("creates with valid rate", func(t *testing.T) {
		rl := NewRateLimiter(10, time.Second)
		require.NotNil(t, rl)
		defer rl.Stop()

		assert.False(t, rl.IsStopped())
	})

	t.Run("allows initial burst", func(t *testing.T) {
		rl := NewRateLimiter(5, time.Second)
		defer rl.Stop()

		// Should allow 5 requests immediately
		for i := 0; i < 5; i++ {
			assert.True(t, rl.Allow())
		}
		// 6th should fail
		assert.False(t, rl.Allow())
	})

	t.Run("refills tokens over time", func(t *testing.T) {
		rl := NewRateLimiter(5, 100*time.Millisecond)
		defer rl.Stop()

		// Use all tokens
		for i := 0; i < 5; i++ {
			rl.Allow()
		}
		assert.False(t, rl.Allow())

		// Wait for refill
		time.Sleep(150 * time.Millisecond)
		assert.True(t, rl.Allow())
	})

	t.Run("wait blocks until token available", func(t *testing.T) {
		rl := NewRateLimiter(1, 100*time.Millisecond)
		defer rl.Stop()

		// Use the only token
		err := rl.Wait(context.Background())
		assert.NoError(t, err)

		// Next wait should block until refill
		ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
		defer cancel()

		start := time.Now()
		err = rl.Wait(ctx)
		elapsed := time.Since(start)

		assert.NoError(t, err)
		assert.GreaterOrEqual(t, elapsed, 50*time.Millisecond)
	})

	t.Run("wait respects context cancellation", func(t *testing.T) {
		rl := NewRateLimiter(1, time.Second)
		defer rl.Stop()

		// Use the only token
		rl.Wait(context.Background())

		ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		err := rl.Wait(ctx)
		assert.ErrorIs(t, err, context.DeadlineExceeded)
	})

	t.Run("returns error when stopped", func(t *testing.T) {
		rl := NewRateLimiter(10, time.Second)
		rl.Stop()

		assert.False(t, rl.Allow())
		assert.ErrorIs(t, rl.Wait(context.Background()), ErrRateLimiterStopped)
	})

	t.Run("is idempotent", func(t *testing.T) {
		rl := NewRateLimiter(10, time.Second)
		rl.Stop()
		rl.Stop() // Should not panic

		assert.True(t, rl.IsStopped())
	})
}

func TestRateLimiter_Reserve(t *testing.T) {
	t.Run("reserves token", func(t *testing.T) {
		rl := NewRateLimiter(10, time.Second)
		defer rl.Stop()

		res := rl.Reserve()
		require.NotNil(t, res)

		select {
		case <-res.Ready():
			// OK
		case <-time.After(time.Second):
			t.Fatal("timeout waiting for reservation")
		}
	})

	t.Run("returns delay for future reservation", func(t *testing.T) {
		rl := NewRateLimiter(1, 100*time.Millisecond)
		defer rl.Stop()

		// Use the only token
		rl.Allow()

		res := rl.Reserve()
		require.NotNil(t, res)
		assert.Greater(t, res.Delay(), time.Duration(0))
	})
}

func TestAdaptiveRateLimiter(t *testing.T) {
	t.Run("creates with valid range", func(t *testing.T) {
		arl := NewAdaptiveRateLimiter(1, 100, time.Second)
		require.NotNil(t, arl)
		defer arl.Stop()

		assert.Equal(t, 1, arl.CurrentRate())
	})

	t.Run("adjusts rate on success", func(t *testing.T) {
		arl := NewAdaptiveRateLimiter(1, 10, time.Second)
		defer arl.Stop()

		// Report successes
		for i := 0; i < 5; i++ {
			arl.Success()
		}

		// Rate should have increased
		time.Sleep(50 * time.Millisecond)
		assert.Greater(t, arl.CurrentRate(), 1)
	})

	t.Run("adjusts rate on failure", func(t *testing.T) {
		arl := NewAdaptiveRateLimiter(5, 10, time.Second)
		defer arl.Stop()

		// Report failure
		arl.Failure()

		// Rate should have decreased
		assert.Less(t, arl.CurrentRate(), 5)
	})

	t.Run("respects min rate", func(t *testing.T) {
		arl := NewAdaptiveRateLimiter(5, 10, time.Second)
		defer arl.Stop()

		// Many failures shouldn't go below min
		for i := 0; i < 10; i++ {
			arl.Failure()
		}

		assert.GreaterOrEqual(t, arl.CurrentRate(), 5)
	})

	t.Run("respects max rate", func(t *testing.T) {
		arl := NewAdaptiveRateLimiter(1, 5, time.Second)
		defer arl.Stop()

		// Wait for limiter to be ready
		time.Sleep(50 * time.Millisecond)

		// Many successes shouldn't go above max
		for i := 0; i < 20; i++ {
			arl.Success()
		}

		assert.LessOrEqual(t, arl.CurrentRate(), 5)
	})

	t.Run("stops correctly", func(t *testing.T) {
		arl := NewAdaptiveRateLimiter(1, 10, time.Second)
		arl.Stop()

		assert.False(t, arl.Allow())
		assert.ErrorIs(t, arl.Wait(context.Background()), ErrRateLimiterStopped)
	})
}

func TestOnce(t *testing.T) {
	t.Run("executes once", func(t *testing.T) {
		var once Once
		var counter atomic.Int32

		for i := 0; i < 10; i++ {
			once.Do(func() {
				counter.Add(1)
			})
		}

		assert.Equal(t, int32(1), counter.Load())
	})

	t.Run("can be reset", func(t *testing.T) {
		var once Once
		var counter atomic.Int32

		once.Do(func() {
			counter.Add(1)
		})
		once.Reset()
		once.Do(func() {
			counter.Add(1)
		})

		assert.Equal(t, int32(2), counter.Load())
	})

	t.Run("Done returns correct state", func(t *testing.T) {
		var once Once
		assert.False(t, once.Done())

		once.Do(func() {})
		assert.True(t, once.Done())
	})
}

func TestWaitGroup(t *testing.T) {
	t.Run("waits for all", func(t *testing.T) {
		var wg WaitGroup
		var counter atomic.Int32

		for i := 0; i < 5; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				counter.Add(1)
			}()
		}

		wg.Wait()
		assert.Equal(t, int32(5), counter.Load())
	})

	t.Run("wait context respects cancellation", func(t *testing.T) {
		var wg WaitGroup
		wg.Add(1)

		ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		err := wg.WaitContext(ctx)
		assert.ErrorIs(t, err, context.DeadlineExceeded)

		// Clean up
		wg.Done()
	})

	t.Run("wait context completes successfully", func(t *testing.T) {
		var wg WaitGroup

		wg.Add(1)
		go func() {
			time.Sleep(50 * time.Millisecond)
			wg.Done()
		}()

		ctx, cancel := context.WithTimeout(context.Background(), time.Second)
		defer cancel()

		err := wg.WaitContext(ctx)
		assert.NoError(t, err)
	})
}

func BenchmarkSemaphore_Acquire(b *testing.B) {
	sem, _ := NewSemaphore(100)
	defer sem.Close()

	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			sem.Acquire(context.Background())
			sem.Release()
		}
	})
}

func BenchmarkRateLimiter_Allow(b *testing.B) {
	rl := NewRateLimiter(1000000, time.Second)
	defer rl.Stop()

	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			rl.Allow()
		}
	})
}

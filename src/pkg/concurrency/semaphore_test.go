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

func TestNewSemaphore(t *testing.T) {
	sem := NewSemaphore("test-sem", 10)
	assert.NotNil(t, sem)
	assert.Equal(t, "test-sem", sem.name)
	assert.Equal(t, int64(10), sem.maxWeight)
	assert.NotNil(t, sem.sem)
	assert.NotNil(t, sem.tracer)
	assert.NotNil(t, sem.meter)
}

func TestSemaphoreAcquireRelease(t *testing.T) {
	sem := NewSemaphore("test-sem", 5)
	ctx := context.Background()

	// Acquire
	err := sem.Acquire(ctx, 1)
	assert.NoError(t, err)

	// Release
	sem.Release(1)
	// Should not panic
}

func TestSemaphoreAcquireMultiple(t *testing.T) {
	sem := NewSemaphore("test-sem", 10)
	ctx := context.Background()

	// Acquire multiple times
	err := sem.Acquire(ctx, 3)
	assert.NoError(t, err)

	err = sem.Acquire(ctx, 2)
	assert.NoError(t, err)

	err = sem.Acquire(ctx, 5)
	assert.NoError(t, err)

	// Release all
	sem.Release(3)
	sem.Release(2)
	sem.Release(5)
}

func TestSemaphoreAcquireTimeout(t *testing.T) {
	sem := NewSemaphore("test-sem", 1)

	// Acquire all capacity
	ctx := context.Background()
	err := sem.Acquire(ctx, 1)
	require.NoError(t, err)

	// Try to acquire with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
	defer cancel()

	err = sem.Acquire(ctx, 1)
	assert.Error(t, err)
	assert.True(t, errors.Is(err, context.DeadlineExceeded), "should be timeout error")
}

func TestSemaphoreAcquireCanceled(t *testing.T) {
	sem := NewSemaphore("test-sem", 1)

	// Acquire all capacity
	ctx := context.Background()
	err := sem.Acquire(ctx, 1)
	require.NoError(t, err)

	// Try to acquire with canceled context
	ctx, cancel := context.WithCancel(context.Background())
	cancel() // Cancel immediately

	err = sem.Acquire(ctx, 1)
	assert.Error(t, err)
	assert.True(t, errors.Is(err, context.Canceled), "should be canceled error")
}

func TestSemaphoreTryAcquire(t *testing.T) {
	sem := NewSemaphore("test-sem", 5)

	// Should succeed
	acquired := sem.TryAcquire(3)
	assert.True(t, acquired)

	// Should succeed
	acquired = sem.TryAcquire(2)
	assert.True(t, acquired)

	// Should fail (no capacity left)
	acquired = sem.TryAcquire(1)
	assert.False(t, acquired)

	// Release and try again
	sem.Release(3)
	acquired = sem.TryAcquire(3)
	assert.True(t, acquired)
}

func TestSemaphoreConcurrency(t *testing.T) {
	sem := NewSemaphore("concurrent-sem", 10)
	ctx := context.Background()

	var wg sync.WaitGroup
	var activeCount atomic.Int32
	var maxActive int32

	iterations := 100

	for i := 0; i < iterations; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()

			err := sem.Acquire(ctx, 1)
			if err != nil {
				return
			}
			defer sem.Release(1)

			// Track active count
			current := activeCount.Add(1)
			if current > maxActive {
				atomic.StoreInt32(&maxActive, current)
			}

			// Simulate work
			time.Sleep(time.Millisecond)

			activeCount.Add(-1)
		}()
	}

	wg.Wait()

	// Max active should not exceed capacity
	assert.LessOrEqual(t, maxActive, int32(10))
}

func TestWithSemaphore(t *testing.T) {
	sem := NewSemaphore("test-sem", 5)
	ctx := context.Background()

	executed := false
	err := sem.WithSemaphore(ctx, 1, func() error {
		executed = true
		return nil
	})

	assert.NoError(t, err)
	assert.True(t, executed)
}

func TestWithSemaphoreError(t *testing.T) {
	sem := NewSemaphore("test-sem", 5)
	ctx := context.Background()

	expectedErr := errors.New("test error")
	err := sem.WithSemaphore(ctx, 1, func() error {
		return expectedErr
	})

	assert.Error(t, err)
	assert.Equal(t, expectedErr, err)
}

func TestWithSemaphoreAcquireFailure(t *testing.T) {
	sem := NewSemaphore("test-sem", 1)

	// Acquire all capacity
	ctx := context.Background()
	err := sem.Acquire(ctx, 1)
	require.NoError(t, err)

	// Try WithSemaphore with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Millisecond)
	defer cancel()

	executed := false
	err = sem.WithSemaphore(ctx, 1, func() error {
		executed = true
		return nil
	})

	assert.Error(t, err)
	assert.False(t, executed, "function should not be executed")
	assert.Contains(t, err.Error(), "failed to acquire semaphore")
}

func TestNewRateLimiter(t *testing.T) {
	limiter := NewRateLimiter("test-limiter", 10, 100*time.Millisecond)
	assert.NotNil(t, limiter)
	assert.Equal(t, int64(10), limiter.maxTokens)
	assert.Equal(t, 100*time.Millisecond, limiter.refillPeriod)

	// Cleanup
	defer limiter.Stop()

	// Give it time to start
	time.Sleep(10 * time.Millisecond)
}

func TestRateLimiterWait(t *testing.T) {
	limiter := NewRateLimiter("test-limiter", 5, 100*time.Millisecond)
	defer limiter.Stop()

	ctx := context.Background()

	// Should be able to acquire burst capacity
	for i := 0; i < 5; i++ {
		err := limiter.Wait(ctx)
		assert.NoError(t, err)
	}

	// Next one should timeout quickly
	ctx2, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
	defer cancel()

	err := limiter.Wait(ctx2)
	assert.Error(t, err)
}

func TestRateLimiterAllow(t *testing.T) {
	limiter := NewRateLimiter("test-limiter", 3, 100*time.Millisecond)
	defer limiter.Stop()

	// Should allow burst capacity
	assert.True(t, limiter.Allow())
	assert.True(t, limiter.Allow())
	assert.True(t, limiter.Allow())

	// Should be exhausted
	assert.False(t, limiter.Allow())
	assert.False(t, limiter.Allow())

	// Wait for refill
	time.Sleep(150 * time.Millisecond)

	// Should allow again (at least one)
	assert.True(t, limiter.Allow())
}

func TestRateLimiterRefill(t *testing.T) {
	limiter := NewRateLimiter("test-limiter", 2, 50*time.Millisecond)
	defer limiter.Stop()

	// Exhaust capacity
	assert.True(t, limiter.Allow())
	assert.True(t, limiter.Allow())
	assert.False(t, limiter.Allow())

	// Wait for refill
	time.Sleep(100 * time.Millisecond)

	// Should have tokens again
	allowed := limiter.Allow()
	assert.True(t, allowed, "should refill after interval")
}

// Benchmarks

func BenchmarkSemaphoreAcquireRelease(b *testing.B) {
	sem := NewSemaphore("bench-sem", 100)
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = sem.Acquire(ctx, 1)
		sem.Release(1)
	}
}

func BenchmarkSemaphoreTryAcquire(b *testing.B) {
	sem := NewSemaphore("bench-sem", 100)

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		if sem.TryAcquire(1) {
			sem.Release(1)
		}
	}
}

func BenchmarkWithSemaphore(b *testing.B) {
	sem := NewSemaphore("bench-sem", 100)
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = sem.WithSemaphore(ctx, 1, func() error {
			return nil
		})
	}
}

func BenchmarkRateLimiterAllow(b *testing.B) {
	limiter := NewRateLimiter("bench-limiter", 1000, time.Second)

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		limiter.Allow()
	}
}

func BenchmarkSemaphoreConcurrent(b *testing.B) {
	sem := NewSemaphore("bench-sem", 10)
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_ = sem.Acquire(ctx, 1)
			sem.Release(1)
		}
	})
}

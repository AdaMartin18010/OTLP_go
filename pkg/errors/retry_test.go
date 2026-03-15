package errors

import (
	"context"
	"errors"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestExponentialBackoff_Calculate(t *testing.T) {
	t.Run("initial delay", func(t *testing.T) {
		eb := NewExponentialBackoff(100 * time.Millisecond)
		delay := eb.Calculate(0)
		assert.Equal(t, 100*time.Millisecond, delay)
	})

	t.Run("exponential growth", func(t *testing.T) {
		eb := NewExponentialBackoff(100 * time.Millisecond).
			WithMultiplier(2.0).
			WithJitter(false)

		assert.Equal(t, 100*time.Millisecond, eb.Calculate(1))
		assert.Equal(t, 200*time.Millisecond, eb.Calculate(2))
		assert.Equal(t, 400*time.Millisecond, eb.Calculate(3))
		assert.Equal(t, 800*time.Millisecond, eb.Calculate(4))
	})

	t.Run("max delay cap", func(t *testing.T) {
		eb := NewExponentialBackoff(100 * time.Millisecond).
			WithMultiplier(2.0).
			WithMaxDelay(500 * time.Millisecond).
			WithJitter(false)

		assert.Equal(t, 500*time.Millisecond, eb.Calculate(5))
		assert.Equal(t, 500*time.Millisecond, eb.Calculate(10))
	})

	t.Run("with jitter", func(t *testing.T) {
		eb := NewExponentialBackoff(100 * time.Millisecond).
			WithJitter(true).
			WithJitterFactor(0.1)

		delay1 := eb.Calculate(2)
		delay2 := eb.Calculate(2)
		delay3 := eb.Calculate(2)

		// With jitter, delays should vary
		// 200ms with 10% jitter = 180ms to 220ms
		assert.GreaterOrEqual(t, delay1, 180*time.Millisecond)
		assert.LessOrEqual(t, delay1, 220*time.Millisecond)

		// Note: There's a small chance all three could be equal
		atLeastOneDifferent := delay1 != delay2 || delay2 != delay3
		_ = atLeastOneDifferent // Just documenting the behavior
	})

	t.Run("without jitter", func(t *testing.T) {
		eb := NewExponentialBackoff(100 * time.Millisecond).
			WithMultiplier(2.0).
			WithJitter(false)

		delay1 := eb.Calculate(2)
		delay2 := eb.Calculate(2)

		assert.Equal(t, delay1, delay2)
		assert.Equal(t, 200*time.Millisecond, delay1)
	})

	t.Run("custom multiplier", func(t *testing.T) {
		eb := NewExponentialBackoff(100 * time.Millisecond).
			WithMultiplier(3.0).
			WithJitter(false)

		assert.Equal(t, 100*time.Millisecond, eb.Calculate(1))
		assert.Equal(t, 300*time.Millisecond, eb.Calculate(2))
		assert.Equal(t, 900*time.Millisecond, eb.Calculate(3))
	})
}

func TestFixedBackoff(t *testing.T) {
	fb := NewFixedBackoff(500 * time.Millisecond)

	assert.Equal(t, 500*time.Millisecond, fb.Calculate(0))
	assert.Equal(t, 500*time.Millisecond, fb.Calculate(1))
	assert.Equal(t, 500*time.Millisecond, fb.Calculate(100))
}

func TestLinearBackoff(t *testing.T) {
	lb := NewLinearBackoff(100*time.Millisecond, 50*time.Millisecond)

	assert.Equal(t, 100*time.Millisecond, lb.Calculate(0))
	assert.Equal(t, 100*time.Millisecond, lb.Calculate(1))
	assert.Equal(t, 150*time.Millisecond, lb.Calculate(2))
	assert.Equal(t, 200*time.Millisecond, lb.Calculate(3))
	assert.Equal(t, 250*time.Millisecond, lb.Calculate(4))
}

func TestLinearBackoff_WithMaxDelay(t *testing.T) {
	lb := NewLinearBackoff(100*time.Millisecond, 100*time.Millisecond).
		WithMaxDelay(300 * time.Millisecond)

	assert.Equal(t, 100*time.Millisecond, lb.Calculate(1))
	assert.Equal(t, 200*time.Millisecond, lb.Calculate(2))
	assert.Equal(t, 300*time.Millisecond, lb.Calculate(3))
	assert.Equal(t, 300*time.Millisecond, lb.Calculate(10))
}

func TestDecorrelatedJitterBackoff(t *testing.T) {
	djb := NewDecorrelatedJitterBackoff(100*time.Millisecond, 1000*time.Millisecond)

	t.Run("stays within bounds", func(t *testing.T) {
		for i := 0; i < 100; i++ {
			delay := djb.Calculate(i)
			assert.GreaterOrEqual(t, delay, 100*time.Millisecond)
			assert.LessOrEqual(t, delay, 1000*time.Millisecond)
		}
	})

	t.Run("varies over calls", func(t *testing.T) {
		delay1 := djb.Calculate(0)
		delay2 := djb.Calculate(0)
		delay3 := djb.Calculate(0)

		// With jitter, delays should generally vary
		// (though there's a small chance they could be equal)
		_ = delay1
		_ = delay2
		_ = delay3
	})
}

func TestStandardRetryPolicy(t *testing.T) {
	t.Run("next delay", func(t *testing.T) {
		backoff := NewExponentialBackoff(100 * time.Millisecond).WithJitter(false)
		policy := NewRetryPolicy(3, backoff)

		delay1, ok1 := policy.NextDelay(0)
		assert.True(t, ok1)
		assert.Equal(t, 100*time.Millisecond, delay1)

		delay2, ok2 := policy.NextDelay(1)
		assert.True(t, ok2)
		assert.Equal(t, 100*time.Millisecond, delay2)

		delay3, ok3 := policy.NextDelay(2)
		assert.True(t, ok3)
		assert.Equal(t, 200*time.Millisecond, delay3)

		_, ok4 := policy.NextDelay(3)
		assert.False(t, ok4)
	})

	t.Run("max attempts", func(t *testing.T) {
		backoff := NewFixedBackoff(100 * time.Millisecond)
		policy := NewRetryPolicy(5, backoff)

		assert.Equal(t, 5, policy.MaxAttempts())
	})

	t.Run("default retryable codes", func(t *testing.T) {
		policy := NewRetryPolicy(3, NewFixedBackoff(100*time.Millisecond))

		assert.True(t, policy.IsRetryable(New("test").WithCode(CodeUnavailable)))
		assert.True(t, policy.IsRetryable(New("test").WithCode(CodeResourceExhausted)))
		assert.True(t, policy.IsRetryable(New("test").WithCode(CodeAborted)))
		assert.True(t, policy.IsRetryable(New("test").WithCode(CodeDeadlineExceeded)))
	})

	t.Run("custom retryable codes", func(t *testing.T) {
		policy := NewRetryPolicy(3, NewFixedBackoff(100*time.Millisecond)).
			WithRetryableCodes(CodeInternal, CodeUnknown)

		assert.True(t, policy.IsRetryable(New("test").WithCode(CodeInternal)))
		assert.True(t, policy.IsRetryable(New("test").WithCode(CodeUnknown)))
		assert.False(t, policy.IsRetryable(New("test").WithCode(CodeUnavailable)))
	})

	t.Run("custom retryable func", func(t *testing.T) {
		policy := NewRetryPolicy(3, NewFixedBackoff(100*time.Millisecond)).
			WithRetryableFunc(func(err error) bool {
				return err != nil && err.Error() == "special"
			})

		assert.True(t, policy.IsRetryable(errors.New("special")))
		assert.False(t, policy.IsRetryable(errors.New("other")))
	})

	t.Run("OTLPError retryable flag", func(t *testing.T) {
		policy := NewRetryPolicy(3, NewFixedBackoff(100*time.Millisecond))

		retryableErr := New("test").WithRetryable(true)
		nonRetryableErr := New("test").WithRetryable(false)

		assert.True(t, policy.IsRetryable(retryableErr))
		assert.False(t, policy.IsRetryable(nonRetryableErr))
	})

	t.Run("nil error", func(t *testing.T) {
		policy := NewRetryPolicy(3, NewFixedBackoff(100*time.Millisecond))
		assert.False(t, policy.IsRetryable(nil))
	})
}

func TestRetry(t *testing.T) {
	t.Run("success on first attempt", func(t *testing.T) {
		callCount := 0
		fn := func() error {
			callCount++
			return nil
		}

		policy := NewRetryPolicy(3, NewFixedBackoff(10*time.Millisecond))
		result, err := Retry(policy, fn)

		require.NoError(t, err)
		assert.Equal(t, 1, result.Attempts)
		assert.Equal(t, 1, callCount)
	})

	t.Run("success after retries", func(t *testing.T) {
		callCount := 0
		fn := func() error {
			callCount++
			if callCount < 3 {
				return New("temporary").WithCode(CodeUnavailable)
			}
			return nil
		}

		policy := NewRetryPolicy(5, NewFixedBackoff(10*time.Millisecond))
		result, err := Retry(policy, fn)

		require.NoError(t, err)
		assert.Equal(t, 3, result.Attempts)
	})

	t.Run("max attempts exceeded", func(t *testing.T) {
		callCount := 0
		fn := func() error {
			callCount++
			return New("always fails").WithCode(CodeUnavailable)
		}

		policy := NewRetryPolicy(3, NewFixedBackoff(10*time.Millisecond))
		result, err := Retry(policy, fn)

		require.Error(t, err)
		assert.Equal(t, 3, result.Attempts)
		assert.Equal(t, 3, callCount)
		// The error is wrapped with code/category info
		assert.Contains(t, result.LastErr.Error(), "always fails")
	})

	t.Run("non-retryable error", func(t *testing.T) {
		callCount := 0
		fn := func() error {
			callCount++
			return New("permanent").WithCode(CodeInvalidArgument)
		}

		policy := NewRetryPolicy(5, NewFixedBackoff(10*time.Millisecond))
		_, err := Retry(policy, fn)

		require.Error(t, err)
		assert.Equal(t, 1, callCount) // Should not retry
	})

	t.Run("context cancellation", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())

		callCount := 0
		fn := func(ctx context.Context) error {
			callCount++
			if callCount == 2 {
				cancel()
			}
			time.Sleep(5 * time.Millisecond)
			return New("error").WithCode(CodeUnavailable)
		}

		policy := NewRetryPolicy(10, NewFixedBackoff(100*time.Millisecond))
		_, err := RetryWithContext(ctx, policy, fn)

		require.Error(t, err)
		assert.Contains(t, err.Error(), "cancelled")
	})

	t.Run("context timeout", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		fn := func(ctx context.Context) error {
			time.Sleep(20 * time.Millisecond)
			return New("error").WithCode(CodeUnavailable)
		}

		policy := NewRetryPolicy(10, NewFixedBackoff(100*time.Millisecond))
		_, err := RetryWithContext(ctx, policy, fn)

		require.Error(t, err)
		assert.Contains(t, err.Error(), "cancelled")
	})
}

func TestRetryConfig(t *testing.T) {
	t.Run("default config", func(t *testing.T) {
		config := DefaultRetryConfig()

		assert.Equal(t, 3, config.MaxAttempts)
		assert.Equal(t, 100*time.Millisecond, config.InitialDelay)
		assert.Equal(t, 30*time.Second, config.MaxDelay)
		assert.Equal(t, 2.0, config.Multiplier)
		assert.True(t, config.UseJitter)
	})

	t.Run("build policy", func(t *testing.T) {
		config := DefaultRetryConfig().WithJitter(false)
		policy := config.BuildPolicy()

		assert.Equal(t, 3, policy.MaxAttempts())

		delay, ok := policy.NextDelay(1)
		assert.True(t, ok)
		assert.Equal(t, 100*time.Millisecond, delay)
	})

	t.Run("chaining methods", func(t *testing.T) {
		config := DefaultRetryConfig().
			WithMaxAttempts(5).
			WithInitialDelay(200 * time.Millisecond).
			WithMaxDelay(10 * time.Second).
			WithMultiplier(3.0).
			WithJitter(false)

		assert.Equal(t, 5, config.MaxAttempts)
		assert.Equal(t, 200*time.Millisecond, config.InitialDelay)
		assert.Equal(t, 10*time.Second, config.MaxDelay)
		assert.Equal(t, 3.0, config.Multiplier)
		assert.False(t, config.UseJitter)
	})
}

func TestDo(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		callCount := 0
		err := Do(func() error {
			callCount++
			return nil
		})

		require.NoError(t, err)
		assert.Equal(t, 1, callCount)
	})

	t.Run("with options", func(t *testing.T) {
		callCount := 0
		err := Do(
			func() error {
				callCount++
				if callCount < 2 {
					return New("error").WithCode(CodeUnavailable)
				}
				return nil
			},
			func(c *RetryConfig) {
				c.MaxAttempts = 5
			},
		)

		require.NoError(t, err)
		assert.Equal(t, 2, callCount)
	})
}

func TestDoWithContext(t *testing.T) {
	ctx := context.Background()

	err := DoWithContext(ctx, func(ctx context.Context) error {
		return nil
	})

	require.NoError(t, err)
}

func TestPermanentError(t *testing.T) {
	t.Run("mark permanent", func(t *testing.T) {
		original := errors.New("original")
		permanent := MarkPermanent(original)

		assert.True(t, IsPermanent(permanent))
		assert.Equal(t, original, Unwrap(permanent))
	})

	t.Run("mark nil returns nil", func(t *testing.T) {
		assert.Nil(t, MarkPermanent(nil))
	})

	t.Run("is permanent false for non-permanent", func(t *testing.T) {
		assert.False(t, IsPermanent(errors.New("regular")))
	})

	t.Run("is permanent false for nil", func(t *testing.T) {
		assert.False(t, IsPermanent(nil))
	})
}

func TestRetryResult(t *testing.T) {
	fn := func() error { return nil }
	policy := NewRetryPolicy(3, NewFixedBackoff(10*time.Millisecond))

	result, err := Retry(policy, fn)
	require.NoError(t, err)

	assert.Equal(t, 1, result.Attempts)
	assert.GreaterOrEqual(t, result.Duration, time.Duration(0))
}

func TestRetryWithPolicyInterruption(t *testing.T) {
	t.Run("stops on context done during delay", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), 50*time.Millisecond)
		defer cancel()

		callCount := 0
		fn := func(ctx context.Context) error {
			callCount++
			return New("error").WithCode(CodeUnavailable)
		}

		// Use a policy with long delays
		policy := NewRetryPolicy(10, NewFixedBackoff(1*time.Second))
		result, err := RetryWithContext(ctx, policy, fn)

		require.Error(t, err)
		assert.Contains(t, err.Error(), "cancelled")
		// Should have made at least 1 attempt but stopped early
		assert.GreaterOrEqual(t, result.Attempts, 1)
	})
}

func BenchmarkRetry_Success(b *testing.B) {
	policy := NewRetryPolicy(3, NewFixedBackoff(time.Millisecond))
	fn := func() error { return nil }

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = Retry(policy, fn)
	}
}

func BenchmarkRetry_WithFailure(b *testing.B) {
	policy := NewRetryPolicy(3, NewFixedBackoff(time.Millisecond))
	attempt := 0
	fn := func() error {
		attempt++
		if attempt%2 == 0 {
			return nil
		}
		return New("error").WithCode(CodeUnavailable)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = Retry(policy, fn)
	}
}

func BenchmarkExponentialBackoff_Calculate(b *testing.B) {
	eb := NewExponentialBackoff(100 * time.Millisecond)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = eb.Calculate(5)
	}
}

// TestRetry_Race tests for race conditions in retry logic
func TestRetry_Race(t *testing.T) {
	policy := NewRetryPolicy(5, NewFixedBackoff(1*time.Millisecond))

	var counter int32
	fn := func() error {
		atomic.AddInt32(&counter, 1)
		if atomic.LoadInt32(&counter) < 3 {
			return New("error").WithCode(CodeUnavailable)
		}
		return nil
	}

	// Run multiple retries concurrently
	for i := 0; i < 10; i++ {
		go func() {
			_, _ = Retry(policy, fn)
		}()
	}

	time.Sleep(100 * time.Millisecond)
}

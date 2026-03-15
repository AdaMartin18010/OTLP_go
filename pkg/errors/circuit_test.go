package errors

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestState_String(t *testing.T) {
	tests := []struct {
		state    State
		expected string
	}{
		{StateClosed, "CLOSED"},
		{StateOpen, "OPEN"},
		{StateHalfOpen, "HALF_OPEN"},
		{State(999), "UNKNOWN"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			assert.Equal(t, tt.expected, tt.state.String())
		})
	}
}

func TestDefaultConfig(t *testing.T) {
	config := DefaultConfig()

	assert.Equal(t, uint32(5), config.MaxFailures)
	assert.Equal(t, 30*time.Second, config.ResetTimeout)
	assert.Equal(t, uint32(3), config.HalfOpenMaxCalls)
	assert.Equal(t, uint32(2), config.SuccessThreshold)
	assert.Nil(t, config.OnStateChange)
	assert.Nil(t, config.IsSuccessful)
}

func TestNewCircuitBreaker(t *testing.T) {
	t.Run("with custom config", func(t *testing.T) {
		config := Config{
			MaxFailures:      3,
			ResetTimeout:     10 * time.Second,
			HalfOpenMaxCalls: 5,
			SuccessThreshold: 1,
		}

		cb := NewCircuitBreaker(config)
		require.NotNil(t, cb)
		assert.Equal(t, StateClosed, cb.State())
	})

	t.Run("with default config", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()
		require.NotNil(t, cb)
		assert.Equal(t, StateClosed, cb.State())
	})
}

func TestCircuitBreaker_StateTransitions(t *testing.T) {
	t.Run("closed to open on failures", func(t *testing.T) {
		config := Config{
			MaxFailures:      3,
			ResetTimeout:     100 * time.Millisecond,
			HalfOpenMaxCalls: 1,
			SuccessThreshold: 1,
		}

		cb := NewCircuitBreaker(config)
		assert.Equal(t, StateClosed, cb.State())

		// Record failures up to threshold
		cb.RecordFailure()
		assert.Equal(t, StateClosed, cb.State())
		assert.Equal(t, uint32(1), cb.Failures())

		cb.RecordFailure()
		assert.Equal(t, StateClosed, cb.State())
		assert.Equal(t, uint32(2), cb.Failures())

		cb.RecordFailure()
		assert.Equal(t, StateOpen, cb.State())
	})

	t.Run("open to half-open after timeout", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     50 * time.Millisecond,
			HalfOpenMaxCalls: 3,
			SuccessThreshold: 2,
		}

		cb := NewCircuitBreaker(config)

		// Open the circuit
		cb.RecordFailure()
		assert.Equal(t, StateOpen, cb.State())

		// Wait for timeout
		time.Sleep(100 * time.Millisecond)

		// Next Allow() should transition to half-open
		err := cb.Allow()
		require.NoError(t, err)
		assert.Equal(t, StateHalfOpen, cb.State())
	})

	t.Run("half-open to closed on successes", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     50 * time.Millisecond,
			HalfOpenMaxCalls: 3,
			SuccessThreshold: 2,
		}

		cb := NewCircuitBreaker(config)

		// Open then transition to half-open
		cb.RecordFailure()
		time.Sleep(100 * time.Millisecond)
		cb.Allow()
		assert.Equal(t, StateHalfOpen, cb.State())

		// Record successes
		cb.RecordSuccess()
		assert.Equal(t, StateHalfOpen, cb.State())
		assert.Equal(t, uint32(1), cb.Successes())

		cb.RecordSuccess()
		assert.Equal(t, StateClosed, cb.State())
		assert.Equal(t, uint32(0), cb.Successes()) // Reset after transition
	})

	t.Run("half-open to open on failure", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     50 * time.Millisecond,
			HalfOpenMaxCalls: 3,
			SuccessThreshold: 2,
		}

		cb := NewCircuitBreaker(config)

		// Open then transition to half-open
		cb.RecordFailure()
		time.Sleep(100 * time.Millisecond)
		cb.Allow()
		assert.Equal(t, StateHalfOpen, cb.State())

		// Single failure should reopen
		cb.RecordFailure()
		assert.Equal(t, StateOpen, cb.State())
	})
}

func TestCircuitBreaker_Allow(t *testing.T) {
	t.Run("allows when closed", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()
		assert.NoError(t, cb.Allow())
	})

	t.Run("rejects when open", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     1 * time.Hour, // Long timeout
			HalfOpenMaxCalls: 1,
		}

		cb := NewCircuitBreaker(config)
		cb.RecordFailure()

		err := cb.Allow()
		require.Error(t, err)
		assert.ErrorIs(t, err, ErrCircuitOpen)
	})

	t.Run("allows limited calls in half-open", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     50 * time.Millisecond,
			HalfOpenMaxCalls: 2,
			SuccessThreshold: 2,
		}

		cb := NewCircuitBreaker(config)

		// Open then transition to half-open
		cb.RecordFailure()
		time.Sleep(100 * time.Millisecond)

		// First two calls should be allowed
		assert.NoError(t, cb.Allow())
		assert.NoError(t, cb.Allow())

		// Third call should be rejected
		err := cb.Allow()
		require.Error(t, err)
		assert.Contains(t, err.Error(), "too many calls")
	})
}

func TestCircuitBreaker_Execute(t *testing.T) {
	t.Run("executes when allowed", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()

		callCount := 0
		err := cb.Execute(func() error {
			callCount++
			return nil
		})

		require.NoError(t, err)
		assert.Equal(t, 1, callCount)
	})

	t.Run("returns circuit open error", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     1 * time.Hour,
			HalfOpenMaxCalls: 1,
		}

		cb := NewCircuitBreaker(config)
		cb.RecordFailure()

		callCount := 0
		err := cb.Execute(func() error {
			callCount++
			return nil
		})

		require.Error(t, err)
		assert.ErrorIs(t, err, ErrCircuitOpen)
		assert.Equal(t, 0, callCount) // Function should not be called
	})

	t.Run("records success", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()

		err := cb.Execute(func() error {
			return nil
		})

		require.NoError(t, err)
		assert.Equal(t, uint32(0), cb.Failures())
	})

	t.Run("records failure", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()

		execErr := errors.New("execution failed")
		err := cb.Execute(func() error {
			return execErr
		})

		assert.Equal(t, execErr, err)
		assert.Equal(t, uint32(1), cb.Failures())
	})
}

func TestCircuitBreaker_ExecuteWithContext(t *testing.T) {
	ctx := context.Background()
	cb := NewCircuitBreakerDefault()

	callCount := 0
	err := cb.ExecuteWithContext(ctx, func(ctx context.Context) error {
		callCount++
		return nil
	})

	require.NoError(t, err)
	assert.Equal(t, 1, callCount)
}

func TestCircuitBreaker_RecordResult(t *testing.T) {
	t.Run("records nil as success", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()
		cb.RecordResult(nil)
		assert.Equal(t, uint32(0), cb.Failures())
	})

	t.Run("records error as failure", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()
		cb.RecordResult(errors.New("error"))
		assert.Equal(t, uint32(1), cb.Failures())
	})

	t.Run("uses custom IsSuccessful function", func(t *testing.T) {
		config := Config{
			MaxFailures:  3,
			ResetTimeout: 100 * time.Millisecond,
			IsSuccessful: func(err error) bool {
				// Treat "retryable" errors as "successful" for circuit purposes
				return err == nil || (err != nil && err.Error() == "retryable")
			},
		}

		cb := NewCircuitBreaker(config)

		// This should be counted as a failure (not successful)
		cb.RecordResult(errors.New("fatal"))
		assert.Equal(t, uint32(1), cb.Failures())

		// This should be counted as a success (based on custom logic)
		// In Closed state, RecordSuccess resets failures to 0
		// Note: Successes are only tracked in HalfOpen state, so it remains 0 in Closed state
		cb.RecordResult(errors.New("retryable"))
		assert.Equal(t, uint32(0), cb.Failures()) // Reset by RecordSuccess in Closed state
		// Successes counter is only used in HalfOpen state
	})
}

func TestCircuitBreaker_Reset(t *testing.T) {
	config := Config{
		MaxFailures:      1,
		ResetTimeout:     50 * time.Millisecond,
		HalfOpenMaxCalls: 1,
	}

	cb := NewCircuitBreaker(config)

	// Open the circuit
	cb.RecordFailure()
	assert.Equal(t, StateOpen, cb.State())

	// Reset it
	cb.Reset()
	assert.Equal(t, StateClosed, cb.State())
	assert.Equal(t, uint32(0), cb.Failures())
	assert.Equal(t, uint32(0), cb.Successes())

	// Should allow calls again
	assert.NoError(t, cb.Allow())
}

func TestCircuitBreaker_Metrics(t *testing.T) {
	config := Config{
		MaxFailures:      2,
		ResetTimeout:     100 * time.Millisecond,
		HalfOpenMaxCalls: 1,
	}

	cb := NewCircuitBreaker(config)

	// Initial state
	metrics := cb.Metrics()
	assert.Equal(t, StateClosed, metrics.State)
	assert.Equal(t, uint32(0), metrics.Failures)
	assert.Equal(t, uint32(0), metrics.Successes)
	// LastFailure should be zero until a failure is recorded
	// Note: This assertion depends on implementation details

	// After failure
	cb.RecordFailure()
	metrics = cb.Metrics()
	assert.Equal(t, StateClosed, metrics.State)
	assert.Equal(t, uint32(1), metrics.Failures)
	assert.False(t, metrics.LastFailure.IsZero())

	// After opening
	cb.RecordFailure()
	metrics = cb.Metrics()
	assert.Equal(t, StateOpen, metrics.State)
}

func TestCircuitBreaker_StateChangeCallback(t *testing.T) {
	var transitions []struct{ from, to State }

	config := Config{
		MaxFailures:      1,
		ResetTimeout:     50 * time.Millisecond,
		HalfOpenMaxCalls: 1,
		SuccessThreshold: 1,
		OnStateChange: func(from, to State) {
			transitions = append(transitions, struct{ from, to State }{from, to})
		},
	}

	cb := NewCircuitBreaker(config)

	// Closed -> Open
	cb.RecordFailure()
	require.Len(t, transitions, 1)
	assert.Equal(t, StateClosed, transitions[0].from)
	assert.Equal(t, StateOpen, transitions[0].to)

	// Wait and trigger HalfOpen
	time.Sleep(100 * time.Millisecond)
	cb.Allow()
	require.Len(t, transitions, 2)
	assert.Equal(t, StateOpen, transitions[1].from)
	assert.Equal(t, StateHalfOpen, transitions[1].to)

	// HalfOpen -> Closed
	cb.RecordSuccess()
	require.Len(t, transitions, 3)
	assert.Equal(t, StateHalfOpen, transitions[2].from)
	assert.Equal(t, StateClosed, transitions[2].to)
}

func TestCircuitGroup(t *testing.T) {
	t.Run("get or create circuit", func(t *testing.T) {
		group := NewCircuitGroup(DefaultConfig())

		cb1 := group.Get("service1")
		cb2 := group.Get("service1")
		cb3 := group.Get("service2")

		assert.Same(t, cb1, cb2)
		assert.NotSame(t, cb1, cb3)
	})

	t.Run("execute on circuit", func(t *testing.T) {
		group := NewCircuitGroup(DefaultConfig())

		callCount := 0
		err := group.Execute("service1", func() error {
			callCount++
			return nil
		})

		require.NoError(t, err)
		assert.Equal(t, 1, callCount)
	})

	t.Run("keys and count", func(t *testing.T) {
		group := NewCircuitGroup(DefaultConfig())

		group.Get("a")
		group.Get("b")
		group.Get("c")

		keys := group.Keys()
		assert.Len(t, keys, 3)
		assert.Contains(t, keys, "a")
		assert.Contains(t, keys, "b")
		assert.Contains(t, keys, "c")

		assert.Equal(t, 3, group.Count())
	})

	t.Run("remove circuit", func(t *testing.T) {
		group := NewCircuitGroup(DefaultConfig())

		cb1 := group.Get("service1")
		group.Remove("service1")

		cb2 := group.Get("service1")
		assert.NotSame(t, cb1, cb2)
	})

	t.Run("concurrent access", func(t *testing.T) {
		group := NewCircuitGroup(DefaultConfig())

		var wg sync.WaitGroup
		for i := 0; i < 100; i++ {
			wg.Add(2)
			go func(n int) {
				defer wg.Done()
				group.Get(fmt.Sprintf("service%d", n%10))
			}(i)
			go func(n int) {
				defer wg.Done()
				_ = group.Count()
			}(i)
		}
		wg.Wait()

		assert.Equal(t, 10, group.Count())
	})
}

func TestCircuitManager(t *testing.T) {
	t.Run("get group", func(t *testing.T) {
		manager := NewCircuitManager()

		config := DefaultConfig()
		group1 := manager.GetGroup("service1", config)
		group2 := manager.GetGroup("service1", config)

		assert.Same(t, group1, group2)
	})

	t.Run("get circuit", func(t *testing.T) {
		manager := NewCircuitManager()
		config := DefaultConfig()

		cb1 := manager.GetCircuit("service1", "endpoint1", config)
		cb2 := manager.GetCircuit("service1", "endpoint1", config)

		assert.Same(t, cb1, cb2)
	})

	t.Run("service names", func(t *testing.T) {
		manager := NewCircuitManager()

		manager.GetGroup("service1", DefaultConfig())
		manager.GetGroup("service2", DefaultConfig())

		names := manager.ServiceNames()
		assert.Len(t, names, 2)
		assert.Contains(t, names, "service1")
		assert.Contains(t, names, "service2")
	})

	t.Run("remove group", func(t *testing.T) {
		manager := NewCircuitManager()
		config := DefaultConfig()

		group1 := manager.GetGroup("service1", config)
		manager.RemoveGroup("service1")

		group2 := manager.GetGroup("service1", config)
		assert.NotSame(t, group1, group2)
	})
}

func TestCircuitBreaker_Fallback(t *testing.T) {
	t.Run("fallback on open circuit", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     1 * time.Hour,
			HalfOpenMaxCalls: 1,
		}

		cb := NewCircuitBreaker(config)
		cb.RecordFailure()

		fallbackCalled := false
		err := cb.ExecuteWithFallback(
			func() error {
				return errors.New("should not be called")
			},
			func(err error) error {
				fallbackCalled = true
				return errors.New("fallback result")
			},
		)

		require.Error(t, err)
		assert.Equal(t, "fallback result", err.Error())
		assert.True(t, fallbackCalled)
	})

	t.Run("no fallback when circuit allows", func(t *testing.T) {
		cb := NewCircuitBreakerDefault()

		fallbackCalled := false
		err := cb.ExecuteWithFallback(
			func() error {
				return nil
			},
			func(err error) error {
				fallbackCalled = true
				return errors.New("fallback result")
			},
		)

		require.NoError(t, err)
		assert.False(t, fallbackCalled)
	})

	t.Run("fallback with context", func(t *testing.T) {
		config := Config{
			MaxFailures:      1,
			ResetTimeout:     1 * time.Hour,
			HalfOpenMaxCalls: 1,
		}

		cb := NewCircuitBreaker(config)
		cb.RecordFailure()

		ctx := context.Background()
		err := cb.ExecuteWithContextAndFallback(
			ctx,
			func(ctx context.Context) error {
				return errors.New("should not be called")
			},
			func(err error) error {
				return errors.New("fallback")
			},
		)

		assert.Equal(t, "fallback", err.Error())
	})
}

func TestWithTimeout(t *testing.T) {
	t.Run("completes before timeout", func(t *testing.T) {
		err := WithTimeout(func() error {
			time.Sleep(10 * time.Millisecond)
			return nil
		}, 100*time.Millisecond)

		require.NoError(t, err)
	})

	t.Run("times out", func(t *testing.T) {
		err := WithTimeout(func() error {
			time.Sleep(100 * time.Millisecond)
			return nil
		}, 10*time.Millisecond)

		require.Error(t, err)
		var timeoutErr *TimeoutError
		assert.True(t, errors.As(err, &timeoutErr))
		assert.Equal(t, 10*time.Millisecond, timeoutErr.Duration)
	})

	t.Run("returns function error", func(t *testing.T) {
		expectedErr := errors.New("function error")
		err := WithTimeout(func() error {
			return expectedErr
		}, 100*time.Millisecond)

		assert.Equal(t, expectedErr, err)
	})
}

func TestWithTimeoutContext(t *testing.T) {
	t.Run("completes before timeout", func(t *testing.T) {
		ctx := context.Background()
		err := WithTimeoutContext(ctx, func(ctx context.Context) error {
			return nil
		}, 100*time.Millisecond)

		require.NoError(t, err)
	})

	t.Run("respects parent context", func(t *testing.T) {
		parentCtx, cancel := context.WithCancel(context.Background())
		cancel() // Cancel immediately

		// Wait a bit for cancel to propagate
		time.Sleep(10 * time.Millisecond)

		err := WithTimeoutContext(parentCtx, func(ctx context.Context) error {
			select {
			case <-ctx.Done():
				return ctx.Err()
			default:
				return nil
			}
		}, 1*time.Hour)

		require.Error(t, err)
		assert.ErrorIs(t, err, context.Canceled)
	})
}

func TestTimeoutError(t *testing.T) {
	err := &TimeoutError{Duration: 5 * time.Second}
	assert.Contains(t, err.Error(), "5s")
}

func TestCircuitBreaker_Concurrency(t *testing.T) {
	config := Config{
		MaxFailures:      100,
		ResetTimeout:     100 * time.Millisecond,
		HalfOpenMaxCalls: 50,
	}

	cb := NewCircuitBreaker(config)

	var wg sync.WaitGroup
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = cb.Execute(func() error {
				return nil
			})
		}()
	}
	wg.Wait()

	assert.Equal(t, StateClosed, cb.State())
}

func TestCircuitGroup_ResetAll(t *testing.T) {
	group := NewCircuitGroup(DefaultConfig())

	// Open multiple circuits
	cb1 := group.Get("service1")
	cb2 := group.Get("service2")

	cb1.RecordFailure()
	cb1.RecordFailure()
	cb1.RecordFailure()
	cb1.RecordFailure()
	cb1.RecordFailure()

	cb2.RecordFailure()
	cb2.RecordFailure()
	cb2.RecordFailure()
	cb2.RecordFailure()
	cb2.RecordFailure()

	assert.Equal(t, StateOpen, cb1.State())
	assert.Equal(t, StateOpen, cb2.State())

	// Reset all
	group.ResetAll()

	assert.Equal(t, StateClosed, cb1.State())
	assert.Equal(t, StateClosed, cb2.State())
}

func BenchmarkCircuitBreaker_Execute(b *testing.B) {
	cb := NewCircuitBreakerDefault()
	fn := func() error { return nil }

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = cb.Execute(fn)
	}
}

func BenchmarkCircuitBreaker_Allow(b *testing.B) {
	cb := NewCircuitBreakerDefault()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = cb.Allow()
	}
}

func BenchmarkCircuitGroup_Get(b *testing.B) {
	group := NewCircuitGroup(DefaultConfig())

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = group.Get(fmt.Sprintf("service%d", i%100))
	}
}

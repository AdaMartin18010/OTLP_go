// Package errors provides error handling utilities for the OTLP Go SDK.
// Retry implementation with multiple backoff strategies.

package errors

import (
	"context"
	"fmt"
	"math"
	"math/rand"
	"sync"
	"time"
)

// RetryPolicy defines the interface for retry policies.
type RetryPolicy interface {
	// NextDelay returns the delay for the next retry attempt.
	// Returns false if no more retries should be attempted.
	NextDelay(attempt int) (time.Duration, bool)
	// MaxAttempts returns the maximum number of retry attempts.
	MaxAttempts() int
}

// BackoffStrategy defines the interface for backoff calculation strategies.
type BackoffStrategy interface {
	// Calculate returns the delay for a given attempt number.
	Calculate(attempt int) time.Duration
	// MaxDelay returns the maximum delay allowed.
	MaxDelay() time.Duration
}

// ExponentialBackoff implements exponential backoff with jitter.
type ExponentialBackoff struct {
	InitialDelay time.Duration
	Multiplier   float64
	MaxDelay     time.Duration
	Jitter       bool
	JitterFactor float64
}

// NewExponentialBackoff creates a new exponential backoff strategy.
func NewExponentialBackoff(initialDelay time.Duration) *ExponentialBackoff {
	return &ExponentialBackoff{
		InitialDelay: initialDelay,
		Multiplier:   2.0,
		MaxDelay:     30 * time.Second,
		Jitter:       true,
		JitterFactor: 0.1,
	}
}

// WithMultiplier sets the multiplier for exponential backoff.
func (eb *ExponentialBackoff) WithMultiplier(multiplier float64) *ExponentialBackoff {
	eb.Multiplier = multiplier
	return eb
}

// WithMaxDelay sets the maximum delay.
func (eb *ExponentialBackoff) WithMaxDelay(maxDelay time.Duration) *ExponentialBackoff {
	eb.MaxDelay = maxDelay
	return eb
}

// WithJitter enables or disables jitter.
func (eb *ExponentialBackoff) WithJitter(enable bool) *ExponentialBackoff {
	eb.Jitter = enable
	return eb
}

// WithJitterFactor sets the jitter factor (0.0 to 1.0).
func (eb *ExponentialBackoff) WithJitterFactor(factor float64) *ExponentialBackoff {
	eb.JitterFactor = factor
	return eb
}

// Calculate returns the delay for a given attempt.
func (eb *ExponentialBackoff) Calculate(attempt int) time.Duration {
	if attempt <= 0 {
		return eb.InitialDelay
	}
	
	delay := float64(eb.InitialDelay) * math.Pow(eb.Multiplier, float64(attempt-1))
	result := time.Duration(delay)
	
	if result > eb.MaxDelay {
		result = eb.MaxDelay
	}
	
	if eb.Jitter {
		jitterRange := float64(result) * eb.JitterFactor
		jitter := time.Duration(rand.Float64() * jitterRange)
		if rand.Intn(2) == 0 {
			result += jitter
		} else {
			result -= jitter
		}
	}
	
	return result
}

// FixedBackoff implements fixed interval backoff.
type FixedBackoff struct {
	Delay    time.Duration
	MaxDelay time.Duration
}

// NewFixedBackoff creates a new fixed backoff strategy.
func NewFixedBackoff(delay time.Duration) *FixedBackoff {
	return &FixedBackoff{
		Delay:    delay,
		MaxDelay: delay,
	}
}

// Calculate returns the fixed delay.
func (fb *FixedBackoff) Calculate(attempt int) time.Duration {
	_ = attempt // Fixed backoff ignores attempt number
	return fb.Delay
}

// LinearBackoff implements linear increasing backoff.
type LinearBackoff struct {
	InitialDelay time.Duration
	Increment    time.Duration
	MaxDelay     time.Duration
}

// NewLinearBackoff creates a new linear backoff strategy.
func NewLinearBackoff(initialDelay, increment time.Duration) *LinearBackoff {
	return &LinearBackoff{
		InitialDelay: initialDelay,
		Increment:    increment,
		MaxDelay:     30 * time.Second,
	}
}

// Calculate returns the linearly increasing delay.
func (lb *LinearBackoff) Calculate(attempt int) time.Duration {
	if attempt <= 0 {
		return lb.InitialDelay
	}
	
	result := lb.InitialDelay + lb.Increment*time.Duration(attempt-1)
	if result > lb.MaxDelay {
		result = lb.MaxDelay
	}
	return result
}

// DecorrelatedJitterBackoff implements decorrelated jitter backoff.
// This is the "Full Jitter" approach recommended by AWS.
type DecorrelatedJitterBackoff struct {
	BaseDelay  time.Duration
	MaxDelay   time.Duration
	Multiplier float64
	lastDelay  time.Duration
	mu         sync.Mutex
}

// NewDecorrelatedJitterBackoff creates a new decorrelated jitter backoff.
func NewDecorrelatedJitterBackoff(baseDelay, maxDelay time.Duration) *DecorrelatedJitterBackoff {
	return &DecorrelatedJitterBackoff{
		BaseDelay:  baseDelay,
		MaxDelay:   maxDelay,
		Multiplier: 3.0,
		lastDelay:  baseDelay,
	}
}

// Calculate returns the delay with decorrelated jitter.
func (djb *DecorrelatedJitterBackoff) Calculate(attempt int) time.Duration {
	djb.mu.Lock()
	defer djb.mu.Unlock()
	
	_ = attempt // Decorrelated jitter doesn't use attempt number directly
	
	// Calculate next delay with decorrelated jitter
	maxDelay := time.Duration(float64(djb.lastDelay) * djb.Multiplier)
	if maxDelay > djb.MaxDelay {
		maxDelay = djb.MaxDelay
	}
	if maxDelay < djb.BaseDelay {
		maxDelay = djb.BaseDelay
	}
	
	// Random delay between base and max
	delayRange := maxDelay - djb.BaseDelay
	if delayRange <= 0 {
		djb.lastDelay = djb.BaseDelay
		return djb.BaseDelay
	}
	
	djb.lastDelay = djb.BaseDelay + time.Duration(rand.Float64()*float64(delayRange))
	return djb.lastDelay
}

// StandardRetryPolicy implements a standard retry policy with backoff.
type StandardRetryPolicy struct {
	maxAttempts     int
	backoffStrategy BackoffStrategy
	retryableCodes  []ErrorCode
	retryableFuncs  []func(error) bool
	mu              sync.RWMutex
}

// NewRetryPolicy creates a new standard retry policy.
func NewRetryPolicy(maxAttempts int, backoff BackoffStrategy) *StandardRetryPolicy {
	return &StandardRetryPolicy{
		maxAttempts:     maxAttempts,
		backoffStrategy: backoff,
		retryableCodes: []ErrorCode{
			CodeUnavailable,
			CodeResourceExhausted,
			CodeAborted,
			CodeDeadlineExceeded,
		},
		retryableFuncs: make([]func(error) bool, 0),
	}
}

// WithRetryableCodes sets the error codes that should trigger a retry.
func (rp *StandardRetryPolicy) WithRetryableCodes(codes ...ErrorCode) *StandardRetryPolicy {
	rp.mu.Lock()
	defer rp.mu.Unlock()
	rp.retryableCodes = codes
	return rp
}

// WithRetryableFunc adds a custom function to determine if an error is retryable.
func (rp *StandardRetryPolicy) WithRetryableFunc(fn func(error) bool) *StandardRetryPolicy {
	rp.mu.Lock()
	defer rp.mu.Unlock()
	rp.retryableFuncs = append(rp.retryableFuncs, fn)
	return rp
}

// NextDelay returns the delay for the next retry attempt.
func (rp *StandardRetryPolicy) NextDelay(attempt int) (time.Duration, bool) {
	if attempt >= rp.maxAttempts {
		return 0, false
	}
	return rp.backoffStrategy.Calculate(attempt), true
}

// MaxAttempts returns the maximum number of retry attempts.
func (rp *StandardRetryPolicy) MaxAttempts() int {
	return rp.maxAttempts
}

// IsRetryable checks if an error should trigger a retry.
func (rp *StandardRetryPolicy) IsRetryable(err error) bool {
	if err == nil {
		return false
	}
	
	rp.mu.RLock()
	defer rp.mu.RUnlock()
	
	// Check retryable codes
	code := GetCode(err)
	for _, retryableCode := range rp.retryableCodes {
		if code == retryableCode {
			return true
		}
	}
	
	// Check custom functions
	for _, fn := range rp.retryableFuncs {
		if fn(err) {
			return true
		}
	}
	
	// Check if it's an OTLPError with retryable flag
	var otlpErr *OTLPError
	if As(err, &otlpErr) {
		return otlpErr.IsRetryable()
	}
	
	return false
}

// RetryResult contains the result of a retry operation.
type RetryResult struct {
	Attempts int
	Duration time.Duration
	LastErr  error
}

// RetryableFunc is a function that can be retried.
type RetryableFunc func() error

// RetryableFuncWithContext is a function that can be retried with context.
type RetryableFuncWithContext func(ctx context.Context) error

// Retry executes a function with retry logic.
func Retry(policy RetryPolicy, fn RetryableFunc) (*RetryResult, error) {
	return RetryWithContext(context.Background(), policy, func(ctx context.Context) error {
		return fn()
	})
}

// RetryWithContext executes a function with retry logic and context support.
func RetryWithContext(ctx context.Context, policy RetryPolicy, fn RetryableFuncWithContext) (*RetryResult, error) {
	result := &RetryResult{}
	startTime := time.Now()
	
	for attempt := 0; attempt < policy.MaxAttempts(); attempt++ {
		result.Attempts = attempt + 1
		
		err := fn(ctx)
		if err == nil {
			result.Duration = time.Since(startTime)
			return result, nil
		}
		
		result.LastErr = err
		
		// Check if we should retry this error
		if standardPolicy, ok := policy.(*StandardRetryPolicy); ok {
			if !standardPolicy.IsRetryable(err) {
				result.Duration = time.Since(startTime)
				return result, err
			}
		}
		
		// Check if this is the last attempt
		if attempt == policy.MaxAttempts()-1 {
			break
		}
		
		// Calculate next delay
		delay, shouldRetry := policy.NextDelay(attempt + 1)
		if !shouldRetry {
			result.Duration = time.Since(startTime)
			return result, err
		}
		
		// Wait for next attempt or context cancellation
		select {
		case <-ctx.Done():
			result.Duration = time.Since(startTime)
			return result, fmt.Errorf("retry cancelled: %w", ctx.Err())
		case <-time.After(delay):
			// Continue to next attempt
		}
	}
	
	result.Duration = time.Since(startTime)
	return result, result.LastErr
}

// RetryConfig provides a convenient way to configure retries.
type RetryConfig struct {
	MaxAttempts  int
	InitialDelay time.Duration
	MaxDelay     time.Duration
	Multiplier   float64
	UseJitter    bool
}

// DefaultRetryConfig returns a default retry configuration.
func DefaultRetryConfig() *RetryConfig {
	return &RetryConfig{
		MaxAttempts:  3,
		InitialDelay: 100 * time.Millisecond,
		MaxDelay:     30 * time.Second,
		Multiplier:   2.0,
		UseJitter:    true,
	}
}

// BuildPolicy builds a retry policy from the configuration.
func (rc *RetryConfig) BuildPolicy() RetryPolicy {
	backoff := NewExponentialBackoff(rc.InitialDelay).
		WithMultiplier(rc.Multiplier).
		WithMaxDelay(rc.MaxDelay).
		WithJitter(rc.UseJitter)
	
	return NewRetryPolicy(rc.MaxAttempts, backoff)
}

// WithMaxAttempts sets the maximum attempts.
func (rc *RetryConfig) WithMaxAttempts(n int) *RetryConfig {
	rc.MaxAttempts = n
	return rc
}

// WithInitialDelay sets the initial delay.
func (rc *RetryConfig) WithInitialDelay(d time.Duration) *RetryConfig {
	rc.InitialDelay = d
	return rc
}

// WithMaxDelay sets the maximum delay.
func (rc *RetryConfig) WithMaxDelay(d time.Duration) *RetryConfig {
	rc.MaxDelay = d
	return rc
}

// WithMultiplier sets the backoff multiplier.
func (rc *RetryConfig) WithMultiplier(m float64) *RetryConfig {
	rc.Multiplier = m
	return rc
}

// WithJitter enables or disables jitter.
func (rc *RetryConfig) WithJitter(enable bool) *RetryConfig {
	rc.UseJitter = enable
	return rc
}

// Do is a convenience function for simple retry scenarios.
func Do(fn RetryableFunc, opts ...func(*RetryConfig)) error {
	config := DefaultRetryConfig()
	for _, opt := range opts {
		opt(config)
	}
	
	_, err := Retry(config.BuildPolicy(), fn)
	return err
}

// DoWithContext is a convenience function for simple retry scenarios with context.
func DoWithContext(ctx context.Context, fn RetryableFuncWithContext, opts ...func(*RetryConfig)) error {
	config := DefaultRetryConfig()
	for _, opt := range opts {
		opt(config)
	}
	
	_, err := RetryWithContext(ctx, config.BuildPolicy(), fn)
	return err
}

// Permanent wraps an error to indicate it should not be retried.
type Permanent struct {
	err error
}

// Error implements the error interface.
func (p *Permanent) Error() string {
	return p.err.Error()
}

// Unwrap returns the underlying error.
func (p *Permanent) Unwrap() error {
	return p.err
}

// IsPermanent checks if an error is a permanent error (should not be retried).
func IsPermanent(err error) bool {
	if err == nil {
		return false
	}
	var p *Permanent
	return As(err, &p)
}

// MarkPermanent marks an error as permanent (non-retryable).
func MarkPermanent(err error) error {
	if err == nil {
		return nil
	}
	return &Permanent{err: err}
}

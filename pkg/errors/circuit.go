// Package errors provides error handling utilities for the OTLP Go SDK.
// Circuit breaker implementation for fault tolerance.
//
// Stability: Stable
// Compliance: OpenTelemetry Specification v1.42.0
package errors

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"time"
)

// State represents the state of a circuit breaker.
type State int32

const (
	// StateClosed indicates the circuit is closed (normal operation).
	// All requests are allowed through.
	StateClosed State = iota
	// StateOpen indicates the circuit is open (failing).
	// All requests are rejected immediately.
	StateOpen
	// StateHalfOpen indicates the circuit is testing if the issue is resolved.
	// A limited number of requests are allowed through to test the service.
	StateHalfOpen
)

// String returns the string representation of the state.
func (s State) String() string {
	switch s {
	case StateClosed:
		return "CLOSED"
	case StateOpen:
		return "OPEN"
	case StateHalfOpen:
		return "HALF_OPEN"
	default:
		return "UNKNOWN"
	}
}

// Config holds the configuration for a circuit breaker.
type Config struct {
	// MaxFailures is the number of failures before opening the circuit.
	MaxFailures uint32
	// ResetTimeout is the duration to wait before transitioning to half-open.
	ResetTimeout time.Duration
	// HalfOpenMaxCalls is the number of test calls allowed in half-open state.
	HalfOpenMaxCalls uint32
	// SuccessThreshold is the number of successful calls needed to close circuit.
	SuccessThreshold uint32
	// OnStateChange is called when the circuit breaker state changes.
	OnStateChange func(from, to State)
	// IsSuccessful determines if an error should be counted as a failure.
	// If nil, all non-nil errors are considered failures.
	IsSuccessful func(err error) bool
}

// DefaultConfig returns a default circuit breaker configuration.
func DefaultConfig() Config {
	return Config{
		MaxFailures:      5,
		ResetTimeout:     30 * time.Second,
		HalfOpenMaxCalls: 3,
		SuccessThreshold: 2,
		OnStateChange:    nil,
		IsSuccessful:     nil,
	}
}

// CircuitBreaker implements the circuit breaker pattern.
type CircuitBreaker struct {
	config Config

	// State
	state           atomic.Int32
	failures        atomic.Uint32
	successes       atomic.Uint32
	halfOpenCalls   atomic.Uint32
	lastFailureTime atomic.Int64 // Unix nano

	mu sync.RWMutex
}

// ErrCircuitOpen is returned when the circuit breaker is open.
var ErrCircuitOpen = errors.New("circuit breaker is open")

// ErrCircuitTooManyCalls is returned when too many calls are made in half-open state.
var ErrCircuitTooManyCalls = errors.New("circuit breaker: too many calls in half-open state")

// NewCircuitBreaker creates a new circuit breaker with the given configuration.
func NewCircuitBreaker(config Config) *CircuitBreaker {
	cb := &CircuitBreaker{
		config: config,
	}
	cb.state.Store(int32(StateClosed))
	return cb
}

// New creates a new circuit breaker with default configuration.
func NewCircuitBreakerDefault() *CircuitBreaker {
	return NewCircuitBreaker(DefaultConfig())
}

// State returns the current state of the circuit breaker.
func (cb *CircuitBreaker) State() State {
	return State(cb.state.Load())
}

// Failures returns the current number of consecutive failures.
func (cb *CircuitBreaker) Failures() uint32 {
	return cb.failures.Load()
}

// Successes returns the current number of consecutive successes.
func (cb *CircuitBreaker) Successes() uint32 {
	return cb.successes.Load()
}

// Allow checks if a request is allowed to pass through.
func (cb *CircuitBreaker) Allow() error {
	state := cb.State()

	switch state {
	case StateClosed:
		return nil

	case StateOpen:
		// Check if we should transition to half-open
		lastFailure := time.Unix(0, cb.lastFailureTime.Load())
		if time.Since(lastFailure) > cb.config.ResetTimeout {
			if cb.transitionTo(StateHalfOpen) {
				cb.halfOpenCalls.Store(1) // First call is being counted
				cb.failures.Store(0)
				cb.successes.Store(0)
			}
			return nil
		}
		return fmt.Errorf("%w: circuit has been open since %v", ErrCircuitOpen, lastFailure)

	case StateHalfOpen:
		calls := cb.halfOpenCalls.Add(1)
		if calls > cb.config.HalfOpenMaxCalls {
			cb.halfOpenCalls.Add(^uint32(0)) // Decrement
			return ErrCircuitTooManyCalls
		}
		return nil
	}

	return nil
}

// RecordSuccess records a successful call.
func (cb *CircuitBreaker) RecordSuccess() {
	state := cb.State()

	switch state {
	case StateClosed:
		cb.failures.Store(0)

	case StateHalfOpen:
		successes := cb.successes.Add(1)
		cb.failures.Store(0)

		if successes >= cb.config.SuccessThreshold {
			cb.transitionTo(StateClosed)
			cb.halfOpenCalls.Store(0)
			cb.successes.Store(0)
		}
	}
}

// RecordFailure records a failed call.
func (cb *CircuitBreaker) RecordFailure() {
	cb.lastFailureTime.Store(time.Now().UnixNano())
	state := cb.State()

	switch state {
	case StateClosed:
		cb.successes.Store(0)
		failures := cb.failures.Add(1)

		if failures >= cb.config.MaxFailures {
			cb.transitionTo(StateOpen)
		}

	case StateHalfOpen:
		cb.transitionTo(StateOpen)
		cb.halfOpenCalls.Store(0)
		cb.successes.Store(0)
	}
}

// RecordResult records the result of a call.
func (cb *CircuitBreaker) RecordResult(err error) {
	if cb.config.IsSuccessful != nil {
		if cb.config.IsSuccessful(err) {
			cb.RecordSuccess()
		} else {
			cb.RecordFailure()
		}
	} else {
		if err == nil {
			cb.RecordSuccess()
		} else {
			cb.RecordFailure()
		}
	}
}

// Execute runs the given function if the circuit allows it.
// Records the result automatically.
func (cb *CircuitBreaker) Execute(fn func() error) error {
	if err := cb.Allow(); err != nil {
		return err
	}

	err := fn()
	cb.RecordResult(err)
	return err
}

// ExecuteWithContext runs the given function with context if the circuit allows it.
func (cb *CircuitBreaker) ExecuteWithContext(ctx context.Context, fn func(context.Context) error) error {
	if err := cb.Allow(); err != nil {
		return err
	}

	err := fn(ctx)
	cb.RecordResult(err)
	return err
}

// transitionTo attempts to transition to a new state.
// Returns true if the transition occurred.
func (cb *CircuitBreaker) transitionTo(newState State) bool {
	oldState := State(cb.state.Load())
	if oldState == newState {
		return false
	}

	if cb.state.CompareAndSwap(int32(oldState), int32(newState)) {
		if cb.config.OnStateChange != nil {
			cb.config.OnStateChange(oldState, newState)
		}
		return true
	}
	return false
}

// Reset manually resets the circuit breaker to closed state.
func (cb *CircuitBreaker) Reset() {
	cb.state.Store(int32(StateClosed))
	cb.failures.Store(0)
	cb.successes.Store(0)
	cb.halfOpenCalls.Store(0)
	cb.lastFailureTime.Store(0)
}

// Metrics returns current metrics for the circuit breaker.
func (cb *CircuitBreaker) Metrics() CircuitBreakerMetrics {
	return CircuitBreakerMetrics{
		State:       cb.State(),
		Failures:    cb.Failures(),
		Successes:   cb.Successes(),
		LastFailure: time.Unix(0, cb.lastFailureTime.Load()),
	}
}

// CircuitBreakerMetrics holds metrics for a circuit breaker.
type CircuitBreakerMetrics struct {
	State       State
	Failures    uint32
	Successes   uint32
	LastFailure time.Time
}

// CircuitGroup manages multiple circuit breakers by key.
type CircuitGroup struct {
	config   Config
	breakers map[string]*CircuitBreaker
	mu       sync.RWMutex
}

// NewCircuitGroup creates a new circuit group with the given configuration.
func NewCircuitGroup(config Config) *CircuitGroup {
	return &CircuitGroup{
		config:   config,
		breakers: make(map[string]*CircuitBreaker),
	}
}

// Get returns the circuit breaker for the given key, creating it if necessary.
func (cg *CircuitGroup) Get(key string) *CircuitBreaker {
	cg.mu.RLock()
	cb, exists := cg.breakers[key]
	cg.mu.RUnlock()

	if exists {
		return cb
	}

	cg.mu.Lock()
	defer cg.mu.Unlock()

	// Double-check after acquiring write lock
	if cb, exists := cg.breakers[key]; exists {
		return cb
	}

	cb = NewCircuitBreaker(cg.config)
	cg.breakers[key] = cb
	return cb
}

// Execute executes a function on the circuit breaker for the given key.
func (cg *CircuitGroup) Execute(key string, fn func() error) error {
	return cg.Get(key).Execute(fn)
}

// ExecuteWithContext executes a function with context on the circuit breaker for the given key.
func (cg *CircuitGroup) ExecuteWithContext(ctx context.Context, key string, fn func(context.Context) error) error {
	return cg.Get(key).ExecuteWithContext(ctx, fn)
}

// Remove removes a circuit breaker from the group.
func (cg *CircuitGroup) Remove(key string) {
	cg.mu.Lock()
	defer cg.mu.Unlock()
	delete(cg.breakers, key)
}

// Keys returns all keys in the group.
func (cg *CircuitGroup) Keys() []string {
	cg.mu.RLock()
	defer cg.mu.RUnlock()

	keys := make([]string, 0, len(cg.breakers))
	for k := range cg.breakers {
		keys = append(keys, k)
	}
	return keys
}

// Count returns the number of circuit breakers in the group.
func (cg *CircuitGroup) Count() int {
	cg.mu.RLock()
	defer cg.mu.RUnlock()
	return len(cg.breakers)
}

// ResetAll resets all circuit breakers in the group.
func (cg *CircuitGroup) ResetAll() {
	cg.mu.RLock()
	breakers := make([]*CircuitBreaker, 0, len(cg.breakers))
	for _, cb := range cg.breakers {
		breakers = append(breakers, cb)
	}
	cg.mu.RUnlock()

	for _, cb := range breakers {
		cb.Reset()
	}
}

// CircuitManager manages circuit breakers for different services.
type CircuitManager struct {
	groups map[string]*CircuitGroup
	mu     sync.RWMutex
}

// NewCircuitManager creates a new circuit manager.
func NewCircuitManager() *CircuitManager {
	return &CircuitManager{
		groups: make(map[string]*CircuitGroup),
	}
}

// GetGroup returns or creates a circuit group for the given name.
func (cm *CircuitManager) GetGroup(name string, config Config) *CircuitGroup {
	cm.mu.RLock()
	group, exists := cm.groups[name]
	cm.mu.RUnlock()

	if exists {
		return group
	}

	cm.mu.Lock()
	defer cm.mu.Unlock()

	if group, exists := cm.groups[name]; exists {
		return group
	}

	group = NewCircuitGroup(config)
	cm.groups[name] = group
	return group
}

// GetCircuit returns a circuit breaker for a service and key.
func (cm *CircuitManager) GetCircuit(service, key string, config Config) *CircuitBreaker {
	return cm.GetGroup(service, config).Get(key)
}

// RemoveGroup removes a circuit group.
func (cm *CircuitManager) RemoveGroup(name string) {
	cm.mu.Lock()
	defer cm.mu.Unlock()
	delete(cm.groups, name)
}

// ServiceNames returns all service names.
func (cm *CircuitManager) ServiceNames() []string {
	cm.mu.RLock()
	defer cm.mu.RUnlock()

	names := make([]string, 0, len(cm.groups))
	for name := range cm.groups {
		names = append(names, name)
	}
	return names
}

// FallbackFunc is a function that provides a fallback value when the circuit is open.
type FallbackFunc func(error) error

// ExecuteWithFallback executes a function with a fallback if the circuit is open.
func (cb *CircuitBreaker) ExecuteWithFallback(fn func() error, fallback FallbackFunc) error {
	err := cb.Execute(fn)
	if err != nil && errors.Is(err, ErrCircuitOpen) && fallback != nil {
		return fallback(err)
	}
	return err
}

// ExecuteWithContextAndFallback executes a function with context and fallback.
func (cb *CircuitBreaker) ExecuteWithContextAndFallback(
	ctx context.Context,
	fn func(context.Context) error,
	fallback FallbackFunc,
) error {
	err := cb.ExecuteWithContext(ctx, fn)
	if err != nil && errors.Is(err, ErrCircuitOpen) && fallback != nil {
		return fallback(err)
	}
	return err
}

// TimeoutError is returned when a call times out.
type TimeoutError struct {
	Duration time.Duration
}

// Error implements the error interface.
func (e *TimeoutError) Error() string {
	return fmt.Sprintf("operation timed out after %v", e.Duration)
}

// WithTimeout executes a function with a timeout.
func WithTimeout(fn func() error, timeout time.Duration) error {
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	done := make(chan error, 1)
	go func() {
		done <- fn()
	}()

	select {
	case err := <-done:
		return err
	case <-ctx.Done():
		return &TimeoutError{Duration: timeout}
	}
}

// WithTimeoutContext executes a function with a timeout using the provided context.
func WithTimeoutContext(ctx context.Context, fn func(context.Context) error, timeout time.Duration) error {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	return fn(ctx)
}

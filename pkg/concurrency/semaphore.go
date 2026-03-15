// Package concurrency provides thread-safe primitives and utilities
// for concurrent programming in the OTLP Go SDK.
//
// This package includes:
//   - Semaphore for resource limiting
//   - Rate limiter for request throttling
//   - Worker pools for parallel processing
//   - Context-aware synchronization primitives
//   - Pipeline pattern implementation
//   - Fan-Out/Fan-In pattern implementation
package concurrency

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"time"
)

var (
	// ErrRateLimiterStopped is returned when operating on a stopped rate limiter.
	ErrRateLimiterStopped = errors.New("rate limiter is stopped")
	// ErrInvalidCapacity is returned when creating a semaphore with invalid capacity.
	ErrInvalidCapacity = errors.New("semaphore capacity must be positive")
)

// Semaphore is a counting semaphore implementation.
//
// A semaphore controls access to a finite number of resources.
// It maintains a set of permits that can be acquired and released.
//
// This implementation:
//   - Is thread-safe
//   - Supports context cancellation
//   - Provides non-blocking operations
//   - Tracks current usage
//
// Example usage:
//
//	sem := concurrency.NewSemaphore(10) // Allow 10 concurrent operations
//	defer sem.Close()
//
//	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
//	defer cancel()
//
//	if err := sem.Acquire(ctx); err != nil {
//	    // Handle timeout
//	}
//	defer sem.Release()
//
//	// Do work...
type Semaphore struct {
	ch       chan struct{}
	capacity int
	acquired atomic.Int32
	closed   atomic.Bool
}

// NewSemaphore creates a new semaphore with the given capacity.
//
// The capacity determines the maximum number of permits available.
// Returns ErrInvalidCapacity if capacity is not positive.
func NewSemaphore(capacity int) (*Semaphore, error) {
	if capacity <= 0 {
		return nil, ErrInvalidCapacity
	}

	return &Semaphore{
		ch:       make(chan struct{}, capacity),
		capacity: capacity,
	}, nil
}

// MustNewSemaphore creates a new semaphore and panics on error.
func MustNewSemaphore(capacity int) *Semaphore {
	s, err := NewSemaphore(capacity)
	if err != nil {
		panic(err)
	}
	return s
}

// Acquire acquires a permit from the semaphore.
//
// This method blocks until a permit is available or the context is cancelled.
// Returns ctx.Err() if the context is cancelled before a permit is acquired.
func (s *Semaphore) Acquire(ctx context.Context) error {
	if s.closed.Load() {
		return ErrInvalidCapacity
	}

	select {
	case s.ch <- struct{}{}:
		s.acquired.Add(1)
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// TryAcquire attempts to acquire a permit without blocking.
//
// Returns true if a permit was acquired, false otherwise.
func (s *Semaphore) TryAcquire() bool {
	if s.closed.Load() {
		return false
	}

	select {
	case s.ch <- struct{}{}:
		s.acquired.Add(1)
		return true
	default:
		return false
	}
}

// Release releases a permit back to the semaphore.
//
// This method never blocks. If the semaphore is full (which shouldn't
// happen with correct usage), the release is silently dropped.
func (s *Semaphore) Release() {
	select {
	case <-s.ch:
		s.acquired.Add(-1)
	default:
		// Semaphore was empty, ignore
	}
}

// Capacity returns the semaphore's capacity.
func (s *Semaphore) Capacity() int {
	return s.capacity
}

// Available returns the number of available permits.
func (s *Semaphore) Available() int {
	return s.capacity - len(s.ch)
}

// Acquired returns the number of currently acquired permits.
func (s *Semaphore) Acquired() int {
	return int(s.acquired.Load())
}

// Close closes the semaphore.
//
// After closing, Acquire will return an error.
// This method is idempotent.
func (s *Semaphore) Close() {
	s.closed.Store(true)
}

// WeightedSemaphore is a semaphore that supports weighted acquires.
//
// Unlike the basic Semaphore where each acquire takes exactly one permit,
// WeightedSemaphore allows acquiring multiple permits at once.
type WeightedSemaphore struct {
	capacity int64
	current  atomic.Int64
	mu       sync.Mutex
	waiters  []chan struct{}
	closed   atomic.Bool
}

// NewWeightedSemaphore creates a new weighted semaphore.
func NewWeightedSemaphore(capacity int64) (*WeightedSemaphore, error) {
	if capacity <= 0 {
		return nil, ErrInvalidCapacity
	}

	return &WeightedSemaphore{
		capacity: capacity,
		waiters:  make([]chan struct{}, 0),
	}, nil
}

// Acquire acquires the specified weight from the semaphore.
//
// Blocks until the weight is available or the context is cancelled.
func (w *WeightedSemaphore) Acquire(ctx context.Context, weight int64) error {
	if w.closed.Load() {
		return ErrInvalidCapacity
	}

	if weight <= 0 {
		return errors.New("weight must be positive")
	}

	if weight > w.capacity {
		return errors.New("weight exceeds semaphore capacity")
	}

	w.mu.Lock()
	if w.current.Load()+weight <= w.capacity {
		w.current.Add(weight)
		w.mu.Unlock()
		return nil
	}

	// Need to wait
	ch := make(chan struct{})
	w.waiters = append(w.waiters, ch)
	w.mu.Unlock()

	select {
	case <-ch:
		return nil
	case <-ctx.Done():
		// Remove from waiters
		w.mu.Lock()
		for i, waiter := range w.waiters {
			if waiter == ch {
				w.waiters = append(w.waiters[:i], w.waiters[i+1:]...)
				break
			}
		}
		w.mu.Unlock()
		return ctx.Err()
	}
}

// TryAcquire attempts to acquire weight without blocking.
func (w *WeightedSemaphore) TryAcquire(weight int64) bool {
	if w.closed.Load() {
		return false
	}

	if weight <= 0 || weight > w.capacity {
		return false
	}

	w.mu.Lock()
	defer w.mu.Unlock()

	if w.current.Load()+weight <= w.capacity {
		w.current.Add(weight)
		return true
	}
	return false
}

// Release releases the specified weight back to the semaphore.
func (w *WeightedSemaphore) Release(weight int64) {
	if weight <= 0 {
		return
	}

	w.mu.Lock()
	defer w.mu.Unlock()

	w.current.Add(-weight)
	if w.current.Load() < 0 {
		w.current.Store(0)
	}

	// Notify waiters
	newWaiters := w.waiters[:0]
	for _, ch := range w.waiters {
		select {
		case ch <- struct{}{}:
			// Notified
		default:
			newWaiters = append(newWaiters, ch)
		}
	}
	w.waiters = newWaiters
}

// Close closes the weighted semaphore.
func (w *WeightedSemaphore) Close() {
	w.closed.Store(true)
}

// RateLimiter is a token bucket rate limiter.
//
// It allows a burst of requests up to the bucket size,
// then limits to a steady rate of requests.
//
// Example usage:
//
//	limiter := concurrency.NewRateLimiter(100, time.Second) // 100 req/sec
//	defer limiter.Stop()
//
//	ctx, cancel := context.WithTimeout(context.Background(), time.Second)
//	defer cancel()
//
//	if err := limiter.Wait(ctx); err != nil {
//	    // Handle rate limit
//	}
//	// Proceed with request...
type RateLimiter struct {
	rate       int
	interval   time.Duration
	tokens     chan struct{}
	ticker     *time.Ticker
	stopCh     chan struct{}
	stopOnce   sync.Once
	mu         sync.RWMutex
	stopped    bool
}

// NewRateLimiter creates a new rate limiter.
//
// The rate parameter specifies the maximum number of requests
// allowed per interval. The bucket size is equal to the rate.
func NewRateLimiter(rate int, interval time.Duration) *RateLimiter {
	if rate <= 0 {
		rate = 1
	}
	if interval <= 0 {
		interval = time.Second
	}

	rl := &RateLimiter{
		rate:     rate,
		interval: interval,
		tokens:   make(chan struct{}, rate),
		stopCh:   make(chan struct{}),
	}

	// Fill bucket initially
	for i := 0; i < rate; i++ {
		rl.tokens <- struct{}{}
	}

	// Start refill goroutine
	rl.ticker = time.NewTicker(interval / time.Duration(rate))
	go rl.refill()

	return rl
}

// refill periodically adds tokens to the bucket.
func (rl *RateLimiter) refill() {
	for {
		select {
		case <-rl.stopCh:
			return
		case <-rl.ticker.C:
			rl.mu.RLock()
			stopped := rl.stopped
			rl.mu.RUnlock()

			if stopped {
				return
			}

			select {
			case rl.tokens <- struct{}{}:
			default:
				// Bucket is full
			}
		}
	}
}

// Allow checks if a request is allowed without blocking.
//
// Returns true if a token is available, false otherwise.
// This is a non-blocking operation.
func (rl *RateLimiter) Allow() bool {
	rl.mu.RLock()
	if rl.stopped {
		rl.mu.RUnlock()
		return false
	}
	rl.mu.RUnlock()

	select {
	case <-rl.tokens:
		return true
	default:
		return false
	}
}

// Wait waits for a token to be available.
//
// Blocks until a token is available or the context is cancelled.
// Returns ctx.Err() if the context is cancelled.
func (rl *RateLimiter) Wait(ctx context.Context) error {
	rl.mu.RLock()
	if rl.stopped {
		rl.mu.RUnlock()
		return ErrRateLimiterStopped
	}
	rl.mu.RUnlock()

	select {
	case <-rl.tokens:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	case <-rl.stopCh:
		return ErrRateLimiterStopped
	}
}

// Reserve reserves a token for future use.
//
// Returns a Reservation that can be used to wait for the token.
// The returned reservation may already be ready (delay = 0).
func (rl *RateLimiter) Reserve() *Reservation {
	rl.mu.RLock()
	if rl.stopped {
		rl.mu.RUnlock()
		return &Reservation{ready: make(chan struct{})}
	}
	rl.mu.RUnlock()

	res := &Reservation{
		ready: make(chan struct{}, 1),
	}

	select {
	case <-rl.tokens:
		res.delay = 0
		res.ready <- struct{}{}
	default:
		// Calculate delay based on refill rate
		res.delay = rl.interval / time.Duration(rl.rate)
		go func() {
			time.Sleep(res.delay)
			select {
			case <-rl.stopCh:
				return
			default:
				<-rl.tokens
				res.ready <- struct{}{}
			}
		}()
	}

	return res
}

// Reservation represents a reserved token.
type Reservation struct {
	delay time.Duration
	ready chan struct{}
}

// Delay returns the time until the token is ready.
func (r *Reservation) Delay() time.Duration {
	return r.delay
}

// Ready returns a channel that's closed when the token is ready.
func (r *Reservation) Ready() <-chan struct{} {
	return r.ready
}

// Stop stops the rate limiter.
//
// After stopping, Allow returns false and Wait returns an error.
// This method is idempotent.
func (rl *RateLimiter) Stop() {
	rl.stopOnce.Do(func() {
		rl.mu.Lock()
		rl.stopped = true
		rl.mu.Unlock()

		rl.ticker.Stop()
		close(rl.stopCh)
	})
}

// IsStopped returns true if the rate limiter has been stopped.
func (rl *RateLimiter) IsStopped() bool {
	rl.mu.RLock()
	defer rl.mu.RUnlock()
	return rl.stopped
}

// AdaptiveRateLimiter is a rate limiter that adjusts its rate based on success/failure feedback.
type AdaptiveRateLimiter struct {
	currentRate  atomic.Int32
	minRate      int
	maxRate      int
	interval     time.Duration
	successCount atomic.Int32
	errorCount   atomic.Int32
	limiter      *RateLimiter
	mu           sync.RWMutex
	stopped      bool
}

// NewAdaptiveRateLimiter creates a new adaptive rate limiter.
//
// The rate limiter adjusts between minRate and maxRate based on
// feedback from success and failure calls.
func NewAdaptiveRateLimiter(minRate, maxRate int, interval time.Duration) *AdaptiveRateLimiter {
	if minRate <= 0 {
		minRate = 1
	}
	if maxRate < minRate {
		maxRate = minRate
	}

	arl := &AdaptiveRateLimiter{
		minRate:  minRate,
		maxRate:  maxRate,
		interval: interval,
	}
	arl.currentRate.Store(int32(minRate))
	arl.limiter = NewRateLimiter(minRate, interval)

	return arl
}

// Allow checks if a request is allowed.
func (arl *AdaptiveRateLimiter) Allow() bool {
	arl.mu.RLock()
	stopped := arl.stopped
	arl.mu.RUnlock()

	if stopped {
		return false
	}
	return arl.limiter.Allow()
}

// Wait waits for a token.
func (arl *AdaptiveRateLimiter) Wait(ctx context.Context) error {
	arl.mu.RLock()
	stopped := arl.stopped
	arl.mu.RUnlock()

	if stopped {
		return ErrRateLimiterStopped
	}
	return arl.limiter.Wait(ctx)
}

// Success reports a successful operation.
//
// On enough successes, the rate limit may be increased.
func (arl *AdaptiveRateLimiter) Success() {
	count := arl.successCount.Add(1)
	if count >= int32(arl.currentRate.Load()) {
		arl.adjustRate(1)
		arl.successCount.Store(0)
	}
}

// Failure reports a failed operation.
//
// On failures, the rate limit will be decreased.
func (arl *AdaptiveRateLimiter) Failure() {
	arl.errorCount.Add(1)
	arl.adjustRate(-1)
	arl.successCount.Store(0)
}

// adjustRate adjusts the current rate by delta.
func (arl *AdaptiveRateLimiter) adjustRate(delta int) {
	current := int(arl.currentRate.Load())
	newRate := current + delta

	if newRate < arl.minRate {
		newRate = arl.minRate
	}
	if newRate > arl.maxRate {
		newRate = arl.maxRate
	}

	if newRate != current {
		arl.currentRate.Store(int32(newRate))
		// Recreate limiter with new rate
		arl.limiter.Stop()
		arl.limiter = NewRateLimiter(newRate, arl.interval)
	}
}

// Stop stops the adaptive rate limiter.
func (arl *AdaptiveRateLimiter) Stop() {
	arl.mu.Lock()
	arl.stopped = true
	arl.mu.Unlock()
	arl.limiter.Stop()
}

// CurrentRate returns the current rate limit.
func (arl *AdaptiveRateLimiter) CurrentRate() int {
	return int(arl.currentRate.Load())
}

// Once is an object that will perform exactly one action.
//
// A Once must not be copied after first use.
type Once struct {
	done atomic.Uint32
	m    sync.Mutex
}

// Do calls the function f if and only if Do is being called for the
// first time for this instance of Once.
func (o *Once) Do(f func()) {
	if o.done.Load() == 0 {
		o.doSlow(f)
	}
}

func (o *Once) doSlow(f func()) {
	o.m.Lock()
	defer o.m.Unlock()
	if o.done.Load() == 0 {
		defer o.done.Store(1)
		f()
	}
}

// Reset allows the Once to be used again.
func (o *Once) Reset() {
	o.m.Lock()
	defer o.m.Unlock()
	o.done.Store(0)
}

// Done returns true if the Once has been triggered.
func (o *Once) Done() bool {
	return o.done.Load() != 0
}

// WaitGroup is a context-aware wait group.
//
// It extends sync.WaitGroup with context cancellation support.
type WaitGroup struct {
	wg sync.WaitGroup
}

// Add adds delta, which may be negative, to the WaitGroup counter.
func (w *WaitGroup) Add(delta int) {
	w.wg.Add(delta)
}

// Done decrements the WaitGroup counter by one.
func (w *WaitGroup) Done() {
	w.wg.Done()
}

// Wait blocks until the WaitGroup counter is zero.
func (w *WaitGroup) Wait() {
	w.wg.Wait()
}

// WaitContext waits with context cancellation.
//
// Returns ctx.Err() if the context is cancelled before the wait completes.
func (w *WaitGroup) WaitContext(ctx context.Context) error {
	done := make(chan struct{})
	go func() {
		w.wg.Wait()
		close(done)
	}()

	select {
	case <-done:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

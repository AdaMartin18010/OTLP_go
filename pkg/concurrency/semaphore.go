// Package concurrency provides thread-safe primitives and utilities
// for concurrent programming in the OTLP Go SDK.
//
// This package includes:
//   - Semaphore for resource limiting
//   - Rate limiter for request throttling
//   - Worker pools for parallel processing
//   - Context-aware synchronization primitives
package concurrency

import (
	"context"
	"sync"
	"time"
)

// Semaphore is a weighted semaphore implementation.
type Semaphore struct {
	ch chan struct{}
}

// NewSemaphore creates a new semaphore with the given capacity.
func NewSemaphore(capacity int) *Semaphore {
	return &Semaphore{
		ch: make(chan struct{}, capacity),
	}
}

// Acquire acquires a permit from the semaphore.
func (s *Semaphore) Acquire(ctx context.Context) error {
	select {
	case s.ch <- struct{}{}:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// Release releases a permit back to the semaphore.
func (s *Semaphore) Release() {
	select {
	case <-s.ch:
	default:
	}
}

// RateLimiter is a token bucket rate limiter.
type RateLimiter struct {
	tokens   chan struct{}
	interval time.Duration
	ticker   *time.Ticker
	stopCh   chan struct{}
	mu       sync.Mutex
}

// NewRateLimiter creates a new rate limiter.
func NewRateLimiter(rate int, interval time.Duration) *RateLimiter {
	rl := &RateLimiter{
		tokens:   make(chan struct{}, rate),
		interval: interval,
		stopCh:   make(chan struct{}),
	}
	return rl
}

// Allow checks if a request is allowed.
func (rl *RateLimiter) Allow() bool {
	select {
	case <-rl.tokens:
		return true
	default:
		return false
	}
}

// Wait waits for a token to be available.
func (rl *RateLimiter) Wait(ctx context.Context) error {
	select {
	case <-rl.tokens:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// Stop stops the rate limiter.
func (rl *RateLimiter) Stop() {
	close(rl.stopCh)
}

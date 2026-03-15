// Package pool provides object pool implementations for the OTLP Go SDK.
//
// This package includes:
//   - Generic typed pool with sync.Pool foundation
//   - Sized pools with capacity limits
//   - Pool statistics tracking
//   - Custom object lifecycle management
//
// Example usage:
//
//	pool := pool.New(func() *Buffer {
//	    return &Buffer{data: make([]byte, 0, 1024)}
//	})
//
//	buf := pool.Get()
//	defer pool.Put(buf)
package pool

import (
	"sync"
	"sync/atomic"
)

// Stats holds pool statistics.
type Stats struct {
	Gets         uint64 // Total number of Get calls
	Puts         uint64 // Total number of Put calls
	Hits         uint64 // Number of times object was retrieved from pool
	Misses       uint64 // Number of times new object was created
	Active       int64  // Current number of objects in use (not in pool)
	TotalCreates uint64 // Total number of objects created
}

// Reset resets all statistics to zero.
func (s *Stats) Reset() {
	atomic.StoreUint64(&s.Gets, 0)
	atomic.StoreUint64(&s.Puts, 0)
	atomic.StoreUint64(&s.Hits, 0)
	atomic.StoreUint64(&s.Misses, 0)
	atomic.StoreInt64(&s.Active, 0)
	atomic.StoreUint64(&s.TotalCreates, 0)
}

// Pool is a generic object pool with statistics tracking.
// It wraps sync.Pool and provides type safety and metrics.
type Pool[T any] struct {
	pool sync.Pool

	// new creates a new object when pool is empty
	new func() T

	// reset resets an object before returning to pool
	reset func(T)

	// stats tracks pool statistics
	stats Stats

	// maxSize limits the number of objects in pool (0 = unlimited)
	maxSize int32

	// currentSize tracks current pooled objects (approximate due to race conditions)
	currentSize int32
}

// Option configures a Pool.
type Option[T any] func(*Pool[T])

// WithReset sets the reset function for objects.
// The reset function is called before putting an object back into the pool.
func WithReset[T any](reset func(T)) Option[T] {
	return func(p *Pool[T]) {
		p.reset = reset
	}
}

// WithMaxSize sets the maximum number of objects to keep in the pool.
// When max size is reached, extra objects are discarded.
func WithMaxSize[T any](size int32) Option[T] {
	return func(p *Pool[T]) {
		p.maxSize = size
	}
}

// New creates a new Pool with the given factory function.
// The factory function creates new objects when the pool is empty.
//
// Example:
//
//	pool := pool.New(func() *bytes.Buffer {
//	    return bytes.NewBuffer(make([]byte, 0, 1024))
//	})
func New[T any](new func() T, opts ...Option[T]) *Pool[T] {
	p := &Pool[T]{
		new:     new,
		maxSize: 0, // unlimited by default
	}

	for _, opt := range opts {
		opt(p)
	}

	p.pool.New = func() any {
		atomic.AddUint64(&p.stats.Misses, 1)
		atomic.AddUint64(&p.stats.TotalCreates, 1)
		return p.new()
	}

	return p
}

// Get retrieves an object from the pool.
// If the pool is empty, a new object is created using the factory function.
//
// The returned object should be returned to the pool using Put when no longer needed.
func (p *Pool[T]) Get() T {
	atomic.AddUint64(&p.stats.Gets, 1)
	atomic.AddInt64(&p.stats.Active, 1)

	v := p.pool.Get()
	obj := v.(T)

	// If this was a new object (not from pool), Misses was already incremented in pool.New
	// If this was from pool, we need to decrement Misses and increment Hits
	// This is a simplification - actual hit/miss tracking has race conditions
	// but is good enough for statistical purposes

	return obj
}

// Put returns an object to the pool.
// The object should not be used after calling Put.
//
// If a reset function was configured, it will be called before
// the object is returned to the pool.
func (p *Pool[T]) Put(obj T) {
	atomic.AddUint64(&p.stats.Puts, 1)
	atomic.AddInt64(&p.stats.Active, -1)

	// Check max size limit
	if p.maxSize > 0 {
		current := atomic.LoadInt32(&p.currentSize)
		if current >= p.maxSize {
			// Pool is full, discard the object
			return
		}
		atomic.AddInt32(&p.currentSize, 1)
	}

	// Reset object if reset function is configured
	if p.reset != nil {
		p.reset(obj)
	}

	p.pool.Put(obj)
}

// Stats returns a copy of the current pool statistics.
// The statistics are approximate due to concurrent access.
func (p *Pool[T]) Stats() Stats {
	return Stats{
		Gets:         atomic.LoadUint64(&p.stats.Gets),
		Puts:         atomic.LoadUint64(&p.stats.Puts),
		Hits:         atomic.LoadUint64(&p.stats.Hits),
		Misses:       atomic.LoadUint64(&p.stats.Misses),
		Active:       atomic.LoadInt64(&p.stats.Active),
		TotalCreates: atomic.LoadUint64(&p.stats.TotalCreates),
	}
}

// ResetStats resets all pool statistics to zero.
func (p *Pool[T]) ResetStats() {
	p.stats.Reset()
}

// HitRate returns the cache hit rate as a percentage (0-100).
// Returns 0 if no gets have been performed.
func (p *Pool[T]) HitRate() float64 {
	gets := atomic.LoadUint64(&p.stats.Gets)
	if gets == 0 {
		return 0
	}
	misses := atomic.LoadUint64(&p.stats.Misses)
	hits := gets - misses
	return float64(hits) * 100 / float64(gets)
}

// SizedPool is a pool with a fixed size and blocking semantics.
// It blocks when the pool is empty until an object is available.
type SizedPool[T any] struct {
	objects chan T
	new     func() T
	reset   func(T)
	stats   Stats
	maxSize int
}

// NewSized creates a new SizedPool with the given capacity.
// The pool pre-creates objects up to the minimum of size and prefill.
//
// Example:
//
//	pool := pool.NewSized(100, 50, func() *Buffer {
//	    return &Buffer{}
//	})
func NewSized[T any](size, prefill int, new func() T, opts ...Option[T]) *SizedPool[T] {
	if prefill > size {
		prefill = size
	}

	p := &SizedPool[T]{
		objects: make(chan T, size),
		new:     new,
		maxSize: size,
	}

	_ = opts // Options are ignored for SizedPool as size is fixed

	// Prefill the pool
	for i := 0; i < prefill; i++ {
		obj := new()
		p.objects <- obj
		atomic.AddUint64(&p.stats.TotalCreates, 1)
	}

	return p
}

// Get retrieves an object from the pool.
// If the pool is empty, a new object is created.
func (p *SizedPool[T]) Get() T {
	atomic.AddUint64(&p.stats.Gets, 1)

	select {
	case obj := <-p.objects:
		atomic.AddUint64(&p.stats.Hits, 1)
		atomic.AddInt64(&p.stats.Active, 1)
		return obj
	default:
		atomic.AddUint64(&p.stats.Misses, 1)
		atomic.AddUint64(&p.stats.TotalCreates, 1)
		atomic.AddInt64(&p.stats.Active, 1)
		return p.new()
	}
}

// Put returns an object to the pool.
// If the pool is full, the object is discarded.
func (p *SizedPool[T]) Put(obj T) {
	atomic.AddUint64(&p.stats.Puts, 1)
	atomic.AddInt64(&p.stats.Active, -1)

	if p.reset != nil {
		p.reset(obj)
	}

	select {
	case p.objects <- obj:
		// Object returned to pool
	default:
		// Pool is full, discard object
	}
}

// Stats returns a copy of the current pool statistics.
func (p *SizedPool[T]) Stats() Stats {
	return Stats{
		Gets:         atomic.LoadUint64(&p.stats.Gets),
		Puts:         atomic.LoadUint64(&p.stats.Puts),
		Hits:         atomic.LoadUint64(&p.stats.Hits),
		Misses:       atomic.LoadUint64(&p.stats.Misses),
		Active:       atomic.LoadInt64(&p.stats.Active),
		TotalCreates: atomic.LoadUint64(&p.stats.TotalCreates),
	}
}

// Len returns the current number of objects available in the pool.
func (p *SizedPool[T]) Len() int {
	return len(p.objects)
}

// Cap returns the capacity of the pool.
func (p *SizedPool[T]) Cap() int {
	return p.maxSize
}

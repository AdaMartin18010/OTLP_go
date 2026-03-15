// Package pool provides object pool implementations for the OTLP Go SDK.
package pool

import (
	"bytes"
	"sync"
)

// DefaultBufferSize is the default initial capacity for pooled buffers.
const DefaultBufferSize = 4096

// MaxBufferSize is the maximum size a buffer can grow to before being discarded.
const MaxBufferSize = 1024 * 1024 // 1MB

// BufferPool is a specialized pool for bytes.Buffer objects.
// It provides efficient buffer reuse for serialization and encoding operations.
//
// Example usage:
//
//	bp := pool.NewBufferPool(100, DefaultBufferSize)
//	buf := bp.Get()
//	defer bp.Put(buf)
//	
//	// Use buffer
//	buf.WriteString("hello world")
//	data := buf.Bytes()
type BufferPool struct {
	pool      *Pool[*bytes.Buffer]
	poolSize  int32
	bufSize   int
}

// NewBufferPool creates a new BufferPool.
//
// Parameters:
//   - maxSize: maximum number of buffers to keep in the pool (0 = unlimited)
//   - bufSize: initial capacity for new buffers
//
// Example:
//
//	bp := pool.NewBufferPool(100, 4096)
func NewBufferPool(maxSize int32, bufSize int) *BufferPool {
	if bufSize <= 0 {
		bufSize = DefaultBufferSize
	}
	
	bp := &BufferPool{
		poolSize: maxSize,
		bufSize:  bufSize,
	}
	
	bp.pool = New(
		func() *bytes.Buffer {
			return bytes.NewBuffer(make([]byte, 0, bufSize))
		},
		WithMaxSize(maxSize),
		WithReset(func(b *bytes.Buffer) {
			if b.Cap() > MaxBufferSize {
				// Discard oversized buffers
				return
			}
			b.Reset()
		}),
	)
	
	return bp
}

// Get retrieves a buffer from the pool.
// The returned buffer is reset and ready for use.
func (bp *BufferPool) Get() *bytes.Buffer {
	return bp.pool.Get()
}

// Put returns a buffer to the pool.
// Buffers that have grown too large are discarded to prevent memory bloat.
func (bp *BufferPool) Put(buf *bytes.Buffer) {
	if buf == nil {
		return
	}
	
	// Discard oversized buffers to prevent memory bloat
	if buf.Cap() > MaxBufferSize {
		return
	}
	
	bp.pool.Put(buf)
}

// Stats returns statistics about the buffer pool.
func (bp *BufferPool) Stats() Stats {
	return bp.pool.Stats()
}

// ResetStats resets the pool statistics.
func (bp *BufferPool) ResetStats() {
	bp.pool.ResetStats()
}

// HitRate returns the cache hit rate as a percentage.
func (bp *BufferPool) HitRate() float64 {
	return bp.pool.HitRate()
}

// DefaultBufferPool is a package-level default buffer pool.
// It can be used for simple cases where a custom pool is not needed.
var DefaultBufferPool = NewBufferPool(0, DefaultBufferSize)

// GetBuffer retrieves a buffer from the default pool.
func GetBuffer() *bytes.Buffer {
	return DefaultBufferPool.Get()
}

// PutBuffer returns a buffer to the default pool.
func PutBuffer(buf *bytes.Buffer) {
	DefaultBufferPool.Put(buf)
}

// SizedBufferPool is a buffer pool with a fixed maximum size.
// When the pool is empty, Get() blocks until a buffer is available.
type SizedBufferPool struct {
	pool     *SizedPool[*bytes.Buffer]
	bufSize  int
}

// NewSizedBufferPool creates a new SizedBufferPool.
//
// Parameters:
//   - size: maximum number of buffers in the pool
//   - prefill: number of buffers to pre-create
//   - bufSize: initial capacity for new buffers
func NewSizedBufferPool(size, prefill, bufSize int) *SizedBufferPool {
	if bufSize <= 0 {
		bufSize = DefaultBufferSize
	}
	
	return &SizedBufferPool{
		pool: NewSized(
			size,
			prefill,
			func() *bytes.Buffer {
				return bytes.NewBuffer(make([]byte, 0, bufSize))
			},
		),
		bufSize: bufSize,
	}
}

// Get retrieves a buffer from the pool.
func (sbp *SizedBufferPool) Get() *bytes.Buffer {
	return sbp.pool.Get()
}

// Put returns a buffer to the pool.
func (sbp *SizedBufferPool) Put(buf *bytes.Buffer) {
	if buf == nil {
		return
	}
	
	if buf.Cap() > MaxBufferSize {
		return
	}
	
	buf.Reset()
	sbp.pool.Put(buf)
}

// Stats returns statistics about the buffer pool.
func (sbp *SizedBufferPool) Stats() Stats {
	return sbp.pool.Stats()
}

// Len returns the number of buffers currently in the pool.
func (sbp *SizedBufferPool) Len() int {
	return sbp.pool.Len()
}

// Cap returns the capacity of the pool.
func (sbp *SizedBufferPool) Cap() int {
	return sbp.pool.Cap()
}

// syncPoolBuffer is a wrapper for use with sync.Pool directly.
// Used internally for high-performance scenarios.
type syncPoolBuffer struct {
	pool *sync.Pool
}

// newSyncPoolBuffer creates an internal sync.Pool-based buffer pool.
func newSyncPoolBuffer(bufSize int) *syncPoolBuffer {
	return &syncPoolBuffer{
		pool: &sync.Pool{
			New: func() any {
				return bytes.NewBuffer(make([]byte, 0, bufSize))
			},
		},
	}
}

// Get retrieves a buffer from the pool.
func (spb *syncPoolBuffer) Get() *bytes.Buffer {
	return spb.pool.Get().(*bytes.Buffer)
}

// Put returns a buffer to the pool.
func (spb *syncPoolBuffer) Put(buf *bytes.Buffer) {
	if buf != nil && buf.Cap() <= MaxBufferSize {
		buf.Reset()
		spb.pool.Put(buf)
	}
}

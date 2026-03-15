// Package pool provides object pool implementations for the OTLP Go SDK.
//
// This package includes:
//   - Sync.Pool wrappers with type safety
//   - Sized pools with bounds
//   - Pool statistics
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


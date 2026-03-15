// Package performance provides performance optimization utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Memory pool management
//   - Allocation reduction techniques
//   - Benchmarking helpers
//   - Performance profiling integration
//
// Example usage:
//
//	pool := performance.NewSpanPool(1000)
//	span := pool.Get()
//	defer pool.Put(span)
//
//	// Use span...
package performance

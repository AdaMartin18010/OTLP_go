// Package profiling provides profiling and debugging utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - CPU profiling
//   - Memory profiling
//   - Goroutine dump capture
//   - Runtime metrics collection
//
// Example usage:
//
//	// Start CPU profiling
//	stop := profiling.StartCPUProfile("cpu.prof")
//	defer stop()
//
//	// Application code...
package profiling

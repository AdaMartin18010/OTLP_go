// Package runtime provides runtime introspection utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Go version detection
//   - Memory statistics
//   - GC metrics
//   - Goroutine monitoring
//
// Example usage:
//
//	stats := runtime.GetMemStats()
//	fmt.Printf("Alloc: %d MB\n", stats.Alloc/1024/1024)
package runtime

// Package concurrency provides thread-safe primitives and utilities
// for concurrent programming in the OTLP Go SDK.
//
// This package includes:
//   - Semaphore for resource limiting
//   - Rate limiter for request throttling
//   - Worker pools for parallel processing
//   - Context-aware synchronization primitives
//
// Example usage:
//
//	// Create a semaphore with capacity 10
//	sem := concurrency.NewSemaphore(10)
//	
//	// Acquire permit
//	if err := sem.Acquire(ctx); err != nil {
//	    return err
//	}
//	defer sem.Release()
//	
//	// Do work...


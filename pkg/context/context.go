// Package context provides context propagation utilities for the OTLP Go SDK.
//
// This package includes:
//   - Baggage propagation
//   - Context with timeout helpers
//   - Distributed context carriers
//   - W3C Trace Context support
//
// Example usage:
//
//	// Create context with baggage
//	ctx := context.WithBaggage(ctx, "user-id", "12345")
//	
//	// Extract baggage
//	value := context.GetBaggage(ctx, "user-id")
package context


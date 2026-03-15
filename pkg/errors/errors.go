// Package errors provides error handling utilities for the OTLP Go SDK.
//
// This package offers:
//   - Structured error wrapping
//   - Error categorization
//   - Stack trace capture
//   - Error retry detection
//
// Example usage:
//
//	if err != nil {
//	    return errors.Wrap(err, "failed to create exporter").
//	        WithCategory(errors.CategoryConfig).
//	        WithRetryable(true)
//	}
package errors


// Package options provides functional options pattern implementations
// for configuring OTLP Go SDK components.
//
// This package includes:
//   - Option types for all SDK components
//   - Validation functions
//   - Default option sets
//   - Option composition utilities
//
// Example usage:
//
//	opts := []options.TracerOption{
//	    options.WithSampler(sdktrace.AlwaysSample()),
//	    options.WithResource(resource),
//	}
//	tp := sdktrace.NewTracerProvider(opts...)
package options

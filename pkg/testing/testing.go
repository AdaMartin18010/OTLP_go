// Package testing provides testing utilities for the OTLP Go SDK.
//
// This package includes:
//   - Test span exporters
//   - In-memory metric readers
//   - Trace validation helpers
//   - Test resource fixtures
//
// Example usage:
//
//	exporter := testing.NewTestExporter()
//	tp := sdktrace.NewTracerProvider(
//	    sdktrace.WithSyncer(exporter),
//	)
//	
//	// Run code...
//	
//	spans := exporter.GetSpans()
//	assert.Len(t, spans, 1)
package testing


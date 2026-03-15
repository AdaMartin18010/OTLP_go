// Package resource provides OpenTelemetry resource utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Resource detection from environment
//   - Resource merging
//   - Resource validation
//   - Cloud provider detection (GCP, AWS, Azure)
//
// Example usage:
//
//	res, err := resource.New(ctx,
//	    resource.WithFromEnv(),
//	    resource.WithProcess(),
//	    resource.WithOS(),
//	    resource.WithContainer(),
//	)
package resource

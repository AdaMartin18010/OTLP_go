// Package otel provides OpenTelemetry SDK initialization and management
// for the OTLP Go SDK.
//
// This package handles:
//   - TracerProvider setup
//   - MeterProvider setup
//   - LoggerProvider setup
//   - Resource detection
//   - Graceful shutdown
//
// Example usage:
//
//	otelSDK, err := otel.Setup(ctx, otel.Config{
//	    ServiceName: "my-service",
//	    Endpoint:    "localhost:4317",
//	})
//	if err != nil {
//	    log.Fatal(err)
//	}
//	defer otelSDK.Shutdown(ctx)
package otel

// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This package implements:
//   - LoggerProvider for managing loggers
//   - BatchProcessor for efficient log export
//   - ConsoleExporter for development
//   - Severity levels (TRACE to FATAL)
//
// Example usage:
//
//	provider := logs.NewLoggerProvider(resource, processor, nil)
//	logger := provider.GetLogger("my-service")
//	
//	logger.Info(ctx, "Application started",
//	    attribute.String("version", "1.0.0"),
//	)


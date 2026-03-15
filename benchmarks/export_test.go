package benchmarks

import (
	"context"
	"testing"

	"go.opentelemetry.io/otel"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// TestBasicExport tests basic export functionality
func TestBasicExport(t *testing.T) {
	ctx := context.Background()
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(ctx)

	tracer := otel.Tracer("test")
	_, span := tracer.Start(ctx, "test-operation")
	span.End()
}

package benchmarks

import (
	"context"
	"testing"

	"go.opentelemetry.io/otel"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// TestSpanCreation tests span creation
func TestSpanCreation(t *testing.T) {
	ctx := context.Background()
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(ctx)

	tracer := otel.Tracer("test")
	_, span := tracer.Start(ctx, "test-operation")
	if span == nil {
		t.Error("Expected non-nil span")
	}
	span.End()
}

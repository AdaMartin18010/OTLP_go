package benchmarks

import (
	"context"
	"fmt"
	"io"
	"testing"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

// TestExportFunctionality tests basic export functionality
func TestExportFunctionality(t *testing.T) {
	tp := setupTracerProviderWithBatchSize(t, 100)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("test")
	ctx := context.Background()

	_, span := tracer.Start(ctx, "test-operation")
	span.SetAttributes(attribute.String("key", "value"))
	span.End()

	// Force flush to ensure export
	err := tp.ForceFlush(ctx)
	if err != nil {
		t.Errorf("ForceFlush failed: %v", err)
	}
}

// TestBatchSizes tests different batch sizes
func TestBatchSizes(t *testing.T) {
	batchSizes := []int{1, 10, 100}

	for _, size := range batchSizes {
		t.Run(fmt.Sprintf("batch-%d", size), func(t *testing.T) {
			tp := setupTracerProviderWithBatchSize(t, size)
			defer tp.Shutdown(context.Background())

			tracer := otel.Tracer("test")
			ctx := context.Background()

			// Create multiple spans
			for i := 0; i < size*2; i++ {
				_, span := tracer.Start(ctx, fmt.Sprintf("operation-%d", i))
				span.End()
			}

			err := tp.ForceFlush(ctx)
			if err != nil {
				t.Errorf("ForceFlush failed: %v", err)
			}
		})
	}
}

// setupTracerProviderWithBatchSizeT creates a tracer provider with custom batch size (for tests)
func setupTracerProviderWithBatchSize(t testing.TB, batchSize int) *sdktrace.TracerProvider {
	t.Helper()

	exporter, err := stdouttrace.New(
		stdouttrace.WithWriter(io.Discard),
	)
	if err != nil {
		t.Fatalf("Failed to create exporter: %v", err)
	}

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("test"),
		),
	)
	if err != nil {
		t.Fatalf("Failed to create resource: %v", err)
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter,
			sdktrace.WithMaxExportBatchSize(batchSize),
		),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	otel.SetTracerProvider(tp)
	return tp
}

// BenchmarkBatchExport benchmarks batch export with different batch sizes
func BenchmarkBatchExport(b *testing.B) {
	batchSizes := []int{100, 512, 1024, 2048}

	for _, size := range batchSizes {
		b.Run(fmt.Sprintf("%d", size), func(b *testing.B) {
			tp := setupTracerProviderWithBatchSize(b, size)
			defer tp.Shutdown(context.Background())

			tracer := otel.Tracer("benchmark")
			ctx := context.Background()

			b.ResetTimer()
			b.ReportAllocs()

			for i := 0; i < b.N; i++ {
				_, span := tracer.Start(ctx, "operation")
				span.SetAttributes(
					attribute.String("key", "value"),
				)
				span.End()
			}
		})
	}
}

// BenchmarkExportWithAttributes benchmarks export with varying attribute counts
func BenchmarkExportWithAttributes(b *testing.B) {
	attrCounts := []int{0, 5, 10, 20, 50}

	for _, count := range attrCounts {
		b.Run(fmt.Sprintf("%d", count), func(b *testing.B) {
			tp := setupTracerProviderWithBatchSize(b, 512)
			defer tp.Shutdown(context.Background())

			tracer := otel.Tracer("benchmark")
			ctx := context.Background()

			// Pre-generate attributes
			attrs := make([]attribute.KeyValue, count)
			for i := range count {
				attrs[i] = attribute.String("key", "value")
			}

			b.ResetTimer()
			b.ReportAllocs()

			for i := 0; i < b.N; i++ {
				_, span := tracer.Start(ctx, "operation")
				if count > 0 {
					span.SetAttributes(attrs...)
				}
				span.End()
			}
		})
	}
}

// BenchmarkExportWithEvents benchmarks export with varying event counts
func BenchmarkExportWithEvents(b *testing.B) {
	eventCounts := []int{0, 1, 5, 10}

	for _, count := range eventCounts {
		b.Run(fmt.Sprintf("%d", count), func(b *testing.B) {
			tp := setupTracerProviderWithBatchSize(b, 512)
			defer tp.Shutdown(context.Background())

			tracer := otel.Tracer("benchmark")
			ctx := context.Background()

			b.ResetTimer()
			b.ReportAllocs()

			for i := 0; i < b.N; i++ {
				_, span := tracer.Start(ctx, "operation")
				for range count {
					span.AddEvent("event")
				}
				span.End()
			}
		})
	}
}

// BenchmarkConcurrentExport benchmarks concurrent span export
func BenchmarkConcurrentExport(b *testing.B) {
	tp := setupTracerProviderWithBatchSize(b, 1024)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, span := tracer.Start(ctx, "operation")
			span.SetAttributes(
				attribute.String("key1", "value1"),
				attribute.Int("key2", 42),
			)
			span.End()
		}
	})
}

// BenchmarkExportLatency benchmarks export latency
func BenchmarkExportLatency(b *testing.B) {
	tp := setupTracerProviderWithBatchSize(b, 512)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()

	for i := 0; i < b.N; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.End()

		// Force flush to measure latency
		if i%100 == 0 {
			tp.ForceFlush(ctx)
		}
	}
}

// BenchmarkMemoryUsage benchmarks memory usage during export
func BenchmarkMemoryUsage(b *testing.B) {
	tp := setupTracerProviderWithBatchSize(b, 1024)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.SetAttributes(
			attribute.String("http.method", "GET"),
			attribute.String("http.url", "/api/users"),
			attribute.Int("http.status_code", 200),
		)
		span.AddEvent("event1")
		span.AddEvent("event2")
		span.End()
	}
}

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
			for i := 0; i < count; i++ {
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
				for j := 0; j < count; j++ {
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

// setupTracerProviderWithBatchSize creates a tracer provider with custom batch size
func setupTracerProviderWithBatchSize(b *testing.B, batchSize int) *sdktrace.TracerProvider {
	b.Helper()

	// Use stdout exporter that discards output for benchmarking
	exporter, err := stdouttrace.New(
		stdouttrace.WithWriter(io.Discard),
	)
	if err != nil {
		b.Fatalf("Failed to create exporter: %v", err)
	}

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("benchmark"),
		),
	)
	if err != nil {
		b.Fatalf("Failed to create resource: %v", err)
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

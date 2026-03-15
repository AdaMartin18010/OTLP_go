package benchmarks

import (
	"context"
	"testing"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

// TestSpanCreation tests basic span creation
func TestSpanCreation(t *testing.T) {
	tp := setupTracerProvider(t)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("test")
	ctx := context.Background()

	_, span := tracer.Start(ctx, "test-operation")
	if span == nil {
		t.Error("Expected non-nil span")
	}
	span.End()
}

// TestSpanWithAttributes tests span with attributes
func TestSpanWithAttributes(t *testing.T) {
	tp := setupTracerProvider(t)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("test")
	ctx := context.Background()

	_, span := tracer.Start(ctx, "test-operation",
		trace.WithAttributes(
			attribute.String("key1", "value1"),
			attribute.Int("key2", 42),
		),
	)
	span.End()
}

// TestNestedSpans tests nested span creation
func TestNestedSpans(t *testing.T) {
	tp := setupTracerProvider(t)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("test")
	ctx := context.Background()

	ctx1, span1 := tracer.Start(ctx, "parent")
	ctx2, span2 := tracer.Start(ctx1, "child1")
	_, span3 := tracer.Start(ctx2, "child2")
	span3.End()
	span2.End()
	span1.End()
}

// TestSpanSampling tests different sampling rates
func TestSpanSampling(t *testing.T) {
	samplers := []struct {
		name    string
		sampler sdktrace.Sampler
	}{
		{"AlwaysSample", sdktrace.AlwaysSample()},
		{"NeverSample", sdktrace.NeverSample()},
		{"TraceIDRatio_50%", sdktrace.TraceIDRatioBased(0.5)},
	}

	for _, s := range samplers {
		t.Run(s.name, func(t *testing.T) {
			tp := setupTracerProviderWithSampler(t, s.sampler)
			defer tp.Shutdown(context.Background())

			tracer := otel.Tracer("test")
			ctx := context.Background()

			_, span := tracer.Start(ctx, "test-operation")
			span.End()
		})
	}
}

// setupTracerProvider creates a tracer provider for testing
func setupTracerProvider(t testing.TB) *sdktrace.TracerProvider {
	t.Helper()

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("test"),
		),
	)
	if err != nil {
		t.Fatalf("Failed to create resource: %v", err)
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	otel.SetTracerProvider(tp)
	return tp
}

// setupTracerProviderWithSampler creates a tracer provider with custom sampler
func setupTracerProviderWithSampler(t testing.TB, sampler sdktrace.Sampler) *sdktrace.TracerProvider {
	t.Helper()

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("test"),
		),
	)
	if err != nil {
		t.Fatalf("Failed to create resource: %v", err)
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sampler),
	)

	otel.SetTracerProvider(tp)
	return tp
}

// BenchmarkSpanCreation benchmarks basic span creation
func BenchmarkSpanCreation(b *testing.B) {
	tp := setupTracerProvider(b)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.End()
	}
}

// BenchmarkSpanWithAttributes benchmarks span creation with attributes
func BenchmarkSpanWithAttributes(b *testing.B) {
	tp := setupTracerProvider(b)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_, span := tracer.Start(ctx, "operation",
			trace.WithAttributes(
				attribute.String("key1", "value1"),
				attribute.Int("key2", 42),
				attribute.Bool("key3", true),
			),
		)
		span.End()
	}
}

// BenchmarkSpanWithEvents benchmarks span with events
func BenchmarkSpanWithEvents(b *testing.B) {
	tp := setupTracerProvider(b)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.AddEvent("event1")
		span.AddEvent("event2", trace.WithAttributes(
			attribute.String("detail", "info"),
		))
		span.End()
	}
}

// BenchmarkNestedSpans benchmarks nested span creation
func BenchmarkNestedSpans(b *testing.B) {
	tp := setupTracerProvider(b)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		ctx1, span1 := tracer.Start(ctx, "parent")
		ctx2, span2 := tracer.Start(ctx1, "child1")
		_, span3 := tracer.Start(ctx2, "child2")
		span3.End()
		span2.End()
		span1.End()
	}
}

// BenchmarkConcurrentSpans benchmarks concurrent span creation
func BenchmarkConcurrentSpans(b *testing.B) {
	tp := setupTracerProvider(b)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("benchmark")
	ctx := context.Background()

	b.ResetTimer()
	b.ReportAllocs()

	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, span := tracer.Start(ctx, "operation")
			span.End()
		}
	})
}

// BenchmarkSpanSetAttributes benchmarks setting attributes
func BenchmarkSpanSetAttributes(b *testing.B) {
	tp := setupTracerProvider(b)
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
			attribute.Int64("http.response_size", 1024),
		)
		span.End()
	}
}

// BenchmarkSpanWithSampling benchmarks span with different sampling rates
func BenchmarkSpanWithSampling(b *testing.B) {
	samplers := []struct {
		name    string
		sampler sdktrace.Sampler
	}{
		{"AlwaysSample", sdktrace.AlwaysSample()},
		{"NeverSample", sdktrace.NeverSample()},
		{"TraceIDRatio_10%", sdktrace.TraceIDRatioBased(0.1)},
		{"TraceIDRatio_50%", sdktrace.TraceIDRatioBased(0.5)},
	}

	for _, s := range samplers {
		b.Run(s.name, func(b *testing.B) {
			tp := setupTracerProviderWithSampler(b, s.sampler)
			defer tp.Shutdown(context.Background())

			tracer := otel.Tracer("benchmark")
			ctx := context.Background()

			b.ResetTimer()
			b.ReportAllocs()

			for i := 0; i < b.N; i++ {
				_, span := tracer.Start(ctx, "operation")
				span.End()
			}
		})
	}
}

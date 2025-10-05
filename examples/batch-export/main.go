// Package main demonstrates batch export optimization
package main

import (
	"context"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

func main() {
	log.Println("Starting batch export example...")

	// Test different batch configurations
	configs := []struct {
		name      string
		batchSize int
		timeout   time.Duration
	}{
		{"Small Batch", 100, 1 * time.Second},
		{"Medium Batch", 512, 5 * time.Second},
		{"Large Batch", 2048, 10 * time.Second},
	}

	for _, cfg := range configs {
		log.Printf("\n=== Testing %s (size=%d, timeout=%v) ===", cfg.name, cfg.batchSize, cfg.timeout)
		testBatchConfig(cfg.batchSize, cfg.timeout)
		time.Sleep(2 * time.Second)
	}

	log.Println("\nBatch export example completed!")
}

func testBatchConfig(batchSize int, timeout time.Duration) {
	tp, err := initTracerProviderWithBatch(batchSize, timeout)
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)
	tracer := otel.Tracer("batch-export-example")

	start := time.Now()
	spanCount := 1000

	// Create many spans quickly
	for i := 0; i < spanCount; i++ {
		_, span := tracer.Start(context.Background(), "operation",
			trace.WithAttributes(
				attribute.Int("span.index", i),
			),
		)
		span.End()
	}

	// Force flush to ensure all spans are exported
	tp.ForceFlush(context.Background())

	elapsed := time.Since(start)
	log.Printf("Created and exported %d spans in %v (%.2f spans/sec)",
		spanCount, elapsed, float64(spanCount)/elapsed.Seconds())
}

func initTracerProviderWithBatch(batchSize int, timeout time.Duration) (*sdktrace.TracerProvider, error) {
	ctx := context.Background()

	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint("localhost:4317"),
		otlptracegrpc.WithInsecure(),
	)
	if err != nil {
		return nil, err
	}

	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("batch-export-example"),
		),
	)
	if err != nil {
		return nil, err
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter,
			sdktrace.WithMaxExportBatchSize(batchSize),
			sdktrace.WithBatchTimeout(timeout),
			sdktrace.WithMaxQueueSize(batchSize*4),
		),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	return tp, nil
}

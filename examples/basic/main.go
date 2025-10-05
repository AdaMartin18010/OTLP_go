// Package main demonstrates the most basic OTLP tracing example
package main

import (
	"context"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

func main() {
	log.Println("Starting basic OTLP tracing example...")

	// Initialize tracer provider
	tp, err := initTracerProvider()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Printf("Error shutting down tracer provider: %v", err)
		}
	}()

	// Set global tracer provider
	otel.SetTracerProvider(tp)

	// Get tracer
	tracer := otel.Tracer("basic-example")

	// Create root span
	ctx, span := tracer.Start(context.Background(), "main-operation",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			attribute.String("environment", "development"),
			attribute.String("version", "1.0.0"),
		),
	)
	defer span.End()

	log.Println("Created root span")

	// Simulate some work
	doWork(ctx, tracer)

	// Add event to span
	span.AddEvent("work-completed",
		trace.WithAttributes(
			attribute.Int("items.processed", 100),
		),
	)

	log.Println("Basic tracing example completed successfully!")
}

// initTracerProvider initializes an OTLP exporter and tracer provider
func initTracerProvider() (*sdktrace.TracerProvider, error) {
	ctx := context.Background()

	// Create OTLP trace exporter
	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint("localhost:4317"),
		otlptracegrpc.WithInsecure(),
	)
	if err != nil {
		return nil, err
	}

	// Create resource with service information
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("basic-example"),
			semconv.ServiceVersion("1.0.0"),
			semconv.DeploymentEnvironment("development"),
		),
	)
	if err != nil {
		return nil, err
	}

	// Create tracer provider
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	return tp, nil
}

// doWork simulates some work with child spans
func doWork(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "do-work",
		trace.WithSpanKind(trace.SpanKindInternal),
	)
	defer span.End()

	log.Println("Starting work...")

	// Simulate database query
	queryDatabase(ctx, tracer)

	// Simulate API call
	callExternalAPI(ctx, tracer)

	// Simulate processing
	processData(ctx, tracer)

	log.Println("Work completed")
}

// queryDatabase simulates a database query
func queryDatabase(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "query-database",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("db.system", "postgresql"),
			attribute.String("db.name", "mydb"),
			attribute.String("db.statement", "SELECT * FROM users WHERE id = ?"),
		),
	)
	defer span.End()

	// Simulate query execution
	time.Sleep(50 * time.Millisecond)

	span.SetAttributes(
		attribute.Int("db.rows_affected", 1),
	)

	log.Println("Database query completed")
}

// callExternalAPI simulates an external API call
func callExternalAPI(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "call-external-api",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("http.method", "GET"),
			attribute.String("http.url", "https://api.example.com/data"),
		),
	)
	defer span.End()

	// Simulate API call
	time.Sleep(100 * time.Millisecond)

	// Simulate successful response
	span.SetAttributes(
		attribute.Int("http.status_code", 200),
		attribute.Int("http.response_size", 1024),
	)
	span.SetStatus(codes.Ok, "API call successful")

	log.Println("External API call completed")
}

// processData simulates data processing
func processData(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "process-data",
		trace.WithSpanKind(trace.SpanKindInternal),
	)
	defer span.End()

	// Simulate processing
	for i := 0; i < 5; i++ {
		time.Sleep(20 * time.Millisecond)
		span.AddEvent("processing-item",
			trace.WithAttributes(
				attribute.Int("item.index", i),
			),
		)
	}

	span.SetAttributes(
		attribute.Int("items.processed", 5),
	)

	log.Println("Data processing completed")
}

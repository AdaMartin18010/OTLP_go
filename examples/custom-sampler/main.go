// Package main demonstrates custom sampling strategies
package main

import (
	"context"
	"log"
	"math/rand"
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
	log.Println("Starting custom sampler example...")

	// Initialize tracer provider with custom sampler
	tp, err := initTracerProviderWithCustomSampler()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Printf("Error shutting down tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)
	tracer := otel.Tracer("custom-sampler-example")

	// Simulate various requests
	for i := 0; i < 20; i++ {
		simulateRequest(tracer, i)
		time.Sleep(100 * time.Millisecond)
	}

	log.Println("Custom sampler example completed!")
}

// initTracerProviderWithCustomSampler initializes tracer with custom sampler
func initTracerProviderWithCustomSampler() (*sdktrace.TracerProvider, error) {
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
			semconv.ServiceName("custom-sampler-example"),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		return nil, err
	}

	// Create custom sampler
	customSampler := NewAdaptiveSampler(
		0.1, // Base sampling rate: 10%
		1.0, // Error sampling rate: 100%
		1.0, // Slow request sampling rate: 100%
		500, // Slow threshold: 500ms
	)

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(customSampler),
	)

	return tp, nil
}

// AdaptiveSampler implements custom sampling logic
type AdaptiveSampler struct {
	baseSamplingRate  float64
	errorSamplingRate float64
	slowSamplingRate  float64
	slowThresholdMs   int64
}

// NewAdaptiveSampler creates a new adaptive sampler
func NewAdaptiveSampler(base, errorRate, slowRate float64, slowThreshold int64) *AdaptiveSampler {
	return &AdaptiveSampler{
		baseSamplingRate:  base,
		errorSamplingRate: errorRate,
		slowSamplingRate:  slowRate,
		slowThresholdMs:   slowThreshold,
	}
}

// ShouldSample implements the Sampler interface
func (s *AdaptiveSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
	// Always sample if parent is sampled
	if p.ParentContext != nil {
		parentSpanContext := trace.SpanContextFromContext(p.ParentContext)
		if parentSpanContext.IsValid() && parentSpanContext.IsSampled() {
			return sdktrace.SamplingResult{
				Decision:   sdktrace.RecordAndSample,
				Attributes: []attribute.KeyValue{},
			}
		}
	}

	// Check for error status in attributes
	for _, attr := range p.Attributes {
		if attr.Key == "error" && attr.Value.AsBool() {
			log.Printf("Sampling: ERROR detected - 100%% sampling")
			return sdktrace.SamplingResult{
				Decision: sdktrace.RecordAndSample,
				Attributes: []attribute.KeyValue{
					attribute.String("sampling.reason", "error"),
				},
			}
		}

		// Check for slow requests
		if attr.Key == "duration_ms" {
			duration := attr.Value.AsInt64()
			if duration > s.slowThresholdMs {
				log.Printf("Sampling: SLOW request (%dms) - 100%% sampling", duration)
				return sdktrace.SamplingResult{
					Decision: sdktrace.RecordAndSample,
					Attributes: []attribute.KeyValue{
						attribute.String("sampling.reason", "slow_request"),
					},
				}
			}
		}
	}

	// Base sampling using probability
	if rand.Float64() < s.baseSamplingRate {
		log.Printf("Sampling: BASE rate - sampled")
		return sdktrace.SamplingResult{
			Decision: sdktrace.RecordAndSample,
			Attributes: []attribute.KeyValue{
				attribute.String("sampling.reason", "base_rate"),
			},
		}
	}

	log.Printf("Sampling: BASE rate - dropped")
	return sdktrace.SamplingResult{
		Decision: sdktrace.Drop,
	}
}

// Description returns the sampler description
func (s *AdaptiveSampler) Description() string {
	return "AdaptiveSampler{base=0.1,error=1.0,slow=1.0}"
}

// simulateRequest simulates various types of requests
func simulateRequest(tracer trace.Tracer, requestID int) {
	// Randomly generate request characteristics
	isError := rand.Float64() < 0.1     // 10% error rate
	isSlow := rand.Float64() < 0.15     // 15% slow requests
	duration := rand.Int63n(1000) + 100 // 100-1100ms

	if isSlow {
		duration = rand.Int63n(1000) + 600 // 600-1600ms for slow requests
	}

	// Create span with attributes for sampling decision
	attrs := []attribute.KeyValue{
		attribute.Int("request.id", requestID),
		attribute.Int64("duration_ms", duration),
		attribute.Bool("error", isError),
	}

	_, span := tracer.Start(
		context.Background(),
		"handle-request",
		trace.WithAttributes(attrs...),
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	// Simulate work
	time.Sleep(time.Duration(duration) * time.Millisecond)

	// Log request details
	status := "SUCCESS"
	if isError {
		status = "ERROR"
	}
	speed := "NORMAL"
	if isSlow {
		speed = "SLOW"
	}

	log.Printf("Request #%d: %s, %s, %dms", requestID, status, speed, duration)

	// Set span status
	if isError {
		span.SetAttributes(attribute.String("error.message", "simulated error"))
	}

	span.AddEvent("request-completed",
		trace.WithAttributes(
			attribute.String("status", status),
			attribute.String("speed", speed),
		),
	)
}

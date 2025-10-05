// Package main demonstrates custom span processor implementation
package main

import (
	"context"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

// CustomProcessor implements SpanProcessor interface
type CustomProcessor struct {
	name string
}

// NewCustomProcessor creates a new custom processor
func NewCustomProcessor(name string) *CustomProcessor {
	return &CustomProcessor{name: name}
}

// OnStart is called when a span starts
func (p *CustomProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	log.Printf("[%s] Span started: %s", p.name, s.Name())

	// Add custom attributes
	s.SetAttributes(
		attribute.String("processor.name", p.name),
		attribute.Int64("processor.start_time", time.Now().Unix()),
	)

	// Filter sensitive attributes
	p.filterSensitiveData(s)
}

// OnEnd is called when a span ends
func (p *CustomProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	duration := s.EndTime().Sub(s.StartTime())
	log.Printf("[%s] Span ended: %s (duration: %v)", p.name, s.Name(), duration)

	// Log slow spans
	if duration > 100*time.Millisecond {
		log.Printf("[%s] ⚠️  SLOW SPAN: %s took %v", p.name, s.Name(), duration)
	}

	// Log error spans
	if s.Status().Code == 2 { // Error code
		log.Printf("[%s] ❌ ERROR SPAN: %s - %s", p.name, s.Name(), s.Status().Description)
	}
}

// Shutdown is called when the processor is shut down
func (p *CustomProcessor) Shutdown(ctx context.Context) error {
	log.Printf("[%s] Processor shutting down", p.name)
	return nil
}

// ForceFlush is called to flush any buffered spans
func (p *CustomProcessor) ForceFlush(ctx context.Context) error {
	log.Printf("[%s] Force flush", p.name)
	return nil
}

// filterSensitiveData removes or masks sensitive attributes
func (p *CustomProcessor) filterSensitiveData(s sdktrace.ReadWriteSpan) {
	// Example: Remove password attributes
	sensitiveKeys := []string{"password", "api_key", "secret", "token"}

	for _, key := range sensitiveKeys {
		// In a real implementation, you would check and remove these attributes
		// This is a simplified example
		_ = key
	}
}

// MetricsProcessor collects metrics from spans
type MetricsProcessor struct {
	spanCount    int64
	errorCount   int64
	totalLatency time.Duration
}

// NewMetricsProcessor creates a new metrics processor
func NewMetricsProcessor() *MetricsProcessor {
	return &MetricsProcessor{}
}

func (p *MetricsProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	// Nothing to do on start
}

func (p *MetricsProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	p.spanCount++
	p.totalLatency += s.EndTime().Sub(s.StartTime())

	if s.Status().Code == 2 { // Error
		p.errorCount++
	}
}

func (p *MetricsProcessor) Shutdown(ctx context.Context) error {
	p.printMetrics()
	return nil
}

func (p *MetricsProcessor) ForceFlush(ctx context.Context) error {
	return nil
}

func (p *MetricsProcessor) printMetrics() {
	avgLatency := time.Duration(0)
	if p.spanCount > 0 {
		avgLatency = p.totalLatency / time.Duration(p.spanCount)
	}

	log.Println("\n=== Metrics Summary ===")
	log.Printf("Total Spans: %d", p.spanCount)
	log.Printf("Error Spans: %d", p.errorCount)
	log.Printf("Average Latency: %v", avgLatency)
	if p.spanCount > 0 {
		log.Printf("Error Rate: %.2f%%", float64(p.errorCount)/float64(p.spanCount)*100)
	}
}

func main() {
	log.Println("Starting custom processor example...")

	// Initialize tracer provider with custom processors
	tp, err := initTracerProviderWithCustomProcessors()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)
	tracer := otel.Tracer("custom-processor-example")

	// Create various spans
	ctx := context.Background()

	// Normal span
	_, span1 := tracer.Start(ctx, "fast-operation")
	time.Sleep(10 * time.Millisecond)
	span1.End()

	// Slow span
	_, span2 := tracer.Start(ctx, "slow-operation")
	time.Sleep(150 * time.Millisecond)
	span2.End()

	// Error span
	_, span3 := tracer.Start(ctx, "error-operation")
	span3.SetAttributes(attribute.String("error", "something went wrong"))
	time.Sleep(20 * time.Millisecond)
	span3.End()

	// More spans
	for i := 0; i < 10; i++ {
		_, span := tracer.Start(ctx, "batch-operation")
		time.Sleep(5 * time.Millisecond)
		span.End()
	}

	log.Println("\nCustom processor example completed!")
	time.Sleep(1 * time.Second) // Allow processors to finish
}

func initTracerProviderWithCustomProcessors() (*sdktrace.TracerProvider, error) {
	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("custom-processor-example"),
		),
	)
	if err != nil {
		return nil, err
	}

	// Create custom processors
	customProc := NewCustomProcessor("MyProcessor")
	metricsProc := NewMetricsProcessor()

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithResource(res),
		sdktrace.WithSpanProcessor(customProc),
		sdktrace.WithSpanProcessor(metricsProc),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	return tp, nil
}

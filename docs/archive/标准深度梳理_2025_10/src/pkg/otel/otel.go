package otel

import (
	"context"
	"fmt"
	"log"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"

	"otlp-go-monitoring/src/pkg/config"
)

// OTelManager manages OpenTelemetry SDK lifecycle
type OTelManager struct {
	tracerProvider *sdktrace.TracerProvider
	meterProvider  metric.MeterProvider
	resource       *resource.Resource
}

// InitializeGlobalOTel initializes the global OpenTelemetry SDK
func InitializeGlobalOTel(ctx context.Context, cfg *config.OTLPConfig) error {
	// Create resource
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName(cfg.ServiceName),
			semconv.ServiceVersion(cfg.ServiceVersion),
			semconv.DeploymentEnvironment(cfg.Environment),
		),
	)
	if err != nil {
		return fmt.Errorf("failed to create resource: %w", err)
	}

	// Create OTLP trace exporter
	traceExporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint(cfg.Endpoint),
		otlptracegrpc.WithInsecure(),
	)
	if err != nil {
		return fmt.Errorf("failed to create trace exporter: %w", err)
	}

	// Create tracer provider
	tracerProvider := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(traceExporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.TraceIDRatioBased(cfg.SamplingRate)),
	)

	// Set global providers
	otel.SetTracerProvider(tracerProvider)
	otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
		propagation.TraceContext{},
		propagation.Baggage{},
	))

	// Create manager
	manager := &OTelManager{
		tracerProvider: tracerProvider,
		resource:       res,
	}

	// Store globally for shutdown
	globalManager = manager

	log.Printf("OpenTelemetry initialized successfully")
	return nil
}

// ShutdownGlobalOTel shuts down the global OpenTelemetry SDK
func ShutdownGlobalOTel(ctx context.Context) error {
	if globalManager != nil && globalManager.tracerProvider != nil {
		if err := globalManager.tracerProvider.Shutdown(ctx); err != nil {
			return fmt.Errorf("failed to shutdown tracer provider: %w", err)
		}
		log.Printf("OpenTelemetry shutdown completed")
	}
	return nil
}

// GetTracer returns a tracer instance
func GetTracer(name string) trace.Tracer {
	return otel.Tracer(name)
}

// GetMeter returns a meter instance
func GetMeter(name string) metric.Meter {
	return otel.Meter(name)
}

// GetTextMapPropagator returns the global text map propagator
func GetTextMapPropagator() propagation.TextMapPropagator {
	return otel.GetTextMapPropagator()
}

// Helper functions for attributes
func AttributeString(key, value string) attribute.KeyValue {
	return attribute.String(key, value)
}

func AttributeInt(key string, value int) attribute.KeyValue {
	return attribute.Int(key, value)
}

func AttributeInt64(key string, value int64) attribute.KeyValue {
	return attribute.Int64(key, value)
}

func AttributeFloat64(key string, value float64) attribute.KeyValue {
	return attribute.Float64(key, value)
}

func AttributeBool(key string, value bool) attribute.KeyValue {
	return attribute.Bool(key, value)
}

func AttributeStringSlice(key string, value []string) attribute.KeyValue {
	return attribute.StringSlice(key, value)
}

func AttributeInt64Slice(key string, value []int64) attribute.KeyValue {
	return attribute.Int64Slice(key, value)
}

// Global manager instance
var globalManager *OTelManager

// Package main demonstrates OTLP metrics collection
package main

import (
	"context"
	"log"
	"math/rand"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
	"go.opentelemetry.io/otel/metric"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func main() {
	log.Println("Starting metrics collection example...")

	// Initialize meter provider
	mp, err := initMeterProvider()
	if err != nil {
		log.Fatalf("Failed to initialize meter provider: %v", err)
	}
	defer func() {
		if err := mp.Shutdown(context.Background()); err != nil {
			log.Printf("Error shutting down meter provider: %v", err)
		}
	}()

	otel.SetMeterProvider(mp)

	// Get meter
	meter := otel.Meter("metrics-example")

	// Create metrics
	requestCounter, _ := meter.Int64Counter(
		"http.server.requests",
		metric.WithDescription("Total number of HTTP requests"),
		metric.WithUnit("{request}"),
	)

	requestDuration, _ := meter.Float64Histogram(
		"http.server.duration",
		metric.WithDescription("HTTP request duration"),
		metric.WithUnit("ms"),
	)

	activeConnections, _ := meter.Int64UpDownCounter(
		"http.server.active_connections",
		metric.WithDescription("Number of active connections"),
		metric.WithUnit("{connection}"),
	)

	cpuUsage, _ := meter.Float64ObservableGauge(
		"system.cpu.usage",
		metric.WithDescription("CPU usage percentage"),
		metric.WithUnit("%"),
	)

	// Register callback for observable gauge
	_, err = meter.RegisterCallback(
		func(ctx context.Context, o metric.Observer) error {
			// Simulate CPU usage
			usage := rand.Float64() * 100
			o.ObserveFloat64(cpuUsage, usage,
				metric.WithAttributes(
					attribute.String("cpu", "0"),
				),
			)
			return nil
		},
		cpuUsage,
	)
	if err != nil {
		log.Fatalf("Failed to register callback: %v", err)
	}

	// Simulate HTTP server metrics
	ctx := context.Background()
	for i := 0; i < 100; i++ {
		// Simulate request
		method := []string{"GET", "POST", "PUT", "DELETE"}[rand.Intn(4)]
		status := []int{200, 201, 400, 404, 500}[rand.Intn(5)]
		duration := rand.Float64() * 1000 // 0-1000ms

		attrs := []attribute.KeyValue{
			attribute.String("http.method", method),
			attribute.Int("http.status_code", status),
			attribute.String("http.route", "/api/users"),
		}

		// Increment request counter
		requestCounter.Add(ctx, 1, metric.WithAttributes(attrs...))

		// Record request duration
		requestDuration.Record(ctx, duration, metric.WithAttributes(attrs...))

		// Update active connections
		if i%10 == 0 {
			activeConnections.Add(ctx, 1)
		}
		if i%15 == 0 {
			activeConnections.Add(ctx, -1)
		}

		log.Printf("Request #%d: %s %d %.2fms", i+1, method, status, duration)
		time.Sleep(100 * time.Millisecond)
	}

	log.Println("Metrics collection example completed!")
	time.Sleep(2 * time.Second) // Allow metrics to be exported
}

// initMeterProvider initializes the meter provider
func initMeterProvider() (*sdkmetric.MeterProvider, error) {
	ctx := context.Background()

	// Create OTLP metric exporter
	exporter, err := otlpmetricgrpc.New(ctx,
		otlpmetricgrpc.WithEndpoint("localhost:4317"),
		otlpmetricgrpc.WithInsecure(),
	)
	if err != nil {
		return nil, err
	}

	// Create resource
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("metrics-example"),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		return nil, err
	}

	// Create meter provider
	mp := sdkmetric.NewMeterProvider(
		sdkmetric.WithReader(sdkmetric.NewPeriodicReader(exporter,
			sdkmetric.WithInterval(5*time.Second),
		)),
		sdkmetric.WithResource(res),
	)

	return mp, nil
}

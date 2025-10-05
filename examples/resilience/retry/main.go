// Package main demonstrates retry mechanism with exponential backoff
package main

import (
	"context"
	"errors"
	"log"
	"math"
	"math/rand"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

// RetryConfig holds retry configuration
type RetryConfig struct {
	InitialInterval time.Duration
	MaxInterval     time.Duration
	MaxElapsedTime  time.Duration
	Multiplier      float64
	MaxRetries      int
}

// DefaultRetryConfig returns default retry configuration
func DefaultRetryConfig() RetryConfig {
	return RetryConfig{
		InitialInterval: 1 * time.Second,
		MaxInterval:     30 * time.Second,
		MaxElapsedTime:  5 * time.Minute,
		Multiplier:      2.0,
		MaxRetries:      5,
	}
}

// RetryWithBackoff executes function with exponential backoff retry
func RetryWithBackoff(ctx context.Context, tracer trace.Tracer, fn func() error, config RetryConfig) error {
	ctx, span := tracer.Start(ctx, "retry-with-backoff")
	defer span.End()

	interval := config.InitialInterval
	elapsed := time.Duration(0)
	attempt := 0

	for {
		attempt++
		_, attemptSpan := tracer.Start(ctx, "retry-attempt",
			trace.WithAttributes(
				attribute.Int("retry.attempt", attempt),
				attribute.String("retry.interval", interval.String()),
			),
		)

		err := fn()
		attemptSpan.End()

		if err == nil {
			span.SetStatus(codes.Ok, "success")
			span.SetAttributes(attribute.Int("retry.total_attempts", attempt))
			log.Printf("✓ Success on attempt %d", attempt)
			return nil
		}

		attemptSpan.RecordError(err)
		log.Printf("✗ Attempt %d failed: %v", attempt, err)

		// Check if we should retry
		if attempt >= config.MaxRetries {
			span.SetStatus(codes.Error, "max retries exceeded")
			span.SetAttributes(attribute.Int("retry.total_attempts", attempt))
			log.Printf("✗ Max retries (%d) exceeded", config.MaxRetries)
			return err
		}

		if elapsed >= config.MaxElapsedTime {
			span.SetStatus(codes.Error, "max elapsed time exceeded")
			span.SetAttributes(
				attribute.Int("retry.total_attempts", attempt),
				attribute.String("retry.total_elapsed", elapsed.String()),
			)
			log.Printf("✗ Max elapsed time (%v) exceeded", config.MaxElapsedTime)
			return err
		}

		// Wait before retry
		log.Printf("⏳ Waiting %v before retry...", interval)
		time.Sleep(interval)

		// Update for next iteration
		elapsed += interval
		interval = time.Duration(math.Min(
			float64(interval)*config.Multiplier,
			float64(config.MaxInterval),
		))
	}
}

func main() {
	log.Println("Starting retry mechanism example...")

	tp, err := initTracerProvider()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)
	tracer := otel.Tracer("retry-example")

	// Example 1: Successful retry
	log.Println("\n=== Example 1: Successful Retry ===")
	ctx := context.Background()
	err = RetryWithBackoff(ctx, tracer, func() error {
		return simulateFlakeyService(0.7) // 70% failure rate
	}, DefaultRetryConfig())

	if err != nil {
		log.Printf("Final result: FAILED")
	} else {
		log.Printf("Final result: SUCCESS")
	}

	// Example 2: Max retries exceeded
	log.Println("\n=== Example 2: Max Retries Exceeded ===")
	config := DefaultRetryConfig()
	config.MaxRetries = 3
	err = RetryWithBackoff(ctx, tracer, func() error {
		return simulateFlakeyService(1.0) // Always fails
	}, config)

	if err != nil {
		log.Printf("Final result: FAILED (expected)")
	}

	log.Println("\nRetry mechanism example completed!")
}

// simulateFlakeyService simulates a service that fails sometimes
func simulateFlakeyService(failureRate float64) error {
	if rand.Float64() < failureRate {
		return errors.New("service temporarily unavailable")
	}
	return nil
}

func initTracerProvider() (*sdktrace.TracerProvider, error) {
	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("retry-example"),
		),
	)
	if err != nil {
		return nil, err
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	return tp, nil
}

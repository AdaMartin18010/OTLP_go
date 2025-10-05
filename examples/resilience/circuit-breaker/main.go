// Package main demonstrates circuit breaker pattern for fault tolerance
package main

import (
	"context"
	"errors"
	"log"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

// State represents the circuit breaker state
type State int

const (
	StateClosed State = iota
	StateOpen
	StateHalfOpen
)

func (s State) String() string {
	return []string{"CLOSED", "OPEN", "HALF_OPEN"}[s]
}

// CircuitBreaker implements the circuit breaker pattern
type CircuitBreaker struct {
	maxFailures  int
	timeout      time.Duration
	state        State
	failures     int
	lastFailTime time.Time
	mu           sync.Mutex
	tracer       trace.Tracer
}

// NewCircuitBreaker creates a new circuit breaker
func NewCircuitBreaker(maxFailures int, timeout time.Duration, tracer trace.Tracer) *CircuitBreaker {
	return &CircuitBreaker{
		maxFailures: maxFailures,
		timeout:     timeout,
		state:       StateClosed,
		tracer:      tracer,
	}
}

var ErrCircuitOpen = errors.New("circuit breaker is open")

// Call executes the function with circuit breaker protection
func (cb *CircuitBreaker) Call(ctx context.Context, fn func() error) error {
	ctx, span := cb.tracer.Start(ctx, "circuit-breaker-call",
		trace.WithAttributes(
			attribute.String("circuit.state", cb.getState().String()),
		),
	)
	defer span.End()

	cb.mu.Lock()
	state := cb.state

	if state == StateOpen {
		if time.Since(cb.lastFailTime) > cb.timeout {
			log.Printf("[Circuit Breaker] Transitioning to HALF_OPEN")
			cb.state = StateHalfOpen
			state = StateHalfOpen
		} else {
			cb.mu.Unlock()
			span.SetStatus(codes.Error, "circuit breaker is open")
			span.SetAttributes(attribute.Int("circuit.failures", cb.failures))
			return ErrCircuitOpen
		}
	}
	cb.mu.Unlock()

	// Execute function
	err := fn()

	cb.mu.Lock()
	defer cb.mu.Unlock()

	if err != nil {
		cb.failures++
		cb.lastFailTime = time.Now()
		span.RecordError(err)
		span.SetAttributes(
			attribute.Int("circuit.failures", cb.failures),
			attribute.String("circuit.new_state", cb.state.String()),
		)

		if cb.failures >= cb.maxFailures {
			log.Printf("[Circuit Breaker] Opening circuit (failures: %d)", cb.failures)
			cb.state = StateOpen
			span.AddEvent("circuit-opened")
		}
		return err
	}

	// Success
	if state == StateHalfOpen {
		log.Printf("[Circuit Breaker] Closing circuit (recovered)")
		cb.state = StateClosed
		span.AddEvent("circuit-closed")
	}
	cb.failures = 0
	span.SetStatus(codes.Ok, "success")
	return nil
}

func (cb *CircuitBreaker) getState() State {
	cb.mu.Lock()
	defer cb.mu.Unlock()
	return cb.state
}

func main() {
	log.Println("Starting circuit breaker example...")

	tp, err := initTracerProvider()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)
	tracer := otel.Tracer("circuit-breaker-example")

	// Create circuit breaker
	cb := NewCircuitBreaker(
		3,             // Max 3 failures
		5*time.Second, // 5 second timeout
		tracer,
	)

	// Simulate service calls
	ctx := context.Background()
	for i := 0; i < 20; i++ {
		time.Sleep(500 * time.Millisecond)

		err := cb.Call(ctx, func() error {
			return simulateServiceCall(i)
		})

		if err != nil {
			if errors.Is(err, ErrCircuitOpen) {
				log.Printf("Request #%d: REJECTED (circuit open)", i+1)
			} else {
				log.Printf("Request #%d: FAILED (%v)", i+1, err)
			}
		} else {
			log.Printf("Request #%d: SUCCESS", i+1)
		}
	}

	log.Println("Circuit breaker example completed!")
}

// simulateServiceCall simulates a service that fails sometimes
func simulateServiceCall(requestID int) error {
	// Fail requests 5-10
	if requestID >= 5 && requestID <= 10 {
		return errors.New("service unavailable")
	}
	return nil
}

func initTracerProvider() (*sdktrace.TracerProvider, error) {
	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("circuit-breaker-example"),
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

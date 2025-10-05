// Package main demonstrates context propagation between services
package main

import (
	"context"
	"fmt"
	"io"
	"log"
	"net/http"
	"time"

	"go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/baggage"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

const (
	serviceAPort = ":8081"
	serviceBPort = ":8082"
)

func main() {
	log.Println("Starting context propagation example...")

	// Initialize tracer provider
	tp, err := initTracerProvider("context-propagation-example")
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Printf("Error shutting down tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)

	// Set up propagators (W3C Trace Context + Baggage)
	otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
		propagation.TraceContext{},
		propagation.Baggage{},
	))

	// Start Service B (downstream service)
	go startServiceB()
	time.Sleep(1 * time.Second) // Wait for service B to start

	// Start Service A (upstream service)
	go startServiceA()
	time.Sleep(1 * time.Second) // Wait for service A to start

	// Make a request to Service A
	makeRequest()

	// Keep running for a bit to allow traces to be exported
	time.Sleep(3 * time.Second)
	log.Println("Context propagation example completed!")
}

// initTracerProvider initializes the tracer provider
func initTracerProvider(serviceName string) (*sdktrace.TracerProvider, error) {
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
			semconv.ServiceName(serviceName),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		return nil, err
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	return tp, nil
}

// startServiceA starts the upstream service
func startServiceA() {
	tracer := otel.Tracer("service-a")

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ctx := r.Context()

		// Extract baggage from incoming request
		bag := baggage.FromContext(ctx)
		userID := bag.Member("user.id").Value()
		sessionID := bag.Member("session.id").Value()

		log.Printf("[Service A] Received request - User: %s, Session: %s", userID, sessionID)

		// Create span for this service
		ctx, span := tracer.Start(ctx, "service-a-handler",
			trace.WithSpanKind(trace.SpanKindServer),
			trace.WithAttributes(
				attribute.String("user.id", userID),
				attribute.String("session.id", sessionID),
			),
		)
		defer span.End()

		// Call Service B
		callServiceB(ctx)

		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, "Service A processed request for user %s\n", userID)
	})

	// Wrap handler with otelhttp for automatic instrumentation
	wrappedHandler := otelhttp.NewHandler(handler, "service-a")

	log.Printf("[Service A] Starting on %s", serviceAPort)
	if err := http.ListenAndServe(serviceAPort, wrappedHandler); err != nil {
		log.Fatalf("Service A failed: %v", err)
	}
}

// startServiceB starts the downstream service
func startServiceB() {
	tracer := otel.Tracer("service-b")

	handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ctx := r.Context()

		// Extract baggage
		bag := baggage.FromContext(ctx)
		userID := bag.Member("user.id").Value()
		sessionID := bag.Member("session.id").Value()

		log.Printf("[Service B] Received request - User: %s, Session: %s", userID, sessionID)

		// Create span for this service
		ctx, span := tracer.Start(ctx, "service-b-handler",
			trace.WithSpanKind(trace.SpanKindServer),
			trace.WithAttributes(
				attribute.String("user.id", userID),
				attribute.String("session.id", sessionID),
			),
		)
		defer span.End()

		// Simulate some work
		time.Sleep(50 * time.Millisecond)

		// Add event
		span.AddEvent("processing-complete",
			trace.WithAttributes(
				attribute.String("result", "success"),
			),
		)

		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, "Service B processed request for user %s\n", userID)
	})

	wrappedHandler := otelhttp.NewHandler(handler, "service-b")

	log.Printf("[Service B] Starting on %s", serviceBPort)
	if err := http.ListenAndServe(serviceBPort, wrappedHandler); err != nil {
		log.Fatalf("Service B failed: %v", err)
	}
}

// callServiceB makes a request to Service B
func callServiceB(ctx context.Context) {
	tracer := otel.Tracer("service-a")

	ctx, span := tracer.Start(ctx, "call-service-b",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("http.method", "GET"),
			attribute.String("http.url", "http://localhost"+serviceBPort),
		),
	)
	defer span.End()

	// Create HTTP client with otelhttp instrumentation
	client := http.Client{
		Transport: otelhttp.NewTransport(http.DefaultTransport),
	}

	req, err := http.NewRequestWithContext(ctx, "GET", "http://localhost"+serviceBPort, nil)
	if err != nil {
		log.Printf("Failed to create request: %v", err)
		return
	}

	resp, err := client.Do(req)
	if err != nil {
		log.Printf("Failed to call Service B: %v", err)
		span.RecordError(err)
		return
	}
	defer resp.Body.Close()

	body, _ := io.ReadAll(resp.Body)
	log.Printf("[Service A] Response from Service B: %s", string(body))

	span.SetAttributes(
		attribute.Int("http.status_code", resp.StatusCode),
	)
}

// makeRequest makes an initial request to Service A
func makeRequest() {
	tracer := otel.Tracer("client")

	ctx, span := tracer.Start(context.Background(), "client-request",
		trace.WithSpanKind(trace.SpanKindClient),
	)
	defer span.End()

	// Create baggage with user context
	member1, _ := baggage.NewMember("user.id", "user-123")
	member2, _ := baggage.NewMember("session.id", "session-abc")
	bag, _ := baggage.New(member1, member2)
	ctx = baggage.ContextWithBaggage(ctx, bag)

	log.Println("[Client] Making request with baggage: user.id=user-123, session.id=session-abc")

	// Create HTTP client
	client := http.Client{
		Transport: otelhttp.NewTransport(http.DefaultTransport),
	}

	req, err := http.NewRequestWithContext(ctx, "GET", "http://localhost"+serviceAPort, nil)
	if err != nil {
		log.Printf("Failed to create request: %v", err)
		return
	}

	resp, err := client.Do(req)
	if err != nil {
		log.Printf("Failed to call Service A: %v", err)
		span.RecordError(err)
		return
	}
	defer resp.Body.Close()

	body, _ := io.ReadAll(resp.Body)
	log.Printf("[Client] Response: %s", string(body))
}

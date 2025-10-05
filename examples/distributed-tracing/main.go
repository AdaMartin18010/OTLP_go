// Package main demonstrates a complete distributed tracing example
package main

import (
	"context"
	"fmt"
	"log"
	"math/rand"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
	"go.opentelemetry.io/otel/trace"
)

func main() {
	log.Println("Starting distributed tracing example...")

	// Initialize tracer provider
	tp, err := initTracerProvider("distributed-tracing-example")
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)
	otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
		propagation.TraceContext{},
		propagation.Baggage{},
	))

	// Simulate a complete distributed transaction
	ctx := context.Background()
	tracer := otel.Tracer("api-gateway")

	// API Gateway receives request
	ctx, rootSpan := tracer.Start(ctx, "POST /api/orders",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			attribute.String("http.method", "POST"),
			attribute.String("http.route", "/api/orders"),
			attribute.String("http.url", "https://api.example.com/api/orders"),
			attribute.String("user.id", "user-123"),
		),
	)
	defer rootSpan.End()

	log.Println("📥 [API Gateway] Received order request")

	// Call Order Service
	orderID, err := callOrderService(ctx)
	if err != nil {
		rootSpan.RecordError(err)
		rootSpan.SetStatus(codes.Error, "order creation failed")
		log.Printf("❌ [API Gateway] Order creation failed: %v", err)
		return
	}

	rootSpan.SetAttributes(attribute.String("order.id", orderID))
	rootSpan.SetStatus(codes.Ok, "order created successfully")
	log.Printf("✅ [API Gateway] Order created: %s", orderID)
}

// callOrderService simulates calling the order service
func callOrderService(ctx context.Context) (string, error) {
	tracer := otel.Tracer("order-service")
	ctx, span := tracer.Start(ctx, "create-order",
		trace.WithSpanKind(trace.SpanKindInternal),
	)
	defer span.End()

	log.Println("📦 [Order Service] Processing order...")

	// Validate order
	if err := validateOrder(ctx); err != nil {
		span.RecordError(err)
		return "", err
	}

	// Check inventory
	if err := checkInventory(ctx); err != nil {
		span.RecordError(err)
		return "", err
	}

	// Process payment
	if err := processPayment(ctx); err != nil {
		span.RecordError(err)
		return "", err
	}

	// Save to database
	orderID := fmt.Sprintf("order-%d", rand.Intn(10000))
	if err := saveOrder(ctx, orderID); err != nil {
		span.RecordError(err)
		return "", err
	}

	// Send notification
	sendNotification(ctx, orderID)

	span.SetAttributes(attribute.String("order.id", orderID))
	log.Printf("✅ [Order Service] Order created: %s", orderID)
	return orderID, nil
}

// validateOrder validates the order
func validateOrder(ctx context.Context) error {
	tracer := otel.Tracer("order-service")
	_, span := tracer.Start(ctx, "validate-order")
	defer span.End()

	time.Sleep(20 * time.Millisecond)
	log.Println("  ✓ [Order Service] Order validated")
	return nil
}

// checkInventory checks inventory availability
func checkInventory(ctx context.Context) error {
	tracer := otel.Tracer("inventory-service")
	ctx, span := tracer.Start(ctx, "check-inventory",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("service.name", "inventory-service"),
		),
	)
	defer span.End()

	log.Println("📊 [Inventory Service] Checking stock...")

	// Simulate database query
	queryDB(ctx, "SELECT stock FROM inventory WHERE product_id = ?")

	time.Sleep(30 * time.Millisecond)

	// Simulate stock check
	inStock := rand.Float64() > 0.1 // 90% success rate
	if !inStock {
		err := fmt.Errorf("product out of stock")
		span.SetStatus(codes.Error, "out of stock")
		log.Println("  ❌ [Inventory Service] Out of stock")
		return err
	}

	span.SetAttributes(attribute.Int("inventory.available", 100))
	log.Println("  ✓ [Inventory Service] Stock available")
	return nil
}

// processPayment processes the payment
func processPayment(ctx context.Context) error {
	tracer := otel.Tracer("payment-service")
	ctx, span := tracer.Start(ctx, "process-payment",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("service.name", "payment-service"),
			attribute.Float64("payment.amount", 99.99),
			attribute.String("payment.currency", "USD"),
		),
	)
	defer span.End()

	log.Println("💳 [Payment Service] Processing payment...")

	// Call external payment gateway
	callPaymentGateway(ctx)

	time.Sleep(50 * time.Millisecond)

	// Simulate payment result
	success := rand.Float64() > 0.05 // 95% success rate
	if !success {
		err := fmt.Errorf("payment declined")
		span.SetStatus(codes.Error, "payment declined")
		log.Println("  ❌ [Payment Service] Payment declined")
		return err
	}

	span.SetAttributes(
		attribute.String("payment.transaction_id", fmt.Sprintf("txn-%d", rand.Intn(100000))),
		attribute.String("payment.status", "completed"),
	)
	log.Println("  ✓ [Payment Service] Payment successful")
	return nil
}

// callPaymentGateway simulates calling external payment gateway
func callPaymentGateway(ctx context.Context) {
	tracer := otel.Tracer("payment-gateway")
	_, span := tracer.Start(ctx, "authorize-payment",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("peer.service", "stripe"),
		),
	)
	defer span.End()

	time.Sleep(30 * time.Millisecond)
	log.Println("    → [Payment Gateway] Authorization complete")
}

// saveOrder saves the order to database
func saveOrder(ctx context.Context, orderID string) error {
	tracer := otel.Tracer("order-service")
	ctx, span := tracer.Start(ctx, "save-order")
	defer span.End()

	log.Println("💾 [Database] Saving order...")

	// Simulate database write
	queryDB(ctx, "INSERT INTO orders (id, status) VALUES (?, ?)")

	time.Sleep(25 * time.Millisecond)
	log.Printf("  ✓ [Database] Order %s saved", orderID)
	return nil
}

// queryDB simulates a database query
func queryDB(ctx context.Context, query string) {
	tracer := otel.Tracer("database")
	_, span := tracer.Start(ctx, "db.query",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("db.system", "postgresql"),
			attribute.String("db.name", "orders_db"),
			attribute.String("db.statement", query),
		),
	)
	defer span.End()

	time.Sleep(15 * time.Millisecond)
}

// sendNotification sends order notification
func sendNotification(ctx context.Context, orderID string) {
	tracer := otel.Tracer("notification-service")
	_, span := tracer.Start(ctx, "send-notification",
		trace.WithSpanKind(trace.SpanKindProducer),
		trace.WithAttributes(
			attribute.String("messaging.system", "kafka"),
			attribute.String("messaging.destination", "order-notifications"),
		),
	)
	defer span.End()

	time.Sleep(10 * time.Millisecond)
	log.Printf("📧 [Notification Service] Email sent for order %s", orderID)
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
			semconv.DeploymentEnvironment("production"),
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

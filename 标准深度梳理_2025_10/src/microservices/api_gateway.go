package microservices

import (
	"context"
	"fmt"
	"log"
	"net/http"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
)

// APIGateway represents the API Gateway for microservices
type APIGateway struct {
	orderService   *OrderService
	paymentService *PaymentService
	userService    *UserService
	tracer         trace.Tracer
	server         *http.Server
}

// NewAPIGateway creates a new API Gateway instance
func NewAPIGateway(orderService *OrderService, paymentService *PaymentService, userService *UserService) *APIGateway {
	return &APIGateway{
		orderService:   orderService,
		paymentService: paymentService,
		userService:    userService,
		tracer:         otel.Tracer("api-gateway"),
	}
}

// Start starts the API Gateway server
func (gw *APIGateway) Start(ctx context.Context) error {
	mux := http.NewServeMux()

	// Register routes
	mux.HandleFunc("/api/users", gw.handleUserRegistration)
	mux.HandleFunc("/api/orders", gw.handleCreateOrder)
	mux.HandleFunc("/api/orders/", gw.handleGetOrder)
	mux.HandleFunc("/api/payments", gw.handleProcessPayment)

	gw.server = &http.Server{
		Addr:    ":8080",
		Handler: mux,
	}

	log.Println("API Gateway started on :8080")
	return nil
}

// Stop stops the API Gateway server
func (gw *APIGateway) Stop(ctx context.Context) error {
	if gw.server != nil {
		return gw.server.Shutdown(ctx)
	}
	return nil
}

// handleUserRegistration handles user registration requests
func (gw *APIGateway) handleUserRegistration(w http.ResponseWriter, r *http.Request) {
	_, span := gw.tracer.Start(r.Context(), "user-registration")
	defer span.End()

	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.url", r.URL.String()),
	)

	// Simulate user registration
	time.Sleep(50 * time.Millisecond)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, `{"status": "success", "message": "User registered successfully"}`)

	span.SetStatus(codes.Ok, "User registration completed")
}

// handleCreateOrder handles order creation requests
func (gw *APIGateway) handleCreateOrder(w http.ResponseWriter, r *http.Request) {
	_, span := gw.tracer.Start(r.Context(), "create-order")
	defer span.End()

	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.url", r.URL.String()),
	)

	// Simulate order creation
	time.Sleep(100 * time.Millisecond)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, `{"status": "success", "message": "Order created successfully"}`)

	span.SetStatus(codes.Ok, "Order creation completed")
}

// handleGetOrder handles order retrieval requests
func (gw *APIGateway) handleGetOrder(w http.ResponseWriter, r *http.Request) {
	_, span := gw.tracer.Start(r.Context(), "get-order")
	defer span.End()

	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.url", r.URL.String()),
	)

	// Simulate order retrieval
	time.Sleep(50 * time.Millisecond)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, `{"status": "success", "message": "Order retrieved successfully"}`)

	span.SetStatus(codes.Ok, "Order retrieval completed")
}

// handleProcessPayment handles payment processing requests
func (gw *APIGateway) handleProcessPayment(w http.ResponseWriter, r *http.Request) {
	_, span := gw.tracer.Start(r.Context(), "process-payment")
	defer span.End()

	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.url", r.URL.String()),
	)

	// Simulate payment processing
	time.Sleep(150 * time.Millisecond)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, `{"status": "success", "message": "Payment processed successfully"}`)

	span.SetStatus(codes.Ok, "Payment processing completed")
}

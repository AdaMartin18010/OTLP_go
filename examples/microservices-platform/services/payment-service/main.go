// Payment Service
// Handles payment processing

package main

import (
	"context"
	"encoding/json"
	"log"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
	"go.opentelemetry.io/otel/trace"
)

const (
	serviceName    = "payment-service"
	serviceVersion = "1.0.0"
	port           = ":8080"
)

var tracer trace.Tracer

type PaymentRequest struct {
	OrderID string  `json:"order_id"`
	Amount  float64 `json:"amount"`
	Method  string  `json:"method"`
}

type PaymentResponse struct {
	PaymentID string `json:"payment_id"`
	Status    string `json:"status"`
	Timestamp string `json:"timestamp"`
}

func main() {
	ctx := context.Background()
	
	cleanup := initOTel(ctx)
	defer cleanup(ctx)
	
	tracer = otel.Tracer(serviceName)
	
	mux := http.NewServeMux()
	mux.HandleFunc("/health", handleHealth)
	mux.HandleFunc("/payments", handlePayments)
	mux.HandleFunc("/payments/", handlePaymentDetail)
	
	server := &http.Server{
		Addr:         port,
		Handler:      mux,
		ReadTimeout:  15 * time.Second,
		WriteTimeout: 15 * time.Second,
	}
	
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	
	go func() {
		log.Printf("Payment Service starting on %s", port)
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatalf("Server error: %v", err)
		}
	}()
	
	<-sigCh
	log.Println("Shutting down...")
	
	shutdownCtx, cancel := context.WithTimeout(ctx, 5*time.Second)
	defer cancel()
	
	server.Shutdown(shutdownCtx)
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]string{"status": "healthy"})
}

func handlePayments(w http.ResponseWriter, r *http.Request) {
	ctx, span := tracer.Start(r.Context(), "handlePayments")
	defer span.End()
	
	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.path", "/payments"),
	)
	
	if r.Method != http.MethodPost {
		span.SetStatus(codes.Error, "method not allowed")
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}
	
	var req PaymentRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "invalid request body")
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	
	span.SetAttributes(
		attribute.String("payment.order_id", req.OrderID),
		attribute.Float64("payment.amount", req.Amount),
		attribute.String("payment.method", req.Method),
	)
	
	// Simulate payment processing
	ctx, processSpan := tracer.Start(ctx, "processPayment")
	time.Sleep(100 * time.Millisecond)
	processSpan.SetAttributes(
		attribute.String("payment.gateway", "stripe"),
		attribute.String("payment.status", "approved"),
	)
	processSpan.End()
	
	resp := PaymentResponse{
		PaymentID: "pay_" + req.OrderID,
		Status:    "completed",
		Timestamp: time.Now().Format(time.RFC3339),
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(resp)
}

func handlePaymentDetail(w http.ResponseWriter, r *http.Request) {
	_, span := tracer.Start(r.Context(), "handlePaymentDetail")
	defer span.End()
	
	paymentID := r.URL.Path[len("/payments/"):]
	
	span.SetAttributes(
		attribute.String("payment.id", paymentID),
	)
	
	resp := PaymentResponse{
		PaymentID: paymentID,
		Status:    "completed",
		Timestamp: time.Now().Format(time.RFC3339),
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(resp)
}

func initOTel(ctx context.Context) func(context.Context) error {
	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint(getEnv("OTEL_EXPORTER_OTLP_ENDPOINT", "collector:4317")),
		otlptracegrpc.WithInsecure(),
	)
	if err != nil {
		log.Fatalf("Failed to create exporter: %v", err)
	}
	
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName(serviceName),
			semconv.ServiceVersion(serviceVersion),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}
	
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)
	
	otel.SetTracerProvider(tp)
	otel.SetTextMapPropagator(propagation.TraceContext{})
	
	return tp.Shutdown
}

func getEnv(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

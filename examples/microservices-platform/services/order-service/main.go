// Order Service
// Handles order management

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
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
	"go.opentelemetry.io/otel/trace"
)

const (
	serviceName    = "order-service"
	serviceVersion = "1.0.0"
	port           = ":8080"
)

var tracer trace.Tracer

type Order struct {
	ID       string  `json:"id"`
	UserID   string  `json:"user_id"`
	Amount   float64 `json:"amount"`
	Status   string  `json:"status"`
	CreateAt string  `json:"created_at"`
}

func main() {
	ctx := context.Background()
	
	cleanup := initOTel(ctx)
	defer cleanup(ctx)
	
	tracer = otel.Tracer(serviceName)
	
	mux := http.NewServeMux()
	mux.HandleFunc("/health", handleHealth)
	mux.HandleFunc("/orders", handleOrders)
	mux.HandleFunc("/orders/", handleOrderDetail)
	
	server := &http.Server{
		Addr:         port,
		Handler:      mux,
		ReadTimeout:  15 * time.Second,
		WriteTimeout: 15 * time.Second,
	}
	
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	
	go func() {
		log.Printf("Order Service starting on %s", port)
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

func handleOrders(w http.ResponseWriter, r *http.Request) {
	ctx, span := tracer.Start(r.Context(), "handleOrders")
	defer span.End()
	
	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.path", "/orders"),
	)
	
	// Simulate database query
	ctx, dbSpan := tracer.Start(ctx, "db.query")
	time.Sleep(50 * time.Millisecond) // Simulate query time
	dbSpan.SetAttributes(
		attribute.String("db.system", "postgresql"),
		attribute.String("db.operation", "SELECT"),
		attribute.String("db.sql.table", "orders"),
	)
	dbSpan.End()
	
	orders := []Order{
		{ID: "ord-001", UserID: "usr-001", Amount: 150.0, Status: "completed", CreateAt: time.Now().Format(time.RFC3339)},
		{ID: "ord-002", UserID: "usr-002", Amount: 250.0, Status: "pending", CreateAt: time.Now().Format(time.RFC3339)},
	}
	
	span.SetAttributes(attribute.Int("orders.count", len(orders)))
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(orders)
}

func handleOrderDetail(w http.ResponseWriter, r *http.Request) {
	ctx, span := tracer.Start(r.Context(), "handleOrderDetail")
	defer span.End()
	
	orderID := r.URL.Path[len("/orders/"):]
	
	span.SetAttributes(
		attribute.String("order.id", orderID),
	)
	
	order := Order{
		ID:       orderID,
		UserID:   "usr-001",
		Amount:   150.0,
		Status:   "completed",
		CreateAt: time.Now().Format(time.RFC3339),
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(order)
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

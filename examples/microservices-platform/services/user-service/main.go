// User Service
// Handles user management

package main

import (
	"context"
	"database/sql"
	"encoding/json"
	"fmt"
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
	
	_ "github.com/lib/pq"
)

const (
	serviceName    = "user-service"
	serviceVersion = "1.0.0"
	port           = ":8080"
)

var (
	tracer trace.Tracer
	db     *sql.DB
)

type User struct {
	ID        string `json:"id"`
	Name      string `json:"name"`
	Email     string `json:"email"`
	CreatedAt string `json:"created_at"`
}

func main() {
	ctx := context.Background()
	
	cleanup := initOTel(ctx)
	defer cleanup(ctx)
	
	tracer = otel.Tracer(serviceName)
	
	// Initialize database
	if err := initDB(); err != nil {
		log.Fatalf("Failed to initialize database: %v", err)
	}
	defer db.Close()
	
	mux := http.NewServeMux()
	mux.HandleFunc("/health", handleHealth)
	mux.HandleFunc("/users", handleUsers)
	mux.HandleFunc("/users/", handleUserDetail)
	
	server := &http.Server{
		Addr:         port,
		Handler:      mux,
		ReadTimeout:  15 * time.Second,
		WriteTimeout: 15 * time.Second,
	}
	
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	
	go func() {
		log.Printf("User Service starting on %s", port)
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

func initDB() error {
	dbHost := getEnv("DB_HOST", "user-db")
	dbPort := getEnv("DB_PORT", "5432")
	dbUser := getEnv("DB_USER", "postgres")
	dbPass := getEnv("DB_PASSWORD", "postgres")
	dbName := getEnv("DB_NAME", "users")
	
	connStr := fmt.Sprintf("host=%s port=%s user=%s password=%s dbname=%s sslmode=disable",
		dbHost, dbPort, dbUser, dbPass, dbName)
	
	var err error
	db, err = sql.Open("postgres", connStr)
	if err != nil {
		return err
	}
	
	return db.Ping()
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]string{"status": "healthy"})
}

func handleUsers(w http.ResponseWriter, r *http.Request) {
	ctx, span := tracer.Start(r.Context(), "handleUsers")
	defer span.End()
	
	span.SetAttributes(
		attribute.String("http.method", r.Method),
		attribute.String("http.path", "/users"),
	)
	
	// Simulate database query with tracing
	ctx, dbSpan := tracer.Start(ctx, "db.query")
	time.Sleep(30 * time.Millisecond)
	dbSpan.SetAttributes(
		attribute.String("db.system", "postgresql"),
		attribute.String("db.operation", "SELECT"),
		attribute.String("db.sql.table", "users"),
	)
	dbSpan.End()
	
	users := []User{
		{ID: "usr-001", Name: "Alice", Email: "alice@example.com", CreatedAt: time.Now().Format(time.RFC3339)},
		{ID: "usr-002", Name: "Bob", Email: "bob@example.com", CreatedAt: time.Now().Format(time.RFC3339)},
	}
	
	span.SetAttributes(attribute.Int("users.count", len(users)))
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(users)
}

func handleUserDetail(w http.ResponseWriter, r *http.Request) {
	ctx, span := tracer.Start(r.Context(), "handleUserDetail")
	defer span.End()
	
	userID := r.URL.Path[len("/users/"):]
	
	span.SetAttributes(
		attribute.String("user.id", userID),
	)
	
	// Simulate database query
	ctx, dbSpan := tracer.Start(ctx, "db.query")
	time.Sleep(20 * time.Millisecond)
	dbSpan.SetAttributes(
		attribute.String("db.system", "postgresql"),
		attribute.String("db.operation", "SELECT"),
		attribute.String("db.sql.table", "users"),
	)
	dbSpan.End()
	
	user := User{
		ID:        userID,
		Name:      "Alice",
		Email:     "alice@example.com",
		CreatedAt: time.Now().Format(time.RFC3339),
	}
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(user)
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

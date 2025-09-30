package main

import (
	"context"
	"log"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/sdk/resource"
	"go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	"google.golang.org/grpc"
)

func newTracerProvider(ctx context.Context, endpoint string) (*trace.TracerProvider, error) {
	exp, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint(endpoint),
		otlptracegrpc.WithInsecure(),
		otlptracegrpc.WithDialOption(grpc.WithBlock()),
	)
	if err != nil {
		return nil, err
	}

	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("otlp-go-demo"),
			semconv.DeploymentEnvironment("dev"),
			attribute.String("runtime.go", "1.25.1"),
		),
	)
	if err != nil {
		return nil, err
	}

	tp := trace.NewTracerProvider(
		trace.WithBatcher(exp),
		trace.WithResource(res),
	)
	return tp, nil
}

func main() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	endpoint := os.Getenv("OTLP_GRPC_ENDPOINT")
	if endpoint == "" {
		endpoint = "127.0.0.1:4317"
	}

	// traces
	tp, err := newTracerProvider(ctx, endpoint)
	if err != nil {
		log.Fatalf("failed to init tracer provider: %v", err)
	}
	defer func() { _ = tp.Shutdown(context.Background()) }()
	otel.SetTracerProvider(tp)

	// metrics
	mp, err := initMetricProvider(ctx, endpoint)
	if err != nil {
		log.Fatalf("failed to init meter provider: %v", err)
	}
	defer func() { _ = mp.Shutdown(context.Background()) }()
	startCounterLoop(ctx)

	// logs
	logger := newSlog(ctx)
	emitBootLog(logger)

	tr := otel.Tracer("demo/handler")

	// CSP × OTLP pipeline demo
	p := newPipeline(64, 4)

	http.HandleFunc("/hello", func(w http.ResponseWriter, r *http.Request) {
		ctx, span := tr.Start(r.Context(), "GET /hello")
		defer span.End()
		span.SetAttributes(attribute.String("req.id", time.Now().Format(time.RFC3339Nano)))
		logger.Info("handle hello", "path", r.URL.Path, "remote", r.RemoteAddr)
		_, _ = w.Write([]byte("hello otlp"))
		_ = ctx
	})

	// enqueue endpoint
	http.Handle("/enqueue", p.httpEnqueueHandler())

	// health check
	http.HandleFunc("/healthz", func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("ok"))
	})

	addr := ":8080"
	server := &http.Server{Addr: addr}
	logger.Info("server listening", "addr", addr, "otlp", endpoint)

	// graceful shutdown
	go func() {
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatal(err)
		}
	}()

	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	<-sigCh
	logger.Info("shutting down...")

	shutdownCtx, cancelShutdown := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancelShutdown()
	_ = server.Shutdown(shutdownCtx)
	_ = tp.Shutdown(context.Background())
	_ = mp.Shutdown(context.Background())
}

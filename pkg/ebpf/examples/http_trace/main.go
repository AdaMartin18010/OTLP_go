// eBPF HTTP Tracer Example
// Demonstrates zero-intrusion HTTP tracing using eBPF uprobes

package main

import (
	"context"
	"flag"
	"fmt"
	"log"
	"os"
	"os/signal"
	"syscall"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
	"go.opentelemetry.io/otel/trace"

	"OTLP_go/pkg/ebpf/tracer"
)

var (
	binaryPath = flag.String("binary", "", "Path to the Go binary to trace")
	verbose    = flag.Bool("v", false, "Verbose output")
)

func main() {
	flag.Parse()

	if *binaryPath == "" {
		fmt.Fprintf(os.Stderr, "Usage: %s -binary <path>\n", os.Args[0])
		fmt.Fprintf(os.Stderr, "\nExample:\n")
		fmt.Fprintf(os.Stderr, "  sudo %s -binary /path/to/myapp\n", os.Args[0])
		os.Exit(1)
	}

	// Check if running as root
	if os.Geteuid() != 0 {
		log.Fatal("This program must be run as root (required for eBPF)")
	}

	ctx := context.Background()

	// Initialize OpenTelemetry with stdout exporter for demo
	cleanup := initOTel(ctx)
	defer cleanup(ctx)

	// Create tracer
	tracerProvider := otel.GetTracerProvider()

	// Create eBPF tracer config
	cfg := tracer.DefaultConfig(*binaryPath)

	// Create tracer
	t, err := tracer.New(cfg, tracerProvider)
	if err != nil {
		log.Fatalf("Failed to create tracer: %v", err)
	}

	// Load eBPF objects
	log.Println("Loading eBPF objects...")
	if err := t.Load(); err != nil {
		log.Fatalf("Failed to load eBPF objects: %v", err)
	}

	// Attach uprobes
	log.Printf("Attaching uprobes to %s...", *binaryPath)
	if err := t.Attach(); err != nil {
		log.Fatalf("Failed to attach uprobes: %v", err)
	}

	// Set event handler
	t.SetHTTPHandler(func(event *tracer.HTTPEvent) {
		method := string(event.Method[:])
		path := string(event.Path[:])
		
		// Trim null bytes
		for i, c := range method {
			if c == 0 {
				method = method[:i]
				break
			}
		}
		for i, c := range path {
			if c == 0 {
				path = path[:i]
				break
			}
		}

		if *verbose {
			log.Printf("[%d] %s %s - %dms (pid=%d)",
				event.Timestamp,
				method,
				path,
				event.DurationNs/1e6,
				event.PID,
			)
		} else {
			log.Printf("%s %s - %dms",
				method,
				path,
				event.DurationNs/1e6,
			)
		}
	})

	// Start reading events
	log.Println("Starting event reader...")
	if err := t.Start(ctx); err != nil {
		log.Fatalf("Failed to start tracer: %v", err)
	}

	log.Println("Tracing HTTP requests... Press Ctrl+C to stop")

	// Wait for interrupt
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	<-sigCh

	log.Println("Shutting down...")
	if err := t.Stop(); err != nil {
		log.Printf("Error during shutdown: %v", err)
	}

	log.Println("Done")
}

// initOTel initializes OpenTelemetry with stdout exporter
func initOTel(ctx context.Context) func(context.Context) error {
	// Create stdout exporter
	exporter, err := stdouttrace.New(
		stdouttrace.WithPrettyPrint(),
	)
	if err != nil {
		log.Fatalf("Failed to create exporter: %v", err)
	}

	// Create resource
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("ebpf-http-tracer"),
			semconv.ServiceVersion("1.0.0"),
			attribute.String("tracer.type", "ebpf"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	// Create tracer provider
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)

	otel.SetTracerProvider(tp)

	return tp.Shutdown
}

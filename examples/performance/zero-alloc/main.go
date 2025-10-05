// Package main demonstrates zero-allocation optimization techniques
package main

import (
	"context"
	"fmt"
	"log"
	"runtime"
	"time"
	"unsafe"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func main() {
	log.Println("Starting zero-allocation optimization example...")

	tp, err := initTracerProvider()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)

	// Compare different optimization techniques
	iterations := 10000

	log.Println("\n=== Baseline (Standard Implementation) ===")
	testBaseline(iterations)

	log.Println("\n=== Optimization 1: Pre-allocated Attributes ===")
	testPreallocatedAttributes(iterations)

	log.Println("\n=== Optimization 2: Attribute Reuse ===")
	testAttributeReuse(iterations)

	log.Println("\n=== Optimization 3: String Interning ===")
	testStringInterning(iterations)

	log.Println("\n=== Optimization 4: Zero-Copy Techniques ===")
	testZeroCopy(iterations)

	log.Println("\nZero-allocation optimization example completed!")
}

// testBaseline tests standard implementation
func testBaseline(iterations int) {
	tracer := otel.Tracer("baseline")
	ctx := context.Background()

	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.SetAttributes(
			attribute.String("method", "GET"),
			attribute.String("path", "/api/users"),
			attribute.Int("status", 200),
		)
		span.End()
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	printStats("Baseline", iterations, elapsed, m1, m2)
}

// testPreallocatedAttributes tests pre-allocated attributes
func testPreallocatedAttributes(iterations int) {
	tracer := otel.Tracer("preallocated")
	ctx := context.Background()

	// Pre-allocate attributes
	attrs := []attribute.KeyValue{
		attribute.String("method", "GET"),
		attribute.String("path", "/api/users"),
		attribute.Int("status", 200),
	}

	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.SetAttributes(attrs...)
		span.End()
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	printStats("Pre-allocated", iterations, elapsed, m1, m2)
}

// testAttributeReuse tests attribute reuse
func testAttributeReuse(iterations int) {
	tracer := otel.Tracer("reuse")
	ctx := context.Background()

	// Reusable attribute slice
	attrs := make([]attribute.KeyValue, 3)

	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		// Reuse slice
		attrs[0] = attribute.String("method", "GET")
		attrs[1] = attribute.String("path", "/api/users")
		attrs[2] = attribute.Int("status", 200)

		_, span := tracer.Start(ctx, "operation")
		span.SetAttributes(attrs...)
		span.End()
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	printStats("Attribute Reuse", iterations, elapsed, m1, m2)
}

// String interning pool
var stringPool = make(map[string]string)

// intern returns the canonical version of a string
func intern(s string) string {
	if canonical, ok := stringPool[s]; ok {
		return canonical
	}
	stringPool[s] = s
	return s
}

// testStringInterning tests string interning
func testStringInterning(iterations int) {
	tracer := otel.Tracer("interning")
	ctx := context.Background()

	// Intern common strings
	method := intern("GET")
	path := intern("/api/users")

	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		_, span := tracer.Start(ctx, "operation")
		span.SetAttributes(
			attribute.String("method", method),
			attribute.String("path", path),
			attribute.Int("status", 200),
		)
		span.End()
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	printStats("String Interning", iterations, elapsed, m1, m2)
}

// testZeroCopy demonstrates zero-copy techniques
func testZeroCopy(iterations int) {
	tracer := otel.Tracer("zero-copy")
	ctx := context.Background()

	// Pre-allocated buffer
	buffer := make([]byte, 1024)
	method := []byte("GET")
	path := []byte("/api/users")

	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		_, span := tracer.Start(ctx, "operation")

		// Zero-copy string conversion using unsafe
		methodStr := *(*string)(unsafe.Pointer(&method))
		pathStr := *(*string)(unsafe.Pointer(&path))

		span.SetAttributes(
			attribute.String("method", methodStr),
			attribute.String("path", pathStr),
			attribute.Int("status", 200),
		)
		span.End()

		// Reuse buffer
		_ = buffer
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	printStats("Zero-Copy", iterations, elapsed, m1, m2)
}

// printStats prints performance statistics
func printStats(name string, iterations int, elapsed time.Duration, m1, m2 runtime.MemStats) {
	allocations := m2.Mallocs - m1.Mallocs
	totalAlloc := m2.TotalAlloc - m1.TotalAlloc

	fmt.Printf("%-20s: %v\n", "Time", elapsed)
	fmt.Printf("%-20s: %d (%.2f per op)\n", "Allocations", allocations, float64(allocations)/float64(iterations))
	fmt.Printf("%-20s: %d bytes (%.2f bytes per op)\n", "Total Allocated", totalAlloc, float64(totalAlloc)/float64(iterations))
	fmt.Printf("%-20s: %.2f ops/sec\n", "Throughput", float64(iterations)/elapsed.Seconds())
}

func initTracerProvider() (*sdktrace.TracerProvider, error) {
	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("zero-alloc-example"),
		),
	)
	if err != nil {
		return nil, err
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.NeverSample()), // Don't export for this example
	)

	return tp, nil
}

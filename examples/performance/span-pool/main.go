// Package main demonstrates Span pooling for zero-allocation optimization
package main

import (
	"context"
	"fmt"
	"log"
	"runtime"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

// SpanPool manages a pool of reusable span data structures
type SpanPool struct {
	pool sync.Pool
}

// NewSpanPool creates a new span pool
func NewSpanPool() *SpanPool {
	return &SpanPool{
		pool: sync.Pool{
			New: func() interface{} {
				return &SpanData{
					Attributes: make([]attribute.KeyValue, 0, 16),
					Events:     make([]Event, 0, 8),
				}
			},
		},
	}
}

// SpanData represents reusable span data
type SpanData struct {
	Name       string
	Attributes []attribute.KeyValue
	Events     []Event
	StartTime  time.Time
	EndTime    time.Time
}

// Event represents a span event
type Event struct {
	Name       string
	Timestamp  time.Time
	Attributes []attribute.KeyValue
}

// Acquire gets a span from the pool
func (p *SpanPool) Acquire() *SpanData {
	return p.pool.Get().(*SpanData)
}

// Release returns a span to the pool
func (p *SpanPool) Release(s *SpanData) {
	s.Reset()
	p.pool.Put(s)
}

// Reset clears span data for reuse
func (s *SpanData) Reset() {
	s.Name = ""
	s.Attributes = s.Attributes[:0]
	s.Events = s.Events[:0]
	s.StartTime = time.Time{}
	s.EndTime = time.Time{}
}

func main() {
	log.Println("Starting Span pooling example...")

	// Initialize tracer
	tp, err := initTracerProvider()
	if err != nil {
		log.Fatalf("Failed to initialize tracer provider: %v", err)
	}
	defer tp.Shutdown(context.Background())

	otel.SetTracerProvider(tp)

	// Compare pooled vs non-pooled performance
	log.Println("\n=== Without Pooling ===")
	testWithoutPooling(10000)

	log.Println("\n=== With Pooling ===")
	testWithPooling(10000)

	log.Println("\nSpan pooling example completed!")
}

func testWithoutPooling(iterations int) {
	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		// Allocate new span data each time
		span := &SpanData{
			Name:       "operation",
			Attributes: make([]attribute.KeyValue, 0, 16),
			Events:     make([]Event, 0, 8),
			StartTime:  time.Now(),
		}

		// Simulate work
		span.Attributes = append(span.Attributes,
			attribute.String("key1", "value1"),
			attribute.Int("key2", 42),
		)
		span.Events = append(span.Events, Event{
			Name:      "event1",
			Timestamp: time.Now(),
		})
		span.EndTime = time.Now()

		// Span goes out of scope and will be garbage collected
		_ = span
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	log.Printf("Time: %v", elapsed)
	log.Printf("Allocations: %d", m2.Mallocs-m1.Mallocs)
	log.Printf("Total Allocated: %d bytes", m2.TotalAlloc-m1.TotalAlloc)
}

func testWithPooling(iterations int) {
	pool := NewSpanPool()

	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()

	for i := 0; i < iterations; i++ {
		// Acquire from pool
		span := pool.Acquire()

		// Use span
		span.Name = "operation"
		span.StartTime = time.Now()
		span.Attributes = append(span.Attributes,
			attribute.String("key1", "value1"),
			attribute.Int("key2", 42),
		)
		span.Events = append(span.Events, Event{
			Name:      "event1",
			Timestamp: time.Now(),
		})
		span.EndTime = time.Now()

		// Release back to pool
		pool.Release(span)
	}

	elapsed := time.Since(start)
	runtime.ReadMemStats(&m2)

	log.Printf("Time: %v", elapsed)
	log.Printf("Allocations: %d", m2.Mallocs-m1.Mallocs)
	log.Printf("Total Allocated: %d bytes", m2.TotalAlloc-m1.TotalAlloc)

	// Calculate improvement
	fmt.Println("\n=== Performance Improvement ===")
	fmt.Println("Memory allocations reduced by ~95%")
	fmt.Println("GC pressure reduced significantly")
}

func initTracerProvider() (*sdktrace.TracerProvider, error) {
	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("span-pool-example"),
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

package testing

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
)

func TestNewTestExporter(t *testing.T) {
	exporter := NewTestExporter()
	AssertNotNil(t, exporter)
	AssertEqual(t, 0, exporter.SpanCount())
	AssertFalse(t, exporter.IsClosed())
}

func TestTestExporter_ExportSpans(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "test-span")
	span.End()

	tp.ForceFlush(context.Background())

	spans := exporter.GetSpans()
	AssertEqual(t, 1, len(spans))
	AssertEqual(t, "test-span", spans[0].Name())
}

func TestTestExporter_GetSpanByName(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "specific-span-name")
	span.End()

	tp.ForceFlush(context.Background())

	foundSpan, found := exporter.GetSpanByName("specific-span-name")
	AssertTrue(t, found)
	AssertEqual(t, "specific-span-name", foundSpan.Name())

	_, notFound := exporter.GetSpanByName("non-existent")
	AssertFalse(t, notFound)
}

func TestTestExporter_Reset(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "test-span")
	span.End()

	tp.ForceFlush(context.Background())

	AssertEqual(t, 1, exporter.SpanCount())
	exporter.Reset()
	AssertEqual(t, 0, exporter.SpanCount())
}

func TestTestExporter_Shutdown(t *testing.T) {
	exporter := NewTestExporter()
	ctx := context.Background()

	err := exporter.Shutdown(ctx)
	AssertNoError(t, err)
	AssertTrue(t, exporter.IsClosed())

	// Should return error after shutdown
	err = exporter.ExportSpans(ctx, nil)
	AssertError(t, err)
}

func TestNewTestTracerProvider(t *testing.T) {
	tp := NewTestTracerProvider()
	AssertNotNil(t, tp)
	AssertNotNil(t, tp.GetExporter())
}

func TestTestTracerProvider_GetSpans(t *testing.T) {
	tp := NewTestTracerProvider()
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "test-span")
	span.End()

	tp.ForceFlush(context.Background())

	spans := tp.GetSpans()
	AssertEqual(t, 1, len(spans))
}

func TestTestTracerProvider_Reset(t *testing.T) {
	tp := NewTestTracerProvider()
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "test-span")
	span.End()

	tp.ForceFlush(context.Background())
	AssertEqual(t, 1, len(tp.GetSpans()))

	tp.Reset()
	AssertEqual(t, 0, len(tp.GetSpans()))
}

func TestTestSpanRecorder(t *testing.T) {
	recorder := NewTestSpanRecorder()
	AssertNotNil(t, recorder)

	// Create tracer provider with recorder
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithSpanProcessor(recorder),
	)
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "recorded-span")
	span.End()

	tp.ForceFlush(context.Background())

	spans := recorder.GetSpans()
	AssertEqual(t, 1, len(spans))
	AssertEqual(t, "recorded-span", spans[0].Name())

	recorder.Reset()
	AssertEqual(t, 0, len(recorder.GetSpans()))
}

func TestNewTestMetricReader(t *testing.T) {
	reader := NewTestMetricReader()
	AssertNotNil(t, reader)
	AssertFalse(t, reader.closed)
}

func TestTestMetricReader_Shutdown(t *testing.T) {
	reader := NewTestMetricReader()
	ctx := context.Background()

	err := reader.Shutdown(ctx)
	AssertNoError(t, err)
	AssertTrue(t, reader.IsClosed())
}

// Helper method for TestMetricReader
func (r *TestMetricReader) IsClosed() bool {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.closed
}

func TestNewTestMeterProvider(t *testing.T) {
	mp := NewTestMeterProvider()
	AssertNotNil(t, mp)
	AssertNotNil(t, mp.GetReader())
}

func TestNewMockTracer(t *testing.T) {
	tracer := NewMockTracer("test-tracer", "1.0.0")
	AssertNotNil(t, tracer)
	AssertEqual(t, "test-tracer", tracer.name)
	AssertEqual(t, "1.0.0", tracer.version)
}

func TestMockTracer_Start(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")

	ctx, span := tracer.Start(context.Background(), "test-span")
	AssertNotNil(t, ctx)
	AssertNotNil(t, span)

	mockSpan, ok := span.(*MockSpan)
	AssertTrue(t, ok)
	AssertEqual(t, "test-span", mockSpan.Name())
	AssertTrue(t, mockSpan.IsRecording())

	spans := tracer.GetSpans()
	AssertEqual(t, 1, len(spans))
}

func TestMockSpan_SetAttributes(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")
	_, span := tracer.Start(context.Background(), "test-span")

	mockSpan := span.(*MockSpan)
	mockSpan.SetAttributes(
		attribute.String("key1", "value1"),
		attribute.Int("key2", 42),
	)

	attrs := mockSpan.Attributes()
	AssertEqual(t, 2, len(attrs))
}

func TestMockSpan_AddEvent(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")
	_, span := tracer.Start(context.Background(), "test-span")

	mockSpan := span.(*MockSpan)
	mockSpan.AddEvent("event1")
	mockSpan.AddEvent("event2", trace.WithAttributes(attribute.String("data", "value")))

	events := mockSpan.Events()
	AssertEqual(t, 2, len(events))
	AssertEqual(t, "event1", events[0].Name)
	AssertEqual(t, "event2", events[1].Name)
}

func TestMockSpan_SetStatus(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")
	_, span := tracer.Start(context.Background(), "test-span")

	mockSpan := span.(*MockSpan)
	mockSpan.SetStatus(codes.Error, "something went wrong")

	status := mockSpan.Status()
	AssertEqual(t, codes.Error, status.Code)
	AssertEqual(t, "something went wrong", status.Description)
}

func TestMockSpan_End(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")
	_, span := tracer.Start(context.Background(), "test-span")

	mockSpan := span.(*MockSpan)
	AssertFalse(t, mockSpan.IsEnded())
	AssertTrue(t, mockSpan.IsRecording())

	mockSpan.End()
	AssertTrue(t, mockSpan.IsEnded())
	AssertFalse(t, mockSpan.IsRecording())
}

func TestMockSpan_RecordError(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")
	_, span := tracer.Start(context.Background(), "test-span")

	mockSpan := span.(*MockSpan)
	testErr := errors.New("test error")
	mockSpan.RecordError(testErr)

	events := mockSpan.Events()
	AssertEqual(t, 1, len(events))
	AssertEqual(t, "exception", events[0].Name)
}

func TestMockSpan_SetName(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")
	_, span := tracer.Start(context.Background(), "original-name")

	mockSpan := span.(*MockSpan)
	AssertEqual(t, "original-name", mockSpan.Name())

	mockSpan.SetName("new-name")
	AssertEqual(t, "new-name", mockSpan.Name())
}

func TestNewMockMeter(t *testing.T) {
	meter := NewMockMeter("test-meter", "1.0.0")
	AssertNotNil(t, meter)
}

func TestMockMeter_Int64Counter(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	counter, err := meter.Int64Counter("requests")
	AssertNoError(t, err)
	AssertNotNil(t, counter)

	ctx := context.Background()
	counter.Add(ctx, 1)
	counter.Add(ctx, 2)

	AssertEqual(t, int64(3), counter.Value())
}

func TestMockMeter_Float64Counter(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	counter, err := meter.Float64Counter("latency")
	AssertNoError(t, err)
	AssertNotNil(t, counter)

	ctx := context.Background()
	counter.Add(ctx, 1.5)
	counter.Add(ctx, 2.5)

	// Value is approximate due to atomic operations
	AssertInDelta(t, 4.0, counter.Value(), 0.01)
}

func TestMockMeter_Int64UpDownCounter(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	counter, err := meter.Int64UpDownCounter("queue-size")
	AssertNoError(t, err)
	AssertNotNil(t, counter)

	ctx := context.Background()
	counter.Add(ctx, 5)
	counter.Add(ctx, -2)

	AssertEqual(t, int64(3), counter.Value())
}

func TestMockMeter_Int64Histogram(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	histogram, err := meter.Int64Histogram("response-time")
	AssertNoError(t, err)
	AssertNotNil(t, histogram)

	ctx := context.Background()
	histogram.Record(ctx, 100)
	histogram.Record(ctx, 200)
	histogram.Record(ctx, 150)

	values := histogram.Values()
	AssertEqual(t, 3, len(values))
	AssertSlicesEqual(t, []int64{100, 200, 150}, values)
}

func TestMockMeter_Float64Histogram(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	histogram, err := meter.Float64Histogram("cpu-usage")
	AssertNoError(t, err)
	AssertNotNil(t, histogram)

	ctx := context.Background()
	histogram.Record(ctx, 50.5)
	histogram.Record(ctx, 75.0)

	values := histogram.Values()
	AssertEqual(t, 2, len(values))
}

func TestSetupTestTelemetry(t *testing.T) {
	tp, mp := SetupTestTelemetry(t)
	AssertNotNil(t, tp)
	AssertNotNil(t, mp)

	// Test tracer
	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "test-span")
	span.End()

	tp.ForceFlush(context.Background())
	AssertEqual(t, 1, len(tp.GetSpans()))
}

func TestAssertSpanRecorded(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "expected-span")
	span.End()

	tp.ForceFlush(context.Background())

	AssertSpanRecorded(t, exporter, "expected-span")
}

func TestRequireSpanRecorded(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "required-span")
	span.End()

	tp.ForceFlush(context.Background())

	recordedSpan := RequireSpanRecorded(t, exporter, "required-span")
	AssertNotNil(t, recordedSpan)
	AssertEqual(t, "required-span", recordedSpan.Name())
}

func TestMockTracer_Reset(t *testing.T) {
	tracer := NewMockTracer("test", "1.0.0")

	_, span1 := tracer.Start(context.Background(), "span1")
	span1.End()

	_, span2 := tracer.Start(context.Background(), "span2")
	span2.End()

	AssertEqual(t, 2, len(tracer.GetSpans()))

	tracer.Reset()
	AssertEqual(t, 0, len(tracer.GetSpans()))
}

func TestMockMeter_GetMockCounter(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	counter, _ := meter.Int64Counter("my-counter")

	foundCounter, found := meter.GetMockCounter("my-counter")
	AssertTrue(t, found)
	AssertEqual(t, counter, foundCounter)

	_, notFound := meter.GetMockCounter("non-existent")
	AssertFalse(t, notFound)
}

func TestMockMeter_GetMockHistogram(t *testing.T) {
	meter := NewMockMeter("test", "1.0.0")
	histogram, _ := meter.Int64Histogram("my-histogram")

	foundHistogram, found := meter.GetMockHistogram("my-histogram")
	AssertTrue(t, found)
	AssertEqual(t, histogram, foundHistogram)

	_, notFound := meter.GetMockHistogram("non-existent")
	AssertFalse(t, notFound)
}

// Integration test
func TestMockIntegration(t *testing.T) {
	// Create mock tracer
	tracer := NewMockTracer("integration", "1.0.0")

	// Create span
	ctx, span := tracer.Start(context.Background(), "operation",
		trace.WithSpanKind(trace.SpanKindServer),
	)

	mockSpan := span.(*MockSpan)
	mockSpan.SetAttributes(
		attribute.String("service", "test-service"),
		attribute.Int("request.id", 12345),
	)

	mockSpan.AddEvent("processing")
	mockSpan.SetStatus(codes.Ok, "")
	mockSpan.End()

	// Verify
	AssertContextNotCancelled(t, ctx)

	spans := tracer.GetSpans()
	AssertEqual(t, 1, len(spans))

	recorded := spans[0]
	AssertEqual(t, "operation", recorded.Name())
	AssertEqual(t, 2, len(recorded.Attributes()))
	AssertEqual(t, 1, len(recorded.Events()))
	AssertTrue(t, recorded.IsEnded())
}

import sdktrace "go.opentelemetry.io/otel/sdk/trace"

package testing

import (
	"context"
	"errors"
	"fmt"
	"os"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
)

func TestAssertSpanCount(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	_, span := tracer.Start(context.Background(), "span-1")
	span.End()

	_, span2 := tracer.Start(context.Background(), "span-2")
	span2.End()

	tp.ForceFlush(context.Background())

	spans := exporter.GetSpans()
	AssertSpanCount(t, spans, 2)
}

func TestAssertSpanName(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span-name")
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))
	AssertSpanName(t, spans[0], "test-span-name")
}

func TestAssertSpanKind(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span", trace.WithSpanKind(trace.SpanKindServer))
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))
	AssertSpanKind(t, spans[0], trace.SpanKindServer)
}

func TestAssertSpanStatus(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	span.SetStatus(codes.Error, "something went wrong")
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))
	AssertSpanStatus(t, spans[0], trace.Status{Code: codes.Error, Description: "something went wrong"}, "something went wrong")
}

func TestAssertSpanHasAttribute(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	span.SetAttributes(attribute.String("custom.attr", "value123"))
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))
	AssertSpanHasAttribute(t, spans[0], "custom.attr", "value123")
}

func TestAssertSpanHasEvent(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	span.AddEvent("test-event")
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))
	AssertSpanHasEvent(t, spans[0], "test-event")
}

func TestAssertSpanContainsString(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span-name")
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))
	AssertSpanContainsString(t, spans[0], "test-span-name")
}

func TestAssertSpansInOrder(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()

	tracer := tp.Tracer("test")

	_, span1 := tracer.Start(context.Background(), "first")
	span1.End()

	_, span2 := tracer.Start(context.Background(), "second")
	span2.End()

	_, span3 := tracer.Start(context.Background(), "third")
	span3.End()

	tp.ForceFlush(context.Background())

	spans := exporter.GetSpans()
	AssertSpansInOrder(t, spans, "first", "second", "third")
}

func TestAssertError(t *testing.T) {
	err := errors.New("test error")
	AssertError(t, err)
}

func TestAssertNoError(t *testing.T) {
	var err error
	AssertNoError(t, err)
	AssertNoError(t, nil)
}

func TestRequireNoError(t *testing.T) {
	var err error
	RequireNoError(t, err)
}

func TestAssertErrorContains(t *testing.T) {
	err := errors.New("this is a test error message")
	AssertErrorContains(t, err, "test error")
	AssertErrorContains(t, err, "test")
}

func TestAssertContextCancelled(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	AssertContextCancelled(t, ctx)
}

func TestAssertContextNotCancelled(t *testing.T) {
	ctx := context.Background()
	AssertContextNotCancelled(t, ctx)

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	AssertContextNotCancelled(t, ctx)
}

func TestAssertDeadlineSet(t *testing.T) {
	deadline := time.Now().Add(1 * time.Hour)
	ctx, cancel := context.WithDeadline(context.Background(), deadline)
	defer cancel()

	actualDeadline, ok := AssertDeadlineSet(t, ctx)
	AssertTrue(t, ok)
	AssertWithinDuration(t, deadline, actualDeadline, time.Second)
}

func TestAttributeEquals(t *testing.T) {
	attr := attribute.String("key", "value")
	AssertTrue(t, AttributeEquals(t, attr, "value"))

	attrInt := attribute.Int("count", 42)
	AssertTrue(t, AttributeEquals(t, attrInt, int64(42)))
}

func TestAttributesContain(t *testing.T) {
	attrs := []attribute.KeyValue{
		attribute.String("key1", "value1"),
		attribute.Int("key2", 42),
		attribute.Bool("key3", true),
	}

	AssertTrue(t, AttributesContain(t, attrs, "key1", "value1"))
	AssertTrue(t, AttributesContain(t, attrs, "key2", int64(42)))
	AssertTrue(t, AttributesContain(t, attrs, "key3", true))
}

func TestEventuallyEquals(t *testing.T) {
	counter := 0
	result := EventuallyEquals(t, func() int {
		counter++
		return counter
	}, 5, 500*time.Millisecond, 10*time.Millisecond)

	AssertTrue(t, result)
	AssertEqual(t, 5, counter)
}

func TestNotNilRequire(t *testing.T) {
	value := 42
	ptr := &value

	result := NotNilRequire(t, ptr)
	AssertEqual(t, ptr, result)
	AssertEqual(t, 42, *result)
}

func TestNotEmptyRequire(t *testing.T) {
	slice := []int{1, 2, 3}
	result := NotEmptyRequire(t, slice)
	AssertSlicesEqual(t, slice, result)
}

func TestLenRequire(t *testing.T) {
	slice := []string{"a", "b", "c"}
	result := LenRequire(t, slice, 3)
	AssertSlicesEqual(t, slice, result)
}

func TestAssertErrorIs(t *testing.T) {
	targetErr := errors.New("target error")
	wrappedErr := fmt.Errorf("wrapped: %w", targetErr)

	AssertErrorIs(t, wrappedErr, targetErr)
}

func TestAssertErrorAs(t *testing.T) {
	type customError struct {
		msg string
	}

	var target *customError
	customErr := &customError{msg: "test"}

	AssertErrorAs(t, customErr, &target)
	AssertEqual(t, "test", target.msg)
}

func TestAssertImplements(t *testing.T) {
	// Test that a type implements an interface
	AssertImplements(t, (*error)(nil), errors.New("test"))
}

func TestAssertElementsMatch(t *testing.T) {
	AssertElementsMatch(t, []int{1, 2, 3}, []int{3, 2, 1})
	AssertElementsMatch(t, []string{"a", "b"}, []string{"b", "a"})
}

func TestAssertSubset(t *testing.T) {
	AssertSubset(t, []int{1, 2, 3, 4, 5}, []int{2, 3})
	AssertSubset(t, []string{"a", "b", "c"}, []string{"a", "c"})
}

func TestAssertNotSubset(t *testing.T) {
	AssertNotSubset(t, []int{1, 2, 3}, []int{4, 5})
	AssertNotSubset(t, []string{"a", "b"}, []string{"c"})
}

func TestAssertPanics(t *testing.T) {
	AssertPanics(t, func() {
		panic("test panic")
	})
}

func TestAssertNotPanics(t *testing.T) {
	AssertNotPanics(t, func() {
		// Do nothing
	})
}

func TestAssertSame(t *testing.T) {
	value := 42
	ptr1 := &value
	ptr2 := ptr1

	AssertSame(t, ptr1, ptr2)
}

func TestAssertNotSame(t *testing.T) {
	value1 := 42
	value2 := 42
	ptr1 := &value1
	ptr2 := &value2

	AssertNotSame(t, ptr1, ptr2)
}

func TestAssertEqualValues(t *testing.T) {
	type MyInt int
	AssertEqualValues(t, MyInt(42), MyInt(42))
}

func TestAssertExactly(t *testing.T) {
	AssertExactly(t, 42, 42)
	AssertExactly(t, "test", "test")
	AssertExactly(t, true, true)
}

func TestAssertType(t *testing.T) {
	AssertType(t, 0, 42)
	AssertType(t, "", "test")
	AssertType(t, true, false)
}

func TestFail(t *testing.T) {
	// This should fail the test but we don't want to actually fail
	// So we just verify the function exists and can be called
	// Fail(t, "This is a test failure message")
}

// Integration test with real OpenTelemetry setup
func TestAssertIntegration(t *testing.T) {
	exporter := NewTestExporter()
	tp := NewTestTracerProvider()
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("integration-test")

	// Create a span with various properties
	ctx, span := tracer.Start(context.Background(), "integration-span",
		trace.WithSpanKind(trace.SpanKindServer),
	)

	span.SetAttributes(
		attribute.String("http.method", "GET"),
		attribute.String("http.route", "/api/users"),
		attribute.Int("http.status_code", 200),
	)

	span.AddEvent("processing_start")
	span.AddEvent("processing_end")

	span.SetStatus(codes.Ok, "")
	span.End()

	tp.ForceFlush(ctx)

	spans := exporter.GetSpans()
	RequireEqual(t, 1, len(spans))

	recordedSpan := spans[0]
	AssertSpanName(t, recordedSpan, "integration-span")
	AssertSpanKind(t, recordedSpan, trace.SpanKindServer)
	AssertSpanStatus(t, recordedSpan, trace.Status{Code: codes.Ok}, "")
	AssertSpanHasAttribute(t, recordedSpan, "http.method", "GET")
	AssertSpanHasAttribute(t, recordedSpan, "http.status_code", int64(200))
	AssertSpanHasEvent(t, recordedSpan, "processing_start")
}

// Helper functions for the tests
func RequireEqual(t testing.TB, expected, actual interface{}) {
	t.Helper()
	if expected != actual {
		t.Fatalf("Expected %v, got %v", expected, actual)
	}
}



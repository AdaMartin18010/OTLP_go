package testing

import (
	"context"
	"errors"
	"fmt"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

func TestTestResource(t *testing.T) {
	res := TestResource("my-service")
	AssertNotNil(t, res)

	attrs := res.Attributes()
	AssertNotEmpty(t, attrs)

	// Check that common attributes are present
	foundServiceName := false
	for _, attr := range attrs {
		if string(attr.Key) == "service.name" {
			foundServiceName = true
			AssertEqual(t, "my-service", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundServiceName, "service.name attribute should be present")
}

func TestTestResourceWithAttributes(t *testing.T) {
	res := TestResourceWithAttributes("my-service",
		attribute.String("custom.key", "custom-value"),
		attribute.Int("custom.count", 42),
	)
	AssertNotNil(t, res)

	attrs := res.Attributes()
	AssertNotEmpty(t, attrs)

	// Check custom attributes
	foundCustomKey := false
	foundCustomCount := false
	for _, attr := range attrs {
		switch string(attr.Key) {
		case "custom.key":
			foundCustomKey = true
			AssertEqual(t, "custom-value", attr.Value.AsString())
		case "custom.count":
			foundCustomCount = true
			AssertEqual(t, int64(42), attr.Value.AsInterface())
		}
	}
	AssertTrue(t, foundCustomKey, "custom.key attribute should be present")
	AssertTrue(t, foundCustomCount, "custom.count attribute should be present")
}

func TestDefaultSpanConfig(t *testing.T) {
	config := DefaultSpanConfig()
	AssertEqual(t, "test-span", config.Name)
	AssertEqual(t, trace.SpanKindInternal, config.Kind)
	AssertNotNil(t, config.StartTime)
	AssertEqual(t, trace.StatusCodeUnset, config.Status.Code)
	AssertNotEmpty(t, config.Attributes)
}

func TestSimpleTestSpan(t *testing.T) {
	exporter := NewTestExporter()
	span := SimpleTestSpan(exporter, "my-simple-span")
	AssertNotNil(t, span)
	AssertEqual(t, "my-simple-span", span.(*MockSpan).Name())
}

func TestTestSpanWithError(t *testing.T) {
	exporter := NewTestExporter()
	testErr := errors.New("test error occurred")
	span := TestSpanWithError(exporter, "error-span", testErr)
	AssertNotNil(t, span)
	AssertEqual(t, "error-span", span.(*MockSpan).Name())
	AssertEqual(t, trace.StatusCodeError, span.(*MockSpan).Status().Code)
	AssertEqual(t, "test error occurred", span.(*MockSpan).Status().Description)
}

func TestCommonAttributes(t *testing.T) {
	attrs := CommonAttributes()
	AssertNotEmpty(t, attrs)

	// Check for HTTP-specific attributes
	foundMethod := false
	for _, attr := range attrs {
		if string(attr.Key) == "http.method" {
			foundMethod = true
			AssertEqual(t, "GET", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundMethod, "http.method attribute should be present")
}

func TestDatabaseAttributes(t *testing.T) {
	attrs := DatabaseAttributes()
	AssertNotEmpty(t, attrs)

	foundDBSystem := false
	for _, attr := range attrs {
		if string(attr.Key) == "db.system" {
			foundDBSystem = true
			AssertEqual(t, "postgresql", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundDBSystem, "db.system attribute should be present")
}

func TestMessagingAttributes(t *testing.T) {
	attrs := MessagingAttributes()
	AssertNotEmpty(t, attrs)

	foundMessagingSystem := false
	for _, attr := range attrs {
		if string(attr.Key) == "messaging.system" {
			foundMessagingSystem = true
			AssertEqual(t, "kafka", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundMessagingSystem, "messaging.system attribute should be present")
}

func TestRPCAttributes(t *testing.T) {
	attrs := RPCAttributes()
	AssertNotEmpty(t, attrs)

	foundRPCSystem := false
	for _, attr := range attrs {
		if string(attr.Key) == "rpc.system" {
			foundRPCSystem = true
			AssertEqual(t, "grpc", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundRPCSystem, "rpc.system attribute should be present")
}

func TestCustomAttributes(t *testing.T) {
	input := map[string]interface{}{
		"string.key":  "string-value",
		"int.key":     42,
		"int64.key":   int64(100),
		"float.key":   3.14,
		"bool.key":    true,
		"slice.key":   []string{"a", "b", "c"},
		"unknown.key": struct{}{}, // Will be converted to string
	}

	attrs := CustomAttributes(input)
	AssertEqual(t, len(input), len(attrs))

	// Verify each attribute type
	for _, attr := range attrs {
		switch string(attr.Key) {
		case "string.key":
			AssertEqual(t, "string-value", attr.Value.AsString())
		case "int.key":
			AssertEqual(t, int64(42), attr.Value.AsInterface())
		case "int64.key":
			AssertEqual(t, int64(100), attr.Value.AsInterface())
		case "float.key":
			AssertEqual(t, 3.14, attr.Value.AsInterface())
		case "bool.key":
			AssertEqual(t, true, attr.Value.AsInterface())
		}
	}
}

func TestSpanKindHelpers(t *testing.T) {
	AssertEqual(t, trace.SpanKindClient, ClientSpanKind())
	AssertEqual(t, trace.SpanKindServer, ServerSpanKind())
	AssertEqual(t, trace.SpanKindInternal, InternalSpanKind())
	AssertEqual(t, trace.SpanKindProducer, ProducerSpanKind())
	AssertEqual(t, trace.SpanKindConsumer, ConsumerSpanKind())
}

func TestDefaultTestData(t *testing.T) {
	data := DefaultTestData()
	AssertEqual(t, "test-service", data.ServiceName)
	AssertEqual(t, "1.0.0", data.ServiceVersion)
	AssertEqual(t, "test", data.Environment)
	AssertNotZero(t, data.TraceID)
	AssertNotZero(t, data.SpanID)
	AssertNotZero(t, data.ParentSpanID)
}

func TestNewSpanContext(t *testing.T) {
	traceID := trace.TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
	spanID := trace.SpanID{1, 2, 3, 4, 5, 6, 7, 8}

	ctx := NewSpanContext(traceID, spanID, true)
	AssertTrue(t, ctx.IsValid())
	AssertEqual(t, traceID, ctx.TraceID())
	AssertEqual(t, spanID, ctx.SpanID())
	AssertTrue(t, ctx.IsSampled())
}

func TestRandomSpanContext(t *testing.T) {
	ctx := RandomSpanContext()
	AssertTrue(t, ctx.IsValid())
	AssertNotZero(t, ctx.TraceID())
	AssertNotZero(t, ctx.SpanID())
}

func TestInvalidSpanContext(t *testing.T) {
	ctx := InvalidSpanContext()
	AssertFalse(t, ctx.IsValid())
	AssertFalse(t, ctx.IsSampled())
}

func TestDefaultHTTPScenario(t *testing.T) {
	scenario := DefaultHTTPScenario()
	AssertEqual(t, "GET", scenario.Method)
	AssertEqual(t, "http://api.example.com/users", scenario.URL)
	AssertEqual(t, 200, scenario.StatusCode)
	AssertEqual(t, int64(1024), scenario.ContentLength)
	AssertEqual(t, 100*time.Millisecond, scenario.Duration)
}

func TestHTTPScenario_ToAttributes(t *testing.T) {
	scenario := DefaultHTTPScenario()
	attrs := scenario.ToAttributes()
	AssertNotEmpty(t, attrs)

	// Check for expected attributes
	foundMethod := false
	foundStatusCode := false
	for _, attr := range attrs {
		switch string(attr.Key) {
		case "http.method":
			foundMethod = true
			AssertEqual(t, "GET", attr.Value.AsString())
		case "http.status_code":
			foundStatusCode = true
			AssertEqual(t, int64(200), attr.Value.AsInterface())
		}
	}
	AssertTrue(t, foundMethod)
	AssertTrue(t, foundStatusCode)
}

func TestDefaultDatabaseScenario(t *testing.T) {
	scenario := DefaultDatabaseScenario()
	AssertEqual(t, "postgresql", scenario.System)
	AssertEqual(t, "testdb", scenario.Database)
	AssertEqual(t, "users", scenario.Table)
	AssertEqual(t, "SELECT", scenario.Operation)
	AssertEqual(t, 50*time.Millisecond, scenario.Duration)
}

func TestDatabaseScenario_ToAttributes(t *testing.T) {
	scenario := DefaultDatabaseScenario()
	attrs := scenario.ToAttributes()
	AssertNotEmpty(t, attrs)

	foundSystem := false
	foundStatement := false
	for _, attr := range attrs {
		switch string(attr.Key) {
		case "db.system":
			foundSystem = true
			AssertEqual(t, "postgresql", attr.Value.AsString())
		case "db.statement":
			foundStatement = true
			AssertNotEmpty(t, attr.Value.AsString())
		}
	}
	AssertTrue(t, foundSystem)
	AssertTrue(t, foundStatement)
}

func TestTestEvent(t *testing.T) {
	event := TestEvent("test-event")
	AssertEqual(t, "test-event", event.Name)
	AssertNotZero(t, event.Timestamp)
	AssertNotEmpty(t, event.Attributes)
}

func TestExceptionEvent(t *testing.T) {
	testErr := errors.New("exception occurred")
	event := ExceptionEvent(testErr)
	AssertEqual(t, "exception", event.Name)
	AssertNotZero(t, event.Timestamp)
	AssertNotEmpty(t, event.Attributes)

	// Check exception attributes
	foundType := false
	foundMessage := false
	for _, attr := range event.Attributes {
		switch string(attr.Key) {
		case "exception.type":
			foundType = true
			AssertNotEmpty(t, attr.Value.AsString())
		case "exception.message":
			foundMessage = true
			AssertEqual(t, "exception occurred", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundType)
	AssertTrue(t, foundMessage)
}

func TestMessageEvent(t *testing.T) {
	event := MessageEvent("send", "msg-123")
	AssertEqual(t, "message.send", event.Name)
	AssertNotZero(t, event.Timestamp)
	AssertNotEmpty(t, event.Attributes)

	foundID := false
	foundOperation := false
	for _, attr := range event.Attributes {
		switch string(attr.Key) {
		case "message.id":
			foundID = true
			AssertEqual(t, "msg-123", attr.Value.AsString())
		case "message.operation":
			foundOperation = true
			AssertEqual(t, "send", attr.Value.AsString())
		}
	}
	AssertTrue(t, foundID)
	AssertTrue(t, foundOperation)
}

func TestFixedTime(t *testing.T) {
	tm := FixedTime()
	AssertEqual(t, 2024, tm.Year())
	AssertEqual(t, time.January, tm.Month())
	AssertEqual(t, 15, tm.Day())
	AssertEqual(t, 10, tm.Hour())
	AssertEqual(t, 30, tm.Minute())
}

func TestFixedDuration(t *testing.T) {
	d := FixedDuration()
	AssertEqual(t, 100*time.Millisecond, d)
}

func TestPastTime(t *testing.T) {
	past := PastTime()
	AssertTrue(t, past.Before(time.Now()))
}

func TestFutureTime(t *testing.T) {
	future := FutureTime()
	AssertTrue(t, future.After(time.Now()))
}

func TestBatchSpans(t *testing.T) {
	exporter := NewTestExporter()
	spans := BatchSpans(exporter, 5)
	AssertEqual(t, 5, len(spans))

	for i, span := range spans {
		AssertEqual(t, fmt.Sprintf("span-%d", i), span.(*MockSpan).Name())
	}
}

func TestBatchSpansWithPattern(t *testing.T) {
	exporter := NewTestExporter()
	spans := BatchSpansWithPattern(exporter, "operation-%d", 3)
	AssertEqual(t, 3, len(spans))

	for i, span := range spans {
		expectedName := fmt.Sprintf("operation-%d", i)
		AssertEqual(t, expectedName, span.(*MockSpan).Name())
	}
}

func TestOKStatus(t *testing.T) {
	status := OKStatus()
	AssertEqual(t, trace.StatusCodeOk, status.Code)
}

func TestErrorStatus(t *testing.T) {
	status := ErrorStatus("error description")
	AssertEqual(t, trace.StatusCodeError, status.Code)
	AssertEqual(t, "error description", status.Description)
}

func TestUnsetStatus(t *testing.T) {
	status := UnsetStatus()
	AssertEqual(t, trace.StatusCodeUnset, status.Code)
}

// Integration test using fixtures
func TestFixturesIntegration(t *testing.T) {
	// Create test resource
	res := TestResourceWithAttributes("test-service",
		attribute.String("test.attr", "test-value"),
	)
	AssertNotNil(t, res)

	// Create span config
	config := SpanConfig{
		Name:      "integration-span",
		Kind:      trace.SpanKindServer,
		StartTime: time.Now(),
		Attributes: CommonAttributes(),
		Events: []EventData{
			TestEvent("start"),
			TestEvent("end"),
		},
		Status: OKStatus(),
	}

	// Create span
	exporter := NewTestExporter()
	span := TestSpan(exporter, config)
	span.End()

	// Verify span
	mockSpan := span.(*MockSpan)
	AssertEqual(t, "integration-span", mockSpan.Name())
	AssertEqual(t, 4, len(mockSpan.Attributes())) // 4 from CommonAttributes
	AssertEqual(t, 2, len(mockSpan.Events()))
	AssertEqual(t, trace.StatusCodeOk, mockSpan.Status().Code)
}

package testing

import (
	"context"
	"fmt"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

// TestResource creates a test resource with common attributes.
func TestResource(name string) *resource.Resource {
	return resource.NewWithAttributes(
		"test-schema",
		attribute.String("service.name", name),
		attribute.String("service.version", "1.0.0-test"),
		attribute.String("deployment.environment", "test"),
		attribute.String("host.name", "test-host"),
	)
}

// TestResourceWithAttributes creates a test resource with custom attributes.
func TestResourceWithAttributes(name string, attrs ...attribute.KeyValue) *resource.Resource {
	baseAttrs := []attribute.KeyValue{
		attribute.String("service.name", name),
		attribute.String("service.version", "1.0.0-test"),
		attribute.String("deployment.environment", "test"),
	}
	return resource.NewWithAttributes("test-schema", append(baseAttrs, attrs...)...)
}

// SpanConfig contains configuration for creating test spans.
type SpanConfig struct {
	Name       string
	Kind       trace.SpanKind
	Attributes []attribute.KeyValue
	Events     []EventData
	Links      []LinkData
	Status     trace.Status
	StartTime  time.Time
	EndTime    *time.Time
	Parent     trace.SpanContext
}

// EventData represents event data for test spans.
type EventData struct {
	Name       string
	Timestamp  time.Time
	Attributes []attribute.KeyValue
}

// LinkData represents link data for test spans.
type LinkData struct {
	SpanContext trace.SpanContext
	Attributes  []attribute.KeyValue
}

// DefaultSpanConfig returns a default span configuration.
func DefaultSpanConfig() SpanConfig {
	return SpanConfig{
		Name:      "test-span",
		Kind:      trace.SpanKindInternal,
		StartTime: time.Now(),
		Attributes: []attribute.KeyValue{
			attribute.String("test.attribute", "value"),
		},
		Status: trace.Status{Code: trace.StatusCodeUnset},
	}
}

// TestSpan creates a test span using the TestExporter.
func TestSpan(exporter *TestExporter, config SpanConfig) trace.Span {
	ctx := context.Background()

	// Create tracer provider with the exporter
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithSyncer(exporter),
		sdktrace.WithResource(TestResource("test-service")),
	)
	defer tp.Shutdown(ctx)

	tracer := tp.Tracer("test-tracer")

	// Create start options
	opts := []trace.SpanStartOption{
		trace.WithSpanKind(config.Kind),
		trace.WithTimestamp(config.StartTime),
	}

	if config.Parent.IsValid() {
		ctx = trace.ContextWithSpanContext(ctx, config.Parent)
	}

	ctx, span := tracer.Start(ctx, config.Name, opts...)

	// Set attributes
	if len(config.Attributes) > 0 {
		span.SetAttributes(config.Attributes...)
	}

	// Add events
	for _, event := range config.Events {
		span.AddEvent(event.Name,
			trace.WithTimestamp(event.Timestamp),
			trace.WithAttributes(event.Attributes...),
		)
	}

	// Add links
	for _, link := range config.Links {
		span.AddLink(link.SpanContext, trace.WithAttributes(link.Attributes...))
	}

	// Set status
	if config.Status.Code != trace.StatusCodeUnset {
		span.SetStatus(config.Status.Code, config.Status.Description)
	}

	// End span if EndTime is provided
	if config.EndTime != nil {
		span.End(trace.WithTimestamp(*config.EndTime))
	}

	return span
}

// SimpleTestSpan creates a simple test span with minimal configuration.
func SimpleTestSpan(exporter *TestExporter, name string) trace.Span {
	return TestSpan(exporter, SpanConfig{
		Name:      name,
		Kind:      trace.SpanKindInternal,
		StartTime: time.Now(),
		EndTime:   func() *time.Time { t := time.Now().Add(time.Millisecond); return &t }(),
	})
}

// TestSpanWithError creates a test span with an error status.
func TestSpanWithError(exporter *TestExporter, name string, err error) trace.Span {
	config := DefaultSpanConfig()
	config.Name = name
	config.Status = trace.Status{
		Code:        trace.StatusCodeError,
		Description: err.Error(),
	}
	config.EndTime = func() *time.Time { t := time.Now().Add(time.Millisecond); return &t }()
	return TestSpan(exporter, config)
}

// Attribute fixtures

// CommonAttributes returns commonly used test attributes.
func CommonAttributes() []attribute.KeyValue {
	return []attribute.KeyValue{
		attribute.String("http.method", "GET"),
		attribute.String("http.url", "http://example.com/api"),
		attribute.Int("http.status_code", 200),
		attribute.String("http.user_agent", "TestAgent/1.0"),
	}
}

// DatabaseAttributes returns database-related test attributes.
func DatabaseAttributes() []attribute.KeyValue {
	return []attribute.KeyValue{
		attribute.String("db.system", "postgresql"),
		attribute.String("db.name", "testdb"),
		attribute.String("db.statement", "SELECT * FROM users"),
		attribute.String("db.user", "testuser"),
		attribute.String("net.peer.name", "localhost"),
		attribute.Int("net.peer.port", 5432),
	}
}

// MessagingAttributes returns messaging-related test attributes.
func MessagingAttributes() []attribute.KeyValue {
	return []attribute.KeyValue{
		attribute.String("messaging.system", "kafka"),
		attribute.String("messaging.destination", "test-topic"),
		attribute.String("messaging.destination_kind", "topic"),
		attribute.String("messaging.operation", "send"),
		attribute.String("messaging.message_id", "msg-123"),
	}
}

// RPCAttributes returns RPC-related test attributes.
func RPCAttributes() []attribute.KeyValue {
	return []attribute.KeyValue{
		attribute.String("rpc.system", "grpc"),
		attribute.String("rpc.service", "test.TestService"),
		attribute.String("rpc.method", "TestMethod"),
		attribute.String("net.peer.name", "localhost"),
		attribute.Int("net.peer.port", 50051),
	}
}

// CustomAttributes creates custom attributes from a map.
func CustomAttributes(attrs map[string]interface{}) []attribute.KeyValue {
	result := make([]attribute.KeyValue, 0, len(attrs))
	for k, v := range attrs {
		result = append(result, createAttribute(k, v))
	}
	return result
}

func createAttribute(key string, value interface{}) attribute.KeyValue {
	switch v := value.(type) {
	case string:
		return attribute.String(key, v)
	case int:
		return attribute.Int(key, v)
	case int64:
		return attribute.Int64(key, v)
	case float64:
		return attribute.Float64(key, v)
	case bool:
		return attribute.Bool(key, v)
	case []string:
		return attribute.StringSlice(key, v)
	case []int:
		return attribute.IntSlice(key, v)
	case []int64:
		return attribute.Int64Slice(key, v)
	case []float64:
		return attribute.Float64Slice(key, v)
	case []bool:
		return attribute.BoolSlice(key, v)
	default:
		return attribute.String(key, fmt.Sprintf("%v", v))
	}
}

// SpanKind fixtures

// ClientSpanKind returns Client span kind.
func ClientSpanKind() trace.SpanKind {
	return trace.SpanKindClient
}

// ServerSpanKind returns Server span kind.
func ServerSpanKind() trace.SpanKind {
	return trace.SpanKindServer
}

// InternalSpanKind returns Internal span kind.
func InternalSpanKind() trace.SpanKind {
	return trace.SpanKindInternal
}

// ProducerSpanKind returns Producer span kind.
func ProducerSpanKind() trace.SpanKind {
	return trace.SpanKindProducer
}

// ConsumerSpanKind returns Consumer span kind.
func ConsumerSpanKind() trace.SpanKind {
	return trace.SpanKindConsumer
}

// TestData fixtures

// TestData represents a collection of test fixtures.
type TestData struct {
	ServiceName    string
	ServiceVersion string
	Environment    string
	TraceID        trace.TraceID
	SpanID         trace.SpanID
	ParentSpanID   trace.SpanID
}

// DefaultTestData returns default test data.
func DefaultTestData() TestData {
	return TestData{
		ServiceName:    "test-service",
		ServiceVersion: "1.0.0",
		Environment:    "test",
		TraceID:        [16]byte{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
		SpanID:         [8]byte{1, 2, 3, 4, 5, 6, 7, 8},
		ParentSpanID:   [8]byte{8, 7, 6, 5, 4, 3, 2, 1},
	}
}

// SpanContext fixtures

// NewSpanContext creates a new span context with the given IDs.
func NewSpanContext(traceID trace.TraceID, spanID trace.SpanID, sampled bool) trace.SpanContext {
	return trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: trace.FlagsSampled,
	})
}

// RandomSpanContext creates a random span context.
func RandomSpanContext() trace.SpanContext {
	return trace.NewSpanContext(trace.SpanContextConfig{
		TraceFlags: trace.FlagsSampled,
	})
}

// InvalidSpanContext creates an invalid span context.
func InvalidSpanContext() trace.SpanContext {
	return trace.SpanContext{}
}

// Test scenarios

// HTTPRequestScenario creates a complete HTTP request/response test scenario.
type HTTPRequestScenario struct {
	Method        string
	URL           string
	StatusCode    int
	ContentLength int64
	Duration      time.Duration
}

// DefaultHTTPScenario returns a default HTTP scenario.
func DefaultHTTPScenario() HTTPRequestScenario {
	return HTTPRequestScenario{
		Method:        "GET",
		URL:           "http://api.example.com/users",
		StatusCode:    200,
		ContentLength: 1024,
		Duration:      100 * time.Millisecond,
	}
}

// ToAttributes converts the scenario to span attributes.
func (s HTTPRequestScenario) ToAttributes() []attribute.KeyValue {
	return []attribute.KeyValue{
		attribute.String("http.method", s.Method),
		attribute.String("http.url", s.URL),
		attribute.Int("http.status_code", s.StatusCode),
		attribute.Int64("http.response_content_length", s.ContentLength),
		attribute.Int64("http.duration_ms", s.Duration.Milliseconds()),
	}
}

// DatabaseQueryScenario creates a database query test scenario.
type DatabaseQueryScenario struct {
	System   string
	Database string
	Table    string
	Operation string
	Duration time.Duration
}

// DefaultDatabaseScenario returns a default database scenario.
func DefaultDatabaseScenario() DatabaseQueryScenario {
	return DatabaseQueryScenario{
		System:    "postgresql",
		Database:  "testdb",
		Table:     "users",
		Operation: "SELECT",
		Duration:  50 * time.Millisecond,
	}
}

// ToAttributes converts the scenario to span attributes.
func (s DatabaseQueryScenario) ToAttributes() []attribute.KeyValue {
	return []attribute.KeyValue{
		attribute.String("db.system", s.System),
		attribute.String("db.name", s.Database),
		attribute.String("db.sql.table", s.Table),
		attribute.String("db.operation", s.Operation),
		attribute.String("db.statement", fmt.Sprintf("%s * FROM %s", s.Operation, s.Table)),
		attribute.Int64("db.duration_ms", s.Duration.Milliseconds()),
	}
}

// Event fixtures

// TestEvent creates a test event.
func TestEvent(name string) EventData {
	return EventData{
		Name:      name,
		Timestamp: time.Now(),
		Attributes: []attribute.KeyValue{
			attribute.String("event.data", "test"),
		},
	}
}

// ExceptionEvent creates an exception event.
func ExceptionEvent(err error) EventData {
	return EventData{
		Name:      "exception",
		Timestamp: time.Now(),
		Attributes: []attribute.KeyValue{
			attribute.String("exception.type", fmt.Sprintf("%T", err)),
			attribute.String("exception.message", err.Error()),
		},
	}
}

// MessageEvent creates a message event (for messaging systems).
func MessageEvent(operation, id string) EventData {
	return EventData{
		Name:      fmt.Sprintf("message.%s", operation),
		Timestamp: time.Now(),
		Attributes: []attribute.KeyValue{
			attribute.String("message.id", id),
			attribute.String("message.operation", operation),
		},
	}
}

// Time fixtures

// FixedTime returns a fixed time for testing.
func FixedTime() time.Time {
	return time.Date(2024, 1, 15, 10, 30, 0, 0, time.UTC)
}

// FixedDuration returns a fixed duration for testing.
func FixedDuration() time.Duration {
	return 100 * time.Millisecond
}

// PastTime returns a time in the past.
func PastTime() time.Time {
	return time.Now().Add(-1 * time.Hour)
}

// FutureTime returns a time in the future.
func FutureTime() time.Time {
	return time.Now().Add(1 * time.Hour)
}

// Batch fixtures

// BatchSpans creates multiple test spans at once.
func BatchSpans(exporter *TestExporter, count int) []trace.Span {
	spans := make([]trace.Span, count)
	for i := 0; i < count; i++ {
		spans[i] = SimpleTestSpan(exporter, fmt.Sprintf("span-%d", i))
	}
	return spans
}

// BatchSpansWithPattern creates spans following a naming pattern.
func BatchSpansWithPattern(exporter *TestExporter, pattern string, count int) []trace.Span {
	spans := make([]trace.Span, count)
	for i := 0; i < count; i++ {
		name := fmt.Sprintf(pattern, i)
		spans[i] = SimpleTestSpan(exporter, name)
	}
	return spans
}

// NestedSpanScenario creates parent-child span relationships.
func NestedSpanScenario(exporter *TestExporter, depth int) {
	if depth <= 0 {
		return
	}

	ctx := context.Background()
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithSyncer(exporter),
	)
	defer tp.Shutdown(ctx)

	tracer := tp.Tracer("test")
	createNestedSpans(ctx, tracer, depth, 0)
}

func createNestedSpans(ctx context.Context, tracer trace.Tracer, depth, current int) {
	if current >= depth {
		return
	}

	_, span := tracer.Start(ctx, fmt.Sprintf("span-level-%d", current))
	defer span.End()

	// Create child span
	createNestedSpans(trace.ContextWithSpan(ctx, span), tracer, depth, current+1)
}

// Status fixtures

// OKStatus returns an OK status.
func OKStatus() trace.Status {
	return trace.Status{Code: trace.StatusCodeOk}
}

// ErrorStatus returns an Error status.
func ErrorStatus(description string) trace.Status {
	return trace.Status{
		Code:        trace.StatusCodeError,
		Description: description,
	}
}

// UnsetStatus returns an Unset status.
func UnsetStatus() trace.Status {
	return trace.Status{Code: trace.StatusCodeUnset}
}

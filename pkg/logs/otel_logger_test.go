package logs

import (
	"bytes"
	"context"
	"strings"
	"sync"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

func TestDefaultTracePropagator_Inject(t *testing.T) {
	propagator := &DefaultTracePropagator{}
	record := &LogRecord{}

	// Create a span context
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")
	spanID, _ := trace.SpanIDFromHex("0123456789abcdef")
	spanCtx := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: trace.FlagsSampled,
	})

	ctx := trace.ContextWithSpanContext(context.Background(), spanCtx)
	propagator.Inject(ctx, record)

	if record.TraceID != traceID {
		t.Error("TraceID not injected correctly")
	}
	if record.SpanID != spanID {
		t.Error("SpanID not injected correctly")
	}
}

func TestDefaultTracePropagator_Extract(t *testing.T) {
	propagator := &DefaultTracePropagator{}

	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")
	spanID, _ := trace.SpanIDFromHex("0123456789abcdef")
	record := &LogRecord{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: trace.FlagsSampled,
	}

	ctx := propagator.Extract(context.Background(), record)
	spanCtx := trace.SpanContextFromContext(ctx)

	if spanCtx.TraceID() != traceID {
		t.Error("TraceID not extracted correctly")
	}
	if spanCtx.SpanID() != spanID {
		t.Error("SpanID not extracted correctly")
	}
}

func TestDefaultTracePropagator_Extract_Invalid(t *testing.T) {
	propagator := &DefaultTracePropagator{}
	record := &LogRecord{} // Empty record

	ctx := propagator.Extract(context.Background(), record)
	spanCtx := trace.SpanContextFromContext(ctx)

	if spanCtx.IsValid() {
		t.Error("Should not extract valid span context from empty record")
	}
}

func TestNewOTelLogger(t *testing.T) {
	config := OTelLoggerConfig{
		Config: Config{
			Level: LevelInfo,
		},
	}

	logger := NewOTelLogger(config)
	if logger == nil {
		t.Fatal("NewOTelLogger() returned nil")
	}
	if logger.StructuredLogger == nil {
		t.Error("OTelLogger.StructuredLogger is nil")
	}
}

func TestOTelLogger_WithTrace(t *testing.T) {
	// Create a real tracer provider and span
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(context.Background())
	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	config := OTelLoggerConfig{
		Config: Config{
			Level: LevelInfo,
		},
	}
	logger := NewOTelLogger(config)

	tracedLogger := logger.WithTrace(span)

	if tracedLogger == nil {
		t.Error("WithTrace() returned nil")
	}
	_ = ctx
}

func TestOTelLogger_WithSpanContext(t *testing.T) {
	config := OTelLoggerConfig{
		Config: Config{
			Level: LevelInfo,
		},
	}
	logger := NewOTelLogger(config)

	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")
	spanID, _ := trace.SpanIDFromHex("0123456789abcdef")
	spanCtx := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID: traceID,
		SpanID:  spanID,
	})

	tracedLogger := logger.WithSpanContext(spanCtx)
	if tracedLogger == nil {
		t.Error("WithSpanContext() returned nil")
	}

	// Test with invalid span context
	invalidLogger := logger.WithSpanContext(trace.SpanContext{})
	if invalidLogger == nil {
		t.Error("WithSpanContext() with invalid context returned nil")
	}
}

func TestOTelLogger_StartSpan(t *testing.T) {
	// Create a tracer provider
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(context.Background())

	var buf bytes.Buffer
	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &buf,
		},
		TracerProvider: tp,
		TracerName:     "test",
	}
	logger := NewOTelLogger(config)

	ctx := context.Background()
	ctx, span := logger.StartSpan(ctx, "test-operation")

	if span == nil {
		t.Error("StartSpan() returned nil span")
	} else {
		span.End()
	}

	// Test without tracer provider
	config2 := OTelLoggerConfig{
		Config: Config{Level: LevelInfo},
	}
	logger2 := NewOTelLogger(config2)
	ctx2, span2 := logger2.StartSpan(ctx, "test")
	if span2 != nil {
		t.Error("StartSpan() should return nil span without tracer provider")
	}
	_ = ctx2
}

func TestOTelLogger_LogSpanEvent(t *testing.T) {
	var buf bytes.Buffer
	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &buf,
		},
	}
	logger := NewOTelLogger(config)

	ctx := context.Background()
	logger.LogSpanEvent(ctx, "test-event", attribute.String("key", "value"))

	output := buf.String()
	if !strings.Contains(output, "test-event") {
		t.Errorf("LogSpanEvent output missing event name: %s", output)
	}
}

func TestOTelLogger_LogError(t *testing.T) {
	var buf bytes.Buffer
	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &buf,
		},
	}
	logger := NewOTelLogger(config)

	ctx := context.Background()
	testErr := &testError{msg: "test error"}
	logger.LogError(ctx, testErr, String("context", "testing"))

	output := buf.String()
	if !strings.Contains(output, "test error") {
		t.Errorf("LogError output missing error message: %s", output)
	}
}

func TestNewTraceLogger(t *testing.T) {
	var buf bytes.Buffer
	baseLogger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	traceLogger := NewTraceLogger(baseLogger, nil)
	if traceLogger == nil {
		t.Fatal("NewTraceLogger() returned nil")
	}

	ctx := context.Background()
	traceLogger.Log(ctx, LevelInfo, "test message")

	if buf.Len() == 0 {
		t.Error("TraceLogger did not produce output")
	}
}

func TestNewTraceLogger_WithPropagator(t *testing.T) {
	var buf bytes.Buffer
	baseLogger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	propagator := &DefaultTracePropagator{}
	traceLogger := NewTraceLogger(baseLogger, propagator)

	// Create context with span
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")
	spanID, _ := trace.SpanIDFromHex("0123456789abcdef")
	spanCtx := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID: traceID,
		SpanID:  spanID,
	})
	ctx := trace.ContextWithSpanContext(context.Background(), spanCtx)

	traceLogger.Log(ctx, LevelInfo, "traced message")

	output := buf.String()
	if !strings.Contains(output, "trace_id") {
		t.Errorf("Output should contain trace_id: %s", output)
	}
}

func TestTraceLogger_Log_Disabled(t *testing.T) {
	var buf bytes.Buffer
	baseLogger := NewLogger(Config{
		Level:  LevelWarn,
		Output: &buf,
	})

	traceLogger := NewTraceLogger(baseLogger, nil)
	ctx := context.Background()
	traceLogger.Log(ctx, LevelInfo, "should not appear")

	if buf.Len() > 0 {
		t.Error("Disabled level should not produce output")
	}
}

func TestLevelToSeverity(t *testing.T) {
	tests := []struct {
		level    Level
		expected SeverityNumber
	}{
		{LevelTrace, SeverityTrace},
		{LevelDebug, SeverityDebug},
		{LevelInfo, SeverityInfo},
		{LevelWarn, SeverityWarn},
		{LevelError, SeverityError},
		{LevelFatal, SeverityFatal},
		{Level(999), SeverityInfo},
	}

	for _, tt := range tests {
		t.Run(tt.level.String(), func(t *testing.T) {
			if got := levelToSeverity(tt.level); got != tt.expected {
				t.Errorf("levelToSeverity(%v) = %v, want %v", tt.level, got, tt.expected)
			}
		})
	}
}

func TestLogCorrelator(t *testing.T) {
	lc := NewLogCorrelator(10)
	if lc == nil {
		t.Fatal("NewLogCorrelator() returned nil")
	}

	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")

	// Add logs
	for i := 0; i < 5; i++ {
		record := &CorrelatedLogRecord{
			LogRecord: &LogRecord{
				TraceID: traceID,
				Body:    "log message",
			},
		}
		lc.Add(record)
	}

	// Get logs
	logs := lc.GetLogs(traceID)
	if len(logs) != 5 {
		t.Errorf("GetLogs returned %d logs, want 5", len(logs))
	}

	// Clear specific trace
	lc.Clear(traceID)
	logs = lc.GetLogs(traceID)
	if len(logs) != 0 {
		t.Error("Clear should remove all logs for trace")
	}

	// Test Add with invalid trace ID
	invalidRecord := &CorrelatedLogRecord{
		LogRecord: &LogRecord{
			Body: "no trace",
		},
	}
	lc.Add(invalidRecord) // Should not panic
}

func TestLogCorrelator_MaxPerTrace(t *testing.T) {
	lc := NewLogCorrelator(3)
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")

	// Add more than max
	for i := 0; i < 5; i++ {
		record := &CorrelatedLogRecord{
			LogRecord: &LogRecord{
				TraceID: traceID,
				Body:    "log message",
			},
		}
		lc.Add(record)
	}

	logs := lc.GetLogs(traceID)
	if len(logs) != 3 {
		t.Errorf("Should limit to max per trace, got %d", len(logs))
	}
}

func TestLogCorrelator_ClearAll(t *testing.T) {
	lc := NewLogCorrelator(10)
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")

	record := &CorrelatedLogRecord{
		LogRecord: &LogRecord{
			TraceID: traceID,
			Body:    "log message",
		},
	}
	lc.Add(record)

	lc.ClearAll()
	logs := lc.GetLogs(traceID)
	if len(logs) != 0 {
		t.Error("ClearAll should remove all logs")
	}
}

func TestLogCorrelator_Concurrent(t *testing.T) {
	lc := NewLogCorrelator(1000)
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")

	var wg sync.WaitGroup
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func(n int) {
			defer wg.Done()
			record := &CorrelatedLogRecord{
				LogRecord: &LogRecord{
					TraceID: traceID,
					Body:    "message",
				},
			}
			lc.Add(record)
		}(i)
	}
	wg.Wait()

	logs := lc.GetLogs(traceID)
	if len(logs) != 100 {
		t.Errorf("Expected 100 logs, got %d", len(logs))
	}
}

func TestNewSpanEventLogger(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	spanLogger := NewSpanEventLogger(logger, nil)
	if spanLogger == nil {
		t.Fatal("NewSpanEventLogger() returned nil")
	}

	// Test Event without span
	spanLogger.Event("test-event")

	// Create a real span for testing
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(context.Background())
	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	spanLogger2 := NewSpanEventLogger(logger, span)
	spanLogger2.Event("span-event", attribute.String("key", "value"))

	_ = ctx
}

func TestSpanEventLogger_SetStatus(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	spanLogger := NewSpanEventLogger(logger, nil)
	spanLogger.SetStatus(codes.Error, "error occurred")

	output := buf.String()
	if !strings.Contains(output, "error occurred") {
		t.Errorf("SetStatus should log: %s", output)
	}
}

func TestSpanEventLogger_SetAttributes(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	// Test with nil span - should not panic
	spanLogger := NewSpanEventLogger(logger, nil)
	spanLogger.SetAttributes(attribute.String("key", "value"))
}

func TestSpanEventLogger_TraceID(t *testing.T) {
	logger := NewLogger(Config{Level: LevelInfo})

	// With nil span
	spanLogger := NewSpanEventLogger(logger, nil)
	if spanLogger.TraceID().IsValid() {
		t.Error("TraceID should not be valid with nil span")
	}
	if spanLogger.SpanID().IsValid() {
		t.Error("SpanID should not be valid with nil span")
	}
	if spanLogger.IsRecording() {
		t.Error("IsRecording should be false with nil span")
	}
}

func TestTracedLogger(t *testing.T) {
	var buf bytes.Buffer
	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &buf,
		},
	}
	oLogger := NewOTelLogger(config)
	ctx := context.Background()
	tracedLogger := oLogger.WithContext(ctx)

	if tracedLogger == nil {
		t.Fatal("WithContext() returned nil")
	}

	tests := []struct {
		name string
		fn   func()
	}{
		{"Debug", func() { tracedLogger.Debug("debug message") }},
		{"Info", func() { tracedLogger.Info("info message") }},
		{"Warn", func() { tracedLogger.Warn("warn message") }},
		{"Error", func() { tracedLogger.Error("error message") }},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			buf.Reset()
			tt.fn()
			// Note: Debug might be filtered
		})
	}

	// Test Context
	if tracedLogger.Context() != ctx {
		t.Error("Context() should return the underlying context")
	}
}

func TestTracedLogger_Trace(t *testing.T) {
	var buf bytes.Buffer
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(context.Background())

	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &buf,
		},
		TracerProvider: tp,
		TracerName:     "test",
	}
	oLogger := NewOTelLogger(config)
	ctx := context.Background()
	tracedLogger := oLogger.WithContext(ctx)

	spanLogger := tracedLogger.Trace("test-operation")
	if spanLogger == nil {
		t.Fatal("Trace() returned nil")
	}

	// Test Span() with current context
	spanLogger2 := tracedLogger.Span()
	if spanLogger2 == nil {
		t.Error("Span() returned nil")
	}
}

func TestFromContext(t *testing.T) {
	// Empty context
	tc := FromContext(context.Background())
	if tc.TraceID != "" {
		t.Error("Empty context should return empty TraceContext")
	}

	// Context with span
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(context.Background())
	tracer := tp.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	tc = FromContext(ctx)
	if tc.TraceID == "" {
		t.Error("Should extract TraceID from context")
	}
	if tc.SpanID == "" {
		t.Error("Should extract SpanID from context")
	}
	if !tc.Sampled {
		t.Error("Should detect sampled flag")
	}
}

func TestTraceContext_InjectToFields(t *testing.T) {
	tc := TraceContext{
		TraceID: "abc123",
		SpanID:  "def456",
		Sampled: true,
	}

	fields := tc.InjectToFields(String("custom", "value"))
	if len(fields) != 4 { // 3 trace fields + 1 custom
		t.Errorf("Expected 4 fields, got %d", len(fields))
	}

	// Test with empty TraceID
	emptyTC := TraceContext{}
	fields2 := emptyTC.InjectToFields(String("key", "value"))
	if len(fields2) != 1 {
		t.Errorf("Expected 1 field for empty context, got %d", len(fields2))
	}
}

func TestLogBaggage(t *testing.T) {
	var buf bytes.Buffer
	logger := NewLogger(Config{
		Level:  LevelInfo,
		Output: &buf,
	})

	items := []BaggageItem{
		{Key: "user", Value: "john"},
		{Key: "tenant", Value: "acme"},
	}
	LogBaggage(logger, items...)

	output := buf.String()
	if !strings.Contains(output, "baggage.user") {
		t.Errorf("Output should contain baggage: %s", output)
	}
}

func TestNewTraceSampler(t *testing.T) {
	sampler := NewTraceSampler()

	// Sampled trace
	record := &LogRecord{
		TraceFlags: trace.FlagsSampled,
	}
	if !sampler.ShouldSample(record) {
		t.Error("Should sample when trace is sampled")
	}

	// Unsampled trace
	record2 := &LogRecord{
		TraceFlags: 0,
	}
	if sampler.ShouldSample(record2) {
		t.Error("Should not sample when trace is not sampled")
	}
}

func TestCompositeSampler(t *testing.T) {
	t.Run("And", func(t *testing.T) {
		sampler := NewCompositeSampler(CompositeAnd,
			AlwaysSample,
			AlwaysSample,
		)
		if !sampler.ShouldSample(&LogRecord{}) {
			t.Error("AND with all true should return true")
		}

		sampler2 := NewCompositeSampler(CompositeAnd,
			AlwaysSample,
			NeverSample,
		)
		if sampler2.ShouldSample(&LogRecord{}) {
			t.Error("AND with one false should return false")
		}
	})

	t.Run("Or", func(t *testing.T) {
		sampler := NewCompositeSampler(CompositeOr,
			NeverSample,
			AlwaysSample,
		)
		if !sampler.ShouldSample(&LogRecord{}) {
			t.Error("OR with one true should return true")
		}

		sampler2 := NewCompositeSampler(CompositeOr,
			NeverSample,
			NeverSample,
		)
		if sampler2.ShouldSample(&LogRecord{}) {
			t.Error("OR with all false should return false")
		}
	})

	t.Run("Empty", func(t *testing.T) {
		sampler := NewCompositeSampler(CompositeAnd)
		if !sampler.ShouldSample(&LogRecord{}) {
			t.Error("Empty AND should return true")
		}

		sampler2 := NewCompositeSampler(CompositeOr)
		if sampler2.ShouldSample(&LogRecord{}) {
			t.Error("Empty OR should return false")
		}
	})
}

func TestNewLevelSampler(t *testing.T) {
	sampler := NewLevelSampler(LevelWarn)

	tests := []struct {
		severity SeverityNumber
		expected bool
	}{
		{SeverityDebug, false},
		{SeverityInfo, false},
		{SeverityWarn, true},
		{SeverityError, true},
		{SeverityFatal, true},
	}

	for _, tt := range tests {
		t.Run(tt.severity.String(), func(t *testing.T) {
			record := &LogRecord{SeverityNumber: tt.severity}
			if got := sampler.ShouldSample(record); got != tt.expected {
				t.Errorf("ShouldSample(%v) = %v, want %v", tt.severity, got, tt.expected)
			}
		})
	}
}

func TestNewConfigurableOTelLogger(t *testing.T) {
	var called bool
	onChange := func(config OTelLoggerConfig) {
		called = true
	}

	config := OTelLoggerConfig{
		Config: Config{
			Level: LevelInfo,
		},
	}

	logger := NewConfigurableOTelLogger(config, onChange)
	if logger == nil {
		t.Fatal("NewConfigurableOTelLogger() returned nil")
	}

	// Test GetConfig
	if logger.GetConfig().Level != LevelInfo {
		t.Error("GetConfig returned wrong level")
	}

	// Test UpdateConfig
	newConfig := OTelLoggerConfig{
		Config: Config{
			Level: LevelDebug,
		},
	}
	logger.UpdateConfig(newConfig)

	if !called {
		t.Error("onChange callback should have been called")
	}

	if logger.GetLevel() != LevelDebug {
		t.Error("UpdateConfig should update the level")
	}
}

func TestSetupOTelLogger(t *testing.T) {
	logger, err := SetupOTelLogger("test-service")
	if err != nil {
		t.Fatalf("SetupOTelLogger() error = %v", err)
	}
	if logger == nil {
		t.Fatal("SetupOTelLogger() returned nil")
	}
}

func TestSetupOTelLogger_WithOptions(t *testing.T) {
	tp := sdktrace.NewTracerProvider()
	defer tp.Shutdown(context.Background())

	r := resource.NewWithAttributes("test")

	logger, err := SetupOTelLogger("test-service",
		WithOTelLevel(LevelDebug),
		WithOTelTracerProvider(tp),
		WithOTelResource(r),
	)
	if err != nil {
		t.Fatalf("SetupOTelLogger() error = %v", err)
	}
	if logger == nil {
		t.Fatal("SetupOTelLogger() returned nil")
	}
	if logger.GetLevel() != LevelDebug {
		t.Error("WithOTelLevel should set the level")
	}
}

func TestTraceSpanEvent_ToLogRecord(t *testing.T) {
	event := &TraceSpanEvent{
		Timestamp:  time.Now(),
		Name:       "test-event",
		Attributes: []attribute.KeyValue{attribute.String("key", "value")},
		Level:      LevelInfo,
	}

	record := event.ToLogRecord()
	if record == nil {
		t.Fatal("ToLogRecord() returned nil")
	}
	if record.Body != "test-event" {
		t.Errorf("Body = %v, want 'test-event'", record.Body)
	}
	if record.SeverityNumber != SeverityInfo {
		t.Errorf("SeverityNumber = %v, want SeverityInfo", record.SeverityNumber)
	}
}

func TestNewOTelSpanProcessor(t *testing.T) {
	var buf bytes.Buffer
	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &buf,
		},
	}
	logger := NewOTelLogger(config)

	processor := NewOTelSpanProcessor(logger)
	if processor == nil {
		t.Fatal("NewOTelSpanProcessor() returned nil")
	}

	ctx := context.Background()

	// Test OnStart
	tp := sdktrace.NewTracerProvider(sdktrace.WithSpanProcessor(processor))
	defer tp.Shutdown(ctx)
	tracer := tp.Tracer("test")
	_, span := tracer.Start(ctx, "test-span")
	span.End()

	// Test Shutdown
	if err := processor.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown() error = %v", err)
	}

	// Test ForceFlush
	if err := processor.ForceFlush(ctx); err != nil {
		t.Errorf("ForceFlush() error = %v", err)
	}
}

var _ sdktrace.SpanProcessor = (*OTelSpanProcessor)(nil)

func TestIsValidTraceID(t *testing.T) {
	tests := []struct {
		id       string
		expected bool
	}{
		{"0123456789abcdef0123456789abcdef", true},
		{"0123456789ABCDEF0123456789ABCDEF", true},
		{"0123456789abcdef", false},                   // Too short
		{"0123456789abcdef0123456789abcdef00", false}, // Too long
		{"0123456789abcdef0123456789abcdeg", false},   // Invalid char
		{"", false},
	}

	for _, tt := range tests {
		t.Run(tt.id, func(t *testing.T) {
			if got := IsValidTraceID(tt.id); got != tt.expected {
				t.Errorf("IsValidTraceID(%q) = %v, want %v", tt.id, got, tt.expected)
			}
		})
	}
}

func TestIsValidSpanID(t *testing.T) {
	tests := []struct {
		id       string
		expected bool
	}{
		{"0123456789abcdef", true},
		{"0123456789ABCDEF", true},
		{"0123456789abc", false},      // Too short
		{"0123456789abcdef00", false}, // Too long
		{"0123456789abcdeg", false},   // Invalid char
		{"", false},
	}

	for _, tt := range tests {
		t.Run(tt.id, func(t *testing.T) {
			if got := IsValidSpanID(tt.id); got != tt.expected {
				t.Errorf("IsValidSpanID(%q) = %v, want %v", tt.id, got, tt.expected)
			}
		})
	}
}

func TestParseTraceID(t *testing.T) {
	id, err := ParseTraceID("0123456789abcdef0123456789abcdef")
	if err != nil {
		t.Errorf("ParseTraceID() error = %v", err)
	}
	if !id.IsValid() {
		t.Error("Parsed TraceID should be valid")
	}

	_, err = ParseTraceID("invalid")
	if err == nil {
		t.Error("ParseTraceID() should return error for invalid ID")
	}
}

func TestParseSpanID(t *testing.T) {
	id, err := ParseSpanID("0123456789abcdef")
	if err != nil {
		t.Errorf("ParseSpanID() error = %v", err)
	}
	if !id.IsValid() {
		t.Error("Parsed SpanID should be valid")
	}

	_, err = ParseSpanID("invalid")
	if err == nil {
		t.Error("ParseSpanID() should return error for invalid ID")
	}
}

// mockSpan is a mock implementation of trace.Span for testing
type mockSpan struct {
	spanContext trace.SpanContext
}

func (m *mockSpan) SpanContext() trace.SpanContext          { return m.spanContext }
func (m *mockSpan) IsRecording() bool                       { return true }
func (m *mockSpan) End(...trace.SpanEndOption)              {}
func (m *mockSpan) SetError(bool)                           {}
func (m *mockSpan) RecordError(error, ...trace.EventOption) {}
func (m *mockSpan) AddEvent(string, ...trace.EventOption)   {}
func (m *mockSpan) AddLink(trace.Link)                      {}
func (m *mockSpan) SetStatus(codes.Code, string)            {}
func (m *mockSpan) SetName(string)                          {}
func (m *mockSpan) SetAttributes(...attribute.KeyValue)     {}
func (m *mockSpan) TracerProvider() trace.TracerProvider    { return nil }
func (m *mockSpan) span(trace.Span)                         {}

// testError is a simple error type for testing
type testError struct {
	msg string
}

func (e *testError) Error() string { return e.msg }

func BenchmarkOTelLogger_Info(b *testing.B) {
	config := OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: &bytes.Buffer{},
		},
	}
	logger := NewOTelLogger(config)
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			logger.Info("benchmark message", String("key", "value"))
		}
	})
}

func BenchmarkTraceLogger_Log(b *testing.B) {
	logger := NopLogger()
	tLogger := NewTraceLogger(logger, nil)
	ctx := context.Background()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			tLogger.Log(ctx, LevelInfo, "benchmark message")
		}
	})
}

func BenchmarkLogCorrelator_Add(b *testing.B) {
	lc := NewLogCorrelator(10000)
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			record := &CorrelatedLogRecord{
				LogRecord: &LogRecord{
					TraceID: traceID,
					Body:    "message",
				},
			}
			lc.Add(record)
		}
	})
}

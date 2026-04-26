package logs

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

func TestLogRecord_Struct(t *testing.T) {
	record := LogRecord{
		Timestamp:         time.Now(),
		ObservedTimestamp: time.Now(),
		SeverityNumber:    SeverityInfo,
		SeverityText:      "INFO",
		Body:              "test message",
		Attributes:        []attribute.KeyValue{attribute.String("key", "value")},
		EventName:         "test.event",
	}

	if record.SeverityNumber != SeverityInfo {
		t.Errorf("SeverityNumber = %v, want SeverityInfo", record.SeverityNumber)
	}
	if record.SeverityText != "INFO" {
		t.Errorf("SeverityText = %v, want INFO", record.SeverityText)
	}
	if record.Body != "test message" {
		t.Errorf("Body = %v, want 'test message'", record.Body)
	}
	if record.EventName != "test.event" {
		t.Errorf("EventName = %v, want 'test.event'", record.EventName)
	}
	if len(record.Attributes) != 1 {
		t.Errorf("Attributes len = %d, want 1", len(record.Attributes))
	}
}

func TestLogRecord_BodyTypes(t *testing.T) {
	tests := []struct {
		name string
		body interface{}
	}{
		{"string", "test"},
		{"int", 42},
		{"bool", true},
		{"map", map[string]interface{}{"a": 1}},
		{"array", []interface{}{1, 2, 3}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			record := LogRecord{Body: tt.body}
			if record.Body == nil {
				t.Error("Body should not be nil")
			}
		})
	}
}

func TestLogRecord_TraceContext(t *testing.T) {
	traceID, _ := trace.TraceIDFromHex("0123456789abcdef0123456789abcdef")
	spanID, _ := trace.SpanIDFromHex("0123456789abcdef")

	record := LogRecord{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: trace.FlagsSampled,
	}

	if !record.TraceID.IsValid() {
		t.Error("TraceID should be valid")
	}
	if !record.SpanID.IsValid() {
		t.Error("SpanID should be valid")
	}
	if !record.TraceFlags.IsSampled() {
		t.Error("TraceFlags should be sampled")
	}
}

func TestLoggerProvider_Interface(t *testing.T) {
	lp := NewLoggerProvider()
	var _ LoggerProvider = lp

	logger := lp.Logger("test")
	if logger == nil {
		t.Fatal("Logger() returned nil")
	}
}

func TestLogger_Interface(t *testing.T) {
	lp := NewLoggerProvider()
	logger := lp.Logger("test")
	var _ Logger = logger

	ctx := context.Background()
	if !logger.Enabled(ctx, SeverityInfo) {
		t.Error("Enabled should return true for INFO")
	}

	record := LogRecord{
		Timestamp:      time.Now(),
		SeverityNumber: SeverityInfo,
		Body:           "test",
		EventName:      "test.event",
	}
	logger.Emit(record)
}

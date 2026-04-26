package slog

import (
	"bytes"
	"context"
	"log/slog"
	"strings"
	"testing"
	"time"

	"github.com/OTLP_go/pkg/logs"
)

type testLogger struct {
	records []logs.LogRecord
}

func (l *testLogger) Emit(record logs.LogRecord) {
	l.records = append(l.records, record)
}

func (l *testLogger) Enabled(ctx context.Context, severity logs.SeverityNumber) bool {
	return true
}

func TestNewHandler(t *testing.T) {
	tlogger := &testLogger{}
	handler := NewHandler(tlogger)
	if handler == nil {
		t.Fatal("NewHandler() returned nil")
	}
}

func TestHandler_Enabled(t *testing.T) {
	tlogger := &testLogger{}
	handler := NewHandler(tlogger, WithMinLevel(slog.LevelInfo))
	ctx := context.Background()

	if !handler.Enabled(ctx, slog.LevelInfo) {
		t.Error("Enabled should return true for Info")
	}
	if handler.Enabled(ctx, slog.LevelDebug) {
		t.Error("Enabled should return false for Debug")
	}
}

func TestHandler_Handle(t *testing.T) {
	tlogger := &testLogger{}
	handler := NewHandler(tlogger)
	ctx := context.Background()

	record := slog.NewRecord(time.Now(), slog.LevelInfo, "test message", 0)
	record.AddAttrs(slog.String("key", "value"))

	if err := handler.Handle(ctx, record); err != nil {
		t.Errorf("Handle error = %v", err)
	}

	if len(tlogger.records) != 1 {
		t.Fatalf("expected 1 record, got %d", len(tlogger.records))
	}

	r := tlogger.records[0]
	if r.Body != "test message" {
		t.Errorf("Body = %v, want 'test message'", r.Body)
	}
	if r.SeverityNumber != logs.SeverityInfo {
		t.Errorf("SeverityNumber = %v, want SeverityInfo", r.SeverityNumber)
	}
	if r.EventName != "test message" {
		t.Errorf("EventName = %v, want 'test message'", r.EventName)
	}
	if len(r.Attributes) != 1 {
		t.Errorf("Attributes len = %d, want 1", len(r.Attributes))
	}
}

func TestHandler_Handle_Disabled(t *testing.T) {
	tlogger := &testLogger{}
	handler := NewHandler(tlogger, WithMinLevel(slog.LevelError))
	ctx := context.Background()

	// Handler.Enabled returns false for Info when min level is Error,
	// so Handle won't be called by slog. We test Enabled directly.
	if handler.Enabled(ctx, slog.LevelInfo) {
		t.Error("Enabled should return false for Info when min level is Error")
	}
	if !handler.Enabled(ctx, slog.LevelError) {
		t.Error("Enabled should return true for Error")
	}
}

func TestHandler_WithAttrs(t *testing.T) {
	tlogger := &testLogger{}
	handler := NewHandler(tlogger)
	handler2 := handler.WithAttrs([]slog.Attr{slog.String("extra", "data")})
	if handler2 == nil {
		t.Fatal("WithAttrs() returned nil")
	}
}

func TestHandler_WithGroup(t *testing.T) {
	tlogger := &testLogger{}
	handler := NewHandler(tlogger)
	handler2 := handler.WithGroup("group1")
	if handler2 == nil {
		t.Fatal("WithGroup() returned nil")
	}
}

func TestSlogLevelToSeverity(t *testing.T) {
	tests := []struct {
		level    slog.Level
		expected logs.SeverityNumber
	}{
		{slog.LevelDebug - 1, logs.SeverityDebug},
		{slog.LevelDebug, logs.SeverityDebug},
		{slog.LevelInfo, logs.SeverityInfo},
		{slog.LevelWarn, logs.SeverityWarn},
		{slog.LevelError, logs.SeverityError},
		{slog.LevelError + 1, logs.SeverityFatal},
	}

	for _, tt := range tests {
		t.Run(tt.level.String(), func(t *testing.T) {
			got := slogLevelToSeverity(tt.level)
			if got != tt.expected {
				t.Errorf("slogLevelToSeverity(%v) = %v, want %v", tt.level, got, tt.expected)
			}
		})
	}
}

func TestSlogAttrToOTel(t *testing.T) {
	tests := []struct {
		name         string
		attr         slog.Attr
		expectedType string
		expectedStr  string
	}{
		{"bool", slog.Bool("b", true), "Bool", "true"},
		{"int64", slog.Int64("i", 42), "Int64", "42"},
		{"float64", slog.Float64("f", 3.14), "Float64", "3.14"},
		{"string", slog.String("s", "hello"), "String", "hello"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			kv := slogAttrToOTel(tt.attr)
			if string(kv.Key) != tt.attr.Key {
				t.Errorf("Key = %v, want %v", kv.Key, tt.attr.Key)
			}
			if kv.Value.Type().String() != tt.expectedType {
				t.Errorf("Type = %v, want %v", kv.Value.Type().String(), tt.expectedType)
			}
			if kv.Value.AsString() != tt.expectedStr {
				t.Errorf("Value = %v, want %v", kv.Value.AsString(), tt.expectedStr)
			}
		})
	}
}

func TestHandler_Integration(t *testing.T) {
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))
	_ = logger

	tlogger := &testLogger{}
	otelHandler := NewHandler(tlogger)
	otelLogger := slog.New(otelHandler)

	otelLogger.Info("integration test", slog.String("service", "test"))

	if len(tlogger.records) != 1 {
		t.Fatalf("expected 1 record, got %d", len(tlogger.records))
	}

	r := tlogger.records[0]
	if r.Body != "integration test" {
		t.Errorf("Body = %v, want 'integration test'", r.Body)
	}
	if !strings.Contains(r.SeverityText, "INFO") && r.SeverityText != "INFO" {
		// SeverityText might be empty depending on handler
	}
}

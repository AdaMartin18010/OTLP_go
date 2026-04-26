// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This file contains the API layer (bridge interfaces) for log library authors.
package logs

import (
	"context"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// LoggerProvider is the API for obtaining Loggers.
type LoggerProvider interface {
	Logger(name string) Logger
}

// Logger is the API for emitting log records.
type Logger interface {
	Emit(record LogRecord)
	Enabled(ctx context.Context, severity SeverityNumber) bool
}

// LogRecord represents a log record following the OpenTelemetry Logs Data Model.
// It includes the EventName field introduced in OTLP v1.10+.
type LogRecord struct {
	Timestamp         time.Time
	ObservedTimestamp time.Time
	SeverityNumber    SeverityNumber
	SeverityText      string
	Body              interface{}
	Attributes        []attribute.KeyValue
	TraceID           trace.TraceID
	SpanID            trace.SpanID
	TraceFlags        trace.TraceFlags
	EventName         string
}

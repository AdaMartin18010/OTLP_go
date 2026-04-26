// Package slog provides a bridge between Go's standard log/slog and OpenTelemetry logs.
package slog

import (
	"context"
	"fmt"
	"log/slog"
	"time"

	"github.com/OTLP_go/pkg/logs"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// Handler implements slog.Handler, converting slog records to OTel LogRecords.
type Handler struct {
	logger   logs.Logger
	attrs    []slog.Attr
	groups   []string
	minLevel slog.Level
}

// HandlerOption configures the Handler.
type HandlerOption func(*Handler)

// WithMinLevel sets the minimum log level.
func WithMinLevel(level slog.Level) HandlerOption {
	return func(h *Handler) {
		h.minLevel = level
	}
}

// NewHandler creates a new OTel slog.Handler.
func NewHandler(logger logs.Logger, opts ...HandlerOption) *Handler {
	h := &Handler{
		logger:   logger,
		minLevel: slog.LevelDebug,
	}
	for _, opt := range opts {
		opt(h)
	}
	return h
}

// Enabled reports whether the handler handles records at the given level.
func (h *Handler) Enabled(ctx context.Context, level slog.Level) bool {
	return level >= h.minLevel
}

// Handle converts a slog.Record to an OTel LogRecord and emits it.
func (h *Handler) Handle(ctx context.Context, record slog.Record) error {
	severity := slogLevelToSeverity(record.Level)
	if !h.logger.Enabled(ctx, severity) {
		return nil
	}

	var attrs []attribute.KeyValue
	record.Attrs(func(attr slog.Attr) bool {
		attrs = append(attrs, slogAttrToOTel(attr))
		return true
	})

	logRecord := logs.LogRecord{
		Timestamp:         record.Time,
		ObservedTimestamp: time.Now(),
		SeverityNumber:    severity,
		SeverityText:      severity.String(),
		Body:              record.Message,
		Attributes:        attrs,
		EventName:         record.Message,
	}

	if span := trace.SpanFromContext(ctx); span != nil {
		spanCtx := span.SpanContext()
		logRecord.TraceID = spanCtx.TraceID()
		logRecord.SpanID = spanCtx.SpanID()
		logRecord.TraceFlags = spanCtx.TraceFlags()
	}

	h.logger.Emit(logRecord)
	return nil
}

// WithAttrs returns a new Handler with the given attributes.
func (h *Handler) WithAttrs(attrs []slog.Attr) slog.Handler {
	newHandler := &Handler{
		logger:   h.logger,
		attrs:    append(h.attrs, attrs...),
		groups:   append([]string(nil), h.groups...),
		minLevel: h.minLevel,
	}
	return newHandler
}

// WithGroup returns a new Handler with the given group name.
func (h *Handler) WithGroup(name string) slog.Handler {
	newHandler := &Handler{
		logger:   h.logger,
		attrs:    append([]slog.Attr(nil), h.attrs...),
		groups:   append(append([]string(nil), h.groups...), name),
		minLevel: h.minLevel,
	}
	return newHandler
}

func slogLevelToSeverity(level slog.Level) logs.SeverityNumber {
	switch {
	case level <= slog.LevelDebug:
		return logs.SeverityDebug
	case level <= slog.LevelInfo:
		return logs.SeverityInfo
	case level <= slog.LevelWarn:
		return logs.SeverityWarn
	case level <= slog.LevelError:
		return logs.SeverityError
	default:
		return logs.SeverityFatal
	}
}

func slogAttrToOTel(attr slog.Attr) attribute.KeyValue {
	switch attr.Value.Kind() {
	case slog.KindBool:
		return attribute.Bool(attr.Key, attr.Value.Bool())
	case slog.KindInt64:
		return attribute.Int64(attr.Key, attr.Value.Int64())
	case slog.KindFloat64:
		return attribute.Float64(attr.Key, attr.Value.Float64())
	case slog.KindString:
		return attribute.String(attr.Key, attr.Value.String())
	case slog.KindDuration:
		return attribute.String(attr.Key, attr.Value.Duration().String())
	case slog.KindTime:
		return attribute.String(attr.Key, attr.Value.Time().Format(time.RFC3339Nano))
	case slog.KindAny:
		return attribute.String(attr.Key, fmt.Sprintf("%v", attr.Value.Any()))
	default:
		return attribute.String(attr.Key, attr.Value.String())
	}
}

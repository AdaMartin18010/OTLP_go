//go:build ignore

package logrus

import (
	"context"
	"fmt"
	"time"

	"github.com/OTLP_go/pkg/logs"
	"github.com/sirupsen/logrus"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// Hook implements logrus.Hook for OTel logs.
type Hook struct {
	logger logs.Logger
	levels []logrus.Level
}

// NewHook creates a new logrus hook that emits to the given OTel logger.
func NewHook(logger logs.Logger, levels ...logrus.Level) *Hook {
	if len(levels) == 0 {
		levels = logrus.AllLevels
	}
	return &Hook{
		logger: logger,
		levels: levels,
	}
}

// Levels returns the log levels that this hook handles.
func (h *Hook) Levels() []logrus.Level {
	return h.levels
}

// Fire converts a logrus entry to an OTel LogRecord and emits it.
func (h *Hook) Fire(entry *logrus.Entry) error {
	severity := logrusLevelToSeverity(entry.Level)

	var attrs []attribute.KeyValue
	for k, v := range entry.Data {
		attrs = append(attrs, attribute.String(k, formatValue(v)))
	}

	record := logs.LogRecord{
		Timestamp:         entry.Time,
		ObservedTimestamp: time.Now(),
		SeverityNumber:    severity,
		SeverityText:      severity.String(),
		Body:              entry.Message,
		Attributes:        attrs,
		EventName:         entry.Message,
	}

	if entry.Context != nil {
		if span := trace.SpanFromContext(entry.Context); span != nil {
			spanCtx := span.SpanContext()
			record.TraceID = spanCtx.TraceID()
			record.SpanID = spanCtx.SpanID()
			record.TraceFlags = spanCtx.TraceFlags()
		}
	}

	h.logger.Emit(record)
	return nil
}

func logrusLevelToSeverity(level logrus.Level) logs.SeverityNumber {
	switch level {
	case logrus.TraceLevel:
		return logs.SeverityTrace
	case logrus.DebugLevel:
		return logs.SeverityDebug
	case logrus.InfoLevel:
		return logs.SeverityInfo
	case logrus.WarnLevel:
		return logs.SeverityWarn
	case logrus.ErrorLevel:
		return logs.SeverityError
	case logrus.FatalLevel, logrus.PanicLevel:
		return logs.SeverityFatal
	default:
		return logs.SeverityInfo
	}
}

func formatValue(v interface{}) string {
	if s, ok := v.(string); ok {
		return s
	}
	if err, ok := v.(error); ok {
		return err.Error()
	}
	return fmt.Sprintf("%v", v)
}

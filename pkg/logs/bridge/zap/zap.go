// Package zap provides a bridge between zap and OpenTelemetry logs.
package zap

import (
	"math"
	"time"

	"github.com/OTLP_go/pkg/logs"
	"go.opentelemetry.io/otel/attribute"
	"go.uber.org/zap/zapcore"
)

// Core implements zapcore.Core for OTel logs.
type Core struct {
	enc    zapcore.Encoder
	out    zapcore.WriteSyncer
	level  zapcore.LevelEnabler
	logger logs.Logger
	fields []zapcore.Field
}

// NewCore creates a new zap Core that emits to the given OTel logger.
func NewCore(logger logs.Logger, enc zapcore.Encoder, out zapcore.WriteSyncer, level zapcore.LevelEnabler) *Core {
	return &Core{
		enc:    enc,
		out:    out,
		level:  level,
		logger: logger,
	}
}

// Enabled reports whether the given level is enabled.
func (c *Core) Enabled(level zapcore.Level) bool {
	return c.level.Enabled(level)
}

// With adds fields to the logging context.
func (c *Core) With(fields []zapcore.Field) zapcore.Core {
	return &Core{
		enc:    c.enc.Clone(),
		out:    c.out,
		level:  c.level,
		logger: c.logger,
		fields: append(append([]zapcore.Field(nil), c.fields...), fields...),
	}
}

// Check determines whether the supplied entry should be logged.
func (c *Core) Check(ent zapcore.Entry, ce *zapcore.CheckedEntry) *zapcore.CheckedEntry {
	if c.Enabled(ent.Level) {
		return ce.AddCore(ent, c)
	}
	return ce
}

// Write converts a zap entry to an OTel LogRecord and emits it.
func (c *Core) Write(ent zapcore.Entry, fields []zapcore.Field) error {
	severity := zapLevelToSeverity(ent.Level)

	var attrs []attribute.KeyValue
	for _, f := range c.fields {
		attrs = append(attrs, zapFieldToOTel(f))
	}
	for _, f := range fields {
		attrs = append(attrs, zapFieldToOTel(f))
	}

	record := logs.LogRecord{
		Timestamp:         ent.Time,
		ObservedTimestamp: time.Now(),
		SeverityNumber:    severity,
		SeverityText:      severity.String(),
		Body:              ent.Message,
		Attributes:        attrs,
		EventName:         ent.Message,
	}

	c.logger.Emit(record)
	return nil
}

// Sync flushes the output.
func (c *Core) Sync() error {
	return c.out.Sync()
}

func zapLevelToSeverity(level zapcore.Level) logs.SeverityNumber {
	switch {
	case level < zapcore.InfoLevel:
		return logs.SeverityDebug
	case level == zapcore.InfoLevel:
		return logs.SeverityInfo
	case level == zapcore.WarnLevel:
		return logs.SeverityWarn
	case level == zapcore.ErrorLevel:
		return logs.SeverityError
	case level >= zapcore.DPanicLevel:
		return logs.SeverityFatal
	default:
		return logs.SeverityInfo
	}
}

func zapFieldToOTel(field zapcore.Field) attribute.KeyValue {
	switch field.Type {
	case zapcore.BoolType:
		return attribute.Bool(field.Key, field.Integer == 1)
	case zapcore.Int8Type, zapcore.Int16Type, zapcore.Int32Type, zapcore.Int64Type:
		return attribute.Int64(field.Key, field.Integer)
	case zapcore.Uint8Type, zapcore.Uint16Type, zapcore.Uint32Type, zapcore.Uint64Type, zapcore.UintptrType:
		return attribute.Int64(field.Key, int64(field.Integer))
	case zapcore.Float64Type:
		return attribute.Float64(field.Key, math.Float64frombits(uint64(field.Integer)))
	case zapcore.Float32Type:
		return attribute.Float64(field.Key, float64(math.Float32frombits(uint32(field.Integer))))
	case zapcore.StringType:
		return attribute.String(field.Key, field.String)
	case zapcore.ErrorType:
		if err, ok := field.Interface.(error); ok {
			return attribute.String(field.Key, err.Error())
		}
		return attribute.String(field.Key, "unknown error")
	default:
		return attribute.String(field.Key, field.String)
	}
}

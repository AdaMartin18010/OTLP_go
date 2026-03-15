// Package logs provides OpenTelemetry Logs SDK implementation
// Based on OpenTelemetry Go SDK v1.42.0
package logs

import (
	"context"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
)

// SeverityNumber represents the severity level of a log record
type SeverityNumber int32

const (
	SeverityTrace  SeverityNumber = 1
	SeverityDebug  SeverityNumber = 5
	SeverityInfo   SeverityNumber = 9
	SeverityWarn   SeverityNumber = 13
	SeverityError  SeverityNumber = 17
	SeverityFatal  SeverityNumber = 21
)

// String returns the string representation of severity
func (s SeverityNumber) String() string {
	switch {
	case s >= 1 && s <= 4:
		return "TRACE"
	case s >= 5 && s <= 8:
		return "DEBUG"
	case s >= 9 && s <= 12:
		return "INFO"
	case s >= 13 && s <= 16:
		return "WARN"
	case s >= 17 && s <= 20:
		return "ERROR"
	case s >= 21:
		return "FATAL"
	default:
		return "UNSPECIFIED"
	}
}

// LogRecord represents a log record
type LogRecord struct {
	Timestamp         time.Time
	ObservedTimestamp time.Time
	Severity          SeverityNumber
	SeverityText      string
	Body              string
	Attributes        []attribute.KeyValue
	TraceID           string
	SpanID            string
	TraceFlags        byte
}

// LoggerProvider provides loggers
type LoggerProvider struct {
	processor LogProcessor
	resource  *resource.Resource
	loggers   map[string]*Logger
	mu        sync.RWMutex
	stopped   bool
}

// LogProcessor processes log records
type LogProcessor interface {
	OnEmit(ctx context.Context, record *LogRecord) error
	ForceFlush(ctx context.Context) error
	Shutdown(ctx context.Context) error
}

// LogExporter exports log records
type LogExporter interface {
	Export(ctx context.Context, records []*LogRecord) error
	ForceFlush(ctx context.Context) error
	Shutdown(ctx context.Context) error
}

// LoggerConfig configures a logger provider
type LoggerConfig struct {
	Endpoint       string
	ServiceName    string
	ServiceVersion string
	Environment    string
}

// DefaultLoggerConfig returns default logger config
func DefaultLoggerConfig() *LoggerConfig {
	return &LoggerConfig{
		Endpoint:       "localhost:4317",
		ServiceName:    "otlp-go-service",
		ServiceVersion: "1.0.0",
		Environment:    "development",
	}
}

// NewLoggerProvider creates a new LoggerProvider
func NewLoggerProvider(cfg *LoggerConfig, processor LogProcessor, res *resource.Resource) *LoggerProvider {
	if cfg == nil {
		cfg = DefaultLoggerConfig()
	}

	return &LoggerProvider{
		processor: processor,
		resource:  res,
		loggers:   make(map[string]*Logger),
	}
}

// GetLogger returns a logger with the given name
func (p *LoggerProvider) GetLogger(name string) *Logger {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.stopped {
		return nil
	}

	if logger, exists := p.loggers[name]; exists {
		return logger
	}

	logger := &Logger{
		name:     name,
		provider: p,
	}
	p.loggers[name] = logger
	return logger
}

// Shutdown shuts down the provider
func (p *LoggerProvider) Shutdown(ctx context.Context) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.stopped {
		return nil
	}

	p.stopped = true
	return p.processor.Shutdown(ctx)
}

// ForceFlush forces flush
func (p *LoggerProvider) ForceFlush(ctx context.Context) error {
	return p.processor.ForceFlush(ctx)
}

// Logger logs messages
type Logger struct {
	name       string
	provider   *LoggerProvider
	attributes []attribute.KeyValue
}

// Emit emits a log record
func (l *Logger) Emit(ctx context.Context, severity SeverityNumber, body string, attrs ...attribute.KeyValue) {
	if l.provider.stopped {
		return
	}

	now := time.Now()
	allAttrs := make([]attribute.KeyValue, 0, len(l.attributes)+len(attrs))
	allAttrs = append(allAttrs, l.attributes...)
	allAttrs = append(allAttrs, attrs...)

	record := &LogRecord{
		Timestamp:         now,
		ObservedTimestamp: now,
		Severity:          severity,
		SeverityText:      severity.String(),
		Body:              body,
		Attributes:        allAttrs,
	}

	l.provider.processor.OnEmit(ctx, record)
}

// Debug logs debug message
func (l *Logger) Debug(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityDebug, message, attrs...)
}

// Info logs info message
func (l *Logger) Info(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityInfo, message, attrs...)
}

// Warn logs warn message
func (l *Logger) Warn(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityWarn, message, attrs...)
}

// Error logs error message
func (l *Logger) Error(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityError, message, attrs...)
}

// Fatal logs fatal message
func (l *Logger) Fatal(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityFatal, message, attrs...)
}

// WithAttributes returns a logger with additional attributes
func (l *Logger) WithAttributes(attrs ...attribute.KeyValue) *Logger {
	newAttrs := make([]attribute.KeyValue, 0, len(l.attributes)+len(attrs))
	newAttrs = append(newAttrs, l.attributes...)
	newAttrs = append(newAttrs, attrs...)

	return &Logger{
		name:       l.name,
		provider:   l.provider,
		attributes: newAttrs,
	}
}

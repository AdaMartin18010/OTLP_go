// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This package implements:
//   - LoggerProvider for managing loggers
//   - BatchProcessor for efficient log export
//   - ConsoleExporter for development
//   - Severity levels (TRACE to FATAL)
package logs

import (
	"context"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

// SeverityNumber represents log severity levels.
type SeverityNumber int

const (
	SeverityTrace SeverityNumber = 1
	SeverityDebug SeverityNumber = 5
	SeverityInfo  SeverityNumber = 9
	SeverityWarn  SeverityNumber = 13
	SeverityError SeverityNumber = 17
	SeverityFatal SeverityNumber = 21
)

// String returns the string representation of severity.
func (s SeverityNumber) String() string {
	switch s {
	case SeverityTrace:
		return "TRACE"
	case SeverityDebug:
		return "DEBUG"
	case SeverityInfo:
		return "INFO"
	case SeverityWarn:
		return "WARN"
	case SeverityError:
		return "ERROR"
	case SeverityFatal:
		return "FATAL"
	default:
		return "UNKNOWN"
	}
}

// LogRecord represents a log record.
type LogRecord struct {
	Timestamp  time.Time
	Severity   SeverityNumber
	Body       string
	Attributes []attribute.KeyValue
}

// LogProcessor processes log records.
type LogProcessor interface {
	OnLog(log *LogRecord)
	Shutdown(ctx context.Context) error
	ForceFlush(ctx context.Context) error
}

// LogExporter exports log records.
type LogExporter interface {
	Export(ctx context.Context, logs []*LogRecord) error
	Shutdown(ctx context.Context) error
}

// LoggerProvider provides loggers.
type LoggerProvider struct {
	loggers    map[string]*Logger
	processors []LogProcessor
	resource   interface{}
	mu         sync.RWMutex
	stopped    bool
}

// NewLoggerProvider creates a new LoggerProvider.
func NewLoggerProvider(resource interface{}, processors ...LogProcessor) *LoggerProvider {
	return &LoggerProvider{
		loggers:    make(map[string]*Logger),
		processors: processors,
		resource:   resource,
	}
}

// GetLogger gets or creates a logger.
func (p *LoggerProvider) GetLogger(name string) *Logger {
	p.mu.Lock()
	defer p.mu.Unlock()

	if logger, ok := p.loggers[name]; ok {
		return logger
	}

	logger := &Logger{
		provider: p,
		name:     name,
	}
	p.loggers[name] = logger
	return logger
}

// Shutdown shuts down the provider.
func (p *LoggerProvider) Shutdown(ctx context.Context) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.stopped {
		return nil
	}

	p.stopped = true
	var errs []error
	for _, processor := range p.processors {
		if err := processor.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	if len(errs) > 0 {
		return errs[0]
	}
	return nil
}

// Logger is a logger instance.
type Logger struct {
	provider   *LoggerProvider
	name       string
	version    string
	attributes []attribute.KeyValue
}

// Emit emits a log record.
func (l *Logger) Emit(ctx context.Context, severity SeverityNumber, body string, attrs ...attribute.KeyValue) {
	record := &LogRecord{
		Timestamp:  time.Now(),
		Severity:   severity,
		Body:       body,
		Attributes: append(l.attributes, attrs...),
	}

	l.provider.mu.RLock()
	processors := l.provider.processors
	l.provider.mu.RUnlock()

	for _, processor := range processors {
		processor.OnLog(record)
	}
}

// Debug logs a debug message.
func (l *Logger) Debug(ctx context.Context, body string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityDebug, body, attrs...)
}

// Info logs an info message.
func (l *Logger) Info(ctx context.Context, body string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityInfo, body, attrs...)
}

// Warn logs a warning message.
func (l *Logger) Warn(ctx context.Context, body string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityWarn, body, attrs...)
}

// Error logs an error message.
func (l *Logger) Error(ctx context.Context, body string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityError, body, attrs...)
}

// Fatal logs a fatal message.
func (l *Logger) Fatal(ctx context.Context, body string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityFatal, body, attrs...)
}

// Trace logs a trace message.
func (l *Logger) Trace(ctx context.Context, body string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityTrace, body, attrs...)
}

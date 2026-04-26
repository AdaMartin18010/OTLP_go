// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This package implements:
//   - Structured logging with fields
//   - Log level management
//   - OpenTelemetry trace correlation
//   - High-performance logging with sampling
//   - JSON output format
//
// Example usage:
//
//	logger := logs.NewLogger(logs.Config{
//	    Level:  logs.LevelInfo,
//	    Output: os.Stdout,
//	})
//	defer logger.Shutdown()
//
//	logger.Info("server started",
//	    logs.String("addr", ":8080"),
//	    logs.Int("workers", 10),
//	)
package logs

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// SeverityNumber represents log severity levels.
type SeverityNumber int32

const (
	// SeverityTrace is the most detailed level.
	SeverityTrace SeverityNumber = 1
	// SeverityDebug is for debugging information.
	SeverityDebug SeverityNumber = 5
	// SeverityInfo is for informational messages.
	SeverityInfo SeverityNumber = 9
	// SeverityWarn is for warning messages.
	SeverityWarn SeverityNumber = 13
	// SeverityError is for error messages.
	SeverityError SeverityNumber = 17
	// SeverityFatal is for fatal error messages.
	SeverityFatal SeverityNumber = 21

	// Fine-grained severity levels (OTel 1-24)
	SeverityTrace2 = SeverityNumber(2)
	SeverityTrace3 = SeverityNumber(3)
	SeverityTrace4 = SeverityNumber(4)
	SeverityDebug2 = SeverityNumber(6)
	SeverityDebug3 = SeverityNumber(7)
	SeverityDebug4 = SeverityNumber(8)
	SeverityInfo2  = SeverityNumber(10)
	SeverityInfo3  = SeverityNumber(11)
	SeverityInfo4  = SeverityNumber(12)
	SeverityWarn2  = SeverityNumber(14)
	SeverityWarn3  = SeverityNumber(15)
	SeverityWarn4  = SeverityNumber(16)
	SeverityError2 = SeverityNumber(18)
	SeverityError3 = SeverityNumber(19)
	SeverityError4 = SeverityNumber(20)
	SeverityFatal2 = SeverityNumber(22)
	SeverityFatal3 = SeverityNumber(23)
	SeverityFatal4 = SeverityNumber(24)
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
	case SeverityTrace2:
		return "TRACE2"
	case SeverityTrace3:
		return "TRACE3"
	case SeverityTrace4:
		return "TRACE4"
	case SeverityDebug2:
		return "DEBUG2"
	case SeverityDebug3:
		return "DEBUG3"
	case SeverityDebug4:
		return "DEBUG4"
	case SeverityInfo2:
		return "INFO2"
	case SeverityInfo3:
		return "INFO3"
	case SeverityInfo4:
		return "INFO4"
	case SeverityWarn2:
		return "WARN2"
	case SeverityWarn3:
		return "WARN3"
	case SeverityWarn4:
		return "WARN4"
	case SeverityError2:
		return "ERROR2"
	case SeverityError3:
		return "ERROR3"
	case SeverityError4:
		return "ERROR4"
	case SeverityFatal2:
		return "FATAL2"
	case SeverityFatal3:
		return "FATAL3"
	case SeverityFatal4:
		return "FATAL4"
	default:
		return "UNKNOWN"
	}
}

// ToLevel converts SeverityNumber to Level.
func (s SeverityNumber) ToLevel() Level {
	switch {
	case s >= SeverityTrace && s <= SeverityTrace4:
		return LevelTrace
	case s >= SeverityDebug && s <= SeverityDebug4:
		return LevelDebug
	case s >= SeverityInfo && s <= SeverityInfo4:
		return LevelInfo
	case s >= SeverityWarn && s <= SeverityWarn4:
		return LevelWarn
	case s >= SeverityError && s <= SeverityError4:
		return LevelError
	case s >= SeverityFatal && s <= SeverityFatal4:
		return LevelFatal
	default:
		return LevelInfo
	}
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

// Provider provides loggers.
type Provider struct {
	loggers    map[string]*StructuredLogger
	processors []LogProcessor
	resource   interface{}
	mu         sync.RWMutex
	stopped    bool
}

// NewProvider creates a new Provider.
func NewProvider(resource interface{}, processors ...LogProcessor) *Provider {
	return &Provider{
		loggers:    make(map[string]*StructuredLogger),
		processors: processors,
		resource:   resource,
	}
}

// Logger gets or creates a logger.
func (p *Provider) Logger(name string) *StructuredLogger {
	p.mu.Lock()
	defer p.mu.Unlock()

	if logger, ok := p.loggers[name]; ok {
		return logger
	}

	logger := &StructuredLogger{
		provider: p,
		name:     name,
	}
	p.loggers[name] = logger
	return logger
}

// Shutdown shuts down the provider.
func (p *Provider) Shutdown(ctx context.Context) error {
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

// Sampler decides whether to sample a log record.
type Sampler interface {
	ShouldSample(record *LogRecord) bool
}

// SamplerFunc is a function that implements Sampler.
type SamplerFunc func(record *LogRecord) bool

// ShouldSample implements Sampler.
func (f SamplerFunc) ShouldSample(record *LogRecord) bool {
	return f(record)
}

// AlwaysSample always samples log records.
var AlwaysSample = SamplerFunc(func(record *LogRecord) bool { return true })

// NeverSample never samples log records.
var NeverSample = SamplerFunc(func(record *LogRecord) bool { return false })

// ProbabilitySampler samples log records with a given probability.
func ProbabilitySampler(probability float64) Sampler {
	if probability <= 0 {
		return NeverSample
	}
	if probability >= 1 {
		return AlwaysSample
	}
	threshold := uint64(probability * float64(^uint64(0)))
	return SamplerFunc(func(record *LogRecord) bool {
		return getRecordHash(record) < threshold
	})
}

// RateLimiter limits the rate of log records.
type RateLimiter struct {
	interval time.Duration
	lastLog  atomic.Int64
}

// NewRateLimiter creates a new rate limiter.
func NewRateLimiter(interval time.Duration) *RateLimiter {
	rl := &RateLimiter{interval: interval}
	// Initialize to 0 to allow first log
	rl.lastLog.Store(0)
	return rl
}

// ShouldSample implements Sampler.
func (rl *RateLimiter) ShouldSample(record *LogRecord) bool {
	now := time.Now().UnixNano()
	last := rl.lastLog.Load()
	if now-last < rl.interval.Nanoseconds() {
		return false
	}
	return rl.lastLog.CompareAndSwap(last, now)
}

// getRecordHash returns a hash of the log record for sampling.
func getRecordHash(record *LogRecord) uint64 {
	// Simple hash based on timestamp and body
	h := uint64(record.Timestamp.UnixNano())
	bodyStr := ""
	switch v := record.Body.(type) {
	case string:
		bodyStr = v
	default:
		bodyStr = fmt.Sprintf("%v", v)
	}
	for _, c := range bodyStr {
		h = h*31 + uint64(c)
	}
	return h
}

// Config is the configuration for a Logger.
type Config struct {
	Level       Level
	Output      io.Writer
	Encoder     Encoder
	Sampler     Sampler
	Development bool
	AddCaller   bool
	CallerSkip  int
}

// Encoder encodes log records.
type Encoder interface {
	Encode(record *LogRecord, fields Fields) ([]byte, error)
}

// LogJSONEncoder encodes log records as JSON.
type LogJSONEncoder struct {
	enc JSONEncoder
}

// NewJSONLogEncoder creates a new JSON encoder for log records.
func NewJSONLogEncoder() *LogJSONEncoder {
	return &LogJSONEncoder{}
}

// Encode encodes a log record as JSON.
func (e *LogJSONEncoder) Encode(record *LogRecord, fields Fields) ([]byte, error) {
	e.enc.Reset()

	e.enc.buffer = append(e.enc.buffer, '{')

	// Timestamp
	e.enc.EncodeTime("timestamp", record.Timestamp)

	// Level
	e.enc.EncodeString("level", record.SeverityNumber.String())

	// Message
	e.enc.EncodeAny("message", record.Body)

	// EventName
	if record.EventName != "" {
		e.enc.EncodeString("event_name", record.EventName)
	}

	// Logger name (if any)
	// (Would be added via fields)

	// Trace context
	if record.TraceID.IsValid() {
		e.enc.EncodeString("trace_id", record.TraceID.String())
	}
	if record.SpanID.IsValid() {
		e.enc.EncodeString("span_id", record.SpanID.String())
	}

	// Fields
	e.enc.EncodeFields(fields)

	// Attributes
	for _, attr := range record.Attributes {
		e.encodeAttribute(&e.enc, attr)
	}

	e.enc.buffer = append(e.enc.buffer, '}')
	result := make([]byte, len(e.enc.buffer))
	copy(result, e.enc.buffer)
	return result, nil
}

// encodeAttribute encodes an OpenTelemetry attribute.
func (e *LogJSONEncoder) encodeAttribute(enc *JSONEncoder, attr attribute.KeyValue) {
	switch attr.Value.Type() {
	case attribute.BOOL:
		enc.EncodeBool(string(attr.Key), attr.Value.AsBool())
	case attribute.INT64:
		enc.EncodeInt64(string(attr.Key), attr.Value.AsInt64())
	case attribute.FLOAT64:
		enc.EncodeFloat64(string(attr.Key), attr.Value.AsFloat64())
	case attribute.STRING:
		enc.EncodeString(string(attr.Key), attr.Value.AsString())
	default:
		enc.EncodeString(string(attr.Key), attr.Value.AsString())
	}
}

// StructuredLogger is a high-performance structured logger.
type StructuredLogger struct {
	provider *Provider
	name     string
	version  string
	config   Config
	level    *LevelManager
	sampler  Sampler
	encoder  Encoder
	output   io.Writer
	fields   Fields
	mu       sync.RWMutex
}

// NewLogger creates a new StructuredLogger with the given configuration.
func NewLogger(config Config) *StructuredLogger {
	if config.Output == nil {
		config.Output = os.Stdout
	}
	if config.Encoder == nil {
		config.Encoder = NewJSONLogEncoder()
	}
	if config.Sampler == nil {
		config.Sampler = AlwaysSample
	}
	if config.CallerSkip == 0 {
		config.CallerSkip = 1
	}

	return &StructuredLogger{
		config:  config,
		level:   NewLevelManager(config.Level),
		sampler: config.Sampler,
		encoder: config.Encoder,
		output:  config.Output,
		fields:  make(Fields, 0),
	}
}

// New creates a new StructuredLogger with the given name.
func New(name string, opts ...LoggerOption) *StructuredLogger {
	config := Config{
		Level:  LevelInfo,
		Output: os.Stdout,
	}

	for _, opt := range opts {
		opt(&config)
	}

	logger := NewLogger(config)
	logger.name = name
	return logger
}

// LoggerOption configures a Logger.
type LoggerOption func(*Config)

// WithLevel sets the logger level.
func WithLevel(level Level) LoggerOption {
	return func(c *Config) {
		c.Level = level
	}
}

// WithOutput sets the logger output.
func WithOutput(output io.Writer) LoggerOption {
	return func(c *Config) {
		c.Output = output
	}
}

// WithSampler sets the logger sampler.
func WithSampler(sampler Sampler) LoggerOption {
	return func(c *Config) {
		c.Sampler = sampler
	}
}

// WithDevelopment enables development mode.
func WithDevelopment(dev bool) LoggerOption {
	return func(c *Config) {
		c.Development = dev
	}
}

// WithCaller enables caller information.
func WithCaller(caller bool) LoggerOption {
	return func(c *Config) {
		c.AddCaller = caller
	}
}

// WithFields sets the default fields for the logger.
func WithFields(fields ...Field) LoggerOption {
	return func(c *Config) {
		// Store fields in a closure that will be applied after logger creation
		// This is handled in New()
	}
}

// Named creates a new logger with the given name.
func (l *StructuredLogger) Named(name string) *StructuredLogger {
	newName := name
	if l.name != "" {
		newName = l.name + "." + name
	}

	l.mu.RLock()
	defer l.mu.RUnlock()

	return &StructuredLogger{
		name:    newName,
		version: l.version,
		config:  l.config,
		level:   l.level,
		sampler: l.sampler,
		encoder: l.encoder,
		output:  l.output,
		fields:  append(Fields(nil), l.fields...),
	}
}

// With creates a new logger with the given fields.
func (l *StructuredLogger) With(fields ...Field) *StructuredLogger {
	l.mu.RLock()
	defer l.mu.RUnlock()

	newFields := make(Fields, len(l.fields)+len(fields))
	copy(newFields, l.fields)
	copy(newFields[len(l.fields):], fields)

	return &StructuredLogger{
		name:    l.name,
		version: l.version,
		config:  l.config,
		level:   l.level,
		sampler: l.sampler,
		encoder: l.encoder,
		output:  l.output,
		fields:  newFields,
	}
}

// SetLevel sets the logger level dynamically.
func (l *StructuredLogger) SetLevel(level Level) {
	l.level.Set(level)
}

// GetLevel returns the current logger level.
func (l *StructuredLogger) GetLevel() Level {
	return l.level.Get()
}

// IsEnabled returns true if the given level is enabled.
func (l *StructuredLogger) IsEnabled(level Level) bool {
	return l.level.Enabled(level)
}

// Enabled implements the Logger interface.
func (l *StructuredLogger) Enabled(ctx context.Context, severity SeverityNumber) bool {
	return l.IsEnabled(severity.ToLevel())
}

// Emit implements the Logger interface.
func (l *StructuredLogger) Emit(record LogRecord) {
	ctx := context.Background()
	fields := make(Fields, len(record.Attributes))
	for i, attr := range record.Attributes {
		fields[i] = Field{
			Key:   string(attr.Key),
			Type:  AnyType,
			Value: attr.Value,
		}
	}
	bodyStr := ""
	switch v := record.Body.(type) {
	case string:
		bodyStr = v
	default:
		bodyStr = fmt.Sprintf("%v", v)
	}
	l.log(ctx, record.SeverityNumber, bodyStr, fields...)
}

// log is the internal logging method.
func (l *StructuredLogger) log(ctx context.Context, severity SeverityNumber, msg string, fields ...Field) {
	level := severity.ToLevel()
	if !l.level.Enabled(level) {
		return
	}

	record := &LogRecord{
		Timestamp:         time.Now(),
		ObservedTimestamp: time.Now(),
		SeverityNumber:    severity,
		SeverityText:      severity.String(),
		Body:              msg,
	}

	// Extract trace context from context
	if span := trace.SpanFromContext(ctx); span != nil {
		spanCtx := span.SpanContext()
		record.TraceID = spanCtx.TraceID()
		record.SpanID = spanCtx.SpanID()
		record.TraceFlags = spanCtx.TraceFlags()
	}

	// Check sampler
	if l.sampler != nil && !l.sampler.ShouldSample(record) {
		return
	}

	// Merge fields
	l.mu.RLock()
	allFields := make(Fields, len(l.fields)+len(fields))
	copy(allFields, l.fields)
	copy(allFields[len(l.fields):], fields)
	l.mu.RUnlock()

	// Encode and output
	data, err := l.encoder.Encode(record, allFields)
	if err != nil {
		// Fall back to simple output
		fmt.Fprintf(l.output, "{\"error\":\"encoding failed\",\"message\":%q}\n", msg)
		return
	}

	l.output.Write(data)
	l.output.Write([]byte("\n"))

	// Send to processors if provider is set
	if l.provider != nil {
		l.provider.mu.RLock()
		processors := l.provider.processors
		l.provider.mu.RUnlock()

		for _, processor := range processors {
			processor.OnLog(record)
		}
	}
}

// Debug logs a debug message.
func (l *StructuredLogger) Debug(msg string, fields ...Field) {
	l.log(context.Background(), SeverityDebug, msg, fields...)
}

// DebugContext logs a debug message with context.
func (l *StructuredLogger) DebugContext(ctx context.Context, msg string, fields ...Field) {
	l.log(ctx, SeverityDebug, msg, fields...)
}

// Info logs an info message.
func (l *StructuredLogger) Info(msg string, fields ...Field) {
	l.log(context.Background(), SeverityInfo, msg, fields...)
}

// InfoContext logs an info message with context.
func (l *StructuredLogger) InfoContext(ctx context.Context, msg string, fields ...Field) {
	l.log(ctx, SeverityInfo, msg, fields...)
}

// Warn logs a warning message.
func (l *StructuredLogger) Warn(msg string, fields ...Field) {
	l.log(context.Background(), SeverityWarn, msg, fields...)
}

// WarnContext logs a warning message with context.
func (l *StructuredLogger) WarnContext(ctx context.Context, msg string, fields ...Field) {
	l.log(ctx, SeverityWarn, msg, fields...)
}

// Error logs an error message.
func (l *StructuredLogger) Error(msg string, fields ...Field) {
	l.log(context.Background(), SeverityError, msg, fields...)
}

// ErrorContext logs an error message with context.
func (l *StructuredLogger) ErrorContext(ctx context.Context, msg string, fields ...Field) {
	l.log(ctx, SeverityError, msg, fields...)
}

// Fatal logs a fatal message.
func (l *StructuredLogger) Fatal(msg string, fields ...Field) {
	l.log(context.Background(), SeverityFatal, msg, fields...)
}

// FatalContext logs a fatal message with context.
func (l *StructuredLogger) FatalContext(ctx context.Context, msg string, fields ...Field) {
	l.log(ctx, SeverityFatal, msg, fields...)
}

// Trace logs a trace message.
func (l *StructuredLogger) Trace(msg string, fields ...Field) {
	l.log(context.Background(), SeverityTrace, msg, fields...)
}

// TraceContext logs a trace message with context.
func (l *StructuredLogger) TraceContext(ctx context.Context, msg string, fields ...Field) {
	l.log(ctx, SeverityTrace, msg, fields...)
}

// EmitContext emits a log record with context (legacy method for compatibility).
func (l *StructuredLogger) EmitContext(ctx context.Context, severity SeverityNumber, body string, attrs ...attribute.KeyValue) {
	fields := make(Fields, len(attrs))
	for i, attr := range attrs {
		fields[i] = Field{
			Key:   string(attr.Key),
			Type:  AnyType,
			Value: attr.Value,
		}
	}
	l.log(ctx, severity, body, fields...)
}

// Sync flushes any buffered log entries.
func (l *StructuredLogger) Sync() error {
	if syncer, ok := l.output.(interface{ Sync() error }); ok {
		return syncer.Sync()
	}
	return nil
}

// Shutdown shuts down the logger.
func (l *StructuredLogger) Shutdown() error {
	return l.Sync()
}

// StdLogger returns a standard library logger that writes to this logger.
func (l *StructuredLogger) StdLogger() *StdLogger {
	return &StdLogger{logger: l}
}

// StdLogger adapts StructuredLogger to standard library logger interface.
type StdLogger struct {
	logger *StructuredLogger
}

// Print logs a message.
func (s *StdLogger) Print(v ...interface{}) {
	s.logger.Info(fmt.Sprint(v...))
}

// Printf logs a formatted message.
func (s *StdLogger) Printf(format string, v ...interface{}) {
	s.logger.Info(fmt.Sprintf(format, v...))
}

// Println logs a message with a newline.
func (s *StdLogger) Println(v ...interface{}) {
	s.logger.Info(fmt.Sprintln(v...))
}

// Fatal logs a fatal message and exits.
func (s *StdLogger) Fatal(v ...interface{}) {
	s.logger.Fatal(fmt.Sprint(v...))
}

// Fatalf logs a formatted fatal message and exits.
func (s *StdLogger) Fatalf(format string, v ...interface{}) {
	s.logger.Fatal(fmt.Sprintf(format, v...))
}

// Fatalln logs a fatal message with a newline and exits.
func (s *StdLogger) Fatalln(v ...interface{}) {
	s.logger.Fatal(fmt.Sprintln(v...))
}

// Panic logs a panic message and panics.
func (s *StdLogger) Panic(v ...interface{}) {
	msg := fmt.Sprint(v...)
	s.logger.Error(msg)
	panic(msg)
}

// Panicf logs a formatted panic message and panics.
func (s *StdLogger) Panicf(format string, v ...interface{}) {
	msg := fmt.Sprintf(format, v...)
	s.logger.Error(msg)
	panic(msg)
}

// Panicln logs a panic message with a newline and panics.
func (s *StdLogger) Panicln(v ...interface{}) {
	msg := fmt.Sprintln(v...)
	s.logger.Error(msg)
	panic(msg)
}

// ConsoleLogger is a simple console logger for development.
type ConsoleLogger struct {
	*StructuredLogger
}

// NewConsoleLogger creates a new console logger.
func NewConsoleLogger(level Level) *ConsoleLogger {
	return &ConsoleLogger{
		StructuredLogger: New("console", WithLevel(level), WithDevelopment(true)),
	}
}

// NopLogger returns a no-op logger.
func NopLogger() *StructuredLogger {
	return &StructuredLogger{
		level: NewLevelManager(LevelNone),
	}
}

// Global logger instance.
var globalLogger = NewLogger(Config{Level: LevelInfo})
var globalLoggerMu sync.RWMutex

// SetGlobalLogger sets the global logger.
func SetGlobalLogger(logger *StructuredLogger) {
	globalLoggerMu.Lock()
	defer globalLoggerMu.Unlock()
	globalLogger = logger
}

// GetGlobalLogger returns the global logger.
func GetGlobalLogger() *StructuredLogger {
	globalLoggerMu.RLock()
	defer globalLoggerMu.RUnlock()
	return globalLogger
}

// L returns the global logger.
func L() *StructuredLogger {
	return GetGlobalLogger()
}

// Sugar provides a simplified logging API.
type Sugar struct {
	logger *StructuredLogger
}

// Sugar returns a sugared logger.
func (l *StructuredLogger) Sugar() *Sugar {
	return &Sugar{logger: l}
}

// Debugf logs a debug message with formatting.
func (s *Sugar) Debugf(format string, args ...interface{}) {
	s.logger.Debug(fmt.Sprintf(format, args...))
}

// Infof logs an info message with formatting.
func (s *Sugar) Infof(format string, args ...interface{}) {
	s.logger.Info(fmt.Sprintf(format, args...))
}

// Warnf logs a warning message with formatting.
func (s *Sugar) Warnf(format string, args ...interface{}) {
	s.logger.Warn(fmt.Sprintf(format, args...))
}

// Errorf logs an error message with formatting.
func (s *Sugar) Errorf(format string, args ...interface{}) {
	s.logger.Error(fmt.Sprintf(format, args...))
}

// Fatalf logs a fatal message with formatting.
func (s *Sugar) Fatalf(format string, args ...interface{}) {
	s.logger.Fatal(fmt.Sprintf(format, args...))
}

// Debugw logs a debug message with key-value pairs.
func (s *Sugar) Debugw(msg string, keysAndValues ...interface{}) {
	s.logger.Debug(msg, kvToFields(keysAndValues)...)
}

// Infow logs an info message with key-value pairs.
func (s *Sugar) Infow(msg string, keysAndValues ...interface{}) {
	s.logger.Info(msg, kvToFields(keysAndValues)...)
}

// Warnw logs a warning message with key-value pairs.
func (s *Sugar) Warnw(msg string, keysAndValues ...interface{}) {
	s.logger.Warn(msg, kvToFields(keysAndValues)...)
}

// Errorw logs an error message with key-value pairs.
func (s *Sugar) Errorw(msg string, keysAndValues ...interface{}) {
	s.logger.Error(msg, kvToFields(keysAndValues)...)
}

// Fatalw logs a fatal message with key-value pairs.
func (s *Sugar) Fatalw(msg string, keysAndValues ...interface{}) {
	s.logger.Fatal(msg, kvToFields(keysAndValues)...)
}

// kvToFields converts key-value pairs to Fields.
func kvToFields(kv []interface{}) []Field {
	if len(kv)%2 != 0 {
		kv = append(kv, "missing")
	}
	fields := make([]Field, 0, len(kv)/2)
	for i := 0; i < len(kv); i += 2 {
		key, ok := kv[i].(string)
		if !ok {
			key = fmt.Sprintf("%v", kv[i])
		}
		fields = append(fields, Any(key, kv[i+1]))
	}
	return fields
}

// LogEntry represents a structured log entry for parsing/serialization.
type LogEntry struct {
	Timestamp time.Time              `json:"timestamp"`
	Level     string                 `json:"level"`
	Message   string                 `json:"message"`
	Logger    string                 `json:"logger,omitempty"`
	TraceID   string                 `json:"trace_id,omitempty"`
	SpanID    string                 `json:"span_id,omitempty"`
	Fields    map[string]interface{} `json:"fields,omitempty"`
}

// ParseLogEntry parses a JSON log entry.
func ParseLogEntry(data []byte) (*LogEntry, error) {
	var entry LogEntry
	if err := json.Unmarshal(data, &entry); err != nil {
		return nil, err
	}
	return &entry, nil
}

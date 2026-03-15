// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This file contains OpenTelemetry trace correlation and OTLP integration.
package logs

import (
	"context"
	"fmt"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

// OTelLogger is a logger that integrates with OpenTelemetry.
type OTelLogger struct {
	*Logger
	tracerProvider trace.TracerProvider
	tracer         trace.Tracer
	resource       *resource.Resource
	propagator     TraceContextPropagator
}

// TraceContextPropagator propagates trace context to log records.
type TraceContextPropagator interface {
	Inject(ctx context.Context, record *LogRecord)
	Extract(ctx context.Context, record *LogRecord) context.Context
}

// DefaultTracePropagator is the default trace context propagator.
type DefaultTracePropagator struct{}

// Inject injects trace context into the log record.
func (p *DefaultTracePropagator) Inject(ctx context.Context, record *LogRecord) {
	if span := trace.SpanFromContext(ctx); span != nil {
		spanCtx := span.SpanContext()
		record.TraceID = spanCtx.TraceID()
		record.SpanID = spanCtx.SpanID()
		record.TraceFlags = spanCtx.TraceFlags()
	}
}

// Extract extracts trace context from the log record and returns a new context.
func (p *DefaultTracePropagator) Extract(ctx context.Context, record *LogRecord) context.Context {
	if record.TraceID.IsValid() && record.SpanID.IsValid() {
		spanCtx := trace.NewSpanContext(trace.SpanContextConfig{
			TraceID:    record.TraceID,
			SpanID:     record.SpanID,
			TraceFlags: record.TraceFlags,
		})
		return trace.ContextWithSpanContext(ctx, spanCtx)
	}
	return ctx
}

// OTelLoggerConfig is the configuration for an OTelLogger.
type OTelLoggerConfig struct {
	Config
	TracerProvider trace.TracerProvider
	TracerName     string
	Resource       *resource.Resource
	Propagator     TraceContextPropagator
}

// NewOTelLogger creates a new OpenTelemetry-integrated logger.
func NewOTelLogger(config OTelLoggerConfig) *OTelLogger {
	if config.Propagator == nil {
		config.Propagator = &DefaultTracePropagator{}
	}

	logger := NewLogger(config.Config)

	o := &OTelLogger{
		Logger:         logger,
		tracerProvider: config.TracerProvider,
		resource:       config.Resource,
		propagator:     config.Propagator,
	}

	if config.TracerProvider != nil {
		o.tracer = config.TracerProvider.Tracer(config.TracerName)
	}

	return o
}

// WithTrace creates a new logger with trace context from the given span.
func (o *OTelLogger) WithTrace(span trace.Span) *OTelLogger {
	newLogger := *o
	if span != nil {
		spanCtx := span.SpanContext()
		newLogger.Logger = o.Logger.With(
			String("trace_id", spanCtx.TraceID().String()),
			String("span_id", spanCtx.SpanID().String()),
		)
	}
	return &newLogger
}

// WithSpanContext creates a new logger with the given span context.
func (o *OTelLogger) WithSpanContext(spanCtx trace.SpanContext) *OTelLogger {
	newLogger := *o
	if spanCtx.IsValid() {
		newLogger.Logger = o.Logger.With(
			String("trace_id", spanCtx.TraceID().String()),
			String("span_id", spanCtx.SpanID().String()),
		)
	}
	return &newLogger
}

// StartSpan starts a new span and returns a context with the span.
func (o *OTelLogger) StartSpan(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	if o.tracer == nil {
		return ctx, nil
	}
	ctx, span := o.tracer.Start(ctx, name, opts...)
	return ctx, span
}

// LogSpanEvent logs an event on the current span and as a log record.
func (o *OTelLogger) LogSpanEvent(ctx context.Context, name string, attrs ...attribute.KeyValue) {
	// Log to span
	if span := trace.SpanFromContext(ctx); span != nil {
		span.AddEvent(name, trace.WithAttributes(attrs...))
	}

	// Log as log record
	fields := make(Fields, len(attrs)+1)
	fields[0] = String("event", name)
	for i, attr := range attrs {
		fields[i+1] = Field{
			Key:   string(attr.Key),
			Type:  AnyType,
			Value: attr.Value,
		}
	}

	o.InfoContext(ctx, "span event", fields...)
}

// LogError logs an error with trace context.
func (o *OTelLogger) LogError(ctx context.Context, err error, fields ...Field) {
	// Record error on span
	if span := trace.SpanFromContext(ctx); span != nil {
		span.RecordError(err)
	}

	// Log the error
	allFields := make(Fields, len(fields)+1)
	allFields[0] = Error(err)
	copy(allFields[1:], fields)

	o.ErrorContext(ctx, err.Error(), allFields...)
}

// TraceLogger wraps a logger with trace correlation capabilities.
type TraceLogger struct {
	logger     *Logger
	propagator TraceContextPropagator
}

// NewTraceLogger creates a new trace-aware logger.
func NewTraceLogger(logger *Logger, propagator TraceContextPropagator) *TraceLogger {
	if propagator == nil {
		propagator = &DefaultTracePropagator{}
	}
	return &TraceLogger{
		logger:     logger,
		propagator: propagator,
	}
}

// Log logs a message with trace context.
func (t *TraceLogger) Log(ctx context.Context, level Level, msg string, fields ...Field) {
	if !t.logger.Enabled(level) {
		return
	}

	// Extract trace context
	record := &LogRecord{}
	t.propagator.Inject(ctx, record)

	// Add trace fields
	traceFields := make(Fields, 0, 2)
	if record.TraceID.IsValid() {
		traceFields = append(traceFields, String("trace_id", record.TraceID.String()))
	}
	if record.SpanID.IsValid() {
		traceFields = append(traceFields, String("span_id", record.SpanID.String()))
	}

	allFields := make(Fields, len(fields)+len(traceFields))
	copy(allFields, traceFields)
	copy(allFields[len(traceFields):], fields)

	// Map Level to SeverityNumber
	severity := levelToSeverity(level)
	t.logger.log(ctx, severity, msg, allFields...)
}

// levelToSeverity converts Level to SeverityNumber.
func levelToSeverity(level Level) SeverityNumber {
	switch level {
	case LevelTrace:
		return SeverityTrace
	case LevelDebug:
		return SeverityDebug
	case LevelInfo:
		return SeverityInfo
	case LevelWarn:
		return SeverityWarn
	case LevelError:
		return SeverityError
	case LevelFatal:
		return SeverityFatal
	default:
		return SeverityInfo
	}
}

// CorrelatedLogRecord is a log record correlated with a trace span.
type CorrelatedLogRecord struct {
	*LogRecord
	Span trace.Span
}

// LogCorrelator correlates logs with traces.
type LogCorrelator struct {
	mu          sync.RWMutex
	logs        map[trace.TraceID][]*CorrelatedLogRecord
	maxPerTrace int
}

// NewLogCorrelator creates a new log correlator.
func NewLogCorrelator(maxPerTrace int) *LogCorrelator {
	if maxPerTrace <= 0 {
		maxPerTrace = 1000
	}
	return &LogCorrelator{
		logs:        make(map[trace.TraceID][]*CorrelatedLogRecord),
		maxPerTrace: maxPerTrace,
	}
}

// Add adds a log record to the correlator.
func (lc *LogCorrelator) Add(record *CorrelatedLogRecord) {
	if !record.TraceID.IsValid() {
		return
	}

	lc.mu.Lock()
	defer lc.mu.Unlock()

	logs := lc.logs[record.TraceID]
	if len(logs) >= lc.maxPerTrace {
		// Drop oldest
		logs = logs[1:]
	}
	lc.logs[record.TraceID] = append(logs, record)
}

// GetLogs returns logs for a given trace ID.
func (lc *LogCorrelator) GetLogs(traceID trace.TraceID) []*CorrelatedLogRecord {
	lc.mu.RLock()
	defer lc.mu.RUnlock()

	logs := lc.logs[traceID]
	result := make([]*CorrelatedLogRecord, len(logs))
	copy(result, logs)
	return result
}

// Clear clears logs for a given trace ID.
func (lc *LogCorrelator) Clear(traceID trace.TraceID) {
	lc.mu.Lock()
	defer lc.mu.Unlock()
	delete(lc.logs, traceID)
}

// ClearAll clears all logs.
func (lc *LogCorrelator) ClearAll() {
	lc.mu.Lock()
	defer lc.mu.Unlock()
	lc.logs = make(map[trace.TraceID][]*CorrelatedLogRecord)
}

// SpanEventLogger logs events to both a span and as log records.
type SpanEventLogger struct {
	logger *Logger
	span   trace.Span
}

// NewSpanEventLogger creates a new span event logger.
func NewSpanEventLogger(logger *Logger, span trace.Span) *SpanEventLogger {
	return &SpanEventLogger{
		logger: logger,
		span:   span,
	}
}

// Event logs an event to the span.
func (s *SpanEventLogger) Event(name string, attrs ...attribute.KeyValue) {
	if s.span != nil {
		s.span.AddEvent(name, trace.WithAttributes(attrs...))
	}

	fields := make(Fields, len(attrs)+1)
	fields[0] = String("event_name", name)
	for i, attr := range attrs {
		fields[i+1] = Field{
			Key:   string(attr.Key),
			Type:  AnyType,
			Value: attr.Value,
		}
	}

	ctx := context.Background()
	if s.span != nil {
		ctx = trace.ContextWithSpan(ctx, s.span)
	}
	s.logger.InfoContext(ctx, "span event", fields...)
}

// Error records an error on the span and logs it.
func (s *SpanEventLogger) Error(err error, opts ...trace.EventOption) {
	if s.span != nil {
		s.span.RecordError(err, opts...)
	}

	ctx := context.Background()
	if s.span != nil {
		ctx = trace.ContextWithSpan(ctx, s.span)
	}
	s.logger.ErrorContext(ctx, err.Error(), Error(err))
}

// SetStatus sets the span status.
func (s *SpanEventLogger) SetStatus(code codes.Code, description string) {
	if s.span != nil {
		s.span.SetStatus(code, description)
	}

	ctx := context.Background()
	if s.span != nil {
		ctx = trace.ContextWithSpan(ctx, s.span)
	}
	s.logger.InfoContext(ctx, "span status",
		String("status_code", code.String()),
		String("description", description),
	)
}

// SetAttributes sets attributes on the span.
func (s *SpanEventLogger) SetAttributes(attrs ...attribute.KeyValue) {
	if s.span != nil {
		s.span.SetAttributes(attrs...)
	}
}

// End ends the span.
func (s *SpanEventLogger) End(opts ...trace.SpanEndOption) {
	if s.span != nil {
		s.span.End(opts...)
	}
}

// TraceID returns the trace ID of the span.
func (s *SpanEventLogger) TraceID() trace.TraceID {
	if s.span != nil {
		return s.span.SpanContext().TraceID()
	}
	return trace.TraceID{}
}

// SpanID returns the span ID of the span.
func (s *SpanEventLogger) SpanID() trace.SpanID {
	if s.span != nil {
		return s.span.SpanContext().SpanID()
	}
	return trace.SpanID{}
}

// IsRecording returns true if the span is recording.
func (s *SpanEventLogger) IsRecording() bool {
	if s.span != nil {
		return s.span.IsRecording()
	}
	return false
}

// TracedLogger wraps a logger with automatic trace injection.
type TracedLogger struct {
	logger *OTelLogger
	ctx    context.Context
}

// WithContext returns a new TracedLogger with the given context.
func (o *OTelLogger) WithContext(ctx context.Context) *TracedLogger {
	return &TracedLogger{
		logger: o,
		ctx:    ctx,
	}
}

// Debug logs a debug message.
func (t *TracedLogger) Debug(msg string, fields ...Field) {
	t.logger.DebugContext(t.ctx, msg, fields...)
}

// Info logs an info message.
func (t *TracedLogger) Info(msg string, fields ...Field) {
	t.logger.InfoContext(t.ctx, msg, fields...)
}

// Warn logs a warning message.
func (t *TracedLogger) Warn(msg string, fields ...Field) {
	t.logger.WarnContext(t.ctx, msg, fields...)
}

// Error logs an error message.
func (t *TracedLogger) Error(msg string, fields ...Field) {
	t.logger.ErrorContext(t.ctx, msg, fields...)
}

// Fatal logs a fatal message.
func (t *TracedLogger) Fatal(msg string, fields ...Field) {
	t.logger.FatalContext(t.ctx, msg, fields...)
}

// Trace starts a new span and returns a SpanEventLogger.
func (t *TracedLogger) Trace(name string, opts ...trace.SpanStartOption) *SpanEventLogger {
	ctx, span := t.logger.StartSpan(t.ctx, name, opts...)
	t.ctx = ctx
	return NewSpanEventLogger(t.logger.Logger, span)
}

// Span returns a SpanEventLogger for the current span in context.
func (t *TracedLogger) Span() *SpanEventLogger {
	span := trace.SpanFromContext(t.ctx)
	return NewSpanEventLogger(t.logger.Logger, span)
}

// Context returns the current context.
func (t *TracedLogger) Context() context.Context {
	return t.ctx
}

// TraceContext holds trace and span IDs for correlation.
type TraceContext struct {
	TraceID string `json:"trace_id"`
	SpanID  string `json:"span_id"`
	Sampled bool   `json:"sampled"`
}

// FromContext extracts trace context from a context.
func FromContext(ctx context.Context) TraceContext {
	span := trace.SpanFromContext(ctx)
	if span == nil {
		return TraceContext{}
	}
	spanCtx := span.SpanContext()
	if !spanCtx.IsValid() {
		return TraceContext{}
	}
	return TraceContext{
		TraceID: spanCtx.TraceID().String(),
		SpanID:  spanCtx.SpanID().String(),
		Sampled: spanCtx.IsSampled(),
	}
}

// InjectToFields injects trace context into log fields.
func (tc TraceContext) InjectToFields(fields ...Field) []Field {
	if tc.TraceID == "" {
		return fields
	}
	traceFields := []Field{
		String("trace_id", tc.TraceID),
		String("span_id", tc.SpanID),
		Bool("sampled", tc.Sampled),
	}
	return append(traceFields, fields...)
}

// BaggageItem represents a baggage item for log correlation.
type BaggageItem struct {
	Key   string
	Value string
}

// LogBaggage logs baggage items as fields.
func LogBaggage(logger *Logger, items ...BaggageItem) {
	fields := make(Fields, len(items))
	for i, item := range items {
		fields[i] = String("baggage."+item.Key, item.Value)
	}
	logger.Info("baggage", fields...)
}

// TraceSampler is a sampler that uses the trace sampling decision.
type TraceSampler struct{}

// ShouldSample returns true if the trace is sampled.
func (t *TraceSampler) ShouldSample(record *LogRecord) bool {
	return record.TraceFlags.IsSampled()
}

// NewTraceSampler creates a new trace-based sampler.
func NewTraceSampler() *TraceSampler {
	return &TraceSampler{}
}

// CompositeSampler combines multiple samplers.
type CompositeSampler struct {
	samplers []Sampler
	mode     CompositeMode
}

// CompositeMode determines how samplers are combined.
type CompositeMode int

const (
	// CompositeAnd requires all samplers to return true.
	CompositeAnd CompositeMode = iota
	// CompositeOr requires at least one sampler to return true.
	CompositeOr
)

// NewCompositeSampler creates a new composite sampler.
func NewCompositeSampler(mode CompositeMode, samplers ...Sampler) *CompositeSampler {
	return &CompositeSampler{
		samplers: samplers,
		mode:     mode,
	}
}

// ShouldSample implements Sampler.
func (c *CompositeSampler) ShouldSample(record *LogRecord) bool {
	if len(c.samplers) == 0 {
		// Empty AND returns true (identity), empty OR returns false
		return c.mode == CompositeAnd
	}

	if c.mode == CompositeAnd {
		for _, s := range c.samplers {
			if !s.ShouldSample(record) {
				return false
			}
		}
		return true
	}

	// CompositeOr
	for _, s := range c.samplers {
		if s.ShouldSample(record) {
			return true
		}
	}
	return false
}

// LevelSampler samples based on log level.
type LevelSampler struct {
	minLevel Level
}

// NewLevelSampler creates a new level-based sampler.
func NewLevelSampler(minLevel Level) *LevelSampler {
	return &LevelSampler{minLevel: minLevel}
}

// ShouldSample implements Sampler.
func (l *LevelSampler) ShouldSample(record *LogRecord) bool {
	return record.Severity.ToLevel() >= l.minLevel
}

// ConfigurableOTelLogger is an OTelLogger with dynamic configuration.
type ConfigurableOTelLogger struct {
	*OTelLogger
	config         OTelLoggerConfig
	configMu       sync.RWMutex
	onConfigChange func(OTelLoggerConfig)
}

// NewConfigurableOTelLogger creates a new configurable OTel logger.
func NewConfigurableOTelLogger(config OTelLoggerConfig, onChange func(OTelLoggerConfig)) *ConfigurableOTelLogger {
	return &ConfigurableOTelLogger{
		OTelLogger:     NewOTelLogger(config),
		config:         config,
		onConfigChange: onChange,
	}
}

// UpdateConfig updates the logger configuration dynamically.
func (c *ConfigurableOTelLogger) UpdateConfig(config OTelLoggerConfig) {
	c.configMu.Lock()
	c.config = config
	c.configMu.Unlock()

	c.SetLevel(config.Level)

	if c.onConfigChange != nil {
		c.onConfigChange(config)
	}
}

// GetConfig returns the current configuration.
func (c *ConfigurableOTelLogger) GetConfig() OTelLoggerConfig {
	c.configMu.RLock()
	defer c.configMu.RUnlock()
	return c.config
}

// SetupOTelLogger sets up a standard OpenTelemetry logger.
func SetupOTelLogger(serviceName string, opts ...OTelLoggerOption) (*OTelLogger, error) {
	config := defaultOTelLoggerConfig()
	config.TracerName = serviceName

	for _, opt := range opts {
		opt(&config)
	}

	return NewOTelLogger(config), nil
}

// otelLoggerConfig holds configuration for SetupOTelLogger.
type otelLoggerConfig struct {
	OTelLoggerConfig
}

func defaultOTelLoggerConfig() OTelLoggerConfig {
	return OTelLoggerConfig{
		Config: Config{
			Level:  LevelInfo,
			Output: nil, // Uses stdout by default
		},
	}
}

// OTelLoggerOption configures the OTel logger setup.
type OTelLoggerOption func(*OTelLoggerConfig)

// WithOTelLevel sets the log level.
func WithOTelLevel(level Level) OTelLoggerOption {
	return func(c *OTelLoggerConfig) {
		c.Level = level
	}
}

// WithOTelTracerProvider sets the tracer provider.
func WithOTelTracerProvider(provider trace.TracerProvider) OTelLoggerOption {
	return func(c *OTelLoggerConfig) {
		c.TracerProvider = provider
	}
}

// WithOTelResource sets the resource.
func WithOTelResource(r *resource.Resource) OTelLoggerOption {
	return func(c *OTelLoggerConfig) {
		c.Resource = r
	}
}

// TraceSpanEvent is an event associated with a trace span.
type TraceSpanEvent struct {
	Timestamp  time.Time
	Name       string
	Attributes []attribute.KeyValue
	Level      Level
}

// ToLogRecord converts the event to a log record.
func (e *TraceSpanEvent) ToLogRecord() *LogRecord {
	return &LogRecord{
		Timestamp:  e.Timestamp,
		Severity:   levelToSeverity(e.Level),
		Body:       e.Name,
		Attributes: e.Attributes,
	}
}

// OTelSpanProcessor is a span processor that logs span events.
type OTelSpanProcessor struct {
	logger *OTelLogger
}

// NewOTelSpanProcessor creates a new OTel span processor.
func NewOTelSpanProcessor(logger *OTelLogger) *OTelSpanProcessor {
	return &OTelSpanProcessor{logger: logger}
}

// OnStart is called when a span starts.
func (p *OTelSpanProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	p.logger.InfoContext(parent, "span started",
		String("span_name", s.Name()),
		String("trace_id", s.SpanContext().TraceID().String()),
		String("span_id", s.SpanContext().SpanID().String()),
	)
}

// OnEnd is called when a span ends.
func (p *OTelSpanProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	ctx := context.Background()
	p.logger.InfoContext(ctx, "span ended",
		String("span_name", s.Name()),
		String("trace_id", s.SpanContext().TraceID().String()),
		String("span_id", s.SpanContext().SpanID().String()),
		Duration("duration", s.EndTime().Sub(s.StartTime())),
	)
}

// Shutdown shuts down the processor.
func (p *OTelSpanProcessor) Shutdown(ctx context.Context) error {
	return p.logger.Shutdown()
}

// ForceFlush flushes the processor.
func (p *OTelSpanProcessor) ForceFlush(ctx context.Context) error {
	return p.logger.Sync()
}

var _ sdktrace.SpanProcessor = (*OTelSpanProcessor)(nil)

// IsValidTraceID checks if a trace ID string is valid.
func IsValidTraceID(id string) bool {
	if len(id) != 32 {
		return false
	}
	for _, c := range id {
		if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) {
			return false
		}
	}
	return true
}

// IsValidSpanID checks if a span ID string is valid.
func IsValidSpanID(id string) bool {
	if len(id) != 16 {
		return false
	}
	for _, c := range id {
		if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) {
			return false
		}
	}
	return true
}

// ParseTraceID parses a trace ID from string.
func ParseTraceID(id string) (trace.TraceID, error) {
	if !IsValidTraceID(id) {
		return trace.TraceID{}, fmt.Errorf("invalid trace ID: %s", id)
	}
	return trace.TraceIDFromHex(id)
}

// ParseSpanID parses a span ID from string.
func ParseSpanID(id string) (trace.SpanID, error) {
	if !IsValidSpanID(id) {
		return trace.SpanID{}, fmt.Errorf("invalid span ID: %s", id)
	}
	return trace.SpanIDFromHex(id)
}

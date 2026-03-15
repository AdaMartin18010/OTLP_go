package testing

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/metric/metricdata"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
)

// ReadableSpan is an alias for sdktrace.ReadOnlySpan for convenience.
type ReadableSpan = sdktrace.ReadOnlySpan

// StatusCode is an alias for codes.Code for convenience.
type StatusCode = trace.Status

// TestExporter is a test span exporter that stores exported spans in memory.
type TestExporter struct {
	mu     sync.RWMutex
	spans  []sdktrace.ReadOnlySpan
	closed bool
}

// NewTestExporter creates a new TestExporter.
func NewTestExporter() *TestExporter {
	return &TestExporter{
		spans: make([]sdktrace.ReadOnlySpan, 0),
	}
}

// ExportSpans implements sdktrace.SpanExporter.
func (e *TestExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
	e.mu.Lock()
	defer e.mu.Unlock()

	if e.closed {
		return fmt.Errorf("exporter is closed")
	}

	e.spans = append(e.spans, spans...)
	return nil
}

// Shutdown implements sdktrace.SpanExporter.
func (e *TestExporter) Shutdown(ctx context.Context) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.closed = true
	return nil
}

// GetSpans returns a copy of all exported spans.
func (e *TestExporter) GetSpans() []sdktrace.ReadOnlySpan {
	e.mu.RLock()
	defer e.mu.RUnlock()

	result := make([]sdktrace.ReadOnlySpan, len(e.spans))
	copy(result, e.spans)
	return result
}

// GetSpanByName returns the first span with the given name.
func (e *TestExporter) GetSpanByName(name string) (sdktrace.ReadOnlySpan, bool) {
	e.mu.RLock()
	defer e.mu.RUnlock()

	for _, span := range e.spans {
		if span.Name() == name {
			return span, true
		}
	}
	return nil, false
}

// SpanCount returns the number of exported spans.
func (e *TestExporter) SpanCount() int {
	e.mu.RLock()
	defer e.mu.RUnlock()
	return len(e.spans)
}

// Reset clears all exported spans.
func (e *TestExporter) Reset() {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.spans = e.spans[:0]
}

// IsClosed returns true if the exporter has been shut down.
func (e *TestExporter) IsClosed() bool {
	e.mu.RLock()
	defer e.mu.RUnlock()
	return e.closed
}

// TestTracerProvider is a tracer provider for testing.
type TestTracerProvider struct {
	*sdktrace.TracerProvider
	exporter *TestExporter
}

// NewTestTracerProvider creates a new TestTracerProvider with an in-memory exporter.
func NewTestTracerProvider() *TestTracerProvider {
	exporter := NewTestExporter()
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithSyncer(exporter),
	)

	return &TestTracerProvider{
		TracerProvider: tp,
		exporter:       exporter,
	}
}

// GetExporter returns the underlying TestExporter.
func (tp *TestTracerProvider) GetExporter() *TestExporter {
	return tp.exporter
}

// GetSpans returns all exported spans.
func (tp *TestTracerProvider) GetSpans() []sdktrace.ReadOnlySpan {
	return tp.exporter.GetSpans()
}

// Reset clears all exported spans.
func (tp *TestTracerProvider) Reset() {
	tp.exporter.Reset()
}

// TestSpanRecorder records spans for testing.
type TestSpanRecorder struct {
	mu    sync.RWMutex
	spans []sdktrace.ReadOnlySpan
}

// NewTestSpanRecorder creates a new TestSpanRecorder.
func NewTestSpanRecorder() *TestSpanRecorder {
	return &TestSpanRecorder{
		spans: make([]sdktrace.ReadOnlySpan, 0),
	}
}

// OnStart is called when a span starts.
func (r *TestSpanRecorder) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {}

// OnEnd is called when a span ends.
func (r *TestSpanRecorder) OnEnd(s sdktrace.ReadOnlySpan) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.spans = append(r.spans, s)
}

// Shutdown is called when the TracerProvider shuts down.
func (r *TestSpanRecorder) Shutdown(ctx context.Context) error {
	return nil
}

// ForceFlush flushes spans.
func (r *TestSpanRecorder) ForceFlush(ctx context.Context) error {
	return nil
}

// GetSpans returns all recorded spans.
func (r *TestSpanRecorder) GetSpans() []sdktrace.ReadOnlySpan {
	r.mu.RLock()
	defer r.mu.RUnlock()

	result := make([]sdktrace.ReadOnlySpan, len(r.spans))
	copy(result, r.spans)
	return result
}

// Reset clears all recorded spans.
func (r *TestSpanRecorder) Reset() {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.spans = r.spans[:0]
}

// TestMetricReader is a metric reader for testing that stores metrics in memory.
type TestMetricReader struct {
	mu      sync.RWMutex
	metrics metricdata.ResourceMetrics
	closed  bool
}

// NewTestMetricReader creates a new TestMetricReader.
func NewTestMetricReader() *TestMetricReader {
	return &TestMetricReader{}
}

// Aggregation returns the aggregation for an instrument.
func (r *TestMetricReader) Aggregation(kind sdkmetric.InstrumentKind) sdkmetric.Aggregation {
	return sdkmetric.DefaultAggregationSelector(kind)
}

// Temporality returns the temporality for an instrument.
func (r *TestMetricReader) Temporality(kind sdkmetric.InstrumentKind) metricdata.Temporality {
	return sdkmetric.DefaultTemporalitySelector(kind)
}

// Collect gathers metrics.
func (r *TestMetricReader) Collect(ctx context.Context) (metricdata.ResourceMetrics, error) {
	r.mu.RLock()
	defer r.mu.RUnlock()

	if r.closed {
		return metricdata.ResourceMetrics{}, fmt.Errorf("reader is closed")
	}

	return r.metrics, nil
}

// Shutdown closes the reader.
func (r *TestMetricReader) Shutdown(ctx context.Context) error {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.closed = true
	return nil
}

// SetMetrics sets the metrics for testing.
func (r *TestMetricReader) SetMetrics(metrics metricdata.ResourceMetrics) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.metrics = metrics
}

// TestMeterProvider is a meter provider for testing.
type TestMeterProvider struct {
	*sdkmetric.MeterProvider
	reader *TestMetricReader
}

// NewTestMeterProvider creates a new TestMeterProvider.
func NewTestMeterProvider() *TestMeterProvider {
	reader := NewTestMetricReader()
	mp := sdkmetric.NewMeterProvider(
		sdkmetric.WithReader(reader),
	)

	return &TestMeterProvider{
		MeterProvider: mp,
		reader:        reader,
	}
}

// GetReader returns the underlying TestMetricReader.
func (mp *TestMeterProvider) GetReader() *TestMetricReader {
	return mp.reader
}

// MockTracer is a mock implementation of trace.Tracer for testing.
type MockTracer struct {
	name    string
	version string
	spans   []*MockSpan
	mu      sync.RWMutex
}

// NewMockTracer creates a new MockTracer.
func NewMockTracer(name, version string) *MockTracer {
	return &MockTracer{
		name:    name,
		version: version,
		spans:   make([]*MockSpan, 0),
	}
}

// Start creates a new span.
func (t *MockTracer) Start(ctx context.Context, spanName string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	config := trace.NewSpanStartConfig(opts...)
	span := NewMockSpan(spanName, t, config)

	t.mu.Lock()
	t.spans = append(t.spans, span)
	t.mu.Unlock()

	return trace.ContextWithSpan(ctx, span), span
}

// GetSpans returns all created spans.
func (t *MockTracer) GetSpans() []*MockSpan {
	t.mu.RLock()
	defer t.mu.RUnlock()

	result := make([]*MockSpan, len(t.spans))
	copy(result, t.spans)
	return result
}

// Reset clears all spans.
func (t *MockTracer) Reset() {
	t.mu.Lock()
	defer t.mu.Unlock()
	t.spans = t.spans[:0]
}

// MockSpan is a mock implementation of trace.Span for testing.
type MockSpan struct {
	name       string
	tracer     *MockTracer
	spanContext trace.SpanContext
	parent     trace.SpanContext
	status     trace.Status
	attrs      []attribute.KeyValue
	events     []MockEvent
	links      []trace.Link
	startTime  time.Time
	endTime    *time.Time
	ended      bool
	mu         sync.RWMutex
}

// MockEvent represents a recorded event.
type MockEvent struct {
	Name       string
	Attributes []attribute.KeyValue
	Timestamp  time.Time
}

// NewMockSpan creates a new MockSpan.
func NewMockSpan(name string, tracer *MockTracer, config trace.SpanConfig) *MockSpan {
	return &MockSpan{
		name:        name,
		tracer:      tracer,
		spanContext: trace.NewSpanContext(trace.SpanContextConfig{TraceID: [16]byte{1}, SpanID: [8]byte{1}}),
		parent:      trace.SpanContext{},
		attrs:       make([]attribute.KeyValue, 0),
		events:      make([]MockEvent, 0),
		links:       make([]trace.Link{}, 0),
		startTime:   time.Now(),
		status:      trace.Status{Code: trace.StatusCodeUnset},
	}
}

// End ends the span.
func (s *MockSpan) End(options ...trace.SpanEndOption) {
	s.mu.Lock()
	defer s.mu.Unlock()
	now := time.Now()
	s.endTime = &now
	s.ended = true
}

// AddEvent adds an event.
func (s *MockSpan) AddEvent(name string, options ...trace.EventOption) {
	s.mu.Lock()
	defer s.mu.Unlock()

	config := trace.NewEventConfig(options...)
	s.events = append(s.events, MockEvent{
		Name:       name,
		Attributes: config.Attributes(),
		Timestamp:  config.Timestamp(),
	})
}

// AddLink adds a link.
func (s *MockSpan) AddLink(link trace.Link) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.links = append(s.links, link)
}

// IsRecording returns true if the span is recording.
func (s *MockSpan) IsRecording() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return !s.ended
}

// RecordError records an error.
func (s *MockSpan) RecordError(err error, options ...trace.EventOption) {
	if err == nil {
		return
	}

	config := trace.NewEventConfig(options...)
	attrs := append(config.Attributes(),
		attribute.String("exception.type", fmt.Sprintf("%T", err)),
		attribute.String("exception.message", err.Error()),
	)

	s.mu.Lock()
	defer s.mu.Unlock()
	s.events = append(s.events, MockEvent{
		Name:       "exception",
		Attributes: attrs,
		Timestamp:  config.Timestamp(),
	})
}

// SpanContext returns the span context.
func (s *MockSpan) SpanContext() trace.SpanContext {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.spanContext
}

// SetStatus sets the status.
func (s *MockSpan) SetStatus(code codes.Code, description string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.status = trace.Status{Code: code, Description: description}
}

// SetName sets the name.
func (s *MockSpan) SetName(name string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.name = name
}

// SetAttributes sets attributes.
func (s *MockSpan) SetAttributes(kv ...attribute.KeyValue) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.attrs = append(s.attrs, kv...)
}

// TracerProvider returns the tracer provider.
func (s *MockSpan) TracerProvider() trace.TracerProvider {
	return nil
}

// Name returns the span name.
func (s *MockSpan) Name() string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.name
}

// Attributes returns the span attributes.
func (s *MockSpan) Attributes() []attribute.KeyValue {
	s.mu.RLock()
	defer s.mu.RUnlock()
	result := make([]attribute.KeyValue, len(s.attrs))
	copy(result, s.attrs)
	return result
}

// Events returns the span events.
func (s *MockSpan) Events() []MockEvent {
	s.mu.RLock()
	defer s.mu.RUnlock()
	result := make([]MockEvent, len(s.events))
	copy(result, s.events)
	return result
}

// Status returns the span status.
func (s *MockSpan) Status() trace.Status {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.status
}

// IsEnded returns true if the span has ended.
func (s *MockSpan) IsEnded() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.ended
}

// codes alias for trace codes
type codes = trace.StatusCode

// MockMeter is a mock implementation of metric.Meter for testing.
type MockMeter struct {
	name    string
	version string
	counters sync.Map
	upDownCounters sync.Map
	gauges sync.Map
	histograms sync.Map
	observers sync.Map
}

// NewMockMeter creates a new MockMeter.
func NewMockMeter(name, version string) *MockMeter {
	return &MockMeter{
		name:    name,
		version: version,
	}
}

// Int64Counter creates a mock int64 counter.
func (m *MockMeter) Int64Counter(name string, options ...metric.Int64CounterOption) (metric.Int64Counter, error) {
	counter := &MockInt64Counter{name: name}
	m.counters.Store(name, counter)
	return counter, nil
}

// Int64UpDownCounter creates a mock int64 up-down counter.
func (m *MockMeter) Int64UpDownCounter(name string, options ...metric.Int64UpDownCounterOption) (metric.Int64UpDownCounter, error) {
	counter := &MockInt64UpDownCounter{name: name}
	m.upDownCounters.Store(name, counter)
	return counter, nil
}

// Int64Histogram creates a mock int64 histogram.
func (m *MockMeter) Int64Histogram(name string, options ...metric.Int64HistogramOption) (metric.Int64Histogram, error) {
	histogram := &MockInt64Histogram{name: name}
	m.histograms.Store(name, histogram)
	return histogram, nil
}

// Int64ObservableCounter creates a mock int64 observable counter.
func (m *MockMeter) Int64ObservableCounter(name string, options ...metric.Int64ObservableCounterOption) (metric.Int64ObservableCounter, error) {
	counter := &MockInt64ObservableCounter{name: name}
	m.observers.Store(name, counter)
	return counter, nil
}

// Int64ObservableUpDownCounter creates a mock int64 observable up-down counter.
func (m *MockMeter) Int64ObservableUpDownCounter(name string, options ...metric.Int64ObservableUpDownCounterOption) (metric.Int64ObservableUpDownCounter, error) {
	counter := &MockInt64ObservableUpDownCounter{name: name}
	m.observers.Store(name, counter)
	return counter, nil
}

// Int64ObservableGauge creates a mock int64 observable gauge.
func (m *MockMeter) Int64ObservableGauge(name string, options ...metric.Int64ObservableGaugeOption) (metric.Int64ObservableGauge, error) {
	gauge := &MockInt64ObservableGauge{name: name}
	m.observers.Store(name, gauge)
	return gauge, nil
}

// Float64Counter creates a mock float64 counter.
func (m *MockMeter) Float64Counter(name string, options ...metric.Float64CounterOption) (metric.Float64Counter, error) {
	counter := &MockFloat64Counter{name: name}
	m.counters.Store(name, counter)
	return counter, nil
}

// Float64UpDownCounter creates a mock float64 up-down counter.
func (m *MockMeter) Float64UpDownCounter(name string, options ...metric.Float64UpDownCounterOption) (metric.Float64UpDownCounter, error) {
	counter := &MockFloat64UpDownCounter{name: name}
	m.upDownCounters.Store(name, counter)
	return counter, nil
}

// Float64Histogram creates a mock float64 histogram.
func (m *MockMeter) Float64Histogram(name string, options ...metric.Float64HistogramOption) (metric.Float64Histogram, error) {
	histogram := &MockFloat64Histogram{name: name}
	m.histograms.Store(name, histogram)
	return histogram, nil
}

// Float64ObservableCounter creates a mock float64 observable counter.
func (m *MockMeter) Float64ObservableCounter(name string, options ...metric.Float64ObservableCounterOption) (metric.Float64ObservableCounter, error) {
	counter := &MockFloat64ObservableCounter{name: name}
	m.observers.Store(name, counter)
	return counter, nil
}

// Float64ObservableUpDownCounter creates a mock float64 observable up-down counter.
func (m *MockMeter) Float64ObservableUpDownCounter(name string, options ...metric.Float64ObservableUpDownCounterOption) (metric.Float64ObservableUpDownCounter, error) {
	counter := &MockFloat64ObservableUpDownCounter{name: name}
	m.observers.Store(name, counter)
	return counter, nil
}

// Float64ObservableGauge creates a mock float64 observable gauge.
func (m *MockMeter) Float64ObservableGauge(name string, options ...metric.Float64ObservableGaugeOption) (metric.Float64ObservableGauge, error) {
	gauge := &MockFloat64ObservableGauge{name: name}
	m.observers.Store(name, gauge)
	return gauge, nil
}

// RegisterCallback registers a callback for observable instruments.
func (m *MockMeter) RegisterCallback(f metric.Callback, instruments ...metric.Observable) (metric.Registration, error) {
	// In a mock implementation, we simply store the callback and return a no-op registration
	return &MockRegistration{}, nil
}

// MockCounter is a mock counter for testing.
type MockCounter struct {
	name  string
	value int64
}

// MockInt64Counter is a mock int64 counter.
type MockInt64Counter struct {
	name  string
	value int64
}

// Add adds to the counter.
func (c *MockInt64Counter) Add(ctx context.Context, inc int64, options ...metric.AddOption) {
	atomic.AddInt64(&c.value, inc)
}

// Value returns the current value.
func (c *MockInt64Counter) Value() int64 {
	return atomic.LoadInt64(&c.value)
}

// MockFloat64Counter is a mock float64 counter.
type MockFloat64Counter struct {
	name  string
	value uint64 // stored as bits
}

// Add adds to the counter.
func (c *MockFloat64Counter) Add(ctx context.Context, inc float64, options ...metric.AddOption) {
	for {
		old := atomic.LoadUint64(&c.value)
		newVal := old + uint64(inc)
		if atomic.CompareAndSwapUint64(&c.value, old, newVal) {
			return
		}
	}
}

// Value returns the current value.
func (c *MockFloat64Counter) Value() float64 {
	return float64(atomic.LoadUint64(&c.value))
}

// MockInt64UpDownCounter is a mock int64 up-down counter.
type MockInt64UpDownCounter struct {
	name  string
	value int64
}

// Add adds to the counter.
func (c *MockInt64UpDownCounter) Add(ctx context.Context, inc int64, options ...metric.AddOption) {
	atomic.AddInt64(&c.value, inc)
}

// Value returns the current value.
func (c *MockInt64UpDownCounter) Value() int64 {
	return atomic.LoadInt64(&c.value)
}

// MockFloat64UpDownCounter is a mock float64 up-down counter.
type MockFloat64UpDownCounter struct {
	name  string
	value uint64
}

// Add adds to the counter.
func (c *MockFloat64UpDownCounter) Add(ctx context.Context, inc float64, options ...metric.AddOption) {
	for {
		old := atomic.LoadUint64(&c.value)
		newVal := uint64(float64(old) + inc)
		if atomic.CompareAndSwapUint64(&c.value, old, newVal) {
			return
		}
	}
}

// Value returns the current value.
func (c *MockFloat64UpDownCounter) Value() float64 {
	return float64(atomic.LoadUint64(&c.value))
}

// MockInt64Histogram is a mock int64 histogram.
type MockInt64Histogram struct {
	name   string
	values []int64
	mu     sync.RWMutex
}

// Record records a value.
func (h *MockInt64Histogram) Record(ctx context.Context, value int64, options ...metric.RecordOption) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.values = append(h.values, value)
}

// Values returns recorded values.
func (h *MockInt64Histogram) Values() []int64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	result := make([]int64, len(h.values))
	copy(result, h.values)
	return result
}

// MockFloat64Histogram is a mock float64 histogram.
type MockFloat64Histogram struct {
	name   string
	values []float64
	mu     sync.RWMutex
}

// Record records a value.
func (h *MockFloat64Histogram) Record(ctx context.Context, value float64, options ...metric.RecordOption) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.values = append(h.values, value)
}

// Values returns recorded values.
func (h *MockFloat64Histogram) Values() []float64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	result := make([]float64, len(h.values))
	copy(result, h.values)
	return result
}

// Mock observable instruments (placeholders)
type MockInt64ObservableCounter struct{ name string }
type MockInt64ObservableUpDownCounter struct{ name string }
type MockInt64ObservableGauge struct{ name string }
type MockFloat64ObservableCounter struct{ name string }
type MockFloat64ObservableUpDownCounter struct{ name string }
type MockFloat64ObservableGauge struct{ name string }

// MockRegistration is a mock registration.
type MockRegistration struct{}

// Unregister unregisters the callback.
func (r *MockRegistration) Unregister() error { return nil }

// SetupTestTelemetry creates a complete test telemetry setup with tracer and meter providers.
func SetupTestTelemetry(t testing.TB) (*TestTracerProvider, *TestMeterProvider) {
	tp := NewTestTracerProvider()
	mp := NewTestMeterProvider()

	t.Cleanup(func() {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		if err := tp.Shutdown(ctx); err != nil {
			t.Logf("Warning: failed to shutdown tracer provider: %v", err)
		}
		if err := mp.Shutdown(ctx); err != nil {
			t.Logf("Warning: failed to shutdown meter provider: %v", err)
		}
	})

	return tp, mp
}

// GetMockCounter retrieves a mock counter by name.
func (m *MockMeter) GetMockCounter(name string) (*MockInt64Counter, bool) {
	if v, ok := m.counters.Load(name); ok {
		return v.(*MockInt64Counter), true
	}
	return nil, false
}

// GetMockHistogram retrieves a mock histogram by name.
func (m *MockMeter) GetMockHistogram(name string) (*MockInt64Histogram, bool) {
	if v, ok := m.histograms.Load(name); ok {
		return v.(*MockInt64Histogram), true
	}
	return nil, false
}

// AssertSpanRecorded asserts that a span was recorded by the exporter.
func AssertSpanRecorded(t testing.TB, exporter *TestExporter, spanName string) {
	t.Helper()
	_, found := exporter.GetSpanByName(spanName)
	require.True(t, found, "Expected span %q to be recorded", spanName)
}

// RequireSpanRecorded requires that a span was recorded by the exporter.
func RequireSpanRecorded(t testing.TB, exporter *TestExporter, spanName string) *sdktrace.ReadOnlySpan {
	t.Helper()
	span, found := exporter.GetSpanByName(spanName)
	require.True(t, found, "Expected span %q to be recorded", spanName)
	return &span
}

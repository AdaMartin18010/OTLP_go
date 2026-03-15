// Package types provides telemetry data types for OpenTelemetry compatible data.
package types

import (
	"encoding/json"
	"fmt"
	"sync"
)

// Span represents a single operation within a trace.
// Spans are the building blocks of distributed traces, representing
// units of work or operations in a system.
//
// Example:
//
//	span := &types.Span{
//	    TraceID:   types.NewTraceID(),
//	    SpanID:    types.NewSpanID(),
//	    ParentID:  parentSpanID,
//	    Name:      "process-order",
//	    Kind:      types.SpanKindServer,
//	    StartTime: types.Now(),
//	    Attributes: types.NewAttributes(
//	        "order.id", "12345",
//	        "customer.id", "67890",
//	    ),
//	}
//	// ... do work ...
//	span.EndTime = types.Now()
//	span.Status = types.Status{Code: types.StatusOK}
type Span struct {
	// TraceID is the trace identifier.
	TraceID TraceID `json:"trace_id"`

	// SpanID is the unique span identifier.
	SpanID SpanID `json:"span_id"`

	// TraceState is the W3C trace context tracestate header.
	TraceState string `json:"trace_state,omitempty"`

	// ParentSpanID is the parent span ID (empty if root span).
	ParentSpanID SpanID `json:"parent_span_id,omitempty"`

	// Flags are the trace flags.
	Flags Flags `json:"flags,omitempty"`

	// Name is the span name.
	Name string `json:"name"`

	// Kind is the span kind.
	Kind SpanKind `json:"kind"`

	// StartTime is when the span started.
	StartTime Timestamp `json:"start_time"`

	// EndTime is when the span ended.
	EndTime Timestamp `json:"end_time,omitempty"`

	// Attributes are the span attributes.
	Attributes Attributes `json:"attributes,omitempty"`

	// DroppedAttributeCount is the number of dropped attributes.
	DroppedAttributeCount uint32 `json:"dropped_attribute_count,omitempty"`

	// Events are timed events that occurred during the span.
	Events []Event `json:"events,omitempty"`

	// DroppedEventCount is the number of dropped events.
	DroppedEventCount uint32 `json:"dropped_event_count,omitempty"`

	// Links are links to other spans.
	Links []Link `json:"links,omitempty"`

	// DroppedLinkCount is the number of dropped links.
	DroppedLinkCount uint32 `json:"dropped_link_count,omitempty"`

	// Status is the span status.
	Status Status `json:"status,omitempty"`

	// Resource is the resource that produced this span.
	Resource *Resource `json:"resource,omitempty"`

	// InstrumentationScope identifies the instrumentation library.
	InstrumentationScope InstrumentationScope `json:"instrumentation_scope,omitempty"`
}

// IsRoot returns true if this is a root span (no parent).
func (s *Span) IsRoot() bool {
	return !s.ParentSpanID.IsValid()
}

// IsEnded returns true if the span has ended.
func (s *Span) IsEnded() bool {
	return !s.EndTime.IsZero()
}

// Duration returns the span duration. Returns 0 if span hasn't ended.
func (s *Span) Duration() Duration {
	if !s.IsEnded() {
		return Duration{}
	}
	return NewDuration(s.EndTime.Time.Sub(s.StartTime.Time))
}

// End marks the span as ended with the given timestamp.
func (s *Span) End(t Timestamp) {
	s.EndTime = t
}

// EndNow marks the span as ended with the current time.
func (s *Span) EndNow() {
	s.EndTime = Now()
}

// AddEvent adds an event to the span.
func (s *Span) AddEvent(name string, t Timestamp, attrs ...Attribute) {
	s.Events = append(s.Events, Event{
		Name:       name,
		Timestamp:  t,
		Attributes: attrs,
	})
}

// AddLink adds a link to the span.
func (s *Span) AddLink(traceID TraceID, spanID SpanID, attrs ...Attribute) {
	s.Links = append(s.Links, Link{
		TraceID:    traceID,
		SpanID:     spanID,
		Attributes: attrs,
	})
}

// SetStatus sets the span status.
func (s *Span) SetStatus(code StatusCode, description string) {
	s.Status = Status{
		Code:        code,
		Description: description,
	}
}

// SetError sets the span status to error with the given description.
func (s *Span) SetError(description string) {
	s.SetStatus(StatusError, description)
}

// Clone creates a deep copy of the span.
func (s *Span) Clone() *Span {
	if s == nil {
		return nil
	}

	cloned := &Span{
		TraceID:               s.TraceID,
		SpanID:                s.SpanID,
		TraceState:            s.TraceState,
		ParentSpanID:          s.ParentSpanID,
		Flags:                 s.Flags,
		Name:                  s.Name,
		Kind:                  s.Kind,
		StartTime:             s.StartTime,
		EndTime:               s.EndTime,
		Attributes:            s.Attributes.Clone(),
		DroppedAttributeCount: s.DroppedAttributeCount,
		Events:                make([]Event, len(s.Events)),
		DroppedEventCount:     s.DroppedEventCount,
		Links:                 make([]Link, len(s.Links)),
		DroppedLinkCount:      s.DroppedLinkCount,
		Status:                s.Status,
		InstrumentationScope:  s.InstrumentationScope,
	}

	copy(cloned.Events, s.Events)
	copy(cloned.Links, s.Links)

	if s.Resource != nil {
		cloned.Resource = s.Resource.Clone()
	}

	return cloned
}

// MarshalJSON implements json.Marshaler.
func (s *Span) MarshalJSON() ([]byte, error) {
	type spanJSON struct {
		TraceID               string               `json:"trace_id"`
		SpanID                string               `json:"span_id"`
		TraceState            string               `json:"trace_state,omitempty"`
		ParentSpanID          string               `json:"parent_span_id,omitempty"`
		Flags                 string               `json:"flags,omitempty"`
		Name                  string               `json:"name"`
		Kind                  SpanKind             `json:"kind"`
		StartTime             Timestamp            `json:"start_time"`
		EndTime               Timestamp            `json:"end_time,omitempty"`
		Attributes            Attributes           `json:"attributes,omitempty"`
		DroppedAttributeCount uint32               `json:"dropped_attribute_count,omitempty"`
		Events                []Event              `json:"events,omitempty"`
		DroppedEventCount     uint32               `json:"dropped_event_count,omitempty"`
		Links                 []Link               `json:"links,omitempty"`
		DroppedLinkCount      uint32               `json:"dropped_link_count,omitempty"`
		Status                Status               `json:"status,omitempty"`
		Resource              *Resource            `json:"resource,omitempty"`
		InstrumentationScope  InstrumentationScope `json:"instrumentation_scope,omitempty"`
	}

	return json.Marshal(spanJSON{
		TraceID:               s.TraceID.String(),
		SpanID:                s.SpanID.String(),
		TraceState:            s.TraceState,
		ParentSpanID:          s.ParentSpanID.String(),
		Flags:                 s.Flags.String(),
		Name:                  s.Name,
		Kind:                  s.Kind,
		StartTime:             s.StartTime,
		EndTime:               s.EndTime,
		Attributes:            s.Attributes,
		DroppedAttributeCount: s.DroppedAttributeCount,
		Events:                s.Events,
		DroppedEventCount:     s.DroppedEventCount,
		Links:                 s.Links,
		DroppedLinkCount:      s.DroppedLinkCount,
		Status:                s.Status,
		Resource:              s.Resource,
		InstrumentationScope:  s.InstrumentationScope,
	})
}

// Status represents the status of a span.
type Status struct {
	// Code is the status code.
	Code StatusCode `json:"code"`
	// Description provides additional details when Code is Error.
	Description string `json:"description,omitempty"`
}

// IsError returns true if the status indicates an error.
func (s Status) IsError() bool {
	return s.Code.IsError()
}

// IsOK returns true if the status indicates success.
func (s Status) IsOK() bool {
	return s.Code == StatusOK
}

// IsUnset returns true if the status is unset.
func (s Status) IsUnset() bool {
	return s.Code == StatusUnset
}

// Event represents a timed event that occurred during a span.
type Event struct {
	// Name is the event name.
	Name string `json:"name"`
	// Timestamp is when the event occurred.
	Timestamp Timestamp `json:"timestamp"`
	// Attributes are event attributes.
	Attributes Attributes `json:"attributes,omitempty"`
	// DroppedAttributeCount is the number of dropped attributes.
	DroppedAttributeCount uint32 `json:"dropped_attribute_count,omitempty"`
}

// Link represents a reference to another span.
type Link struct {
	// TraceID is the linked trace ID.
	TraceID TraceID `json:"trace_id"`
	// SpanID is the linked span ID.
	SpanID SpanID `json:"span_id"`
	// TraceState is the W3C tracestate.
	TraceState string `json:"trace_state,omitempty"`
	// Attributes are link attributes.
	Attributes Attributes `json:"attributes,omitempty"`
	// DroppedAttributeCount is the number of dropped attributes.
	DroppedAttributeCount uint32 `json:"dropped_attribute_count,omitempty"`
}

// InstrumentationScope identifies the instrumentation library.
type InstrumentationScope struct {
	// Name is the instrumentation library name.
	Name string `json:"name"`
	// Version is the instrumentation library version.
	Version string `json:"version,omitempty"`
	// Attributes are additional scope attributes.
	Attributes Attributes `json:"attributes,omitempty"`
}

// String returns the string representation.
func (is InstrumentationScope) String() string {
	if is.Version != "" {
		return fmt.Sprintf("%s@%s", is.Name, is.Version)
	}
	return is.Name
}

// IsEmpty returns true if the scope is empty.
func (is InstrumentationScope) IsEmpty() bool {
	return is.Name == ""
}

// LogRecord represents a log entry.
type LogRecord struct {
	// Timestamp is when the log was recorded.
	Timestamp Timestamp `json:"timestamp"`
	// ObservedTimestamp is when the log was observed (may differ from Timestamp).
	ObservedTimestamp Timestamp `json:"observed_timestamp,omitempty"`
	// Severity indicates the severity level.
	Severity LogLevel `json:"severity"`
	// SeverityText is the human-readable severity.
	SeverityText string `json:"severity_text,omitempty"`
	// Body is the log body/message.
	Body Value `json:"body"`
	// Attributes are log attributes.
	Attributes Attributes `json:"attributes,omitempty"`
	// DroppedAttributeCount is the number of dropped attributes.
	DroppedAttributeCount uint32 `json:"dropped_attribute_count,omitempty"`
	// TraceID is the associated trace ID (if any).
	TraceID TraceID `json:"trace_id,omitempty"`
	// SpanID is the associated span ID (if any).
	SpanID SpanID `json:"span_id,omitempty"`
	// TraceFlags are the trace flags.
	TraceFlags Flags `json:"trace_flags,omitempty"`
	// Resource is the resource that produced this log.
	Resource *Resource `json:"resource,omitempty"`
	// InstrumentationScope identifies the instrumentation library.
	InstrumentationScope InstrumentationScope `json:"instrumentation_scope,omitempty"`
}

// NewLogRecord creates a new log record with the given severity and body.
func NewLogRecord(severity LogLevel, body string) *LogRecord {
	return &LogRecord{
		Timestamp:         Now(),
		ObservedTimestamp: Now(),
		Severity:          severity,
		SeverityText:      severity.String(),
		Body:              StringValue(body),
	}
}

// SetTraceContext associates the log with a span.
func (l *LogRecord) SetTraceContext(traceID TraceID, spanID SpanID, flags Flags) {
	l.TraceID = traceID
	l.SpanID = spanID
	l.TraceFlags = flags
}

// String returns the log body as a string.
func (l *LogRecord) String() string {
	return l.Body.AsString()
}

// Metric represents a metric data point.
type Metric struct {
	// Name is the metric name.
	Name string `json:"name"`
	// Description describes the metric.
	Description string `json:"description,omitempty"`
	// Unit is the unit of measurement.
	Unit string `json:"unit,omitempty"`
	// Type is the metric type.
	Type MetricType `json:"type"`
	// Data contains the metric data points.
	Data MetricData `json:"data"`
	// Resource is the resource that produced this metric.
	Resource *Resource `json:"resource,omitempty"`
	// InstrumentationScope identifies the instrumentation library.
	InstrumentationScope InstrumentationScope `json:"instrumentation_scope,omitempty"`
}

// MetricType represents the type of metric.
type MetricType int32

const (
	// MetricTypeGauge is a gauge metric.
	MetricTypeGauge MetricType = 0
	// MetricTypeSum is a sum metric.
	MetricTypeSum MetricType = 1
	// MetricTypeHistogram is a histogram metric.
	MetricTypeHistogram MetricType = 2
	// MetricTypeSummary is a summary metric.
	MetricTypeSummary MetricType = 3
	// MetricTypeExponentialHistogram is an exponential histogram metric.
	MetricTypeExponentialHistogram MetricType = 4
)

// String returns the string representation.
func (m MetricType) String() string {
	switch m {
	case MetricTypeGauge:
		return "Gauge"
	case MetricTypeSum:
		return "Sum"
	case MetricTypeHistogram:
		return "Histogram"
	case MetricTypeSummary:
		return "Summary"
	case MetricTypeExponentialHistogram:
		return "ExponentialHistogram"
	default:
		return fmt.Sprintf("MetricType(%d)", m)
	}
}

// MetricData is a union type for metric data.
type MetricData struct {
	// Gauge points.
	GaugePoints []NumberDataPoint `json:"gauge_points,omitempty"`
	// Sum points.
	SumPoints []SumDataPoint `json:"sum_points,omitempty"`
	// Histogram points.
	HistogramPoints []HistogramDataPoint `json:"histogram_points,omitempty"`
}

// NumberDataPoint represents a numeric data point.
type NumberDataPoint struct {
	// Attributes are data point attributes.
	Attributes Attributes `json:"attributes,omitempty"`
	// StartTime is when the aggregation started.
	StartTime Timestamp `json:"start_time,omitempty"`
	// Time is when the value was recorded.
	Time Timestamp `json:"time"`
	// Value is the numeric value.
	Value Value `json:"value"`
	// Exemplars are exemplars for this data point.
	Exemplars []Exemplar `json:"exemplars,omitempty"`
}

// SumDataPoint represents a sum data point.
type SumDataPoint struct {
	NumberDataPoint
	// IsMonotonic indicates if the sum is monotonic.
	IsMonotonic bool `json:"is_monotonic"`
	// AggregationTemporality is the temporality.
	AggregationTemporality AggregationTemporality `json:"aggregation_temporality"`
}

// HistogramDataPoint represents a histogram data point.
type HistogramDataPoint struct {
	// Attributes are data point attributes.
	Attributes Attributes `json:"attributes,omitempty"`
	// StartTime is when the aggregation started.
	StartTime Timestamp `json:"start_time,omitempty"`
	// Time is when the value was recorded.
	Time Timestamp `json:"time"`
	// Count is the number of values.
	Count uint64 `json:"count"`
	// Sum is the sum of values (optional).
	Sum *float64 `json:"sum,omitempty"`
	// BucketCounts are the counts in each bucket.
	BucketCounts []uint64 `json:"bucket_counts,omitempty"`
	// ExplicitBounds are the bucket boundaries.
	ExplicitBounds []float64 `json:"explicit_bounds,omitempty"`
	// Min is the minimum value (optional).
	Min *float64 `json:"min,omitempty"`
	// Max is the maximum value (optional).
	Max *float64 `json:"max,omitempty"`
	// Exemplars are exemplars for this data point.
	Exemplars []Exemplar `json:"exemplars,omitempty"`
}

// AggregationTemporality represents the temporality of aggregation.
type AggregationTemporality int32

const (
	// AggregationTemporalityUnspecified is unspecified.
	AggregationTemporalityUnspecified AggregationTemporality = 0
	// AggregationTemporalityDelta is delta temporality.
	AggregationTemporalityDelta AggregationTemporality = 1
	// AggregationTemporalityCumulative is cumulative temporality.
	AggregationTemporalityCumulative AggregationTemporality = 2
)

// Exemplar represents an exemplar value.
type Exemplar struct {
	// FilteredAttributes are filtered attributes.
	FilteredAttributes Attributes `json:"filtered_attributes,omitempty"`
	// Time is when the exemplar was recorded.
	Time Timestamp `json:"time"`
	// Value is the exemplar value.
	Value Value `json:"value"`
	// TraceID is the associated trace ID.
	TraceID TraceID `json:"trace_id,omitempty"`
	// SpanID is the associated span ID.
	SpanID SpanID `json:"span_id,omitempty"`
}

// TracesData holds a collection of spans.
type TracesData struct {
	// ResourceSpans are spans grouped by resource.
	ResourceSpans []ResourceSpans `json:"resource_spans"`
}

// ResourceSpans groups spans by resource and instrumentation scope.
type ResourceSpans struct {
	// Resource is the resource that produced the spans.
	Resource *Resource `json:"resource"`
	// ScopeSpans are spans grouped by instrumentation scope.
	ScopeSpans []ScopeSpans `json:"scope_spans"`
	// SchemaURL is the schema URL.
	SchemaURL string `json:"schema_url,omitempty"`
}

// ScopeSpans groups spans by instrumentation scope.
type ScopeSpans struct {
	// Scope is the instrumentation scope.
	Scope InstrumentationScope `json:"scope"`
	// Spans are the spans.
	Spans []Span `json:"spans"`
	// SchemaURL is the schema URL.
	SchemaURL string `json:"schema_url,omitempty"`
}

// MetricsData holds a collection of metrics.
type MetricsData struct {
	// ResourceMetrics are metrics grouped by resource.
	ResourceMetrics []ResourceMetrics `json:"resource_metrics"`
}

// ResourceMetrics groups metrics by resource and instrumentation scope.
type ResourceMetrics struct {
	// Resource is the resource that produced the metrics.
	Resource *Resource `json:"resource"`
	// ScopeMetrics are metrics grouped by instrumentation scope.
	ScopeMetrics []ScopeMetrics `json:"scope_metrics"`
	// SchemaURL is the schema URL.
	SchemaURL string `json:"schema_url,omitempty"`
}

// ScopeMetrics groups metrics by instrumentation scope.
type ScopeMetrics struct {
	// Scope is the instrumentation scope.
	Scope InstrumentationScope `json:"scope"`
	// Metrics are the metrics.
	Metrics []Metric `json:"metrics"`
	// SchemaURL is the schema URL.
	SchemaURL string `json:"schema_url,omitempty"`
}

// LogsData holds a collection of log records.
type LogsData struct {
	// ResourceLogs are logs grouped by resource.
	ResourceLogs []ResourceLogs `json:"resource_logs"`
}

// ResourceLogs groups logs by resource and instrumentation scope.
type ResourceLogs struct {
	// Resource is the resource that produced the logs.
	Resource *Resource `json:"resource"`
	// ScopeLogs are logs grouped by instrumentation scope.
	ScopeLogs []ScopeLogs `json:"scope_logs"`
	// SchemaURL is the schema URL.
	SchemaURL string `json:"schema_url,omitempty"`
}

// ScopeLogs groups logs by instrumentation scope.
type ScopeLogs struct {
	// Scope is the instrumentation scope.
	Scope InstrumentationScope `json:"scope"`
	// LogRecords are the log records.
	LogRecords []LogRecord `json:"log_records"`
	// SchemaURL is the schema URL.
	SchemaURL string `json:"schema_url,omitempty"`
}

// TelemetryBatch represents a batch of telemetry data for efficient processing.
type TelemetryBatch struct {
	mu sync.RWMutex

	// Spans in the batch.
	Spans []*Span
	// Logs in the batch.
	Logs []*LogRecord
	// Metrics in the batch.
	Metrics []*Metric

	// Resource is the common resource (optional, can be per-item).
	Resource *Resource
}

// NewTelemetryBatch creates a new telemetry batch.
func NewTelemetryBatch() *TelemetryBatch {
	return &TelemetryBatch{
		Spans:   make([]*Span, 0),
		Logs:    make([]*LogRecord, 0),
		Metrics: make([]*Metric, 0),
	}
}

// AddSpan adds a span to the batch.
func (b *TelemetryBatch) AddSpan(span *Span) {
	if b == nil || span == nil {
		return
	}
	b.mu.Lock()
	defer b.mu.Unlock()
	b.Spans = append(b.Spans, span)
}

// AddLog adds a log to the batch.
func (b *TelemetryBatch) AddLog(log *LogRecord) {
	if b == nil || log == nil {
		return
	}
	b.mu.Lock()
	defer b.mu.Unlock()
	b.Logs = append(b.Logs, log)
}

// AddMetric adds a metric to the batch.
func (b *TelemetryBatch) AddMetric(metric *Metric) {
	if b == nil || metric == nil {
		return
	}
	b.mu.Lock()
	defer b.mu.Unlock()
	b.Metrics = append(b.Metrics, metric)
}

// SpanCount returns the number of spans in the batch.
func (b *TelemetryBatch) SpanCount() int {
	if b == nil {
		return 0
	}
	b.mu.RLock()
	defer b.mu.RUnlock()
	return len(b.Spans)
}

// LogCount returns the number of logs in the batch.
func (b *TelemetryBatch) LogCount() int {
	if b == nil {
		return 0
	}
	b.mu.RLock()
	defer b.mu.RUnlock()
	return len(b.Logs)
}

// MetricCount returns the number of metrics in the batch.
func (b *TelemetryBatch) MetricCount() int {
	if b == nil {
		return 0
	}
	b.mu.RLock()
	defer b.mu.RUnlock()
	return len(b.Metrics)
}

// IsEmpty returns true if the batch is empty.
func (b *TelemetryBatch) IsEmpty() bool {
	return b.SpanCount() == 0 && b.LogCount() == 0 && b.MetricCount() == 0
}

// Clear removes all items from the batch.
func (b *TelemetryBatch) Clear() {
	if b == nil {
		return
	}
	b.mu.Lock()
	defer b.mu.Unlock()
	b.Spans = b.Spans[:0]
	b.Logs = b.Logs[:0]
	b.Metrics = b.Metrics[:0]
}

// ToTracesData converts the batch to TracesData.
func (b *TelemetryBatch) ToTracesData() *TracesData {
	if b == nil || len(b.Spans) == 0 {
		return &TracesData{ResourceSpans: []ResourceSpans{}}
	}

	// Group spans by resource
	resourceMap := make(map[string]*ResourceSpans)

	b.mu.RLock()
	defer b.mu.RUnlock()

	for _, span := range b.Spans {
		var resourceKey string
		var resource *Resource

		if span.Resource != nil {
			resource = span.Resource
			resourceKey = resource.Hash()
		}

		rs, exists := resourceMap[resourceKey]
		if !exists {
			rs = &ResourceSpans{
				Resource:   resource,
				ScopeSpans: []ScopeSpans{},
			}
			resourceMap[resourceKey] = rs
		}

		// Find or create scope spans
		var scopeIdx = -1
		scopeKey := span.InstrumentationScope.String()
		for i, ss := range rs.ScopeSpans {
			if ss.Scope.String() == scopeKey {
				scopeIdx = i
				break
			}
		}

		if scopeIdx == -1 {
			rs.ScopeSpans = append(rs.ScopeSpans, ScopeSpans{
				Scope: span.InstrumentationScope,
				Spans: []Span{*span},
			})
		} else {
			rs.ScopeSpans[scopeIdx].Spans = append(rs.ScopeSpans[scopeIdx].Spans, *span)
		}
	}

	// Convert map to slice
	result := &TracesData{
		ResourceSpans: make([]ResourceSpans, 0, len(resourceMap)),
	}
	for _, rs := range resourceMap {
		result.ResourceSpans = append(result.ResourceSpans, *rs)
	}

	return result
}

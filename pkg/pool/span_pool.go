// Package pool provides object pool implementations for the OTLP Go SDK.
package pool

import (
	"sync"
	"sync/atomic"
	"time"
)

// Span represents a trace span for OpenTelemetry.
// This is a simplified representation for demonstration purposes.
// In production, this would align with OpenTelemetry's trace.Span interface.
type Span struct {
	// TraceID is the trace identifier
	TraceID [16]byte

	// SpanID is the span identifier
	SpanID [8]byte

	// ParentSpanID is the parent span identifier (optional)
	ParentSpanID [8]byte

	// Name is the span name
	Name string

	// StartTime is when the span started
	StartTime time.Time

	// EndTime is when the span ended (zero if not ended)
	EndTime time.Time

	// Attributes are key-value pairs attached to the span
	Attributes map[string]any

	// Events are timed events recorded during the span
	Events []SpanEvent

	// Links are references to other spans
	Links []SpanLink

	// StatusCode indicates the span status (Unset, Ok, Error)
	StatusCode uint32

	// StatusMessage provides additional status information
	StatusMessage string

	// Kind indicates the type of span (Internal, Server, Client, Producer, Consumer)
	Kind SpanKind

	// flags for internal state management
	ended bool
}

// SpanKind represents the type of span.
type SpanKind int

const (
	// SpanKindUnspecified is an unspecified span kind.
	SpanKindUnspecified SpanKind = 0
	// SpanKindInternal is an internal operation.
	SpanKindInternal SpanKind = 1
	// SpanKindServer indicates a server operation.
	SpanKindServer SpanKind = 2
	// SpanKindClient indicates a client operation.
	SpanKindClient SpanKind = 3
	// SpanKindProducer indicates a producer operation.
	SpanKindProducer SpanKind = 4
	// SpanKindConsumer indicates a consumer operation.
	SpanKindConsumer SpanKind = 5
)

// SpanEvent represents a timed event in a span.
type SpanEvent struct {
	Name       string
	Timestamp  time.Time
	Attributes map[string]any
}

// SpanLink represents a reference to another span.
type SpanLink struct {
	TraceID    [16]byte
	SpanID     [8]byte
	Attributes map[string]any
}

// Reset resets the span to its zero value for reuse.
// This clears all data while preserving allocated capacity where possible.
func (s *Span) Reset() {
	// Reset identifiers
	for i := range s.TraceID {
		s.TraceID[i] = 0
	}
	for i := range s.SpanID {
		s.SpanID[i] = 0
	}
	for i := range s.ParentSpanID {
		s.ParentSpanID[i] = 0
	}

	// Reset basic fields
	s.Name = ""
	s.StartTime = time.Time{}
	s.EndTime = time.Time{}
	s.StatusCode = 0
	s.StatusMessage = ""
	s.Kind = SpanKindUnspecified
	s.ended = false

	// Clear attributes while preserving map
	for k := range s.Attributes {
		delete(s.Attributes, k)
	}

	// Clear events while preserving slice capacity
	s.Events = s.Events[:0]

	// Clear links while preserving slice capacity
	s.Links = s.Links[:0]
}

// IsRecording returns true if the span is recording events.
func (s *Span) IsRecording() bool {
	return !s.ended && !s.StartTime.IsZero()
}

// End marks the span as ended.
func (s *Span) End(options ...SpanEndOption) {
	if s.ended {
		return
	}

	cfg := &spanEndConfig{}
	for _, opt := range options {
		opt(cfg)
	}

	if cfg.timestamp.IsZero() {
		s.EndTime = time.Now()
	} else {
		s.EndTime = cfg.timestamp
	}

	s.ended = true
}

// spanEndConfig holds configuration for span end options.
type spanEndConfig struct {
	timestamp time.Time
}

// SpanEndOption is an option for ending a span.
type SpanEndOption func(*spanEndConfig)

// WithTimestamp sets the end timestamp.
func WithTimestamp(t time.Time) SpanEndOption {
	return func(cfg *spanEndConfig) {
		cfg.timestamp = t
	}
}

// SpanPool is a specialized pool for Span objects.
// It provides efficient span reuse for high-throughput tracing scenarios.
//
// Example usage:
//
//	sp := pool.NewSpanPool(1000)
//	span := sp.Get()
//	defer func() {
//	    span.End()
//	    sp.Put(span)
//	}()
//
//	span.Name = "my-operation"
//	span.StartTime = time.Now()
//	// ... record span data ...
type SpanPool struct {
	pool    *Pool[*Span]
	maxSize int32

	// attributePool is a pool for attribute maps
	attributePool sync.Pool

	// eventPool is a pool for event slices
	eventPool sync.Pool

	// linkPool is a pool for link slices
	linkPool sync.Pool
}

// DefaultSpanPoolSize is the default maximum size for span pools.
const DefaultSpanPoolSize = 10000

// MaxAttributes is the maximum number of attributes to keep in pooled maps.
const MaxAttributes = 32

// MaxEvents is the maximum number of events to keep in pooled slices.
const MaxEvents = 10

// MaxLinks is the maximum number of links to keep in pooled slices.
const MaxLinks = 5

// NewSpanPool creates a new SpanPool.
//
// Parameters:
//   - maxSize: maximum number of spans to keep in the pool (0 = unlimited)
//
// Example:
//
//	sp := pool.NewSpanPool(10000)
func NewSpanPool(maxSize int32) *SpanPool {
	sp := &SpanPool{
		maxSize: maxSize,
	}

	sp.pool = New(
		func() *Span {
			return &Span{
				Attributes: make(map[string]any, MaxAttributes),
				Events:     make([]SpanEvent, 0, MaxEvents),
				Links:      make([]SpanLink, 0, MaxLinks),
			}
		},
		WithMaxSize[*Span](maxSize),
		WithReset(func(s *Span) {
			s.Reset()
		}),
	)

	// Initialize sub-pools
	sp.attributePool = sync.Pool{
		New: func() any {
			return make(map[string]any, MaxAttributes)
		},
	}

	sp.eventPool = sync.Pool{
		New: func() any {
			return make([]SpanEvent, 0, MaxEvents)
		},
	}

	sp.linkPool = sync.Pool{
		New: func() any {
			return make([]SpanLink, 0, MaxLinks)
		},
	}

	return sp
}

// Get retrieves a span from the pool.
// The returned span is reset and ready for use.
func (sp *SpanPool) Get() *Span {
	return sp.pool.Get()
}

// Put returns a span to the pool.
// The span will be reset before being reused.
func (sp *SpanPool) Put(span *Span) {
	if span == nil {
		return
	}

	// Validate span state
	if !span.ended && !span.StartTime.IsZero() {
		// Span was started but not ended - end it now
		span.End()
	}

	sp.pool.Put(span)
}

// Stats returns statistics about the span pool.
func (sp *SpanPool) Stats() Stats {
	return sp.pool.Stats()
}

// ResetStats resets the pool statistics.
func (sp *SpanPool) ResetStats() {
	sp.pool.ResetStats()
}

// HitRate returns the cache hit rate as a percentage.
func (sp *SpanPool) HitRate() float64 {
	return sp.pool.HitRate()
}

// AcquireAttributes gets an attribute map from the pool.
// Returns a map with capacity for MaxAttributes.
func (sp *SpanPool) AcquireAttributes() map[string]any {
	v := sp.attributePool.Get()
	if v == nil {
		return make(map[string]any, MaxAttributes)
	}
	m := v.(map[string]any)
	// Clear the map
	for k := range m {
		delete(m, k)
	}
	return m
}

// ReleaseAttributes returns an attribute map to the pool.
// Maps that are too large are discarded.
func (sp *SpanPool) ReleaseAttributes(m map[string]any) {
	if m == nil {
		return
	}

	// Only pool reasonably sized maps
	if len(m) <= MaxAttributes*2 {
		// Clear the map before returning
		for k := range m {
			delete(m, k)
		}
		sp.attributePool.Put(m)
	}
}

// AcquireEvents gets an event slice from the pool.
func (sp *SpanPool) AcquireEvents() []SpanEvent {
	v := sp.eventPool.Get()
	if v == nil {
		return make([]SpanEvent, 0, MaxEvents)
	}
	return v.([]SpanEvent)[:0]
}

// ReleaseEvents returns an event slice to the pool.
func (sp *SpanPool) ReleaseEvents(e []SpanEvent) {
	if e == nil {
		return
	}

	if cap(e) <= MaxEvents*2 {
		sp.eventPool.Put(e[:0])
	}
}

// AcquireLinks gets a link slice from the pool.
func (sp *SpanPool) AcquireLinks() []SpanLink {
	v := sp.linkPool.Get()
	if v == nil {
		return make([]SpanLink, 0, MaxLinks)
	}
	return v.([]SpanLink)[:0]
}

// ReleaseLinks returns a link slice to the pool.
func (sp *SpanPool) ReleaseLinks(l []SpanLink) {
	if l == nil {
		return
	}

	if cap(l) <= MaxLinks*2 {
		sp.linkPool.Put(l[:0])
	}
}

// defaultSpanPool is the package-level default span pool.
var defaultSpanPool = NewSpanPool(DefaultSpanPoolSize)

// GetSpan retrieves a span from the default pool.
func GetSpan() *Span {
	return defaultSpanPool.Get()
}

// PutSpan returns a span to the default pool.
func PutSpan(span *Span) {
	defaultSpanPool.Put(span)
}

// SpanPoolStats returns statistics for the default span pool.
func SpanPoolStats() Stats {
	return defaultSpanPool.Stats()
}

// ConcurrentSpanPool is a thread-safe pool optimized for concurrent access.
// It uses sharding to reduce contention in high-concurrency scenarios.
type ConcurrentSpanPool struct {
	shards    []*SpanPool
	shardMask uint32

	// stats aggregate stats from all shards (use uint32 for atomic operations)
	totalGets   uint32
	totalPuts   uint32
	totalHits   uint32
	totalMisses uint32
}

// NewConcurrentSpanPool creates a new ConcurrentSpanPool with the given number of shards.
// The number of shards should be a power of 2 for optimal performance.
//
// Example:
//
//	cp := pool.NewConcurrentSpanPool(16, 1000)
func NewConcurrentSpanPool(shards int, shardSize int32) *ConcurrentSpanPool {
	// Round up to power of 2
	if shards <= 0 {
		shards = 16
	}
	if (shards & (shards - 1)) != 0 {
		// Not a power of 2, round up
		shards = 1 << (32 - bitsLen(uint32(shards-1)))
	}

	csp := &ConcurrentSpanPool{
		shards:    make([]*SpanPool, shards),
		shardMask: uint32(shards - 1),
	}

	for i := range csp.shards {
		csp.shards[i] = NewSpanPool(shardSize)
	}

	return csp
}

// bitsLen returns the minimum number of bits required to represent x.
func bitsLen(x uint32) int {
	n := 0
	for x > 0 {
		x >>= 1
		n++
	}
	return n
}

// getShard returns the shard index for the current goroutine.
// Uses a simple hash of goroutine ID approximation via stack pointer.
func (csp *ConcurrentSpanPool) getShard() *SpanPool {
	// Use a simple counter for distribution
	// In production, this could use runtime.GoID() or similar
	idx := atomic.AddUint32(&csp.totalGets, 1) & csp.shardMask
	return csp.shards[idx]
}

// Get retrieves a span from the pool.
func (csp *ConcurrentSpanPool) Get() *Span {
	return csp.getShard().Get()
}

// Put returns a span to the pool.
func (csp *ConcurrentSpanPool) Put(span *Span) {
	csp.getShard().Put(span)
}

// Stats returns aggregated statistics from all shards.
func (csp *ConcurrentSpanPool) Stats() Stats {
	var total Stats
	for _, shard := range csp.shards {
		s := shard.Stats()
		total.Gets += s.Gets
		total.Puts += s.Puts
		total.Hits += s.Hits
		total.Misses += s.Misses
		total.Active += s.Active
		total.TotalCreates += s.TotalCreates
	}
	return total
}

// ResetStats resets statistics for all shards.
func (csp *ConcurrentSpanPool) ResetStats() {
	for _, shard := range csp.shards {
		shard.ResetStats()
	}
}

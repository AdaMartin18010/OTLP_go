// Package context provides context propagation utilities for the OTLP Go SDK.
package context

import (
	"context"
	"encoding/hex"
	"errors"
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

// W3C Trace Context constants.
const (
	// TraceParentHeader is the W3C traceparent header name.
	TraceParentHeader = "traceparent"
	// TraceStateHeader is the W3C tracestate header name.
	TraceStateHeader = "tracestate"
	// BaggageHeader is the W3C baggage header name.
	BaggageHeader = "baggage"

	// TraceParentVersion is the current traceparent version.
	TraceParentVersion = 0

	// TraceIDSize is the size of trace ID in bytes.
	TraceIDSize = 16
	// SpanIDSize is the size of span ID in bytes.
	SpanIDSize = 8
)

// Common errors.
var (
	ErrInvalidTraceParent = errors.New("invalid traceparent format")
	ErrInvalidTraceID     = errors.New("invalid trace ID")
	ErrInvalidSpanID      = errors.New("invalid span ID")
	ErrInvalidTraceFlags  = errors.New("invalid trace flags")
	ErrInvalidTraceState  = errors.New("invalid tracestate format")
)

// SpanContext represents the context of a span in a trace.
type SpanContext struct {
	TraceID    TraceID
	SpanID     SpanID
	TraceFlags TraceFlags
	TraceState TraceState
	Remote     bool
}

// TraceID is a 16-byte unique identifier for a trace.
type TraceID [16]byte

// IsValid returns true if the TraceID is valid (non-zero).
func (t TraceID) IsValid() bool {
	return t != [16]byte{}
}

// String returns the hex string representation of the TraceID.
func (t TraceID) String() string {
	return hex.EncodeToString(t[:])
}

// MarshalText implements encoding.TextMarshaler.
func (t TraceID) MarshalText() ([]byte, error) {
	return []byte(t.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (t *TraceID) UnmarshalText(data []byte) error {
	if len(data) != 32 {
		return ErrInvalidTraceID
	}
	_, err := hex.Decode(t[:], data)
	return err
}

// SpanID is an 8-byte unique identifier for a span.
type SpanID [8]byte

// IsValid returns true if the SpanID is valid (non-zero).
func (s SpanID) IsValid() bool {
	return s != [8]byte{}
}

// String returns the hex string representation of the SpanID.
func (s SpanID) String() string {
	return hex.EncodeToString(s[:])
}

// MarshalText implements encoding.TextMarshaler.
func (s SpanID) MarshalText() ([]byte, error) {
	return []byte(s.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (s *SpanID) UnmarshalText(data []byte) error {
	if len(data) != 16 {
		return ErrInvalidSpanID
	}
	_, err := hex.Decode(s[:], data)
	return err
}

// TraceFlags represents trace flags as defined in W3C Trace Context.
type TraceFlags byte

// Flags for TraceFlags.
const (
	// FlagSampled indicates the trace is sampled.
	FlagSampled TraceFlags = 1 << 0
	// FlagRandom indicates the trace ID was randomly generated.
	FlagRandom TraceFlags = 1 << 1
)

// IsSampled returns true if the sampled flag is set.
func (f TraceFlags) IsSampled() bool {
	return f&FlagSampled != 0
}

// WithSampled returns a new Flags with the sampled flag set or cleared.
func (f TraceFlags) WithSampled(sampled bool) TraceFlags {
	if sampled {
		return f | FlagSampled
	}
	return f & ^FlagSampled
}

// String returns the hex string representation of the flags.
func (f TraceFlags) String() string {
	return hex.EncodeToString([]byte{byte(f)})
}

// ParseTraceFlags parses a hex string into TraceFlags.
func ParseTraceFlags(s string) (TraceFlags, error) {
	if len(s) != 2 {
		return 0, ErrInvalidTraceFlags
	}
	b, err := hex.DecodeString(s)
	if err != nil {
		return 0, err
	}
	return TraceFlags(b[0]), nil
}

// TraceState is a vendor-specific data for tracing systems.
type TraceState struct {
	entries map[string]string
}

// NewTraceState creates a new empty TraceState.
func NewTraceState() TraceState {
	return TraceState{entries: make(map[string]string)}
}

// Get returns the value for a given key.
func (ts TraceState) Get(key string) (string, bool) {
	if ts.entries == nil {
		return "", false
	}
	val, ok := ts.entries[key]
	return val, ok
}

// Set sets the value for a given key.
func (ts *TraceState) Set(key, value string) error {
	if err := validateTraceStateKey(key); err != nil {
		return err
	}
	if err := validateTraceStateValue(value); err != nil {
		return err
	}
	if ts.entries == nil {
		ts.entries = make(map[string]string)
	}
	ts.entries[key] = value
	return nil
}

// Delete removes a key from tracestate.
func (ts *TraceState) Delete(key string) {
	if ts.entries != nil {
		delete(ts.entries, key)
	}
}

// Len returns the number of entries.
func (ts TraceState) Len() int {
	if ts.entries == nil {
		return 0
	}
	return len(ts.entries)
}

// IsEmpty returns true if tracestate has no entries.
func (ts TraceState) IsEmpty() bool {
	return ts.Len() == 0
}

// String returns the W3C tracestate string representation.
func (ts TraceState) String() string {
	if ts.entries == nil {
		return ""
	}
	var parts []string
	for k, v := range ts.entries {
		parts = append(parts, fmt.Sprintf("%s=%s", k, v))
	}
	return strings.Join(parts, ",")
}

// ParseTraceState parses a W3C tracestate header value.
func ParseTraceState(s string) (TraceState, error) {
	ts := NewTraceState()
	if s == "" {
		return ts, nil
	}

	pairs := strings.Split(s, ",")
	if len(pairs) > 32 {
		return ts, ErrInvalidTraceState
	}

	for _, pair := range pairs {
		pair = strings.TrimSpace(pair)
		if pair == "" {
			continue
		}
		parts := strings.SplitN(pair, "=", 2)
		if len(parts) != 2 {
			continue // Skip invalid entries
		}
		key := strings.TrimSpace(parts[0])
		value := strings.TrimSpace(parts[1])
		ts.entries[key] = value
	}

	return ts, nil
}

// validateTraceStateKey validates a tracestate key.
func validateTraceStateKey(key string) error {
	if key == "" {
		return errors.New("tracestate key cannot be empty")
	}
	if len(key) > 256 {
		return errors.New("tracestate key too long")
	}
	return nil
}

// validateTraceStateValue validates a tracestate value.
func validateTraceStateValue(value string) error {
	if len(value) > 256 {
		return errors.New("tracestate value too long")
	}
	return nil
}

// IsValid returns true if the span context is valid.
func (sc SpanContext) IsValid() bool {
	return sc.TraceID.IsValid() && sc.SpanID.IsValid()
}

// IsRemote indicates if the span context was propagated from a remote parent.
func (sc SpanContext) IsRemote() bool {
	return sc.Remote
}

// WithRemote returns a new SpanContext with the Remote field set.
func (sc SpanContext) WithRemote(remote bool) SpanContext {
	sc.Remote = remote
	return sc
}

// spanContextKey is the key for storing SpanContext in context.
type spanContextKey struct{}

// WithSpanContext attaches a SpanContext to the context.
func WithSpanContext(ctx context.Context, sc SpanContext) context.Context {
	return context.WithValue(ctx, spanContextKey{}, sc)
}

// SpanContextFromContext extracts SpanContext from context.
func SpanContextFromContext(ctx context.Context) SpanContext {
	if ctx == nil {
		return SpanContext{}
	}
	if sc, ok := ctx.Value(spanContextKey{}).(SpanContext); ok {
		return sc
	}
	return SpanContext{}
}

// ContextWithRemoteSpanContext attaches a remote SpanContext to context.
func ContextWithRemoteSpanContext(ctx context.Context, sc SpanContext) context.Context {
	sc.Remote = true
	return WithSpanContext(ctx, sc)
}

// TraceContextPropagator implements W3C Trace Context propagation.
type TraceContextPropagator struct{}

// NewTraceContextPropagator creates a new W3C Trace Context propagator.
func NewTraceContextPropagator() *TraceContextPropagator {
	return &TraceContextPropagator{}
}

// traceparentRegex matches valid traceparent format.
var traceparentRegex = regexp.MustCompile(
	`^[0-9a-f]{2}-[0-9a-f]{32}-[0-9a-f]{16}-[0-9a-f]{2}$`)

// Inject injects span context into the carrier.
func (p *TraceContextPropagator) Inject(ctx context.Context, carrier Carrier) {
	sc := SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	// Format: version-traceid-parentid-flags
	traceparent := fmt.Sprintf("%02x-%s-%s-%s",
		TraceParentVersion,
		sc.TraceID.String(),
		sc.SpanID.String(),
		sc.TraceFlags.String(),
	)
	carrier.Set(TraceParentHeader, traceparent)

	// Inject tracestate if present
	if !sc.TraceState.IsEmpty() {
		carrier.Set(TraceStateHeader, sc.TraceState.String())
	}
}

// Extract extracts span context from the carrier.
func (p *TraceContextPropagator) Extract(ctx context.Context, carrier Carrier) context.Context {
	traceparent := carrier.Get(TraceParentHeader)
	if traceparent == "" {
		return ctx
	}

	sc, err := ParseTraceParent(traceparent)
	if err != nil {
		return ctx
	}

	// Extract tracestate if present
	tracestate := carrier.Get(TraceStateHeader)
	if tracestate != "" {
		ts, err := ParseTraceState(tracestate)
		if err == nil {
			sc.TraceState = ts
		}
	}

	return ContextWithRemoteSpanContext(ctx, sc)
}

// Fields returns the fields used by this propagator.
func (p *TraceContextPropagator) Fields() []string {
	return []string{TraceParentHeader, TraceStateHeader}
}

// ParseTraceParent parses a traceparent header value.
func ParseTraceParent(s string) (SpanContext, error) {
	var sc SpanContext

	if !traceparentRegex.MatchString(s) {
		return sc, ErrInvalidTraceParent
	}

	parts := strings.Split(s, "-")
	if len(parts) != 4 {
		return sc, ErrInvalidTraceParent
	}

	// Parse version
	version, err := strconv.ParseInt(parts[0], 16, 8)
	if err != nil {
		return sc, ErrInvalidTraceParent
	}
	if version == 0xff {
		return sc, ErrInvalidTraceParent
	}

	// Parse trace ID
	if err := sc.TraceID.UnmarshalText([]byte(parts[1])); err != nil {
		return sc, ErrInvalidTraceID
	}
	if !sc.TraceID.IsValid() {
		return sc, ErrInvalidTraceID
	}

	// Parse span ID
	if err := sc.SpanID.UnmarshalText([]byte(parts[2])); err != nil {
		return sc, ErrInvalidSpanID
	}
	if !sc.SpanID.IsValid() {
		return sc, ErrInvalidSpanID
	}

	// Parse trace flags
	flags, err := ParseTraceFlags(parts[3])
	if err != nil {
		return sc, ErrInvalidTraceFlags
	}
	sc.TraceFlags = flags

	return sc, nil
}

// B3Propagator implements B3 (Zipkin) propagation format.
type B3Propagator struct {
	// SingleHeader indicates whether to use single header format.
	SingleHeader bool
	// InjectEncoding specifies the encoding to use for injection.
	InjectEncoding B3Encoding
}

// B3Encoding represents the B3 encoding type.
type B3Encoding int

const (
	// B3MultipleHeader uses multiple headers (x-b3-*).
	B3MultipleHeader B3Encoding = iota
	// B3SingleHeader uses single b3 header.
	B3SingleHeader
)

// B3 header names.
const (
	B3TraceIDHeader      = "x-b3-traceid"
	B3SpanIDHeader       = "x-b3-spanid"
	B3ParentSpanIDHeader = "x-b3-parentspanid"
	B3SampledHeader      = "x-b3-sampled"
	B3FlagsHeader        = "x-b3-flags"
	B3SingleHeaderName   = "b3"
)

// NewB3Propagator creates a new B3 propagator.
func NewB3Propagator() *B3Propagator {
	return &B3Propagator{
		SingleHeader:   false,
		InjectEncoding: B3MultipleHeader,
	}
}

// NewB3SingleHeaderPropagator creates a B3 propagator using single header format.
func NewB3SingleHeaderPropagator() *B3Propagator {
	return &B3Propagator{
		SingleHeader:   true,
		InjectEncoding: B3SingleHeader,
	}
}

// Inject injects span context into the carrier.
func (p *B3Propagator) Inject(ctx context.Context, carrier Carrier) {
	sc := SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	if p.InjectEncoding == B3SingleHeader {
		// Single header format: traceId-spanId-sampled-parentSpanId
		sampled := "0"
		if sc.TraceFlags.IsSampled() {
			sampled = "1"
		}
		value := fmt.Sprintf("%s-%s-%s", sc.TraceID.String(), sc.SpanID.String(), sampled)
		carrier.Set(B3SingleHeaderName, value)
	} else {
		// Multiple headers
		carrier.Set(B3TraceIDHeader, sc.TraceID.String())
		carrier.Set(B3SpanIDHeader, sc.SpanID.String())
		if sc.TraceFlags.IsSampled() {
			carrier.Set(B3SampledHeader, "1")
		} else {
			carrier.Set(B3SampledHeader, "0")
		}
	}
}

// Extract extracts span context from the carrier.
func (p *B3Propagator) Extract(ctx context.Context, carrier Carrier) context.Context {
	var sc SpanContext

	if p.SingleHeader {
		// Try single header first
		single := carrier.Get(B3SingleHeaderName)
		if single != "" {
			sc = p.parseSingleHeader(single)
		}
	} else {
		// Try multiple headers
		sc = p.parseMultipleHeaders(carrier)
	}

	if sc.IsValid() {
		return ContextWithRemoteSpanContext(ctx, sc)
	}
	return ctx
}

// Fields returns the fields used by this propagator.
func (p *B3Propagator) Fields() []string {
	if p.SingleHeader {
		return []string{B3SingleHeaderName}
	}
	return []string{B3TraceIDHeader, B3SpanIDHeader, B3ParentSpanIDHeader, B3SampledHeader, B3FlagsHeader}
}

func (p *B3Propagator) parseMultipleHeaders(carrier Carrier) SpanContext {
	var sc SpanContext

	traceIDStr := carrier.Get(B3TraceIDHeader)
	if traceIDStr == "" {
		return sc
	}

	// B3 trace ID can be 16 or 32 hex chars, pad if needed
	if len(traceIDStr) == 16 {
		traceIDStr = "0000000000000000" + traceIDStr
	}
	if err := sc.TraceID.UnmarshalText([]byte(traceIDStr)); err != nil {
		return SpanContext{}
	}

	spanIDStr := carrier.Get(B3SpanIDHeader)
	if spanIDStr == "" {
		return SpanContext{}
	}
	if err := sc.SpanID.UnmarshalText([]byte(spanIDStr)); err != nil {
		return SpanContext{}
	}

	sampled := carrier.Get(B3SampledHeader)
	if sampled == "1" || sampled == "true" || sampled == "d" {
		sc.TraceFlags = FlagSampled
	}

	return sc
}

func (p *B3Propagator) parseSingleHeader(value string) SpanContext {
	var sc SpanContext

	parts := strings.Split(value, "-")
	if len(parts) < 2 {
		return sc
	}

	traceIDStr := parts[0]
	if len(traceIDStr) == 16 {
		traceIDStr = "0000000000000000" + traceIDStr
	}
	if err := sc.TraceID.UnmarshalText([]byte(traceIDStr)); err != nil {
		return SpanContext{}
	}

	if err := sc.SpanID.UnmarshalText([]byte(parts[1])); err != nil {
		return SpanContext{}
	}

	if len(parts) >= 3 {
		sampled := parts[2]
		if sampled == "1" || sampled == "d" {
			sc.TraceFlags = FlagSampled
		}
	}

	return sc
}

// JaegerPropagator implements Jaeger propagation format.
type JaegerPropagator struct{}

// Jaeger header name.
const (
	JaegerHeader = "uber-trace-id"
)

// NewJaegerPropagator creates a new Jaeger propagator.
func NewJaegerPropagator() *JaegerPropagator {
	return &JaegerPropagator{}
}

// Inject injects span context into the carrier.
func (p *JaegerPropagator) Inject(ctx context.Context, carrier Carrier) {
	sc := SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	// Format: {trace-id}:{span-id}:{parent-span-id}:{flags}
	// Jaeger uses 64-bit trace IDs, so we use the lower 64 bits
	traceID64 := hex.EncodeToString(sc.TraceID[8:])
	spanID := sc.SpanID.String()
	flags := 0
	if sc.TraceFlags.IsSampled() {
		flags = 1
	}

	value := fmt.Sprintf("%s:%s:0:%d", traceID64, spanID, flags)
	carrier.Set(JaegerHeader, value)
}

// Extract extracts span context from the carrier.
func (p *JaegerPropagator) Extract(ctx context.Context, carrier Carrier) context.Context {
	header := carrier.Get(JaegerHeader)
	if header == "" {
		return ctx
	}

	sc := p.parseHeader(header)
	if sc.IsValid() {
		return ContextWithRemoteSpanContext(ctx, sc)
	}
	return ctx
}

// Fields returns the fields used by this propagator.
func (p *JaegerPropagator) Fields() []string {
	return []string{JaegerHeader}
}

func (p *JaegerPropagator) parseHeader(header string) SpanContext {
	var sc SpanContext

	parts := strings.Split(header, ":")
	if len(parts) < 4 {
		return sc
	}

	// Parse 64-bit trace ID and pad to 128-bit
	traceID64 := parts[0]
	if len(traceID64) == 16 {
		traceIDStr := "0000000000000000" + traceID64
		if err := sc.TraceID.UnmarshalText([]byte(traceIDStr)); err != nil {
			return SpanContext{}
		}
	}

	if err := sc.SpanID.UnmarshalText([]byte(parts[1])); err != nil {
		return SpanContext{}
	}

	// Parse flags
	flags, _ := strconv.Atoi(parts[3])
	if flags&1 == 1 {
		sc.TraceFlags = FlagSampled
	}

	return sc
}

// PropagatorRegistry holds registered propagators.
type PropagatorRegistry struct {
	propagators map[string]Propagator
}

// NewPropagatorRegistry creates a new propagator registry.
func NewPropagatorRegistry() *PropagatorRegistry {
	return &PropagatorRegistry{
		propagators: make(map[string]Propagator),
	}
}

// Register registers a propagator with the given name.
func (r *PropagatorRegistry) Register(name string, p Propagator) {
	r.propagators[name] = p
}

// Get retrieves a propagator by name.
func (r *PropagatorRegistry) Get(name string) (Propagator, bool) {
	p, ok := r.propagators[name]
	return p, ok
}

// Unregister removes a propagator.
func (r *PropagatorRegistry) Unregister(name string) {
	delete(r.propagators, name)
}

// Names returns all registered propagator names.
func (r *PropagatorRegistry) Names() []string {
	names := make([]string, 0, len(r.propagators))
	for name := range r.propagators {
		names = append(names, name)
	}
	return names
}

// GetPropagator returns a propagator by name from the default registry.
func GetPropagator(name string) (Propagator, bool) {
	return defaultRegistry.Get(name)
}

var defaultRegistry = NewPropagatorRegistry()

func init() {
	// Register default propagators
	defaultRegistry.Register("tracecontext", NewTraceContextPropagator())
	defaultRegistry.Register("b3", NewB3Propagator())
	defaultRegistry.Register("b3single", NewB3SingleHeaderPropagator())
	defaultRegistry.Register("jaeger", NewJaegerPropagator())
}

// ExtractTextMap extracts span context from a TextMapCarrier.
func ExtractTextMap(carrier TextMapCarrier) SpanContext {
	propagator := NewTraceContextPropagator()
	ctx := propagator.Extract(context.Background(), carrier)
	return SpanContextFromContext(ctx)
}

// InjectTextMap injects span context into a TextMapCarrier.
func InjectTextMap(sc SpanContext, carrier TextMapCarrier) {
	ctx := WithSpanContext(context.Background(), sc)
	propagator := NewTraceContextPropagator()
	propagator.Inject(ctx, carrier)
}

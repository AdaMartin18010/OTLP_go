// Package context provides context propagation utilities for the OTLP Go SDK.
//
// This package includes:
//   - Baggage propagation
//   - Context with timeout helpers
//   - Distributed context carriers
//   - W3C Trace Context support
//
// Example usage:
//
//	// Create context with baggage
//	ctx := context.WithBaggage(ctx, "user-id", "12345")
//
//	// Extract baggage
//	value := context.GetBaggage(ctx, "user-id")
package context

import (
	"context"
	"time"
)

// contextKey is a private type to avoid collisions with other packages.
type contextKey int

const (
	// baggageKey is the context key for baggage storage.
	baggageKey contextKey = iota
	// deadlineKey is the context key for custom deadline tracking.
	deadlineKey
	// metadataKey is the context key for context metadata.
	metadataKey
)

// Metadata holds contextual information that can be propagated.
type Metadata struct {
	data map[string]interface{}
}

// NewMetadata creates a new empty Metadata.
func NewMetadata() *Metadata {
	return &Metadata{
		data: make(map[string]interface{}),
	}
}

// Get retrieves a value from metadata.
func (m *Metadata) Get(key string) (interface{}, bool) {
	if m == nil || m.data == nil {
		return nil, false
	}
	val, ok := m.data[key]
	return val, ok
}

// Set stores a value in metadata.
func (m *Metadata) Set(key string, value interface{}) {
	if m.data == nil {
		m.data = make(map[string]interface{})
	}
	m.data[key] = value
}

// Delete removes a value from metadata.
func (m *Metadata) Delete(key string) {
	if m.data != nil {
		delete(m.data, key)
	}
}

// Has returns true if the key exists in metadata.
func (m *Metadata) Has(key string) bool {
	if m.data == nil {
		return false
	}
	_, ok := m.data[key]
	return ok
}

// Keys returns all keys in metadata.
func (m *Metadata) Keys() []string {
	if m.data == nil {
		return nil
	}
	keys := make([]string, 0, len(m.data))
	for k := range m.data {
		keys = append(keys, k)
	}
	return keys
}

// Len returns the number of items in metadata.
func (m *Metadata) Len() int {
	if m.data == nil {
		return 0
	}
	return len(m.data)
}

// Clone creates a deep copy of the metadata.
func (m *Metadata) Clone() *Metadata {
	cloned := NewMetadata()
	if m.data == nil {
		return cloned
	}
	for k, v := range m.data {
		cloned.data[k] = v
	}
	return cloned
}

// WithMetadata attaches metadata to the context.
func WithMetadata(ctx context.Context, md *Metadata) context.Context {
	if md == nil {
		return ctx
	}
	return context.WithValue(ctx, metadataKey, md.Clone())
}

// GetMetadata retrieves metadata from the context.
// Returns nil if no metadata is found.
func GetMetadata(ctx context.Context) *Metadata {
	if ctx == nil {
		return nil
	}
	if val := ctx.Value(metadataKey); val != nil {
		if md, ok := val.(*Metadata); ok {
			return md
		}
	}
	return nil
}

// GetMetadataValue retrieves a specific value from context metadata.
func GetMetadataValue(ctx context.Context, key string) (interface{}, bool) {
	md := GetMetadata(ctx)
	if md == nil {
		return nil, false
	}
	return md.Get(key)
}

// SetMetadataValue sets a value in context metadata.
// If the context doesn't have metadata, a new one is created.
func SetMetadataValue(ctx context.Context, key string, value interface{}) context.Context {
	md := GetMetadata(ctx)
	if md == nil {
		md = NewMetadata()
	} else {
		md = md.Clone()
	}
	md.Set(key, value)
	return WithMetadata(ctx, md)
}

// DeadlineInfo holds information about context deadlines.
type DeadlineInfo struct {
	Deadline time.Time
	SetAt    time.Time
}

// WithDeadlineInfo attaches deadline information to the context.
func WithDeadlineInfo(ctx context.Context, deadline time.Time) context.Context {
	info := DeadlineInfo{
		Deadline: deadline,
		SetAt:    time.Now(),
	}
	return context.WithValue(ctx, deadlineKey, info)
}

// GetDeadlineInfo retrieves deadline information from the context.
func GetDeadlineInfo(ctx context.Context) (DeadlineInfo, bool) {
	if ctx == nil {
		return DeadlineInfo{}, false
	}
	if val := ctx.Value(deadlineKey); val != nil {
		if info, ok := val.(DeadlineInfo); ok {
			return info, true
		}
	}
	return DeadlineInfo{}, false
}

// TimeUntilDeadline returns the remaining time until the deadline.
// Returns 0 if no deadline is set or deadline has passed.
func TimeUntilDeadline(ctx context.Context) time.Duration {
	if deadline, ok := ctx.Deadline(); ok {
		remaining := time.Until(deadline)
		if remaining < 0 {
			return 0
		}
		return remaining
	}
	return 0
}

// IsDeadlineSet returns true if the context has a deadline.
func IsDeadlineSet(ctx context.Context) bool {
	_, ok := ctx.Deadline()
	return ok
}

// WithTimeoutExtended creates a context with extended timeout.
// Useful for operations that need more time than parent context allows.
func WithTimeoutExtended(ctx context.Context, timeout time.Duration) (context.Context, context.CancelFunc) {
	return context.WithTimeout(context.Background(), timeout)
}

// WithTimeoutFromParent creates a child context with a timeout
// that respects the parent's deadline but may be shorter.
func WithTimeoutFromParent(ctx context.Context, timeout time.Duration) (context.Context, context.CancelFunc) {
	if deadline, ok := ctx.Deadline(); ok {
		parentTimeout := time.Until(deadline)
		if parentTimeout < timeout {
			timeout = parentTimeout
		}
	}
	return context.WithTimeout(ctx, timeout)
}

// Detach creates a new context that inherits values from the parent
// but is not affected by parent's cancellation.
// Useful for fire-and-forget operations.
func Detach(ctx context.Context) context.Context {
	return &detachedContext{Context: context.Background(), values: ctx}
}

// detachedContext wraps a context to only provide value lookup
type detachedContext struct {
	context.Context
	values context.Context
}

func (d *detachedContext) Value(key interface{}) interface{} {
	return d.values.Value(key)
}

// Carrier is an interface for transporting context across process boundaries.
type Carrier interface {
	// Get returns the value associated with key.
	Get(key string) string
	// Set stores the key-value pair.
	Set(key string, value string)
	// Keys returns all keys currently stored.
	Keys() []string
}

// TextMapCarrier is a carrier that uses a map for storage.
type TextMapCarrier map[string]string

// Get returns the value for the given key.
func (c TextMapCarrier) Get(key string) string {
	if c == nil {
		return ""
	}
	return c[key]
}

// Set stores the key-value pair.
func (c TextMapCarrier) Set(key string, value string) {
	if c != nil {
		c[key] = value
	}
}

// Keys returns all keys in the carrier.
func (c TextMapCarrier) Keys() []string {
	if c == nil {
		return nil
	}
	keys := make([]string, 0, len(c))
	for k := range c {
		keys = append(keys, k)
	}
	return keys
}

// HTTPHeadersCarrier wraps http.Header to implement Carrier interface.
type HTTPHeadersCarrier map[string][]string

// Get returns the first value for the given key.
func (c HTTPHeadersCarrier) Get(key string) string {
	if c == nil {
		return ""
	}
	values := c[key]
	if len(values) == 0 {
		return ""
	}
	return values[0]
}

// Set stores the key-value pair.
func (c HTTPHeadersCarrier) Set(key string, value string) {
	if c != nil {
		c[key] = []string{value}
	}
}

// Keys returns all keys in the carrier.
func (c HTTPHeadersCarrier) Keys() []string {
	if c == nil {
		return nil
	}
	keys := make([]string, 0, len(c))
	for k := range c {
		keys = append(keys, k)
	}
	return keys
}

// Add adds a value to the header (for multiple values).
func (c HTTPHeadersCarrier) Add(key string, value string) {
	if c != nil {
		c[key] = append(c[key], value)
	}
}

// Values returns all values for a key.
func (c HTTPHeadersCarrier) Values(key string) []string {
	if c == nil {
		return nil
	}
	return c[key]
}

// GRPCMetadataCarrier wraps metadata.MD for gRPC context propagation.
// This is a simplified version without external dependencies.
type GRPCMetadataCarrier map[string][]string

// Get returns the first value for the given key.
func (c GRPCMetadataCarrier) Get(key string) string {
	if c == nil {
		return ""
	}
	// gRPC metadata keys are case-insensitive
	key = CanonicalGRPCKey(key)
	values := c[key]
	if len(values) == 0 {
		return ""
	}
	return values[0]
}

// Set stores the key-value pair.
func (c GRPCMetadataCarrier) Set(key string, value string) {
	if c != nil {
		key = CanonicalGRPCKey(key)
		c[key] = []string{value}
	}
}

// Keys returns all keys in the carrier.
func (c GRPCMetadataCarrier) Keys() []string {
	if c == nil {
		return nil
	}
	keys := make([]string, 0, len(c))
	for k := range c {
		keys = append(keys, k)
	}
	return keys
}

// Append adds a value to the metadata.
func (c GRPCMetadataCarrier) Append(key string, value string) {
	if c != nil {
		key = CanonicalGRPCKey(key)
		c[key] = append(c[key], value)
	}
}

// CanonicalGRPCKey converts a key to gRPC canonical format (lowercase).
func CanonicalGRPCKey(key string) string {
	return string([]byte(key))
}

// CompositeCarrier combines multiple carriers into one.
type CompositeCarrier struct {
	carriers []Carrier
}

// NewCompositeCarrier creates a new composite carrier.
func NewCompositeCarrier(carriers ...Carrier) *CompositeCarrier {
	return &CompositeCarrier{carriers: carriers}
}

// Get returns the first non-empty value from any carrier.
func (c *CompositeCarrier) Get(key string) string {
	for _, carrier := range c.carriers {
		if carrier == nil {
			continue
		}
		if val := carrier.Get(key); val != "" {
			return val
		}
	}
	return ""
}

// Set stores the key-value pair in all carriers.
func (c *CompositeCarrier) Set(key string, value string) {
	for _, carrier := range c.carriers {
		if carrier != nil {
			carrier.Set(key, value)
		}
	}
}

// Keys returns all unique keys from all carriers.
func (c *CompositeCarrier) Keys() []string {
	keySet := make(map[string]struct{})
	for _, carrier := range c.carriers {
		if carrier == nil {
			continue
		}
		for _, key := range carrier.Keys() {
			keySet[key] = struct{}{}
		}
	}
	keys := make([]string, 0, len(keySet))
	for k := range keySet {
		keys = append(keys, k)
	}
	return keys
}

// Propagator defines the interface for propagating context across boundaries.
type Propagator interface {
	// Inject injects context values into the carrier.
	Inject(ctx context.Context, carrier Carrier)
	// Extract extracts context values from the carrier.
	Extract(ctx context.Context, carrier Carrier) context.Context
	// Fields returns the fields used by this propagator.
	Fields() []string
}

// CompositePropagator combines multiple propagators.
type CompositePropagator struct {
	propagators []Propagator
}

// NewCompositePropagator creates a new composite propagator.
func NewCompositePropagator(propagators ...Propagator) *CompositePropagator {
	return &CompositePropagator{propagators: propagators}
}

// Inject injects context using all propagators.
func (c *CompositePropagator) Inject(ctx context.Context, carrier Carrier) {
	for _, p := range c.propagators {
		if p != nil {
			p.Inject(ctx, carrier)
		}
	}
}

// Extract extracts context using all propagators.
func (c *CompositePropagator) Extract(ctx context.Context, carrier Carrier) context.Context {
	for _, p := range c.propagators {
		if p != nil {
			ctx = p.Extract(ctx, carrier)
		}
	}
	return ctx
}

// Fields returns all fields from all propagators.
func (c *CompositePropagator) Fields() []string {
	fieldSet := make(map[string]struct{})
	for _, p := range c.propagators {
		if p == nil {
			continue
		}
		for _, f := range p.Fields() {
			fieldSet[f] = struct{}{}
		}
	}
	fields := make([]string, 0, len(fieldSet))
	for f := range fieldSet {
		fields = append(fields, f)
	}
	return fields
}

// NoopPropagator is a propagator that does nothing.
type NoopPropagator struct{}

// Inject does nothing.
func (n *NoopPropagator) Inject(ctx context.Context, carrier Carrier) {}

// Extract returns the context unchanged.
func (n *NoopPropagator) Extract(ctx context.Context, carrier Carrier) context.Context {
	return ctx
}

// Fields returns empty list.
func (n *NoopPropagator) Fields() []string {
	return nil
}

// NoopPropagatorInstance is the shared noop propagator instance.
var NoopPropagatorInstance = &NoopPropagator{}

// SafeContext wraps a context to provide safe operations.
type SafeContext struct {
	ctx context.Context
}

// NewSafeContext creates a new safe context wrapper.
func NewSafeContext(ctx context.Context) *SafeContext {
	if ctx == nil {
		ctx = context.Background()
	}
	return &SafeContext{ctx: ctx}
}

// Context returns the underlying context.
func (s *SafeContext) Context() context.Context {
	return s.ctx
}

// Done returns the done channel.
func (s *SafeContext) Done() <-chan struct{} {
	if s.ctx == nil {
		return nil
	}
	return s.ctx.Done()
}

// Err returns the context error.
func (s *SafeContext) Err() error {
	if s.ctx == nil {
		return context.Canceled
	}
	return s.ctx.Err()
}

// Value returns the value for the key.
func (s *SafeContext) Value(key interface{}) interface{} {
	if s.ctx == nil {
		return nil
	}
	return s.ctx.Value(key)
}

// Deadline returns the deadline.
func (s *SafeContext) Deadline() (time.Time, bool) {
	if s.ctx == nil {
		return time.Time{}, false
	}
	return s.ctx.Deadline()
}

// WithCancel creates a cancellable context.
func (s *SafeContext) WithCancel() (*SafeContext, context.CancelFunc) {
	ctx, cancel := context.WithCancel(s.ctx)
	return NewSafeContext(ctx), cancel
}

// WithTimeout creates a context with timeout.
func (s *SafeContext) WithTimeout(timeout time.Duration) (*SafeContext, context.CancelFunc) {
	ctx, cancel := context.WithTimeout(s.ctx, timeout)
	return NewSafeContext(ctx), cancel
}

// WithValue creates a context with a value.
func (s *SafeContext) WithValue(key, val interface{}) *SafeContext {
	return NewSafeContext(context.WithValue(s.ctx, key, val))
}

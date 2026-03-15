// Package context provides context propagation utilities for the OTLP Go SDK.
package context

import (
	"context"
	"encoding/base64"
	"errors"
	"fmt"
	"net/url"
	"regexp"
	"sort"
	"strings"
	"sync"
)

// Baggage is a collection of key-value pairs that can be propagated across process boundaries.
// Baggage values are immutable once created.
type Baggage struct {
	entries map[string]BaggageItem
}

// BaggageItem represents a single baggage entry with metadata.
type BaggageItem struct {
	// Value is the baggage value.
	Value string
	// Metadata contains optional metadata for the item.
	Metadata BaggageItemMetadata
}

// BaggageItemMetadata holds optional metadata for a baggage item.
type BaggageItemMetadata struct {
	// Properties are optional key-value pairs.
	Properties map[string]string
}

// baggageContextKey is the key for storing baggage in context.
type baggageContextKey struct{}

var (
	// ErrInvalidKey is returned when a baggage key is invalid.
	ErrInvalidKey = errors.New("invalid baggage key")
	// ErrInvalidValue is returned when a baggage value is invalid.
	ErrInvalidValue = errors.New("invalid baggage value")
	// ErrTooManyEntries is returned when baggage exceeds maximum entries.
	ErrTooManyEntries = errors.New("too many baggage entries")
	// ErrKeyNotFound is returned when a key is not found in baggage.
	ErrKeyNotFound = errors.New("baggage key not found")
)

// Baggage limits as per W3C spec.
const (
	// MaxBaggageEntries is the maximum number of baggage entries.
	MaxBaggageEntries = 180
	// MaxBaggageKeyLength is the maximum length of a baggage key.
	MaxBaggageKeyLength = 256
	// MaxBaggageValueLength is the maximum length of a baggage value.
	MaxBaggageValueLength = 8192
)

// validKeyRegex matches valid baggage keys.
// Key must start with a letter and contain only alphanumeric characters and special chars.
var validKeyRegex = regexp.MustCompile(`^[a-zA-Z][a-zA-Z0-9!#$%&'*+-.^_|~\-]*$`)

// NewBaggage creates a new empty Baggage.
func NewBaggage() Baggage {
	return Baggage{
		entries: make(map[string]BaggageItem),
	}
}

// BaggageFromContext extracts baggage from the context.
// Returns empty baggage if none is found.
func BaggageFromContext(ctx context.Context) Baggage {
	if ctx == nil {
		return NewBaggage()
	}
	if val := ctx.Value(baggageContextKey{}); val != nil {
		if b, ok := val.(Baggage); ok {
			return b
		}
	}
	return NewBaggage()
}

// ContextWithBaggage attaches baggage to the context.
func ContextWithBaggage(ctx context.Context, baggage Baggage) context.Context {
	if ctx == nil {
		ctx = context.Background()
	}
	return context.WithValue(ctx, baggageContextKey{}, baggage)
}

// WithBaggage attaches a single baggage entry to the context.
// This is a convenience function for simple use cases.
func WithBaggage(ctx context.Context, key, value string) context.Context {
	if ctx == nil {
		ctx = context.Background()
	}
	baggage := BaggageFromContext(ctx)
	newBaggage, err := baggage.Set(key, value)
	if err != nil {
		// If we can't set the baggage, return the original context
		return ctx
	}
	return ContextWithBaggage(ctx, newBaggage)
}

// WithBaggageItem attaches a baggage item with metadata to the context.
func WithBaggageItem(ctx context.Context, key, value string, metadata BaggageItemMetadata) context.Context {
	if ctx == nil {
		ctx = context.Background()
	}
	baggage := BaggageFromContext(ctx)
	newBaggage, err := baggage.SetWithMetadata(key, value, metadata)
	if err != nil {
		return ctx
	}
	return ContextWithBaggage(ctx, newBaggage)
}

// GetBaggage retrieves a baggage value from the context.
// Returns empty string if key is not found.
func GetBaggage(ctx context.Context, key string) string {
	baggage := BaggageFromContext(ctx)
	item, ok := baggage.Get(key)
	if !ok {
		return ""
	}
	return item.Value
}

// GetBaggageItem retrieves a baggage item from the context.
func GetBaggageItem(ctx context.Context, key string) (BaggageItem, bool) {
	baggage := BaggageFromContext(ctx)
	return baggage.Get(key)
}

// DeleteBaggage removes a baggage entry from the context.
func DeleteBaggage(ctx context.Context, key string) context.Context {
	if ctx == nil {
		return ctx
	}
	baggage := BaggageFromContext(ctx)
	newBaggage := baggage.Delete(key)
	return ContextWithBaggage(ctx, newBaggage)
}

// ClearBaggage removes all baggage from the context.
func ClearBaggage(ctx context.Context) context.Context {
	if ctx == nil {
		return ctx
	}
	return ContextWithBaggage(ctx, NewBaggage())
}

// HasBaggage returns true if the context has any baggage.
func HasBaggage(ctx context.Context) bool {
	if ctx == nil {
		return false
	}
	return BaggageFromContext(ctx).Len() > 0
}

// BaggageKeys returns all baggage keys from the context.
func BaggageKeys(ctx context.Context) []string {
	if ctx == nil {
		return nil
	}
	return BaggageFromContext(ctx).Keys()
}

// BaggageLen returns the number of baggage entries in the context.
func BaggageLen(ctx context.Context) int {
	if ctx == nil {
		return 0
	}
	return BaggageFromContext(ctx).Len()
}

// Get retrieves a baggage item by key.
func (b Baggage) Get(key string) (BaggageItem, bool) {
	if b.entries == nil {
		return BaggageItem{}, false
	}
	item, ok := b.entries[key]
	return item, ok
}

// GetValue retrieves just the value for a key.
func (b Baggage) GetValue(key string) (string, bool) {
	item, ok := b.Get(key)
	return item.Value, ok
}

// Set adds or updates a baggage entry.
// Returns a new Baggage with the entry added (immutability).
func (b Baggage) Set(key, value string) (Baggage, error) {
	return b.SetWithMetadata(key, value, BaggageItemMetadata{})
}

// SetWithMetadata adds or updates a baggage entry with metadata.
func (b Baggage) SetWithMetadata(key, value string, metadata BaggageItemMetadata) (Baggage, error) {
	// Validate key
	if err := ValidateBaggageKey(key); err != nil {
		return Baggage{}, err
	}

	// Validate value
	if err := ValidateBaggageValue(value); err != nil {
		return Baggage{}, err
	}

	// Create new baggage (immutable)
	newBaggage := NewBaggage()
	
	// Copy existing entries
	for k, v := range b.entries {
		newBaggage.entries[k] = v
	}

	// Check entry limit
	if _, exists := newBaggage.entries[key]; !exists && len(newBaggage.entries) >= MaxBaggageEntries {
		return Baggage{}, ErrTooManyEntries
	}

	// Set new entry
	newBaggage.entries[key] = BaggageItem{
		Value:    value,
		Metadata: metadata,
	}

	return newBaggage, nil
}

// Delete removes a baggage entry.
// Returns a new Baggage without the entry (immutability).
func (b Baggage) Delete(key string) Baggage {
	if b.entries == nil {
		return b
	}
	if _, ok := b.entries[key]; !ok {
		return b
	}

	newBaggage := NewBaggage()
	for k, v := range b.entries {
		if k != key {
			newBaggage.entries[k] = v
		}
	}
	return newBaggage
}

// Has returns true if the key exists in baggage.
func (b Baggage) Has(key string) bool {
	if b.entries == nil {
		return false
	}
	_, ok := b.entries[key]
	return ok
}

// Len returns the number of entries.
func (b Baggage) Len() int {
	if b.entries == nil {
		return 0
	}
	return len(b.entries)
}

// IsEmpty returns true if baggage has no entries.
func (b Baggage) IsEmpty() bool {
	return b.Len() == 0
}

// Keys returns all baggage keys, sorted.
func (b Baggage) Keys() []string {
	if b.entries == nil {
		return nil
	}
	keys := make([]string, 0, len(b.entries))
	for k := range b.entries {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// Entries returns all baggage entries as a map.
func (b Baggage) Entries() map[string]BaggageItem {
	if b.entries == nil {
		return map[string]BaggageItem{}
	}
	// Return a copy to maintain immutability
	result := make(map[string]BaggageItem, len(b.entries))
	for k, v := range b.entries {
		result[k] = v
	}
	return result
}

// String returns the W3C baggage header string representation.
func (b Baggage) String() string {
	if b.entries == nil || len(b.entries) == 0 {
		return ""
	}

	var parts []string
	for _, key := range b.Keys() {
		item := b.entries[key]
		part := encodeBaggageItem(key, item)
		parts = append(parts, part)
	}

	return strings.Join(parts, ",")
}

// encodeBaggageItem encodes a baggage item to string format.
func encodeBaggageItem(key string, item BaggageItem) string {
	// Encode value (URL encoding for special chars)
	value := percentEncode(item.Value)
	
	result := fmt.Sprintf("%s=%s", key, value)
	
	// Add metadata properties if any
	if len(item.Metadata.Properties) > 0 {
		var props []string
		for k, v := range item.Metadata.Properties {
			props = append(props, fmt.Sprintf("%s=%s", percentEncode(k), percentEncode(v)))
		}
		sort.Strings(props)
		result += ";" + strings.Join(props, ";")
	}
	
	return result
}

// ParseBaggage parses a W3C baggage header value.
func ParseBaggage(s string) (Baggage, error) {
	baggage := NewBaggage()
	if s == "" {
		return baggage, nil
	}

	// Split by comma (separates different baggage entries)
	entries := splitBaggageEntries(s)

	for _, entry := range entries {
		entry = strings.TrimSpace(entry)
		if entry == "" {
			continue
		}

		key, item, err := parseBaggageEntry(entry)
		if err != nil {
			// Skip invalid entries per W3C spec
			continue
		}

		baggage.entries[key] = item
	}

	return baggage, nil
}

// splitBaggageEntries splits baggage string by comma, handling quoted values.
func splitBaggageEntries(s string) []string {
	var result []string
	var current strings.Builder
	inQuotes := false
	
	for i, r := range s {
		switch r {
		case '"':
			inQuotes = !inQuotes
			current.WriteRune(r)
		case ',':
			if inQuotes {
				current.WriteRune(r)
			} else {
				result = append(result, current.String())
				current.Reset()
			}
		default:
			current.WriteRune(r)
		}
		_ = i
	}
	
	if current.Len() > 0 {
		result = append(result, current.String())
	}
	
	return result
}

// parseBaggageEntry parses a single baggage entry.
func parseBaggageEntry(entry string) (string, BaggageItem, error) {
	// Split key=value from properties
	parts := strings.SplitN(entry, ";", 2)
	
	// Parse key=value
	kv := strings.TrimSpace(parts[0])
	kvParts := strings.SplitN(kv, "=", 2)
	if len(kvParts) != 2 {
		return "", BaggageItem{}, ErrInvalidValue
	}
	
	key := strings.TrimSpace(kvParts[0])
	value := percentDecode(strings.TrimSpace(kvParts[1]))
	
	item := BaggageItem{
		Value:    value,
		Metadata: BaggageItemMetadata{},
	}
	
	// Parse properties if present
	if len(parts) > 1 {
		item.Metadata.Properties = parseBaggageProperties(parts[1])
	}
	
	return key, item, nil
}

// parseBaggageProperties parses baggage property metadata.
func parseBaggageProperties(props string) map[string]string {
	result := make(map[string]string)
	
	parts := strings.Split(props, ";")
	for _, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		
		// Property can be just a flag (no value) or key=value
		kv := strings.SplitN(part, "=", 2)
		key := strings.TrimSpace(kv[0])
		
		if len(kv) == 2 {
			result[key] = percentDecode(strings.TrimSpace(kv[1]))
		} else {
			// Flag property (no value)
			result[key] = ""
		}
	}
	
	return result
}

// percentEncode URL-encodes a string for baggage.
func percentEncode(s string) string {
	// URL encode special characters
	return url.QueryEscape(s)
}

// percentDecode URL-decodes a string from baggage.
func percentDecode(s string) string {
	// URL decode
	d, _ := url.QueryUnescape(s)
	return d
}

// ValidateBaggageKey validates a baggage key.
func ValidateBaggageKey(key string) error {
	if key == "" {
		return fmt.Errorf("%w: key cannot be empty", ErrInvalidKey)
	}
	if len(key) > MaxBaggageKeyLength {
		return fmt.Errorf("%w: key too long (%d > %d)", ErrInvalidKey, len(key), MaxBaggageKeyLength)
	}
	if !validKeyRegex.MatchString(key) {
		return fmt.Errorf("%w: key contains invalid characters", ErrInvalidKey)
	}
	return nil
}

// ValidateBaggageValue validates a baggage value.
func ValidateBaggageValue(value string) error {
	if len(value) > MaxBaggageValueLength {
		return fmt.Errorf("%w: value too long (%d > %d)", ErrInvalidValue, len(value), MaxBaggageValueLength)
	}
	return nil
}

// BaggagePropagator implements W3C Baggage propagation.
type BaggagePropagator struct {
	once sync.Once
}

// NewBaggagePropagator creates a new W3C Baggage propagator.
func NewBaggagePropagator() *BaggagePropagator {
	return &BaggagePropagator{}
}

// Inject injects baggage into the carrier.
func (p *BaggagePropagator) Inject(ctx context.Context, carrier Carrier) {
	baggage := BaggageFromContext(ctx)
	if baggage.IsEmpty() {
		return
	}

	headerValue := baggage.String()
	if headerValue != "" {
		carrier.Set(BaggageHeader, headerValue)
	}
}

// Extract extracts baggage from the carrier.
func (p *BaggagePropagator) Extract(ctx context.Context, carrier Carrier) context.Context {
	headerValue := carrier.Get(BaggageHeader)
	if headerValue == "" {
		return ctx
	}

	baggage, err := ParseBaggage(headerValue)
	if err != nil {
		// If parsing fails, return original context
		return ctx
	}

	return ContextWithBaggage(ctx, baggage)
}

// Fields returns the fields used by this propagator.
func (p *BaggagePropagator) Fields() []string {
	return []string{BaggageHeader}
}

// BaggageSize returns the approximate size of baggage in bytes.
func (b Baggage) Size() int {
	size := 0
	for key, item := range b.entries {
		size += len(key)
		size += len(item.Value)
		size += 1 // separator
		for k, v := range item.Metadata.Properties {
			size += len(k) + len(v) + 2 // property separator
		}
	}
	return size
}

// Clone creates a deep copy of baggage.
func (b Baggage) Clone() Baggage {
	if b.entries == nil {
		return NewBaggage()
	}
	cloned := NewBaggage()
	for k, v := range b.entries {
		// Clone metadata
		metadata := BaggageItemMetadata{}
		if len(v.Metadata.Properties) > 0 {
			metadata.Properties = make(map[string]string, len(v.Metadata.Properties))
			for pk, pv := range v.Metadata.Properties {
				metadata.Properties[pk] = pv
			}
		}
		cloned.entries[k] = BaggageItem{
			Value:    v.Value,
			Metadata: metadata,
		}
	}
	return cloned
}

// Merge combines two baggage instances.
// Entries from 'other' take precedence.
func (b Baggage) Merge(other Baggage) Baggage {
	if other.IsEmpty() {
		return b
	}
	if b.IsEmpty() {
		return other
	}

	merged := b.Clone()
	for k, v := range other.entries {
		merged.entries[k] = v
	}
	return merged
}

// Filter returns a new baggage with only the specified keys.
func (b Baggage) Filter(keys ...string) Baggage {
	if b.IsEmpty() || len(keys) == 0 {
		return NewBaggage()
	}

	keySet := make(map[string]struct{}, len(keys))
	for _, k := range keys {
		keySet[k] = struct{}{}
	}

	filtered := NewBaggage()
	for k, v := range b.entries {
		if _, ok := keySet[k]; ok {
			filtered.entries[k] = v
		}
	}
	return filtered
}

// Map applies a function to all baggage values.
func (b Baggage) Map(fn func(key, value string) string) Baggage {
	if b.IsEmpty() {
		return b
	}

	mapped := NewBaggage()
	for k, v := range b.entries {
		newValue := fn(k, v.Value)
		if err := ValidateBaggageValue(newValue); err == nil {
			mapped.entries[k] = BaggageItem{
				Value:    newValue,
				Metadata: v.Metadata,
			}
		} else {
			// Keep original if new value is invalid
			mapped.entries[k] = v
		}
	}
	return mapped
}

// ForEach iterates over all baggage entries.
func (b Baggage) ForEach(fn func(key string, item BaggageItem) bool) {
	for k, v := range b.entries {
		if !fn(k, v) {
			break
		}
	}
}

// baggagePool for efficient baggage allocation
type baggagePool struct {
	pool sync.Pool
}

func newBaggagePool() *baggagePool {
	return &baggagePool{
		pool: sync.Pool{
			New: func() interface{} {
				return &Baggage{entries: make(map[string]BaggageItem)}
			},
		},
	}
}

var globalBaggagePool = newBaggagePool()

// getBaggageFromPool gets a baggage from the pool.
func getBaggageFromPool() *Baggage {
	return globalBaggagePool.pool.Get().(*Baggage)
}

// putBaggageToPool returns a baggage to the pool.
func putBaggageToPool(b *Baggage) {
	if b == nil || b.entries == nil {
		return
	}
	// Clear entries but keep the map allocated
	for k := range b.entries {
		delete(b.entries, k)
	}
	globalBaggagePool.pool.Put(b)
}

// EncodeBase64 encodes baggage to base64 string.
func (b Baggage) EncodeBase64() string {
	if b.IsEmpty() {
		return ""
	}
	return base64.StdEncoding.EncodeToString([]byte(b.String()))
}

// DecodeBase64 decodes base64 encoded baggage.
func DecodeBase64(s string) (Baggage, error) {
	if s == "" {
		return NewBaggage(), nil
	}
	data, err := base64.StdEncoding.DecodeString(s)
	if err != nil {
		return NewBaggage(), err
	}
	return ParseBaggage(string(data))
}

// MustParseBaggage parses baggage and panics on error.
// Use only in tests or when input is guaranteed valid.
func MustParseBaggage(s string) Baggage {
	b, err := ParseBaggage(s)
	if err != nil {
		panic(fmt.Sprintf("failed to parse baggage: %v", err))
	}
	return b
}

// BaggageFromMap creates baggage from a map.
func BaggageFromMap(m map[string]string) (Baggage, error) {
	baggage := NewBaggage()
	for k, v := range m {
		var err error
		baggage, err = baggage.Set(k, v)
		if err != nil {
			return NewBaggage(), err
		}
	}
	return baggage, nil
}

// BaggageToMap converts baggage to a simple map.
func BaggageToMap(b Baggage) map[string]string {
	result := make(map[string]string, b.Len())
	for k, v := range b.entries {
		result[k] = v.Value
	}
	return result
}

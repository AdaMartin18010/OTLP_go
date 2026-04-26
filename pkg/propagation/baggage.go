// Package propagation implements OpenTelemetry propagators for various
// distributed tracing formats.
//
// Baggage 管理器实现了 W3C Baggage 规范的完整传播器，支持键值对的
// 增删改查、属性附加、长度限制和非法字符过滤。
// https://www.w3.org/TR/baggage/
package propagation

import (
	"context"
	"fmt"
	"net/url"
	"regexp"
	"strings"
	"unicode/utf8"

	otelbaggage "go.opentelemetry.io/otel/baggage"
	otelprop "go.opentelemetry.io/otel/propagation"
)

const (
	baggageHeader = "baggage"

	// W3C Baggage limits.
	maxBaggageMembers       = 180
	maxBytesPerMember       = 4096
	maxBytesPerBaggageString = 8192
)

// Baggage implements the W3C Baggage propagator with extended management capabilities.
type Baggage struct{}

// Compile-time interface check.
var _ otelprop.TextMapPropagator = Baggage{}

// Inject injects baggage from ctx into carrier.
func (b Baggage) Inject(ctx context.Context, carrier otelprop.TextMapCarrier) {
	bag := otelbaggage.FromContext(ctx)
	bStr := bag.String()
	if bStr != "" {
		carrier.Set(baggageHeader, bStr)
	}
}

// Extract returns a copy of parent with the baggage from carrier added.
func (b Baggage) Extract(parent context.Context, carrier otelprop.TextMapCarrier) context.Context {
	bStr := carrier.Get(baggageHeader)
	if bStr == "" {
		return parent
	}

	bag, err := otelbaggage.Parse(bStr)
	if err != nil {
		// Try sanitizing invalid input before giving up.
		sanitized := b.sanitizeBaggageString(bStr)
		bag, err = otelbaggage.Parse(sanitized)
		if err != nil {
			return parent
		}
	}
	return otelbaggage.ContextWithBaggage(parent, bag)
}

// Fields returns the keys whose values are set with Inject.
func (b Baggage) Fields() []string {
	return []string{baggageHeader}
}

// sanitizeBaggageString cleans an incoming baggage string by removing
// invalid characters, truncating oversized members, and dropping malformed entries.
func (b Baggage) sanitizeBaggageString(s string) string {
	entries := strings.Split(s, ",")
	var valid []string

	for _, entry := range entries {
		entry = strings.TrimSpace(entry)
		if entry == "" {
			continue
		}

		member, props, hasProps := splitMemberAndProperties(entry)
		if member == "" {
			continue
		}

		kv := strings.SplitN(member, "=", 2)
		if len(kv) != 2 {
			continue
		}

		key := strings.TrimSpace(kv[0])
		value := strings.TrimSpace(kv[1])

		if !isValidBaggageKey(key) {
			continue
		}
		if !isValidBaggageValue(value) {
			continue
		}

		// Length enforcement.
		if len(key) > 255 {
			key = key[:255]
		}
		if len(value) > 255 {
			value = value[:255]
		}

		encoded := key + "=" + url.PathEscape(value)
		if hasProps && props != "" {
			encoded += ";" + props
		}

		valid = append(valid, encoded)
		if len(valid) >= maxBaggageMembers {
			break
		}
	}

	result := strings.Join(valid, ",")
	if len(result) > maxBytesPerBaggageString {
		result = result[:maxBytesPerBaggageString]
		// Trim to last complete member.
		if idx := strings.LastIndex(result, ","); idx > 0 {
			result = result[:idx]
		}
	}
	return result
}

// splitMemberAndProperties separates the key=value part from properties.
// Properties are separated by semicolons after the first semicolon.
func splitMemberAndProperties(s string) (member string, props string, hasProps bool) {
	parts := strings.SplitN(s, ";", 2)
	if len(parts) == 2 {
		return strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1]), true
	}
	return strings.TrimSpace(parts[0]), "", false
}

// isValidBaggageKey validates a baggage key per W3C spec (token characters).
func isValidBaggageKey(key string) bool {
	if key == "" {
		return false
	}
	for _, r := range key {
		if !isTokenChar(r) {
			return false
		}
	}
	return true
}

// isValidBaggageValue validates a baggage value.
// It must be valid UTF-8 and printable.
func isValidBaggageValue(value string) bool {
	if !utf8.ValidString(value) {
		return false
	}
	// Allow any UTF-8 string; OTel baggage handles percent-encoding.
	return true
}

// isTokenChar reports whether r is a valid token character per RFC7230.
func isTokenChar(r rune) bool {
	return r > 0x20 && r < 0x7f &&
		strings.IndexRune(`()<>@,;:\"/[]?={} `, r) < 0
}

// BaggageManager provides CRUD operations for baggage entries.
type BaggageManager struct{}

// NewBaggageManager creates a new BaggageManager.
func NewBaggageManager() *BaggageManager {
	return &BaggageManager{}
}

// Get retrieves a baggage value by key from context.
func (bm *BaggageManager) Get(ctx context.Context, key string) (string, bool) {
	bag := otelbaggage.FromContext(ctx)
	member := bag.Member(key)
	if member.Key() == "" {
		return "", false
	}
	return member.Value(), true
}

// Set adds or updates a baggage key-value pair in context.
// Returns the new context and an error if the member is invalid.
func (bm *BaggageManager) Set(ctx context.Context, key, value string) (context.Context, error) {
	if !isValidBaggageKey(key) {
		return ctx, fmt.Errorf("invalid baggage key: %s", key)
	}
	if !utf8.ValidString(value) {
		return ctx, fmt.Errorf("invalid baggage value: %s", value)
	}

	member, err := otelbaggage.NewMemberRaw(key, value)
	if err != nil {
		return ctx, fmt.Errorf("failed to create baggage member: %w", err)
	}

	bag := otelbaggage.FromContext(ctx)
	newBag, err := otelbaggage.New(append(bag.Members(), member)...)
	if err != nil {
		return ctx, fmt.Errorf("failed to create baggage: %w", err)
	}

	return otelbaggage.ContextWithBaggage(ctx, newBag), nil
}

// Remove removes a baggage entry by key from context.
func (bm *BaggageManager) Remove(ctx context.Context, key string) context.Context {
	bag := otelbaggage.FromContext(ctx)
	members := bag.Members()
	var filtered []otelbaggage.Member
	for _, m := range members {
		if m.Key() != key {
			filtered = append(filtered, m)
		}
	}
	if len(filtered) == len(members) {
		return ctx // key not found
	}
	newBag, _ := otelbaggage.New(filtered...)
	return otelbaggage.ContextWithBaggage(ctx, newBag)
}

// List returns all baggage key-value pairs from context.
func (bm *BaggageManager) List(ctx context.Context) map[string]string {
	bag := otelbaggage.FromContext(ctx)
	result := make(map[string]string, len(bag.Members()))
	for _, m := range bag.Members() {
		result[m.Key()] = m.Value()
	}
	return result
}

// Clear removes all baggage from context.
func (bm *BaggageManager) Clear(ctx context.Context) context.Context {
	return otelbaggage.ContextWithBaggage(ctx, otelbaggage.Baggage{})
}

// FilterPII scans baggage for PII patterns and returns a sanitized version.
// If PII is detected, the offending entries are removed.
func (bm *BaggageManager) FilterPII(ctx context.Context) context.Context {
	bag := otelbaggage.FromContext(ctx)
	members := bag.Members()
	var filtered []otelbaggage.Member

	for _, m := range members {
		if !containsPII(m.Value()) {
			filtered = append(filtered, m)
		}
	}

	if len(filtered) == len(members) {
		return ctx
	}
	newBag, _ := otelbaggage.New(filtered...)
	return otelbaggage.ContextWithBaggage(ctx, newBag)
}

// containsPII checks if a string contains common PII patterns.
func containsPII(s string) bool {
	emailRe := regexp.MustCompile(`[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}`)
	phoneRe := regexp.MustCompile(`\b\d{3}[-.\s]?\d{3}[-.\s]?\d{4}\b`)
	ssnRe := regexp.MustCompile(`\b\d{3}[-\s]?\d{2}[-\s]?\d{4}\b`)

	return emailRe.MatchString(s) || phoneRe.MatchString(s) || ssnRe.MatchString(s)
}

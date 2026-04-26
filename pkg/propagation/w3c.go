// Package propagation implements OpenTelemetry propagators for various
// distributed tracing formats including W3C Trace Context, B3, and Jaeger.
//
// W3C Trace Context Level 2 支持:
//   - traceparent 解析与编码
//   - tracestate 解析与编码（含条目限制、截断策略、PII扫描）
//   - random-trace-id flag (0x02)
//   - 完整的验证逻辑
package propagation

import (
	"context"
	"encoding/hex"
	"fmt"
	"regexp"
	"strings"
	"sync"

	otelprop "go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
)

const (
	// W3C Trace Context header names
	traceparentHeader = "traceparent"
	tracestateHeader  = "tracestate"
	delimiter         = "-"

	// W3C version constants
	supportedVersion = 0
	maxVersion       = 254

	// Trace-state limits per W3C spec
	maxTraceStateEntries = 32
	maxTraceStateKeyLen  = 256
	maxTraceStateValLen  = 256

	// Random trace ID flag (W3C Level 2)
	flagRandom = 0x02
)

// pre-compiled PII detection regexes for performance
var (
	emailRegex   = regexp.MustCompile(`[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}`)
	phoneRegex   = regexp.MustCompile(`\b\d{3}[-.\s]?\d{3}[-.\s]?\d{4}\b`)
	ssnRegex     = regexp.MustCompile(`\b\d{3}[-\s]?\d{2}[-\s]?\d{4}\b`)
	piiRegexOnce sync.Once
)

// W3C implements a W3C Trace Context Level 2 propagator.
// It supports traceparent and tracestate headers with full validation,
// privacy scanning, and random-trace-id flag propagation.
type W3C struct{}

// Compile-time check that W3C implements TextMapPropagator.
var _ otelprop.TextMapPropagator = W3C{}

// Inject injects the trace context from ctx into carrier.
// It encodes traceparent as version-traceid-parentid-flags and sets
// tracestate if present. The random flag (0x02) is preserved when present.
func (w W3C) Inject(ctx context.Context, carrier otelprop.TextMapCarrier) {
	sc := trace.SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	// Build traceparent: version is always "00" for now
	var sb strings.Builder
	sb.Grow(55) // 2 + 1 + 32 + 1 + 16 + 1 + 2

	sb.WriteString("00")
	sb.WriteByte('-')
	sb.WriteString(sc.TraceID().String())
	sb.WriteByte('-')
	sb.WriteString(sc.SpanID().String())
	sb.WriteByte('-')

	// Preserve both sampled (0x01) and random (0x02) flags.
	flags := byte(sc.TraceFlags()) & (byte(trace.FlagsSampled) | flagRandom)
	sb.WriteString(fmt.Sprintf("%02x", flags))

	carrier.Set(traceparentHeader, sb.String())

	// Inject tracestate with sanitization.
	if tsStr := sc.TraceState().String(); tsStr != "" {
		sanitized := w.sanitizeTraceState(tsStr)
		if sanitized != "" {
			carrier.Set(tracestateHeader, sanitized)
		}
	}
}

// Extract reads tracecontext from carrier into a returned Context.
// If the extracted traceparent is invalid, the original ctx is returned.
func (w W3C) Extract(ctx context.Context, carrier otelprop.TextMapCarrier) context.Context {
	sc := w.extractSpanContext(carrier)
	if !sc.IsValid() {
		return ctx
	}
	return trace.ContextWithRemoteSpanContext(ctx, sc)
}

// extractSpanContext parses traceparent and tracestate from carrier.
func (w W3C) extractSpanContext(carrier otelprop.TextMapCarrier) trace.SpanContext {
	h := carrier.Get(traceparentHeader)
	if h == "" {
		return trace.SpanContext{}
	}

	parts := strings.Split(h, delimiter)
	if len(parts) != 4 {
		return trace.SpanContext{}
	}

	// Version validation: must be 2 hex digits.
	if len(parts[0]) != 2 {
		return trace.SpanContext{}
	}
	var ver [1]byte
	if _, err := hex.Decode(ver[:], []byte(parts[0])); err != nil {
		return trace.SpanContext{}
	}
	version := int(ver[0])
	if version > maxVersion {
		return trace.SpanContext{}
	}

	// Trace-id validation: 32 hex chars, not all zero.
	if len(parts[1]) != 32 {
		return trace.SpanContext{}
	}
	traceID, err := trace.TraceIDFromHex(parts[1])
	if err != nil {
		return trace.SpanContext{}
	}

	// Parent-id (span-id) validation: 16 hex chars, not all zero.
	if len(parts[2]) != 16 {
		return trace.SpanContext{}
	}
	spanID, err := trace.SpanIDFromHex(parts[2])
	if err != nil {
		return trace.SpanContext{}
	}

	// Flags validation: 2 hex digits.
	if len(parts[3]) != 2 {
		return trace.SpanContext{}
	}
	var opts [1]byte
	if _, err := hex.Decode(opts[:], []byte(parts[3])); err != nil {
		return trace.SpanContext{}
	}

	flags := opts[0]

	// For version 00, flags must not exceed 0x03 (sampled + random).
	// Higher versions may define additional flags; we preserve 0x01 and 0x02.
	if version == supportedVersion && flags > 0x03 {
		return trace.SpanContext{}
	}

	tf := trace.TraceFlags(flags)

	// Parse tracestate; ignore errors per W3C spec.
	var ts trace.TraceState
	if tsStr := carrier.Get(tracestateHeader); tsStr != "" {
		sanitized := w.sanitizeTraceState(tsStr)
		if sanitized != "" {
			parsed, _ := trace.ParseTraceState(sanitized)
			ts = parsed
		}
	}

	scc := trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: tf,
		TraceState: ts,
		Remote:     true,
	}

	sc := trace.NewSpanContext(scc)
	if !sc.IsValid() {
		return trace.SpanContext{}
	}
	return sc
}

// Fields returns the keys whose values are set with Inject.
func (w W3C) Fields() []string {
	return []string{traceparentHeader, tracestateHeader}
}

// sanitizeTraceState performs privacy security checks, validates entries,
// enforces length limits, and truncates with vendor-priority strategy.
func (w W3C) sanitizeTraceState(ts string) string {
	// PII scan: if detected, drop the entire tracestate to avoid leaking data.
	if w.containsPII(ts) {
		return ""
	}

	entries := strings.Split(ts, ",")
	var validEntries []string

	for _, entry := range entries {
		entry = strings.TrimSpace(entry)
		if entry == "" {
			continue
		}

		kv := strings.SplitN(entry, "=", 2)
		if len(kv) != 2 {
			continue
		}

		key := strings.TrimSpace(kv[0])
		val := strings.TrimSpace(kv[1])

		if !isValidTraceStateKey(key) {
			continue
		}
		if !isValidTraceStateValue(val) {
			continue
		}

		// Enforce key/value length limits.
		if len(key) > maxTraceStateKeyLen {
			key = key[:maxTraceStateKeyLen]
		}
		if len(val) > maxTraceStateValLen {
			val = val[:maxTraceStateValLen]
		}

		validEntries = append(validEntries, key+"="+val)
		if len(validEntries) >= maxTraceStateEntries {
			break
		}
	}

	// If still over limit, prioritize vendor@key format.
	if len(validEntries) > maxTraceStateEntries {
		validEntries = prioritizeVendorEntries(validEntries)
	}

	return strings.Join(validEntries, ",")
}

// containsPII scans the input for common personally identifiable information
// patterns including email addresses, phone numbers, and SSNs.
func (w W3C) containsPII(s string) bool {
	return emailRegex.MatchString(s) || phoneRegex.MatchString(s) || ssnRegex.MatchString(s)
}

// isValidTraceStateKey validates a tracestate key per W3C spec.
// Keys must be lowercase alphanumeric with _ - * / and may use tenant@system format.
func isValidTraceStateKey(key string) bool {
	if key == "" {
		return false
	}

	parts := strings.Split(key, "@")
	if len(parts) > 2 {
		return false
	}

	for _, part := range parts {
		if part == "" {
			return false
		}
		// First char must be lowercase letter or digit.
		first := part[0]
		if !((first >= 'a' && first <= 'z') || (first >= '0' && first <= '9')) {
			return false
		}
		// Remaining chars: lcalpha / DIGIT / "_" / "-" / "*" / "/"
		for i := 1; i < len(part); i++ {
			c := part[i]
			if !isValidKeyChar(c) {
				return false
			}
		}
	}
	return true
}

// isValidKeyChar reports whether c is a valid tracestate key character.
func isValidKeyChar(c byte) bool {
	return (c >= 'a' && c <= 'z') ||
		(c >= '0' && c <= '9') ||
		c == '_' || c == '-' || c == '*' || c == '/'
}

// isValidTraceStateValue validates a tracestate value per W3C spec.
// value = (0*255(chr)) nblk-chr where chr = %x20-2B / %x2D-3C / %x3E-7E
func isValidTraceStateValue(val string) bool {
	n := len(val)
	if n == 0 || n > maxTraceStateValLen {
		return false
	}
	for i := 0; i < n-1; i++ {
		c := val[i]
		if !isValidValueChar(c) {
			return false
		}
	}
	// Last char must be non-blank printable.
	last := val[n-1]
	return last >= 0x21 && last <= 0x7e && last != 0x2c && last != 0x3d
}

// isValidValueChar reports whether c is a valid non-final tracestate value character.
func isValidValueChar(c byte) bool {
	return c >= 0x20 && c <= 0x7e && c != 0x2c && c != 0x3d
}

// prioritizeVendorEntries sorts entries to keep vendor@key format first
// and truncates to maxTraceStateEntries if necessary.
func prioritizeVendorEntries(entries []string) []string {
	var vendor, others []string

	for _, e := range entries {
		key := strings.SplitN(e, "=", 2)[0]
		if strings.Contains(key, "@") {
			vendor = append(vendor, e)
		} else {
			others = append(others, e)
		}
	}

	result := append(vendor, others...)
	if len(result) > maxTraceStateEntries {
		return result[:maxTraceStateEntries]
	}
	return result
}

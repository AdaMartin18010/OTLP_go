// Package propagation implements OpenTelemetry propagators for various
// distributed tracing formats.
//
// B3 传播器支持单头和多头两种模式，兼容 Zipkin 的 B3 传播规范。
// https://github.com/openzipkin/b3-propagation
package propagation

import (
	"context"
	"fmt"
	"strconv"
	"strings"

	otelprop "go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
)

const (
	// B3 single header name.
	b3SingleHeader = "b3"

	// B3 multi-header names.
	b3TraceIDHeader      = "X-B3-TraceId"
	b3SpanIDHeader       = "X-B3-SpanId"
	b3ParentSpanIDHeader = "X-B3-ParentSpanId"
	b3SampledHeader      = "X-B3-Sampled"
	b3FlagsHeader        = "X-B3-Flags"

	// B3 debug flag value.
	b3DebugFlag = 1
)

// B3Single implements the B3 single-header propagator.
// Format: {TraceId}-{SpanId}-{SamplingState}-{ParentSpanId}
type B3Single struct{}

// Compile-time interface check.
var _ otelprop.TextMapPropagator = B3Single{}

// Inject injects span context into carrier using the B3 single header format.
func (b3 B3Single) Inject(ctx context.Context, carrier otelprop.TextMapCarrier) {
	sc := trace.SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	var sb strings.Builder
	sb.WriteString(sc.TraceID().String())
	sb.WriteByte('-')
	sb.WriteString(sc.SpanID().String())

	if sc.IsSampled() {
		sb.WriteByte('-')
		sb.WriteByte('1')
	} else {
		sb.WriteByte('-')
		sb.WriteByte('0')
	}

	carrier.Set(b3SingleHeader, sb.String())
}

// Extract extracts span context from the B3 single header.
func (b3 B3Single) Extract(ctx context.Context, carrier otelprop.TextMapCarrier) context.Context {
	sc := b3.extract(carrier)
	if !sc.IsValid() {
		return ctx
	}
	return trace.ContextWithRemoteSpanContext(ctx, sc)
}

// Fields returns the fields used by this propagator.
func (b3 B3Single) Fields() []string {
	return []string{b3SingleHeader}
}

func (b3 B3Single) extract(carrier otelprop.TextMapCarrier) trace.SpanContext {
	h := carrier.Get(b3SingleHeader)
	if h == "" {
		return trace.SpanContext{}
	}

	// B3 single header may be just "0" or "1" or "d" for sampling-only.
	switch h {
	case "0":
		return trace.SpanContext{}
	case "1", "d":
		return trace.SpanContext{}
	}

	parts := strings.Split(h, "-")
	if len(parts) < 2 || len(parts) > 4 {
		return trace.SpanContext{}
	}

	traceID, err := parseB3TraceID(parts[0])
	if err != nil {
		return trace.SpanContext{}
	}

	spanID, err := parseB3SpanID(parts[1])
	if err != nil {
		return trace.SpanContext{}
	}

	var flags trace.TraceFlags
	if len(parts) >= 3 {
		switch parts[2] {
		case "1", "d":
			flags = flags.WithSampled(true)
		}
	}

	sc := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: flags,
		Remote:     true,
	})
	if !sc.IsValid() {
		return trace.SpanContext{}
	}
	return sc
}

// B3Multi implements the B3 multi-header propagator.
type B3Multi struct{}

// Compile-time interface check.
var _ otelprop.TextMapPropagator = B3Multi{}

// Inject injects span context into carrier using B3 multi headers.
func (b3 B3Multi) Inject(ctx context.Context, carrier otelprop.TextMapCarrier) {
	sc := trace.SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	carrier.Set(b3TraceIDHeader, sc.TraceID().String())
	carrier.Set(b3SpanIDHeader, sc.SpanID().String())

	if sc.IsSampled() {
		carrier.Set(b3SampledHeader, "1")
	} else {
		carrier.Set(b3SampledHeader, "0")
	}
}

// Extract extracts span context from B3 multi headers.
func (b3 B3Multi) Extract(ctx context.Context, carrier otelprop.TextMapCarrier) context.Context {
	sc := b3.extract(carrier)
	if !sc.IsValid() {
		return ctx
	}
	return trace.ContextWithRemoteSpanContext(ctx, sc)
}

// Fields returns the fields used by this propagator.
func (b3 B3Multi) Fields() []string {
	return []string{b3TraceIDHeader, b3SpanIDHeader, b3ParentSpanIDHeader, b3SampledHeader, b3FlagsHeader}
}

func (b3 B3Multi) extract(carrier otelprop.TextMapCarrier) trace.SpanContext {
	traceIDStr := carrier.Get(b3TraceIDHeader)
	spanIDStr := carrier.Get(b3SpanIDHeader)

	if traceIDStr == "" || spanIDStr == "" {
		return trace.SpanContext{}
	}

	traceID, err := parseB3TraceID(traceIDStr)
	if err != nil {
		return trace.SpanContext{}
	}

	spanID, err := parseB3SpanID(spanIDStr)
	if err != nil {
		return trace.SpanContext{}
	}

	var flags trace.TraceFlags

	sampledStr := carrier.Get(b3SampledHeader)
	switch sampledStr {
	case "1", "true":
		flags = flags.WithSampled(true)
	}

	// B3 debug flag forces sampling.
	flagsStr := carrier.Get(b3FlagsHeader)
	if flagsStr == strconv.Itoa(b3DebugFlag) {
		flags = flags.WithSampled(true)
	}

	sc := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: flags,
		Remote:     true,
	})
	if !sc.IsValid() {
		return trace.SpanContext{}
	}
	return sc
}

// parseB3TraceID parses a B3 trace ID which may be 64-bit (16 hex) or 128-bit (32 hex).
// It left-pads 64-bit IDs to 128-bit.
func parseB3TraceID(s string) (trace.TraceID, error) {
	switch len(s) {
	case 32:
		return trace.TraceIDFromHex(s)
	case 16:
		// Left-pad to 128-bit.
		return trace.TraceIDFromHex(strings.Repeat("0", 16) + s)
	default:
		return trace.TraceID{}, fmt.Errorf("invalid B3 trace ID length: %d", len(s))
	}
}

// parseB3SpanID parses a B3 span ID (64-bit, 16 hex chars).
func parseB3SpanID(s string) (trace.SpanID, error) {
	if len(s) != 16 {
		return trace.SpanID{}, fmt.Errorf("invalid B3 span ID length: %d", len(s))
	}
	return trace.SpanIDFromHex(s)
}

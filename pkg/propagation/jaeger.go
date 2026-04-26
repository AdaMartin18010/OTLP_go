// Package propagation implements OpenTelemetry propagators for various
// distributed tracing formats.
//
// Jaeger 传播器实现了 Uber 的 uber-trace-id 格式。
// https://www.jaegertracing.io/docs/latest/client-libraries/#propagation-format
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
	// Jaeger header name.
	jaegerHeader = "uber-trace-id"

	// Jaeger baggage prefix.
	jaegerBaggagePrefix = "uberctx-"

	// Jaeger flag values.
	jaegerSampledFlag = 0x01
	jaegerDebugFlag   = 0x02
)

// Jaeger implements the Jaeger uber-trace-id propagator.
// Format: {trace-id}:{span-id}:{parent-span-id}:{flags}
type Jaeger struct{}

// Compile-time interface check.
var _ otelprop.TextMapPropagator = Jaeger{}

// Inject injects span context into carrier using the Jaeger format.
func (j Jaeger) Inject(ctx context.Context, carrier otelprop.TextMapCarrier) {
	sc := trace.SpanContextFromContext(ctx)
	if !sc.IsValid() {
		return
	}

	flags := 0
	if sc.IsSampled() {
		flags |= jaegerSampledFlag
	}

	value := fmt.Sprintf("%s:%s:0:%d",
		sc.TraceID().String(),
		sc.SpanID().String(),
		flags,
	)

	carrier.Set(jaegerHeader, value)
}

// Extract extracts span context from the Jaeger header.
func (j Jaeger) Extract(ctx context.Context, carrier otelprop.TextMapCarrier) context.Context {
	sc := j.extract(carrier)
	if !sc.IsValid() {
		return ctx
	}
	return trace.ContextWithRemoteSpanContext(ctx, sc)
}

// Fields returns the fields used by this propagator.
func (j Jaeger) Fields() []string {
	return []string{jaegerHeader}
}

func (j Jaeger) extract(carrier otelprop.TextMapCarrier) trace.SpanContext {
	h := carrier.Get(jaegerHeader)
	if h == "" {
		return trace.SpanContext{}
	}

	parts := strings.Split(h, ":")
	if len(parts) != 4 {
		return trace.SpanContext{}
	}

	traceID, err := parseJaegerTraceID(parts[0])
	if err != nil {
		return trace.SpanContext{}
	}

	spanID, err := parseJaegerSpanID(parts[1])
	if err != nil {
		return trace.SpanContext{}
	}

	// parts[2] is parent-span-id, usually ignored in OTel.

	flags, err := strconv.ParseUint(parts[3], 10, 8)
	if err != nil {
		return trace.SpanContext{}
	}

	var tf trace.TraceFlags
	if flags&jaegerSampledFlag != 0 || flags&jaegerDebugFlag != 0 {
		tf = tf.WithSampled(true)
	}

	sc := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    traceID,
		SpanID:     spanID,
		TraceFlags: tf,
		Remote:     true,
	})
	if !sc.IsValid() {
		return trace.SpanContext{}
	}
	return sc
}

// parseJaegerTraceID parses a Jaeger trace ID which may be 64-bit (16 hex) or 128-bit (32 hex).
func parseJaegerTraceID(s string) (trace.TraceID, error) {
	switch len(s) {
	case 32:
		return trace.TraceIDFromHex(s)
	case 16:
		return trace.TraceIDFromHex(strings.Repeat("0", 16) + s)
	default:
		return trace.TraceID{}, fmt.Errorf("invalid Jaeger trace ID length: %d", len(s))
	}
}

// parseJaegerSpanID parses a Jaeger span ID (64-bit, 16 hex chars).
func parseJaegerSpanID(s string) (trace.SpanID, error) {
	if len(s) != 16 {
		return trace.SpanID{}, fmt.Errorf("invalid Jaeger span ID length: %d", len(s))
	}
	return trace.SpanIDFromHex(s)
}

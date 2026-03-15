// Package context provides context propagation utilities for the OTLP Go SDK.
package context

import (
	"context"
	"testing"
)

func TestTraceID(t *testing.T) {
	t.Run("IsValid", func(t *testing.T) {
		valid := TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
		if !valid.IsValid() {
			t.Error("expected valid trace ID")
		}

		invalid := TraceID{}
		if invalid.IsValid() {
			t.Error("expected invalid zero trace ID")
		}
	})

	t.Run("String", func(t *testing.T) {
		tid := TraceID{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
			0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10}
		expected := "0123456789abcdeffedcba9876543210"
		if s := tid.String(); s != expected {
			t.Errorf("expected %s, got %s", expected, s)
		}
	})

	t.Run("MarshalUnmarshalText", func(t *testing.T) {
		original := TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}

		data, err := original.MarshalText()
		if err != nil {
			t.Fatalf("marshal failed: %v", err)
		}

		var parsed TraceID
		if err := parsed.UnmarshalText(data); err != nil {
			t.Fatalf("unmarshal failed: %v", err)
		}

		if original != parsed {
			t.Error("parsed trace ID does not match original")
		}
	})

	t.Run("UnmarshalText_InvalidLength", func(t *testing.T) {
		var tid TraceID
		err := tid.UnmarshalText([]byte("0123456789abcdef")) // Too short
		if err == nil {
			t.Error("expected error for invalid length")
		}
	})
}

func TestSpanID(t *testing.T) {
	t.Run("IsValid", func(t *testing.T) {
		valid := SpanID{1, 2, 3, 4, 5, 6, 7, 8}
		if !valid.IsValid() {
			t.Error("expected valid span ID")
		}

		invalid := SpanID{}
		if invalid.IsValid() {
			t.Error("expected invalid zero span ID")
		}
	})

	t.Run("String", func(t *testing.T) {
		sid := SpanID{0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef}
		expected := "0123456789abcdef"
		if s := sid.String(); s != expected {
			t.Errorf("expected %s, got %s", expected, s)
		}
	})

	t.Run("MarshalUnmarshalText", func(t *testing.T) {
		original := SpanID{1, 2, 3, 4, 5, 6, 7, 8}

		data, err := original.MarshalText()
		if err != nil {
			t.Fatalf("marshal failed: %v", err)
		}

		var parsed SpanID
		if err := parsed.UnmarshalText(data); err != nil {
			t.Fatalf("unmarshal failed: %v", err)
		}

		if original != parsed {
			t.Error("parsed span ID does not match original")
		}
	})

	t.Run("UnmarshalText_InvalidLength", func(t *testing.T) {
		var sid SpanID
		err := sid.UnmarshalText([]byte("01234567")) // Too short
		if err == nil {
			t.Error("expected error for invalid length")
		}
	})
}

func TestTraceFlags(t *testing.T) {
	t.Run("IsSampled", func(t *testing.T) {
		flags := FlagSampled
		if !flags.IsSampled() {
			t.Error("expected sampled flag to be set")
		}

		flags = 0
		if flags.IsSampled() {
			t.Error("expected sampled flag to be unset")
		}
	})

	t.Run("WithSampled", func(t *testing.T) {
		flags := TraceFlags(0)
		flags = flags.WithSampled(true)
		if !flags.IsSampled() {
			t.Error("expected sampled flag to be set")
		}

		flags = flags.WithSampled(false)
		if flags.IsSampled() {
			t.Error("expected sampled flag to be unset")
		}
	})

	t.Run("String", func(t *testing.T) {
		flags := TraceFlags(0x01)
		if s := flags.String(); s != "01" {
			t.Errorf("expected 01, got %s", s)
		}
	})

	t.Run("ParseTraceFlags", func(t *testing.T) {
		flags, err := ParseTraceFlags("01")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if flags != 0x01 {
			t.Errorf("expected 0x01, got 0x%02x", flags)
		}
	})

	t.Run("ParseTraceFlags_Invalid", func(t *testing.T) {
		_, err := ParseTraceFlags("0") // Too short
		if err == nil {
			t.Error("expected error for invalid length")
		}

		_, err = ParseTraceFlags("xyz") // Invalid hex
		if err == nil {
			t.Error("expected error for invalid hex")
		}
	})
}

func TestTraceState(t *testing.T) {
	t.Run("NewTraceState", func(t *testing.T) {
		ts := NewTraceState()
		if ts.Len() != 0 {
			t.Errorf("expected empty tracestate, got %d entries", ts.Len())
		}
	})

	t.Run("SetGet", func(t *testing.T) {
		ts := NewTraceState()
		err := ts.Set("vendor", "value")
		if err != nil {
			t.Fatalf("set failed: %v", err)
		}

		val, ok := ts.Get("vendor")
		if !ok {
			t.Fatal("expected to find key")
		}
		if val != "value" {
			t.Errorf("expected value, got %s", val)
		}

		_, ok = ts.Get("nonexistent")
		if ok {
			t.Error("expected not to find nonexistent key")
		}
	})

	t.Run("Delete", func(t *testing.T) {
		ts := NewTraceState()
		ts.Set("key1", "value1")
		ts.Delete("key1")

		_, ok := ts.Get("key1")
		if ok {
			t.Error("expected key to be deleted")
		}
	})

	t.Run("IsEmpty", func(t *testing.T) {
		ts := NewTraceState()
		if !ts.IsEmpty() {
			t.Error("expected empty tracestate")
		}

		ts.Set("key", "value")
		if ts.IsEmpty() {
			t.Error("expected non-empty tracestate")
		}
	})

	t.Run("String", func(t *testing.T) {
		ts := NewTraceState()
		ts.Set("vendor1", "value1")
		ts.Set("vendor2", "value2")

		s := ts.String()
		if s == "" {
			t.Error("expected non-empty string")
		}
		if !contains(s, "vendor1=value1") || !contains(s, "vendor2=value2") {
			t.Error("expected string to contain both entries")
		}
	})

	t.Run("ParseTraceState", func(t *testing.T) {
		text := "vendor1=value1,vendor2=value2"
		ts, err := ParseTraceState(text)
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}

		if ts.Len() != 2 {
			t.Errorf("expected 2 entries, got %d", ts.Len())
		}

		val, ok := ts.Get("vendor1")
		if !ok || val != "value1" {
			t.Errorf("expected value1, got %s", val)
		}
	})

	t.Run("ParseTraceState_Empty", func(t *testing.T) {
		ts, err := ParseTraceState("")
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if !ts.IsEmpty() {
			t.Error("expected empty tracestate")
		}
	})

	t.Run("Set_InvalidKey", func(t *testing.T) {
		ts := NewTraceState()
		err := ts.Set("", "value")
		if err == nil {
			t.Error("expected error for empty key")
		}
	})
}

func TestSpanContext(t *testing.T) {
	t.Run("IsValid", func(t *testing.T) {
		valid := SpanContext{
			TraceID: TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
			SpanID:  SpanID{1, 2, 3, 4, 5, 6, 7, 8},
		}
		if !valid.IsValid() {
			t.Error("expected valid span context")
		}

		invalid := SpanContext{
			TraceID: TraceID{},
			SpanID:  SpanID{1, 2, 3, 4, 5, 6, 7, 8},
		}
		if invalid.IsValid() {
			t.Error("expected invalid span context with zero trace ID")
		}

		invalid = SpanContext{
			TraceID: TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
			SpanID:  SpanID{},
		}
		if invalid.IsValid() {
			t.Error("expected invalid span context with zero span ID")
		}
	})

	t.Run("IsRemote", func(t *testing.T) {
		sc := SpanContext{Remote: true}
		if !sc.IsRemote() {
			t.Error("expected remote span context")
		}

		sc = SpanContext{Remote: false}
		if sc.IsRemote() {
			t.Error("expected local span context")
		}
	})

	t.Run("WithRemote", func(t *testing.T) {
		sc := SpanContext{}
		sc = sc.WithRemote(true)
		if !sc.IsRemote() {
			t.Error("expected remote span context")
		}
	})
}

func TestSpanContextFromContext(t *testing.T) {
	t.Run("WithSpanContext", func(t *testing.T) {
		sc := SpanContext{
			TraceID: TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
			SpanID:  SpanID{1, 2, 3, 4, 5, 6, 7, 8},
		}

		ctx := WithSpanContext(context.Background(), sc)
		retrieved := SpanContextFromContext(ctx)

		if retrieved.TraceID != sc.TraceID || retrieved.SpanID != sc.SpanID {
			t.Error("retrieved span context does not match")
		}
	})

	t.Run("SpanContextFromContext_Empty", func(t *testing.T) {
		ctx := context.Background()
		sc := SpanContextFromContext(ctx)
		if sc.IsValid() {
			t.Error("expected empty span context")
		}
	})

	t.Run("SpanContextFromContext_Nil", func(t *testing.T) {
		sc := SpanContextFromContext(nil)
		if sc.IsValid() {
			t.Error("expected empty span context for nil")
		}
	})

	t.Run("ContextWithRemoteSpanContext", func(t *testing.T) {
		sc := SpanContext{
			TraceID: TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
			SpanID:  SpanID{1, 2, 3, 4, 5, 6, 7, 8},
		}

		ctx := ContextWithRemoteSpanContext(context.Background(), sc)
		retrieved := SpanContextFromContext(ctx)

		if !retrieved.IsRemote() {
			t.Error("expected remote span context")
		}
	})
}

func TestTraceContextPropagator(t *testing.T) {
	propagator := NewTraceContextPropagator()

	t.Run("InjectExtract", func(t *testing.T) {
		sc := SpanContext{
			TraceID:    TraceID{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
			SpanID:     SpanID{0, 0, 0, 0, 0, 0, 0, 1},
			TraceFlags: FlagSampled,
		}

		ctx := WithSpanContext(context.Background(), sc)
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		traceparent := carrier.Get(TraceParentHeader)
		if traceparent == "" {
			t.Fatal("expected traceparent header")
		}

		// Extract
		ctx2 := propagator.Extract(context.Background(), carrier)
		sc2 := SpanContextFromContext(ctx2)

		if !sc2.IsValid() {
			t.Fatal("expected valid span context after extract")
		}
		if sc2.TraceID != sc.TraceID {
			t.Errorf("trace ID mismatch: %s vs %s", sc2.TraceID.String(), sc.TraceID.String())
		}
		if sc2.SpanID != sc.SpanID {
			t.Errorf("span ID mismatch: %s vs %s", sc2.SpanID.String(), sc.SpanID.String())
		}
		if sc2.TraceFlags != sc.TraceFlags {
			t.Errorf("trace flags mismatch: %v vs %v", sc2.TraceFlags, sc.TraceFlags)
		}
	})

	t.Run("Inject_InvalidSpanContext", func(t *testing.T) {
		ctx := context.Background()
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		if carrier.Get(TraceParentHeader) != "" {
			t.Error("expected no traceparent for invalid span context")
		}
	})

	t.Run("Extract_EmptyCarrier", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		ctx := propagator.Extract(context.Background(), carrier)

		sc := SpanContextFromContext(ctx)
		if sc.IsValid() {
			t.Error("expected empty span context from empty carrier")
		}
	})

	t.Run("Extract_InvalidTraceParent", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		carrier.Set(TraceParentHeader, "invalid")

		ctx := propagator.Extract(context.Background(), carrier)
		sc := SpanContextFromContext(ctx)

		if sc.IsValid() {
			t.Error("expected empty span context from invalid traceparent")
		}
	})

	t.Run("InjectExtract_WithTraceState", func(t *testing.T) {
		sc := SpanContext{
			TraceID:    TraceID{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
			SpanID:     SpanID{0, 0, 0, 0, 0, 0, 0, 1},
			TraceFlags: FlagSampled,
		}
		sc.TraceState.Set("vendor", "value")

		ctx := WithSpanContext(context.Background(), sc)
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		tracestate := carrier.Get(TraceStateHeader)
		if tracestate == "" {
			t.Error("expected tracestate header")
		}

		ctx2 := propagator.Extract(context.Background(), carrier)
		sc2 := SpanContextFromContext(ctx2)

		val, ok := sc2.TraceState.Get("vendor")
		if !ok || val != "value" {
			t.Errorf("expected tracestate vendor=value, got %s", val)
		}
	})

	t.Run("Fields", func(t *testing.T) {
		fields := propagator.Fields()
		if len(fields) != 2 {
			t.Errorf("expected 2 fields, got %d", len(fields))
		}
	})
}

func TestParseTraceParent(t *testing.T) {
	t.Run("Valid", func(t *testing.T) {
		tp := "00-0123456789abcdef0123456789abcdef-0123456789abcdef-01"
		sc, err := ParseTraceParent(tp)
		if err != nil {
			t.Fatalf("parse failed: %v", err)
		}
		if !sc.IsValid() {
			t.Error("expected valid span context")
		}
		if sc.TraceID.String() != "0123456789abcdef0123456789abcdef" {
			t.Errorf("unexpected trace ID: %s", sc.TraceID.String())
		}
		if !sc.TraceFlags.IsSampled() {
			t.Error("expected sampled flag to be set")
		}
	})

	t.Run("InvalidFormat", func(t *testing.T) {
		_, err := ParseTraceParent("invalid")
		if err == nil {
			t.Error("expected error for invalid format")
		}
	})

	t.Run("InvalidVersion", func(t *testing.T) {
		// Version FF is invalid
		_, err := ParseTraceParent("ff-0123456789abcdef0123456789abcdef-0123456789abcdef-01")
		if err == nil {
			t.Error("expected error for version ff")
		}
	})

	t.Run("ZeroTraceID", func(t *testing.T) {
		_, err := ParseTraceParent("00-00000000000000000000000000000000-0123456789abcdef-01")
		if err == nil {
			t.Error("expected error for zero trace ID")
		}
	})

	t.Run("ZeroSpanID", func(t *testing.T) {
		_, err := ParseTraceParent("00-0123456789abcdef0123456789abcdef-0000000000000000-01")
		if err == nil {
			t.Error("expected error for zero span ID")
		}
	})
}

func TestB3Propagator(t *testing.T) {
	propagator := NewB3Propagator()

	t.Run("InjectExtract_MultipleHeaders", func(t *testing.T) {
		sc := SpanContext{
			TraceID:    TraceID{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
			SpanID:     SpanID{0, 0, 0, 0, 0, 0, 0, 1},
			TraceFlags: FlagSampled,
		}

		ctx := WithSpanContext(context.Background(), sc)
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		traceID := carrier.Get(B3TraceIDHeader)
		if traceID == "" {
			t.Error("expected trace ID header")
		}

		sampled := carrier.Get(B3SampledHeader)
		if sampled != "1" {
			t.Errorf("expected sampled=1, got %s", sampled)
		}

		ctx2 := propagator.Extract(context.Background(), carrier)
		sc2 := SpanContextFromContext(ctx2)

		if !sc2.IsValid() {
			t.Fatal("expected valid span context")
		}
		if !sc2.TraceFlags.IsSampled() {
			t.Error("expected sampled flag to be set")
		}
	})

	t.Run("Extract_64BitTraceID", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		carrier.Set(B3TraceIDHeader, "0123456789abcdef")
		carrier.Set(B3SpanIDHeader, "0123456789abcdef")
		carrier.Set(B3SampledHeader, "1")

		ctx := propagator.Extract(context.Background(), carrier)
		sc := SpanContextFromContext(ctx)

		if !sc.IsValid() {
			t.Fatal("expected valid span context from 64-bit trace ID")
		}
	})

	t.Run("Fields", func(t *testing.T) {
		fields := propagator.Fields()
		if len(fields) != 5 {
			t.Errorf("expected 5 fields, got %d", len(fields))
		}
	})
}

func TestB3SingleHeaderPropagator(t *testing.T) {
	propagator := NewB3SingleHeaderPropagator()

	t.Run("InjectExtract_SingleHeader", func(t *testing.T) {
		sc := SpanContext{
			TraceID:    TraceID{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
			SpanID:     SpanID{0, 0, 0, 0, 0, 0, 0, 1},
			TraceFlags: FlagSampled,
		}

		ctx := WithSpanContext(context.Background(), sc)
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		header := carrier.Get(B3SingleHeaderName)
		if header == "" {
			t.Fatal("expected b3 header")
		}

		ctx2 := propagator.Extract(context.Background(), carrier)
		sc2 := SpanContextFromContext(ctx2)

		if !sc2.IsValid() {
			t.Error("expected valid span context")
		}
	})

	t.Run("Fields", func(t *testing.T) {
		fields := propagator.Fields()
		if len(fields) != 1 {
			t.Errorf("expected 1 field, got %d", len(fields))
		}
	})
}

func TestJaegerPropagator(t *testing.T) {
	propagator := NewJaegerPropagator()

	t.Run("InjectExtract", func(t *testing.T) {
		sc := SpanContext{
			TraceID:    TraceID{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
			SpanID:     SpanID{0, 0, 0, 0, 0, 0, 0, 1},
			TraceFlags: FlagSampled,
		}

		ctx := WithSpanContext(context.Background(), sc)
		carrier := make(TextMapCarrier)

		propagator.Inject(ctx, carrier)

		header := carrier.Get(JaegerHeader)
		if header == "" {
			t.Fatal("expected uber-trace-id header")
		}

		ctx2 := propagator.Extract(context.Background(), carrier)
		sc2 := SpanContextFromContext(ctx2)

		if !sc2.IsValid() {
			t.Error("expected valid span context")
		}
		if !sc2.TraceFlags.IsSampled() {
			t.Error("expected sampled flag to be set")
		}
	})

	t.Run("Extract_InvalidFormat", func(t *testing.T) {
		carrier := make(TextMapCarrier)
		carrier.Set(JaegerHeader, "invalid")

		ctx := propagator.Extract(context.Background(), carrier)
		sc := SpanContextFromContext(ctx)

		if sc.IsValid() {
			t.Error("expected invalid span context")
		}
	})

	t.Run("Fields", func(t *testing.T) {
		fields := propagator.Fields()
		if len(fields) != 1 {
			t.Errorf("expected 1 field, got %d", len(fields))
		}
	})
}

func TestPropagatorRegistry(t *testing.T) {
	registry := NewPropagatorRegistry()

	t.Run("RegisterGet", func(t *testing.T) {
		p := NewTraceContextPropagator()
		registry.Register("test", p)

		got, ok := registry.Get("test")
		if !ok {
			t.Fatal("expected to find registered propagator")
		}
		if got != p {
			t.Error("retrieved propagator does not match")
		}
	})

	t.Run("Get_NotFound", func(t *testing.T) {
		_, ok := registry.Get("nonexistent")
		if ok {
			t.Error("expected not to find unregistered propagator")
		}
	})

	t.Run("Unregister", func(t *testing.T) {
		registry.Register("to-remove", NewTraceContextPropagator())
		registry.Unregister("to-remove")

		_, ok := registry.Get("to-remove")
		if ok {
			t.Error("expected propagator to be unregistered")
		}
	})

	t.Run("Names", func(t *testing.T) {
		registry := NewPropagatorRegistry()
		registry.Register("a", NewTraceContextPropagator())
		registry.Register("b", NewB3Propagator())

		names := registry.Names()
		if len(names) != 2 {
			t.Errorf("expected 2 names, got %d", len(names))
		}
	})
}

func TestDefaultRegistry(t *testing.T) {
	tests := []struct {
		name string
	}{
		{"tracecontext"},
		{"b3"},
		{"b3single"},
		{"jaeger"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			p, ok := GetPropagator(tt.name)
			if !ok {
				t.Errorf("expected %s propagator to be registered", tt.name)
			}
			if p == nil {
				t.Errorf("expected non-nil propagator for %s", tt.name)
			}
		})
	}
}

func TestExtractTextMap(t *testing.T) {
	sc := SpanContext{
		TraceID:    TraceID{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
		SpanID:     SpanID{0, 0, 0, 0, 0, 0, 0, 1},
		TraceFlags: FlagSampled,
	}

	carrier := make(TextMapCarrier)
	InjectTextMap(sc, carrier)

	extracted := ExtractTextMap(carrier)

	if !extracted.IsValid() {
		t.Fatal("expected valid span context")
	}
	if extracted.TraceID != sc.TraceID {
		t.Error("trace ID mismatch")
	}
}

// Helper function
func contains(s, substr string) bool {
	return len(s) >= len(substr) && (s == substr || len(s) > len(substr) && containsAt(s, substr, 0))
}

func containsAt(s, substr string, start int) bool {
	if start+len(substr) > len(s) {
		return false
	}
	if s[start:start+len(substr)] == substr {
		return true
	}
	return containsAt(s, substr, start+1)
}

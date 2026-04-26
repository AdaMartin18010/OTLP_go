// Package propagation provides unit tests for all propagator implementations.
//
// 测试覆盖目标 >= 90%，包含 W3C 官方测试向量、边界条件和错误处理。
package propagation

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	otelbaggage "go.opentelemetry.io/otel/baggage"
	"go.opentelemetry.io/otel/trace"
)

// ============================================================================
// Helper utilities
// ============================================================================

// makeSpanContext creates a trace.SpanContext for testing.
func makeSpanContext(traceID, spanID string, sampled bool, flags byte) trace.SpanContext {
	tid, _ := trace.TraceIDFromHex(traceID)
	sid, _ := trace.SpanIDFromHex(spanID)
	tf := trace.TraceFlags(flags)
	if sampled {
		tf = tf.WithSampled(true)
	}
	return trace.NewSpanContext(trace.SpanContextConfig{
		TraceID:    tid,
		SpanID:     sid,
		TraceFlags: tf,
		Remote:     false,
	})
}

// carrier is a simple in-memory TextMapCarrier for tests.
type carrier map[string]string

func (c carrier) Get(key string) string { return c[key] }
func (c carrier) Set(key, value string) { c[key] = value }
func (c carrier) Keys() []string {
	keys := make([]string, 0, len(c))
	for k := range c {
		keys = append(keys, k)
	}
	return keys
}

// ============================================================================
// W3C Propagator Tests
// ============================================================================

func TestW3CInject(t *testing.T) {
	w3c := W3C{}
	ctx := context.Background()

	t.Run("valid span context", func(t *testing.T) {
		sc := makeSpanContext(
			"4bf92f3577b34da6a3ce929d0e0e4736",
			"00f067aa0ba902b7",
			true,
			0x01,
		)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		w3c.Inject(ctx, c)

		assert.Equal(t, "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01", c["traceparent"])
	})

	t.Run("with random flag", func(t *testing.T) {
		sc := makeSpanContext(
			"4bf92f3577b34da6a3ce929d0e0e4736",
			"00f067aa0ba902b7",
			true,
			0x03, // sampled + random
		)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		w3c.Inject(ctx, c)

		assert.Equal(t, "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-03", c["traceparent"])
	})

	t.Run("invalid span context skipped", func(t *testing.T) {
		ctx = trace.ContextWithSpanContext(ctx, trace.SpanContext{})
		c := make(carrier)
		w3c.Inject(ctx, c)

		assert.Empty(t, c["traceparent"])
	})

	t.Run("with tracestate", func(t *testing.T) {
		ts, _ := trace.ParseTraceState("vendor=key1,other=key2")
		sc := makeSpanContext(
			"4bf92f3577b34da6a3ce929d0e0e4736",
			"00f067aa0ba902b7",
			false,
			0x00,
		).WithTraceState(ts)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		w3c.Inject(ctx, c)

		assert.Equal(t, "vendor=key1,other=key2", c["tracestate"])
	})
}

func TestW3CExtract(t *testing.T) {
	w3c := W3C{}

	t.Run("official test vector - sampled", func(t *testing.T) {
		c := carrier{"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736", sc.TraceID().String())
		assert.Equal(t, "00f067aa0ba902b7", sc.SpanID().String())
		assert.True(t, sc.IsSampled())
		assert.True(t, sc.IsRemote())
	})

	t.Run("official test vector - not sampled", func(t *testing.T) {
		c := carrier{"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-00"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.False(t, sc.IsSampled())
	})

	t.Run("with random flag", func(t *testing.T) {
		c := carrier{"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-03"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
		assert.Equal(t, trace.TraceFlags(0x03), sc.TraceFlags())
	})

	t.Run("with tracestate", func(t *testing.T) {
		c := carrier{
			"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01",
			"tracestate":  "vendor=key1,other=key2",
		}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		ts := sc.TraceState()
		assert.Equal(t, "key1", ts.Get("vendor"))
		assert.Equal(t, "key2", ts.Get("other"))
	})

	t.Run("missing traceparent", func(t *testing.T) {
		c := carrier{}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid format - wrong parts count", func(t *testing.T) {
		c := carrier{"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid version - 255", func(t *testing.T) {
		c := carrier{"traceparent": "ff-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid trace-id - all zeros", func(t *testing.T) {
		c := carrier{"traceparent": "00-00000000000000000000000000000000-00f067aa0ba902b7-01"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid span-id - all zeros", func(t *testing.T) {
		c := carrier{"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-0000000000000000-01"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid flags - version 0 with flags > 0x03", func(t *testing.T) {
		c := carrier{"traceparent": "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-ff"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("uppercase hex rejected", func(t *testing.T) {
		c := carrier{"traceparent": "00-4BF92F3577B34DA6A3CE929D0E0E4736-00F067AA0BA902B7-01"}
		ctx := w3c.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})
}

func TestW3CSanitizeTraceState(t *testing.T) {
	w3c := W3C{}

	t.Run("valid tracestate passes through", func(t *testing.T) {
		input := "vendor=key1,other=key2"
		result := w3c.sanitizeTraceState(input)
		assert.Equal(t, input, result)
	})

	t.Run("PII email detected and cleared", func(t *testing.T) {
		input := "vendor=key1,user=alice@example.com"
		result := w3c.sanitizeTraceState(input)
		assert.Equal(t, "", result)
	})

	t.Run("PII phone detected and cleared", func(t *testing.T) {
		input := "vendor=key1,contact=555-123-4567"
		result := w3c.sanitizeTraceState(input)
		assert.Equal(t, "", result)
	})

	t.Run("PII SSN detected and cleared", func(t *testing.T) {
		input := "vendor=key1,ssn=123-45-6789"
		result := w3c.sanitizeTraceState(input)
		assert.Equal(t, "", result)
	})

	t.Run("invalid characters filtered", func(t *testing.T) {
		input := "vendor=key1, bad==key"
		result := w3c.sanitizeTraceState(input)
		assert.Equal(t, "vendor=key1", result)
	})

	t.Run("vendor priority on truncation", func(t *testing.T) {
		var entries []string
		for i := 0; i < 20; i++ {
			entries = append(entries, fmt.Sprintf("vendor%d@system=value%d", i, i))
		}
		for i := 0; i < 20; i++ {
			entries = append(entries, fmt.Sprintf("key%d=value%d", i, i))
		}
		input := strings.Join(entries, ",")
		result := w3c.sanitizeTraceState(input)

		parts := strings.Split(result, ",")
		assert.LessOrEqual(t, len(parts), maxTraceStateEntries)
		// Verify vendor entries are prioritized (first entries should contain @)
		firstKey := strings.SplitN(parts[0], "=", 2)[0]
		assert.Contains(t, firstKey, "@")
	})

	t.Run("empty input", func(t *testing.T) {
		result := w3c.sanitizeTraceState("")
		assert.Equal(t, "", result)
	})
}

func TestW3CFields(t *testing.T) {
	w3c := W3C{}
	fields := w3c.Fields()
	assert.Equal(t, []string{"traceparent", "tracestate"}, fields)
}

// ============================================================================
// B3 Propagator Tests
// ============================================================================

func TestB3SingleInject(t *testing.T) {
	b3 := B3Single{}
	ctx := context.Background()

	t.Run("sampled", func(t *testing.T) {
		sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", true, 0x01)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		b3.Inject(ctx, c)

		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1", c["b3"])
	})

	t.Run("not sampled", func(t *testing.T) {
		sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", false, 0x00)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		b3.Inject(ctx, c)

		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-0", c["b3"])
	})

	t.Run("invalid span context skipped", func(t *testing.T) {
		ctx = trace.ContextWithSpanContext(ctx, trace.SpanContext{})
		c := make(carrier)
		b3.Inject(ctx, c)
		assert.Empty(t, c["b3"])
	})
}

func TestB3SingleExtract(t *testing.T) {
	b3 := B3Single{}

	t.Run("valid sampled", func(t *testing.T) {
		c := carrier{"b3": "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736", sc.TraceID().String())
		assert.Equal(t, "00f067aa0ba902b7", sc.SpanID().String())
	})

	t.Run("valid not sampled", func(t *testing.T) {
		c := carrier{"b3": "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-0"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.False(t, sc.IsSampled())
	})

	t.Run("debug flag treated as sampled", func(t *testing.T) {
		c := carrier{"b3": "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-d"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
	})

	t.Run("64-bit trace id padded", func(t *testing.T) {
		c := carrier{"b3": "a3ce929d0e0e4736-00f067aa0ba902b7-1"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.Equal(t, "0000000000000000a3ce929d0e0e4736", sc.TraceID().String())
	})

	t.Run("missing header", func(t *testing.T) {
		c := carrier{}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("sampling only - 0", func(t *testing.T) {
		c := carrier{"b3": "0"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid format", func(t *testing.T) {
		c := carrier{"b3": "invalid"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})
}

func TestB3MultiInject(t *testing.T) {
	b3 := B3Multi{}
	ctx := context.Background()

	t.Run("sampled", func(t *testing.T) {
		sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", true, 0x01)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		b3.Inject(ctx, c)

		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736", c["X-B3-TraceId"])
		assert.Equal(t, "00f067aa0ba902b7", c["X-B3-SpanId"])
		assert.Equal(t, "1", c["X-B3-Sampled"])
	})

	t.Run("not sampled", func(t *testing.T) {
		sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", false, 0x00)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		b3.Inject(ctx, c)

		assert.Equal(t, "0", c["X-B3-Sampled"])
	})
}

func TestB3MultiExtract(t *testing.T) {
	b3 := B3Multi{}

	t.Run("valid sampled", func(t *testing.T) {
		c := carrier{
			"X-B3-TraceId": "4bf92f3577b34da6a3ce929d0e0e4736",
			"X-B3-SpanId":  "00f067aa0ba902b7",
			"X-B3-Sampled": "1",
		}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
	})

	t.Run("valid not sampled", func(t *testing.T) {
		c := carrier{
			"X-B3-TraceId": "4bf92f3577b34da6a3ce929d0e0e4736",
			"X-B3-SpanId":  "00f067aa0ba902b7",
			"X-B3-Sampled": "0",
		}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.False(t, sc.IsSampled())
	})

	t.Run("debug flag forces sampled", func(t *testing.T) {
		c := carrier{
			"X-B3-TraceId": "4bf92f3577b34da6a3ce929d0e0e4736",
			"X-B3-SpanId":  "00f067aa0ba902b7",
			"X-B3-Flags":   "1",
		}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
	})

	t.Run("missing trace id", func(t *testing.T) {
		c := carrier{"X-B3-SpanId": "00f067aa0ba902b7"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("missing span id", func(t *testing.T) {
		c := carrier{"X-B3-TraceId": "4bf92f3577b34da6a3ce929d0e0e4736"}
		ctx := b3.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})
}

func TestB3Fields(t *testing.T) {
	assert.Equal(t, []string{"b3"}, B3Single{}.Fields())
	assert.Equal(t, []string{"X-B3-TraceId", "X-B3-SpanId", "X-B3-ParentSpanId", "X-B3-Sampled", "X-B3-Flags"}, B3Multi{}.Fields())
}

// ============================================================================
// Jaeger Propagator Tests
// ============================================================================

func TestJaegerInject(t *testing.T) {
	j := Jaeger{}
	ctx := context.Background()

	t.Run("sampled", func(t *testing.T) {
		sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", true, 0x01)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		j.Inject(ctx, c)

		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:1", c["uber-trace-id"])
	})

	t.Run("not sampled", func(t *testing.T) {
		sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", false, 0x00)
		ctx = trace.ContextWithSpanContext(ctx, sc)
		c := make(carrier)
		j.Inject(ctx, c)

		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:0", c["uber-trace-id"])
	})

	t.Run("invalid span context skipped", func(t *testing.T) {
		ctx = trace.ContextWithSpanContext(ctx, trace.SpanContext{})
		c := make(carrier)
		j.Inject(ctx, c)
		assert.Empty(t, c["uber-trace-id"])
	})
}

func TestJaegerExtract(t *testing.T) {
	j := Jaeger{}

	t.Run("valid sampled", func(t *testing.T) {
		c := carrier{"uber-trace-id": "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:1"}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
		assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736", sc.TraceID().String())
		assert.Equal(t, "00f067aa0ba902b7", sc.SpanID().String())
	})

	t.Run("valid not sampled", func(t *testing.T) {
		c := carrier{"uber-trace-id": "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:0"}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.False(t, sc.IsSampled())
	})

	t.Run("debug flag forces sampled", func(t *testing.T) {
		c := carrier{"uber-trace-id": "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:2"}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.True(t, sc.IsSampled())
	})

	t.Run("64-bit trace id padded", func(t *testing.T) {
		c := carrier{"uber-trace-id": "a3ce929d0e0e4736:00f067aa0ba902b7:0:1"}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.True(t, sc.IsValid())
		assert.Equal(t, "0000000000000000a3ce929d0e0e4736", sc.TraceID().String())
	})

	t.Run("missing header", func(t *testing.T) {
		c := carrier{}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("wrong part count", func(t *testing.T) {
		c := carrier{"uber-trace-id": "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:1"}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})

	t.Run("invalid trace id length", func(t *testing.T) {
		c := carrier{"uber-trace-id": "bad:00f067aa0ba902b7:0:1"}
		ctx := j.Extract(context.Background(), c)
		sc := trace.SpanContextFromContext(ctx)

		assert.False(t, sc.IsValid())
	})
}

func TestJaegerFields(t *testing.T) {
	j := Jaeger{}
	assert.Equal(t, []string{"uber-trace-id"}, j.Fields())
}

// ============================================================================
// Baggage Propagator Tests
// ============================================================================

func TestBaggageInject(t *testing.T) {
	b := Baggage{}
	ctx := context.Background()

	t.Run("with baggage", func(t *testing.T) {
		member, err := otelbaggage.NewMemberRaw("key1", "value1")
		require.NoError(t, err)
		bag, err := otelbaggage.New(member)
		require.NoError(t, err)
		ctx = otelbaggage.ContextWithBaggage(ctx, bag)

		c := make(carrier)
		b.Inject(ctx, c)
		assert.Equal(t, "key1=value1", c["baggage"])
	})

	t.Run("empty baggage", func(t *testing.T) {
		emptyCtx := context.Background()
		c := make(carrier)
		b.Inject(emptyCtx, c)
		assert.Empty(t, c["baggage"])
	})
}

func TestBaggageExtract(t *testing.T) {
	b := Baggage{}

	t.Run("valid baggage", func(t *testing.T) {
		c := carrier{"baggage": "key1=value1,key2=value2"}
		ctx := b.Extract(context.Background(), c)
		bag := otelbaggage.FromContext(ctx)

		assert.Equal(t, "value1", bag.Member("key1").Value())
		assert.Equal(t, "value2", bag.Member("key2").Value())
	})

	t.Run("missing header", func(t *testing.T) {
		c := carrier{}
		ctx := b.Extract(context.Background(), c)
		bag := otelbaggage.FromContext(ctx)

		assert.Equal(t, 0, len(bag.Members()))
	})

	t.Run("invalid baggage ignored", func(t *testing.T) {
		c := carrier{"baggage": "bad baggage without equals"}
		ctx := b.Extract(context.Background(), c)
		bag := otelbaggage.FromContext(ctx)

		assert.Equal(t, 0, len(bag.Members()))
	})
}

func TestBaggageFields(t *testing.T) {
	b := Baggage{}
	assert.Equal(t, []string{"baggage"}, b.Fields())
}

// ============================================================================
// BaggageManager Tests
// ============================================================================

func TestBaggageManager(t *testing.T) {
	bm := NewBaggageManager()
	ctx := context.Background()

	t.Run("Set and Get", func(t *testing.T) {
		var err error
		ctx, err = bm.Set(ctx, "key1", "value1")
		require.NoError(t, err)

		val, ok := bm.Get(ctx, "key1")
		assert.True(t, ok)
		assert.Equal(t, "value1", val)
	})

	t.Run("Get missing key", func(t *testing.T) {
		_, ok := bm.Get(ctx, "missing")
		assert.False(t, ok)
	})

	t.Run("Update existing key", func(t *testing.T) {
		var err error
		ctx, err = bm.Set(ctx, "key1", "updated")
		require.NoError(t, err)

		val, ok := bm.Get(ctx, "key1")
		assert.True(t, ok)
		assert.Equal(t, "updated", val)
	})

	t.Run("Remove key", func(t *testing.T) {
		ctx = bm.Remove(ctx, "key1")
		_, ok := bm.Get(ctx, "key1")
		assert.False(t, ok)
	})

	t.Run("List", func(t *testing.T) {
		var err error
		ctx, err = bm.Set(ctx, "a", "1")
		require.NoError(t, err)
		ctx, err = bm.Set(ctx, "b", "2")
		require.NoError(t, err)

		list := bm.List(ctx)
		assert.Equal(t, "1", list["a"])
		assert.Equal(t, "2", list["b"])
	})

	t.Run("Clear", func(t *testing.T) {
		ctx = bm.Clear(ctx)
		list := bm.List(ctx)
		assert.Empty(t, list)
	})

	t.Run("invalid key rejected", func(t *testing.T) {
		_, err := bm.Set(ctx, "key with spaces", "value")
		assert.Error(t, err)
	})

	t.Run("FilterPII removes email", func(t *testing.T) {
		var err error
		ctx, err = bm.Set(ctx, "safe", "ok")
		require.NoError(t, err)
		ctx, err = bm.Set(ctx, "pii", "alice@example.com")
		require.NoError(t, err)

		ctx = bm.FilterPII(ctx)
		list := bm.List(ctx)
		assert.Equal(t, "ok", list["safe"])
		assert.NotContains(t, list, "pii")
	})
}

// ============================================================================
// TraceState validation helpers
// ============================================================================

func TestIsValidTraceStateKey(t *testing.T) {
	tests := []struct {
		key   string
		valid bool
	}{
		{"vendor", true},
		{"tenant@system", true},
		{"key1", true},
		{"", false},
		{"Key", false},           // uppercase
		{"key space", false},     // space
		{"a@b@c", false},         // multiple @
		{"@vendor", false},       // leading @
		{"vendor@", false},       // trailing @
		{"123", true},            // digits ok at start for tenant
	}

	for _, tt := range tests {
		t.Run(tt.key, func(t *testing.T) {
			assert.Equal(t, tt.valid, isValidTraceStateKey(tt.key), "key: %s", tt.key)
		})
	}
}

func TestIsValidTraceStateValue(t *testing.T) {
	tests := []struct {
		val   string
		valid bool
	}{
		{"value1", true},
		{"value with spaces", true},
		{"", false},
		{"value=bad", false},     // = not allowed
		{"value,bad", false},     // , not allowed
		{"value\x00bad", false},  // null not allowed
		{"value\x7fbad", false},  // DEL not allowed
		{"value ", false},        // trailing space not allowed as last char
		{"value", true},          // single char ok
	}

	for _, tt := range tests {
		t.Run(fmt.Sprintf("value_%q", tt.val), func(t *testing.T) {
			assert.Equal(t, tt.valid, isValidTraceStateValue(tt.val), "val: %q", tt.val)
		})
	}
}

// ============================================================================
// Round-trip tests
// ============================================================================

func TestW3CRoundTrip(t *testing.T) {
	w3c := W3C{}
	sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", true, 0x03)

	ctx := trace.ContextWithSpanContext(context.Background(), sc)
	c := make(carrier)
	w3c.Inject(ctx, c)

	extractedCtx := w3c.Extract(context.Background(), c)
	extractedSC := trace.SpanContextFromContext(extractedCtx)

	assert.Equal(t, sc.TraceID(), extractedSC.TraceID())
	assert.Equal(t, sc.SpanID(), extractedSC.SpanID())
	assert.Equal(t, sc.TraceFlags(), extractedSC.TraceFlags())
}

func TestB3SingleRoundTrip(t *testing.T) {
	b3 := B3Single{}
	sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", true, 0x01)

	ctx := trace.ContextWithSpanContext(context.Background(), sc)
	c := make(carrier)
	b3.Inject(ctx, c)

	extractedCtx := b3.Extract(context.Background(), c)
	extractedSC := trace.SpanContextFromContext(extractedCtx)

	assert.Equal(t, sc.TraceID(), extractedSC.TraceID())
	assert.Equal(t, sc.SpanID(), extractedSC.SpanID())
	assert.Equal(t, sc.IsSampled(), extractedSC.IsSampled())
}

func TestB3MultiRoundTrip(t *testing.T) {
	b3 := B3Multi{}
	sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", false, 0x00)

	ctx := trace.ContextWithSpanContext(context.Background(), sc)
	c := make(carrier)
	b3.Inject(ctx, c)

	extractedCtx := b3.Extract(context.Background(), c)
	extractedSC := trace.SpanContextFromContext(extractedCtx)

	assert.Equal(t, sc.TraceID(), extractedSC.TraceID())
	assert.Equal(t, sc.SpanID(), extractedSC.SpanID())
	assert.Equal(t, sc.IsSampled(), extractedSC.IsSampled())
}

func TestJaegerRoundTrip(t *testing.T) {
	j := Jaeger{}
	sc := makeSpanContext("4bf92f3577b34da6a3ce929d0e0e4736", "00f067aa0ba902b7", true, 0x01)

	ctx := trace.ContextWithSpanContext(context.Background(), sc)
	c := make(carrier)
	j.Inject(ctx, c)

	extractedCtx := j.Extract(context.Background(), c)
	extractedSC := trace.SpanContextFromContext(extractedCtx)

	assert.Equal(t, sc.TraceID(), extractedSC.TraceID())
	assert.Equal(t, sc.SpanID(), extractedSC.SpanID())
	assert.Equal(t, sc.IsSampled(), extractedSC.IsSampled())
}

func TestBaggageRoundTrip(t *testing.T) {
	b := Baggage{}
	member, _ := otelbaggage.NewMemberRaw("key1", "value1")
	bag, _ := otelbaggage.New(member)
	ctx := otelbaggage.ContextWithBaggage(context.Background(), bag)

	c := make(carrier)
	b.Inject(ctx, c)

	extractedCtx := b.Extract(context.Background(), c)
	extractedBag := otelbaggage.FromContext(extractedCtx)

	assert.Equal(t, "value1", extractedBag.Member("key1").Value())
}

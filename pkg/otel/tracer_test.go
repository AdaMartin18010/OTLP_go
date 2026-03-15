package otel

import (
	"context"
	"errors"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/noop"
)

func TestNewTracerWrapper(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	require.NotNil(t, tracer)
	assert.Equal(t, "test-service", tracer.name)
	assert.NotNil(t, tracer.tracer)
}

func TestTracerWrapper_Start(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	ctx, span := tracer.Start(context.Background(), "test-span")
	require.NotNil(t, ctx)
	require.NotNil(t, span)
	defer span.End()
}

func TestTracerWrapper_NewSpanBuilder(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	builder := tracer.NewSpanBuilder("test-span")
	require.NotNil(t, builder)
	assert.Equal(t, tracer, builder.tracer)
	assert.Equal(t, "test-span", builder.name)
	assert.Equal(t, trace.SpanKindInternal, builder.kind)
	assert.Empty(t, builder.attributes)
}

func TestSpanBuilder_WithKind(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	builder := tracer.NewSpanBuilder("test-span")

	builder.WithKind(trace.SpanKindServer)
	assert.Equal(t, trace.SpanKindServer, builder.kind)

	builder.WithKind(trace.SpanKindClient)
	assert.Equal(t, trace.SpanKindClient, builder.kind)
}

func TestSpanBuilder_WithAttribute(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	builder := tracer.NewSpanBuilder("test-span")

	builder.WithAttribute("key1", "value1")
	builder.WithAttribute("key2", 123)
	builder.WithAttribute("key3", true)

	assert.Len(t, builder.attributes, 3)
}

func TestSpanBuilder_WithAttributes(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	builder := tracer.NewSpanBuilder("test-span")

	attrs := map[string]interface{}{
		"key1": "value1",
		"key2": 123,
		"key3": true,
	}
	builder.WithAttributes(attrs)

	assert.Len(t, builder.attributes, 3)
}

func TestSpanBuilder_Start(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	builder := tracer.NewSpanBuilder("test-span").
		WithKind(trace.SpanKindServer).
		WithAttribute("key", "value")

	ctx, span := builder.Start(context.Background())
	require.NotNil(t, ctx)
	require.NotNil(t, span)
	defer span.End()
}

func TestSpanBuilder_Run(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	t.Run("successful function", func(t *testing.T) {
		builder := tracer.NewSpanBuilder("test-span")
		executed := false

		err := builder.Run(context.Background(), func(ctx context.Context) error {
			executed = true
			return nil
		})

		assert.NoError(t, err)
		assert.True(t, executed)
	})

	t.Run("function with error", func(t *testing.T) {
		builder := tracer.NewSpanBuilder("test-span")
		testErr := errors.New("test error")

		err := builder.Run(context.Background(), func(ctx context.Context) error {
			return testErr
		})

		assert.Error(t, err)
		assert.Equal(t, testErr, err)
	})
}

func TestSpanContext_SetAttribute(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)
	require.NotNil(t, sc)

	result := sc.SetAttribute("key", "value")
	assert.Equal(t, sc, result)
}

func TestSpanContext_SetAttributes(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)

	attrs := map[string]interface{}{
		"key1": "value1",
		"key2": 123,
	}
	result := sc.SetAttributes(attrs)
	assert.Equal(t, sc, result)
}

func TestSpanContext_AddEvent(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)

	result := sc.AddEvent("test-event", attribute.String("key", "value"))
	assert.Equal(t, sc, result)
}

func TestSpanContext_RecordError(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)

	t.Run("record error", func(t *testing.T) {
		testErr := errors.New("test error")
		result := sc.RecordError(testErr)
		assert.Equal(t, sc, result)
	})

	t.Run("record nil error", func(t *testing.T) {
		result := sc.RecordError(nil)
		assert.Equal(t, sc, result)
	})
}

func TestSpanContext_SetStatus(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)

	result := sc.SetStatus(codes.Ok, "success")
	assert.Equal(t, sc, result)
}

func TestSpanContext_IsRecording(t *testing.T) {
	t.Run("with recording span", func(t *testing.T) {
		provider := noop.NewTracerProvider()
		tracer := NewTracerWrapper(provider, "test-service")
		ctx, span := tracer.Start(context.Background(), "test-span")
		defer span.End()

		sc := CurrentSpanContext(ctx)
		assert.False(t, sc.IsRecording()) // noop span doesn't record
	})

	t.Run("with nil span", func(t *testing.T) {
		sc := &SpanContext{Span: nil}
		assert.False(t, sc.IsRecording())
	})
}

func TestSpanContext_TraceID(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)
	traceID := sc.TraceID()
	assert.NotEmpty(t, traceID)
}

func TestSpanContext_SpanID(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := CurrentSpanContext(ctx)
	spanID := sc.SpanID()
	assert.NotEmpty(t, spanID)
}

func TestSpanContext_NilSpan(t *testing.T) {
	sc := &SpanContext{Span: nil, Ctx: context.Background()}

	// All operations should handle nil span gracefully
	sc.SetAttribute("key", "value")
	sc.SetAttributes(map[string]interface{}{"key": "value"})
	sc.AddEvent("event")
	sc.RecordError(errors.New("error"))
	sc.SetStatus(codes.Error, "error")
	sc.End()

	assert.False(t, sc.IsRecording())
	assert.Empty(t, sc.TraceID())
	assert.Empty(t, sc.SpanID())
}

func TestTracerWrapper_TraceFunc(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	t.Run("successful execution", func(t *testing.T) {
		executed := false
		err := tracer.TraceFunc(context.Background(), "test-span", func(ctx context.Context) error {
			executed = true
			return nil
		})

		assert.NoError(t, err)
		assert.True(t, executed)
	})

	t.Run("execution with error", func(t *testing.T) {
		testErr := errors.New("test error")
		err := tracer.TraceFunc(context.Background(), "test-span", func(ctx context.Context) error {
			return testErr
		})

		assert.Error(t, err)
		assert.Equal(t, testErr, err)
	})
}

func TestTraceFuncWithResult(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	t.Run("successful execution", func(t *testing.T) {
		result, err := TraceFuncWithResult(tracer, context.Background(), "test-span", func(ctx context.Context) (string, error) {
			return "success", nil
		})

		assert.NoError(t, err)
		assert.Equal(t, "success", result)
	})

	t.Run("execution with error", func(t *testing.T) {
		testErr := errors.New("test error")
		result, err := TraceFuncWithResult(tracer, context.Background(), "test-span", func(ctx context.Context) (string, error) {
			return "", testErr
		})

		assert.Error(t, err)
		assert.Empty(t, result)
	})

	t.Run("execution with int result", func(t *testing.T) {
		result, err := TraceFuncWithResult(tracer, context.Background(), "test-span", func(ctx context.Context) (int, error) {
			return 42, nil
		})

		assert.NoError(t, err)
		assert.Equal(t, 42, result)
	})
}

func TestTracerWrapper_SpanKinds(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")

	t.Run("ServerSpan", func(t *testing.T) {
		ctx, span := tracer.ServerSpan(context.Background(), "server-span")
		require.NotNil(t, ctx)
		require.NotNil(t, span)
		span.End()
	})

	t.Run("ClientSpan", func(t *testing.T) {
		ctx, span := tracer.ClientSpan(context.Background(), "client-span")
		require.NotNil(t, ctx)
		require.NotNil(t, span)
		span.End()
	})

	t.Run("ProducerSpan", func(t *testing.T) {
		ctx, span := tracer.ProducerSpan(context.Background(), "producer-span")
		require.NotNil(t, ctx)
		require.NotNil(t, span)
		span.End()
	})

	t.Run("ConsumerSpan", func(t *testing.T) {
		ctx, span := tracer.ConsumerSpan(context.Background(), "consumer-span")
		require.NotNil(t, ctx)
		require.NotNil(t, span)
		span.End()
	})

	t.Run("InternalSpan", func(t *testing.T) {
		ctx, span := tracer.InternalSpan(context.Background(), "internal-span")
		require.NotNil(t, ctx)
		require.NotNil(t, span)
		span.End()
	})
}

func TestCreateAttribute(t *testing.T) {
	tests := []struct {
		name  string
		key   string
		value interface{}
		want  attribute.KeyValue
	}{
		{"string", "key", "value", attribute.String("key", "value")},
		{"int", "key", 42, attribute.Int("key", 42)},
		{"int64", "key", int64(42), attribute.Int64("key", 42)},
		{"float64", "key", 3.14, attribute.Float64("key", 3.14)},
		{"bool", "key", true, attribute.Bool("key", true)},
		{"duration", "key", time.Second, attribute.String("key", "1s")},
		{"string slice", "key", []string{"a", "b"}, attribute.StringSlice("key", []string{"a", "b"})},
		{"int slice", "key", []int{1, 2}, attribute.IntSlice("key", []int{1, 2})},
		{"int64 slice", "key", []int64{1, 2}, attribute.Int64Slice("key", []int64{1, 2})},
		{"float64 slice", "key", []float64{1.0, 2.0}, attribute.Float64Slice("key", []float64{1.0, 2.0})},
		{"bool slice", "key", []bool{true, false}, attribute.BoolSlice("key", []bool{true, false})},
		{"unknown", "key", struct{}{}, attribute.String("key", "{}")},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := createAttribute(tt.key, tt.value)
			assert.Equal(t, tt.want, got)
		})
	}
}

type testStringer struct{}

func (t testStringer) String() string { return "test-stringer" }

func TestCreateAttribute_WithStringer(t *testing.T) {
	got := createAttribute("key", testStringer{})
	assert.Equal(t, attribute.String("key", "test-stringer"), got)
}

func TestTracerFromContext(t *testing.T) {
	t.Run("no tracer in context", func(t *testing.T) {
		tracer := TracerFromContext(context.Background(), "test")
		assert.Nil(t, tracer)
	})

	t.Run("with tracer in context", func(t *testing.T) {
		provider := noop.NewTracerProvider()
		ctx := ContextWithTracerProvider(context.Background(), provider)

		tracer := TracerFromContext(ctx, "test")
		assert.NotNil(t, tracer)
	})
}

func TestContextWithTracerProvider(t *testing.T) {
	provider := noop.NewTracerProvider()
	ctx := ContextWithTracerProvider(context.Background(), provider)

	// Verify the provider is in the context
	retrievedProvider, ok := ctx.Value(tracerProviderKey{}).(trace.TracerProvider)
	assert.True(t, ok)
	assert.Equal(t, provider, retrievedProvider)
}

func TestSpanFromContext(t *testing.T) {
	t.Run("no span in context", func(t *testing.T) {
		span := SpanFromContext(context.Background())
		assert.NotNil(t, span)
	})

	t.Run("with span in context", func(t *testing.T) {
		provider := noop.NewTracerProvider()
		tracer := NewTracerWrapper(provider, "test")
		ctx, span := tracer.Start(context.Background(), "test-span")

		retrievedSpan := SpanFromContext(ctx)
		assert.Equal(t, span, retrievedSpan)
		span.End()
	})
}

func TestContextWithSpan(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test")
	_, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	ctx := ContextWithSpan(context.Background(), span)
	retrievedSpan := SpanFromContext(ctx)
	assert.Equal(t, span, retrievedSpan)
}

func TestExtractSpanContext(t *testing.T) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	sc := ExtractSpanContext(ctx)
	assert.True(t, sc.IsValid())
}

func TestIsValidSpanContext(t *testing.T) {
	t.Run("invalid context", func(t *testing.T) {
		valid := IsValidSpanContext(context.Background())
		assert.False(t, valid) // noop context is not valid
	})

	t.Run("valid context", func(t *testing.T) {
		provider := noop.NewTracerProvider()
		tracer := NewTracerWrapper(provider, "test")
		ctx, span := tracer.Start(context.Background(), "test-span")
		defer span.End()

		valid := IsValidSpanContext(ctx)
		assert.False(t, valid) // noop context is not valid
	})
}

func TestSpanKindString(t *testing.T) {
	tests := []struct {
		kind trace.SpanKind
		want string
	}{
		{trace.SpanKindInternal, "internal"},
		{trace.SpanKindServer, "server"},
		{trace.SpanKindClient, "client"},
		{trace.SpanKindProducer, "producer"},
		{trace.SpanKindConsumer, "consumer"},
		{trace.SpanKind(-1), "unspecified"},
	}

	for _, tt := range tests {
		t.Run(tt.want, func(t *testing.T) {
			got := SpanKindString(tt.kind)
			assert.Equal(t, tt.want, got)
		})
	}
}

// Benchmark tests

func BenchmarkTracerWrapper_Start(b *testing.B) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, span := tracer.Start(ctx, "test-span")
		span.End()
	}
}

func BenchmarkSpanBuilder_Start(b *testing.B) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	builder := tracer.NewSpanBuilder("test-span")
	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, span := builder.Start(ctx)
		span.End()
	}
}

func BenchmarkCreateAttribute(b *testing.B) {
	b.Run("string", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = createAttribute("key", "value")
		}
	})

	b.Run("int", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = createAttribute("key", 42)
		}
	})

	b.Run("float64", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = createAttribute("key", 3.14)
		}
	})
}

func BenchmarkCurrentSpanContext(b *testing.B) {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "test-service")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = CurrentSpanContext(ctx)
	}
}

func ExampleTracerWrapper_TraceFunc() {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "example-service")

	err := tracer.TraceFunc(context.Background(), "example-operation", func(ctx context.Context) error {
		// Your business logic here
		fmt.Println("Executing operation...")
		return nil
	})

	if err != nil {
		fmt.Printf("Error: %v\n", err)
	}
	// Output: Executing operation...
}

func ExampleSpanBuilder() {
	provider := noop.NewTracerProvider()
	tracer := NewTracerWrapper(provider, "example-service")

	ctx, span := tracer.NewSpanBuilder("process-request").
		WithKind(trace.SpanKindServer).
		WithAttribute("http.method", "GET").
		WithAttribute("http.route", "/api/users").
		Start(context.Background())

	defer span.End()

	// Process request...
	fmt.Println("Processing request...")
	// Output: Processing request...
}

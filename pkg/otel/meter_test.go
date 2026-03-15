package otel

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/metric/noop"
)

func TestNewMeterWrapper(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	require.NotNil(t, meter)
	assert.Equal(t, "test-service", meter.name)
	assert.NotNil(t, meter.meter)
	assert.NotNil(t, meter.counters)
	assert.NotNil(t, meter.upDownCounters)
	assert.NotNil(t, meter.histograms)
}

func TestMeterWrapper_Counter(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new counter", func(t *testing.T) {
		counter, err := meter.Counter("test-counter")
		require.NoError(t, err)
		assert.NotNil(t, counter)
	})

	t.Run("get existing counter", func(t *testing.T) {
		counter1, err := meter.Counter("test-counter-2")
		require.NoError(t, err)

		counter2, err := meter.Counter("test-counter-2")
		require.NoError(t, err)

		assert.Equal(t, counter1, counter2)
	})

	t.Run("concurrent access", func(t *testing.T) {
		meter := NewMeterWrapper(provider, "test-service")

		done := make(chan bool, 10)
		for i := 0; i < 10; i++ {
			go func() {
				_, err := meter.Counter("concurrent-counter")
				assert.NoError(t, err)
				done <- true
			}()
		}

		for i := 0; i < 10; i++ {
			<-done
		}
	})
}

func TestMeterWrapper_UpDownCounter(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new up-down counter", func(t *testing.T) {
		counter, err := meter.UpDownCounter("test-up-down")
		require.NoError(t, err)
		assert.NotNil(t, counter)
	})

	t.Run("get existing up-down counter", func(t *testing.T) {
		counter1, err := meter.UpDownCounter("test-up-down-2")
		require.NoError(t, err)

		counter2, err := meter.UpDownCounter("test-up-down-2")
		require.NoError(t, err)

		assert.Equal(t, counter1, counter2)
	})
}

func TestMeterWrapper_Histogram(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new histogram", func(t *testing.T) {
		histogram, err := meter.Histogram("test-histogram")
		require.NoError(t, err)
		assert.NotNil(t, histogram)
	})

	t.Run("get existing histogram", func(t *testing.T) {
		histogram1, err := meter.Histogram("test-histogram-2")
		require.NoError(t, err)

		histogram2, err := meter.Histogram("test-histogram-2")
		require.NoError(t, err)

		assert.Equal(t, histogram1, histogram2)
	})
}

func TestMeterWrapper_FloatCounter(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new float counter", func(t *testing.T) {
		counter, err := meter.FloatCounter("test-float-counter")
		require.NoError(t, err)
		assert.NotNil(t, counter)
	})

	t.Run("get existing float counter", func(t *testing.T) {
		counter1, err := meter.FloatCounter("test-float-counter-2")
		require.NoError(t, err)

		counter2, err := meter.FloatCounter("test-float-counter-2")
		require.NoError(t, err)

		assert.Equal(t, counter1, counter2)
	})
}

func TestMeterWrapper_FloatUpDownCounter(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new float up-down counter", func(t *testing.T) {
		counter, err := meter.FloatUpDownCounter("test-float-up-down")
		require.NoError(t, err)
		assert.NotNil(t, counter)
	})

	t.Run("get existing float up-down counter", func(t *testing.T) {
		counter1, err := meter.FloatUpDownCounter("test-float-up-down-2")
		require.NoError(t, err)

		counter2, err := meter.FloatUpDownCounter("test-float-up-down-2")
		require.NoError(t, err)

		assert.Equal(t, counter1, counter2)
	})
}

func TestMeterWrapper_FloatHistogram(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new float histogram", func(t *testing.T) {
		histogram, err := meter.FloatHistogram("test-float-histogram")
		require.NoError(t, err)
		assert.NotNil(t, histogram)
	})

	t.Run("get existing float histogram", func(t *testing.T) {
		histogram1, err := meter.FloatHistogram("test-float-histogram-2")
		require.NoError(t, err)

		histogram2, err := meter.FloatHistogram("test-float-histogram-2")
		require.NoError(t, err)

		assert.Equal(t, histogram1, histogram2)
	})
}

func TestMeterWrapper_Gauge(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new gauge", func(t *testing.T) {
		gauge, err := meter.Gauge("test-gauge")
		require.NoError(t, err)
		assert.NotNil(t, gauge)
	})

	t.Run("get existing gauge", func(t *testing.T) {
		gauge1, err := meter.Gauge("test-gauge-2")
		require.NoError(t, err)

		gauge2, err := meter.Gauge("test-gauge-2")
		require.NoError(t, err)

		assert.Equal(t, gauge1, gauge2)
	})
}

func TestMeterWrapper_FloatGauge(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	t.Run("create new float gauge", func(t *testing.T) {
		gauge, err := meter.FloatGauge("test-float-gauge")
		require.NoError(t, err)
		assert.NotNil(t, gauge)
	})

	t.Run("get existing float gauge", func(t *testing.T) {
		gauge1, err := meter.FloatGauge("test-float-gauge-2")
		require.NoError(t, err)

		gauge2, err := meter.FloatGauge("test-float-gauge-2")
		require.NoError(t, err)

		assert.Equal(t, gauge1, gauge2)
	})
}

func TestMeterWrapper_Add(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	err := meter.Add(ctx, "test-counter", 5, attribute.String("key", "value"))
	assert.NoError(t, err)
}

func TestMeterWrapper_Inc(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	err := meter.Inc(ctx, "test-counter", attribute.String("key", "value"))
	assert.NoError(t, err)
}

func TestMeterWrapper_Record(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	err := meter.Record(ctx, "test-histogram", 100, attribute.String("key", "value"))
	assert.NoError(t, err)
}

func TestMeterWrapper_RecordDuration(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	err := meter.RecordDuration(ctx, "test-duration", 150*time.Millisecond, attribute.String("key", "value"))
	assert.NoError(t, err)
}

func TestMeterWrapper_SetGauge(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	// Note: This is a simplified implementation that doesn't actually do anything
	err := meter.SetGauge(ctx, "test-gauge", 42, attribute.String("key", "value"))
	assert.NoError(t, err)
}

func TestMeterWrapper_ObservableGauge(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	callback := func(ctx context.Context, obs metric.Int64Observer) error {
		obs.Observe(42)
		return nil
	}

	err := meter.ObservableGauge("test-observable-gauge", callback)
	assert.NoError(t, err)
}

func TestTimer(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	t.Run("new timer", func(t *testing.T) {
		timer := meter.NewTimer("test-duration", attribute.String("key", "value"))
		require.NotNil(t, timer)
		assert.Equal(t, meter, timer.meter)
		assert.Equal(t, "test-duration", timer.name)
		assert.NotZero(t, timer.start)
		assert.NotEmpty(t, timer.attrs)
	})

	t.Run("stop timer", func(t *testing.T) {
		timer := meter.NewTimer("test-duration")
		time.Sleep(10 * time.Millisecond)
		duration := timer.Stop(ctx)
		assert.True(t, duration > 0)
	})

	t.Run("elapsed without recording", func(t *testing.T) {
		timer := meter.NewTimer("test-duration")
		time.Sleep(5 * time.Millisecond)
		elapsed := timer.Elapsed()
		assert.True(t, elapsed > 0)
	})

	t.Run("record", func(t *testing.T) {
		timer := meter.NewTimer("test-duration")
		time.Sleep(5 * time.Millisecond)
		duration := timer.Record(ctx)
		assert.True(t, duration > 0)
	})
}

func TestMeterWrapper_TimerFunc(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	t.Run("successful execution", func(t *testing.T) {
		executed := false
		err := meter.TimerFunc(ctx, "test-duration", func() error {
			executed = true
			time.Sleep(5 * time.Millisecond)
			return nil
		})

		assert.NoError(t, err)
		assert.True(t, executed)
	})

	t.Run("execution with error", func(t *testing.T) {
		testErr := fmt.Errorf("test error")
		err := meter.TimerFunc(ctx, "test-duration", func() error {
			return testErr
		})

		assert.Error(t, err)
		assert.Equal(t, testErr, err)
	})
}

func TestTimerFuncWithResult(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	t.Run("successful execution", func(t *testing.T) {
		result, err := TimerFuncWithResult(meter, ctx, "test-duration", func() (string, error) {
			time.Sleep(5 * time.Millisecond)
			return "success", nil
		})

		assert.NoError(t, err)
		assert.Equal(t, "success", result)
	})

	t.Run("execution with error", func(t *testing.T) {
		testErr := fmt.Errorf("test error")
		result, err := TimerFuncWithResult(meter, ctx, "test-duration", func() (string, error) {
			return "", testErr
		})

		assert.Error(t, err)
		assert.Empty(t, result)
	})

	t.Run("execution with int result", func(t *testing.T) {
		result, err := TimerFuncWithResult(meter, ctx, "test-duration", func() (int, error) {
			time.Sleep(5 * time.Millisecond)
			return 42, nil
		})

		assert.NoError(t, err)
		assert.Equal(t, 42, result)
	})
}

func TestMetricsBatch(t *testing.T) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	t.Run("new batch", func(t *testing.T) {
		batch := meter.NewBatch(ctx)
		require.NotNil(t, batch)
		assert.Equal(t, meter, batch.meter)
		assert.Equal(t, ctx, batch.ctx)
	})

	t.Run("add to batch", func(t *testing.T) {
		batch := meter.NewBatch(ctx)
		result := batch.Add("counter1", 5)
		assert.Equal(t, batch, result)
	})

	t.Run("inc in batch", func(t *testing.T) {
		batch := meter.NewBatch(ctx)
		result := batch.Inc("counter1")
		assert.Equal(t, batch, result)
	})

	t.Run("record in batch", func(t *testing.T) {
		batch := meter.NewBatch(ctx)
		result := batch.Record("histogram1", 100)
		assert.Equal(t, batch, result)
	})

	t.Run("chained operations", func(t *testing.T) {
		batch := meter.NewBatch(ctx).
			Add("counter1", 5).
			Inc("counter2").
			Record("histogram1", 100).
			Add("counter1", 3)

		assert.NotNil(t, batch)
	})
}

func TestMeterFromContext(t *testing.T) {
	t.Run("no meter in context", func(t *testing.T) {
		meter := MeterFromContext(context.Background(), "test")
		assert.Nil(t, meter)
	})

	t.Run("with meter in context", func(t *testing.T) {
		provider := noop.NewMeterProvider()
		ctx := ContextWithMeterProvider(context.Background(), provider)

		meter := MeterFromContext(ctx, "test")
		assert.NotNil(t, meter)
	})
}

func TestContextWithMeterProvider(t *testing.T) {
	provider := noop.NewMeterProvider()
	ctx := ContextWithMeterProvider(context.Background(), provider)

	// Verify the provider is in the context
	retrievedProvider, ok := ctx.Value(meterProviderKey{}).(metric.MeterProvider)
	assert.True(t, ok)
	assert.Equal(t, provider, retrievedProvider)
}

func TestAttributeHelpers(t *testing.T) {
	t.Run("StringAttr", func(t *testing.T) {
		attr := StringAttr("key", "value")
		assert.Equal(t, attribute.String("key", "value"), attr)
	})

	t.Run("IntAttr", func(t *testing.T) {
		attr := IntAttr("key", 42)
		assert.Equal(t, attribute.Int("key", 42), attr)
	})

	t.Run("Int64Attr", func(t *testing.T) {
		attr := Int64Attr("key", 42)
		assert.Equal(t, attribute.Int64("key", 42), attr)
	})

	t.Run("Float64Attr", func(t *testing.T) {
		attr := Float64Attr("key", 3.14)
		assert.Equal(t, attribute.Float64("key", 3.14), attr)
	})

	t.Run("BoolAttr", func(t *testing.T) {
		attr := BoolAttr("key", true)
		assert.Equal(t, attribute.Bool("key", true), attr)
	})

	t.Run("StringSliceAttr", func(t *testing.T) {
		attr := StringSliceAttr("key", []string{"a", "b"})
		assert.Equal(t, attribute.StringSlice("key", []string{"a", "b"}), attr)
	})
}

func TestAttributes(t *testing.T) {
	attrs := map[string]interface{}{
		"string":  "value",
		"int":     42,
		"int64":   int64(42),
		"float64": 3.14,
		"bool":    true,
	}

	result := Attributes(attrs)
	assert.Len(t, result, 5)
}

func TestCreateMetricAttribute(t *testing.T) {
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
		{"string slice", "key", []string{"a", "b"}, attribute.StringSlice("key", []string{"a", "b"})},
		{"int slice", "key", []int{1, 2}, attribute.IntSlice("key", []int{1, 2})},
		{"int64 slice", "key", []int64{1, 2}, attribute.Int64Slice("key", []int64{1, 2})},
		{"float64 slice", "key", []float64{1.0, 2.0}, attribute.Float64Slice("key", []float64{1.0, 2.0})},
		{"bool slice", "key", []bool{true, false}, attribute.BoolSlice("key", []bool{true, false})},
		{"unknown", "key", struct{}{}, attribute.String("key", "{}")},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := createMetricAttribute(tt.key, tt.value)
			assert.Equal(t, tt.want, got)
		})
	}
}

// Benchmark tests

func BenchmarkMeterWrapper_Counter(b *testing.B) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = meter.Counter("test-counter")
	}
}

func BenchmarkMeterWrapper_Add(b *testing.B) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	// Create counter first
	_, _ = meter.Counter("test-counter")

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = meter.Add(ctx, "test-counter", 1)
	}
}

func BenchmarkMeterWrapper_Record(b *testing.B) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	// Create histogram first
	_, _ = meter.Histogram("test-histogram")

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = meter.Record(ctx, "test-histogram", int64(i))
	}
}

func BenchmarkTimer_Stop(b *testing.B) {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "test-service")
	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		timer := meter.NewTimer("test-duration")
		timer.Stop(ctx)
	}
}

func BenchmarkCreateMetricAttribute(b *testing.B) {
	b.Run("string", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = createMetricAttribute("key", "value")
		}
	})

	b.Run("int", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = createMetricAttribute("key", 42)
		}
	})

	b.Run("float64", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = createMetricAttribute("key", 3.14)
		}
	})
}

func BenchmarkAttributes(b *testing.B) {
	attrs := map[string]interface{}{
		"key1": "value1",
		"key2": 42,
		"key3": 3.14,
		"key4": true,
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = Attributes(attrs)
	}
}

// Example tests

func ExampleMeterWrapper_Add() {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "example-service")
	ctx := context.Background()

	_ = meter.Add(ctx, "requests_total", 1, attribute.String("method", "GET"))
	fmt.Println("Counter incremented")
	// Output: Counter incremented
}

func ExampleMeterWrapper_RecordDuration() {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "example-service")
	ctx := context.Background()

	start := time.Now()
	time.Sleep(10 * time.Millisecond)
	duration := time.Since(start)

	_ = meter.RecordDuration(ctx, "request_duration", duration, attribute.String("endpoint", "/api/users"))
	fmt.Println("Duration recorded")
	// Output: Duration recorded
}

func ExampleTimer() {
	provider := noop.NewMeterProvider()
	meter := NewMeterWrapper(provider, "example-service")
	ctx := context.Background()

	timer := meter.NewTimer("operation_duration", attribute.String("operation", "database_query"))

	// Simulate some work
	time.Sleep(10 * time.Millisecond)

	duration := timer.Stop(ctx)
	fmt.Printf("Operation took %v\n", duration)
}

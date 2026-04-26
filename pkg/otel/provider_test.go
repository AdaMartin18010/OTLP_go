package otel

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func TestDefaultSDKOptions(t *testing.T) {
	opts := DefaultSDKOptions()

	assert.True(t, opts.TracerEnabled)
	assert.True(t, opts.MeterEnabled)
	assert.False(t, opts.LoggerEnabled)
	assert.Equal(t, []string{"tracecontext", "baggage"}, opts.Propagators)
	assert.Nil(t, opts.Config)
	assert.Nil(t, opts.Resource)
}

func TestWithConfig(t *testing.T) {
	cfg := DefaultConfig()
	sdk := &SDK{}

	opt := WithConfig(cfg)
	opt(sdk)

	assert.Equal(t, cfg, sdk.Config)
}

func TestWithResource(t *testing.T) {
	res, _ := resource.New(context.Background(),
		resource.WithAttributes(semconv.ServiceName("test-service")),
	)
	sdk := &SDK{}

	opt := WithResource(res)
	opt(sdk)

	assert.Equal(t, res, sdk.Resource)
}

func TestWithPropagator(t *testing.T) {
	sdk := &SDK{}
	propagator := &mockPropagator{}

	opt := WithPropagator(propagator)
	opt(sdk)

	assert.Equal(t, propagator, sdk.Propagator)
}

func TestWithExporterManager(t *testing.T) {
	sdk := &SDK{}
	em := NewExporterManager(DefaultExporterConfig())

	opt := WithExporterManager(em)
	opt(sdk)

	assert.Equal(t, em, sdk.ExporterManager)
}

func TestSDK_createSampler(t *testing.T) {
	tests := []struct {
		name     string
		strategy string
		ratio    float64
	}{
		{
			name:     "always_on",
			strategy: "always_on",
			ratio:    1.0,
		},
		{
			name:     "always_off",
			strategy: "always_off",
			ratio:    0.0,
		},
		{
			name:     "traceidratio",
			strategy: "traceidratio",
			ratio:    0.5,
		},
		{
			name:     "parentbased_always_on",
			strategy: "parentbased_always_on",
			ratio:    1.0,
		},
		{
			name:     "parentbased_always_off",
			strategy: "parentbased_always_off",
			ratio:    0.0,
		},
		{
			name:     "parentbased_traceidratio",
			strategy: "parentbased_traceidratio",
			ratio:    0.5,
		},
		{
			name:     "default",
			strategy: "unknown",
			ratio:    1.0,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultConfig()
			cfg.Sampling.Strategy = tt.strategy
			cfg.Sampling.Ratio = tt.ratio

			sdk := &SDK{Config: cfg}
			sampler := sdk.createSampler()

			assert.NotNil(t, sampler)
		})
	}
}

func TestSDK_registerShutdown(t *testing.T) {
	sdk := &SDK{
		shutdown: make([]func(context.Context) error, 0),
	}

	fn1 := func(ctx context.Context) error { return nil }
	fn2 := func(ctx context.Context) error { return nil }

	sdk.registerShutdown(fn1)
	assert.Len(t, sdk.shutdown, 1)

	sdk.registerShutdown(fn2)
	assert.Len(t, sdk.shutdown, 2)
}

func TestSDK_Shutdown(t *testing.T) {
	t.Run("shutdown with no functions", func(t *testing.T) {
		sdk := &SDK{
			shutdown: make([]func(context.Context) error, 0),
		}

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		err := sdk.Shutdown(ctx)
		assert.NoError(t, err)
	})

	t.Run("shutdown executes in reverse order", func(t *testing.T) {
		var order []int
		sdk := &SDK{
			shutdown: make([]func(context.Context) error, 0),
		}

		fn1 := func(ctx context.Context) error {
			order = append(order, 1)
			return nil
		}
		fn2 := func(ctx context.Context) error {
			order = append(order, 2)
			return nil
		}
		fn3 := func(ctx context.Context) error {
			order = append(order, 3)
			return nil
		}

		sdk.registerShutdown(fn1)
		sdk.registerShutdown(fn2)
		sdk.registerShutdown(fn3)

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		err := sdk.Shutdown(ctx)
		require.NoError(t, err)

		// Should execute in reverse order: 3, 2, 1
		assert.Equal(t, []int{3, 2, 1}, order)
	})

	t.Run("shutdown with error", func(t *testing.T) {
		sdk := &SDK{
			shutdown: make([]func(context.Context) error, 0),
		}

		fn := func(ctx context.Context) error {
			return assert.AnError
		}

		sdk.registerShutdown(fn)

		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		err := sdk.Shutdown(ctx)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "shutdown errors")
	})
}

func TestSDK_Tracer(t *testing.T) {
	t.Run("nil tracer provider", func(t *testing.T) {
		sdk := &SDK{TracerProvider: nil}
		tracer := sdk.Tracer("test")
		assert.Nil(t, tracer)
	})

	t.Run("with tracer provider", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Tracer.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		tracer := sdk.Tracer("test-service")
		assert.NotNil(t, tracer)
	})
}

func TestSDK_Meter(t *testing.T) {
	t.Run("nil meter provider", func(t *testing.T) {
		sdk := &SDK{MeterProvider: nil}
		meter := sdk.Meter("test")
		assert.Nil(t, meter)
	})

	t.Run("with meter provider", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Meter.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		meter := sdk.Meter("test-service")
		assert.NotNil(t, meter)
	})
}

func TestSDK_Logger(t *testing.T) {
	t.Run("nil logger provider", func(t *testing.T) {
		sdk := &SDK{LoggerProvider: nil}
		logger := sdk.Logger("test")
		assert.Nil(t, logger)
	})

	t.Run("with logger provider", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Logger.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		logger := sdk.Logger("test-service")
		assert.NotNil(t, logger)
	})
}

func TestSDK_IsTracingEnabled(t *testing.T) {
	t.Run("disabled", func(t *testing.T) {
		sdk := &SDK{TracerProvider: nil}
		assert.False(t, sdk.IsTracingEnabled())
	})

	t.Run("enabled", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Tracer.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.True(t, sdk.IsTracingEnabled())
	})
}

func TestSDK_IsMetricsEnabled(t *testing.T) {
	t.Run("disabled", func(t *testing.T) {
		sdk := &SDK{MeterProvider: nil}
		assert.False(t, sdk.IsMetricsEnabled())
	})

	t.Run("enabled", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Meter.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.True(t, sdk.IsMetricsEnabled())
	})
}

func TestSDK_IsLoggingEnabled(t *testing.T) {
	t.Run("disabled", func(t *testing.T) {
		sdk := &SDK{LoggerProvider: nil}
		assert.False(t, sdk.IsLoggingEnabled())
	})

	t.Run("enabled", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Logger.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.True(t, sdk.IsLoggingEnabled())
	})
}

func TestSetup(t *testing.T) {
	t.Run("basic setup", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.ServiceName = "test-service"
		cfg.Tracer.Enabled = true
		cfg.Meter.Enabled = true
		cfg.Logger.Enabled = false
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.NotNil(t, sdk)
		assert.NotNil(t, sdk.Resource)
		assert.NotNil(t, sdk.TracerProvider)
		assert.NotNil(t, sdk.MeterProvider)
		assert.Nil(t, sdk.LoggerProvider) // Disabled
		assert.NotNil(t, sdk.Propagator)
		assert.NotNil(t, sdk.ExporterManager)
		assert.Equal(t, cfg, sdk.Config)
	})

	t.Run("with resource option", func(t *testing.T) {
		res, _ := resource.New(context.Background(),
			resource.WithAttributes(semconv.ServiceName("custom-service")),
		)

		cfg := DefaultConfig()
		cfg.Tracer.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg, WithResource(res))
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.NotNil(t, sdk)
		assert.Equal(t, res, sdk.Resource)
	})

	t.Run("logger enabled", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Logger.Enabled = true
		cfg.Exporter.Endpoint = "localhost:4317"

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.NotNil(t, sdk.LoggerProvider)
	})

	t.Run("disabled providers", func(t *testing.T) {
		cfg := DefaultConfig()
		cfg.Tracer.Enabled = false
		cfg.Meter.Enabled = false
		cfg.Logger.Enabled = false

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		sdk, err := Setup(ctx, cfg)
		require.NoError(t, err)
		defer sdk.Shutdown(ctx)

		assert.NotNil(t, sdk)
		assert.Nil(t, sdk.TracerProvider)
		assert.Nil(t, sdk.MeterProvider)
		assert.Nil(t, sdk.LoggerProvider)
	})
}

func TestSetup_WithCustomPropagators(t *testing.T) {
	cfg := DefaultConfig()
	cfg.Tracer.Enabled = true
	cfg.Exporter.Endpoint = "localhost:4317"
	cfg.Propagator.Propagators = []string{"tracecontext", "baggage", "b3"}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	sdk, err := Setup(ctx, cfg)
	require.NoError(t, err)
	defer sdk.Shutdown(ctx)

	assert.NotNil(t, sdk.Propagator)
}

func TestSetup_WithCustomAttributes(t *testing.T) {
	cfg := DefaultConfig()
	cfg.Tracer.Enabled = true
	cfg.Exporter.Endpoint = "localhost:4317"
	cfg.Resource.Attributes = map[string]string{
		"custom.attribute": "value",
		"environment":      "test",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	sdk, err := Setup(ctx, cfg)
	require.NoError(t, err)
	defer sdk.Shutdown(ctx)

	assert.NotNil(t, sdk.Resource)
}

func TestSetup_WithHTTPProtocol(t *testing.T) {
	cfg := DefaultConfig()
	cfg.Tracer.Enabled = true
	cfg.Meter.Enabled = true
	cfg.Exporter.Endpoint = "localhost:4318"
	cfg.Exporter.Protocol = "http"

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	sdk, err := Setup(ctx, cfg)
	require.NoError(t, err)
	defer sdk.Shutdown(ctx)

	assert.NotNil(t, sdk)
	assert.Equal(t, ExporterTypeHTTP, sdk.ExporterManager.GetExporterType())
}

// Mock types

type mockPropagator struct{}

func (m *mockPropagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {}
func (m *mockPropagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
	return ctx
}
func (m *mockPropagator) Fields() []string { return nil }

// Benchmark tests

func BenchmarkSDK_createSampler(b *testing.B) {
	cfg := DefaultConfig()
	sdk := &SDK{Config: cfg}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = sdk.createSampler()
	}
}

func BenchmarkSetup(b *testing.B) {
	cfg := DefaultConfig()
	cfg.Tracer.Enabled = true
	cfg.Meter.Enabled = false
	cfg.Logger.Enabled = false
	cfg.Exporter.Endpoint = "localhost:4317"

	ctx := context.Background()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		sdk, err := Setup(ctx, cfg)
		if err == nil {
			_ = sdk.Shutdown(ctx)
		}
	}
}

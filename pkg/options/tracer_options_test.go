package options

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestSamplerType_IsValid(t *testing.T) {
	tests := []struct {
		name   string
		sample SamplerType
		want   bool
	}{
		{"always_on", SamplerAlwaysOn, true},
		{"always_off", SamplerAlwaysOff, true},
		{"trace_id_ratio", SamplerTraceIDRatio, true},
		{"parent_based", SamplerParentBased, true},
		{"invalid", SamplerType("invalid"), false},
		{"empty", SamplerType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.sample.IsValid())
		})
	}
}

func TestSamplerType_String(t *testing.T) {
	assert.Equal(t, "always_on", SamplerAlwaysOn.String())
	assert.Equal(t, "always_off", SamplerAlwaysOff.String())
	assert.Equal(t, "parent_based", SamplerParentBased.String())
}

func TestSpanProcessorType_IsValid(t *testing.T) {
	tests := []struct {
		name      string
		processor SpanProcessorType
		want      bool
	}{
		{"batch", SpanProcessorBatch, true},
		{"simple", SpanProcessorSimple, true},
		{"invalid", SpanProcessorType("invalid"), false},
		{"empty", SpanProcessorType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.processor.IsValid())
		})
	}
}

func TestDefaultBatchSpanProcessorConfig(t *testing.T) {
	cfg := DefaultBatchSpanProcessorConfig()
	require.NotNil(t, cfg)

	assert.Equal(t, 2048, cfg.MaxQueueSize)
	assert.Equal(t, 5*time.Second, cfg.BatchTimeout)
	assert.Equal(t, 30*time.Second, cfg.ExportTimeout)
	assert.Equal(t, 512, cfg.MaxExportBatchSize)
}

func TestBatchSpanProcessorConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *BatchSpanProcessorConfig
		wantErr bool
		errMsg  string
	}{
		{
			name:    "nil config",
			config:  nil,
			wantErr: false,
		},
		{
			name:    "valid config",
			config:  DefaultBatchSpanProcessorConfig(),
			wantErr: false,
		},
		{
			name: "zero max queue size",
			config: &BatchSpanProcessorConfig{
				MaxQueueSize:       0,
				BatchTimeout:       5 * time.Second,
				ExportTimeout:      30 * time.Second,
				MaxExportBatchSize: 512,
			},
			wantErr: true,
			errMsg:  "max queue size must be positive",
		},
		{
			name: "negative max queue size",
			config: &BatchSpanProcessorConfig{
				MaxQueueSize:       -1,
				BatchTimeout:       5 * time.Second,
				ExportTimeout:      30 * time.Second,
				MaxExportBatchSize: 512,
			},
			wantErr: true,
			errMsg:  "max queue size must be positive",
		},
		{
			name: "zero batch timeout",
			config: &BatchSpanProcessorConfig{
				MaxQueueSize:       2048,
				BatchTimeout:       0,
				ExportTimeout:      30 * time.Second,
				MaxExportBatchSize: 512,
			},
			wantErr: true,
			errMsg:  "batch timeout must be positive",
		},
		{
			name: "zero export timeout",
			config: &BatchSpanProcessorConfig{
				MaxQueueSize:       2048,
				BatchTimeout:       5 * time.Second,
				ExportTimeout:      0,
				MaxExportBatchSize: 512,
			},
			wantErr: true,
			errMsg:  "export timeout must be positive",
		},
		{
			name: "zero export batch size",
			config: &BatchSpanProcessorConfig{
				MaxQueueSize:       2048,
				BatchTimeout:       5 * time.Second,
				ExportTimeout:      30 * time.Second,
				MaxExportBatchSize: 0,
			},
			wantErr: true,
			errMsg:  "max export batch size must be positive",
		},
		{
			name: "export batch size larger than queue",
			config: &BatchSpanProcessorConfig{
				MaxQueueSize:       100,
				BatchTimeout:       5 * time.Second,
				ExportTimeout:      30 * time.Second,
				MaxExportBatchSize: 200,
			},
			wantErr: true,
			errMsg:  "max export batch size",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestDefaultTracerConfig(t *testing.T) {
	cfg := DefaultTracerConfig()
	require.NotNil(t, cfg)

	assert.Equal(t, SamplerParentBased, cfg.SamplerType)
	assert.Equal(t, 1.0, cfg.SamplingRatio)
	assert.Equal(t, SpanProcessorBatch, cfg.SpanProcessorType)
	assert.NotNil(t, cfg.BatchConfig)
	assert.Equal(t, 128, cfg.MaxEventsPerSpan)
	assert.Equal(t, 128, cfg.MaxAttributesPerSpan)
	assert.Equal(t, 32, cfg.MaxLinksPerSpan)
	assert.NotNil(t, cfg.Attributes)

	// Check base config
	assert.Equal(t, "localhost:4317", cfg.Endpoint)
	assert.Equal(t, 10*time.Second, cfg.Timeout)
}

func TestTracerConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *TracerConfig
		wantErr bool
		errMsg  string
	}{
		{
			name: "valid with service name",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				return c
			}(),
			wantErr: false,
		},
		{
			name:    "missing service name",
			config:  DefaultTracerConfig(),
			wantErr: true,
			errMsg:  "service name is required",
		},
		{
			name: "invalid sampler type",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.SamplerType = SamplerType("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid sampler type",
		},
		{
			name: "sampling ratio too high",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.SamplingRatio = 1.5
				return c
			}(),
			wantErr: true,
			errMsg:  "sampling ratio must be between 0.0 and 1.0",
		},
		{
			name: "sampling ratio negative",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.SamplingRatio = -0.1
				return c
			}(),
			wantErr: true,
			errMsg:  "sampling ratio must be between 0.0 and 1.0",
		},
		{
			name: "invalid span processor type",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.SpanProcessorType = SpanProcessorType("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid span processor type",
		},
		{
			name: "invalid batch config",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.BatchConfig = &BatchSpanProcessorConfig{
					MaxQueueSize: 0,
				}
				return c
			}(),
			wantErr: true,
			errMsg:  "batch config validation failed",
		},
		{
			name: "zero max events",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.MaxEventsPerSpan = 0
				return c
			}(),
			wantErr: true,
			errMsg:  "max events per span must be positive",
		},
		{
			name: "zero max attributes",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.MaxAttributesPerSpan = 0
				return c
			}(),
			wantErr: true,
			errMsg:  "max attributes per span must be positive",
		},
		{
			name: "zero max links",
			config: func() *TracerConfig {
				c := DefaultTracerConfig()
				c.ServiceName = "test-service"
				c.MaxLinksPerSpan = 0
				return c
			}(),
			wantErr: true,
			errMsg:  "max links per span must be positive",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestTracerOption_Apply_WrongType(t *testing.T) {
	opt := TracerOption(func(cfg *TracerConfig) error {
		return nil
	})

	err := opt.Apply("wrong type")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "expected *TracerConfig")
}

func TestWithServiceName(t *testing.T) {
	tests := []struct {
		name    string
		service string
		wantErr bool
		errMsg  string
	}{
		{"valid name", "my-service", false, ""},
		{"with version", "my-service-v2", false, ""},
		{"empty name", "", true, "service name cannot be empty"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithServiceName(tt.service)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.service, cfg.ServiceName)
			}
		})
	}
}

func TestWithServiceVersion(t *testing.T) {
	cfg := &TracerConfig{}
	err := WithServiceVersion("1.2.3")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "1.2.3", cfg.ServiceVersion)
}

func TestWithServiceNamespace(t *testing.T) {
	cfg := &TracerConfig{}
	err := WithServiceNamespace("my-namespace")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "my-namespace", cfg.ServiceNamespace)
}

func TestWithServiceInstanceID(t *testing.T) {
	cfg := &TracerConfig{}
	err := WithServiceInstanceID("instance-123")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "instance-123", cfg.ServiceInstanceID)
}

func TestWithSampler(t *testing.T) {
	tests := []struct {
		name    string
		sampler SamplerType
		wantErr bool
		errMsg  string
	}{
		{"always_on", SamplerAlwaysOn, false, ""},
		{"always_off", SamplerAlwaysOff, false, ""},
		{"trace_id_ratio", SamplerTraceIDRatio, false, ""},
		{"parent_based", SamplerParentBased, false, ""},
		{"invalid", SamplerType("invalid"), true, "invalid sampler type"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithSampler(tt.sampler)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.sampler, cfg.SamplerType)
			}
		})
	}
}

func TestWithSamplingRatio(t *testing.T) {
	tests := []struct {
		name    string
		ratio   float64
		wantErr bool
		errMsg  string
	}{
		{"zero", 0.0, false, ""},
		{"half", 0.5, false, ""},
		{"one", 1.0, false, ""},
		{"negative", -0.1, true, "sampling ratio must be between 0.0 and 1.0"},
		{"greater than one", 1.5, true, "sampling ratio must be between 0.0 and 1.0"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithSamplingRatio(tt.ratio)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.InDelta(t, tt.ratio, cfg.SamplingRatio, 0.001)
			}
		})
	}
}

func TestWithSpanProcessor(t *testing.T) {
	tests := []struct {
		name      string
		processor SpanProcessorType
		wantErr   bool
		errMsg    string
	}{
		{"batch", SpanProcessorBatch, false, ""},
		{"simple", SpanProcessorSimple, false, ""},
		{"invalid", SpanProcessorType("invalid"), true, "invalid span processor type"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithSpanProcessor(tt.processor)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.processor, cfg.SpanProcessorType)
			}
		})
	}
}

func TestWithBatchConfig(t *testing.T) {
	t.Run("valid config", func(t *testing.T) {
		cfg := &TracerConfig{}
		batchCfg := &BatchSpanProcessorConfig{
			MaxQueueSize:       1024,
			BatchTimeout:       1 * time.Second,
			ExportTimeout:      10 * time.Second,
			MaxExportBatchSize: 256,
		}
		opt := WithBatchConfig(batchCfg)
		err := opt(cfg)
		require.NoError(t, err)
		assert.Equal(t, 1024, cfg.BatchConfig.MaxQueueSize)
	})

	t.Run("invalid config", func(t *testing.T) {
		cfg := &TracerConfig{}
		batchCfg := &BatchSpanProcessorConfig{
			MaxQueueSize: 0,
		}
		opt := WithBatchConfig(batchCfg)
		err := opt(cfg)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid batch config")
	})
}

func TestWithMaxQueueSize(t *testing.T) {
	tests := []struct {
		name    string
		size    int
		wantErr bool
		errMsg  string
	}{
		{"valid size", 1024, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max queue size must be positive"},
		{"negative", -1, true, "max queue size must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithMaxQueueSize(tt.size)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.size, cfg.BatchConfig.MaxQueueSize)
			}
		})
	}
}

func TestWithBatchTimeout(t *testing.T) {
	tests := []struct {
		name    string
		timeout time.Duration
		wantErr bool
		errMsg  string
	}{
		{"one second", 1 * time.Second, false, ""},
		{"100ms", 100 * time.Millisecond, false, ""},
		{"zero", 0, true, "batch timeout must be positive"},
		{"negative", -1 * time.Second, true, "batch timeout must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithBatchTimeout(tt.timeout)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.timeout, cfg.BatchConfig.BatchTimeout)
			}
		})
	}
}

func TestWithExportTimeout(t *testing.T) {
	tests := []struct {
		name    string
		timeout time.Duration
		wantErr bool
		errMsg  string
	}{
		{"10 seconds", 10 * time.Second, false, ""},
		{"zero", 0, true, "export timeout must be positive"},
		{"negative", -1 * time.Second, true, "export timeout must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithExportTimeout(tt.timeout)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.timeout, cfg.BatchConfig.ExportTimeout)
			}
		})
	}
}

func TestWithMaxExportBatchSize(t *testing.T) {
	tests := []struct {
		name    string
		size    int
		wantErr bool
		errMsg  string
	}{
		{"valid size", 256, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max export batch size must be positive"},
		{"negative", -1, true, "max export batch size must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithMaxExportBatchSize(tt.size)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.size, cfg.BatchConfig.MaxExportBatchSize)
			}
		})
	}
}

func TestWithMaxEventsPerSpan(t *testing.T) {
	tests := []struct {
		name    string
		max     int
		wantErr bool
		errMsg  string
	}{
		{"valid max", 100, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max events per span must be positive"},
		{"negative", -1, true, "max events per span must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithMaxEventsPerSpan(tt.max)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.max, cfg.MaxEventsPerSpan)
			}
		})
	}
}

func TestWithMaxAttributesPerSpan(t *testing.T) {
	tests := []struct {
		name    string
		max     int
		wantErr bool
		errMsg  string
	}{
		{"valid max", 100, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max attributes per span must be positive"},
		{"negative", -1, true, "max attributes per span must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithMaxAttributesPerSpan(tt.max)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.max, cfg.MaxAttributesPerSpan)
			}
		})
	}
}

func TestWithMaxLinksPerSpan(t *testing.T) {
	tests := []struct {
		name    string
		max     int
		wantErr bool
		errMsg  string
	}{
		{"valid max", 10, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max links per span must be positive"},
		{"negative", -1, true, "max links per span must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &TracerConfig{}
			opt := WithMaxLinksPerSpan(tt.max)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.max, cfg.MaxLinksPerSpan)
			}
		})
	}
}

func TestWithAttribute(t *testing.T) {
	cfg := &TracerConfig{}

	err := WithAttribute("key1", "value1")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value1", cfg.Attributes["key1"])

	err = WithAttribute("key2", 123)(cfg)
	require.NoError(t, err)
	assert.Equal(t, 123, cfg.Attributes["key2"])
}

func TestWithAttributes(t *testing.T) {
	cfg := &TracerConfig{}

	attrs := map[string]interface{}{
		"key1": "value1",
		"key2": 123,
		"key3": true,
	}

	err := WithAttributes(attrs)(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value1", cfg.Attributes["key1"])
	assert.Equal(t, 123, cfg.Attributes["key2"])
	assert.Equal(t, true, cfg.Attributes["key3"])
}

func TestApplyTracerOptions(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		cfg, err := ApplyTracerOptions(
			WithServiceName("test-service"),
			WithServiceVersion("1.0.0"),
			WithSampler(SamplerAlwaysOn),
		)
		require.NoError(t, err)
		assert.Equal(t, "test-service", cfg.ServiceName)
		assert.Equal(t, "1.0.0", cfg.ServiceVersion)
		assert.Equal(t, SamplerAlwaysOn, cfg.SamplerType)
	})

	t.Run("option error", func(t *testing.T) {
		cfg, err := ApplyTracerOptions(
			WithServiceName(""),
		)
		require.Error(t, err)
		assert.Nil(t, cfg)
		assert.Contains(t, err.Error(), "service name cannot be empty")
	})

	t.Run("validation error", func(t *testing.T) {
		cfg, err := ApplyTracerOptions(
			WithServiceName("test-service"),
			func(c *TracerConfig) error {
				c.MaxEventsPerSpan = 0
				return nil
			},
		)
		require.Error(t, err)
		assert.Nil(t, cfg)
		assert.Contains(t, err.Error(), "max events per span must be positive")
	})
}

func TestTracerBaseEndpoint(t *testing.T) {
	cfg := &TracerConfig{}
	err := TracerBaseEndpoint("custom:4318")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "custom:4318", cfg.Endpoint)
}

func TestTracerBaseTimeout(t *testing.T) {
	cfg := &TracerConfig{}
	err := TracerBaseTimeout(5 * time.Second)(cfg)
	require.NoError(t, err)
	assert.Equal(t, 5*time.Second, cfg.Timeout)
}

func TestTracerBaseHeaders(t *testing.T) {
	cfg := &TracerConfig{}
	headers := map[string]string{"X-Custom": "value"}
	err := TracerBaseHeaders(headers)(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value", cfg.Headers["X-Custom"])
}

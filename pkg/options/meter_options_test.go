package options

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestAggregationTemporality_IsValid(t *testing.T) {
	tests := []struct {
		name        string
		temporality AggregationTemporality
		want        bool
	}{
		{"delta", AggregationTemporalityDelta, true},
		{"cumulative", AggregationTemporalityCumulative, true},
		{"invalid", AggregationTemporality("invalid"), false},
		{"empty", AggregationTemporality(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.temporality.IsValid())
		})
	}
}

func TestMetricExporterType_IsValid(t *testing.T) {
	tests := []struct {
		name     string
		exporter MetricExporterType
		want     bool
	}{
		{"otlp", MetricExporterOTLP, true},
		{"prometheus", MetricExporterPrometheus, true},
		{"console", MetricExporterConsole, true},
		{"invalid", MetricExporterType("invalid"), false},
		{"empty", MetricExporterType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.exporter.IsValid())
		})
	}
}

func TestViewType_IsValid(t *testing.T) {
	tests := []struct {
		name string
		view ViewType
		want bool
	}{
		{"drop", ViewTypeDrop, true},
		{"rename", ViewTypeRename, true},
		{"change_aggregation", ViewTypeChangeAggregation, true},
		{"invalid", ViewType("invalid"), false},
		{"empty", ViewType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.view.IsValid())
		})
	}
}

func TestAggregationType_IsValid(t *testing.T) {
	tests := []struct {
		name        string
		aggregation AggregationType
		want        bool
	}{
		{"default", AggregationDefault, true},
		{"sum", AggregationSum, true},
		{"count", AggregationCount, true},
		{"last_value", AggregationLastValue, true},
		{"explicit_bucket_histogram", AggregationExplicitBucketHistogram, true},
		{"invalid", AggregationType("invalid"), false},
		{"empty", AggregationType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.aggregation.IsValid())
		})
	}
}

func TestDefaultMeterConfig(t *testing.T) {
	cfg := DefaultMeterConfig()
	require.NotNil(t, cfg)

	assert.Equal(t, MetricExporterOTLP, cfg.ExporterType)
	assert.Equal(t, AggregationTemporalityCumulative, cfg.Temporality)
	assert.Equal(t, 60*time.Second, cfg.PeriodicReaderInterval)
	assert.Equal(t, 30*time.Second, cfg.PeriodicReaderTimeout)
	assert.NotNil(t, cfg.Views)
	assert.Empty(t, cfg.Views)
	assert.NotNil(t, cfg.ResourceAttributes)
	assert.False(t, cfg.DisableBuiltinMetrics)

	// Check base config
	assert.Equal(t, "localhost:4317", cfg.Endpoint)
	assert.Equal(t, 10*time.Second, cfg.Timeout)
}

func TestMeterConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *MeterConfig
		wantErr bool
		errMsg  string
	}{
		{
			name: "valid with service name",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				return c
			}(),
			wantErr: false,
		},
		{
			name:    "missing service name",
			config:  DefaultMeterConfig(),
			wantErr: true,
			errMsg:  "service name is required",
		},
		{
			name: "invalid exporter type",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				c.ExporterType = MetricExporterType("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid exporter type",
		},
		{
			name: "invalid temporality",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				c.Temporality = AggregationTemporality("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid temporality",
		},
		{
			name: "zero periodic reader interval",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				c.PeriodicReaderInterval = 0
				return c
			}(),
			wantErr: true,
			errMsg:  "periodic reader interval must be positive",
		},
		{
			name: "zero periodic reader timeout",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				c.PeriodicReaderTimeout = 0
				return c
			}(),
			wantErr: true,
			errMsg:  "periodic reader timeout must be positive",
		},
		{
			name: "timeout greater than interval",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				c.PeriodicReaderInterval = 10 * time.Second
				c.PeriodicReaderTimeout = 20 * time.Second
				return c
			}(),
			wantErr: true,
			errMsg:  "periodic reader timeout",
		},
		{
			name: "invalid view",
			config: func() *MeterConfig {
				c := DefaultMeterConfig()
				c.ServiceName = "test-service"
				c.Views = []View{{Type: ViewType("invalid")}}
				return c
			}(),
			wantErr: true,
			errMsg:  "view 0 validation failed",
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

func TestView_Validate(t *testing.T) {
	tests := []struct {
		name    string
		view    View
		wantErr bool
		errMsg  string
	}{
		{
			name: "valid drop view",
			view: View{
				Type:           ViewTypeDrop,
				InstrumentName: "my-instrument",
			},
			wantErr: false,
		},
		{
			name: "valid rename view",
			view: View{
				Type:           ViewTypeRename,
				InstrumentName: "my-instrument",
				NewName:        "new-name",
			},
			wantErr: false,
		},
		{
			name: "valid change aggregation view",
			view: View{
				Type:           ViewTypeChangeAggregation,
				InstrumentName: "my-instrument",
				Aggregation:    AggregationSum,
			},
			wantErr: false,
		},
		{
			name: "invalid view type",
			view: View{
				Type:           ViewType("invalid"),
				InstrumentName: "my-instrument",
			},
			wantErr: true,
			errMsg:  "invalid view type",
		},
		{
			name: "missing instrument name",
			view: View{
				Type: ViewTypeDrop,
			},
			wantErr: true,
			errMsg:  "instrument name is required",
		},
		{
			name: "rename without new name",
			view: View{
				Type:           ViewTypeRename,
				InstrumentName: "my-instrument",
			},
			wantErr: true,
			errMsg:  "new name is required for rename view",
		},
		{
			name: "change aggregation without aggregation",
			view: View{
				Type:           ViewTypeChangeAggregation,
				InstrumentName: "my-instrument",
			},
			wantErr: true,
			errMsg:  "invalid aggregation type",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.view.Validate()
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestMeterOption_Apply_WrongType(t *testing.T) {
	opt := MeterOption(func(cfg *MeterConfig) error {
		return nil
	})

	err := opt.Apply("wrong type")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "expected *MeterConfig")
}

func TestWithMeterServiceName(t *testing.T) {
	tests := []struct {
		name    string
		service string
		wantErr bool
		errMsg  string
	}{
		{"valid name", "my-service", false, ""},
		{"empty name", "", true, "service name cannot be empty"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &MeterConfig{}
			opt := WithMeterServiceName(tt.service)
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

func TestWithMeterServiceVersion(t *testing.T) {
	cfg := &MeterConfig{}
	err := WithMeterServiceVersion("2.0.0")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "2.0.0", cfg.ServiceVersion)
}

func TestWithMetricExporter(t *testing.T) {
	tests := []struct {
		name     string
		exporter MetricExporterType
		wantErr  bool
		errMsg   string
	}{
		{"otlp", MetricExporterOTLP, false, ""},
		{"prometheus", MetricExporterPrometheus, false, ""},
		{"console", MetricExporterConsole, false, ""},
		{"invalid", MetricExporterType("invalid"), true, "invalid exporter type"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &MeterConfig{}
			opt := WithMetricExporter(tt.exporter)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.exporter, cfg.ExporterType)
			}
		})
	}
}

func TestWithTemporality(t *testing.T) {
	tests := []struct {
		name        string
		temporality AggregationTemporality
		wantErr     bool
		errMsg      string
	}{
		{"delta", AggregationTemporalityDelta, false, ""},
		{"cumulative", AggregationTemporalityCumulative, false, ""},
		{"invalid", AggregationTemporality("invalid"), true, "invalid temporality"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &MeterConfig{}
			opt := WithTemporality(tt.temporality)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.temporality, cfg.Temporality)
			}
		})
	}
}

func TestWithPeriodicReaderInterval(t *testing.T) {
	tests := []struct {
		name     string
		interval time.Duration
		wantErr  bool
		errMsg   string
	}{
		{"valid interval", 30 * time.Second, false, ""},
		{"one second", 1 * time.Second, false, ""},
		{"zero", 0, true, "periodic reader interval must be positive"},
		{"negative", -1 * time.Second, true, "periodic reader interval must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &MeterConfig{}
			opt := WithPeriodicReaderInterval(tt.interval)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.interval, cfg.PeriodicReaderInterval)
			}
		})
	}
}

func TestWithPeriodicReaderTimeout(t *testing.T) {
	tests := []struct {
		name    string
		timeout time.Duration
		wantErr bool
		errMsg  string
	}{
		{"valid timeout", 10 * time.Second, false, ""},
		{"one second", 1 * time.Second, false, ""},
		{"zero", 0, true, "periodic reader timeout must be positive"},
		{"negative", -1 * time.Second, true, "periodic reader timeout must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &MeterConfig{}
			opt := WithPeriodicReaderTimeout(tt.timeout)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.timeout, cfg.PeriodicReaderTimeout)
			}
		})
	}
}

func TestWithView(t *testing.T) {
	t.Run("valid view", func(t *testing.T) {
		cfg := &MeterConfig{Views: make([]View, 0)}
		view := View{
			Type:           ViewTypeDrop,
			InstrumentName: "test-instrument",
		}
		opt := WithView(view)
		err := opt(cfg)
		require.NoError(t, err)
		assert.Len(t, cfg.Views, 1)
		assert.Equal(t, "test-instrument", cfg.Views[0].InstrumentName)
	})

	t.Run("invalid view", func(t *testing.T) {
		cfg := &MeterConfig{Views: make([]View, 0)}
		view := View{
			Type: ViewTypeDrop,
		}
		opt := WithView(view)
		err := opt(cfg)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid view")
	})
}

func TestWithDropView(t *testing.T) {
	cfg := &MeterConfig{Views: make([]View, 0)}
	err := WithDropView("my-instrument")(cfg)
	require.NoError(t, err)
	assert.Len(t, cfg.Views, 1)
	assert.Equal(t, ViewTypeDrop, cfg.Views[0].Type)
	assert.Equal(t, "my-instrument", cfg.Views[0].InstrumentName)
}

func TestWithRenameView(t *testing.T) {
	cfg := &MeterConfig{Views: make([]View, 0)}
	err := WithRenameView("old-name", "new-name")(cfg)
	require.NoError(t, err)
	assert.Len(t, cfg.Views, 1)
	assert.Equal(t, ViewTypeRename, cfg.Views[0].Type)
	assert.Equal(t, "old-name", cfg.Views[0].InstrumentName)
	assert.Equal(t, "new-name", cfg.Views[0].NewName)
}

func TestWithChangeAggregationView(t *testing.T) {
	cfg := &MeterConfig{Views: make([]View, 0)}
	err := WithChangeAggregationView("my-instrument", AggregationSum)(cfg)
	require.NoError(t, err)
	assert.Len(t, cfg.Views, 1)
	assert.Equal(t, ViewTypeChangeAggregation, cfg.Views[0].Type)
	assert.Equal(t, "my-instrument", cfg.Views[0].InstrumentName)
	assert.Equal(t, AggregationSum, cfg.Views[0].Aggregation)
}

func TestWithMeterResourceAttribute(t *testing.T) {
	cfg := &MeterConfig{}

	err := WithMeterResourceAttribute("key1", "value1")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value1", cfg.ResourceAttributes["key1"])

	err = WithMeterResourceAttribute("key2", 456)(cfg)
	require.NoError(t, err)
	assert.Equal(t, 456, cfg.ResourceAttributes["key2"])
}

func TestWithMeterResourceAttributes(t *testing.T) {
	cfg := &MeterConfig{}

	attrs := map[string]interface{}{
		"key1": "value1",
		"key2": 789,
		"key3": false,
	}

	err := WithMeterResourceAttributes(attrs)(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value1", cfg.ResourceAttributes["key1"])
	assert.Equal(t, 789, cfg.ResourceAttributes["key2"])
	assert.Equal(t, false, cfg.ResourceAttributes["key3"])
}

func TestWithBuiltinMetricsDisabled(t *testing.T) {
	cfg := &MeterConfig{DisableBuiltinMetrics: false}
	err := WithBuiltinMetricsDisabled()(cfg)
	require.NoError(t, err)
	assert.True(t, cfg.DisableBuiltinMetrics)
}

func TestApplyMeterOptions(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		cfg, err := ApplyMeterOptions(
			WithMeterServiceName("test-service"),
			WithMeterServiceVersion("1.0.0"),
			WithMetricExporter(MetricExporterPrometheus),
		)
		require.NoError(t, err)
		assert.Equal(t, "test-service", cfg.ServiceName)
		assert.Equal(t, "1.0.0", cfg.ServiceVersion)
		assert.Equal(t, MetricExporterPrometheus, cfg.ExporterType)
	})

	t.Run("option error", func(t *testing.T) {
		cfg, err := ApplyMeterOptions(
			WithMeterServiceName(""),
		)
		require.Error(t, err)
		assert.Nil(t, cfg)
		assert.Contains(t, err.Error(), "service name cannot be empty")
	})

	t.Run("validation error", func(t *testing.T) {
		cfg, err := ApplyMeterOptions(
			WithMeterServiceName("test-service"),
			func(c *MeterConfig) error {
				c.PeriodicReaderInterval = 0
				return nil
			},
		)
		require.Error(t, err)
		assert.Nil(t, cfg)
		assert.Contains(t, err.Error(), "periodic reader interval must be positive")
	})
}

func TestMeterBaseEndpoint(t *testing.T) {
	cfg := &MeterConfig{}
	err := MeterBaseEndpoint("custom:4318")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "custom:4318", cfg.Endpoint)
}

func TestMeterBaseTimeout(t *testing.T) {
	cfg := &MeterConfig{}
	err := MeterBaseTimeout(5 * time.Second)(cfg)
	require.NoError(t, err)
	assert.Equal(t, 5*time.Second, cfg.Timeout)
}

func TestMeterBaseHeaders(t *testing.T) {
	cfg := &MeterConfig{}
	headers := map[string]string{"X-Custom": "value"}
	err := MeterBaseHeaders(headers)(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value", cfg.Headers["X-Custom"])
}

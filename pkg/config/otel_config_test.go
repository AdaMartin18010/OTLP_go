package config

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestOTelConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  OTelConfig
		wantErr bool
	}{
		{
			name: "valid config",
			config: OTelConfig{
				ServiceName: "test-service",
				Exporter: OTLPExporterConfig{
					Endpoint: "http://localhost:4317",
					Protocol: "grpc",
				},
				Sampling: SamplingConfig{
					Strategy: "always_on",
					Ratio:    1.0,
				},
				Logger: LoggerConfig{
					Level: "info",
				},
			},
			wantErr: false,
		},
		{
			name: "empty service name",
			config: OTelConfig{
				ServiceName: "",
				Exporter: OTLPExporterConfig{
					Endpoint: "http://localhost:4317",
				},
			},
			wantErr: true,
		},
		{
			name: "invalid protocol",
			config: OTelConfig{
				ServiceName: "test-service",
				Exporter: OTLPExporterConfig{
					Endpoint: "http://localhost:4317",
					Protocol: "invalid",
				},
			},
			wantErr: true,
		},
		{
			name: "empty endpoint",
			config: OTelConfig{
				ServiceName: "test-service",
				Exporter: OTLPExporterConfig{
					Endpoint: "",
				},
			},
			wantErr: true,
		},
		{
			name: "invalid sampling ratio - negative",
			config: OTelConfig{
				ServiceName: "test-service",
				Exporter: OTLPExporterConfig{
					Endpoint: "http://localhost:4317",
				},
				Sampling: SamplingConfig{
					Ratio: -0.5,
				},
			},
			wantErr: true,
		},
		{
			name: "invalid sampling ratio - over 1",
			config: OTelConfig{
				ServiceName: "test-service",
				Exporter: OTLPExporterConfig{
					Endpoint: "http://localhost:4317",
				},
				Sampling: SamplingConfig{
					Ratio: 1.5,
				},
			},
			wantErr: true,
		},
		{
			name: "invalid log level",
			config: OTelConfig{
				ServiceName: "test-service",
				Exporter: OTLPExporterConfig{
					Endpoint: "http://localhost:4317",
				},
				Logger: LoggerConfig{
					Level: "invalid",
				},
			},
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.wantErr {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}
		})
	}
}

func TestOTelConfig_GetTracesEndpoint(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Endpoint:       "http://default:4317",
			TracesEndpoint: "http://traces:4317",
		},
	}

	assert.Equal(t, "http://traces:4317", config.GetTracesEndpoint())

	// 当 TracesEndpoint 为空时，应返回 Endpoint
	config.Exporter.TracesEndpoint = ""
	assert.Equal(t, "http://default:4317", config.GetTracesEndpoint())
}

func TestOTelConfig_GetMetricsEndpoint(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Endpoint:        "http://default:4317",
			MetricsEndpoint: "http://metrics:4317",
		},
	}

	assert.Equal(t, "http://metrics:4317", config.GetMetricsEndpoint())

	config.Exporter.MetricsEndpoint = ""
	assert.Equal(t, "http://default:4317", config.GetMetricsEndpoint())
}

func TestOTelConfig_GetLogsEndpoint(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Endpoint:     "http://default:4317",
			LogsEndpoint: "http://logs:4317",
		},
	}

	assert.Equal(t, "http://logs:4317", config.GetLogsEndpoint())

	config.Exporter.LogsEndpoint = ""
	assert.Equal(t, "http://default:4317", config.GetLogsEndpoint())
}

func TestOTelConfig_GetTracesProtocol(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Protocol:       "grpc",
			TracesProtocol: "http/protobuf",
		},
	}

	assert.Equal(t, "http/protobuf", config.GetTracesProtocol())

	config.Exporter.TracesProtocol = ""
	assert.Equal(t, "grpc", config.GetTracesProtocol())
}

func TestOTelConfig_GetMetricsProtocol(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Protocol:        "grpc",
			MetricsProtocol: "http/protobuf",
		},
	}

	assert.Equal(t, "http/protobuf", config.GetMetricsProtocol())

	config.Exporter.MetricsProtocol = ""
	assert.Equal(t, "grpc", config.GetMetricsProtocol())
}

func TestOTelConfig_GetLogsProtocol(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Protocol:     "grpc",
			LogsProtocol: "http/protobuf",
		},
	}

	assert.Equal(t, "http/protobuf", config.GetLogsProtocol())

	config.Exporter.LogsProtocol = ""
	assert.Equal(t, "grpc", config.GetLogsProtocol())
}

func TestOTelConfig_GetTracesTimeout(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Timeout:       10 * time.Second,
			TracesTimeout: 30 * time.Second,
		},
	}

	assert.Equal(t, 30*time.Second, config.GetTracesTimeout())

	config.Exporter.TracesTimeout = 0
	assert.Equal(t, 10*time.Second, config.GetTracesTimeout())
}

func TestOTelConfig_GetMetricsTimeout(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Timeout:        10 * time.Second,
			MetricsTimeout: 30 * time.Second,
		},
	}

	assert.Equal(t, 30*time.Second, config.GetMetricsTimeout())

	config.Exporter.MetricsTimeout = 0
	assert.Equal(t, 10*time.Second, config.GetMetricsTimeout())
}

func TestOTelConfig_GetLogsTimeout(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Timeout:     10 * time.Second,
			LogsTimeout: 30 * time.Second,
		},
	}

	assert.Equal(t, 30*time.Second, config.GetLogsTimeout())

	config.Exporter.LogsTimeout = 0
	assert.Equal(t, 10*time.Second, config.GetLogsTimeout())
}

func TestOTelConfig_GetTracesHeaders(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Headers:       map[string]string{"key1": "value1"},
			TracesHeaders: map[string]string{"key2": "value2"},
		},
	}

	assert.Equal(t, map[string]string{"key2": "value2"}, config.GetTracesHeaders())

	config.Exporter.TracesHeaders = nil
	assert.Equal(t, map[string]string{"key1": "value1"}, config.GetTracesHeaders())
}

func TestOTelConfig_GetMetricsHeaders(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Headers:        map[string]string{"key1": "value1"},
			MetricsHeaders: map[string]string{"key2": "value2"},
		},
	}

	assert.Equal(t, map[string]string{"key2": "value2"}, config.GetMetricsHeaders())

	config.Exporter.MetricsHeaders = nil
	assert.Equal(t, map[string]string{"key1": "value1"}, config.GetMetricsHeaders())
}

func TestOTelConfig_GetLogsHeaders(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Headers:     map[string]string{"key1": "value1"},
			LogsHeaders: map[string]string{"key2": "value2"},
		},
	}

	assert.Equal(t, map[string]string{"key2": "value2"}, config.GetLogsHeaders())

	config.Exporter.LogsHeaders = nil
	assert.Equal(t, map[string]string{"key1": "value1"}, config.GetLogsHeaders())
}

func TestOTelConfig_GetPropagators(t *testing.T) {
	config := OTelConfig{
		Propagator: PropagatorConfig{
			Propagators: []string{"tracecontext", "baggage", "b3"},
		},
	}

	assert.Equal(t, []string{"tracecontext", "baggage", "b3"}, config.GetPropagators())

	// 当 Propagators 为空时，应返回默认值
	config.Propagator.Propagators = nil
	assert.Equal(t, []string{"tracecontext", "baggage"}, config.GetPropagators())
}

func TestLoadOTelConfig(t *testing.T) {
	m := New()
	m.Set("service_name", "test-service")
	m.Set("service_version", "1.0.0")
	m.Set("exporter.endpoint", "http://localhost:4317")
	m.Set("exporter.protocol", "grpc")
	m.Set("sampling.strategy", "always_on")
	m.Set("logger.level", "info")

	ctx := context.Background()
	config, err := LoadOTelConfig(ctx, m)
	require.NoError(t, err)

	assert.Equal(t, "test-service", config.ServiceName)
	assert.Equal(t, "1.0.0", config.ServiceVersion)
	assert.Equal(t, "http://localhost:4317", config.Exporter.Endpoint)
	assert.Equal(t, "grpc", config.Exporter.Protocol)
	assert.Equal(t, "always_on", config.Sampling.Strategy)
	assert.Equal(t, "info", config.Logger.Level)
}

func TestLoadOTelConfig_ValidationError(t *testing.T) {
	m := New()
	m.Set("service_name", "") // 空服务名

	ctx := context.Background()
	_, err := LoadOTelConfig(ctx, m)
	assert.Error(t, err)
}

func TestOTelConfig_Defaults(t *testing.T) {
	config := OTelConfig{}

	// 设置一些默认值
	if config.ServiceName == "" {
		config.ServiceName = "unknown_service"
	}
	if config.ServiceVersion == "" {
		config.ServiceVersion = "1.0.0"
	}
	if config.Exporter.Endpoint == "" {
		config.Exporter.Endpoint = "http://localhost:4317"
	}
	if config.Exporter.Protocol == "" {
		config.Exporter.Protocol = "grpc"
	}
	if config.Logger.Level == "" {
		config.Logger.Level = "info"
	}

	assert.Equal(t, "unknown_service", config.ServiceName)
	assert.Equal(t, "1.0.0", config.ServiceVersion)
	assert.Equal(t, "http://localhost:4317", config.Exporter.Endpoint)
	assert.Equal(t, "grpc", config.Exporter.Protocol)
	assert.Equal(t, "info", config.Logger.Level)
}

func TestOTelConfig_ComplexStructure(t *testing.T) {
	m := New()

	// 设置复杂的嵌套配置
	m.Set("service_name", "complex-service")
	m.Set("exporter.endpoint", "http://otel:4317")
	m.Set("exporter.timeout", "10s")
	m.Set("exporter.headers", map[string]string{
		"Authorization": "Bearer token123",
		"X-Custom":      "value",
	})
	m.Set("batch.traces_max_queue_size", 4096)
	m.Set("batch.traces_schedule_delay", "5s")
	m.Set("resource.attributes", map[string]string{
		"deployment.environment": "production",
		"host.name":              "server-01",
	})
	m.Set("meter.views", []map[string]interface{}{
		{
			"instrument_name": "request_count",
			"aggregation":     "sum",
		},
		{
			"instrument_name": "request_duration",
			"aggregation":     "histogram",
		},
	})

	ctx := context.Background()
	config, err := LoadOTelConfig(ctx, m)
	require.NoError(t, err)

	assert.Equal(t, "complex-service", config.ServiceName)
	assert.Equal(t, "http://otel:4317", config.Exporter.Endpoint)
	assert.Equal(t, 10*time.Second, config.Exporter.Timeout)
	assert.Equal(t, "Bearer token123", config.Exporter.Headers["Authorization"])
	assert.Equal(t, 4096, config.Batch.TracesMaxQueueSize)
	assert.Equal(t, 5*time.Second, config.Batch.TracesScheduleDelay)
	assert.Equal(t, "production", config.Resource.Attributes["deployment.environment"])
}

func TestRetryConfig_Values(t *testing.T) {
	config := OTelConfig{
		Exporter: OTLPExporterConfig{
			Retry: RetryConfig{
				Enabled:         true,
				InitialInterval: 1 * time.Second,
				MaxInterval:     5 * time.Second,
				MaxElapsedTime:  30 * time.Second,
			},
		},
	}

	assert.True(t, config.Exporter.Retry.Enabled)
	assert.Equal(t, 1*time.Second, config.Exporter.Retry.InitialInterval)
	assert.Equal(t, 5*time.Second, config.Exporter.Retry.MaxInterval)
	assert.Equal(t, 30*time.Second, config.Exporter.Retry.MaxElapsedTime)
}

func TestBatchConfig_Values(t *testing.T) {
	config := OTelConfig{
		Batch: BatchConfig{
			TracesMaxQueueSize:       2048,
			TracesMaxExportBatchSize: 512,
			TracesScheduleDelay:      5 * time.Second,
			TracesExportTimeout:      30 * time.Second,
			MetricsExportTimeout:     30 * time.Second,
			MetricsExportInterval:    60 * time.Second,
			LogsMaxQueueSize:         2048,
			LogsMaxExportBatchSize:   512,
			LogsScheduleDelay:        5 * time.Second,
			LogsExportTimeout:        30 * time.Second,
		},
	}

	assert.Equal(t, 2048, config.Batch.TracesMaxQueueSize)
	assert.Equal(t, 512, config.Batch.TracesMaxExportBatchSize)
	assert.Equal(t, 5*time.Second, config.Batch.TracesScheduleDelay)
	assert.Equal(t, 30*time.Second, config.Batch.TracesExportTimeout)
	assert.Equal(t, 60*time.Second, config.Batch.MetricsExportInterval)
}

func TestSamplingConfig_Values(t *testing.T) {
	config := OTelConfig{
		Sampling: SamplingConfig{
			Strategy: "parentbased_traceidratio",
			Ratio:    0.5,
			ParentBased: ParentBasedSamplingConfig{
				Root:             "traceidratio",
				RemoteSampled:    "always_on",
				RemoteNotSampled: "always_off",
				LocalSampled:     "always_on",
				LocalNotSampled:  "always_off",
			},
		},
	}

	assert.Equal(t, "parentbased_traceidratio", config.Sampling.Strategy)
	assert.InDelta(t, 0.5, config.Sampling.Ratio, 0.001)
	assert.Equal(t, "traceidratio", config.Sampling.ParentBased.Root)
}

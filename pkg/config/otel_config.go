package config

import (
	"context"
	"fmt"
	"time"
)

// OTelConfig 是 OpenTelemetry 的专用配置结构
type OTelConfig struct {
	// 服务信息
	ServiceName    string `mapstructure:"service_name" env:"OTEL_SERVICE_NAME" default:"unknown_service"`
	ServiceVersion string `mapstructure:"service_version" env:"OTEL_SERVICE_VERSION" default:"1.0.0"`
	ServiceNamespace string `mapstructure:"service_namespace" env:"OTEL_SERVICE_NAMESPACE"`
	DeploymentEnvironment string `mapstructure:"deployment_environment" env:"OTEL_DEPLOYMENT_ENVIRONMENT" default:"development"`

	// OTLP 导出器配置
	Exporter OTLPExporterConfig `mapstructure:"exporter"`

	// 批处理器配置
	Batch BatchConfig `mapstructure:"batch"`

	// 资源配置
	Resource ResourceConfig `mapstructure:"resource"`

	// 追踪配置
	Tracer TracerConfig `mapstructure:"tracer"`

	// 指标配置
	Meter MeterConfig `mapstructure:"meter"`

	// 日志配置
	Logger LoggerConfig `mapstructure:"logger"`

	// 采样配置
	Sampling SamplingConfig `mapstructure:"sampling"`

	// 传播器配置
	Propagator PropagatorConfig `mapstructure:"propagator"`
}

// OTLPExporterConfig OTLP 导出器配置
type OTLPExporterConfig struct {
	// 端点配置
	Endpoint string `mapstructure:"endpoint" env:"OTEL_EXPORTER_OTLP_ENDPOINT" default:"http://localhost:4317"`
	TracesEndpoint string `mapstructure:"traces_endpoint" env:"OTEL_EXPORTER_OTLP_TRACES_ENDPOINT"`
	MetricsEndpoint string `mapstructure:"metrics_endpoint" env:"OTEL_EXPORTER_OTLP_METRICS_ENDPOINT"`
	LogsEndpoint string `mapstructure:"logs_endpoint" env:"OTEL_EXPORTER_OTLP_LOGS_ENDPOINT"`

	// 协议配置 (grpc 或 http/protobuf)
	Protocol string `mapstructure:"protocol" env:"OTEL_EXPORTER_OTLP_PROTOCOL" default:"grpc"`
	TracesProtocol string `mapstructure:"traces_protocol" env:"OTEL_EXPORTER_OTLP_TRACES_PROTOCOL"`
	MetricsProtocol string `mapstructure:"metrics_protocol" env:"OTEL_EXPORTER_OTLP_METRICS_PROTOCOL"`
	LogsProtocol string `mapstructure:"logs_protocol" env:"OTEL_EXPORTER_OTLP_LOGS_PROTOCOL"`

	// 证书配置
	CertificatePath string `mapstructure:"certificate" env:"OTEL_EXPORTER_OTLP_CERTIFICATE"`
	ClientKeyPath string `mapstructure:"client_key" env:"OTEL_EXPORTER_OTLP_CLIENT_KEY"`
	ClientCertificatePath string `mapstructure:"client_certificate" env:"OTEL_EXPORTER_OTLP_CLIENT_CERTIFICATE"`

	// 头部配置
	Headers map[string]string `mapstructure:"headers" env:"OTEL_EXPORTER_OTLP_HEADERS"`
	TracesHeaders map[string]string `mapstructure:"traces_headers" env:"OTEL_EXPORTER_OTLP_TRACES_HEADERS"`
	MetricsHeaders map[string]string `mapstructure:"metrics_headers" env:"OTEL_EXPORTER_OTLP_METRICS_HEADERS"`
	LogsHeaders map[string]string `mapstructure:"logs_headers" env:"OTEL_EXPORTER_OTLP_LOGS_HEADERS"`

	// 压缩配置
	Compression string `mapstructure:"compression" env:"OTEL_EXPORTER_OTLP_COMPRESSION" default:"gzip"`

	// 超时配置
	Timeout time.Duration `mapstructure:"timeout" env:"OTEL_EXPORTER_OTLP_TIMEOUT" default:"10s"`
	TracesTimeout time.Duration `mapstructure:"traces_timeout" env:"OTEL_EXPORTER_OTLP_TRACES_TIMEOUT"`
	MetricsTimeout time.Duration `mapstructure:"metrics_timeout" env:"OTEL_EXPORTER_OTLP_METRICS_TIMEOUT"`
	LogsTimeout time.Duration `mapstructure:"logs_timeout" env:"OTEL_EXPORTER_OTLP_LOGS_TIMEOUT"`

	// 重试配置
	Retry RetryConfig `mapstructure:"retry"`
}

// RetryConfig 重试配置
type RetryConfig struct {
	Enabled         bool          `mapstructure:"enabled" default:"true"`
	InitialInterval time.Duration `mapstructure:"initial_interval" default:"1s"`
	MaxInterval     time.Duration `mapstructure:"max_interval" default:"5s"`
	MaxElapsedTime  time.Duration `mapstructure:"max_elapsed_time" default:"30s"`
}

// BatchConfig 批处理器配置
type BatchConfig struct {
	// 追踪批处理配置
	TracesMaxQueueSize    int           `mapstructure:"traces_max_queue_size" env:"OTEL_BSP_MAX_QUEUE_SIZE" default:"2048"`
	TracesMaxExportBatchSize int        `mapstructure:"traces_max_export_batch_size" env:"OTEL_BSP_MAX_EXPORT_BATCH_SIZE" default:"512"`
	TracesScheduleDelay   time.Duration `mapstructure:"traces_schedule_delay" env:"OTEL_BSP_SCHEDULE_DELAY" default:"5s"`
	TracesExportTimeout   time.Duration `mapstructure:"traces_export_timeout" env:"OTEL_BSP_EXPORT_TIMEOUT" default:"30s"`

	// 指标批处理配置
	MetricsExportTimeout  time.Duration `mapstructure:"metrics_export_timeout" env:"OTEL_METRIC_EXPORT_TIMEOUT" default:"30s"`
	MetricsExportInterval time.Duration `mapstructure:"metrics_export_interval" env:"OTEL_METRIC_EXPORT_INTERVAL" default:"60s"`

	// 日志批处理配置
	LogsMaxQueueSize      int           `mapstructure:"logs_max_queue_size" default:"2048"`
	LogsMaxExportBatchSize int          `mapstructure:"logs_max_export_batch_size" default:"512"`
	LogsScheduleDelay     time.Duration `mapstructure:"logs_schedule_delay" default:"5s"`
	LogsExportTimeout     time.Duration `mapstructure:"logs_export_timeout" default:"30s"`
}

// ResourceConfig 资源配置
type ResourceConfig struct {
	// 自定义资源属性
	Attributes map[string]string `mapstructure:"attributes" env:"OTEL_RESOURCE_ATTRIBUTES"`
	
	// 是否禁用内置资源检测
	DisableBuiltins bool `mapstructure:"disable_builtins" env:"OTEL_RESOURCE_DISABLE_BUILTINS" default:"false"`
}

// TracerConfig 追踪器配置
type TracerConfig struct {
	Enabled bool `mapstructure:"enabled" env:"OTEL_TRACES_ENABLED" default:"true"`
}

// MeterConfig 指标器配置
type MeterConfig struct {
	Enabled bool `mapstructure:"enabled" env:"OTEL_METRICS_ENABLED" default:"true"`
	// 视图配置（高级）
	Views []ViewConfig `mapstructure:"views"`
}

// ViewConfig 视图配置
type ViewConfig struct {
	InstrumentType string   `mapstructure:"instrument_type"`
	InstrumentName string   `mapstructure:"instrument_name"`
	MeterName      string   `mapstructure:"meter_name"`
	MeterVersion   string   `mapstructure:"meter_version"`
	AttributeKeys  []string `mapstructure:"attribute_keys"`
	Aggregation    string   `mapstructure:"aggregation"`
}

// LoggerConfig 日志器配置
type LoggerConfig struct {
	Enabled bool `mapstructure:"enabled" env:"OTEL_LOGS_ENABLED" default:"false"`
	Level   string `mapstructure:"level" env:"OTEL_LOG_LEVEL" default:"info"`
}

// SamplingConfig 采样配置
type SamplingConfig struct {
	// 采样策略: always_on, always_off, traceidratio, parentbased_always_on, parentbased_always_off, parentbased_traceidratio
	Strategy string `mapstructure:"strategy" env:"OTEL_TRACES_SAMPLER" default:"parentbased_always_on"`

	// 采样比率 (0.0 - 1.0)
	Ratio float64 `mapstructure:"ratio" env:"OTEL_TRACES_SAMPLER_ARG" default:"1.0"`

	// 父级采样配置
	ParentBased ParentBasedSamplingConfig `mapstructure:"parent_based"`
}

// ParentBasedSamplingConfig 父级采样配置
type ParentBasedSamplingConfig struct {
	Root             string  `mapstructure:"root" default:"traceidratio"`
	RemoteSampled    string  `mapstructure:"remote_sampled" default:"always_on"`
	RemoteNotSampled string  `mapstructure:"remote_not_sampled" default:"always_off"`
	LocalSampled     string  `mapstructure:"local_sampled" default:"always_on"`
	LocalNotSampled  string  `mapstructure:"local_not_sampled" default:"always_off"`
}

// PropagatorConfig 传播器配置
type PropagatorConfig struct {
	// 传播器列表: tracecontext, baggage, b3, b3multi, jaeger, ottrace, xray, ottracer, none
	Propagators []string `mapstructure:"propagators" env:"OTEL_PROPAGATORS" default:"tracecontext,baggage"`
}

// LoadOTelConfig 加载 OpenTelemetry 配置
func LoadOTelConfig(ctx context.Context, config Config) (*OTelConfig, error) {
	var otelConfig OTelConfig

	// 从通用配置反序列化
	if err := config.Unmarshal(&otelConfig); err != nil {
		return nil, fmt.Errorf("failed to unmarshal OTel config: %w", err)
	}

	// 应用环境变量覆盖
	if err := applyEnvDefaults(&otelConfig); err != nil {
		return nil, fmt.Errorf("failed to apply environment defaults: %w", err)
	}

	// 验证配置
	if err := otelConfig.Validate(); err != nil {
		return nil, fmt.Errorf("OTel config validation failed: %w", err)
	}

	return &otelConfig, nil
}

// Validate 验证 OTel 配置
func (c *OTelConfig) Validate() error {
	// 验证服务名称
	if c.ServiceName == "" {
		return fmt.Errorf("service name cannot be empty")
	}

	// 验证导出器协议
	validProtocols := map[string]bool{"grpc": true, "http": true, "http/protobuf": true}
	protocol := c.Exporter.Protocol
	if c.Exporter.TracesProtocol != "" {
		protocol = c.Exporter.TracesProtocol
	}
	if !validProtocols[protocol] {
		return fmt.Errorf("invalid protocol: %s", protocol)
	}

	// 验证端点
	if c.Exporter.Endpoint == "" {
		return fmt.Errorf("exporter endpoint cannot be empty")
	}

	// 验证采样比率
	if c.Sampling.Ratio < 0 || c.Sampling.Ratio > 1 {
		return fmt.Errorf("sampling ratio must be between 0 and 1")
	}

	// 验证日志级别
	validLevels := map[string]bool{"debug": true, "info": true, "warn": true, "error": true}
	if !validLevels[c.Logger.Level] {
		return fmt.Errorf("invalid log level: %s", c.Logger.Level)
	}

	return nil
}

// GetTracesEndpoint 获取追踪端点
func (c *OTelConfig) GetTracesEndpoint() string {
	if c.Exporter.TracesEndpoint != "" {
		return c.Exporter.TracesEndpoint
	}
	return c.Exporter.Endpoint
}

// GetMetricsEndpoint 获取指标端点
func (c *OTelConfig) GetMetricsEndpoint() string {
	if c.Exporter.MetricsEndpoint != "" {
		return c.Exporter.MetricsEndpoint
	}
	return c.Exporter.Endpoint
}

// GetLogsEndpoint 获取日志端点
func (c *OTelConfig) GetLogsEndpoint() string {
	if c.Exporter.LogsEndpoint != "" {
		return c.Exporter.LogsEndpoint
	}
	return c.Exporter.Endpoint
}

// GetTracesProtocol 获取追踪协议
func (c *OTelConfig) GetTracesProtocol() string {
	if c.Exporter.TracesProtocol != "" {
		return c.Exporter.TracesProtocol
	}
	return c.Exporter.Protocol
}

// GetMetricsProtocol 获取指标协议
func (c *OTelConfig) GetMetricsProtocol() string {
	if c.Exporter.MetricsProtocol != "" {
		return c.Exporter.MetricsProtocol
	}
	return c.Exporter.Protocol
}

// GetLogsProtocol 获取日志协议
func (c *OTelConfig) GetLogsProtocol() string {
	if c.Exporter.LogsProtocol != "" {
		return c.Exporter.LogsProtocol
	}
	return c.Exporter.Protocol
}

// GetTracesTimeout 获取追踪超时
func (c *OTelConfig) GetTracesTimeout() time.Duration {
	if c.Exporter.TracesTimeout > 0 {
		return c.Exporter.TracesTimeout
	}
	return c.Exporter.Timeout
}

// GetMetricsTimeout 获取指标超时
func (c *OTelConfig) GetMetricsTimeout() time.Duration {
	if c.Exporter.MetricsTimeout > 0 {
		return c.Exporter.MetricsTimeout
	}
	return c.Exporter.Timeout
}

// GetLogsTimeout 获取日志超时
func (c *OTelConfig) GetLogsTimeout() time.Duration {
	if c.Exporter.LogsTimeout > 0 {
		return c.Exporter.LogsTimeout
	}
	return c.Exporter.Timeout
}

// GetTracesHeaders 获取追踪头部
func (c *OTelConfig) GetTracesHeaders() map[string]string {
	if len(c.Exporter.TracesHeaders) > 0 {
		return c.Exporter.TracesHeaders
	}
	return c.Exporter.Headers
}

// GetMetricsHeaders 获取指标头部
func (c *OTelConfig) GetMetricsHeaders() map[string]string {
	if len(c.Exporter.MetricsHeaders) > 0 {
		return c.Exporter.MetricsHeaders
	}
	return c.Exporter.Headers
}

// GetLogsHeaders 获取日志头部
func (c *OTelConfig) GetLogsHeaders() map[string]string {
	if len(c.Exporter.LogsHeaders) > 0 {
		return c.Exporter.LogsHeaders
	}
	return c.Exporter.Headers
}

// GetPropagators 获取传播器列表
func (c *OTelConfig) GetPropagators() []string {
	if len(c.Propagator.Propagators) == 0 {
		return []string{"tracecontext", "baggage"}
	}
	return c.Propagator.Propagators
}

// applyEnvDefaults 应用环境变量默认值
func applyEnvDefaults(config *OTelConfig) error {
	// 这个函数用于在反序列化后应用环境变量的默认值
	// 实际的值已经从 mapstructure 标签中读取
	// 这里可以添加额外的逻辑
	return nil
}

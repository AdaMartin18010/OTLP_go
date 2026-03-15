// Package otel provides OpenTelemetry SDK initialization and management
// for the OTLP Go SDK.
//
// This package handles:
//   - TracerProvider setup
//   - MeterProvider setup
//   - LoggerProvider setup
//   - Resource detection
//   - Graceful shutdown
//
// Example usage:
//
//	otelSDK, err := otel.Setup(ctx, otel.Config{
//	    ServiceName: "my-service",
//	    Endpoint:    "localhost:4317",
//	})
//	if err != nil {
//	    log.Fatal(err)
//	}
//	defer otelSDK.Shutdown(ctx)
package otel

import (
	"context"
	"fmt"

	"github.com/OTLP_go/pkg/config"
)

// Config 是 OpenTelemetry 配置的便捷别名
type Config = config.OTelConfig

// LoadConfig 加载 OpenTelemetry 配置
func LoadConfig(ctx context.Context, cfg config.Config) (*Config, error) {
	return config.LoadOTelConfig(ctx, cfg)
}

// DefaultConfig 返回默认配置
func DefaultConfig() *Config {
	return &Config{
		ServiceName:           "unknown_service",
		ServiceVersion:        "1.0.0",
		DeploymentEnvironment: "development",
		Exporter: config.OTLPExporterConfig{
			Endpoint:    "http://localhost:4317",
			Protocol:    "grpc",
			Compression: "gzip",
			Timeout:     10000000000, // 10s
			Headers:     make(map[string]string),
			Retry: config.RetryConfig{
				Enabled:         true,
				InitialInterval: 1000000000,  // 1s
				MaxInterval:     5000000000,  // 5s
				MaxElapsedTime:  30000000000, // 30s
			},
		},
		Batch: config.BatchConfig{
			TracesMaxQueueSize:       2048,
			TracesMaxExportBatchSize: 512,
			TracesScheduleDelay:      5000000000,  // 5s
			TracesExportTimeout:      30000000000, // 30s
			MetricsExportTimeout:     30000000000, // 30s
			MetricsExportInterval:    60000000000, // 60s
			LogsMaxQueueSize:         2048,
			LogsMaxExportBatchSize:   512,
			LogsScheduleDelay:        5000000000,  // 5s
			LogsExportTimeout:        30000000000, // 30s
		},
		Resource: config.ResourceConfig{
			Attributes:      make(map[string]string),
			DisableBuiltins: false,
		},
		Tracer: config.TracerConfig{
			Enabled: true,
		},
		Meter: config.MeterConfig{
			Enabled: true,
		},
		Logger: config.LoggerConfig{
			Enabled: false,
			Level:   "info",
		},
		Sampling: config.SamplingConfig{
			Strategy: "parentbased_always_on",
			Ratio:    1.0,
		},
		Propagator: config.PropagatorConfig{
			Propagators: []string{"tracecontext", "baggage"},
		},
	}
}

// QuickSetup 快速设置 OpenTelemetry SDK（使用默认配置）
func QuickSetup(ctx context.Context, serviceName string, endpoint ...string) (*SDK, error) {
	cfg := DefaultConfig()
	cfg.ServiceName = serviceName
	
	if len(endpoint) > 0 && endpoint[0] != "" {
		cfg.Exporter.Endpoint = endpoint[0]
	}

	return Setup(ctx, cfg)
}

// QuickSetupWithOptions 使用选项快速设置
func QuickSetupWithOptions(ctx context.Context, serviceName string, opts ...SDKOption) (*SDK, error) {
	cfg := DefaultConfig()
	cfg.ServiceName = serviceName

	return Setup(ctx, cfg, opts...)
}

// MustSetup 设置 OpenTelemetry SDK，失败时 panic
func MustSetup(ctx context.Context, cfg *Config, opts ...SDKOption) *SDK {
	sdk, err := Setup(ctx, cfg, opts...)
	if err != nil {
		panic(fmt.Sprintf("failed to setup OpenTelemetry SDK: %v", err))
	}
	return sdk
}

// Global 返回全局 SDK 实例（如果已设置）
var globalSDK *SDK

// SetGlobalSDK 设置全局 SDK 实例
func SetGlobalSDK(sdk *SDK) {
	globalSDK = sdk
}

// GetGlobalSDK 获取全局 SDK 实例
func GetGlobalSDK() *SDK {
	return globalSDK
}

// GlobalTracer 返回全局 Tracer
func GlobalTracer(name string) *TracerWrapper {
	if globalSDK == nil || globalSDK.TracerProvider == nil {
		return nil
	}
	return NewTracerWrapper(globalSDK.TracerProvider, name)
}

// GlobalMeter 返回全局 Meter
func GlobalMeter(name string) *MeterWrapper {
	if globalSDK == nil || globalSDK.MeterProvider == nil {
		return nil
	}
	return NewMeterWrapper(globalSDK.MeterProvider, name)
}

// GlobalShutdown 关闭全局 SDK
func GlobalShutdown(ctx context.Context) error {
	if globalSDK == nil {
		return nil
	}
	err := globalSDK.Shutdown(ctx)
	globalSDK = nil
	return err
}

// Version 返回包版本
func Version() string {
	return "1.0.0"
}

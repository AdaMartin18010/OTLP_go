package otel

import (
	"context"
	"fmt"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	"go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	oteltrace "go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc"

	"OTLP_go/src/pkg/config"
	otelresource "OTLP_go/src/pkg/resource"
)

// OTelManager OpenTelemetry 管理器
type OTelManager struct {
	tracerProvider *trace.TracerProvider
	config         *config.OTLPConfig
	cleanupFunc    func() error
}

// NewOTelManager 创建 OpenTelemetry 管理器
func NewOTelManager(cfg *config.OTLPConfig) *OTelManager {
	return &OTelManager{
		config: cfg,
	}
}

// Initialize 初始化 OpenTelemetry
func (m *OTelManager) Initialize(ctx context.Context) error {
	// 验证配置
	if err := config.ValidateOTLPConfig(m.config); err != nil {
		return fmt.Errorf("invalid OTLP config: %w", err)
	}

	// 创建 OTLP gRPC Exporter
	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint(m.config.Endpoint),
		otlptracegrpc.WithInsecure(),
		otlptracegrpc.WithDialOption(grpc.WithBlock()),
	)
	if err != nil {
		return fmt.Errorf("failed to create exporter: %w", err)
	}

	// 创建 Resource
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName(m.config.ServiceName),
			semconv.ServiceVersion(m.config.ServiceVersion),
			semconv.DeploymentEnvironment(m.config.Environment),
		),
	)
	if err != nil {
		return fmt.Errorf("failed to create resource: %w", err)
	}

	// 创建 TracerProvider
	m.tracerProvider = trace.NewTracerProvider(
		trace.WithBatcher(exporter,
			trace.WithMaxQueueSize(2048),
			trace.WithMaxExportBatchSize(512),
			trace.WithBatchTimeout(5*time.Second),
		),
		trace.WithResource(res),
		trace.WithSampler(trace.TraceIDRatioBased(m.config.SamplingRate)),
	)

	// 设置全局 TracerProvider
	otel.SetTracerProvider(m.tracerProvider)

	// 设置全局 Propagator
	otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
		propagation.TraceContext{},
		propagation.Baggage{},
	))

	// 设置清理函数
	m.cleanupFunc = func() error {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()

		if err := m.tracerProvider.Shutdown(ctx); err != nil {
			return fmt.Errorf("failed to shutdown tracer provider: %w", err)
		}

		return nil
	}

	log.Printf("OpenTelemetry initialized successfully - Service: %s, Endpoint: %s",
		m.config.ServiceName, m.config.Endpoint)

	return nil
}

// Shutdown 关闭 OpenTelemetry
func (m *OTelManager) Shutdown(ctx context.Context) error {
	if m.cleanupFunc != nil {
		return m.cleanupFunc()
	}
	return nil
}

// IsHealthy 检查健康状态
func (m *OTelManager) IsHealthy() bool {
	return m.tracerProvider != nil
}

// GetName 获取资源名称
func (m *OTelManager) GetName() string {
	return "opentelemetry"
}

// GetTracerProvider 获取 TracerProvider
func (m *OTelManager) GetTracerProvider() *trace.TracerProvider {
	return m.tracerProvider
}

// GetConfig 获取配置
func (m *OTelManager) GetConfig() *config.OTLPConfig {
	return m.config
}

// 实现 Resource 接口
var _ otelresource.Resource = (*OTelManager)(nil)

// 全局 OpenTelemetry 管理器
var globalOTelManager *OTelManager

// InitializeGlobalOTel 初始化全局 OpenTelemetry
func InitializeGlobalOTel(ctx context.Context, cfg *config.OTLPConfig) error {
	globalOTelManager = NewOTelManager(cfg)
	return globalOTelManager.Initialize(ctx)
}

// ShutdownGlobalOTel 关闭全局 OpenTelemetry
func ShutdownGlobalOTel(ctx context.Context) error {
	if globalOTelManager != nil {
		return globalOTelManager.Shutdown(ctx)
	}
	return nil
}

// GetGlobalOTelManager 获取全局 OpenTelemetry 管理器
func GetGlobalOTelManager() *OTelManager {
	return globalOTelManager
}

// 便捷函数

// GetTracer 获取 Tracer
func GetTracer(name string) oteltrace.Tracer {
	return otel.Tracer(name)
}

// GetTextMapPropagator 获取 TextMapPropagator
func GetTextMapPropagator() propagation.TextMapPropagator {
	return otel.GetTextMapPropagator()
}

// 配置辅助函数

// LoadAndInitializeOTel 加载配置并初始化 OpenTelemetry
func LoadAndInitializeOTel(ctx context.Context) error {
	cfg := config.LoadOTLPConfig()
	return InitializeGlobalOTel(ctx, cfg)
}

// LoadAndInitializeOTelWithDefaults 使用默认配置初始化 OpenTelemetry
func LoadAndInitializeOTelWithDefaults(ctx context.Context) error {
	cfg := config.DefaultOTLPConfig()
	return InitializeGlobalOTel(ctx, cfg)
}

// 健康检查

// HealthCheck 健康检查
type HealthCheck struct {
	Status   string            `json:"status"`
	Service  string            `json:"service"`
	Version  string            `json:"version"`
	Endpoint string            `json:"endpoint"`
	Sampling float64           `json:"sampling_rate"`
	Uptime   time.Duration     `json:"uptime,omitempty"`
	Metadata map[string]string `json:"metadata,omitempty"`
}

// GetHealthStatus 获取健康状态
func (m *OTelManager) GetHealthStatus() *HealthCheck {
	status := "healthy"
	if !m.IsHealthy() {
		status = "unhealthy"
	}

	return &HealthCheck{
		Status:   status,
		Service:  m.config.ServiceName,
		Version:  m.config.ServiceVersion,
		Endpoint: m.config.Endpoint,
		Sampling: m.config.SamplingRate,
		Metadata: map[string]string{
			"environment": m.config.Environment,
			"insecure":    fmt.Sprintf("%t", m.config.Insecure),
		},
	}
}

// 性能监控

// PerformanceMetrics 性能指标
type PerformanceMetrics struct {
	ActiveSpans   int64         `json:"active_spans"`
	ExportedSpans int64         `json:"exported_spans"`
	DroppedSpans  int64         `json:"dropped_spans"`
	QueueSize     int64         `json:"queue_size"`
	ExportLatency time.Duration `json:"export_latency"`
}

// GetPerformanceMetrics 获取性能指标
func (m *OTelManager) GetPerformanceMetrics() *PerformanceMetrics {
	// 这里可以添加实际的性能指标收集逻辑
	// 目前返回模拟数据
	return &PerformanceMetrics{
		ActiveSpans:   0,
		ExportedSpans: 0,
		DroppedSpans:  0,
		QueueSize:     0,
		ExportLatency: 0,
	}
}

// 配置更新

// UpdateConfig 更新配置
func (m *OTelManager) UpdateConfig(newConfig *config.OTLPConfig) error {
	// 验证新配置
	if err := config.ValidateOTLPConfig(newConfig); err != nil {
		return fmt.Errorf("invalid config: %w", err)
	}

	// 关闭当前实例
	if m.cleanupFunc != nil {
		if err := m.cleanupFunc(); err != nil {
			log.Printf("Warning: failed to shutdown existing OTel instance: %v", err)
		}
	}

	// 更新配置
	m.config = newConfig

	// 重新初始化
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	return m.Initialize(ctx)
}

// 调试和诊断

// DebugInfo 调试信息
type DebugInfo struct {
	Config         *config.OTLPConfig `json:"config"`
	IsHealthy      bool               `json:"is_healthy"`
	ServiceName    string             `json:"service_name"`
	ServiceVersion string             `json:"service_version"`
	Environment    string             `json:"environment"`
	Endpoint       string             `json:"endpoint"`
	SamplingRate   float64            `json:"sampling_rate"`
	Insecure       bool               `json:"insecure"`
}

// GetDebugInfo 获取调试信息
func (m *OTelManager) GetDebugInfo() *DebugInfo {
	return &DebugInfo{
		Config:         m.config,
		IsHealthy:      m.IsHealthy(),
		ServiceName:    m.config.ServiceName,
		ServiceVersion: m.config.ServiceVersion,
		Environment:    m.config.Environment,
		Endpoint:       m.config.Endpoint,
		SamplingRate:   m.config.SamplingRate,
		Insecure:       m.config.Insecure,
	}
}

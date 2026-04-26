// Package otel provides OpenTelemetry SDK initialization and management
// for the OTLP Go SDK.
//
// Stability: Beta
// Compliance: OpenTelemetry Specification v1.42.0
package otel

import (
	"context"
	"crypto/tls"
	"fmt"
	"time"

	"go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploggrpc"
	"go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploghttp"
	"go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
	"go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetrichttp"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
	"go.opentelemetry.io/otel/sdk/log"
	"go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/trace"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/credentials/insecure"
)

// ExporterType 定义导出器类型
type ExporterType int

const (
	// ExporterTypeGRPC 使用 gRPC 协议
	ExporterTypeGRPC ExporterType = iota
	// ExporterTypeHTTP 使用 HTTP 协议
	ExporterTypeHTTP
)

// String 返回导出器类型的字符串表示
func (e ExporterType) String() string {
	switch e {
	case ExporterTypeGRPC:
		return "grpc"
	case ExporterTypeHTTP:
		return "http"
	default:
		return "unknown"
	}
}

// ExporterConfig 导出器配置
type ExporterConfig struct {
	// Endpoint OTLP 端点地址
	Endpoint string
	// Protocol 协议类型: grpc 或 http
	Protocol string
	// Headers 自定义请求头
	Headers map[string]string
	// Timeout 超时时间
	Timeout time.Duration
	// Compression 压缩算法: gzip 或 none
	Compression string
	// TLSConfig TLS 配置，为 nil 时使用不安全连接
	TLSConfig *tls.Config
	// RetryConfig 重试配置
	RetryConfig RetryConfig
}

// RetryConfig 重试配置
type RetryConfig struct {
	Enabled         bool
	InitialInterval time.Duration
	MaxInterval     time.Duration
	MaxElapsedTime  time.Duration
}

// DefaultExporterConfig 返回默认导出器配置
func DefaultExporterConfig() ExporterConfig {
	return ExporterConfig{
		Endpoint:    "localhost:4317",
		Protocol:    "grpc",
		Headers:     make(map[string]string),
		Timeout:     10 * time.Second,
		Compression: "gzip",
		RetryConfig: RetryConfig{
			Enabled:         true,
			InitialInterval: 1 * time.Second,
			MaxInterval:     5 * time.Second,
			MaxElapsedTime:  30 * time.Second,
		},
	}
}

// ExporterManager 管理 OTLP 导出器的创建和生命周期
type ExporterManager struct {
	config ExporterConfig
}

// NewExporterManager 创建新的导出器管理器
func NewExporterManager(config ExporterConfig) *ExporterManager {
	return &ExporterManager{
		config: config,
	}
}

// GetExporterType 获取导出器类型
func (em *ExporterManager) GetExporterType() ExporterType {
	switch em.config.Protocol {
	case "http", "http/protobuf":
		return ExporterTypeHTTP
	case "grpc":
		fallthrough
	default:
		return ExporterTypeGRPC
	}
}

// CreateTraceExporter 创建追踪导出器
func (em *ExporterManager) CreateTraceExporter(ctx context.Context) (trace.SpanExporter, error) {
	switch em.GetExporterType() {
	case ExporterTypeHTTP:
		return em.createHTTPTraceExporter(ctx)
	case ExporterTypeGRPC:
		fallthrough
	default:
		return em.createGRPCTraceExporter(ctx)
	}
}

// CreateMetricExporter 创建指标导出器
func (em *ExporterManager) CreateMetricExporter(ctx context.Context) (metric.Exporter, error) {
	switch em.GetExporterType() {
	case ExporterTypeHTTP:
		return em.createHTTPMetricExporter(ctx)
	case ExporterTypeGRPC:
		fallthrough
	default:
		return em.createGRPCMetricExporter(ctx)
	}
}

// CreateLogExporter 创建日志导出器
func (em *ExporterManager) CreateLogExporter(ctx context.Context) (log.Exporter, error) {
	switch em.GetExporterType() {
	case ExporterTypeHTTP:
		return em.createHTTPLogExporter(ctx)
	case ExporterTypeGRPC:
		fallthrough
	default:
		return em.createGRPCLogExporter(ctx)
	}
}

// createGRPCTraceExporter 创建 gRPC 追踪导出器
func (em *ExporterManager) createGRPCTraceExporter(ctx context.Context) (trace.SpanExporter, error) {
	opts := []otlptracegrpc.Option{
		otlptracegrpc.WithEndpoint(em.config.Endpoint),
		otlptracegrpc.WithTimeout(em.config.Timeout),
	}

	// 配置 TLS
	if em.config.TLSConfig != nil {
		opts = append(opts, otlptracegrpc.WithTLSCredentials(credentials.NewTLS(em.config.TLSConfig)))
	} else {
		opts = append(opts, otlptracegrpc.WithInsecure())
	}

	// 配置 Headers
	if len(em.config.Headers) > 0 {
		opts = append(opts, otlptracegrpc.WithHeaders(em.config.Headers))
	}

	// 配置压缩
	if em.config.Compression == "gzip" {
		opts = append(opts, otlptracegrpc.WithCompressor("gzip"))
	}

	// 配置重试
	if em.config.RetryConfig.Enabled {
		opts = append(opts, otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
			Enabled:         true,
			InitialInterval: em.config.RetryConfig.InitialInterval,
			MaxInterval:     em.config.RetryConfig.MaxInterval,
			MaxElapsedTime:  em.config.RetryConfig.MaxElapsedTime,
		}))
	}

	return otlptracegrpc.New(ctx, opts...)
}

// createHTTPTraceExporter 创建 HTTP 追踪导出器
func (em *ExporterManager) createHTTPTraceExporter(ctx context.Context) (trace.SpanExporter, error) {
	opts := []otlptracehttp.Option{
		otlptracehttp.WithEndpoint(em.config.Endpoint),
		otlptracehttp.WithTimeout(em.config.Timeout),
	}

	// 配置 TLS
	if em.config.TLSConfig != nil {
		opts = append(opts, otlptracehttp.WithTLSClientConfig(em.config.TLSConfig))
	} else {
		opts = append(opts, otlptracehttp.WithInsecure())
	}

	// 配置 Headers
	if len(em.config.Headers) > 0 {
		opts = append(opts, otlptracehttp.WithHeaders(em.config.Headers))
	}

	// 配置压缩
	if em.config.Compression == "gzip" {
		opts = append(opts, otlptracehttp.WithCompression(otlptracehttp.GzipCompression))
	}

	// 配置重试
	if em.config.RetryConfig.Enabled {
		opts = append(opts, otlptracehttp.WithRetry(otlptracehttp.RetryConfig{
			Enabled:         true,
			InitialInterval: em.config.RetryConfig.InitialInterval,
			MaxInterval:     em.config.RetryConfig.MaxInterval,
			MaxElapsedTime:  em.config.RetryConfig.MaxElapsedTime,
		}))
	}

	return otlptracehttp.New(ctx, opts...)
}

// createGRPCMetricExporter 创建 gRPC 指标导出器
func (em *ExporterManager) createGRPCMetricExporter(ctx context.Context) (metric.Exporter, error) {
	opts := []otlpmetricgrpc.Option{
		otlpmetricgrpc.WithEndpoint(em.config.Endpoint),
		otlpmetricgrpc.WithTimeout(em.config.Timeout),
	}

	// 配置 TLS
	if em.config.TLSConfig != nil {
		opts = append(opts, otlpmetricgrpc.WithTLSCredentials(credentials.NewTLS(em.config.TLSConfig)))
	} else {
		opts = append(opts, otlpmetricgrpc.WithInsecure())
	}

	// 配置 Headers
	if len(em.config.Headers) > 0 {
		opts = append(opts, otlpmetricgrpc.WithHeaders(em.config.Headers))
	}

	// 配置压缩
	if em.config.Compression == "gzip" {
		opts = append(opts, otlpmetricgrpc.WithCompressor("gzip"))
	}

	// 配置重试
	if em.config.RetryConfig.Enabled {
		opts = append(opts, otlpmetricgrpc.WithRetry(otlpmetricgrpc.RetryConfig{
			Enabled:         true,
			InitialInterval: em.config.RetryConfig.InitialInterval,
			MaxInterval:     em.config.RetryConfig.MaxInterval,
			MaxElapsedTime:  em.config.RetryConfig.MaxElapsedTime,
		}))
	}

	return otlpmetricgrpc.New(ctx, opts...)
}

// createHTTPMetricExporter 创建 HTTP 指标导出器
func (em *ExporterManager) createHTTPMetricExporter(ctx context.Context) (metric.Exporter, error) {
	opts := []otlpmetrichttp.Option{
		otlpmetrichttp.WithEndpoint(em.config.Endpoint),
		otlpmetrichttp.WithTimeout(em.config.Timeout),
	}

	// 配置 TLS
	if em.config.TLSConfig != nil {
		opts = append(opts, otlpmetrichttp.WithTLSClientConfig(em.config.TLSConfig))
	} else {
		opts = append(opts, otlpmetrichttp.WithInsecure())
	}

	// 配置 Headers
	if len(em.config.Headers) > 0 {
		opts = append(opts, otlpmetrichttp.WithHeaders(em.config.Headers))
	}

	// 配置压缩
	if em.config.Compression == "gzip" {
		opts = append(opts, otlpmetrichttp.WithCompression(otlpmetrichttp.GzipCompression))
	}

	// 配置重试
	if em.config.RetryConfig.Enabled {
		opts = append(opts, otlpmetrichttp.WithRetry(otlpmetrichttp.RetryConfig{
			Enabled:         true,
			InitialInterval: em.config.RetryConfig.InitialInterval,
			MaxInterval:     em.config.RetryConfig.MaxInterval,
			MaxElapsedTime:  em.config.RetryConfig.MaxElapsedTime,
		}))
	}

	return otlpmetrichttp.New(ctx, opts...)
}

// createGRPCLogExporter 创建 gRPC 日志导出器
func (em *ExporterManager) createGRPCLogExporter(ctx context.Context) (log.Exporter, error) {
	opts := []otlploggrpc.Option{
		otlploggrpc.WithEndpoint(em.config.Endpoint),
		otlploggrpc.WithTimeout(em.config.Timeout),
	}

	// 配置 TLS
	if em.config.TLSConfig != nil {
		opts = append(opts, otlploggrpc.WithTLSCredentials(credentials.NewTLS(em.config.TLSConfig)))
	} else {
		opts = append(opts, otlploggrpc.WithInsecure())
	}

	// 配置 Headers
	if len(em.config.Headers) > 0 {
		opts = append(opts, otlploggrpc.WithHeaders(em.config.Headers))
	}

	// 配置压缩
	if em.config.Compression == "gzip" {
		opts = append(opts, otlploggrpc.WithCompressor("gzip"))
	}

	return otlploggrpc.New(ctx, opts...)
}

// createHTTPLogExporter 创建 HTTP 日志导出器
func (em *ExporterManager) createHTTPLogExporter(ctx context.Context) (log.Exporter, error) {
	opts := []otlploghttp.Option{
		otlploghttp.WithEndpoint(em.config.Endpoint),
		otlploghttp.WithTimeout(em.config.Timeout),
	}

	// 配置 TLS
	if em.config.TLSConfig != nil {
		opts = append(opts, otlploghttp.WithTLSClientConfig(em.config.TLSConfig))
	} else {
		opts = append(opts, otlploghttp.WithInsecure())
	}

	// 配置 Headers
	if len(em.config.Headers) > 0 {
		opts = append(opts, otlploghttp.WithHeaders(em.config.Headers))
	}

	// 配置压缩
	if em.config.Compression == "gzip" {
		opts = append(opts, otlploghttp.WithCompression(otlploghttp.GzipCompression))
	}

	return otlploghttp.New(ctx, opts...)
}

// CreateGRPCConn 创建 gRPC 连接（用于高级场景）
func (em *ExporterManager) CreateGRPCConn(ctx context.Context) (*grpc.ClientConn, error) {
	var creds credentials.TransportCredentials
	if em.config.TLSConfig != nil {
		creds = credentials.NewTLS(em.config.TLSConfig)
	} else {
		creds = insecure.NewCredentials()
	}

	opts := []grpc.DialOption{
		grpc.WithTransportCredentials(creds),
	}

	conn, err := grpc.NewClient(em.config.Endpoint, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create gRPC connection: %w", err)
	}

	return conn, nil
}

// Validate 验证导出器配置
func (ec *ExporterConfig) Validate() error {
	if ec.Endpoint == "" {
		return fmt.Errorf("exporter endpoint cannot be empty")
	}

	validProtocols := map[string]bool{"grpc": true, "http": true, "http/protobuf": true}
	if !validProtocols[ec.Protocol] {
		return fmt.Errorf("invalid protocol: %s", ec.Protocol)
	}

	validCompressions := map[string]bool{"gzip": true, "none": true, "": true}
	if !validCompressions[ec.Compression] {
		return fmt.Errorf("invalid compression: %s", ec.Compression)
	}

	if ec.Timeout <= 0 {
		ec.Timeout = 10 * time.Second
	}

	return nil
}

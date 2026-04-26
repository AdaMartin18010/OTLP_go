// Package otel provides OpenTelemetry SDK initialization and management
// for the OTLP Go SDK.
package otel

import (
	"context"
	"fmt"
	"sync"

	"github.com/OTLP_go/pkg/config"
	"github.com/OTLP_go/pkg/otel/exporter"
	"github.com/OTLP_go/pkg/otel/metric"
	otelpropagation "OTLP_go/pkg/propagation"
	"go.opentelemetry.io/otel"
	otelattribute "go.opentelemetry.io/otel/attribute"
	otellog "go.opentelemetry.io/otel/log"
	otelmetric "go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/log"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/resource"
	"go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	oteltrace "go.opentelemetry.io/otel/trace"
)

// SDK 管理 OpenTelemetry SDK 的生命周期
type SDK struct {
	// TracerProvider 追踪提供器
	TracerProvider *trace.TracerProvider
	// MeterProvider 指标提供器
	MeterProvider *sdkmetric.MeterProvider
	// LoggerProvider 日志提供器
	LoggerProvider *log.LoggerProvider
	// Resource 资源信息
	Resource *resource.Resource
	// Config 配置
	Config *config.OTelConfig
	// ExporterManager 导出器管理器
	ExporterManager *ExporterManager
	// Propagator 传播器
	Propagator propagation.TextMapPropagator

	// Views 自定义视图配置
	Views []metric.View
	// TemporalitySelector 时间性选择器
	TemporalitySelector metric.TemporalitySelector
	// AggregationSelector 聚合选择器
	AggregationSelector metric.AggregationSelector
	// PrometheusExporter Prometheus导出器
	PrometheusExporter *exporter.PrometheusExporter

	mu       sync.RWMutex
	shutdown []func(context.Context) error
}

// SDKOptions SDK 配置选项
type SDKOptions struct {
	// Config OTel 配置
	Config *config.OTelConfig
	// Resource 自定义资源（可选）
	Resource *resource.Resource
	// TracerEnabled 启用追踪
	TracerEnabled bool
	// MeterEnabled 启用指标
	MeterEnabled bool
	// LoggerEnabled 启用日志
	LoggerEnabled bool
	// Propagators 传播器列表
	Propagators []string
}

// DefaultSDKOptions 返回默认 SDK 选项
func DefaultSDKOptions() SDKOptions {
	return SDKOptions{
		TracerEnabled: true,
		MeterEnabled:  true,
		LoggerEnabled: false, // 默认不启用日志
		Propagators:   []string{"tracecontext", "baggage"},
	}
}

// Setup 初始化 OpenTelemetry SDK
func Setup(ctx context.Context, cfg *config.OTelConfig, opts ...SDKOption) (*SDK, error) {
	opts = append(opts, WithConfig(cfg))

	// 创建导出器管理器
	exporterConfig := ExporterConfig{
		Endpoint:    cfg.Exporter.Endpoint,
		Protocol:    cfg.GetTracesProtocol(),
		Headers:     cfg.GetTracesHeaders(),
		Timeout:     cfg.GetTracesTimeout(),
		Compression: cfg.Exporter.Compression,
		RetryConfig: RetryConfig{
			Enabled:         cfg.Exporter.Retry.Enabled,
			InitialInterval: cfg.Exporter.Retry.InitialInterval,
			MaxInterval:     cfg.Exporter.Retry.MaxInterval,
			MaxElapsedTime:  cfg.Exporter.Retry.MaxElapsedTime,
		},
	}
	exporterManager := NewExporterManager(exporterConfig)

	sdk := &SDK{
		Config:          cfg,
		ExporterManager: exporterManager,
		shutdown:        make([]func(context.Context) error, 0),
	}

	// 应用选项
	for _, opt := range opts {
		opt(sdk)
	}

	// 创建或配置资源
	if err := sdk.setupResource(ctx); err != nil {
		return nil, fmt.Errorf("failed to setup resource: %w", err)
	}

	// 设置传播器
	if err := sdk.setupPropagator(); err != nil {
		return nil, fmt.Errorf("failed to setup propagator: %w", err)
	}

	// 初始化追踪器
	if cfg.Tracer.Enabled && sdk.TracerProvider == nil {
		if err := sdk.setupTracerProvider(ctx); err != nil {
			return nil, fmt.Errorf("failed to setup tracer provider: %w", err)
		}
	}

	// 初始化指标器
	if cfg.Meter.Enabled && sdk.MeterProvider == nil {
		if err := sdk.setupMeterProvider(ctx); err != nil {
			return nil, fmt.Errorf("failed to setup meter provider: %w", err)
		}
	}

	// 初始化日志器
	if cfg.Logger.Enabled && sdk.LoggerProvider == nil {
		if err := sdk.setupLoggerProvider(ctx); err != nil {
			return nil, fmt.Errorf("failed to setup logger provider: %w", err)
		}
	}

	return sdk, nil
}

// SDKOption SDK 配置选项函数
type SDKOption func(*SDK)

// WithConfig 设置配置
func WithConfig(cfg *config.OTelConfig) SDKOption {
	return func(s *SDK) {
		s.Config = cfg
	}
}

// WithResource 设置资源
func WithResource(res *resource.Resource) SDKOption {
	return func(s *SDK) {
		s.Resource = res
	}
}

// WithTracerProvider 设置追踪提供器
func WithTracerProvider(tp *trace.TracerProvider) SDKOption {
	return func(s *SDK) {
		s.TracerProvider = tp
	}
}

// WithMeterProvider 设置指标提供器
func WithMeterProvider(mp *sdkmetric.MeterProvider) SDKOption {
	return func(s *SDK) {
		s.MeterProvider = mp
	}
}

// WithLoggerProvider 设置日志提供器
func WithLoggerProvider(lp *log.LoggerProvider) SDKOption {
	return func(s *SDK) {
		s.LoggerProvider = lp
	}
}

// WithPropagator 设置传播器
func WithPropagator(p propagation.TextMapPropagator) SDKOption {
	return func(s *SDK) {
		s.Propagator = p
	}
}

// WithExporterManager 设置导出器管理器
func WithExporterManager(em *ExporterManager) SDKOption {
	return func(s *SDK) {
		s.ExporterManager = em
	}
}

// WithViews 设置自定义视图
func WithViews(views []metric.View) SDKOption {
	return func(s *SDK) {
		s.Views = views
	}
}

// WithTemporalitySelector 设置时间性选择器
func WithTemporalitySelector(selector metric.TemporalitySelector) SDKOption {
	return func(s *SDK) {
		s.TemporalitySelector = selector
	}
}

// WithAggregationSelector 设置聚合选择器
func WithAggregationSelector(selector metric.AggregationSelector) SDKOption {
	return func(s *SDK) {
		s.AggregationSelector = selector
	}
}

// WithPrometheusExporter 设置Prometheus导出器
func WithPrometheusExporter(pe *exporter.PrometheusExporter) SDKOption {
	return func(s *SDK) {
		s.PrometheusExporter = pe
	}
}

// setupResource 创建或配置资源
func (s *SDK) setupResource(ctx context.Context) error {
	if s.Resource != nil {
		return nil
	}

	// 构建资源属性
	attrs := []resource.Option{
		resource.WithAttributes(
			semconv.ServiceName(s.Config.ServiceName),
			semconv.ServiceVersion(s.Config.ServiceVersion),
			semconv.DeploymentEnvironment(s.Config.DeploymentEnvironment),
		),
		resource.WithFromEnv(),
		resource.WithProcess(),
		resource.WithOS(),
		resource.WithContainer(),
		resource.WithHost(),
	}

	// 添加自定义属性
	if len(s.Config.Resource.Attributes) > 0 {
		customAttrs := make([]otelattribute.KeyValue, 0, len(s.Config.Resource.Attributes))
		for k, v := range s.Config.Resource.Attributes {
			customAttrs = append(customAttrs, otelattribute.String(k, v))
		}
		attrs = append(attrs, resource.WithAttributes(customAttrs...))
	}

	res, err := resource.New(ctx, attrs...)
	if err != nil {
		return fmt.Errorf("failed to create resource: %w", err)
	}

	s.Resource = res
	return nil
}

// setupPropagator 配置传播器
func (s *SDK) setupPropagator() error {
	if s.Propagator != nil {
		otel.SetTextMapPropagator(s.Propagator)
		return nil
	}

	propagators := s.Config.GetPropagators()
	var propagatorList []propagation.TextMapPropagator

	for _, p := range propagators {
		switch p {
		case "tracecontext":
			propagatorList = append(propagatorList, propagation.TraceContext{})
		case "baggage":
			propagatorList = append(propagatorList, propagation.Baggage{})
		case "b3":
			// B3 single header
			propagatorList = append(propagatorList, otelpropagation.B3Single{})
		case "b3multi":
			// B3 multiple headers
			propagatorList = append(propagatorList, otelpropagation.B3Multi{})
		case "jaeger":
			propagatorList = append(propagatorList, otelpropagation.Jaeger{})
		}
	}

	if len(propagatorList) == 0 {
		propagatorList = []propagation.TextMapPropagator{
			propagation.TraceContext{},
			propagation.Baggage{},
		}
	}

	s.Propagator = propagation.NewCompositeTextMapPropagator(propagatorList...)
	otel.SetTextMapPropagator(s.Propagator)

	return nil
}

// setupTracerProvider 初始化追踪提供器
func (s *SDK) setupTracerProvider(ctx context.Context) error {
	// 创建导出器
	exporter, err := s.ExporterManager.CreateTraceExporter(ctx)
	if err != nil {
		return fmt.Errorf("failed to create trace exporter: %w", err)
	}

	// 创建批处理器
	batchProcessor := trace.NewBatchSpanProcessor(
		exporter,
		trace.WithMaxQueueSize(s.Config.Batch.TracesMaxQueueSize),
		trace.WithMaxExportBatchSize(s.Config.Batch.TracesMaxExportBatchSize),
		trace.WithBatchTimeout(s.Config.Batch.TracesScheduleDelay),
		trace.WithExportTimeout(s.Config.Batch.TracesExportTimeout),
	)

	// 配置采样器
	sampler := s.createSampler()

	// 创建追踪提供器
	tp := trace.NewTracerProvider(
		trace.WithResource(s.Resource),
		trace.WithSpanProcessor(batchProcessor),
		trace.WithSampler(sampler),
	)

	s.TracerProvider = tp
	otel.SetTracerProvider(tp)

	// 注册关闭函数
	s.registerShutdown(func(ctx context.Context) error {
		return tp.Shutdown(ctx)
	})

	return nil
}

// setupMeterProvider 初始化指标提供器
func (s *SDK) setupMeterProvider(ctx context.Context) error {
	var readers []sdkmetric.Reader

	// 创建OTLP导出器读取器
	if s.ExporterManager != nil {
		exp, err := s.ExporterManager.CreateMetricExporter(ctx)
		if err != nil {
			return fmt.Errorf("failed to create metric exporter: %w", err)
		}

		readerOpts := metric.ReaderOptions{}
		if s.TemporalitySelector != nil {
			readerOpts.TemporalitySelector = s.TemporalitySelector
		}
		if s.AggregationSelector != nil {
			readerOpts.AggregationSelector = s.AggregationSelector
		}

		reader := metric.NewPeriodicExportingReader(
			exp,
			s.Config.Batch.MetricsExportInterval,
			s.Config.Batch.MetricsExportTimeout,
			readerOpts,
		)
		readers = append(readers, reader.SDKReader())
	}

	// 创建Prometheus读取器
	if s.PrometheusExporter != nil {
		readers = append(readers, s.PrometheusExporter.Reader())
	}

	if len(readers) == 0 {
		return fmt.Errorf("no metric readers configured")
	}

	// 转换Views
	var sdkViews []sdkmetric.View
	if len(s.Views) > 0 {
		sdkViews = metric.ViewsToSDK(s.Views)
	}

	// 构建MeterProvider选项
	mpOpts := []sdkmetric.Option{
		sdkmetric.WithResource(s.Resource),
	}
	for _, r := range readers {
		mpOpts = append(mpOpts, sdkmetric.WithReader(r))
	}
	for _, v := range sdkViews {
		mpOpts = append(mpOpts, sdkmetric.WithView(v))
	}

	// 创建指标提供器
	mp := sdkmetric.NewMeterProvider(mpOpts...)

	s.MeterProvider = mp
	otel.SetMeterProvider(mp)

	// 注册关闭函数
	s.registerShutdown(func(ctx context.Context) error {
		return mp.Shutdown(ctx)
	})

	return nil
}

// setupLoggerProvider 初始化日志提供器
func (s *SDK) setupLoggerProvider(ctx context.Context) error {
	// 创建导出器
	exporter, err := s.ExporterManager.CreateLogExporter(ctx)
	if err != nil {
		return fmt.Errorf("failed to create log exporter: %w", err)
	}

	// 创建批处理器
	batchProcessor := log.NewBatchProcessor(
		exporter,
		log.WithMaxQueueSize(s.Config.Batch.LogsMaxQueueSize),
		log.WithExportTimeout(s.Config.Batch.LogsExportTimeout),
		log.WithExportInterval(s.Config.Batch.LogsScheduleDelay),
	)

	// 创建日志提供器
	lp := log.NewLoggerProvider(
		log.WithResource(s.Resource),
		log.WithProcessor(batchProcessor),
	)

	s.LoggerProvider = lp

	// 注册关闭函数
	s.registerShutdown(func(ctx context.Context) error {
		return lp.Shutdown(ctx)
	})

	return nil
}

// createSampler 创建采样器
func (s *SDK) createSampler() trace.Sampler {
	switch s.Config.Sampling.Strategy {
	case "always_on":
		return trace.AlwaysSample()
	case "always_off":
		return trace.NeverSample()
	case "traceidratio":
		return trace.TraceIDRatioBased(s.Config.Sampling.Ratio)
	case "parentbased_always_on":
		return trace.ParentBased(trace.AlwaysSample())
	case "parentbased_always_off":
		return trace.ParentBased(trace.NeverSample())
	case "parentbased_traceidratio":
		return trace.ParentBased(trace.TraceIDRatioBased(s.Config.Sampling.Ratio))
	default:
		return trace.ParentBased(trace.AlwaysSample())
	}
}

// registerShutdown 注册关闭函数
func (s *SDK) registerShutdown(fn func(context.Context) error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.shutdown = append(s.shutdown, fn)
}

// Shutdown 优雅关闭 SDK
func (s *SDK) Shutdown(ctx context.Context) error {
	s.mu.Lock()
	shutdownFns := make([]func(context.Context) error, len(s.shutdown))
	copy(shutdownFns, s.shutdown)
	s.shutdown = s.shutdown[:0] // 清空
	s.mu.Unlock()

	var errs []error

	// 逆序执行关闭函数
	for i := len(shutdownFns) - 1; i >= 0; i-- {
		if err := shutdownFns[i](ctx); err != nil {
			errs = append(errs, err)
		}
	}

	if len(errs) > 0 {
		return fmt.Errorf("shutdown errors: %v", errs)
	}

	return nil
}

// Tracer 返回一个 Tracer 实例
func (s *SDK) Tracer(name string, opts ...oteltrace.TracerOption) oteltrace.Tracer {
	if s.TracerProvider == nil {
		return nil
	}
	return s.TracerProvider.Tracer(name, opts...)
}

// Meter 返回一个 Meter 实例
func (s *SDK) Meter(name string, opts ...otelmetric.MeterOption) otelmetric.Meter {
	if s.MeterProvider == nil {
		return nil
	}
	return s.MeterProvider.Meter(name, opts...)
}

// Logger 返回一个 Logger 实例
func (s *SDK) Logger(name string, opts ...otellog.LoggerOption) otellog.Logger {
	if s.LoggerProvider == nil {
		return nil
	}
	return s.LoggerProvider.Logger(name, opts...)
}

// IsTracingEnabled 返回追踪是否启用
func (s *SDK) IsTracingEnabled() bool {
	return s.TracerProvider != nil
}

// IsMetricsEnabled 返回指标是否启用
func (s *SDK) IsMetricsEnabled() bool {
	return s.MeterProvider != nil
}

// IsLoggingEnabled 返回日志是否启用
func (s *SDK) IsLoggingEnabled() bool {
	return s.LoggerProvider != nil
}

// b3Propagator 返回 B3 单头传播器
func b3Propagator() propagation.TextMapPropagator {
	return otelpropagation.B3Single{}
}

// b3MultiPropagator 返回 B3 多头传播器
func b3MultiPropagator() propagation.TextMapPropagator {
	return otelpropagation.B3Multi{}
}

// jaegerPropagator 返回 Jaeger 传播器
func jaegerPropagator() propagation.TextMapPropagator {
	return otelpropagation.Jaeger{}
}

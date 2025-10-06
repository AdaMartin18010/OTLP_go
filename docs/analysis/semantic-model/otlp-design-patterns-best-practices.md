# OTLP 设计模式与最佳实践

**版本**: 1.0.0  
**日期**: 2025-10-06  
**状态**: ✅ 完整

---

## 目录

- [OTLP 设计模式与最佳实践](#otlp-设计模式与最佳实践)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 设计模式在 OTLP 中的作用](#11-设计模式在-otlp-中的作用)
    - [1.2 最佳实践的价值](#12-最佳实践的价值)
  - [2. 创建型模式](#2-创建型模式)
    - [2.1 Builder 模式](#21-builder-模式)
    - [2.2 Factory 模式](#22-factory-模式)
    - [2.3 Singleton 模式](#23-singleton-模式)
    - [2.4 Prototype 模式](#24-prototype-模式)
  - [3. 结构型模式](#3-结构型模式)
    - [3.1 Adapter 模式](#31-adapter-模式)
    - [3.2 Decorator 模式](#32-decorator-模式)
    - [3.3 Proxy 模式](#33-proxy-模式)
    - [3.4 Composite 模式](#34-composite-模式)
  - [4. 行为型模式](#4-行为型模式)
    - [4.1 Strategy 模式](#41-strategy-模式)
    - [4.2 Observer 模式](#42-observer-模式)
    - [4.3 Chain of Responsibility 模式](#43-chain-of-responsibility-模式)
    - [4.4 Template Method 模式](#44-template-method-模式)
  - [5. 并发模式](#5-并发模式)
    - [5.1 Worker Pool 模式](#51-worker-pool-模式)
    - [5.2 Pipeline 模式](#52-pipeline-模式)
    - [5.3 Fan-Out/Fan-In 模式](#53-fan-outfan-in-模式)
    - [5.4 Circuit Breaker 模式](#54-circuit-breaker-模式)
  - [6. 架构模式](#6-架构模式)
    - [6.1 分层架构](#61-分层架构)
    - [6.2 插件架构](#62-插件架构)
    - [6.3 微服务架构](#63-微服务架构)
    - [6.4 事件驱动架构](#64-事件驱动架构)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 初始化最佳实践](#71-初始化最佳实践)
    - [7.2 资源管理最佳实践](#72-资源管理最佳实践)
    - [7.3 错误处理最佳实践](#73-错误处理最佳实践)
    - [7.4 性能优化最佳实践](#74-性能优化最佳实践)
    - [7.5 测试最佳实践](#75-测试最佳实践)
    - [7.6 部署最佳实践](#76-部署最佳实践)
  - [8. 反模式](#8-反模式)
    - [8.1 设计反模式](#81-设计反模式)
    - [8.2 性能反模式](#82-性能反模式)
    - [8.3 安全反模式](#83-安全反模式)
  - [9. 参考文献](#9-参考文献)

---

## 1. 概述

### 1.1 设计模式在 OTLP 中的作用

设计模式是解决常见问题的可复用解决方案。在 OTLP 编程中:

- **提高代码质量**: 使用经过验证的设计模式
- **增强可维护性**: 标准化的代码结构
- **促进团队协作**: 共同的设计语言
- **加速开发**: 复用成熟的解决方案

### 1.2 最佳实践的价值

最佳实践是从实际经验中总结出的优秀做法:

1. **避免常见陷阱**: 学习他人的经验教训
2. **提高性能**: 优化资源使用
3. **增强可靠性**: 减少错误和故障
4. **改善可观测性**: 更好的监控和调试

---

## 2. 创建型模式

### 2.1 Builder 模式

**目的**: 分步构建复杂对象,提供流畅的 API。

**应用场景**: 构建 TracerProvider、Exporter、Resource 等复杂对象。

**实现示例**:

```go
package telemetry

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
)

// TelemetryBuilder 构建器
type TelemetryBuilder struct {
    serviceName    string
    serviceVersion string
    endpoint       string
    insecure       bool
    batchTimeout   time.Duration
    maxBatchSize   int
    resource       *resource.Resource
    sampler        trace.Sampler
}

// NewTelemetryBuilder 创建构建器
func NewTelemetryBuilder() *TelemetryBuilder {
    return &TelemetryBuilder{
        insecure:     false,
        batchTimeout: 5 * time.Second,
        maxBatchSize: 512,
        sampler:      trace.AlwaysSample(),
    }
}

// WithService 设置服务信息
func (b *TelemetryBuilder) WithService(name, version string) *TelemetryBuilder {
    b.serviceName = name
    b.serviceVersion = version
    return b
}

// WithEndpoint 设置导出端点
func (b *TelemetryBuilder) WithEndpoint(endpoint string) *TelemetryBuilder {
    b.endpoint = endpoint
    return b
}

// WithInsecure 设置不安全连接
func (b *TelemetryBuilder) WithInsecure(insecure bool) *TelemetryBuilder {
    b.insecure = insecure
    return b
}

// WithBatchConfig 设置批处理配置
func (b *TelemetryBuilder) WithBatchConfig(timeout time.Duration, maxSize int) *TelemetryBuilder {
    b.batchTimeout = timeout
    b.maxBatchSize = maxSize
    return b
}

// WithSampler 设置采样器
func (b *TelemetryBuilder) WithSampler(sampler trace.Sampler) *TelemetryBuilder {
    b.sampler = sampler
    return b
}

// Build 构建 TracerProvider
func (b *TelemetryBuilder) Build(ctx context.Context) (*trace.TracerProvider, error) {
    // 1. 创建 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(b.serviceName),
            semconv.ServiceVersion(b.serviceVersion),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 2. 创建 Exporter
    opts := []otlptracegrpc.Option{
        otlptracegrpc.WithEndpoint(b.endpoint),
    }
    if b.insecure {
        opts = append(opts, otlptracegrpc.WithInsecure())
    }
    
    exporter, err := otlptracegrpc.New(ctx, opts...)
    if err != nil {
        return nil, err
    }

    // 3. 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithResource(res),
        trace.WithBatcher(exporter,
            trace.WithBatchTimeout(b.batchTimeout),
            trace.WithMaxExportBatchSize(b.maxBatchSize),
        ),
        trace.WithSampler(b.sampler),
    )

    return tp, nil
}

// 使用示例
func ExampleBuilder() {
    ctx := context.Background()
    
    tp, err := NewTelemetryBuilder().
        WithService("my-service", "1.0.0").
        WithEndpoint("localhost:4317").
        WithInsecure(true).
        WithBatchConfig(10*time.Second, 1024).
        WithSampler(trace.TraceIDRatioBased(0.1)).
        Build(ctx)
    
    if err != nil {
        panic(err)
    }
    
    otel.SetTracerProvider(tp)
}
```

**优点**:

- 流畅的 API
- 参数验证集中
- 易于扩展

### 2.2 Factory 模式

**目的**: 封装对象创建逻辑,提供统一的创建接口。

**应用场景**: 根据配置创建不同类型的 Exporter、Sampler。

**实现示例**:

```go
package factory

import (
    "context"
    "fmt"
    
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
    "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
    "go.opentelemetry.io/otel/sdk/trace"
)

// ExporterType 导出器类型
type ExporterType string

const (
    ExporterTypeGRPC   ExporterType = "grpc"
    ExporterTypeHTTP   ExporterType = "http"
    ExporterTypeStdout ExporterType = "stdout"
)

// ExporterConfig 导出器配置
type ExporterConfig struct {
    Type     ExporterType
    Endpoint string
    Insecure bool
}

// ExporterFactory 导出器工厂
type ExporterFactory struct{}

// NewExporterFactory 创建工厂
func NewExporterFactory() *ExporterFactory {
    return &ExporterFactory{}
}

// CreateExporter 创建导出器
func (f *ExporterFactory) CreateExporter(ctx context.Context, config ExporterConfig) (trace.SpanExporter, error) {
    switch config.Type {
    case ExporterTypeGRPC:
        return f.createGRPCExporter(ctx, config)
    case ExporterTypeHTTP:
        return f.createHTTPExporter(ctx, config)
    case ExporterTypeStdout:
        return f.createStdoutExporter()
    default:
        return nil, fmt.Errorf("unknown exporter type: %s", config.Type)
    }
}

func (f *ExporterFactory) createGRPCExporter(ctx context.Context, config ExporterConfig) (trace.SpanExporter, error) {
    opts := []otlptracegrpc.Option{
        otlptracegrpc.WithEndpoint(config.Endpoint),
    }
    if config.Insecure {
        opts = append(opts, otlptracegrpc.WithInsecure())
    }
    return otlptracegrpc.New(ctx, opts...)
}

func (f *ExporterFactory) createHTTPExporter(ctx context.Context, config ExporterConfig) (trace.SpanExporter, error) {
    opts := []otlptracehttp.Option{
        otlptracehttp.WithEndpoint(config.Endpoint),
    }
    if config.Insecure {
        opts = append(opts, otlptracehttp.WithInsecure())
    }
    return otlptracehttp.New(ctx, opts...)
}

func (f *ExporterFactory) createStdoutExporter() (trace.SpanExporter, error) {
    return stdouttrace.New(
        stdouttrace.WithPrettyPrint(),
    )
}

// 使用示例
func ExampleFactory() {
    ctx := context.Background()
    factory := NewExporterFactory()
    
    config := ExporterConfig{
        Type:     ExporterTypeGRPC,
        Endpoint: "localhost:4317",
        Insecure: true,
    }
    
    exporter, err := factory.CreateExporter(ctx, config)
    if err != nil {
        panic(err)
    }
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
    )
    _ = tp
}
```

**优点**:

- 解耦对象创建和使用
- 易于添加新类型
- 集中配置管理

### 2.3 Singleton 模式

**目的**: 确保全局只有一个实例。

**应用场景**: 全局 TracerProvider、MeterProvider。

**实现示例**:

```go
package singleton

import (
    "context"
    "sync"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// GlobalTracerProvider 全局 TracerProvider 单例
type GlobalTracerProvider struct {
    provider *trace.TracerProvider
    once     sync.Once
}

var instance *GlobalTracerProvider
var instanceOnce sync.Once

// GetInstance 获取单例实例
func GetInstance() *GlobalTracerProvider {
    instanceOnce.Do(func() {
        instance = &GlobalTracerProvider{}
    })
    return instance
}

// Initialize 初始化 TracerProvider
func (g *GlobalTracerProvider) Initialize(ctx context.Context, opts ...trace.TracerProviderOption) error {
    var initErr error
    g.once.Do(func() {
        g.provider = trace.NewTracerProvider(opts...)
    })
    return initErr
}

// GetProvider 获取 TracerProvider
func (g *GlobalTracerProvider) GetProvider() *trace.TracerProvider {
    return g.provider
}

// Shutdown 关闭 TracerProvider
func (g *GlobalTracerProvider) Shutdown(ctx context.Context) error {
    if g.provider != nil {
        return g.provider.Shutdown(ctx)
    }
    return nil
}

// 使用示例
func ExampleSingleton() {
    ctx := context.Background()
    
    // 初始化
    instance := GetInstance()
    err := instance.Initialize(ctx)
    if err != nil {
        panic(err)
    }
    
    // 获取 Provider
    tp := instance.GetProvider()
    tracer := tp.Tracer("my-component")
    
    _, span := tracer.Start(ctx, "operation")
    defer span.End()
    
    // 清理
    defer instance.Shutdown(ctx)
}
```

**优点**:

- 全局唯一实例
- 线程安全
- 延迟初始化

### 2.4 Prototype 模式

**目的**: 通过复制现有对象创建新对象。

**应用场景**: 复制 Span 配置、Resource 配置。

**实现示例**:

```go
package prototype

import (
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
)

// ResourceTemplate 资源模板
type ResourceTemplate struct {
    attributes []attribute.KeyValue
}

// NewResourceTemplate 创建模板
func NewResourceTemplate(attrs ...attribute.KeyValue) *ResourceTemplate {
    return &ResourceTemplate{
        attributes: attrs,
    }
}

// Clone 克隆模板
func (t *ResourceTemplate) Clone() *ResourceTemplate {
    // 深拷贝属性
    attrs := make([]attribute.KeyValue, len(t.attributes))
    copy(attrs, t.attributes)
    
    return &ResourceTemplate{
        attributes: attrs,
    }
}

// AddAttribute 添加属性
func (t *ResourceTemplate) AddAttribute(attr attribute.KeyValue) *ResourceTemplate {
    t.attributes = append(t.attributes, attr)
    return t
}

// Build 构建 Resource
func (t *ResourceTemplate) Build() *resource.Resource {
    return resource.NewWithAttributes(
        "https://opentelemetry.io/schemas/1.17.0",
        t.attributes...,
    )
}

// 使用示例
func ExamplePrototype() {
    // 创建基础模板
    baseTemplate := NewResourceTemplate(
        attribute.String("service.namespace", "production"),
        attribute.String("deployment.environment", "prod"),
    )
    
    // 克隆并定制
    service1 := baseTemplate.Clone().
        AddAttribute(attribute.String("service.name", "api-service")).
        AddAttribute(attribute.String("service.version", "1.0.0"))
    
    service2 := baseTemplate.Clone().
        AddAttribute(attribute.String("service.name", "worker-service")).
        AddAttribute(attribute.String("service.version", "2.0.0"))
    
    res1 := service1.Build()
    res2 := service2.Build()
    
    _, _ = res1, res2
}
```

**优点**:

- 避免重复配置
- 快速创建相似对象
- 支持定制化

---

## 3. 结构型模式

### 3.1 Adapter 模式

**目的**: 将一个接口转换为另一个接口。

**应用场景**: 适配第三方日志库、监控系统。

**实现示例**:

```go
package adapter

import (
    "context"
    "log"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// LegacyLogger 遗留日志接口
type LegacyLogger interface {
    Log(level string, message string, fields map[string]interface{})
}

// SpanExporterAdapter 适配器
type SpanExporterAdapter struct {
    logger LegacyLogger
}

// NewSpanExporterAdapter 创建适配器
func NewSpanExporterAdapter(logger LegacyLogger) *SpanExporterAdapter {
    return &SpanExporterAdapter{
        logger: logger,
    }
}

// ExportSpans 导出 Spans
func (a *SpanExporterAdapter) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    for _, span := range spans {
        fields := make(map[string]interface{})
        fields["trace_id"] = span.SpanContext().TraceID().String()
        fields["span_id"] = span.SpanContext().SpanID().String()
        fields["name"] = span.Name()
        fields["duration"] = span.EndTime().Sub(span.StartTime()).String()
        
        a.logger.Log("INFO", "span exported", fields)
    }
    return nil
}

// Shutdown 关闭
func (a *SpanExporterAdapter) Shutdown(ctx context.Context) error {
    return nil
}

// 使用示例
type SimpleLogger struct{}

func (l *SimpleLogger) Log(level string, message string, fields map[string]interface{}) {
    log.Printf("[%s] %s %v", level, message, fields)
}

func ExampleAdapter() {
    logger := &SimpleLogger{}
    adapter := NewSpanExporterAdapter(logger)
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(adapter),
    )
    _ = tp
}
```

**优点**:

- 复用现有代码
- 解耦系统依赖
- 易于迁移

### 3.2 Decorator 模式

**目的**: 动态添加功能到对象。

**应用场景**: 为 Span 添加额外属性、日志、监控。

**实现示例**:

```go
package decorator

import (
    "context"
    "log"
    "time"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// SpanExporter 接口
type SpanExporter interface {
    ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error
    Shutdown(ctx context.Context) error
}

// LoggingDecorator 日志装饰器
type LoggingDecorator struct {
    exporter SpanExporter
}

// NewLoggingDecorator 创建装饰器
func NewLoggingDecorator(exporter SpanExporter) *LoggingDecorator {
    return &LoggingDecorator{
        exporter: exporter,
    }
}

// ExportSpans 导出 Spans (添加日志)
func (d *LoggingDecorator) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    log.Printf("Exporting %d spans", len(spans))
    start := time.Now()
    
    err := d.exporter.ExportSpans(ctx, spans)
    
    duration := time.Since(start)
    if err != nil {
        log.Printf("Export failed after %v: %v", duration, err)
    } else {
        log.Printf("Export succeeded in %v", duration)
    }
    
    return err
}

// Shutdown 关闭
func (d *LoggingDecorator) Shutdown(ctx context.Context) error {
    log.Println("Shutting down exporter")
    return d.exporter.Shutdown(ctx)
}

// MetricsDecorator 指标装饰器
type MetricsDecorator struct {
    exporter      SpanExporter
    exportCount   int64
    exportErrors  int64
    totalDuration time.Duration
}

// NewMetricsDecorator 创建装饰器
func NewMetricsDecorator(exporter SpanExporter) *MetricsDecorator {
    return &MetricsDecorator{
        exporter: exporter,
    }
}

// ExportSpans 导出 Spans (收集指标)
func (d *MetricsDecorator) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    start := time.Now()
    err := d.exporter.ExportSpans(ctx, spans)
    duration := time.Since(start)
    
    d.exportCount++
    d.totalDuration += duration
    if err != nil {
        d.exportErrors++
    }
    
    return err
}

// Shutdown 关闭
func (d *MetricsDecorator) Shutdown(ctx context.Context) error {
    log.Printf("Metrics: exports=%d, errors=%d, avg_duration=%v",
        d.exportCount, d.exportErrors, d.totalDuration/time.Duration(d.exportCount))
    return d.exporter.Shutdown(ctx)
}

// 使用示例 (链式装饰)
func ExampleDecorator(baseExporter SpanExporter) SpanExporter {
    // 添加日志装饰器
    decorated := NewLoggingDecorator(baseExporter)
    
    // 添加指标装饰器
    decorated2 := NewMetricsDecorator(decorated)
    
    return decorated2
}
```

**优点**:

- 动态添加功能
- 符合开闭原则
- 可组合多个装饰器

### 3.3 Proxy 模式

**目的**: 为对象提供代理,控制访问。

**应用场景**: 延迟加载、访问控制、缓存。

**实现示例**:

```go
package proxy

import (
    "context"
    "sync"
    "time"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// CachingExporterProxy 缓存代理
type CachingExporterProxy struct {
    exporter trace.SpanExporter
    cache    []trace.ReadOnlySpan
    cacheMu  sync.Mutex
    
    cacheSize    int
    flushTimeout time.Duration
    timer        *time.Timer
}

// NewCachingExporterProxy 创建代理
func NewCachingExporterProxy(exporter trace.SpanExporter, cacheSize int, flushTimeout time.Duration) *CachingExporterProxy {
    return &CachingExporterProxy{
        exporter:     exporter,
        cache:        make([]trace.ReadOnlySpan, 0, cacheSize),
        cacheSize:    cacheSize,
        flushTimeout: flushTimeout,
    }
}

// ExportSpans 导出 Spans (使用缓存)
func (p *CachingExporterProxy) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    p.cacheMu.Lock()
    defer p.cacheMu.Unlock()
    
    // 添加到缓存
    p.cache = append(p.cache, spans...)
    
    // 检查是否需要刷新
    if len(p.cache) >= p.cacheSize {
        return p.flush(ctx)
    }
    
    // 启动定时器
    if p.timer == nil {
        p.timer = time.AfterFunc(p.flushTimeout, func() {
            p.cacheMu.Lock()
            defer p.cacheMu.Unlock()
            p.flush(context.Background())
        })
    }
    
    return nil
}

// flush 刷新缓存
func (p *CachingExporterProxy) flush(ctx context.Context) error {
    if len(p.cache) == 0 {
        return nil
    }
    
    err := p.exporter.ExportSpans(ctx, p.cache)
    p.cache = p.cache[:0]
    
    if p.timer != nil {
        p.timer.Stop()
        p.timer = nil
    }
    
    return err
}

// Shutdown 关闭
func (p *CachingExporterProxy) Shutdown(ctx context.Context) error {
    p.cacheMu.Lock()
    defer p.cacheMu.Unlock()
    
    // 刷新剩余缓存
    if err := p.flush(ctx); err != nil {
        return err
    }
    
    return p.exporter.Shutdown(ctx)
}
```

**优点**:

- 控制访问
- 添加额外功能
- 优化性能

### 3.4 Composite 模式

**目的**: 将对象组合成树形结构。

**应用场景**: 组合多个 Exporter、Processor。

**实现示例**:

```go
package composite

import (
    "context"
    "sync"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// CompositeExporter 组合导出器
type CompositeExporter struct {
    exporters []trace.SpanExporter
}

// NewCompositeExporter 创建组合导出器
func NewCompositeExporter(exporters ...trace.SpanExporter) *CompositeExporter {
    return &CompositeExporter{
        exporters: exporters,
    }
}

// AddExporter 添加导出器
func (c *CompositeExporter) AddExporter(exporter trace.SpanExporter) {
    c.exporters = append(c.exporters, exporter)
}

// ExportSpans 导出到所有导出器
func (c *CompositeExporter) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    var wg sync.WaitGroup
    errCh := make(chan error, len(c.exporters))
    
    for _, exporter := range c.exporters {
        wg.Add(1)
        go func(exp trace.SpanExporter) {
            defer wg.Done()
            if err := exp.ExportSpans(ctx, spans); err != nil {
                errCh <- err
            }
        }(exporter)
    }
    
    wg.Wait()
    close(errCh)
    
    // 返回第一个错误
    for err := range errCh {
        return err
    }
    
    return nil
}

// Shutdown 关闭所有导出器
func (c *CompositeExporter) Shutdown(ctx context.Context) error {
    var wg sync.WaitGroup
    errCh := make(chan error, len(c.exporters))
    
    for _, exporter := range c.exporters {
        wg.Add(1)
        go func(exp trace.SpanExporter) {
            defer wg.Done()
            if err := exp.Shutdown(ctx); err != nil {
                errCh <- err
            }
        }(exporter)
    }
    
    wg.Wait()
    close(errCh)
    
    for err := range errCh {
        return err
    }
    
    return nil
}

// 使用示例
func ExampleComposite(exp1, exp2, exp3 trace.SpanExporter) {
    // 创建组合导出器
    composite := NewCompositeExporter(exp1, exp2, exp3)
    
    // 使用组合导出器
    tp := trace.NewTracerProvider(
        trace.WithBatcher(composite),
    )
    _ = tp
}
```

**优点**:

- 统一处理单个和组合对象
- 易于添加新组件
- 并行处理

---

## 4. 行为型模式

### 4.1 Strategy 模式

**目的**: 定义一系列算法,使它们可以互换。

**应用场景**: 采样策略、导出策略、重试策略。

**实现示例**:

```go
package strategy

import (
    "context"
    "math/rand"
    "time"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// SamplingStrategy 采样策略接口
type SamplingStrategy interface {
    ShouldSample(span trace.ReadOnlySpan) bool
}

// AlwaysSampleStrategy 总是采样
type AlwaysSampleStrategy struct{}

func (s *AlwaysSampleStrategy) ShouldSample(span trace.ReadOnlySpan) bool {
    return true
}

// RatioSampleStrategy 比例采样
type RatioSampleStrategy struct {
    ratio float64
}

func NewRatioSampleStrategy(ratio float64) *RatioSampleStrategy {
    return &RatioSampleStrategy{ratio: ratio}
}

func (s *RatioSampleStrategy) ShouldSample(span trace.ReadOnlySpan) bool {
    return rand.Float64() < s.ratio
}

// ErrorSampleStrategy 错误采样
type ErrorSampleStrategy struct{}

func (s *ErrorSampleStrategy) ShouldSample(span trace.ReadOnlySpan) bool {
    return span.Status().Code != 0 // 有错误时采样
}

// AdaptiveSampleStrategy 自适应采样
type AdaptiveSampleStrategy struct {
    baseRatio    float64
    currentRatio float64
    errorCount   int
    totalCount   int
}

func NewAdaptiveSampleStrategy(baseRatio float64) *AdaptiveSampleStrategy {
    return &AdaptiveSampleStrategy{
        baseRatio:    baseRatio,
        currentRatio: baseRatio,
    }
}

func (s *AdaptiveSampleStrategy) ShouldSample(span trace.ReadOnlySpan) bool {
    s.totalCount++
    
    // 错误时总是采样
    if span.Status().Code != 0 {
        s.errorCount++
        return true
    }
    
    // 根据错误率调整采样率
    if s.totalCount > 100 {
        errorRate := float64(s.errorCount) / float64(s.totalCount)
        if errorRate > 0.1 {
            s.currentRatio = 1.0 // 高错误率,提高采样
        } else {
            s.currentRatio = s.baseRatio
        }
    }
    
    return rand.Float64() < s.currentRatio
}

// SamplingContext 采样上下文
type SamplingContext struct {
    strategy SamplingStrategy
}

// NewSamplingContext 创建上下文
func NewSamplingContext(strategy SamplingStrategy) *SamplingContext {
    return &SamplingContext{
        strategy: strategy,
    }
}

// SetStrategy 设置策略
func (c *SamplingContext) SetStrategy(strategy SamplingStrategy) {
    c.strategy = strategy
}

// Sample 执行采样
func (c *SamplingContext) Sample(span trace.ReadOnlySpan) bool {
    return c.strategy.ShouldSample(span)
}

// 使用示例
func ExampleStrategy() {
    ctx := NewSamplingContext(&AlwaysSampleStrategy{})
    
    // 运行时切换策略
    if time.Now().Hour() < 6 {
        // 凌晨低流量时使用高采样率
        ctx.SetStrategy(NewRatioSampleStrategy(0.5))
    } else {
        // 白天高流量时使用低采样率
        ctx.SetStrategy(NewRatioSampleStrategy(0.1))
    }
}
```

**优点**:

- 算法可互换
- 易于扩展
- 运行时切换

### 4.2 Observer 模式

**目的**: 定义对象间的一对多依赖关系。

**应用场景**: Span 事件通知、状态变更监听。

**实现示例**:

```go
package observer

import (
    "log"
    "sync"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// SpanObserver Span 观察者接口
type SpanObserver interface {
    OnSpanStart(span trace.ReadOnlySpan)
    OnSpanEnd(span trace.ReadOnlySpan)
}

// SpanSubject Span 主题
type SpanSubject struct {
    observers []SpanObserver
    mu        sync.RWMutex
}

// NewSpanSubject 创建主题
func NewSpanSubject() *SpanSubject {
    return &SpanSubject{
        observers: make([]SpanObserver, 0),
    }
}

// Attach 添加观察者
func (s *SpanSubject) Attach(observer SpanObserver) {
    s.mu.Lock()
    defer s.mu.Unlock()
    s.observers = append(s.observers, observer)
}

// Detach 移除观察者
func (s *SpanSubject) Detach(observer SpanObserver) {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    for i, obs := range s.observers {
        if obs == observer {
            s.observers = append(s.observers[:i], s.observers[i+1:]...)
            break
        }
    }
}

// NotifyStart 通知 Span 开始
func (s *SpanSubject) NotifyStart(span trace.ReadOnlySpan) {
    s.mu.RLock()
    defer s.mu.RUnlock()
    
    for _, observer := range s.observers {
        observer.OnSpanStart(span)
    }
}

// NotifyEnd 通知 Span 结束
func (s *SpanSubject) NotifyEnd(span trace.ReadOnlySpan) {
    s.mu.RLock()
    defer s.mu.RUnlock()
    
    for _, observer := range s.observers {
        observer.OnSpanEnd(span)
    }
}

// LoggingObserver 日志观察者
type LoggingObserver struct{}

func (o *LoggingObserver) OnSpanStart(span trace.ReadOnlySpan) {
    log.Printf("Span started: %s", span.Name())
}

func (o *LoggingObserver) OnSpanEnd(span trace.ReadOnlySpan) {
    duration := span.EndTime().Sub(span.StartTime())
    log.Printf("Span ended: %s (duration: %v)", span.Name(), duration)
}

// MetricsObserver 指标观察者
type MetricsObserver struct {
    spanCount    int64
    totalLatency int64
}

func (o *MetricsObserver) OnSpanStart(span trace.ReadOnlySpan) {
    o.spanCount++
}

func (o *MetricsObserver) OnSpanEnd(span trace.ReadOnlySpan) {
    duration := span.EndTime().Sub(span.StartTime())
    o.totalLatency += duration.Milliseconds()
}

// 使用示例
func ExampleObserver() {
    subject := NewSpanSubject()
    
    // 添加观察者
    subject.Attach(&LoggingObserver{})
    subject.Attach(&MetricsObserver{})
    
    // 模拟 Span 事件
    // subject.NotifyStart(span)
    // subject.NotifyEnd(span)
}
```

**优点**:

- 解耦主题和观察者
- 支持多个观察者
- 动态添加/移除

### 4.3 Chain of Responsibility 模式

**目的**: 将请求沿着处理链传递。

**应用场景**: Span 处理器链、中间件。

**实现示例**:

```go
package chain

import (
    "context"
    
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/trace"
)

// SpanProcessor Span 处理器接口
type SpanProcessor interface {
    Process(ctx context.Context, span trace.ReadOnlySpan) error
    SetNext(processor SpanProcessor)
}

// BaseProcessor 基础处理器
type BaseProcessor struct {
    next SpanProcessor
}

func (p *BaseProcessor) SetNext(processor SpanProcessor) {
    p.next = processor
}

func (p *BaseProcessor) ProcessNext(ctx context.Context, span trace.ReadOnlySpan) error {
    if p.next != nil {
        return p.next.Process(ctx, span)
    }
    return nil
}

// ValidationProcessor 验证处理器
type ValidationProcessor struct {
    BaseProcessor
}

func (p *ValidationProcessor) Process(ctx context.Context, span trace.ReadOnlySpan) error {
    // 验证 Span
    if span.Name() == "" {
        return nil // 跳过无效 Span
    }
    
    return p.ProcessNext(ctx, span)
}

// EnrichmentProcessor 增强处理器
type EnrichmentProcessor struct {
    BaseProcessor
}

func (p *EnrichmentProcessor) Process(ctx context.Context, span trace.ReadOnlySpan) error {
    // 添加额外属性
    // 注意: ReadOnlySpan 不能修改,这里仅作示例
    _ = attribute.String("enriched", "true")
    
    return p.ProcessNext(ctx, span)
}

// FilterProcessor 过滤处理器
type FilterProcessor struct {
    BaseProcessor
    excludeNames map[string]bool
}

func NewFilterProcessor(excludeNames []string) *FilterProcessor {
    exclude := make(map[string]bool)
    for _, name := range excludeNames {
        exclude[name] = true
    }
    return &FilterProcessor{
        excludeNames: exclude,
    }
}

func (p *FilterProcessor) Process(ctx context.Context, span trace.ReadOnlySpan) error {
    // 过滤不需要的 Span
    if p.excludeNames[span.Name()] {
        return nil // 跳过
    }
    
    return p.ProcessNext(ctx, span)
}

// ExportProcessor 导出处理器
type ExportProcessor struct {
    BaseProcessor
    exporter trace.SpanExporter
}

func NewExportProcessor(exporter trace.SpanExporter) *ExportProcessor {
    return &ExportProcessor{
        exporter: exporter,
    }
}

func (p *ExportProcessor) Process(ctx context.Context, span trace.ReadOnlySpan) error {
    // 导出 Span
    return p.exporter.ExportSpans(ctx, []trace.ReadOnlySpan{span})
}

// 使用示例
func ExampleChain(exporter trace.SpanExporter) SpanProcessor {
    // 构建处理链
    validation := &ValidationProcessor{}
    enrichment := &EnrichmentProcessor{}
    filter := NewFilterProcessor([]string{"health-check", "metrics"})
    export := NewExportProcessor(exporter)
    
    // 链接处理器
    validation.SetNext(enrichment)
    enrichment.SetNext(filter)
    filter.SetNext(export)
    
    return validation
}
```

**优点**:

- 解耦发送者和接收者
- 动态组合处理链
- 易于扩展

### 4.4 Template Method 模式

**目的**: 定义算法骨架,子类实现具体步骤。

**应用场景**: Exporter 基础实现、Processor 基础实现。

**实现示例**:

```go
package template

import (
    "context"
    "fmt"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// ExporterTemplate 导出器模板
type ExporterTemplate struct {
    name string
}

// NewExporterTemplate 创建模板
func NewExporterTemplate(name string) *ExporterTemplate {
    return &ExporterTemplate{name: name}
}

// ExportSpans 模板方法
func (t *ExporterTemplate) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan, impl ExporterImplementation) error {
    // 1. 前置处理
    if err := t.preProcess(ctx, spans); err != nil {
        return err
    }
    
    // 2. 验证
    if err := impl.Validate(ctx, spans); err != nil {
        return err
    }
    
    // 3. 转换
    data, err := impl.Transform(ctx, spans)
    if err != nil {
        return err
    }
    
    // 4. 导出
    if err := impl.Export(ctx, data); err != nil {
        return err
    }
    
    // 5. 后置处理
    return t.postProcess(ctx, spans)
}

func (t *ExporterTemplate) preProcess(ctx context.Context, spans []trace.ReadOnlySpan) error {
    fmt.Printf("[%s] Pre-processing %d spans\n", t.name, len(spans))
    return nil
}

func (t *ExporterTemplate) postProcess(ctx context.Context, spans []trace.ReadOnlySpan) error {
    fmt.Printf("[%s] Post-processing complete\n", t.name)
    return nil
}

// ExporterImplementation 导出器实现接口
type ExporterImplementation interface {
    Validate(ctx context.Context, spans []trace.ReadOnlySpan) error
    Transform(ctx context.Context, spans []trace.ReadOnlySpan) (interface{}, error)
    Export(ctx context.Context, data interface{}) error
}

// JSONExporter JSON 导出器实现
type JSONExporter struct {
    endpoint string
}

func (e *JSONExporter) Validate(ctx context.Context, spans []trace.ReadOnlySpan) error {
    if len(spans) == 0 {
        return fmt.Errorf("no spans to export")
    }
    return nil
}

func (e *JSONExporter) Transform(ctx context.Context, spans []trace.ReadOnlySpan) (interface{}, error) {
    // 转换为 JSON 格式
    data := make([]map[string]interface{}, len(spans))
    for i, span := range spans {
        data[i] = map[string]interface{}{
            "name":     span.Name(),
            "trace_id": span.SpanContext().TraceID().String(),
            "span_id":  span.SpanContext().SpanID().String(),
        }
    }
    return data, nil
}

func (e *JSONExporter) Export(ctx context.Context, data interface{}) error {
    fmt.Printf("Exporting to %s: %v\n", e.endpoint, data)
    return nil
}

// 使用示例
func ExampleTemplate() {
    template := NewExporterTemplate("json-exporter")
    impl := &JSONExporter{endpoint: "http://localhost:8080"}
    
    ctx := context.Background()
    var spans []trace.ReadOnlySpan
    
    template.ExportSpans(ctx, spans, impl)
}
```

**优点**:

- 复用算法骨架
- 子类定制具体步骤
- 符合开闭原则

---

## 5. 并发模式

### 5.1 Worker Pool 模式

**目的**: 使用固定数量的 worker 处理任务。

**应用场景**: 并发导出 Span、批量处理。

**实现示例**:

```go
package concurrent

import (
    "context"
    "sync"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// WorkerPool Worker 池
type WorkerPool struct {
    workerCount int
    taskCh      chan trace.ReadOnlySpan
    exporter    trace.SpanExporter
    wg          sync.WaitGroup
    ctx         context.Context
    cancel      context.CancelFunc
}

// NewWorkerPool 创建 Worker 池
func NewWorkerPool(workerCount int, exporter trace.SpanExporter) *WorkerPool {
    ctx, cancel := context.WithCancel(context.Background())
    return &WorkerPool{
        workerCount: workerCount,
        taskCh:      make(chan trace.ReadOnlySpan, workerCount*10),
        exporter:    exporter,
        ctx:         ctx,
        cancel:      cancel,
    }
}

// Start 启动 Worker 池
func (p *WorkerPool) Start() {
    for i := 0; i < p.workerCount; i++ {
        p.wg.Add(1)
        go p.worker(i)
    }
}

// worker Worker 协程
func (p *WorkerPool) worker(id int) {
    defer p.wg.Done()
    
    for {
        select {
        case span, ok := <-p.taskCh:
            if !ok {
                return
            }
            // 处理 Span
            p.exporter.ExportSpans(p.ctx, []trace.ReadOnlySpan{span})
            
        case <-p.ctx.Done():
            return
        }
    }
}

// Submit 提交任务
func (p *WorkerPool) Submit(span trace.ReadOnlySpan) {
    select {
    case p.taskCh <- span:
    case <-p.ctx.Done():
    }
}

// Stop 停止 Worker 池
func (p *WorkerPool) Stop() {
    close(p.taskCh)
    p.wg.Wait()
    p.cancel()
}

// 使用示例
func ExampleWorkerPool(exporter trace.SpanExporter) {
    pool := NewWorkerPool(10, exporter)
    pool.Start()
    defer pool.Stop()
    
    // 提交任务
    // for _, span := range spans {
    //     pool.Submit(span)
    // }
}
```

**优点**:

- 控制并发数
- 资源复用
- 高吞吐量

### 5.2 Pipeline 模式

**目的**: 将处理分解为多个阶段。

**应用场景**: Span 处理流水线。

**实现示例**:

```go
package pipeline

import (
    "context"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// Stage 处理阶段
type Stage func(ctx context.Context, in <-chan trace.ReadOnlySpan) <-chan trace.ReadOnlySpan

// Pipeline 流水线
type Pipeline struct {
    stages []Stage
}

// NewPipeline 创建流水线
func NewPipeline(stages ...Stage) *Pipeline {
    return &Pipeline{stages: stages}
}

// Execute 执行流水线
func (p *Pipeline) Execute(ctx context.Context, input <-chan trace.ReadOnlySpan) <-chan trace.ReadOnlySpan {
    out := input
    for _, stage := range p.stages {
        out = stage(ctx, out)
    }
    return out
}

// FilterStage 过滤阶段
func FilterStage(predicate func(trace.ReadOnlySpan) bool) Stage {
    return func(ctx context.Context, in <-chan trace.ReadOnlySpan) <-chan trace.ReadOnlySpan {
        out := make(chan trace.ReadOnlySpan)
        go func() {
            defer close(out)
            for span := range in {
                if predicate(span) {
                    select {
                    case out <- span:
                    case <-ctx.Done():
                        return
                    }
                }
            }
        }()
        return out
    }
}

// TransformStage 转换阶段
func TransformStage(transform func(trace.ReadOnlySpan) trace.ReadOnlySpan) Stage {
    return func(ctx context.Context, in <-chan trace.ReadOnlySpan) <-chan trace.ReadOnlySpan {
        out := make(chan trace.ReadOnlySpan)
        go func() {
            defer close(out)
            for span := range in {
                transformed := transform(span)
                select {
                case out <- transformed:
                case <-ctx.Done():
                    return
                }
            }
        }()
        return out
    }
}

// BatchStage 批处理阶段
func BatchStage(batchSize int) Stage {
    return func(ctx context.Context, in <-chan trace.ReadOnlySpan) <-chan trace.ReadOnlySpan {
        out := make(chan trace.ReadOnlySpan)
        go func() {
            defer close(out)
            batch := make([]trace.ReadOnlySpan, 0, batchSize)
            
            for span := range in {
                batch = append(batch, span)
                if len(batch) >= batchSize {
                    for _, s := range batch {
                        select {
                        case out <- s:
                        case <-ctx.Done():
                            return
                        }
                    }
                    batch = batch[:0]
                }
            }
            
            // 处理剩余
            for _, s := range batch {
                select {
                case out <- s:
                case <-ctx.Done():
                    return
                }
            }
        }()
        return out
    }
}

// 使用示例
func ExamplePipeline() {
    ctx := context.Background()
    
    // 创建流水线
    pipeline := NewPipeline(
        FilterStage(func(span trace.ReadOnlySpan) bool {
            return span.Name() != "health-check"
        }),
        BatchStage(100),
    )
    
    // 输入 channel
    input := make(chan trace.ReadOnlySpan)
    
    // 执行流水线
    output := pipeline.Execute(ctx, input)
    
    // 消费输出
    go func() {
        for span := range output {
            _ = span
        }
    }()
}
```

**优点**:

- 模块化处理
- 并行执行
- 易于组合

### 5.3 Fan-Out/Fan-In 模式

**目的**: 将任务分发到多个 worker,然后汇总结果。

**应用场景**: 并行导出到多个后端。

**实现示例**:

```go
package fanout

import (
    "context"
    "sync"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// FanOutFanIn Fan-Out/Fan-In 处理器
type FanOutFanIn struct {
    exporters []trace.SpanExporter
}

// NewFanOutFanIn 创建处理器
func NewFanOutFanIn(exporters ...trace.SpanExporter) *FanOutFanIn {
    return &FanOutFanIn{
        exporters: exporters,
    }
}

// ExportSpans 导出 Spans (Fan-Out/Fan-In)
func (f *FanOutFanIn) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    // Fan-Out: 分发到多个 exporter
    var wg sync.WaitGroup
    errCh := make(chan error, len(f.exporters))
    
    for _, exporter := range f.exporters {
        wg.Add(1)
        go func(exp trace.SpanExporter) {
            defer wg.Done()
            if err := exp.ExportSpans(ctx, spans); err != nil {
                errCh <- err
            }
        }(exporter)
    }
    
    // Fan-In: 等待所有结果
    wg.Wait()
    close(errCh)
    
    // 收集错误
    for err := range errCh {
        return err // 返回第一个错误
    }
    
    return nil
}

// Shutdown 关闭所有 exporter
func (f *FanOutFanIn) Shutdown(ctx context.Context) error {
    var wg sync.WaitGroup
    errCh := make(chan error, len(f.exporters))
    
    for _, exporter := range f.exporters {
        wg.Add(1)
        go func(exp trace.SpanExporter) {
            defer wg.Done()
            if err := exp.Shutdown(ctx); err != nil {
                errCh <- err
            }
        }(exporter)
    }
    
    wg.Wait()
    close(errCh)
    
    for err := range errCh {
        return err
    }
    
    return nil
}
```

**优点**:

- 并行处理
- 提高吞吐量
- 容错能力

### 5.4 Circuit Breaker 模式

**目的**: 防止级联故障。

**应用场景**: Exporter 故障保护。

**实现示例**:

```go
package circuitbreaker

import (
    "context"
    "errors"
    "sync"
    "time"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// State 断路器状态
type State int

const (
    StateClosed State = iota
    StateOpen
    StateHalfOpen
)

// CircuitBreaker 断路器
type CircuitBreaker struct {
    exporter         trace.SpanExporter
    state            State
    failureCount     int
    successCount     int
    failureThreshold int
    successThreshold int
    timeout          time.Duration
    lastFailureTime  time.Time
    mu               sync.RWMutex
}

// NewCircuitBreaker 创建断路器
func NewCircuitBreaker(exporter trace.SpanExporter, failureThreshold, successThreshold int, timeout time.Duration) *CircuitBreaker {
    return &CircuitBreaker{
        exporter:         exporter,
        state:            StateClosed,
        failureThreshold: failureThreshold,
        successThreshold: successThreshold,
        timeout:          timeout,
    }
}

// ExportSpans 导出 Spans (带断路器保护)
func (cb *CircuitBreaker) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    cb.mu.Lock()
    
    // 检查状态
    if cb.state == StateOpen {
        // 检查是否可以尝试恢复
        if time.Since(cb.lastFailureTime) > cb.timeout {
            cb.state = StateHalfOpen
            cb.successCount = 0
        } else {
            cb.mu.Unlock()
            return errors.New("circuit breaker is open")
        }
    }
    
    cb.mu.Unlock()
    
    // 尝试导出
    err := cb.exporter.ExportSpans(ctx, spans)
    
    cb.mu.Lock()
    defer cb.mu.Unlock()
    
    if err != nil {
        cb.onFailure()
        return err
    }
    
    cb.onSuccess()
    return nil
}

// onFailure 处理失败
func (cb *CircuitBreaker) onFailure() {
    cb.failureCount++
    cb.lastFailureTime = time.Now()
    
    if cb.state == StateHalfOpen {
        // 半开状态失败,立即打开
        cb.state = StateOpen
        cb.failureCount = 0
    } else if cb.failureCount >= cb.failureThreshold {
        // 达到失败阈值,打开断路器
        cb.state = StateOpen
        cb.failureCount = 0
    }
}

// onSuccess 处理成功
func (cb *CircuitBreaker) onSuccess() {
    cb.failureCount = 0
    
    if cb.state == StateHalfOpen {
        cb.successCount++
        if cb.successCount >= cb.successThreshold {
            // 达到成功阈值,关闭断路器
            cb.state = StateClosed
            cb.successCount = 0
        }
    }
}

// Shutdown 关闭
func (cb *CircuitBreaker) Shutdown(ctx context.Context) error {
    return cb.exporter.Shutdown(ctx)
}

// GetState 获取状态
func (cb *CircuitBreaker) GetState() State {
    cb.mu.RLock()
    defer cb.mu.RUnlock()
    return cb.state
}
```

**优点**:

- 防止级联故障
- 快速失败
- 自动恢复

---

## 6. 架构模式

### 6.1 分层架构

**目的**: 将系统分为多个层次。

**应用场景**: OTLP 系统架构。

**架构示例**:

```text
┌─────────────────────────────────────┐
│     Application Layer (应用层)      │
│  - Business Logic                   │
│  - API Handlers                     │
└─────────────────────────────────────┘
              ↓
┌─────────────────────────────────────┐
│   Instrumentation Layer (插桩层)    │
│  - Tracer                           │
│  - Span Creation                    │
└─────────────────────────────────────┘
              ↓
┌─────────────────────────────────────┐
│      SDK Layer (SDK 层)             │
│  - TracerProvider                   │
│  - Processors                       │
│  - Samplers                         │
└─────────────────────────────────────┘
              ↓
┌─────────────────────────────────────┐
│    Export Layer (导出层)            │
│  - Exporters                        │
│  - Batching                         │
└─────────────────────────────────────┘
              ↓
┌─────────────────────────────────────┐
│   Transport Layer (传输层)          │
│  - gRPC / HTTP                      │
│  - Protocol Buffers                 │
└─────────────────────────────────────┘
```

**实现示例**:

```go
package architecture

// 应用层
type ApplicationService struct {
    tracer trace.Tracer
}

func (s *ApplicationService) ProcessOrder(ctx context.Context, order *Order) error {
    ctx, span := s.tracer.Start(ctx, "ProcessOrder")
    defer span.End()
    
    // 业务逻辑
    return nil
}

// SDK 层
type SDKLayer struct {
    provider  *trace.TracerProvider
    processor trace.SpanProcessor
    sampler   trace.Sampler
}

// 导出层
type ExportLayer struct {
    exporter trace.SpanExporter
    batcher  *BatchProcessor
}

// 传输层
type TransportLayer struct {
    client *grpc.ClientConn
}
```

**优点**:

- 职责清晰
- 易于维护
- 可替换层次

### 6.2 插件架构

**目的**: 支持动态扩展功能。

**应用场景**: Collector 插件、Processor 插件。

**实现示例**:

```go
package plugin

import (
    "context"
    "fmt"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// Plugin 插件接口
type Plugin interface {
    Name() string
    Initialize(config map[string]interface{}) error
    Process(ctx context.Context, span trace.ReadOnlySpan) error
    Shutdown(ctx context.Context) error
}

// PluginRegistry 插件注册表
type PluginRegistry struct {
    plugins map[string]Plugin
}

// NewPluginRegistry 创建注册表
func NewPluginRegistry() *PluginRegistry {
    return &PluginRegistry{
        plugins: make(map[string]Plugin),
    }
}

// Register 注册插件
func (r *PluginRegistry) Register(plugin Plugin) error {
    name := plugin.Name()
    if _, exists := r.plugins[name]; exists {
        return fmt.Errorf("plugin %s already registered", name)
    }
    r.plugins[name] = plugin
    return nil
}

// Get 获取插件
func (r *PluginRegistry) Get(name string) (Plugin, error) {
    plugin, exists := r.plugins[name]
    if !exists {
        return nil, fmt.Errorf("plugin %s not found", name)
    }
    return plugin, nil
}

// List 列出所有插件
func (r *PluginRegistry) List() []string {
    names := make([]string, 0, len(r.plugins))
    for name := range r.plugins {
        names = append(names, name)
    }
    return names
}

// AttributeEnricherPlugin 属性增强插件
type AttributeEnricherPlugin struct {
    attributes map[string]string
}

func (p *AttributeEnricherPlugin) Name() string {
    return "attribute-enricher"
}

func (p *AttributeEnricherPlugin) Initialize(config map[string]interface{}) error {
    p.attributes = make(map[string]string)
    // 从配置加载属性
    return nil
}

func (p *AttributeEnricherPlugin) Process(ctx context.Context, span trace.ReadOnlySpan) error {
    // 添加属性到 Span
    return nil
}

func (p *AttributeEnricherPlugin) Shutdown(ctx context.Context) error {
    return nil
}

// 使用示例
func ExamplePlugin() {
    registry := NewPluginRegistry()
    
    // 注册插件
    plugin := &AttributeEnricherPlugin{}
    registry.Register(plugin)
    
    // 使用插件
    p, _ := registry.Get("attribute-enricher")
    p.Initialize(map[string]interface{}{})
}
```

**优点**:

- 高度可扩展
- 解耦核心和扩展
- 动态加载

### 6.3 微服务架构

**目的**: 将系统分解为独立的服务。

**应用场景**: 分布式追踪系统。

**架构示例**:

```text
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│   Service A  │────▶│   Service B  │────▶│   Service C  │
│   (Tracer)   │     │   (Tracer)   │     │   (Tracer)   │
└──────┬───────┘     └──────┬───────┘     └──────┬───────┘
       │                    │                    │
       │ OTLP               │ OTLP               │ OTLP
       ▼                    ▼                    ▼
┌─────────────────────────────────────────────────────────┐
│              OTLP Collector (Gateway)                   │
│  - Receive                                              │
│  - Process                                              │
│  - Export                                               │
└──────────────────────────┬──────────────────────────────┘
                           │
                           ▼
                  ┌────────────────┐
                  │    Backend     │
                  │  (Jaeger/...)  │
                  └────────────────┘
```

**实现示例**:

```go
package microservices

// ServiceA 服务 A
type ServiceA struct {
    tracer trace.Tracer
    client *ServiceBClient
}

func (s *ServiceA) HandleRequest(ctx context.Context, req *Request) error {
    ctx, span := s.tracer.Start(ctx, "ServiceA.HandleRequest")
    defer span.End()
    
    // 调用 Service B
    return s.client.Call(ctx, req)
}

// ServiceBClient Service B 客户端
type ServiceBClient struct {
    tracer trace.Tracer
}

func (c *ServiceBClient) Call(ctx context.Context, req *Request) error {
    ctx, span := c.tracer.Start(ctx, "ServiceB.Call")
    defer span.End()
    
    // 发送请求到 Service B
    // Context 会自动传播 trace context
    return nil
}
```

**优点**:

- 独立部署
- 技术多样性
- 弹性扩展

### 6.4 事件驱动架构

**目的**: 通过事件解耦组件。

**应用场景**: 异步 Span 处理。

**实现示例**:

```go
package eventdriven

import (
    "context"
    
    "go.opentelemetry.io/otel/sdk/trace"
)

// Event 事件
type Event struct {
    Type string
    Span trace.ReadOnlySpan
}

// EventBus 事件总线
type EventBus struct {
    subscribers map[string][]chan Event
}

// NewEventBus 创建事件总线
func NewEventBus() *EventBus {
    return &EventBus{
        subscribers: make(map[string][]chan Event),
    }
}

// Subscribe 订阅事件
func (bus *EventBus) Subscribe(eventType string) <-chan Event {
    ch := make(chan Event, 100)
    bus.subscribers[eventType] = append(bus.subscribers[eventType], ch)
    return ch
}

// Publish 发布事件
func (bus *EventBus) Publish(event Event) {
    for _, ch := range bus.subscribers[event.Type] {
        select {
        case ch <- event:
        default:
            // Channel 满了,跳过
        }
    }
}

// SpanEventProcessor 事件处理器
type SpanEventProcessor struct {
    bus *EventBus
}

func (p *SpanEventProcessor) OnEnd(span trace.ReadOnlySpan) {
    p.bus.Publish(Event{
        Type: "span.end",
        Span: span,
    })
}

// 使用示例
func ExampleEventDriven() {
    bus := NewEventBus()
    
    // 订阅事件
    spanEndCh := bus.Subscribe("span.end")
    
    // 处理事件
    go func() {
        for event := range spanEndCh {
            // 处理 Span 结束事件
            _ = event.Span
        }
    }()
}
```

**优点**:

- 松耦合
- 异步处理
- 易于扩展

---

## 7. 最佳实践

### 7.1 初始化最佳实践

**实践 1: 集中初始化**:

```go
package telemetry

import (
    "context"
    "log"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/sdk/trace"
)

// Setup 集中初始化遥测
func Setup(ctx context.Context, serviceName, serviceVersion string) (func(), error) {
    // 1. 创建 Resource
    res, err := createResource(ctx, serviceName, serviceVersion)
    if err != nil {
        return nil, err
    }
    
    // 2. 创建 Exporter
    exporter, err := createExporter(ctx)
    if err != nil {
        return nil, err
    }
    
    // 3. 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithResource(res),
        trace.WithBatcher(exporter),
    )
    
    // 4. 设置全局 Provider
    otel.SetTracerProvider(tp)
    
    // 5. 返回清理函数
    return func() {
        if err := tp.Shutdown(context.Background()); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }, nil
}
```

**实践 2: 优雅关闭**:

```go
func main() {
    ctx := context.Background()
    
    // 初始化
    shutdown, err := telemetry.Setup(ctx, "my-service", "1.0.0")
    if err != nil {
        log.Fatal(err)
    }
    
    // 确保清理
    defer shutdown()
    
    // 应用逻辑
    // ...
}
```

### 7.2 资源管理最佳实践

**实践 3: 使用 Resource 标识服务**:

```go
func createResource(ctx context.Context, serviceName, serviceVersion string) (*resource.Resource, error) {
    return resource.New(ctx,
        resource.WithAttributes(
            // 服务信息
            semconv.ServiceName(serviceName),
            semconv.ServiceVersion(serviceVersion),
            semconv.ServiceNamespace("production"),
            
            // 部署信息
            semconv.DeploymentEnvironment("prod"),
            attribute.String("deployment.region", "us-west-2"),
            
            // 主机信息
            semconv.HostName(hostname),
            semconv.HostArch(runtime.GOARCH),
            
            // 进程信息
            semconv.ProcessPID(os.Getpid()),
            semconv.ProcessRuntimeName("go"),
            semconv.ProcessRuntimeVersion(runtime.Version()),
        ),
    )
}
```

**实践 4: 资源检测器**:

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/contrib/detectors/aws/ec2"
    "go.opentelemetry.io/contrib/detectors/gcp"
)

func createResourceWithDetectors(ctx context.Context) (*resource.Resource, error) {
    return resource.New(ctx,
        resource.WithDetectors(
            ec2.NewResourceDetector(),  // AWS EC2
            gcp.NewDetector(),          // Google Cloud
        ),
        resource.WithAttributes(
            semconv.ServiceName("my-service"),
        ),
    )
}
```

### 7.3 错误处理最佳实践

**实践 5: 统一错误处理**:

```go
func processWithErrorHandling(ctx context.Context) (err error) {
    ctx, span := tracer.Start(ctx, "processWithErrorHandling")
    defer func() {
        if err != nil {
            // 记录错误
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            
            // 添加错误上下文
            span.SetAttributes(
                attribute.String("error.type", fmt.Sprintf("%T", err)),
                attribute.String("error.message", err.Error()),
            )
        }
        span.End()
    }()
    
    // 业务逻辑
    return doWork(ctx)
}
```

**实践 6: 错误分类**:

```go
func classifyError(err error) string {
    switch {
    case errors.Is(err, context.Canceled):
        return "canceled"
    case errors.Is(err, context.DeadlineExceeded):
        return "timeout"
    case errors.Is(err, sql.ErrNoRows):
        return "not_found"
    default:
        return "internal"
    }
}

func handleError(span trace.Span, err error) {
    span.RecordError(err)
    span.SetAttributes(
        attribute.String("error.category", classifyError(err)),
    )
}
```

### 7.4 性能优化最佳实践

**实践 7: 批处理**:

```go
func configureBatching() *trace.TracerProvider {
    return trace.NewTracerProvider(
        trace.WithBatcher(exporter,
            // 批次大小
            trace.WithMaxExportBatchSize(512),
            
            // 批次超时
            trace.WithBatchTimeout(5*time.Second),
            
            // 队列大小
            trace.WithMaxQueueSize(2048),
        ),
    )
}
```

**实践 8: 采样**:

```go
func configureSampling() *trace.TracerProvider {
    // 父级采样 + 比例采样
    sampler := trace.ParentBased(
        trace.TraceIDRatioBased(0.1), // 10% 采样
    )
    
    return trace.NewTracerProvider(
        trace.WithSampler(sampler),
    )
}
```

**实践 9: 资源限制**:

```go
func configureResourceLimits() *trace.TracerProvider {
    return trace.NewTracerProvider(
        trace.WithSpanLimits(trace.SpanLimits{
            // 属性限制
            AttributeCountLimit:      128,
            AttributeValueLengthLimit: 1024,
            
            // 事件限制
            EventCountLimit:          128,
            
            // 链接限制
            LinkCountLimit:           128,
        }),
    )
}
```

### 7.5 测试最佳实践

**实践 10: 使用内存导出器测试**:

```go
func TestWithInMemoryExporter(t *testing.T) {
    // 创建内存导出器
    exporter := tracetest.NewInMemoryExporter()
    
    // 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithSyncer(exporter),
    )
    
    tracer := tp.Tracer("test")
    
    // 执行测试
    ctx, span := tracer.Start(context.Background(), "test-operation")
    span.SetAttributes(attribute.String("key", "value"))
    span.End()
    
    // 验证
    spans := exporter.GetSpans()
    require.Len(t, spans, 1)
    assert.Equal(t, "test-operation", spans[0].Name())
}
```

**实践 11: 模拟测试**:

```go
type MockExporter struct {
    mock.Mock
}

func (m *MockExporter) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    args := m.Called(ctx, spans)
    return args.Error(0)
}

func (m *MockExporter) Shutdown(ctx context.Context) error {
    args := m.Called(ctx)
    return args.Error(0)
}

func TestWithMock(t *testing.T) {
    mockExporter := new(MockExporter)
    mockExporter.On("ExportSpans", mock.Anything, mock.Anything).Return(nil)
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(mockExporter),
    )
    
    // 测试逻辑
    // ...
    
    mockExporter.AssertExpectations(t)
}
```

### 7.6 部署最佳实践

**实践 12: 环境配置**:

```go
type Config struct {
    ServiceName    string
    ServiceVersion string
    Environment    string
    OTLPEndpoint   string
    SampleRate     float64
}

func LoadConfig() *Config {
    return &Config{
        ServiceName:    getEnv("SERVICE_NAME", "unknown"),
        ServiceVersion: getEnv("SERVICE_VERSION", "unknown"),
        Environment:    getEnv("ENVIRONMENT", "development"),
        OTLPEndpoint:   getEnv("OTLP_ENDPOINT", "localhost:4317"),
        SampleRate:     getEnvFloat("SAMPLE_RATE", 1.0),
    }
}

func getEnv(key, defaultValue string) string {
    if value := os.Getenv(key); value != "" {
        return value
    }
    return defaultValue
}
```

**实践 13: 健康检查**:

```go
type HealthChecker struct {
    tp *trace.TracerProvider
}

func (h *HealthChecker) Check(ctx context.Context) error {
    // 检查 TracerProvider 是否正常
    tracer := h.tp.Tracer("health-check")
    _, span := tracer.Start(ctx, "health-check")
    defer span.End()
    
    return nil
}
```

**实践 14: 监控指标**:

```go
type TelemetryMetrics struct {
    spansExported   prometheus.Counter
    exportDuration  prometheus.Histogram
    exportErrors    prometheus.Counter
}

func NewTelemetryMetrics() *TelemetryMetrics {
    return &TelemetryMetrics{
        spansExported: prometheus.NewCounter(prometheus.CounterOpts{
            Name: "otlp_spans_exported_total",
            Help: "Total number of spans exported",
        }),
        exportDuration: prometheus.NewHistogram(prometheus.HistogramOpts{
            Name: "otlp_export_duration_seconds",
            Help: "Duration of span export operations",
        }),
        exportErrors: prometheus.NewCounter(prometheus.CounterOpts{
            Name: "otlp_export_errors_total",
            Help: "Total number of export errors",
        }),
    }
}
```

---

## 8. 反模式

### 8.1 设计反模式

**反模式 1: 过度设计**:

❌ **错误**:

```go
// 为简单场景创建复杂的抽象
type SpanFactoryBuilderProviderManager interface {
    CreateSpanFactoryBuilder() SpanFactoryBuilder
}
```

✅ **正确**:

```go
// 使用简单直接的方式
tracer := otel.Tracer("my-service")
ctx, span := tracer.Start(ctx, "operation")
defer span.End()
```

**反模式 2: 上帝对象**:

❌ **错误**:

```go
// 一个类做所有事情
type TelemetryManager struct {
    // 太多职责
    tracerProvider *trace.TracerProvider
    meterProvider  *metric.MeterProvider
    loggerProvider *log.LoggerProvider
    exporter1      trace.SpanExporter
    exporter2      trace.SpanExporter
    sampler        trace.Sampler
    processor      trace.SpanProcessor
    // ... 更多字段
}
```

✅ **正确**:

```go
// 职责分离
type TraceManager struct {
    provider *trace.TracerProvider
}

type MetricManager struct {
    provider *metric.MeterProvider
}
```

### 8.2 性能反模式

**反模式 3: 同步导出**:

❌ **错误**:

```go
// 同步导出阻塞主流程
tp := trace.NewTracerProvider(
    trace.WithSyncer(exporter), // 同步导出
)
```

✅ **正确**:

```go
// 使用批处理异步导出
tp := trace.NewTracerProvider(
    trace.WithBatcher(exporter), // 异步批处理
)
```

**反模式 4: 无限制的属性**:

❌ **错误**:

```go
// 添加过多属性
span.SetAttributes(
    attribute.String("user.full_profile", largeJSON), // 大量数据
    attribute.String("request.body", requestBody),    // 敏感数据
)
```

✅ **正确**:

```go
// 只添加必要的属性
span.SetAttributes(
    attribute.String("user.id", userID),
    attribute.String("request.method", method),
)
```

### 8.3 安全反模式

**反模式 5: 记录敏感信息**:

❌ **错误**:

```go
span.SetAttributes(
    attribute.String("password", password),      // 敏感!
    attribute.String("credit_card", cardNumber), // 敏感!
)
```

✅ **正确**:

```go
span.SetAttributes(
    attribute.String("user.id", userID),
    attribute.Bool("payment.success", true),
)
```

**反模式 6: 不安全的连接**:

❌ **错误**:

```go
// 生产环境使用不安全连接
exporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("collector:4317"),
    otlptracegrpc.WithInsecure(), // 不安全!
)
```

✅ **正确**:

```go
// 使用 TLS
exporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("collector:4317"),
    otlptracegrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")),
)
```

---

## 9. 参考文献

1. **设计模式**:
   - Gang of Four: Design Patterns
   - Martin Fowler: Patterns of Enterprise Application Architecture

2. **并发模式**:
   - Go Concurrency Patterns
   - Concurrency in Go

3. **OpenTelemetry**:
   - OpenTelemetry Specification
   - OpenTelemetry Go SDK Documentation

4. **相关文档**:
   - `otlp-golang-semantic-programming-integration.md` - 语义模型与编程范式
   - `otlp-golang-idiomatic-programming-guide.md` - 编程惯用法
   - `docs/otlp/semantic-model.md` - OTLP 语义模型

---

**文档结束**:

**版本**: 1.0.0  
**日期**: 2025-10-06  
**作者**: OTLP 项目团队  
**许可**: 遵循项目根目录的 LICENSE 文件

# TracerProvider 配置

## 📋 目录

- [TracerProvider 配置](#tracerprovider-配置)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 TracerProvider](#什么是-tracerprovider)
    - [为什么需要配置](#为什么需要配置)
  - [基本配置](#基本配置)
    - [1. 最小配置](#1-最小配置)
    - [2. 生产级配置](#2-生产级配置)
  - [配置选项](#配置选项)
    - [1. Resource 配置](#1-resource-配置)
    - [2. Sampler 配置](#2-sampler-配置)
    - [3. SpanProcessor 配置](#3-spanprocessor-配置)
    - [4. IDGenerator 配置](#4-idgenerator-配置)
    - [5. SpanLimits 配置](#5-spanlimits-配置)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本配置](#1-基本配置)
    - [2. 函数式选项模式](#2-函数式选项模式)
    - [3. 配置验证](#3-配置验证)
  - [配置加载](#配置加载)
    - [1. 从环境变量加载](#1-从环境变量加载)
    - [2. 从配置文件加载](#2-从配置文件加载)
    - [3. 动态配置](#3-动态配置)
  - [多环境配置](#多环境配置)
    - [1. 开发环境](#1-开发环境)
    - [2. 测试环境](#2-测试环境)
    - [3. 生产环境](#3-生产环境)
  - [性能优化](#性能优化)
  - [最佳实践](#最佳实践)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 TracerProvider

**TracerProvider** 是 OpenTelemetry SDK 的核心组件，负责创建和管理 Tracer 实例。

```text
Application
    ↓
TracerProvider (全局单例)
    ↓ 创建
Tracer (per instrumentation scope)
    ↓ 创建
Span (per operation)
```

### 为什么需要配置

```text
配置的重要性:
✅ 控制采样策略 (减少成本)
✅ 设置 Span 导出器 (数据发送目的地)
✅ 定义资源属性 (服务标识)
✅ 配置处理器 (批处理、过滤)
✅ 设置限制 (防止资源耗尽)
```

---

## 基本配置

### 1. 最小配置

```go
package main

import (
    "context"
    "log"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
    "go.opentelemetry.io/otel/sdk/trace"
)

func main() {
    // 创建导出器
    exporter, err := stdouttrace.New(
        stdouttrace.WithPrettyPrint(),
    )
    if err != nil {
        log.Fatal(err)
    }
    
    // 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
    )
    
    // 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    
    // 应用关闭时清理
    defer func() {
        if err := tp.Shutdown(context.Background()); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }()
    
    // 使用 TracerProvider
    tracer := otel.Tracer("myapp")
    ctx, span := tracer.Start(context.Background(), "main")
    defer span.End()
    
    // ... 业务逻辑
}
```

### 2. 生产级配置

```go
package main

import (
    "context"
    "log"
    "os"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func InitTracer() (*trace.TracerProvider, error) {
    ctx := context.Background()
    
    // 1. 创建 OTLP gRPC 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 配置资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("myapp"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
        ),
        resource.WithProcess(),
        resource.WithHost(),
    )
    if err != nil {
        return nil, err
    }
    
    // 3. 创建 TracerProvider
    tp := trace.NewTracerProvider(
        // 资源
        trace.WithResource(res),
        
        // 采样器: 生产环境使用 ParentBased
        trace.WithSampler(trace.ParentBased(
            trace.TraceIDRatioBased(0.1), // 10% 采样率
        )),
        
        // 批处理导出器
        trace.WithBatcher(exporter,
            trace.WithBatchTimeout(5*time.Second),
            trace.WithMaxExportBatchSize(512),
            trace.WithMaxQueueSize(2048),
        ),
        
        // Span 限制
        trace.WithSpanLimits(trace.SpanLimits{
            AttributeCountLimit:        128,
            EventCountLimit:            128,
            LinkCountLimit:             128,
            AttributeValueLengthLimit:  4096,
        }),
    )
    
    return tp, nil
}

func main() {
    tp, err := InitTracer()
    if err != nil {
        log.Fatal(err)
    }
    
    otel.SetTracerProvider(tp)
    defer tp.Shutdown(context.Background())
    
    // ... 应用逻辑
}
```

---

## 配置选项

### 1. Resource 配置

Resource 描述服务的元数据：

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

// 基本资源
res := resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceName("myapp"),
    semconv.ServiceVersion("1.0.0"),
)

// 自动检测资源
res, _ := resource.New(ctx,
    resource.WithFromEnv(),      // 从环境变量
    resource.WithProcess(),       // 进程信息
    resource.WithHost(),          // 主机信息
    resource.WithContainer(),     // 容器信息
    resource.WithOS(),            // 操作系统信息
)

// 合并资源
res, _ := resource.Merge(
    resource.Default(),
    resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceName("myapp"),
    ),
)
```

### 2. Sampler 配置

Sampler 控制采样策略：

```go
// 1. AlwaysOn: 采样所有 Span
sampler := trace.AlwaysSample()

// 2. AlwaysOff: 不采样任何 Span
sampler := trace.NeverSample()

// 3. TraceIDRatioBased: 基于 TraceID 的比例采样
sampler := trace.TraceIDRatioBased(0.1) // 10% 采样率

// 4. ParentBased: 基于父 Span 的采样决策
sampler := trace.ParentBased(
    trace.TraceIDRatioBased(0.1),
    trace.WithRemoteParentSampled(trace.AlwaysSample()),
    trace.WithRemoteParentNotSampled(trace.NeverSample()),
    trace.WithLocalParentSampled(trace.AlwaysSample()),
    trace.WithLocalParentNotSampled(trace.NeverSample()),
)

// 使用
tp := trace.NewTracerProvider(
    trace.WithSampler(sampler),
)
```

### 3. SpanProcessor 配置

SpanProcessor 处理 Span 的导出：

```go
// 1. SimpleSpanProcessor: 同步导出 (开发环境)
processor := trace.NewSimpleSpanProcessor(exporter)

// 2. BatchSpanProcessor: 批处理导出 (生产环境)
processor := trace.NewBatchSpanProcessor(exporter,
    // 批处理超时
    trace.WithBatchTimeout(5*time.Second),
    
    // 最大批次大小
    trace.WithMaxExportBatchSize(512),
    
    // 最大队列大小
    trace.WithMaxQueueSize(2048),
    
    // 导出超时
    trace.WithExportTimeout(30*time.Second),
)

// 使用多个处理器
tp := trace.NewTracerProvider(
    trace.WithSpanProcessor(processor1),
    trace.WithSpanProcessor(processor2),
)
```

### 4. IDGenerator 配置

IDGenerator 生成 TraceID 和 SpanID：

```go
import "go.opentelemetry.io/otel/sdk/trace"

// 默认: 随机 ID 生成器
tp := trace.NewTracerProvider(
    trace.WithIDGenerator(trace.NewRandomIDGenerator()),
)

// 自定义 ID 生成器
type CustomIDGenerator struct{}

func (g *CustomIDGenerator) NewIDs(ctx context.Context) (trace.TraceID, trace.SpanID) {
    // 自定义逻辑
    return trace.TraceID{}, trace.SpanID{}
}

func (g *CustomIDGenerator) NewSpanID(ctx context.Context, traceID trace.TraceID) trace.SpanID {
    // 自定义逻辑
    return trace.SpanID{}
}

tp := trace.NewTracerProvider(
    trace.WithIDGenerator(&CustomIDGenerator{}),
)
```

### 5. SpanLimits 配置

SpanLimits 限制 Span 的大小：

```go
limits := trace.SpanLimits{
    // 属性数量限制
    AttributeCountLimit: 128,
    
    // 事件数量限制
    EventCountLimit: 128,
    
    // 链接数量限制
    LinkCountLimit: 128,
    
    // 属性值长度限制
    AttributeValueLengthLimit: 4096,
    
    // 每个事件的属性数量限制
    AttributePerEventCountLimit: 128,
    
    // 每个链接的属性数量限制
    AttributePerLinkCountLimit: 128,
}

tp := trace.NewTracerProvider(
    trace.WithSpanLimits(limits),
)
```

---

## Go 1.25.1 实现

### 1. 基本配置

```go
package tracing

import (
    "context"
    "fmt"
    "time"
    
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

// Config TracerProvider 配置
type Config struct {
    ServiceName    string
    ServiceVersion string
    Environment    string
    
    // 采样配置
    SamplingRate float64
    
    // 导出器配置
    ExporterType     string // "otlp", "jaeger", "stdout"
    ExporterEndpoint string
    
    // 批处理配置
    BatchTimeout         time.Duration
    MaxExportBatchSize   int
    MaxQueueSize         int
    
    // Span 限制
    SpanLimits trace.SpanLimits
}

// DefaultConfig 默认配置
func DefaultConfig() Config {
    return Config{
        ServiceName:          "unknown-service",
        ServiceVersion:       "0.0.0",
        Environment:          "development",
        SamplingRate:         1.0,
        ExporterType:         "stdout",
        ExporterEndpoint:     "",
        BatchTimeout:         5 * time.Second,
        MaxExportBatchSize:   512,
        MaxQueueSize:         2048,
        SpanLimits: trace.SpanLimits{
            AttributeCountLimit:       128,
            EventCountLimit:           128,
            LinkCountLimit:            128,
            AttributeValueLengthLimit: 4096,
        },
    }
}

// NewTracerProvider 创建 TracerProvider
func NewTracerProvider(cfg Config) (*trace.TracerProvider, error) {
    ctx := context.Background()
    
    // 1. 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(cfg.ServiceName),
            semconv.ServiceVersion(cfg.ServiceVersion),
            semconv.DeploymentEnvironment(cfg.Environment),
        ),
        resource.WithProcess(),
        resource.WithHost(),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create resource: %w", err)
    }
    
    // 2. 创建导出器
    exporter, err := createExporter(cfg)
    if err != nil {
        return nil, fmt.Errorf("failed to create exporter: %w", err)
    }
    
    // 3. 创建采样器
    sampler := createSampler(cfg.SamplingRate)
    
    // 4. 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithResource(res),
        trace.WithSampler(sampler),
        trace.WithBatcher(exporter,
            trace.WithBatchTimeout(cfg.BatchTimeout),
            trace.WithMaxExportBatchSize(cfg.MaxExportBatchSize),
            trace.WithMaxQueueSize(cfg.MaxQueueSize),
        ),
        trace.WithSpanLimits(cfg.SpanLimits),
    )
    
    return tp, nil
}
```

### 2. 函数式选项模式

```go
package tracing

// Option TracerProvider 配置选项
type Option func(*Config)

// WithServiceName 设置服务名称
func WithServiceName(name string) Option {
    return func(c *Config) {
        c.ServiceName = name
    }
}

// WithServiceVersion 设置服务版本
func WithServiceVersion(version string) Option {
    return func(c *Config) {
        c.ServiceVersion = version
    }
}

// WithEnvironment 设置环境
func WithEnvironment(env string) Option {
    return func(c *Config) {
        c.Environment = env
    }
}

// WithSamplingRate 设置采样率
func WithSamplingRate(rate float64) Option {
    return func(c *Config) {
        c.SamplingRate = rate
    }
}

// WithOTLPExporter 配置 OTLP 导出器
func WithOTLPExporter(endpoint string) Option {
    return func(c *Config) {
        c.ExporterType = "otlp"
        c.ExporterEndpoint = endpoint
    }
}

// NewTracerProviderWithOptions 使用选项创建 TracerProvider
func NewTracerProviderWithOptions(opts ...Option) (*trace.TracerProvider, error) {
    cfg := DefaultConfig()
    
    for _, opt := range opts {
        opt(&cfg)
    }
    
    return NewTracerProvider(cfg)
}

// 使用示例
func main() {
    tp, err := NewTracerProviderWithOptions(
        WithServiceName("myapp"),
        WithServiceVersion("1.0.0"),
        WithEnvironment("production"),
        WithSamplingRate(0.1),
        WithOTLPExporter("localhost:4317"),
    )
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())
}
```

### 3. 配置验证

```go
// Validate 验证配置
func (c Config) Validate() error {
    if c.ServiceName == "" {
        return fmt.Errorf("service name is required")
    }
    
    if c.SamplingRate < 0 || c.SamplingRate > 1 {
        return fmt.Errorf("sampling rate must be between 0 and 1")
    }
    
    if c.BatchTimeout <= 0 {
        return fmt.Errorf("batch timeout must be positive")
    }
    
    if c.MaxExportBatchSize <= 0 {
        return fmt.Errorf("max export batch size must be positive")
    }
    
    if c.MaxQueueSize <= 0 {
        return fmt.Errorf("max queue size must be positive")
    }
    
    return nil
}

// NewTracerProvider 创建前验证
func NewTracerProvider(cfg Config) (*trace.TracerProvider, error) {
    if err := cfg.Validate(); err != nil {
        return nil, fmt.Errorf("invalid config: %w", err)
    }
    
    // ... 创建逻辑
}
```

---

## 配置加载

### 1. 从环境变量加载

```go
package tracing

import (
    "os"
    "strconv"
    "time"
)

// LoadFromEnv 从环境变量加载配置
func LoadFromEnv() Config {
    cfg := DefaultConfig()
    
    if v := os.Getenv("OTEL_SERVICE_NAME"); v != "" {
        cfg.ServiceName = v
    }
    
    if v := os.Getenv("OTEL_SERVICE_VERSION"); v != "" {
        cfg.ServiceVersion = v
    }
    
    if v := os.Getenv("OTEL_ENVIRONMENT"); v != "" {
        cfg.Environment = v
    }
    
    if v := os.Getenv("OTEL_TRACES_SAMPLER_ARG"); v != "" {
        if rate, err := strconv.ParseFloat(v, 64); err == nil {
            cfg.SamplingRate = rate
        }
    }
    
    if v := os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT"); v != "" {
        cfg.ExporterType = "otlp"
        cfg.ExporterEndpoint = v
    }
    
    return cfg
}

// 使用示例
func main() {
    cfg := LoadFromEnv()
    tp, _ := NewTracerProvider(cfg)
    defer tp.Shutdown(context.Background())
}
```

### 2. 从配置文件加载

```go
package tracing

import (
    "encoding/json"
    "os"
)

// ConfigFile 配置文件结构
type ConfigFile struct {
    Tracing struct {
        ServiceName    string  `json:"service_name"`
        ServiceVersion string  `json:"service_version"`
        Environment    string  `json:"environment"`
        SamplingRate   float64 `json:"sampling_rate"`
        Exporter       struct {
            Type     string `json:"type"`
            Endpoint string `json:"endpoint"`
        } `json:"exporter"`
    } `json:"tracing"`
}

// LoadFromFile 从文件加载配置
func LoadFromFile(path string) (Config, error) {
    cfg := DefaultConfig()
    
    data, err := os.ReadFile(path)
    if err != nil {
        return cfg, err
    }
    
    var file ConfigFile
    if err := json.Unmarshal(data, &file); err != nil {
        return cfg, err
    }
    
    cfg.ServiceName = file.Tracing.ServiceName
    cfg.ServiceVersion = file.Tracing.ServiceVersion
    cfg.Environment = file.Tracing.Environment
    cfg.SamplingRate = file.Tracing.SamplingRate
    cfg.ExporterType = file.Tracing.Exporter.Type
    cfg.ExporterEndpoint = file.Tracing.Exporter.Endpoint
    
    return cfg, nil
}

// 配置文件示例 (config.json)
/*
{
  "tracing": {
    "service_name": "myapp",
    "service_version": "1.0.0",
    "environment": "production",
    "sampling_rate": 0.1,
    "exporter": {
      "type": "otlp",
      "endpoint": "localhost:4317"
    }
  }
}
*/
```

### 3. 动态配置

```go
package tracing

import (
    "sync"
    "sync/atomic"
)

// DynamicConfig 支持动态更新的配置
type DynamicConfig struct {
    mu           sync.RWMutex
    config       Config
    samplingRate atomic.Value // float64
}

// NewDynamicConfig 创建动态配置
func NewDynamicConfig(cfg Config) *DynamicConfig {
    dc := &DynamicConfig{
        config: cfg,
    }
    dc.samplingRate.Store(cfg.SamplingRate)
    return dc
}

// GetConfig 获取当前配置
func (dc *DynamicConfig) GetConfig() Config {
    dc.mu.RLock()
    defer dc.mu.RUnlock()
    return dc.config
}

// UpdateSamplingRate 更新采样率
func (dc *DynamicConfig) UpdateSamplingRate(rate float64) {
    dc.samplingRate.Store(rate)
}

// GetSamplingRate 获取当前采样率
func (dc *DynamicConfig) GetSamplingRate() float64 {
    return dc.samplingRate.Load().(float64)
}
```

---

## 多环境配置

### 1. 开发环境

```go
func DevelopmentConfig() Config {
    return Config{
        ServiceName:        "myapp-dev",
        ServiceVersion:     "dev",
        Environment:        "development",
        SamplingRate:       1.0, // 采样所有
        ExporterType:       "stdout",
        BatchTimeout:       1 * time.Second,
        MaxExportBatchSize: 10,
        MaxQueueSize:       100,
    }
}
```

### 2. 测试环境

```go
func TestConfig() Config {
    return Config{
        ServiceName:        "myapp-test",
        ServiceVersion:     "test",
        Environment:        "testing",
        SamplingRate:       0.5, // 50% 采样
        ExporterType:       "otlp",
        ExporterEndpoint:   "test-collector:4317",
        BatchTimeout:       3 * time.Second,
        MaxExportBatchSize: 256,
        MaxQueueSize:       1024,
    }
}
```

### 3. 生产环境

```go
func ProductionConfig() Config {
    return Config{
        ServiceName:        "myapp",
        ServiceVersion:     "1.0.0",
        Environment:        "production",
        SamplingRate:       0.1, // 10% 采样
        ExporterType:       "otlp",
        ExporterEndpoint:   "collector:4317",
        BatchTimeout:       5 * time.Second,
        MaxExportBatchSize: 512,
        MaxQueueSize:       2048,
    }
}
```

---

## 性能优化

```go
// 1. 使用批处理导出器
tp := trace.NewTracerProvider(
    trace.WithBatcher(exporter,
        trace.WithBatchTimeout(5*time.Second),
        trace.WithMaxExportBatchSize(512),
    ),
)

// 2. 设置合理的采样率
sampler := trace.TraceIDRatioBased(0.1) // 10%

// 3. 限制 Span 大小
limits := trace.SpanLimits{
    AttributeCountLimit:       128,
    AttributeValueLengthLimit: 4096,
}

// 4. 使用 sync.OnceFunc (Go 1.25.1)
var initTP = sync.OnceFunc(func() {
    tp, _ := NewTracerProvider(cfg)
    otel.SetTracerProvider(tp)
})
```

---

## 最佳实践

```go
// ✅ 正确：使用全局单例
var tp *trace.TracerProvider

func init() {
    var err error
    tp, err = NewTracerProvider(cfg)
    if err != nil {
        log.Fatal(err)
    }
    otel.SetTracerProvider(tp)
}

// ❌ 错误：每次创建新的 TracerProvider
func handler() {
    tp := trace.NewTracerProvider(...) // 不要这样做
}

// ✅ 正确：正确关闭
defer func() {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    if err := tp.Shutdown(ctx); err != nil {
        log.Printf("Error shutting down: %v", err)
    }
}()

// ✅ 正确：使用环境特定配置
var cfg Config
switch os.Getenv("ENVIRONMENT") {
case "production":
    cfg = ProductionConfig()
case "development":
    cfg = DevelopmentConfig()
default:
    cfg = DefaultConfig()
}
```

---

## 参考资源

- [OpenTelemetry TracerProvider Spec](https://opentelemetry.io/docs/specs/otel/trace/sdk/#tracerprovider)
- [Go SDK TracerProvider](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/trace#TracerProvider)
- [02_Tracer创建.md](./02_Tracer创建.md)
- [03_采样器.md](./03_采样器.md)

---

**🎉 恭喜！你已经掌握了 TracerProvider 的完整配置！**

现在你可以：
- ✅ 配置基本和生产级 TracerProvider
- ✅ 使用函数式选项模式
- ✅ 从环境变量和文件加载配置
- ✅ 实现多环境配置
- ✅ 优化性能和遵循最佳实践


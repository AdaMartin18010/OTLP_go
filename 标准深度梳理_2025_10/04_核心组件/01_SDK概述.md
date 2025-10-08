# OpenTelemetry SDK 概述

> **SDK版本**: v1.20+ (各语言实现)  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry SDK 概述](#opentelemetry-sdk-概述)
  - [目录](#目录)
  - [1. 什么是SDK](#1-什么是sdk)
    - [1.1 SDK vs API](#11-sdk-vs-api)
    - [1.2 SDK职责](#12-sdk职责)
  - [2. SDK架构](#2-sdk架构)
    - [2.1 整体架构](#21-整体架构)
    - [2.2 组件交互](#22-组件交互)
  - [3. TracerProvider](#3-tracerprovider)
    - [3.1 职责](#31-职责)
    - [3.2 配置](#32-配置)
    - [3.3 实现示例](#33-实现示例)
  - [4. Tracer](#4-tracer)
    - [4.1 职责](#41-职责)
    - [4.2 创建Span](#42-创建span)
  - [5. Span Processor](#5-span-processor)
    - [5.1 SimpleSpanProcessor](#51-simplespanprocessor)
    - [5.2 BatchSpanProcessor](#52-batchspanprocessor)
    - [5.3 自定义Processor](#53-自定义processor)
  - [6. Span Exporter](#6-span-exporter)
    - [6.1 OTLP Exporter](#61-otlp-exporter)
    - [6.2 其他Exporter](#62-其他exporter)
  - [7. Sampler](#7-sampler)
    - [7.1 内置采样器](#71-内置采样器)
    - [7.2 自定义采样器](#72-自定义采样器)
  - [8. ID Generator](#8-id-generator)
  - [9. Resource](#9-resource)
  - [10. Propagator](#10-propagator)
  - [11. 生命周期管理](#11-生命周期管理)
  - [12. 多语言SDK实现](#12-多语言sdk实现)
  - [13. 最佳实践](#13-最佳实践)
  - [14. 参考资源](#14-参考资源)

## 1. 什么是SDK

### 1.1 SDK vs API

**关键区别**：

```text
API (应用程序编程接口):
- 定义接口规范
- 业务代码依赖的抽象
- 无实现细节
- 稳定,很少变化

SDK (软件开发工具包):
- 实现API接口
- 提供具体功能
- 包含配置选项
- 可插拔,可替换

关系:
┌──────────────────────────┐
│   应用程序代码            │
└────────────┬─────────────┘
             │ 依赖
    ┌────────▼────────┐
    │   OTel API      │  (接口)
    └────────┬────────┘
             │ 实现
    ┌────────▼────────┐
    │   OTel SDK      │  (实现)
    └────────┬────────┘
             │ 使用
    ┌────────▼────────┐
    │   Exporter      │  (导出器)
    └─────────────────┘

优势:
1. 解耦: 应用代码不依赖SDK实现
2. 灵活: 可更换SDK或配置
3. 测试: 可使用mock API
4. 性能: SDK可优化,不影响API
```

### 1.2 SDK职责

**SDK核心职责**：

```text
1. 实现API接口
   - Tracer, Span, SpanContext
   - Metrics, Logs API

2. 管理追踪生命周期
   - Span创建
   - Span结束
   - 上下文传播

3. 采样决策
   - 决定哪些span被记录
   - 采样策略执行

4. 数据处理
   - Span处理 (Processor)
   - 批处理
   - 重试

5. 数据导出
   - 发送到后端 (Exporter)
   - 协议转换

6. 资源管理
   - Resource检测
   - 资源属性附加

7. 上下文传播
   - W3C Trace Context
   - Baggage

8. 性能优化
   - 批处理
   - 内存管理
   - 线程安全
```

---

## 2. SDK架构

### 2.1 整体架构

**组件层次**：

```text
┌─────────────────────────────────────────────────────────┐
│                      应用程序                            │
└───────────────────────────┬─────────────────────────────┘
                            │ 使用
                ┌───────────▼────────────┐
                │    TracerProvider      │  (全局单例)
                └───────────┬────────────┘
                            │ 创建
                    ┌───────▼────────┐
                    │    Tracer      │  (命名tracer)
                    └───────┬────────┘
                            │ 创建
                        ┌───▼────┐
                        │  Span  │  (追踪单元)
                        └───┬────┘
                            │ 结束时
              ┌─────────────▼─────────────┐
              │     Span Processor        │  (处理逻辑)
              │  - SimpleSpanProcessor    │
              │  - BatchSpanProcessor     │
              └─────────────┬─────────────┘
                            │ 导出
                    ┌───────▼────────┐
                    │  Span Exporter │  (导出器)
                    │  - OTLP        │
                    │  - Jaeger      │
                    │  - Zipkin      │
                    └────────────────┘

横切关注点:
- Sampler (采样决策)
- ID Generator (生成trace_id, span_id)
- Resource (资源属性)
- Propagator (上下文传播)
```

### 2.2 组件交互

**典型流程**：

```text
1. 应用启动:
   TracerProvider.Builder()
     .setResource(resource)
     .setSampler(sampler)
     .addSpanProcessor(batchProcessor)
     .build()

2. 获取Tracer:
   tracer = tracerProvider.getTracer("my-service", "1.0.0")

3. 创建Span:
   span = tracer.spanBuilder("operation")
                .setSpanKind(CLIENT)
                .startSpan()
   
   内部流程:
   ┌──────────────────────────────────────────────┐
   │ 1. Sampler决策: 是否采样?                     │
   │ 2. ID Generator: 生成trace_id, span_id       │
   │ 3. 创建Span对象                              │
   │ 4. 设置开始时间                               │
   │ 5. 关联父Span (如果有)                        │
   └──────────────────────────────────────────────┘

4. Span操作:
   span.setAttribute("http.method", "GET")
   span.addEvent("cache_hit")
   span.recordException(error)

5. Span结束:
   span.end()
   
   内部流程:
   ┌──────────────────────────────────────────────┐
   │ 1. 设置结束时间                               │
   │ 2. 计算duration                              │
   │ 3. 调用Processor.onEnd(span)                 │
   │   ├─ SimpleProcessor: 立即导出               │
   │   └─ BatchProcessor: 加入批处理队列           │
   │ 4. Processor调用Exporter.export(spans)       │
   │ 5. Exporter发送到后端                         │
   └──────────────────────────────────────────────┘

6. 应用关闭:
   tracerProvider.shutdown()
   ├─ 刷新Processor (导出未完成的span)
   ├─ 关闭Exporter
   └─ 释放资源
```

---

## 3. TracerProvider

### 3.1 职责

**TracerProvider核心职责**：

```text
1. Tracer工厂
   - 创建和管理Tracer实例
   - 按name和version缓存Tracer

2. 全局配置
   - Resource (服务属性)
   - Sampler (采样策略)
   - SpanProcessor (span处理管道)
   - ID Generator (ID生成器)

3. 生命周期管理
   - 初始化
   - 运行
   - 优雅关闭

4. 隔离性
   - 支持多个TracerProvider (测试)
   - 默认全局单例
```

### 3.2 配置

**TracerProvider配置项**：

```text
核心配置:
1. Resource
   - 服务名称
   - 服务版本
   - 部署环境
   - 主机信息

2. Sampler
   - 采样策略
   - 采样率

3. SpanProcessor
   - 处理器链
   - 批处理配置

4. ID Generator
   - trace_id生成器
   - span_id生成器

5. SpanLimits
   - 最大属性数
   - 最大事件数
   - 最大link数
   - 属性值最大长度
```

### 3.3 实现示例

**Go SDK配置**：

```go
package main

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func initTracer() (*trace.TracerProvider, error) {
    // 1. 创建Exporter
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 定义Resource
    res, err := resource.New(context.Background(),
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
            semconv.ServiceVersionKey.String("1.0.0"),
            semconv.DeploymentEnvironmentKey.String("production"),
        ),
    )
    if err != nil {
        return nil, err
    }
    
    // 3. 配置TracerProvider
    tp := trace.NewTracerProvider(
        // Resource
        trace.WithResource(res),
        
        // Sampler
        trace.WithSampler(trace.AlwaysSample()),
        
        // SpanProcessor (批处理)
        trace.WithBatcher(exporter,
            trace.WithBatchTimeout(5*time.Second),
            trace.WithMaxExportBatchSize(512),
        ),
        
        // SpanLimits
        trace.WithSpanLimits(trace.SpanLimits{
            AttributeCountLimit:    128,
            EventCountLimit:        128,
            LinkCountLimit:         128,
            AttributeValueLengthLimit: 4096,
        }),
    )
    
    // 4. 设置全局TracerProvider
    otel.SetTracerProvider(tp)
    
    return tp, nil
}

func main() {
    tp, err := initTracer()
    if err != nil {
        panic(err)
    }
    defer tp.Shutdown(context.Background())
    
    // 使用tracer
    tracer := otel.Tracer("my-component")
    ctx, span := tracer.Start(context.Background(), "operation")
    defer span.End()
    
    // ... 业务逻辑
}
```

---

## 4. Tracer

### 4.1 职责

**Tracer职责**：

```text
1. Span创建
   - 创建新span
   - 设置span属性
   - 关联父span

2. 命名空间
   - Tracer有name和version
   - 用于标识instrumentation library

3. 配置继承
   - 继承TracerProvider配置
   - 使用全局Resource
   - 使用全局Sampler
```

### 4.2 创建Span

**SpanBuilder模式**：

```go
// 获取Tracer
tracer := otel.Tracer("my-service", trace.WithInstrumentationVersion("1.0.0"))

// 创建Span
ctx, span := tracer.Start(ctx, "operation-name",
    // SpanKind
    trace.WithSpanKind(trace.SpanKindClient),
    
    // 属性
    trace.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.String("http.url", "https://example.com"),
    ),
    
    // 时间戳 (通常自动设置)
    trace.WithTimestamp(time.Now()),
    
    // Links (关联其他trace)
    trace.WithLinks(
        trace.Link{
            SpanContext: otherSpanContext,
            Attributes: []attribute.KeyValue{
                attribute.String("link.type", "related"),
            },
        },
    ),
)
defer span.End()
```

---

## 5. Span Processor

### 5.1 SimpleSpanProcessor

**立即导出处理器**：

```text
特点:
- Span结束时立即导出
- 同步调用Exporter
- 阻塞应用线程

优点:
- 简单,无延迟
- 适合测试,调试

缺点:
- 性能差 (同步阻塞)
- 不适合生产环境

使用场景:
- 开发环境
- 单元测试
- 低流量应用
```

**配置示例**：

```go
import (
    "go.opentelemetry.io/otel/sdk/trace"
)

exporter := newExporter()
processor := trace.NewSimpleSpanProcessor(exporter)

tp := trace.NewTracerProvider(
    trace.WithSpanProcessor(processor),
)
```

### 5.2 BatchSpanProcessor

**批处理导出器**：

```text
特点:
- Span异步批量导出
- 后台线程处理
- 不阻塞应用

配置参数:
1. MaxQueueSize
   - 队列最大容量
   - 默认: 2048
   - 超过则丢弃span

2. MaxExportBatchSize
   - 单次导出最大span数
   - 默认: 512

3. BatchTimeout
   - 批处理超时
   - 默认: 5秒
   - 到时间即导出

4. ExportTimeout
   - 单次导出超时
   - 默认: 30秒

工作流程:
1. Span结束 → 加入队列
2. 队列满512 or 5秒超时 → 触发导出
3. 后台线程调用Exporter.export(batch)
4. 导出成功 → 清空批次
5. 导出失败 → 重试 (可配置)

优点:
- 高性能 (异步,批量)
- 减少网络请求
- 不阻塞应用

缺点:
- 延迟 (最多5秒)
- 可能丢失数据 (队列满,崩溃)
```

**配置示例**：

```go
exporter := newExporter()

tp := trace.NewTracerProvider(
    trace.WithBatcher(exporter,
        // 批处理超时
        trace.WithBatchTimeout(5*time.Second),
        
        // 最大批次大小
        trace.WithMaxExportBatchSize(512),
        
        // 队列大小
        trace.WithMaxQueueSize(2048),
        
        // 导出超时
        trace.WithExportTimeout(30*time.Second),
    ),
)
```

### 5.3 自定义Processor

**实现自定义Processor**：

```go
type CustomSpanProcessor struct {
    // 自定义字段
}

func (p *CustomSpanProcessor) OnStart(parent context.Context, s trace.ReadWriteSpan) {
    // Span开始时调用
    // 可以修改span属性
    s.SetAttributes(attribute.String("custom.key", "value"))
}

func (p *CustomSpanProcessor) OnEnd(s trace.ReadOnlySpan) {
    // Span结束时调用
    // 处理完成的span
    fmt.Printf("Span ended: %s, duration: %v\n", 
        s.Name(), s.EndTime().Sub(s.StartTime()))
}

func (p *CustomSpanProcessor) Shutdown(ctx context.Context) error {
    // 关闭处理器
    return nil
}

func (p *CustomSpanProcessor) ForceFlush(ctx context.Context) error {
    // 强制刷新
    return nil
}
```

---

## 6. Span Exporter

### 6.1 OTLP Exporter

**OTLP导出器配置**：

```go
import (
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
)

// gRPC Exporter
grpcExporter, err := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("localhost:4317"),
    otlptracegrpc.WithInsecure(),
    otlptracegrpc.WithTimeout(10*time.Second),
    otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
        Enabled:         true,
        InitialInterval: 1 * time.Second,
        MaxInterval:     30 * time.Second,
        MaxElapsedTime:  5 * time.Minute,
    }),
)

// HTTP Exporter
httpExporter, err := otlptracehttp.New(ctx,
    otlptracehttp.WithEndpoint("localhost:4318"),
    otlptracehttp.WithInsecure(),
    otlptracehttp.WithTimeout(10*time.Second),
    otlptracehttp.WithCompression(otlptracehttp.GzipCompression),
)
```

### 6.2 其他Exporter

**常用Exporter**：

```text
1. Jaeger Exporter
   - 导出到Jaeger
   - 支持Thrift协议

2. Zipkin Exporter
   - 导出到Zipkin
   - HTTP JSON格式

3. Console Exporter
   - 输出到控制台
   - 用于开发调试

4. File Exporter
   - 写入文件
   - JSON Lines格式

5. Prometheus Exporter (Metrics)
   - 导出指标到Prometheus
   - Pull模式

6. 云厂商Exporter
   - AWS X-Ray
   - Azure Monitor
   - GCP Cloud Trace
```

---

## 7. Sampler

### 7.1 内置采样器

**常用采样器**：

```text
1. AlwaysOn
   - 总是采样
   - sampled = true

2. AlwaysOff
   - 总是不采样
   - sampled = false

3. TraceIDRatioBased
   - 基于trace_id采样
   - 采样率: 0.0-1.0
   - 一致性: 同一trace_id总是相同决策

4. ParentBased
   - 基于父span采样决策
   - 父采样 → 子采样
   - 父不采样 → 子不采样
   - 无父span → 使用根采样器

5. 自定义采样器
   - 实现Sampler接口
   - 自定义逻辑
```

**配置示例**：

```go
import "go.opentelemetry.io/otel/sdk/trace"

// AlwaysOn
sampler := trace.AlwaysSample()

// AlwaysOff
sampler := trace.NeverSample()

// TraceIDRatioBased (10%采样率)
sampler := trace.TraceIDRatioBased(0.1)

// ParentBased (父采样则采样,否则10%采样)
sampler := trace.ParentBased(
    trace.TraceIDRatioBased(0.1),
)

tp := trace.NewTracerProvider(
    trace.WithSampler(sampler),
)
```

### 7.2 自定义采样器

**实现自定义采样器**：

```go
type ErrorSampler struct {
    baseSampler trace.Sampler
}

func (s *ErrorSampler) ShouldSample(p trace.SamplingParameters) trace.SamplingResult {
    // 总是采样错误
    for _, attr := range p.Attributes {
        if attr.Key == "error" && attr.Value.AsBool() {
            return trace.SamplingResult{
                Decision:   trace.RecordAndSample,
                Tracestate: p.ParentContext.TraceState(),
            }
        }
    }
    
    // 其他情况使用基础采样器
    return s.baseSampler.ShouldSample(p)
}

func (s *ErrorSampler) Description() string {
    return "ErrorSampler"
}
```

---

## 8. ID Generator

**ID生成器**：

```text
职责:
- 生成trace_id (16字节)
- 生成span_id (8字节)

默认实现:
- 使用crypto/rand (加密安全随机数)

自定义实现:
type CustomIDGenerator struct {}

func (g *CustomIDGenerator) NewIDs(ctx context.Context) (trace.TraceID, trace.SpanID) {
    var traceID [16]byte
    var spanID [8]byte
    
    // 自定义生成逻辑
    rand.Read(traceID[:])
    rand.Read(spanID[:])
    
    return traceID, spanID
}

func (g *CustomIDGenerator) NewSpanID(ctx context.Context, traceID trace.TraceID) trace.SpanID {
    var spanID [8]byte
    rand.Read(spanID[:])
    return spanID
}

配置:
tp := trace.NewTracerProvider(
    trace.WithIDGenerator(&CustomIDGenerator{}),
)
```

---

## 9. Resource

**Resource定义**：

```text
Resource: 描述生成追踪数据的实体

常用属性:
- service.name: 服务名称
- service.version: 服务版本
- deployment.environment: 部署环境
- host.name: 主机名
- cloud.provider: 云提供商
- k8s.pod.name: Pod名称

自动检测:
- 主机信息
- 进程信息
- 容器信息
- Kubernetes信息
```

**配置Resource**：

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

res, err := resource.New(ctx,
    // 手动设置
    resource.WithAttributes(
        semconv.ServiceNameKey.String("my-service"),
        semconv.ServiceVersionKey.String("1.0.0"),
    ),
    
    // 自动检测
    resource.WithFromEnv(),      // 从环境变量
    resource.WithHost(),          // 主机信息
    resource.WithProcess(),       // 进程信息
    resource.WithContainer(),     // 容器信息
    resource.WithOS(),            // 操作系统信息
    resource.WithProcessRuntimeName(),
    resource.WithProcessRuntimeVersion(),
    resource.WithProcessRuntimeDescription(),
)

tp := trace.NewTracerProvider(
    trace.WithResource(res),
)
```

---

## 10. Propagator

**上下文传播器**：

```text
作用:
- 跨进程传播SpanContext
- 注入: Context → HTTP头/gRPC metadata
- 提取: HTTP头/gRPC metadata → Context

标准Propagator:
1. W3C Trace Context
   - traceparent
   - tracestate

2. W3C Baggage
   - baggage

3. B3 (Zipkin)
   - X-B3-TraceId
   - X-B3-SpanId
   - X-B3-Sampled

4. Jaeger
   - uber-trace-id
```

**配置Propagator**：

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// 组合多个propagator
otel.SetTextMapPropagator(
    propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},  // W3C Trace Context
        propagation.Baggage{},       // W3C Baggage
    ),
)

// 使用
// 注入
req, _ := http.NewRequest("GET", "http://example.com", nil)
otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))

// 提取
ctx := otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
```

---

## 11. 生命周期管理

**优雅关闭**：

```go
func main() {
    // 初始化
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    
    // 确保关闭
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }()
    
    // 应用逻辑...
}
```

**Shutdown流程**：

```text
TracerProvider.Shutdown():
1. 停止接受新span
2. 调用所有Processor.ForceFlush()
   - 导出所有pending spans
3. 调用所有Processor.Shutdown()
   - 关闭Processor
4. 调用所有Exporter.Shutdown()
   - 关闭网络连接
   - 释放资源
5. 等待所有操作完成或超时
```

---

## 12. 多语言SDK实现

**SDK仓库**：

```text
Go:
https://github.com/open-telemetry/opentelemetry-go

Java:
https://github.com/open-telemetry/opentelemetry-java

Python:
https://github.com/open-telemetry/opentelemetry-python

JavaScript/TypeScript:
https://github.com/open-telemetry/opentelemetry-js

.NET:
https://github.com/open-telemetry/opentelemetry-dotnet

Rust:
https://github.com/open-telemetry/opentelemetry-rust

Ruby:
https://github.com/open-telemetry/opentelemetry-ruby

PHP:
https://github.com/open-telemetry/opentelemetry-php

C++:
https://github.com/open-telemetry/opentelemetry-cpp
```

---

## 13. 最佳实践

```text
1. TracerProvider
   ✅ 应用启动时初始化一次
   ✅ 配置合理的Resource
   ✅ 使用全局单例
   ❌ 不要每次请求创建

2. SpanProcessor
   ✅ 生产环境使用BatchSpanProcessor
   ✅ 配置合理的batch size和timeout
   ❌ 生产环境不要用SimpleSpanProcessor

3. Sampler
   ✅ 高流量应用降低采样率
   ✅ 总是采样错误
   ✅ 使用ParentBased保持一致性

4. Exporter
   ✅ 配置重试策略
   ✅ 配置合理的超时
   ✅ 使用OTLP协议

5. 关闭
   ✅ defer TracerProvider.Shutdown()
   ✅ 设置shutdown超时
   ✅ 处理shutdown错误

6. 性能
   ✅ 避免过度instrumentation
   ✅ 使用采样减少开销
   ✅ 监控SDK metrics
```

---

## 14. 参考资源

- **SDK Spec**: <https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/trace/sdk.md>
- **Go SDK**: <https://pkg.go.dev/go.opentelemetry.io/otel/sdk>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**下一步**: [02_Collector架构.md](./02_Collector架构.md)

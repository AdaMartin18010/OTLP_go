# OpenTelemetry Collector 高级配置指南（Go 1.25.1 - 2025版）

> **文档版本**: v1.0.0  
> **更新日期**: 2025-10-12  
> **Go 版本**: 1.25.1+  
> **OTel Collector 版本**: 0.92.0+  
> **技术深度**: ⭐⭐⭐⭐⭐

---

## 📋 目录

- [OpenTelemetry Collector 高级配置指南（Go 1.25.1 - 2025版）](#opentelemetry-collector-高级配置指南go-1251---2025版)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [什么是 OpenTelemetry Collector？](#什么是-opentelemetry-collector)
    - [核心特性](#核心特性)
    - [架构概览](#架构概览)
  - [OTel Collector 概述](#otel-collector-概述)
    - [部署模式](#部署模式)
      - [1. Agent 模式 (Sidecar)](#1-agent-模式-sidecar)
      - [2. Gateway 模式 (集中式)](#2-gateway-模式-集中式)
      - [3. Hybrid 模式 (混合)](#3-hybrid-模式-混合)
  - [完整集成示例](#完整集成示例)
    - [1. 基础配置](#1-基础配置)
      - [完整配置文件](#完整配置文件)
    - [2. Go 应用集成](#2-go-应用集成)
  - [高级特性](#高级特性)
    - [1. 自定义处理器](#1-自定义处理器)
    - [2. 动态采样](#2-动态采样)
    - [3. 数据转换](#3-数据转换)
    - [4. 数据聚合](#4-数据聚合)
  - [性能优化](#性能优化)
    - [1. 批处理优化](#1-批处理优化)
    - [2. 内存管理](#2-内存管理)
    - [3. 并发配置](#3-并发配置)
    - [4. 资源优化](#4-资源优化)
  - [生产部署](#生产部署)
    - [1. Kubernetes 部署 (DaemonSet)](#1-kubernetes-部署-daemonset)
    - [2. Gateway 部署 (Deployment)](#2-gateway-部署-deployment)
    - [3. HPA 自动扩缩容](#3-hpa-自动扩缩容)
  - [最佳实践](#最佳实践)
    - [1. Pipeline 设计](#1-pipeline-设计)
    - [2. 监控指标](#2-监控指标)
    - [3. 安全配置](#3-安全配置)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
    - [2. 调试工具](#2-调试工具)
  - [总结](#总结)

---

## 简介

### 什么是 OpenTelemetry Collector？

**OpenTelemetry Collector** 是一个厂商无关的代理,用于接收、处理和导出遥测数据（追踪、度量和日志）。它是可观测性数据管道的核心组件。

### 核心特性

```text
✅ 核心优势:
  - 厂商无关 (统一接口)
  - 高性能 (Golang 实现)
  - 可扩展 (插件架构)
  - 云原生 (K8s 友好)
  - 统一配置 (YAML)

✅ 支持协议:
  - OTLP (gRPC/HTTP)
  - Jaeger
  - Zipkin
  - Prometheus
  - StatsD
  - 50+ 协议

✅ 部署模式:
  - Agent (Sidecar/DaemonSet)
  - Gateway (集中式)
  - Standalone (单机)
  - Hybrid (混合)

✅ 核心组件:
  - Receivers (接收器)
  - Processors (处理器)
  - Exporters (导出器)
  - Extensions (扩展)
```

### 架构概览

```text
┌─────────────────────────────────────────────────────────┐
│              OTel Collector 架构                        │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌──────────────────────────────────────────────────┐  │
│  │              Receivers (接收器)                   │  │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌────────┐ │  │
│  │  │  OTLP   │ │ Jaeger  │ │ Zipkin  │ │ Prom   │ │  │
│  │  └────┬────┘ └────┬────┘ └────┬────┘ └───┬────┘ │  │
│  └───────┼───────────┼───────────┼──────────┼──────┘  │
│          │           │           │          │          │
│          └───────────┴───────────┴──────────┘          │
│                      │                                  │
│  ┌───────────────────▼──────────────────────────────┐  │
│  │            Processors (处理器)                     │  │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐         │  │
│  │  │  Batch   │ │ Resource │ │ Sampling │         │  │
│  │  │  Memory  │ │ Attribute│ │ Filter   │  ...    │  │
│  │  └────┬─────┘ └────┬─────┘ └────┬─────┘         │  │
│  └───────┼────────────┼────────────┼───────────────┘  │
│          │            │            │                   │
│          └────────────┴────────────┘                   │
│                      │                                  │
│  ┌───────────────────▼──────────────────────────────┐  │
│  │             Exporters (导出器)                     │  │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌────────┐ │  │
│  │  │  OTLP   │ │  Tempo  │ │  Prom   │ │  Loki  │ │  │
│  │  └─────────┘ └─────────┘ └─────────┘ └────────┘ │  │
│  └──────────────────────────────────────────────────┘  │
│                                                          │
│  ┌──────────────────────────────────────────────────┐  │
│  │            Extensions (扩展)                       │  │
│  │  ┌──────────┐ ┌──────────┐ ┌──────────┐         │  │
│  │  │ Health   │ │  PProp   │ │  Auth    │  ...    │  │
│  │  │ Check    │ │          │ │          │         │  │
│  │  └──────────┘ └──────────┘ └──────────┘         │  │
│  └──────────────────────────────────────────────────┘  │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

---

## OTel Collector 概述

### 部署模式

#### 1. Agent 模式 (Sidecar)

```text
应用容器 → OTel Collector (Sidecar) → Backend

优点:
  - 低延迟
  - 应用解耦
  - 资源隔离

缺点:
  - 资源开销大
  - 管理复杂
```

#### 2. Gateway 模式 (集中式)

```text
应用 → OTel Collector (Gateway) → Backend
      ↑
应用 → 

优点:
  - 集中管理
  - 资源节省
  - 统一处理

缺点:
  - 单点故障
  - 网络跳转
```

#### 3. Hybrid 模式 (混合)

```text
应用 → Agent → Gateway → Backend

优点:
  - 低延迟 + 集中处理
  - 灵活配置
  - 负载均衡

推荐: 生产环境使用
```

---

## 完整集成示例

### 1. 基础配置

#### 完整配置文件

```yaml
# otel-collector-config.yaml
receivers:
  # OTLP 接收器 (gRPC + HTTP)
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 16
        max_concurrent_streams: 100
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - "http://*"
            - "https://*"
  
  # Prometheus 接收器
  prometheus:
    config:
      scrape_configs:
        - job_name: 'otel-collector'
          scrape_interval: 30s
          static_configs:
            - targets: ['localhost:8888']
  
  # Jaeger 接收器
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
      thrift_http:
        endpoint: 0.0.0.0:14268
  
  # Zipkin 接收器
  zipkin:
    endpoint: 0.0.0.0:9411

processors:
  # 批处理器 (必需)
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  # 内存限制器 (推荐)
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  # 资源检测器
  resourcedetection:
    detectors: [env, system, docker]
    timeout: 5s
    override: false
  
  # 属性处理器
  attributes:
    actions:
      - key: environment
        value: production
        action: insert
      - key: team
        value: platform
        action: insert
      - key: sensitive_data
        action: delete
  
  # 采样处理器
  probabilistic_sampler:
    sampling_percentage: 10.0
  
  # 过滤器
  filter:
    traces:
      span:
        - 'attributes["http.status_code"] >= 400'
        - 'attributes["error"] == true'
    metrics:
      metric:
        - 'name == "unwanted_metric"'
  
  # Span 处理器
  span:
    name:
      to_attributes:
        rules:
          - ^/api/v1/users/(.*)$
          - ^/api/v1/orders/(.*)$

exporters:
  # OTLP 导出器 (Tempo)
  otlp/tempo:
    endpoint: tempo:4317
    tls:
      insecure: true
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
  
  # Prometheus Remote Write
  prometheusremotewrite:
    endpoint: http://victoriametrics:8428/api/v1/write
    tls:
      insecure: true
    resource_to_telemetry_conversion:
      enabled: true
  
  # Loki
  loki:
    endpoint: http://loki:3100/loki/api/v1/push
    tls:
      insecure: true
  
  # 日志输出 (调试用)
  logging:
    loglevel: info
    sampling_initial: 5
    sampling_thereafter: 200
  
  # 文件导出 (备份)
  file:
    path: /var/log/otel/traces.json
    rotation:
      max_megabytes: 100
      max_days: 3
      max_backups: 3

extensions:
  # 健康检查
  health_check:
    endpoint: 0.0.0.0:13133
  
  # PProfendpoint
  pprof:
    endpoint: 0.0.0.0:1777
  
  # zPages
  zpages:
    endpoint: 0.0.0.0:55679

service:
  extensions: [health_check, pprof, zpages]
  
  pipelines:
    # 追踪管道
    traces:
      receivers: [otlp, jaeger, zipkin]
      processors: [memory_limiter, batch, resourcedetection, attributes, probabilistic_sampler]
      exporters: [otlp/tempo, logging]
    
    # 度量管道
    metrics:
      receivers: [otlp, prometheus]
      processors: [memory_limiter, batch, resourcedetection, attributes]
      exporters: [prometheusremotewrite, logging]
    
    # 日志管道
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch, resourcedetection, attributes]
      exporters: [loki, logging]
  
  telemetry:
    logs:
      level: info
      development: false
      encoding: json
    metrics:
      level: detailed
      address: 0.0.0.0:8888
```

### 2. Go 应用集成

```go
package main

import (
    "context"
    "fmt"
    "log"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

// OTelConfig OTel Collector 配置
type OTelConfig struct {
    CollectorEndpoint string
    ServiceName       string
    ServiceVersion    string
    Environment       string
}

// DefaultOTelConfig 默认配置
func DefaultOTelConfig() *OTelConfig {
    return &OTelConfig{
        CollectorEndpoint: "localhost:4317",
        ServiceName:       "my-service",
        ServiceVersion:    "1.0.0",
        Environment:       "production",
    }
}

// InitOTel 初始化 OpenTelemetry
func InitOTel(ctx context.Context, cfg *OTelConfig) (func(context.Context) error, error) {
    if cfg == nil {
        cfg = DefaultOTelConfig()
    }

    // 1. 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(cfg.ServiceName),
            semconv.ServiceVersion(cfg.ServiceVersion),
            semconv.DeploymentEnvironment(cfg.Environment),
        ),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create resource: %w", err)
    }

    // 2. 配置 gRPC 连接
    conn, err := grpc.DialContext(ctx, cfg.CollectorEndpoint,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithBlock(),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create gRPC connection: %w", err)
    }

    // 3. 创建追踪导出器
    traceExporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithGRPCConn(conn),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create trace exporter: %w", err)
    }

    // 4. 创建追踪提供者
    tracerProvider := trace.NewTracerProvider(
        trace.WithBatcher(traceExporter),
        trace.WithResource(res),
        trace.WithSampler(trace.AlwaysSample()),
    )
    otel.SetTracerProvider(tracerProvider)

    // 5. 创建度量导出器
    metricExporter, err := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithGRPCConn(conn),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create metric exporter: %w", err)
    }

    // 6. 创建度量提供者
    meterProvider := metric.NewMeterProvider(
        metric.WithReader(metric.NewPeriodicReader(metricExporter,
            metric.WithInterval(30*time.Second),
        )),
        metric.WithResource(res),
    )
    otel.SetMeterProvider(meterProvider)

    // 7. 设置传播器
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    // 8. 返回关闭函数
    cleanup := func(ctx context.Context) error {
        var errors []error

        if err := tracerProvider.Shutdown(ctx); err != nil {
            errors = append(errors, fmt.Errorf("trace provider shutdown: %w", err))
        }

        if err := meterProvider.Shutdown(ctx); err != nil {
            errors = append(errors, fmt.Errorf("meter provider shutdown: %w", err))
        }

        if len(errors) > 0 {
            return fmt.Errorf("shutdown errors: %v", errors)
        }

        return nil
    }

    return cleanup, nil
}

func main() {
    ctx := context.Background()

    // 初始化 OTel
    cleanup, err := InitOTel(ctx, &OTelConfig{
        CollectorEndpoint: "localhost:4317",
        ServiceName:       "demo-app",
        ServiceVersion:    "1.0.0",
        Environment:       "production",
    })
    if err != nil {
        log.Fatalf("Failed to initialize OTel: %v", err)
    }
    defer cleanup(ctx)

    // 使用追踪
    tracer := otel.Tracer("example")
    ctx, span := tracer.Start(ctx, "main-operation")
    defer span.End()

    // 模拟业务逻辑
    time.Sleep(100 * time.Millisecond)

    log.Println("Application completed")
}
```

---

## 高级特性

### 1. 自定义处理器

```go
package processor

import (
    "context"
    "fmt"

    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/consumer"
    "go.opentelemetry.io/collector/pdata/ptrace"
    "go.opentelemetry.io/collector/processor"
)

// CustomProcessor 自定义处理器
type CustomProcessor struct {
    config   *Config
    nextConsumer consumer.Traces
}

// Config 处理器配置
type Config struct {
    Attribute string `mapstructure:"attribute"`
    Value     string `mapstructure:"value"`
}

// NewCustomProcessor 创建自定义处理器
func NewCustomProcessor(
    ctx context.Context,
    set processor.CreateSettings,
    cfg component.Config,
    nextConsumer consumer.Traces,
) (processor.Traces, error) {
    processorCfg := cfg.(*Config)

    return &CustomProcessor{
        config:       processorCfg,
        nextConsumer: nextConsumer,
    }, nil
}

// Capabilities 返回处理器能力
func (p *CustomProcessor) Capabilities() consumer.Capabilities {
    return consumer.Capabilities{MutatesData: true}
}

// Start 启动处理器
func (p *CustomProcessor) Start(ctx context.Context, host component.Host) error {
    return nil
}

// Shutdown 关闭处理器
func (p *CustomProcessor) Shutdown(ctx context.Context) error {
    return nil
}

// ConsumeTraces 处理追踪数据
func (p *CustomProcessor) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // 遍历所有资源
    for i := 0; i < td.ResourceSpans().Len(); i++ {
        rs := td.ResourceSpans().At(i)

        // 遍历所有 scope
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)

            // 遍历所有 span
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)

                // 添加自定义属性
                span.Attributes().PutStr(p.config.Attribute, p.config.Value)

                // 过滤逻辑示例
                if span.Status().Code() == ptrace.StatusCodeError {
                    // 标记错误 span
                    span.Attributes().PutBool("has_error", true)
                }
            }
        }
    }

    // 传递给下一个消费者
    return p.nextConsumer.ConsumeTraces(ctx, td)
}
```

### 2. 动态采样

```yaml
# connector-config.yaml
processors:
  # Tail 采样 (基于整个追踪的采样)
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 1000
    policies:
      # 策略 1: 所有错误追踪
      - name: error-traces
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 策略 2: 慢追踪 (>1s)
      - name: slow-traces
        type: latency
        latency:
          threshold_ms: 1000
      
      # 策略 3: 特定服务
      - name: critical-service
        type: string_attribute
        string_attribute:
          key: service.name
          values: [payment-service, auth-service]
      
      # 策略 4: 概率采样 (10%)
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
      
      # 策略 5: 复合条件
      - name: complex-rule
        type: composite
        composite:
          max_total_spans_per_second: 1000
          policy_order: [error-traces, slow-traces, critical-service]
          composite_sub_policy:
            - name: high-value
              type: and
              and:
                and_sub_policy:
                  - name: http-post
                    type: string_attribute
                    string_attribute:
                      key: http.method
                      values: [POST, PUT]
                  - name: important-path
                    type: string_attribute
                    string_attribute:
                      key: http.target
                      values: [/api/orders, /api/payments]

  # 动态采样率调整
  adaptive_sampling:
    target_spans_per_second: 10000
    adjustment_interval: 60s
    sampling_percentage:
      initial: 100
      min: 1
      max: 100
```

### 3. 数据转换

```yaml
processors:
  # Transform 处理器 (OTTL语言)
  transform:
    error_mode: ignore
    
    # 追踪转换
    trace_statements:
      - context: span
        statements:
          # 重命名属性
          - set(attributes["http.method"], attributes["method"]) where attributes["method"] != nil
          - delete_key(attributes, "method")
          
          # 规范化URL (去除查询参数)
          - set(attributes["http.url"], Split(attributes["http.url"], "?")[0])
          
          # 添加计算属性
          - set(attributes["duration_seconds"], (end_time - start_time) / 1000000000)
          
          # 条件过滤
          - set(attributes["is_slow"], true) where attributes["duration_seconds"] > 1.0
          
          # Span 名称规范化
          - set(name, Concat(["HTTP ", attributes["http.method"], " ", attributes["http.route"]]))
      
      - context: resource
        statements:
          # 添加资源属性
          - set(attributes["deployment.environment"], "production")
          - set(attributes["cloud.provider"], "aws")
    
    # 度量转换
    metric_statements:
      - context: metric
        statements:
          # 重命名度量
          - set(name, "http_requests") where name == "http.requests"
          
          # 单位转换
          - set(unit, "s") where unit == "ms"
    
    # 日志转换
    log_statements:
      - context: log
        statements:
          # 解析 JSON
          - merge_maps(attributes, ParseJSON(body), "insert")
          
          # 提取字段
          - set(severity_text, attributes["level"])
          - set(attributes["message"], body)
```

### 4. 数据聚合

```yaml
# connectors (连接器) - 在管道间传递数据
connectors:
  # Span Metrics Connector (从追踪生成度量)
  spanmetrics:
    dimensions:
      - name: http.method
      - name: http.status_code
      - name: service.name
    
    histogram:
      explicit:
        buckets: [0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10]
    
    metrics_expiration: 5m
    
    # 生成的度量
    # - calls (counter)
    # - duration (histogram)
  
  # Count Connector (计数聚合)
  count:
    spans:
      http.server.duration:
        description: HTTP request duration
        conditions:
          - 'attributes["http.method"] == "GET"'
          - 'attributes["http.status_code"] < 400'

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [spanmetrics, otlp/tempo]
    
    # 从追踪生成的度量管道
    metrics/from_traces:
      receivers: [spanmetrics]
      processors: [batch]
      exporters: [prometheusremotewrite]
```

---

## 性能优化

### 1. 批处理优化

```yaml
processors:
  batch:
    # 批处理大小
    send_batch_size: 10000
    send_batch_max_size: 11000
    
    # 超时设置
    timeout: 10s
    
    # 元数据键 (用于分批)
    metadata_keys:
      - tenant_id
      - service_name
    
    # 元数据基数限制
    metadata_cardinality_limit: 1000

# 高吞吐量配置
  batch/high_throughput:
    send_batch_size: 50000
    send_batch_max_size: 60000
    timeout: 5s
```

### 2. 内存管理

```yaml
processors:
  memory_limiter:
    # 检查间隔
    check_interval: 1s
    
    # 内存限制
    limit_mib: 2048      # 硬限制
    spike_limit_mib: 512 # 软限制
    
    # 限制百分比 (替代 MiB)
    limit_percentage: 75
    spike_limit_percentage: 20

# 配置 Go GC
service:
  telemetry:
    metrics:
      level: detailed
    
    # Go runtime 参数
    resource:
      GOGC: 80  # GC 触发百分比
      GOMEMLIMIT: 2GiB  # 内存软限制
```

### 3. 并发配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        # 最大并发流
        max_concurrent_streams: 1000
        # 最大接收消息大小
        max_recv_msg_size_mib: 32
        # 读写超时
        read_buffer_size: 524288
        write_buffer_size: 524288

exporters:
  otlp/tempo:
    endpoint: tempo:4317
    # 发送队列
    sending_queue:
      enabled: true
      num_consumers: 50      # 并发消费者数
      queue_size: 10000      # 队列大小
      storage: file_storage  # 持久化队列
    
    # 重试配置
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    
    # 超时配置
    timeout: 30s

extensions:
  # 文件存储 (持久化队列)
  file_storage:
    directory: /var/lib/otelcol/file_storage
    timeout: 1s
    compaction:
      on_start: true
      on_rebound: true
      directory: /var/lib/otelcol/file_storage/compaction
```

### 4. 资源优化

```yaml
# Kubernetes 资源配置
resources:
  requests:
    memory: "2Gi"
    cpu: "1000m"
  limits:
    memory: "4Gi"
    cpu: "2000m"

# 环境变量
env:
  # Go runtime
  - name: GOGC
    value: "80"
  - name: GOMEMLIMIT
    value: "3GiB"
  
  # OTel Collector
  - name: OTEL_RESOURCE_ATTRIBUTES
    value: "service.name=otel-collector,deployment.environment=production"
```

---

## 生产部署

### 1. Kubernetes 部署 (DaemonSet)

```yaml
# otel-collector-daemonset.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: observability
data:
  otel-collector-config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
    
    processors:
      memory_limiter:
        limit_mib: 512
        spike_limit_mib: 128
        check_interval: 1s
      
      batch:
        send_batch_size: 1024
        timeout: 10s
      
      resourcedetection:
        detectors: [env, system, docker, kubernetes]
    
    exporters:
      otlp:
        endpoint: otel-collector-gateway:4317
        tls:
          insecure: true
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, resourcedetection, batch]
          exporters: [otlp]

---
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector-agent
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
      component: agent
  template:
    metadata:
      labels:
        app: otel-collector
        component: agent
    spec:
      serviceAccountName: otel-collector
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.92.0
        args:
          - "--config=/conf/otel-collector-config.yaml"
        ports:
        - containerPort: 4317  # OTLP gRPC
          name: otlp-grpc
          protocol: TCP
        - containerPort: 4318  # OTLP HTTP
          name: otlp-http
          protocol: TCP
        - containerPort: 8888  # Metrics
          name: metrics
          protocol: TCP
        volumeMounts:
        - name: config
          mountPath: /conf
        resources:
          requests:
            memory: "512Mi"
            cpu: "200m"
          limits:
            memory: "1Gi"
            cpu: "500m"
        env:
        - name: POD_IP
          valueFrom:
            fieldRef:
              fieldPath: status.podIP
        - name: KUBE_NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
      volumes:
      - name: config
        configMap:
          name: otel-collector-config

---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector-agent
  namespace: observability
spec:
  type: ClusterIP
  clusterIP: None
  selector:
    app: otel-collector
    component: agent
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
```

### 2. Gateway 部署 (Deployment)

```yaml
# otel-collector-gateway.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-gateway-config
  namespace: observability
data:
  otel-collector-config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
    
    processors:
      memory_limiter:
        limit_mib: 2048
        spike_limit_mib: 512
        check_interval: 1s
      
      batch:
        send_batch_size: 10000
        send_batch_max_size: 11000
        timeout: 10s
      
      attributes:
        actions:
          - key: environment
            value: production
            action: insert
    
    exporters:
      otlp/tempo:
        endpoint: tempo:4317
        tls:
          insecure: true
      
      prometheusremotewrite:
        endpoint: http://victoriametrics:8428/api/v1/write
        tls:
          insecure: true
      
      loki:
        endpoint: http://loki:3100/loki/api/v1/push
        tls:
          insecure: true
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, batch, attributes]
          exporters: [otlp/tempo]
        
        metrics:
          receivers: [otlp]
          processors: [memory_limiter, batch, attributes]
          exporters: [prometheusremotewrite]
        
        logs:
          receivers: [otlp]
          processors: [memory_limiter, batch, attributes]
          exporters: [loki]

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector-gateway
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otel-collector
      component: gateway
  template:
    metadata:
      labels:
        app: otel-collector
        component: gateway
    spec:
      serviceAccountName: otel-collector
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.92.0
        args:
          - "--config=/conf/otel-collector-config.yaml"
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        - containerPort: 8888
          name: metrics
        volumeMounts:
        - name: config
          mountPath: /conf
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
        livenessProbe:
          httpGet:
            path: /
            port: 13133
        readinessProbe:
          httpGet:
            path: /
            port: 13133
      volumes:
      - name: config
        configMap:
          name: otel-collector-gateway-config

---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector-gateway
  namespace: observability
spec:
  type: LoadBalancer
  selector:
    app: otel-collector
    component: gateway
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
```

### 3. HPA 自动扩缩容

```yaml
# hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-gateway-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector-gateway
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  - type: Pods
    pods:
      metric:
        name: otelcol_receiver_accepted_spans
      target:
        type: AverageValue
        averageValue: "10000"
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60
```

---

## 最佳实践

### 1. Pipeline 设计

```text
✅ 推荐的 Pipeline 顺序:

1. memory_limiter     (最高优先级,防止 OOM)
2. batch              (批处理,提高效率)
3. resourcedetection  (资源检测)
4. attributes         (属性处理)
5. filter/sampling    (过滤/采样)
6. transform          (数据转换)

示例:
processors: [memory_limiter, batch, resourcedetection, attributes, tail_sampling, transform]
```

### 2. 监控指标

```yaml
# 关键指标
- otelcol_receiver_accepted_spans
- otelcol_receiver_refused_spans
- otelcol_exporter_sent_spans
- otelcol_exporter_send_failed_spans
- otelcol_processor_batch_batch_send_size
- otelcol_processor_batch_timeout_trigger_send

# Prometheus 告警规则
groups:
  - name: otel_collector
    rules:
      - alert: HighSpanDropRate
        expr: rate(otelcol_receiver_refused_spans[5m]) > 100
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "OTel Collector high span drop rate"
      
      - alert: ExporterFailures
        expr: rate(otelcol_exporter_send_failed_spans[5m]) > 10
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "OTel Collector exporter failures"
```

### 3. 安全配置

```yaml
# TLS 配置
exporters:
  otlp/secure:
    endpoint: backend:4317
    tls:
      insecure: false
      ca_file: /etc/otel/ca.crt
      cert_file: /etc/otel/client.crt
      key_file: /etc/otel/client.key
      min_version: "1.3"

# 认证扩展
extensions:
  # Bearer Token
  bearertokenauth:
    token: "your-secret-token"
  
  # Basic Auth
  basicauth/client:
    client_auth:
      username: admin
      password: secretpassword
  
  # OAuth2
  oauth2client:
    client_id: otel-collector
    client_secret: secret
    token_url: https://auth.example.com/token

exporters:
  otlp/authenticated:
    endpoint: backend:4317
    auth:
      authenticator: bearertokenauth
```

---

## 故障排查

### 1. 常见问题

```text
问题 1: Collector 启动失败
排查:
  1. 检查配置文件语法
  2. 验证端口未被占用
  3. 检查权限和文件路径
  4. 查看启动日志

命令:
  otelcol --config config.yaml --dry-run
  otelcol validate --config config.yaml

问题 2: 数据丢失
排查:
  1. 检查 memory_limiter 配置
  2. 查看拒绝的 span 数量
  3. 检查导出器状态
  4. 验证网络连接

指标:
  otelcol_receiver_refused_spans
  otelcol_exporter_send_failed_spans

问题 3: 高内存使用
排查:
  1. 减小批处理大小
  2. 降低队列大小
  3. 启用 memory_limiter
  4. 调整 GOGC

问题 4: 性能瓶颈
排查:
  1. 启用 pprof 分析
  2. 检查处理器顺序
  3. 优化批处理配置
  4. 增加并发数
```

### 2. 调试工具

```yaml
# 启用调试
extensions:
  # Health Check
  health_check:
    endpoint: :13133
    path: /health
  
  # pprof
  pprof:
    endpoint: :1777
  
  # zPages
  zpages:
    endpoint: :55679

# 详细日志
service:
  telemetry:
    logs:
      level: debug
      development: true
      encoding: console
      output_paths:
        - stdout
        - /var/log/otel/collector.log

# 使用 logging exporter
exporters:
  logging:
    loglevel: debug
    sampling_initial: 100
    sampling_thereafter: 100
```

---

## 总结

```text
✅ OTel Collector 优势:
  - 厂商无关 (统一接口)
  - 高性能 (Go 实现)
  - 可扩展 (插件架构)
  - 功能丰富 (50+ 组件)

✅ 部署建议:
  - 生产环境: Hybrid 模式 (Agent + Gateway)
  - Agent: DaemonSet,低资源配置
  - Gateway: Deployment + HPA,高可用

✅ 配置要点:
  1. memory_limiter 必须启用
  2. batch 处理器优化吞吐量
  3. 合理的重试和队列配置
  4. 监控 Collector 自身指标

✅ 性能优化:
  - 批处理大小: 10000+
  - 并发消费者: 50+
  - 持久化队列: file_storage
  - 内存限制: GOMEMLIMIT

✅ 最佳实践:
  - 按环境分离配置
  - 启用健康检查
  - 配置告警规则
  - 定期更新版本
```

---

**更新时间**: 2025-10-12  
**文档版本**: v1.0.0  
**维护团队**: OTLP Go Integration Team

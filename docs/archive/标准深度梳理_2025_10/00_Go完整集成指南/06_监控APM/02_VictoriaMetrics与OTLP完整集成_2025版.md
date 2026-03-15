# VictoriaMetrics 与 OTLP 完整集成指南（Go 1.25.1 - 2025版）

> **文档版本**: v1.0.0  
> **更新日期**: 2025-10-12  
> **Go 版本**: 1.25.1+  
> **VictoriaMetrics 版本**: 1.96.0+  
> **技术深度**: ⭐⭐⭐⭐⭐

---

## 📋 目录

- [VictoriaMetrics 与 OTLP 完整集成指南（Go 1.25.1 - 2025版）](#victoriametrics-与-otlp-完整集成指南go-1251---2025版)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [什么是 VictoriaMetrics？](#什么是-victoriametrics)
    - [核心特性](#核心特性)
    - [与其他方案对比](#与其他方案对比)
  - [VictoriaMetrics 概述](#victoriametrics-概述)
    - [架构设计](#架构设计)
      - [单机版架构](#单机版架构)
      - [集群版架构](#集群版架构)
    - [数据模型](#数据模型)
  - [完整集成示例](#完整集成示例)
    - [1. 基础配置](#1-基础配置)
      - [go.mod 依赖](#gomod-依赖)
    - [2. OTLP Metrics + Prometheus Exporter](#2-otlp-metrics--prometheus-exporter)
    - [3. 应用度量示例](#3-应用度量示例)
    - [4. 自定义度量示例](#4-自定义度量示例)
  - [高级特性](#高级特性)
    - [1. VictoriaMetrics 原生客户端](#1-victoriametrics-原生客户端)
    - [2. MetricsQL 高级查询](#2-metricsql-高级查询)
      - [Go 中使用 MetricsQL](#go-中使用-metricsql)
    - [3. vmagent 配置](#3-vmagent-配置)
  - [性能优化](#性能优化)
    - [1. 度量聚合](#1-度量聚合)
    - [2. 标签优化](#2-标签优化)
    - [3. 采样策略](#3-采样策略)
  - [生产部署](#生产部署)
    - [1. Docker Compose 部署](#1-docker-compose-部署)
      - [Grafana 数据源配置](#grafana-数据源配置)
    - [2. Kubernetes 部署](#2-kubernetes-部署)
    - [3. 告警规则](#3-告警规则)
  - [最佳实践](#最佳实践)
    - [1. 度量命名规范](#1-度量命名规范)
    - [2. 基数控制](#2-基数控制)
    - [3. 度量聚合](#3-度量聚合)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
    - [2. 监控 VictoriaMetrics 自身](#2-监控-victoriametrics-自身)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [性能基准](#性能基准)
    - [下一步](#下一步)

---

## 简介

### 什么是 VictoriaMetrics？

**VictoriaMetrics** 是一个快速、低成本、高度可扩展的时序数据库和监控解决方案。
它完全兼容 Prometheus，但性能更高、资源消耗更低。

### 核心特性

```text
✅ 核心优势:
  - 高性能 (比 Prometheus 快 20x)
  - 低资源消耗 (内存/磁盘)
  - 完全兼容 Prometheus
  - 长期存储 (年级保留)
  - 多租户支持

✅ 性能指标:
  - 写入吞吐量: 1M+ datapoints/s per CPU core
  - 查询性能: 比 Prometheus 快 5-10x
  - 压缩比: 10:1 (相比原始数据)
  - 内存使用: 比 Prometheus 低 7x

✅ 集成能力:
  - Prometheus remote_write
  - InfluxDB line protocol
  - Graphite protocol
  - OpenTSDB protocol
  - OTLP metrics (实验性)

✅ 部署模式:
  - 单机版 (victoria-metrics)
  - 集群版 (vmstorage/vminsert/vmselect)
  - Prometheus Agent Mode
```

### 与其他方案对比

| 特性 | VictoriaMetrics | Prometheus | Thanos | Cortex |
|------|-----------------|------------|--------|--------|
| 性能 | 极高 | 高 | 中 | 高 |
| 资源消耗 | 极低 | 中 | 高 | 高 |
| 长期存储 | 原生支持 | 需要扩展 | 支持 | 支持 |
| 多租户 | 支持 | 不支持 | 支持 | 支持 |
| 运维复杂度 | 低 | 低 | 高 | 高 |
| PromQL兼容 | 100% | 100% | 100% | 100% |
| 成本 | 极低 | 中 | 高 | 高 |

---

## VictoriaMetrics 概述

### 架构设计

#### 单机版架构

```text
┌─────────────────────────────────────────────────────────┐
│            VictoriaMetrics 单机版架构                     │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│  │  Prometheus  │  │   App with   │  │    vmagent   │ │
│  │ remote_write │  │  OTLP metrics│  │  (scraper)   │ │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘ │
│         │                 │                 │          │
│         └─────────────────┼─────────────────┘          │
│                           │                             │
│                  ┌────────▼────────┐                    │
│                  │ victoria-metrics│                    │
│                  │  (single-node)  │                    │
│                  └────────┬────────┘                    │
│                           │                             │
│                  ┌────────▼────────┐                    │
│                  │  Storage Engine │                    │
│                  │  (compression)  │                    │
│                  └────────┬────────┘                    │
│                           │                             │
│                  ┌────────▼────────┐                    │
│                  │   Query API     │                    │
│                  │  (PromQL/HTTP)  │                    │
│                  └────────┬────────┘                    │
│                           │                             │
│                  ┌────────▼────────┐                    │
│                  │     Grafana     │                    │
│                  │  (Visualization)│                    │
│                  └─────────────────┘                    │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

#### 集群版架构

```text
┌─────────────────────────────────────────────────────────┐
│            VictoriaMetrics 集群版架构                     │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐             │
│  │ Producer │  │ Producer │  │ Producer │             │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘             │
│       │             │             │                     │
│       └─────────────┼─────────────┘                     │
│                     │                                    │
│            ┌────────▼────────┐                          │
│            │    vminsert     │  (写入路由)              │
│            │  (replication:2)│                          │
│            └────────┬────────┘                          │
│                     │                                    │
│       ┌─────────────┼─────────────┐                     │
│       │             │             │                     │
│  ┌────▼────┐  ┌────▼────┐  ┌────▼────┐                │
│  │vmstorage│  │vmstorage│  │vmstorage│  (数据存储)     │
│  │ Node 1  │  │ Node 2  │  │ Node 3  │                │
│  └────┬────┘  └────┬────┘  └────┬────┘                │
│       │             │             │                     │
│       └─────────────┼─────────────┘                     │
│                     │                                    │
│            ┌────────▼────────┐                          │
│            │    vmselect     │  (查询聚合)              │
│            │   (caching)     │                          │
│            └────────┬────────┘                          │
│                     │                                    │
│            ┌────────▼────────┐                          │
│            │     Grafana     │                          │
│            └─────────────────┘                          │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

### 数据模型

VictoriaMetrics 使用与 Prometheus 相同的数据模型：

```text
metric_name{label1="value1", label2="value2"} value timestamp

示例:
http_requests_total{method="GET", status="200", service="api"} 1234 1672531200
```

---

## 完整集成示例

### 1. 基础配置

#### go.mod 依赖

```go
module github.com/example/vm-integration

go 1.25.1

require (
    github.com/VictoriaMetrics/metrics v1.24.0
    go.opentelemetry.io/otel v1.24.0
    go.opentelemetry.io/otel/exporters/prometheus v0.46.0
    go.opentelemetry.io/otel/metric v1.24.0
    go.opentelemetry.io/otel/sdk/metric v1.24.0
    github.com/prometheus/client_golang v1.18.0
)
```

### 2. OTLP Metrics + Prometheus Exporter

```go
package vm

import (
    "context"
    "fmt"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/prometheus"
    "go.opentelemetry.io/otel/metric"
    sdkmetric "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// VMConfig VictoriaMetrics 配置
type VMConfig struct {
    ServiceName    string
    ServiceVersion string
    Environment    string
    MetricsPath    string
    MetricsPort    int
}

// DefaultVMConfig 默认配置
func DefaultVMConfig() *VMConfig {
    return &VMConfig{
        ServiceName:    "my-service",
        ServiceVersion: "1.0.0",
        Environment:    "production",
        MetricsPath:    "/metrics",
        MetricsPort:    9090,
    }
}

// VMExporter VictoriaMetrics 导出器
type VMExporter struct {
    config         *VMConfig
    meterProvider  *sdkmetric.MeterProvider
    promExporter   *prometheus.Exporter
    server         *http.Server
}

// NewVMExporter 创建 VictoriaMetrics 导出器
func NewVMExporter(ctx context.Context, cfg *VMConfig) (*VMExporter, error) {
    if cfg == nil {
        cfg = DefaultVMConfig()
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

    // 2. 创建 Prometheus Exporter
    promExporter, err := prometheus.New()
    if err != nil {
        return nil, fmt.Errorf("failed to create prometheus exporter: %w", err)
    }

    // 3. 创建 MeterProvider
    meterProvider := sdkmetric.NewMeterProvider(
        sdkmetric.WithResource(res),
        sdkmetric.WithReader(promExporter),
    )

    // 4. 设置全局 MeterProvider
    otel.SetMeterProvider(meterProvider)

    // 5. 创建 HTTP 服务器
    mux := http.NewServeMux()
    mux.Handle(cfg.MetricsPath, promExporter)
    
    server := &http.Server{
        Addr:    fmt.Sprintf(":%d", cfg.MetricsPort),
        Handler: mux,
    }

    exporter := &VMExporter{
        config:        cfg,
        meterProvider: meterProvider,
        promExporter:  promExporter,
        server:        server,
    }

    // 6. 启动 HTTP 服务器
    go func() {
        if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
            fmt.Printf("Metrics server error: %v\n", err)
        }
    }()

    return exporter, nil
}

// Shutdown 关闭导出器
func (e *VMExporter) Shutdown(ctx context.Context) error {
    if e.meterProvider != nil {
        if err := e.meterProvider.Shutdown(ctx); err != nil {
            return fmt.Errorf("failed to shutdown meter provider: %w", err)
        }
    }
    if e.server != nil {
        if err := e.server.Shutdown(ctx); err != nil {
            return fmt.Errorf("failed to shutdown metrics server: %w", err)
        }
    }
    return nil
}

// GetMeter 获取 Meter
func (e *VMExporter) GetMeter(instrumentationName string) metric.Meter {
    return otel.Meter(instrumentationName)
}
```

### 3. 应用度量示例

```go
package main

import (
    "context"
    "fmt"
    "log"
    "math/rand"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

var meter = otel.Meter("example-app")

// AppMetrics 应用度量
type AppMetrics struct {
    // 计数器
    requestCounter   metric.Int64Counter
    errorCounter     metric.Int64Counter
    
    // 直方图
    requestDuration  metric.Float64Histogram
    payloadSize      metric.Int64Histogram
    
    // 上下线计数器
    activeUsers      metric.Int64UpDownCounter
    
    // 异步 Gauge
    memoryUsage      metric.Int64ObservableGauge
    cpuUsage         metric.Float64ObservableGauge
}

// NewAppMetrics 创建应用度量
func NewAppMetrics() (*AppMetrics, error) {
    // 1. 计数器 - 请求总数
    requestCounter, err := meter.Int64Counter(
        "http_requests_total",
        metric.WithDescription("Total number of HTTP requests"),
        metric.WithUnit("{requests}"),
    )
    if err != nil {
        return nil, err
    }

    // 2. 计数器 - 错误总数
    errorCounter, err := meter.Int64Counter(
        "http_errors_total",
        metric.WithDescription("Total number of HTTP errors"),
        metric.WithUnit("{errors}"),
    )
    if err != nil {
        return nil, err
    }

    // 3. 直方图 - 请求时长
    requestDuration, err := meter.Float64Histogram(
        "http_request_duration_seconds",
        metric.WithDescription("HTTP request duration in seconds"),
        metric.WithUnit("s"),
        metric.WithExplicitBucketBoundaries(0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10),
    )
    if err != nil {
        return nil, err
    }

    // 4. 直方图 - 负载大小
    payloadSize, err := meter.Int64Histogram(
        "http_request_size_bytes",
        metric.WithDescription("HTTP request size in bytes"),
        metric.WithUnit("By"),
        metric.WithExplicitBucketBoundaries(100, 1000, 10000, 100000, 1000000, 10000000),
    )
    if err != nil {
        return nil, err
    }

    // 5. 上下线计数器 - 活跃用户
    activeUsers, err := meter.Int64UpDownCounter(
        "active_users",
        metric.WithDescription("Number of active users"),
        metric.WithUnit("{users}"),
    )
    if err != nil {
        return nil, err
    }

    // 6. 异步 Gauge - 内存使用
    memoryUsage, err := meter.Int64ObservableGauge(
        "process_memory_bytes",
        metric.WithDescription("Process memory usage in bytes"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }

    // 7. 异步 Gauge - CPU 使用率
    cpuUsage, err := meter.Float64ObservableGauge(
        "process_cpu_usage",
        metric.WithDescription("Process CPU usage percentage"),
        metric.WithUnit("1"),
    )
    if err != nil {
        return nil, err
    }

    metrics := &AppMetrics{
        requestCounter:  requestCounter,
        errorCounter:    errorCounter,
        requestDuration: requestDuration,
        payloadSize:     payloadSize,
        activeUsers:     activeUsers,
        memoryUsage:     memoryUsage,
        cpuUsage:        cpuUsage,
    }

    // 注册回调函数
    if _, err := meter.RegisterCallback(
        func(ctx context.Context, observer metric.Observer) error {
            // 模拟获取系统指标
            observer.ObserveInt64(memoryUsage, int64(rand.Intn(100000000)+50000000)) // 50-150MB
            observer.ObserveFloat64(cpuUsage, rand.Float64()*100)                    // 0-100%
            return nil
        },
        memoryUsage,
        cpuUsage,
    ); err != nil {
        return nil, err
    }

    return metrics, nil
}

// RecordRequest 记录请求
func (m *AppMetrics) RecordRequest(ctx context.Context, method, path string, statusCode int, duration time.Duration, size int64) {
    attrs := []attribute.KeyValue{
        attribute.String("method", method),
        attribute.String("path", path),
        attribute.Int("status_code", statusCode),
    }

    // 记录请求计数
    m.requestCounter.Add(ctx, 1, metric.WithAttributes(attrs...))

    // 记录错误计数
    if statusCode >= 400 {
        m.errorCounter.Add(ctx, 1, metric.WithAttributes(attrs...))
    }

    // 记录请求时长
    m.requestDuration.Record(ctx, duration.Seconds(), metric.WithAttributes(attrs...))

    // 记录负载大小
    m.payloadSize.Record(ctx, size, metric.WithAttributes(attrs...))
}

// RecordUserLogin 记录用户登录
func (m *AppMetrics) RecordUserLogin(ctx context.Context) {
    m.activeUsers.Add(ctx, 1)
}

// RecordUserLogout 记录用户登出
func (m *AppMetrics) RecordUserLogout(ctx context.Context) {
    m.activeUsers.Add(ctx, -1)
}

func main() {
    ctx := context.Background()

    // 1. 初始化 VictoriaMetrics 导出器
    vmExporter, err := NewVMExporter(ctx, &VMConfig{
        ServiceName:    "demo-app",
        ServiceVersion: "1.0.0",
        Environment:    "production",
        MetricsPath:    "/metrics",
        MetricsPort:    9090,
    })
    if err != nil {
        log.Fatalf("Failed to create VM exporter: %v", err)
    }
    defer vmExporter.Shutdown(ctx)

    // 2. 创建应用度量
    appMetrics, err := NewAppMetrics()
    if err != nil {
        log.Fatalf("Failed to create app metrics: %v", err)
    }

    log.Println("Metrics server started on :9090/metrics")
    log.Println("Simulating requests...")

    // 3. 模拟请求
    for i := 0; i < 1000; i++ {
        // 模拟用户登录
        if i%10 == 0 {
            appMetrics.RecordUserLogin(ctx)
        }

        // 模拟请求
        method := []string{"GET", "POST", "PUT", "DELETE"}[rand.Intn(4)]
        path := []string{"/api/users", "/api/orders", "/api/products"}[rand.Intn(3)]
        statusCode := []int{200, 200, 200, 400, 500}[rand.Intn(5)]
        duration := time.Duration(rand.Intn(1000)) * time.Millisecond
        size := int64(rand.Intn(10000) + 100)

        appMetrics.RecordRequest(ctx, method, path, statusCode, duration, size)

        // 模拟用户登出
        if i%20 == 0 && i > 0 {
            appMetrics.RecordUserLogout(ctx)
        }

        time.Sleep(100 * time.Millisecond)
    }

    log.Println("Simulation completed. Server will continue running...")
    select {} // 保持运行
}
```

### 4. 自定义度量示例

```go
package vm

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// BusinessMetrics 业务度量
type BusinessMetrics struct {
    meter metric.Meter
    
    // 业务指标
    orderTotal        metric.Int64Counter
    orderAmount       metric.Float64Counter
    orderDuration     metric.Float64Histogram
    inventoryLevel    metric.Int64ObservableGauge
    cartSize          metric.Int64Histogram
    
    // 内部状态
    currentInventory  map[string]int64
    inventoryMu       sync.RWMutex
}

// NewBusinessMetrics 创建业务度量
func NewBusinessMetrics(instrumentationName string) (*BusinessMetrics, error) {
    meter := otel.Meter(instrumentationName)
    
    // 1. 订单总数
    orderTotal, err := meter.Int64Counter(
        "business_orders_total",
        metric.WithDescription("Total number of orders"),
        metric.WithUnit("{orders}"),
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 订单金额
    orderAmount, err := meter.Float64Counter(
        "business_order_amount_total",
        metric.WithDescription("Total order amount"),
        metric.WithUnit("USD"),
    )
    if err != nil {
        return nil, err
    }
    
    // 3. 订单处理时长
    orderDuration, err := meter.Float64Histogram(
        "business_order_duration_seconds",
        metric.WithDescription("Order processing duration"),
        metric.WithUnit("s"),
    )
    if err != nil {
        return nil, err
    }
    
    // 4. 购物车大小
    cartSize, err := meter.Int64Histogram(
        "business_cart_size",
        metric.WithDescription("Shopping cart size"),
        metric.WithUnit("{items}"),
    )
    if err != nil {
        return nil, err
    }
    
    bm := &BusinessMetrics{
        meter:            meter,
        orderTotal:       orderTotal,
        orderAmount:      orderAmount,
        orderDuration:    orderDuration,
        cartSize:         cartSize,
        currentInventory: make(map[string]int64),
    }
    
    // 5. 库存水平 (异步 Gauge)
    inventoryLevel, err := meter.Int64ObservableGauge(
        "business_inventory_level",
        metric.WithDescription("Product inventory level"),
        metric.WithUnit("{items}"),
    )
    if err != nil {
        return nil, err
    }
    bm.inventoryLevel = inventoryLevel
    
    // 注册回调
    if _, err := meter.RegisterCallback(
        func(ctx context.Context, observer metric.Observer) error {
            bm.inventoryMu.RLock()
            defer bm.inventoryMu.RUnlock()
            
            for product, level := range bm.currentInventory {
                observer.ObserveInt64(inventoryLevel, level,
                    metric.WithAttributes(attribute.String("product", product)),
                )
            }
            return nil
        },
        inventoryLevel,
    ); err != nil {
        return nil, err
    }
    
    return bm, nil
}

// RecordOrder 记录订单
func (bm *BusinessMetrics) RecordOrder(ctx context.Context, productType string, amount float64, duration time.Duration) {
    attrs := []attribute.KeyValue{
        attribute.String("product_type", productType),
    }
    
    bm.orderTotal.Add(ctx, 1, metric.WithAttributes(attrs...))
    bm.orderAmount.Add(ctx, amount, metric.WithAttributes(attrs...))
    bm.orderDuration.Record(ctx, duration.Seconds(), metric.WithAttributes(attrs...))
}

// RecordCartSize 记录购物车大小
func (bm *BusinessMetrics) RecordCartSize(ctx context.Context, size int64) {
    bm.cartSize.Record(ctx, size)
}

// UpdateInventory 更新库存
func (bm *BusinessMetrics) UpdateInventory(product string, level int64) {
    bm.inventoryMu.Lock()
    defer bm.inventoryMu.Unlock()
    bm.currentInventory[product] = level
}

// CacheMetrics 缓存度量
type CacheMetrics struct {
    hits   metric.Int64Counter
    misses metric.Int64Counter
    evictions metric.Int64Counter
    latency metric.Float64Histogram
}

// NewCacheMetrics 创建缓存度量
func NewCacheMetrics(meter metric.Meter, cacheName string) (*CacheMetrics, error) {
    attrs := []attribute.KeyValue{
        attribute.String("cache", cacheName),
    }
    
    hits, err := meter.Int64Counter(
        "cache_hits_total",
        metric.WithDescription("Cache hits"),
    )
    if err != nil {
        return nil, err
    }
    
    misses, err := meter.Int64Counter(
        "cache_misses_total",
        metric.WithDescription("Cache misses"),
    )
    if err != nil {
        return nil, err
    }
    
    evictions, err := meter.Int64Counter(
        "cache_evictions_total",
        metric.WithDescription("Cache evictions"),
    )
    if err != nil {
        return nil, err
    }
    
    latency, err := meter.Float64Histogram(
        "cache_operation_duration_seconds",
        metric.WithDescription("Cache operation duration"),
        metric.WithUnit("s"),
    )
    if err != nil {
        return nil, err
    }
    
    return &CacheMetrics{
        hits:      hits,
        misses:    misses,
        evictions: evictions,
        latency:   latency,
    }, nil
}

// RecordHit 记录缓存命中
func (cm *CacheMetrics) RecordHit(ctx context.Context, cacheName string) {
    cm.hits.Add(ctx, 1, metric.WithAttributes(attribute.String("cache", cacheName)))
}

// RecordMiss 记录缓存未命中
func (cm *CacheMetrics) RecordMiss(ctx context.Context, cacheName string) {
    cm.misses.Add(ctx, 1, metric.WithAttributes(attribute.String("cache", cacheName)))
}

// RecordEviction 记录缓存驱逐
func (cm *CacheMetrics) RecordEviction(ctx context.Context, cacheName string) {
    cm.evictions.Add(ctx, 1, metric.WithAttributes(attribute.String("cache", cacheName)))
}

// RecordLatency 记录操作延迟
func (cm *CacheMetrics) RecordLatency(ctx context.Context, cacheName, operation string, duration time.Duration) {
    cm.latency.Record(ctx, duration.Seconds(),
        metric.WithAttributes(
            attribute.String("cache", cacheName),
            attribute.String("operation", operation),
        ),
    )
}
```

---

## 高级特性

### 1. VictoriaMetrics 原生客户端

VictoriaMetrics 提供了高性能的原生 Go 客户端。

```go
package vm

import (
    "fmt"
    "net/http"

    "github.com/VictoriaMetrics/metrics"
)

// VMNativeMetrics VictoriaMetrics 原生度量
type VMNativeMetrics struct {
    // Counter
    requestCounter *metrics.Counter
    
    // Gauge
    activeConnections *metrics.Gauge
    
    // Summary (类似 Histogram)
    requestDuration *metrics.Summary
    
    // Histogram
    payloadSize *metrics.Histogram
}

// NewVMNativeMetrics 创建原生度量
func NewVMNativeMetrics() *VMNativeMetrics {
    return &VMNativeMetrics{
        requestCounter:    metrics.NewCounter(`http_requests_total{service="api"}`),
        activeConnections: metrics.NewGauge(`http_active_connections{service="api"}`, nil),
        requestDuration:   metrics.NewSummary(`http_request_duration_seconds{service="api"}`),
        payloadSize:       metrics.NewHistogram(`http_request_size_bytes{service="api"}`),
    }
}

// RecordRequest 记录请求
func (m *VMNativeMetrics) RecordRequest(statusCode int, duration float64, size uint64) {
    m.requestCounter.Inc()
    m.requestDuration.Update(duration)
    m.payloadSize.Update(float64(size))
}

// SetActiveConnections 设置活跃连接数
func (m *VMNativeMetrics) SetActiveConnections(count float64) {
    m.activeConnections.Set(count)
}

// ServeMetrics 提供度量 HTTP 端点
func ServeMetrics(addr string) error {
    http.HandleFunc("/metrics", func(w http.ResponseWriter, r *http.Request) {
        metrics.WritePrometheus(w, true)
    })
    return http.ListenAndServe(addr, nil)
}

// 使用示例
func ExampleVMNative() {
    m := NewVMNativeMetrics()
    
    // 启动度量服务器
    go ServeMetrics(":9090")
    
    // 记录度量
    m.RecordRequest(200, 0.123, 1024)
    m.SetActiveConnections(42)
}
```

### 2. MetricsQL 高级查询

MetricsQL 是 VictoriaMetrics 扩展的 PromQL，提供更多功能。

```promql
# 1. 基础查询 - 5分钟内的请求速率
rate(http_requests_total[5m])

# 2. 聚合查询 - 按服务分组的请求总数
sum(rate(http_requests_total[5m])) by (service)

# 3. 百分位查询 - P99 请求时长
histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))

# 4. 预测查询 - 预测未来 1 小时的趋势 (VictoriaMetrics 特性)
predict_linear(http_requests_total[1h], 3600)

# 5. 异常检测 - 检测突增 (VictoriaMetrics 特性)
mad(rate(http_requests_total[5m])) > 3 * mad(rate(http_requests_total[1h]))

# 6. 滚动平均 - 1小时滚动平均 (VictoriaMetrics 特性)
rollup_rate(http_requests_total[1h])

# 7. 时间范围聚合 - 过去24小时的平均值
avg_over_time(http_request_duration_seconds[24h])

# 8. 标签操作 - 删除特定标签
label_replace(http_requests_total, "env", "production", "", "")

# 9. Join 查询 - 计算错误率
sum(rate(http_errors_total[5m])) / sum(rate(http_requests_total[5m])) * 100

# 10. Subquery - 嵌套查询
max_over_time((rate(http_requests_total[5m]))[1h:5m])
```

#### Go 中使用 MetricsQL

```go
package vm

import (
    "context"
    "encoding/json"
    "fmt"
    "io"
    "net/http"
    "net/url"
    "time"
)

// VMQuerier VictoriaMetrics 查询客户端
type VMQuerier struct {
    baseURL string
    client  *http.Client
}

// NewVMQuerier 创建查询客户端
func NewVMQuerier(baseURL string) *VMQuerier {
    return &VMQuerier{
        baseURL: baseURL,
        client:  &http.Client{Timeout: 30 * time.Second},
    }
}

// QueryResult 查询结果
type QueryResult struct {
    Status string `json:"status"`
    Data   struct {
        ResultType string `json:"resultType"`
        Result     []struct {
            Metric map[string]string `json:"metric"`
            Value  []interface{}     `json:"value"`
            Values [][]interface{}   `json:"values"`
        } `json:"result"`
    } `json:"data"`
}

// Query 执行即时查询
func (q *VMQuerier) Query(ctx context.Context, query string, time time.Time) (*QueryResult, error) {
    params := url.Values{}
    params.Add("query", query)
    if !time.IsZero() {
        params.Add("time", fmt.Sprintf("%d", time.Unix()))
    }

    queryURL := fmt.Sprintf("%s/api/v1/query?%s", q.baseURL, params.Encode())
    
    req, err := http.NewRequestWithContext(ctx, "GET", queryURL, nil)
    if err != nil {
        return nil, err
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()

    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return nil, err
    }

    var result QueryResult
    if err := json.Unmarshal(body, &result); err != nil {
        return nil, err
    }

    return &result, nil
}

// QueryRange 执行范围查询
func (q *VMQuerier) QueryRange(ctx context.Context, query string, start, end time.Time, step time.Duration) (*QueryResult, error) {
    params := url.Values{}
    params.Add("query", query)
    params.Add("start", fmt.Sprintf("%d", start.Unix()))
    params.Add("end", fmt.Sprintf("%d", end.Unix()))
    params.Add("step", step.String())

    queryURL := fmt.Sprintf("%s/api/v1/query_range?%s", q.baseURL, params.Encode())
    
    req, err := http.NewRequestWithContext(ctx, "GET", queryURL, nil)
    if err != nil {
        return nil, err
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()

    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return nil, err
    }

    var result QueryResult
    if err := json.Unmarshal(body, &result); err != nil {
        return nil, err
    }

    return &result, nil
}

// 使用示例
func ExampleMetricsQL() {
    querier := NewVMQuerier("http://localhost:8428")
    ctx := context.Background()

    // 即时查询
    result, err := querier.Query(ctx, `rate(http_requests_total[5m])`, time.Now())
    if err != nil {
        fmt.Printf("Query failed: %v\n", err)
        return
    }

    fmt.Printf("Query result: %+v\n", result)

    // 范围查询
    end := time.Now()
    start := end.Add(-1 * time.Hour)
    rangeResult, err := querier.QueryRange(ctx, `http_requests_total`, start, end, 1*time.Minute)
    if err != nil {
        fmt.Printf("Range query failed: %v\n", err)
        return
    }

    fmt.Printf("Range query result: %+v\n", rangeResult)
}
```

### 3. vmagent 配置

vmagent 是 VictoriaMetrics 的高性能采集代理。

```yaml
# vmagent-config.yml
global:
  scrape_interval: 30s
  scrape_timeout: 10s
  external_labels:
    cluster: production
    dc: us-east-1

scrape_configs:
  # 采集 Go 应用
  - job_name: 'go-app'
    static_configs:
      - targets:
          - 'app-1:9090'
          - 'app-2:9090'
          - 'app-3:9090'
    relabel_configs:
      - source_labels: [__address__]
        target_label: instance
      - source_labels: [__address__]
        regex: '([^:]+):.+'
        replacement: '${1}'
        target_label: host

  # 采集 Kubernetes Pods
  - job_name: 'kubernetes-pods'
    kubernetes_sd_configs:
      - role: pod
        namespaces:
          names:
            - default
            - production
    relabel_configs:
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
        action: keep
        regex: true
      - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
        action: replace
        target_label: __metrics_path__
        regex: (.+)
      - source_labels: [__address__, __meta_kubernetes_pod_annotation_prometheus_io_port]
        action: replace
        regex: ([^:]+)(?::\d+)?;(\d+)
        replacement: $1:$2
        target_label: __address__

# Remote write 到 VictoriaMetrics
remote_write:
  - url: http://victoriametrics:8428/api/v1/write
    queue_config:
      max_samples_per_send: 10000
      max_shards: 30
      capacity: 50000
```

---

## 性能优化

### 1. 度量聚合

```go
package vm

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel/metric"
)

// MetricsAggregator 度量聚合器
type MetricsAggregator struct {
    counter  metric.Int64Counter
    buffer   map[string]int64
    mu       sync.Mutex
    interval time.Duration
    done     chan struct{}
}

// NewMetricsAggregator 创建度量聚合器
func NewMetricsAggregator(counter metric.Int64Counter, interval time.Duration) *MetricsAggregator {
    agg := &MetricsAggregator{
        counter:  counter,
        buffer:   make(map[string]int64),
        interval: interval,
        done:     make(chan struct{}),
    }
    
    go agg.flush()
    return agg
}

// Increment 增加计数 (缓冲)
func (a *MetricsAggregator) Increment(key string, value int64) {
    a.mu.Lock()
    a.buffer[key] += value
    a.mu.Unlock()
}

// flush 定期刷新
func (a *MetricsAggregator) flush() {
    ticker := time.NewTicker(a.interval)
    defer ticker.Stop()

    for {
        select {
        case <-ticker.C:
            a.mu.Lock()
            for key, value := range a.buffer {
                a.counter.Add(context.Background(), value)
                delete(a.buffer, key)
            }
            a.mu.Unlock()
        case <-a.done:
            return
        }
    }
}

// Close 关闭聚合器
func (a *MetricsAggregator) Close() {
    close(a.done)
}
```

### 2. 标签优化

```go
package vm

import (
    "go.opentelemetry.io/otel/attribute"
)

// LabelOptimizer 标签优化器
type LabelOptimizer struct {
    cache map[string][]attribute.KeyValue
}

// NewLabelOptimizer 创建标签优化器
func NewLabelOptimizer() *LabelOptimizer {
    return &LabelOptimizer{
        cache: make(map[string][]attribute.KeyValue),
    }
}

// GetAttributes 获取缓存的属性
func (lo *LabelOptimizer) GetAttributes(key string, generator func() []attribute.KeyValue) []attribute.KeyValue {
    if attrs, ok := lo.cache[key]; ok {
        return attrs
    }

    attrs := generator()
    lo.cache[key] = attrs
    return attrs
}

// 使用示例
func ExampleLabelOptimizer() {
    optimizer := NewLabelOptimizer()
    
    // 第一次调用会生成
    attrs1 := optimizer.GetAttributes("api-get", func() []attribute.KeyValue {
        return []attribute.KeyValue{
            attribute.String("method", "GET"),
            attribute.String("endpoint", "/api"),
        }
    })
    
    // 第二次调用从缓存获取
    attrs2 := optimizer.GetAttributes("api-get", nil)
    
    _ = attrs1
    _ = attrs2
}
```

### 3. 采样策略

```go
package vm

import (
    "math/rand"
    "sync/atomic"
)

// MetricsSampler 度量采样器
type MetricsSampler struct {
    rate    float64
    counter uint64
}

// NewMetricsSampler 创建采样器
func NewMetricsSampler(rate float64) *MetricsSampler {
    return &MetricsSampler{
        rate: rate,
    }
}

// ShouldSample 是否应该采样
func (s *MetricsSampler) ShouldSample() bool {
    if s.rate >= 1.0 {
        return true
    }
    return rand.Float64() < s.rate
}

// CounterSampler 计数器采样器 (每 N 个记录一次)
type CounterSampler struct {
    interval uint64
    counter  uint64
}

// NewCounterSampler 创建计数器采样器
func NewCounterSampler(interval uint64) *CounterSampler {
    return &CounterSampler{
        interval: interval,
    }
}

// ShouldSample 是否应该采样
func (cs *CounterSampler) ShouldSample() bool {
    count := atomic.AddUint64(&cs.counter, 1)
    return count%cs.interval == 0
}
```

---

## 生产部署

### 1. Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  # VictoriaMetrics 单机版
  victoriametrics:
    image: victoriametrics/victoriametrics:v1.96.0
    container_name: victoriametrics
    command:
      - '--storageDataPath=/storage'
      - '--httpListenAddr=:8428'
      - '--retentionPeriod=12'  # 12 months
      - '--maxLabelsPerTimeseries=50'
      - '--search.maxQueryDuration=30s'
    volumes:
      - vm-data:/storage
    ports:
      - "8428:8428"
    networks:
      - monitoring
    restart: unless-stopped

  # vmagent (采集代理)
  vmagent:
    image: victoriametrics/vmagent:v1.96.0
    container_name: vmagent
    command:
      - '--promscrape.config=/etc/vmagent/scrape.yml'
      - '--remoteWrite.url=http://victoriametrics:8428/api/v1/write'
      - '--remoteWrite.maxBlockSize=10MB'
      - '--remoteWrite.maxDiskUsagePerURL=10GB'
    volumes:
      - ./vmagent-config.yml:/etc/vmagent/scrape.yml
      - vmagent-data:/vmagent-data
    ports:
      - "8429:8429"
    networks:
      - monitoring
    depends_on:
      - victoriametrics
    restart: unless-stopped

  # vmalert (告警)
  vmalert:
    image: victoriametrics/vmalert:v1.96.0
    container_name: vmalert
    command:
      - '--datasource.url=http://victoriametrics:8428'
      - '--notifier.url=http://alertmanager:9093'
      - '--rule=/etc/vmalert/*.yml'
      - '--evaluationInterval=30s'
    volumes:
      - ./alert-rules.yml:/etc/vmalert/alerts.yml
    ports:
      - "8880:8880"
    networks:
      - monitoring
    depends_on:
      - victoriametrics
    restart: unless-stopped

  # Grafana
  grafana:
    image: grafana/grafana:latest
    container_name: grafana
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml
    ports:
      - "3000:3000"
    networks:
      - monitoring
    depends_on:
      - victoriametrics
    restart: unless-stopped

volumes:
  vm-data:
  vmagent-data:
  grafana-data:

networks:
  monitoring:
    driver: bridge
```

#### Grafana 数据源配置

```yaml
# grafana-datasources.yml
apiVersion: 1

datasources:
  - name: VictoriaMetrics
    type: prometheus
    access: proxy
    url: http://victoriametrics:8428
    isDefault: true
    jsonData:
      timeInterval: "30s"
      httpMethod: POST
    editable: true
```

### 2. Kubernetes 部署

```yaml
# vm-deployment.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: vm-config
  namespace: monitoring
data:
  vmagent.yml: |
    global:
      scrape_interval: 30s
    
    scrape_configs:
      - job_name: 'kubernetes-pods'
        kubernetes_sd_configs:
          - role: pod
        relabel_configs:
          - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
            action: keep
            regex: true

---
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: vm-storage
  namespace: monitoring
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 100Gi
  storageClassName: fast-ssd

---
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: victoriametrics
  namespace: monitoring
spec:
  serviceName: victoriametrics
  replicas: 1
  selector:
    matchLabels:
      app: victoriametrics
  template:
    metadata:
      labels:
        app: victoriametrics
    spec:
      containers:
      - name: victoriametrics
        image: victoriametrics/victoriametrics:v1.96.0
        args:
          - '--storageDataPath=/storage'
          - '--httpListenAddr=:8428'
          - '--retentionPeriod=12'
          - '--memory.allowedPercent=80'
        ports:
        - containerPort: 8428
          name: http
        volumeMounts:
        - name: storage
          mountPath: /storage
        resources:
          requests:
            cpu: 1000m
            memory: 2Gi
          limits:
            cpu: 2000m
            memory: 4Gi
        livenessProbe:
          httpGet:
            path: /health
            port: 8428
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 8428
          initialDelaySeconds: 10
          periodSeconds: 5
      volumes:
      - name: storage
        persistentVolumeClaim:
          claimName: vm-storage

---
apiVersion: v1
kind: Service
metadata:
  name: victoriametrics
  namespace: monitoring
spec:
  selector:
    app: victoriametrics
  ports:
  - name: http
    port: 8428
    targetPort: 8428
  type: ClusterIP

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: vmagent
  namespace: monitoring
spec:
  replicas: 2
  selector:
    matchLabels:
      app: vmagent
  template:
    metadata:
      labels:
        app: vmagent
    spec:
      serviceAccountName: vmagent
      containers:
      - name: vmagent
        image: victoriametrics/vmagent:v1.96.0
        args:
          - '--promscrape.config=/etc/vmagent/vmagent.yml'
          - '--remoteWrite.url=http://victoriametrics:8428/api/v1/write'
          - '--remoteWrite.tmpDataPath=/tmpData'
        ports:
        - containerPort: 8429
          name: http
        volumeMounts:
        - name: config
          mountPath: /etc/vmagent
        - name: tmpdata
          mountPath: /tmpData
        resources:
          requests:
            cpu: 500m
            memory: 512Mi
          limits:
            cpu: 1000m
            memory: 1Gi
      volumes:
      - name: config
        configMap:
          name: vm-config
      - name: tmpdata
        emptyDir: {}

---
apiVersion: v1
kind: ServiceAccount
metadata:
  name: vmagent
  namespace: monitoring

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: vmagent
rules:
- apiGroups: [""]
  resources:
    - nodes
    - nodes/metrics
    - services
    - endpoints
    - pods
  verbs: ["get", "list", "watch"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: vmagent
roleRef:
  apiGroup: rbac.authorization.k8s.io
  kind: ClusterRole
  name: vmagent
subjects:
- kind: ServiceAccount
  name: vmagent
  namespace: monitoring
```

### 3. 告警规则

```yaml
# alert-rules.yml
groups:
  - name: app_alerts
    interval: 30s
    rules:
      # 高错误率
      - alert: HighErrorRate
        expr: rate(http_errors_total[5m]) > 10
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }} errors/s"
      
      # 高延迟
      - alert: HighLatency
        expr: histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m])) > 1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High request latency"
          description: "P99 latency is {{ $value }}s"
      
      # 内存使用高
      - alert: HighMemoryUsage
        expr: process_memory_bytes > 2000000000  # 2GB
        for: 10m
        labels:
          severity: critical
        annotations:
          summary: "High memory usage"
          description: "Memory usage is {{ $value | humanize }}B"
      
      # 无活跃用户
      - alert: NoActiveUsers
        expr: active_users == 0
        for: 15m
        labels:
          severity: warning
        annotations:
          summary: "No active users"
          description: "No active users for 15 minutes"
```

---

## 最佳实践

### 1. 度量命名规范

```go
// 推荐的度量命名
const (
    // Counter - 以 _total 结尾
    MetricRequestsTotal = "http_requests_total"
    MetricErrorsTotal   = "http_errors_total"
    
    // Gauge - 无特定后缀
    MetricActiveConnections = "http_active_connections"
    MetricMemoryBytes       = "process_memory_bytes"
    
    // Histogram - 以 duration/size 等单位结尾
    MetricRequestDurationSeconds = "http_request_duration_seconds"
    MetricRequestSizeBytes       = "http_request_size_bytes"
    
    // Summary - 类似 Histogram
    MetricResponseTimeSeconds = "http_response_time_seconds"
)

// 标签命名规范
const (
    LabelMethod     = "method"      // HTTP method
    LabelPath       = "path"        // URL path
    LabelStatusCode = "status_code" // HTTP status code
    LabelService    = "service"     // Service name
    LabelEnvironment = "env"        // Environment
)
```

### 2. 基数控制

```go
package vm

import (
    "crypto/sha256"
    "encoding/hex"
    "fmt"
)

// CardinalityController 基数控制器
type CardinalityController struct {
    maxCardinality int
    buckets        map[string]struct{}
}

// NewCardinalityController 创建基数控制器
func NewCardinalityController(maxCardinality int) *CardinalityController {
    return &CardinalityController{
        maxCardinality: maxCardinality,
        buckets:        make(map[string]struct{}),
    }
}

// NormalizeLabel 规范化标签值
func (cc *CardinalityController) NormalizeLabel(value string) string {
    // 1. 截断过长的值
    if len(value) > 100 {
        value = value[:100]
    }
    
    // 2. 检查基数
    if len(cc.buckets) >= cc.maxCardinality {
        // 使用哈希值
        hash := sha256.Sum256([]byte(value))
        return hex.EncodeToString(hash[:8])
    }
    
    cc.buckets[value] = struct{}{}
    return value
}

// NormalizeURL 规范化 URL (避免高基数)
func NormalizeURL(url string) string {
    // 替换数字ID为占位符
    // /api/users/123 -> /api/users/:id
    // /api/orders/456/items/789 -> /api/orders/:id/items/:id
    
    // 实现略...
    return url
}
```

### 3. 度量聚合

```text
# 按服务聚合请求总数
sum(rate(http_requests_total[5m])) by (service)

# 按状态码聚合错误率
sum(rate(http_errors_total[5m])) by (status_code) / sum(rate(http_requests_total[5m]))

# 计算平均响应时间
rate(http_request_duration_seconds_sum[5m]) / rate(http_request_duration_seconds_count[5m])

# TOP N 最慢的服务
topk(5, avg(rate(http_request_duration_seconds_sum[5m])) by (service))
```

---

## 故障排查

### 1. 常见问题

```text
问题 1: 度量未显示
原因:
  - 应用未暴露 /metrics 端点
  - vmagent 未正确采集
  - 防火墙阻止连接

排查:
  1. 访问应用度量端点: curl http://localhost:9090/metrics
  2. 检查 vmagent 日志: docker logs vmagent
  3. 检查 vmagent targets: http://localhost:8429/targets
  4. 测试连接: telnet localhost 9090

问题 2: 查询缓慢
原因:
  - 时间范围过大
  - 标签基数过高
  - 资源不足

排查:
  1. 减小查询时间范围
  2. 使用 aggregation 减少数据点
  3. 增加 VM 资源配置
  4. 启用查询缓存

问题 3: 数据丢失
原因:
  - 磁盘空间不足
  - 数据保留期过短
  - 写入速率超限

排查:
  1. 检查磁盘空间: df -h
  2. 检查保留期配置: --retentionPeriod
  3. 检查写入速率: rate(vm_rows_inserted_total[5m])
  4. 增大存储空间或调整保留期

问题 4: 高内存使用
原因:
  - 查询复杂度高
  - 缓存过大
  - 标签基数过高

排查:
  1. 优化查询语句
  2. 减少查询时间范围
  3. 控制标签基数
  4. 调整 --memory.allowedPercent
```

### 2. 监控 VictoriaMetrics 自身

```yaml
# vm-self-monitoring-rules.yml
groups:
  - name: victoriametrics_health
    interval: 30s
    rules:
      # VM 磁盘空间
      - alert: VMDiskSpaceLow
        expr: vm_free_disk_space_bytes / vm_disk_space_bytes * 100 < 10
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "VictoriaMetrics disk space low"
          description: "Disk space is below 10%"
      
      # VM 内存使用
      - alert: VMHighMemoryUsage
        expr: process_resident_memory_bytes{job="victoriametrics"} > 8589934592  # 8GB
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "VictoriaMetrics high memory usage"
          description: "Memory usage is {{ $value | humanize }}B"
      
      # VM 插入速率异常
      - alert: VMInsertRateDrop
        expr: rate(vm_rows_inserted_total[5m]) < 100
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "VictoriaMetrics insert rate dropped"
          description: "Insert rate is {{ $value }} rows/s"
      
      # VM 查询慢
      - alert: VMSlowQueries
        expr: histogram_quantile(0.99, rate(vm_request_duration_seconds_bucket{job="victoriametrics"}[5m])) > 10
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "VictoriaMetrics slow queries"
          description: "P99 query duration is {{ $value }}s"
```

---

## 总结

### 核心要点

```text
✅ VictoriaMetrics 优势:
  - 极高性能 (20x Prometheus)
  - 极低资源消耗
  - 100% PromQL 兼容
  - 长期存储原生支持
  - 简单易部署

✅ 集成步骤:
  1. 安装 OTLP/Prometheus 依赖
  2. 配置度量导出器
  3. 创建应用度量
  4. 部署 VictoriaMetrics
  5. 配置 Grafana

✅ 高级特性:
  - MetricsQL 扩展查询
  - vmagent 高性能采集
  - vmalert 告警
  - 多租户支持

✅ 性能优化:
  - 度量聚合
  - 标签优化
  - 基数控制
  - 采样策略

✅ 生产部署:
  - Docker Compose
  - Kubernetes
  - 高可用配置
  - 监控告警
```

### 性能基准

```text
VictoriaMetrics 性能指标:
  - 写入吞吐量: 1M+ datapoints/s per CPU core
  - 查询性能: 5-10x faster than Prometheus
  - 压缩比: 10:1
  - 内存使用: 7x lower than Prometheus
  - 磁盘使用: 10x lower than Prometheus
```

### 下一步

```text
1. 深入学习:
   - MetricsQL 高级查询
   - vmalert 告警规则
   - 集群版部署

2. 集成扩展:
   - 集成 Tempo (追踪)
   - 集成 Loki (日志)
   - 完整可观测性栈

3. 优化调优:
   - 基数控制策略
   - 查询优化
   - 存储优化
```

---

**更新时间**: 2025-10-12  
**文档版本**: v1.0.0  
**维护团队**: OTLP Go Integration Team

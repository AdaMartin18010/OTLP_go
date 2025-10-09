# Metric 类型完整指南

## 📋 目录

- [Metric 类型完整指南](#metric-类型完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [关键特性](#关键特性)
    - [Metric vs Trace](#metric-vs-trace)
  - [Metric 分类](#metric-分类)
    - [同步 vs 异步](#同步-vs-异步)
    - [累加 vs 分组](#累加-vs-分组)
  - [Counter (计数器)](#counter-计数器)
    - [定义](#定义)
    - [特性](#特性)
    - [使用场景](#使用场景)
    - [Go 实现](#go-实现)
  - [UpDownCounter (增减计数器)](#updowncounter-增减计数器)
    - [定义2](#定义2)
    - [特性2](#特性2)
    - [使用场景2](#使用场景2)
    - [Go 实现2](#go-实现2)
  - [Gauge (仪表盘)](#gauge-仪表盘)
    - [定义3](#定义3)
    - [特性3](#特性3)
    - [使用场景3](#使用场景3)
    - [Go 实现3](#go-实现3)
  - [Histogram (直方图)](#histogram-直方图)
    - [定义4](#定义4)
    - [特性4](#特性4)
    - [使用场景4](#使用场景4)
    - [Go 实现4](#go-实现4)
  - [Exponential Histogram (指数直方图)](#exponential-histogram-指数直方图)
    - [定义5](#定义5)
    - [特性5](#特性5)
    - [使用场景5](#使用场景5)
    - [Go 实现5](#go-实现5)
  - [类型选择指南](#类型选择指南)
    - [决策树](#决策树)
    - [常见场景映射](#常见场景映射)
  - [Go 完整实现](#go-完整实现)
    - [完整的监控系统](#完整的监控系统)
  - [最佳实践](#最佳实践)
    - [1. 选择正确的 Metric 类型](#1-选择正确的-metric-类型)
    - [2. 合理的标签使用](#2-合理的标签使用)
    - [3. Histogram 桶配置](#3-histogram-桶配置)
    - [4. 避免高基数问题](#4-避免高基数问题)
  - [常见问题](#常见问题)
    - [Q1: Counter 和 UpDownCounter 如何选择？](#q1-counter-和-updowncounter-如何选择)
    - [Q2: Gauge 和 UpDownCounter 有什么区别？](#q2-gauge-和-updowncounter-有什么区别)
    - [Q3: 何时使用 Histogram？](#q3-何时使用-histogram)
    - [Q4: Exponential Histogram 的优势是什么？](#q4-exponential-histogram-的优势是什么)
    - [Q5: 如何选择 Histogram 的桶边界？](#q5-如何选择-histogram-的桶边界)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Go 实现6](#go-实现6)
    - [相关文档](#相关文档)

---

## 概述

**Metrics** 是数值型的时间序列数据，用于测量和监控系统的运行状态。OpenTelemetry 定义了多种 Metric 类型，每种类型适用于不同的监控场景。

### 关键特性

- ✅ **多种类型**: Counter, Gauge, Histogram 等
- ✅ **聚合友好**: 支持高效的数据聚合
- ✅ **低开销**: 相比 Traces 更轻量级
- ✅ **时间序列**: 随时间变化的数值数据

### Metric vs Trace

| 特性 | Metrics | Traces |
|------|---------|--------|
| **数据类型** | 数值 | 事件序列 |
| **时间粒度** | 时间点/区间 | 精确时间戳 |
| **开销** | 低 | 较高 |
| **用途** | 监控、告警 | 调试、分析 |
| **聚合** | 高效 | 复杂 |

---

## Metric 分类

### 同步 vs 异步

**同步 Metric**: 在代码执行时直接记录

```go
// 同步：Counter, UpDownCounter, Histogram
counter.Add(ctx, 1)
```

**异步 Metric**: 通过回调函数定期采集

```go
// 异步：Gauge (Observable Gauge)
meter.Int64ObservableGauge("memory.usage",
    metric.WithInt64Callback(func(ctx context.Context, o metric.Int64Observer) error {
        o.Observe(getMemoryUsage())
        return nil
    }),
)
```

### 累加 vs 分组

**累加型** (Cumulative): Counter, UpDownCounter  
**分组型** (Grouping): Histogram

---

## Counter (计数器)

### 定义

**Counter** 是单调递增的累积型 Metric，用于记录事件发生的总次数或总量。

### 特性

- ✅ **单调递增**: 值只能增加，不能减少
- ✅ **累积**: 记录总数，不是速率
- ✅ **可加性**: 可以跨维度聚合

### 使用场景

- ✅ HTTP 请求总数
- ✅ 错误总数
- ✅ 处理的字节数
- ✅ 数据库查询次数

### Go 实现

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

var (
    meter = otel.Meter("my-service")
)

// 1. 创建 Counter
func setupCounter() (metric.Int64Counter, error) {
    return meter.Int64Counter(
        "http.server.request.count",
        metric.WithDescription("Total number of HTTP requests"),
        metric.WithUnit("{request}"),
    )
}

// 2. 使用 Counter
func handleRequest(ctx context.Context, counter metric.Int64Counter) {
    // 记录请求
    counter.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("http.method", "GET"),
            attribute.String("http.route", "/api/users"),
            attribute.Int("http.status_code", 200),
        ),
    )
}

// 3. 完整示例：HTTP 服务器监控
type HTTPMetrics struct {
    requestCount metric.Int64Counter
    requestBytes metric.Int64Counter
    errorCount   metric.Int64Counter
}

func NewHTTPMetrics(meter metric.Meter) (*HTTPMetrics, error) {
    requestCount, err := meter.Int64Counter(
        "http.server.request.count",
        metric.WithDescription("Total HTTP requests"),
        metric.WithUnit("{request}"),
    )
    if err != nil {
        return nil, err
    }

    requestBytes, err := meter.Int64Counter(
        "http.server.request.body_size",
        metric.WithDescription("Total HTTP request body bytes"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }

    errorCount, err := meter.Int64Counter(
        "http.server.error.count",
        metric.WithDescription("Total HTTP errors"),
        metric.WithUnit("{error}"),
    )
    if err != nil {
        return nil, err
    }

    return &HTTPMetrics{
        requestCount: requestCount,
        requestBytes: requestBytes,
        errorCount:   errorCount,
    }, nil
}

func (m *HTTPMetrics) RecordRequest(ctx context.Context, method, route string, statusCode, bodySize int) {
    attrs := []attribute.KeyValue{
        attribute.String("http.method", method),
        attribute.String("http.route", route),
        attribute.Int("http.status_code", statusCode),
    }

    // 记录请求数
    m.requestCount.Add(ctx, 1, metric.WithAttributes(attrs...))

    // 记录请求字节数
    m.requestBytes.Add(ctx, int64(bodySize), metric.WithAttributes(attrs...))

    // 记录错误
    if statusCode >= 400 {
        m.errorCount.Add(ctx, 1, metric.WithAttributes(attrs...))
    }
}
```

---

## UpDownCounter (增减计数器)

### 定义2

**UpDownCounter** 是可增可减的累积型 Metric，用于记录可以上升或下降的数量。

### 特性2

- ✅ **双向变化**: 可以增加或减少
- ✅ **累积**: 记录当前总数
- ✅ **可加性**: 可以跨维度聚合

### 使用场景2

- ✅ 活动连接数
- ✅ 队列中的项目数
- ✅ 正在处理的请求数
- ✅ 缓存中的条目数

### Go 实现2

```go
// 1. 创建 UpDownCounter
func setupUpDownCounter() (metric.Int64UpDownCounter, error) {
    return meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Number of active HTTP requests"),
        metric.WithUnit("{request}"),
    )
}

// 2. 使用 UpDownCounter
func trackActiveRequests(ctx context.Context, counter metric.Int64UpDownCounter) {
    // 请求开始：增加
    counter.Add(ctx, 1)
    defer counter.Add(ctx, -1) // 请求结束：减少

    // 处理请求
    handleRequest()
}

// 3. 完整示例：连接池监控
type ConnectionPoolMetrics struct {
    activeConns   metric.Int64UpDownCounter
    idleConns     metric.Int64UpDownCounter
    waitingConns  metric.Int64UpDownCounter
}

func NewConnectionPoolMetrics(meter metric.Meter, poolName string) (*ConnectionPoolMetrics, error) {
    attrs := []attribute.KeyValue{
        attribute.String("pool.name", poolName),
    }

    activeConns, err := meter.Int64UpDownCounter(
        "db.client.connections.active",
        metric.WithDescription("Active database connections"),
        metric.WithUnit("{connection}"),
    )
    if err != nil {
        return nil, err
    }

    idleConns, err := meter.Int64UpDownCounter(
        "db.client.connections.idle",
        metric.WithDescription("Idle database connections"),
        metric.WithUnit("{connection}"),
    )
    if err != nil {
        return nil, err
    }

    waitingConns, err := meter.Int64UpDownCounter(
        "db.client.connections.waiting",
        metric.WithDescription("Waiting database connection requests"),
        metric.WithUnit("{request}"),
    )
    if err != nil {
        return nil, err
    }

    return &ConnectionPoolMetrics{
        activeConns:  activeConns,
        idleConns:    idleConns,
        waitingConns: waitingConns,
    }, nil
}

func (m *ConnectionPoolMetrics) AcquireConnection(ctx context.Context) {
    // 获取连接
    m.idleConns.Add(ctx, -1)   // 空闲连接减少
    m.activeConns.Add(ctx, 1)  // 活动连接增加
}

func (m *ConnectionPoolMetrics) ReleaseConnection(ctx context.Context) {
    // 释放连接
    m.activeConns.Add(ctx, -1)  // 活动连接减少
    m.idleConns.Add(ctx, 1)     // 空闲连接增加
}

func (m *ConnectionPoolMetrics) WaitForConnection(ctx context.Context) {
    m.waitingConns.Add(ctx, 1)
    defer m.waitingConns.Add(ctx, -1)

    // 等待连接可用
    <-waitChan
}
```

---

## Gauge (仪表盘)

### 定义3

**Gauge** 是测量某个时刻的瞬时值的 Metric，通常通过异步回调实现。

### 特性3

- ✅ **瞬时值**: 测量当前状态
- ✅ **异步采集**: 通过回调函数
- ✅ **非累积**: 不是累加值

### 使用场景3

- ✅ 内存使用量
- ✅ CPU 使用率
- ✅ 磁盘空间
- ✅ 温度、湿度等物理量

### Go 实现3

```go
// 1. 创建 Observable Gauge
func setupGauge(meter metric.Meter) error {
    _, err := meter.Int64ObservableGauge(
        "runtime.go.mem.heap_inuse",
        metric.WithDescription("Heap memory in use"),
        metric.WithUnit("By"),
        metric.WithInt64Callback(func(ctx context.Context, o metric.Int64Observer) error {
            var m runtime.MemStats
            runtime.ReadMemStats(&m)
            o.Observe(int64(m.HeapInuse))
            return nil
        }),
    )
    return err
}

// 2. 完整示例：系统资源监控
type SystemMetrics struct {
    meter metric.Meter
}

func NewSystemMetrics(meter metric.Meter) (*SystemMetrics, error) {
    sm := &SystemMetrics{meter: meter}

    // CPU 使用率
    _, err := meter.Float64ObservableGauge(
        "system.cpu.utilization",
        metric.WithDescription("CPU utilization ratio"),
        metric.WithUnit("1"),
        metric.WithFloat64Callback(sm.observeCPU),
    )
    if err != nil {
        return nil, err
    }

    // 内存使用
    _, err = meter.Int64ObservableGauge(
        "system.memory.usage",
        metric.WithDescription("Memory usage in bytes"),
        metric.WithUnit("By"),
        metric.WithInt64Callback(sm.observeMemory),
    )
    if err != nil {
        return nil, err
    }

    // 磁盘使用
    _, err = meter.Int64ObservableGauge(
        "system.disk.usage",
        metric.WithDescription("Disk usage in bytes"),
        metric.WithUnit("By"),
        metric.WithInt64Callback(sm.observeDisk),
    )
    if err != nil {
        return nil, err
    }

    // Goroutine 数量
    _, err = meter.Int64ObservableGauge(
        "runtime.go.goroutines",
        metric.WithDescription("Number of goroutines"),
        metric.WithUnit("{goroutine}"),
        metric.WithInt64Callback(func(ctx context.Context, o metric.Int64Observer) error {
            o.Observe(int64(runtime.NumGoroutine()))
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }

    return sm, nil
}

func (sm *SystemMetrics) observeCPU(ctx context.Context, o metric.Float64Observer) error {
    // 使用 gopsutil 获取 CPU 使用率
    percentages, err := cpu.Percent(0, false)
    if err != nil {
        return err
    }
    if len(percentages) > 0 {
        o.Observe(percentages[0] / 100.0)
    }
    return nil
}

func (sm *SystemMetrics) observeMemory(ctx context.Context, o metric.Int64Observer) error {
    var m runtime.MemStats
    runtime.ReadMemStats(&m)
    
    o.Observe(int64(m.Alloc),
        metric.WithAttributes(attribute.String("state", "used")))
    o.Observe(int64(m.Sys),
        metric.WithAttributes(attribute.String("state", "total")))
    
    return nil
}

func (sm *SystemMetrics) observeDisk(ctx context.Context, o metric.Int64Observer) error {
    // 使用 gopsutil 获取磁盘使用
    stat, err := disk.Usage("/")
    if err != nil {
        return err
    }
    
    o.Observe(int64(stat.Used),
        metric.WithAttributes(
            attribute.String("device", "/"),
            attribute.String("state", "used"),
        ))
    o.Observe(int64(stat.Total),
        metric.WithAttributes(
            attribute.String("device", "/"),
            attribute.String("state", "total"),
        ))
    
    return nil
}
```

---

## Histogram (直方图)

### 定义4

**Histogram** 用于测量值的分布，将观测值分配到预定义的桶中。

### 特性4

- ✅ **分布统计**: 百分位数、平均值、总和
- ✅ **预定义桶**: 固定的桶边界
- ✅ **聚合友好**: 可以跨维度聚合

### 使用场景4

- ✅ 请求延迟
- ✅ 响应大小
- ✅ 处理时间
- ✅ 任何需要了解分布的指标

### Go 实现4

```go
// 1. 创建 Histogram
func setupHistogram() (metric.Float64Histogram, error) {
    return meter.Float64Histogram(
        "http.server.request.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("s"),
        metric.WithExplicitBucketBoundaries(
            0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10,
        ),
    )
}

// 2. 使用 Histogram
func trackRequestDuration(ctx context.Context, histogram metric.Float64Histogram) {
    start := time.Now()
    defer func() {
        duration := time.Since(start).Seconds()
        histogram.Record(ctx, duration,
            metric.WithAttributes(
                attribute.String("http.method", "GET"),
                attribute.String("http.route", "/api/users"),
            ),
        )
    }()

    // 处理请求
    handleRequest()
}

// 3. 完整示例：性能监控
type PerformanceMetrics struct {
    requestDuration  metric.Float64Histogram
    responseSize     metric.Int64Histogram
    dbQueryDuration  metric.Float64Histogram
}

func NewPerformanceMetrics(meter metric.Meter) (*PerformanceMetrics, error) {
    // HTTP 请求延迟（秒）
    requestDuration, err := meter.Float64Histogram(
        "http.server.request.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("s"),
        metric.WithExplicitBucketBoundaries(
            0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10,
        ),
    )
    if err != nil {
        return nil, err
    }

    // HTTP 响应大小（字节）
    responseSize, err := meter.Int64Histogram(
        "http.server.response.body_size",
        metric.WithDescription("HTTP response body size"),
        metric.WithUnit("By"),
        metric.WithExplicitBucketBoundaries(
            100, 1000, 10000, 100000, 1000000, 10000000,
        ),
    )
    if err != nil {
        return nil, err
    }

    // 数据库查询延迟（秒）
    dbQueryDuration, err := meter.Float64Histogram(
        "db.client.operation.duration",
        metric.WithDescription("Database operation duration"),
        metric.WithUnit("s"),
        metric.WithExplicitBucketBoundaries(
            0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1, 5,
        ),
    )
    if err != nil {
        return nil, err
    }

    return &PerformanceMetrics{
        requestDuration: requestDuration,
        responseSize:    responseSize,
        dbQueryDuration: dbQueryDuration,
    }, nil
}

func (pm *PerformanceMetrics) TrackHTTPRequest(
    ctx context.Context,
    method, route string,
    statusCode int,
    start time.Time,
    responseSize int64,
) {
    duration := time.Since(start).Seconds()
    attrs := []attribute.KeyValue{
        attribute.String("http.method", method),
        attribute.String("http.route", route),
        attribute.Int("http.status_code", statusCode),
    }

    pm.requestDuration.Record(ctx, duration,
        metric.WithAttributes(attrs...))
    pm.responseSize.Record(ctx, responseSize,
        metric.WithAttributes(attrs...))
}

func (pm *PerformanceMetrics) TrackDBQuery(
    ctx context.Context,
    operation, table string,
    start time.Time,
) {
    duration := time.Since(start).Seconds()
    pm.dbQueryDuration.Record(ctx, duration,
        metric.WithAttributes(
            attribute.String("db.operation", operation),
            attribute.String("db.sql.table", table),
        ),
    )
}
```

---

## Exponential Histogram (指数直方图)

### 定义5

**Exponential Histogram** 使用指数增长的桶边界，自动适应值的范围。

### 特性5

- ✅ **自动调整**: 桶边界自动适应数据
- ✅ **高精度**: 在感兴趣的范围内提供更高精度
- ✅ **紧凑**: 相比固定桶更节省空间

### 使用场景5

- ✅ 值范围未知或变化大的场景
- ✅ 需要自动适应的分布统计
- ✅ 减少配置复杂度

### Go 实现5

```go
// Exponential Histogram (Go SDK 自动使用)
func setupExponentialHistogram() (metric.Float64Histogram, error) {
    // 默认情况下，OpenTelemetry Go SDK 使用 Exponential Histogram
    return meter.Float64Histogram(
        "http.server.request.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("s"),
        // 不指定 ExplicitBucketBoundaries 时，使用 Exponential Histogram
    )
}
```

---

## 类型选择指南

### 决策树

```text
需要记录什么？
│
├─ 事件发生次数/总量
│  ├─ 只增不减 → Counter
│  └─ 可增可减 → UpDownCounter
│
├─ 当前瞬时值
│  └─ → Gauge (Observable)
│
└─ 值的分布
   └─ → Histogram
```

### 常见场景映射

| 场景 | Metric 类型 | 示例 |
|------|-------------|------|
| HTTP 请求总数 | Counter | `http.server.request.count` |
| 错误总数 | Counter | `http.server.error.count` |
| 活动连接数 | UpDownCounter | `http.server.active_requests` |
| 队列长度 | UpDownCounter | `queue.size` |
| 内存使用量 | Gauge | `runtime.go.mem.heap_inuse` |
| CPU 使用率 | Gauge | `system.cpu.utilization` |
| 请求延迟 | Histogram | `http.server.request.duration` |
| 响应大小 | Histogram | `http.server.response.body_size` |

---

## Go 完整实现

### 完整的监控系统

```go
package monitoring

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

type Metrics struct {
    // Counters
    requestCount  metric.Int64Counter
    errorCount    metric.Int64Counter
    bytesReceived metric.Int64Counter
    bytesSent     metric.Int64Counter

    // UpDownCounters
    activeRequests metric.Int64UpDownCounter
    activeConns    metric.Int64UpDownCounter

    // Histograms
    requestDuration metric.Float64Histogram
    responseSize    metric.Int64Histogram
}

func NewMetrics() (*Metrics, error) {
    meter := otel.Meter("my-service")

    // 初始化 Counters
    requestCount, err := meter.Int64Counter(
        "http.server.request.count",
        metric.WithDescription("Total HTTP requests"),
        metric.WithUnit("{request}"),
    )
    if err != nil {
        return nil, err
    }

    errorCount, err := meter.Int64Counter(
        "http.server.error.count",
        metric.WithDescription("Total HTTP errors"),
        metric.WithUnit("{error}"),
    )
    if err != nil {
        return nil, err
    }

    bytesReceived, err := meter.Int64Counter(
        "http.server.request.body_size",
        metric.WithDescription("Total bytes received"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }

    bytesSent, err := meter.Int64Counter(
        "http.server.response.body_size",
        metric.WithDescription("Total bytes sent"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }

    // 初始化 UpDownCounters
    activeRequests, err := meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Active HTTP requests"),
        metric.WithUnit("{request}"),
    )
    if err != nil {
        return nil, err
    }

    activeConns, err := meter.Int64UpDownCounter(
        "http.server.active_connections",
        metric.WithDescription("Active connections"),
        metric.WithUnit("{connection}"),
    )
    if err != nil {
        return nil, err
    }

    // 初始化 Histograms
    requestDuration, err := meter.Float64Histogram(
        "http.server.request.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("s"),
        metric.WithExplicitBucketBoundaries(
            0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10,
        ),
    )
    if err != nil {
        return nil, err
    }

    responseSize, err := meter.Int64Histogram(
        "http.server.response.size",
        metric.WithDescription("HTTP response size distribution"),
        metric.WithUnit("By"),
        metric.WithExplicitBucketBoundaries(
            100, 1000, 10000, 100000, 1000000, 10000000,
        ),
    )
    if err != nil {
        return nil, err
    }

    return &Metrics{
        requestCount:    requestCount,
        errorCount:      errorCount,
        bytesReceived:   bytesReceived,
        bytesSent:       bytesSent,
        activeRequests:  activeRequests,
        activeConns:     activeConns,
        requestDuration: requestDuration,
        responseSize:    responseSize,
    }, nil
}

// TrackRequest 追踪完整的 HTTP 请求
func (m *Metrics) TrackRequest(
    ctx context.Context,
    method, route string,
    statusCode int,
    requestSize, responseSize int64,
    duration time.Duration,
) {
    attrs := []attribute.KeyValue{
        attribute.String("http.method", method),
        attribute.String("http.route", route),
        attribute.Int("http.status_code", statusCode),
    }

    // 记录请求数
    m.requestCount.Add(ctx, 1, metric.WithAttributes(attrs...))

    // 记录错误
    if statusCode >= 400 {
        m.errorCount.Add(ctx, 1, metric.WithAttributes(attrs...))
    }

    // 记录字节数
    m.bytesReceived.Add(ctx, requestSize, metric.WithAttributes(attrs...))
    m.bytesSent.Add(ctx, responseSize, metric.WithAttributes(attrs...))

    // 记录延迟
    m.requestDuration.Record(ctx, duration.Seconds(),
        metric.WithAttributes(attrs...))

    // 记录响应大小分布
    m.responseSize.Record(ctx, responseSize,
        metric.WithAttributes(attrs...))
}

// RequestStart 请求开始
func (m *Metrics) RequestStart(ctx context.Context) {
    m.activeRequests.Add(ctx, 1)
}

// RequestEnd 请求结束
func (m *Metrics) RequestEnd(ctx context.Context) {
    m.activeRequests.Add(ctx, -1)
}

// ConnectionOpened 连接打开
func (m *Metrics) ConnectionOpened(ctx context.Context) {
    m.activeConns.Add(ctx, 1)
}

// ConnectionClosed 连接关闭
func (m *Metrics) ConnectionClosed(ctx context.Context) {
    m.activeConns.Add(ctx, -1)
}
```

---

## 最佳实践

### 1. 选择正确的 Metric 类型

```go
// ✅ 推荐：使用 Counter 记录累积值
requestCount.Add(ctx, 1)

// ❌ 避免：使用 Gauge 记录累积值
// gauge.Record(ctx, totalRequests)

// ✅ 推荐：使用 Gauge 记录瞬时值
_, _ = meter.Int64ObservableGauge("memory.usage", ...)

// ❌ 避免：使用 Counter 记录瞬时值（会导致错误的累积）
```

### 2. 合理的标签使用

```go
// ✅ 推荐：使用低基数标签
counter.Add(ctx, 1,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),      // 低基数
        attribute.String("http.route", "/api/users"), // 低基数
        attribute.Int("http.status_code", 200),      // 低基数
    ),
)

// ❌ 避免：使用高基数标签
counter.Add(ctx, 1,
    metric.WithAttributes(
        attribute.String("user.id", userID),        // 高基数！
        attribute.String("request.id", requestID),  // 高基数！
    ),
)
```

### 3. Histogram 桶配置

```go
// ✅ 推荐：根据实际分布配置桶
meter.Float64Histogram(
    "http.server.request.duration",
    metric.WithExplicitBucketBoundaries(
        // P50 附近密集，P99 附近稀疏
        0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10,
    ),
)

// ⚠️ 注意：桶数量不要太多（通常 < 20）
```

### 4. 避免高基数问题

```go
// ❌ 高基数问题
for _, userID := range allUserIDs { // 可能有数百万用户
    counter.Add(ctx, 1,
        metric.WithAttributes(attribute.String("user.id", userID)))
}

// ✅ 解决方案：分组或采样
counter.Add(ctx, int64(len(userIDs)),
    metric.WithAttributes(attribute.String("user.segment", segment)))
```

---

## 常见问题

### Q1: Counter 和 UpDownCounter 如何选择？

**A**: 看值是否可以减少

- **只增不减**: Counter (如请求总数、错误总数)
- **可增可减**: UpDownCounter (如活动连接数、队列长度)

---

### Q2: Gauge 和 UpDownCounter 有什么区别？

**A**:

- **Gauge**: 异步采集，瞬时值，不可累加（如内存使用量）
- **UpDownCounter**: 同步更新，累积值，可累加（如活动连接数）

---

### Q3: 何时使用 Histogram？

**A**: 需要了解值的分布时

- 延迟百分位数 (P50, P95, P99)
- 大小分布
- 任何需要统计分布的场景

---

### Q4: Exponential Histogram 的优势是什么？

**A**: 自动适应，无需配置桶边界

- 值范围未知时
- 值范围变化大时
- 简化配置

---

### Q5: 如何选择 Histogram 的桶边界？

**A**: 基于实际数据分布

1. 收集样本数据
2. 分析 P50, P90, P95, P99
3. 在感兴趣的范围内增加桶密度
4. 避免桶数量过多（通常 < 20）

---

## 参考资源

### 官方文档

- [OpenTelemetry Metrics](https://opentelemetry.io/docs/specs/otel/metrics/)
- [Metric API Specification](https://opentelemetry.io/docs/specs/otel/metrics/api/)

### Go 实现6

- [go.opentelemetry.io/otel/metric](https://pkg.go.dev/go.opentelemetry.io/otel/metric)

### 相关文档

- [02_数据点.md](./02_数据点.md)
- [03_时间序列.md](./03_时间序列.md)
- [../../../02_Semantic_Conventions/03_Metric约定/](../../../02_Semantic_Conventions/03_Metric约定/)

---

**🎉 恭喜！你已经掌握了 Metric 类型的完整知识！**

下一步：学习 [数据点](./02_数据点.md) 了解 Metric 的数据结构。

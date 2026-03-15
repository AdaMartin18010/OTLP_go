# Metrics 子类型详解

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Metrics 子类型详解](#metrics-子类型详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 Metrics类型分类](#11-metrics类型分类)
    - [1.2 选择指南](#12-选择指南)
  - [2. Counter（计数器）](#2-counter计数器)
    - [2.1 定义与特性](#21-定义与特性)
    - [2.2 使用场景](#22-使用场景)
    - [2.3 API使用](#23-api使用)
    - [2.4 最佳实践](#24-最佳实践)
  - [3. UpDownCounter（双向计数器）](#3-updowncounter双向计数器)
    - [3.1 定义与特性](#31-定义与特性)
    - [3.2 使用场景](#32-使用场景)
    - [3.3 API使用](#33-api使用)
  - [4. Gauge（仪表盘）](#4-gauge仪表盘)
    - [4.1 定义与特性](#41-定义与特性)
    - [4.2 使用场景](#42-使用场景)
    - [4.3 API使用](#43-api使用)
    - [4.4 与UpDownCounter对比](#44-与updowncounter对比)
  - [5. Histogram（直方图）](#5-histogram直方图)
    - [5.1 定义与特性](#51-定义与特性)
    - [5.2 使用场景](#52-使用场景)
    - [5.3 API使用](#53-api使用)
    - [5.4 Bucket配置](#54-bucket配置)
  - [6. ExponentialHistogram（指数直方图）](#6-exponentialhistogram指数直方图)
    - [6.1 定义与特性](#61-定义与特性)
    - [6.2 优势](#62-优势)
    - [6.3 API使用](#63-api使用)
  - [7. Summary（摘要）](#7-summary摘要)
    - [7.1 定义与特性](#71-定义与特性)
    - [7.2 使用场景](#72-使用场景)
    - [7.3 与Histogram对比](#73-与histogram对比)
  - [8. 类型选择决策树](#8-类型选择决策树)
  - [9. 完整示例](#9-完整示例)
    - [9.1 Web应用监控](#91-web应用监控)
    - [9.2 数据库连接池监控](#92-数据库连接池监控)
    - [9.3 API延迟监控](#93-api延迟监控)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [SDK文档](#sdk文档)
    - [最佳实践](#最佳实践)

---

## 1. 概述

### 1.1 Metrics类型分类

OpenTelemetry定义了6种核心Metric类型：

| 类型 | 累加性 | 方向 | 用途 |
|------|--------|------|------|
| **Counter** | ✅ 单调递增 | 只增 | 计数事件总数 |
| **UpDownCounter** | ✅ 可增可减 | 双向 | 追踪增减变化的值 |
| **Gauge** | ❌ 非累加 | - | 当前瞬时值 |
| **Histogram** | ✅ 分布统计 | - | 值分布与统计 |
| **ExponentialHistogram** | ✅ 指数分布 | - | 高精度分布统计 |
| **Summary** | ✅ 百分位 | - | 客户端百分位计算 |

### 1.2 选择指南

```text
需求                          → 推荐类型
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
计数事件（只增不减）         → Counter
计数资源（可增可减）         → UpDownCounter
测量瞬时值                   → Gauge
统计值分布                   → Histogram
高精度分布统计               → ExponentialHistogram
客户端百分位                 → Summary（不推荐）
```

---

## 2. Counter（计数器）

### 2.1 定义与特性

**Counter**是单调递增的累加指标，只能增加或重置为0。

**核心特性**：

```text
✅ 单调递增（monotonic）
✅ 累加性（additive）
✅ 支持Rate计算
✅ 非负值
```

### 2.2 使用场景

**适用场景**：

```text
✅ HTTP请求总数
✅ 错误发生次数
✅ 任务完成数量
✅ 字节发送/接收总量
✅ 缓存命中次数
```

**❌ 不适用场景**：

```text
❌ 当前活跃用户数（使用UpDownCounter）
❌ CPU使用率（使用Gauge）
❌ 温度（使用Gauge）
```

### 2.3 API使用

**Go SDK**：

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

func main() {
    meter := otel.Meter("example")
    
    // 创建Counter
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Total HTTP requests"),
        metric.WithUnit("{request}"),
    )
    
    // 使用Counter
    ctx := context.Background()
    requestCounter.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("method", "GET"),
            attribute.String("status", "200"),
        ),
    )
}
```

**Python SDK**：

```python
from opentelemetry import metrics

meter = metrics.get_meter(__name__)

# 创建Counter
request_counter = meter.create_counter(
    name="http.server.requests",
    description="Total HTTP requests",
    unit="{request}"
)

# 使用Counter
request_counter.add(1, {
    "method": "GET",
    "status": "200"
})
```

**Java SDK**：

```java
Meter meter = openTelemetry.getMeter("example");

// 创建Counter
LongCounter requestCounter = meter
    .counterBuilder("http.server.requests")
    .setDescription("Total HTTP requests")
    .setUnit("{request}")
    .build();

// 使用Counter
requestCounter.add(1,
    Attributes.of(
        AttributeKey.stringKey("method"), "GET",
        AttributeKey.stringKey("status"), "200"
    )
);
```

### 2.4 最佳实践

**命名规范**：

```text
✅ http.server.requests          (好)
✅ db.queries.total              (好)
✅ cache.hits                    (好)

❌ requests                      (太泛)
❌ httpServerRequestsCount       (使用驼峰)
❌ http_server_requests_total    (多余的_total)
```

**单位选择**：

```text
请求数: {request}
字节数: By (bytes)
操作数: {operation}
消息数: {message}
无单位: 1
```

---

## 3. UpDownCounter（双向计数器）

### 3.1 定义与特性

**UpDownCounter**是可以增加或减少的计数器。

**核心特性**：

```text
✅ 可增可减（non-monotonic）
✅ 累加性（additive）
✅ 追踪当前状态
✅ 可以为负值
```

### 3.2 使用场景

**适用场景**：

```text
✅ 当前活跃连接数
✅ 队列中的任务数
✅ 数据库连接池大小
✅ 内存分配/释放
✅ 库存数量变化
```

### 3.3 API使用

**Go SDK**：

```go
// 创建UpDownCounter
activeConnections, _ := meter.Int64UpDownCounter(
    "db.connections.active",
    metric.WithDescription("Active database connections"),
    metric.WithUnit("{connection}"),
)

// 连接建立时增加
activeConnections.Add(ctx, 1)

// 连接关闭时减少
activeConnections.Add(ctx, -1)
```

**Python SDK**：

```python
# 创建UpDownCounter
active_connections = meter.create_up_down_counter(
    name="db.connections.active",
    description="Active database connections",
    unit="{connection}"
)

# 连接建立
active_connections.add(1)

# 连接关闭
active_connections.add(-1)
```

---

## 4. Gauge（仪表盘）

### 4.1 定义与特性

**Gauge**表示某个时刻的瞬时值。

**核心特性**：

```text
✅ 非累加性（non-additive）
✅ 瞬时值（instantaneous）
✅ 可增可减
✅ 适合直接测量
```

### 4.2 使用场景

**适用场景**：

```text
✅ CPU使用率
✅ 内存使用量
✅ 温度
✅ 磁盘使用率
✅ 队列长度（瞬时）
```

### 4.3 API使用

**Go SDK**：

```go
// 创建Gauge（通过Callback）
_, _ = meter.Float64ObservableGauge(
    "system.memory.usage",
    metric.WithDescription("Current memory usage"),
    metric.WithUnit("By"),
    metric.WithFloat64Callback(func(_ context.Context, observer metric.Float64Observer) error {
        // 获取当前内存使用
        memUsage := getMemoryUsage()
        observer.Observe(memUsage)
        return nil
    }),
)
```

**Python SDK**：

```python
def get_cpu_usage(observer):
    """获取当前CPU使用率"""
    cpu_percent = psutil.cpu_percent()
    observer.observe(cpu_percent, {
        "host": "server-01"
    })

# 创建Gauge
cpu_gauge = meter.create_observable_gauge(
    name="system.cpu.usage",
    callbacks=[get_cpu_usage],
    description="Current CPU usage",
    unit="%"
)
```

### 4.4 与UpDownCounter对比

| 特性 | Gauge | UpDownCounter |
|------|-------|---------------|
| 累加性 | 非累加 | 累加 |
| 聚合 | 取最新值 | 求和 |
| 使用方式 | Callback观察 | 主动Add |
| 适用场景 | 瞬时测量 | 增减计数 |

**示例对比**：

```go
// Gauge: 当前队列长度（观察值）
queueLengthGauge, _ := meter.Int64ObservableGauge(
    "queue.length",
    metric.WithInt64Callback(func(_ context.Context, observer metric.Int64Observer) error {
        observer.Observe(int64(queue.Len()))
        return nil
    }),
)

// UpDownCounter: 队列任务增减（累加）
queueTasks, _ := meter.Int64UpDownCounter("queue.tasks")
queueTasks.Add(ctx, 1)   // 添加任务
queueTasks.Add(ctx, -1)  // 完成任务
```

---

## 5. Histogram（直方图）

### 5.1 定义与特性

**Histogram**记录值的分布情况，自动计算统计信息。

**核心特性**：

```text
✅ 记录值分布
✅ 自动计算count、sum、min、max
✅ 支持Bucket（桶）
✅ 服务器端聚合
```

**输出数据**：

```text
- count:  观察值数量
- sum:    所有值的总和
- min:    最小值
- max:    最大值
- buckets: 每个桶的计数
```

### 5.2 使用场景

**适用场景**：

```text
✅ HTTP请求延迟
✅ 数据库查询时间
✅ 消息大小
✅ 响应时间分布
✅ 批处理大小
```

### 5.3 API使用

**Go SDK**：

```go
// 创建Histogram
requestDuration, _ := meter.Float64Histogram(
    "http.server.duration",
    metric.WithDescription("HTTP request duration"),
    metric.WithUnit("ms"),
)

// 记录延迟
startTime := time.Now()
// ... 处理请求 ...
duration := time.Since(startTime).Milliseconds()

requestDuration.Record(ctx, float64(duration),
    metric.WithAttributes(
        attribute.String("method", "GET"),
        attribute.String("route", "/api/users"),
    ),
)
```

**Python SDK**：

```python
# 创建Histogram
request_duration = meter.create_histogram(
    name="http.server.duration",
    description="HTTP request duration",
    unit="ms"
)

# 记录延迟
start_time = time.time()
# ... 处理请求 ...
duration = (time.time() - start_time) * 1000

request_duration.record(duration, {
    "method": "GET",
    "route": "/api/users"
})
```

### 5.4 Bucket配置

**默认Bucket**：

```text
[0, 5, 10, 25, 50, 75, 100, 250, 500, 750, 1000, 2500, 5000, 7500, 10000]
```

**自定义Bucket（Go）**：

```go
import "go.opentelemetry.io/otel/sdk/metric"

// 延迟Bucket（毫秒）
latencyBuckets := metric.ExplicitBucketBoundaries{
    1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000,
}

// 响应大小Bucket（字节）
sizeBuckets := metric.ExplicitBucketBoundaries{
    100, 500, 1024, 5120, 10240, 51200, 102400, 512000, 1048576,
}
```

**Bucket选择指南**：

```text
延迟监控: 使用对数分布（1, 2, 5, 10, 20, 50...）
大小监控: 使用2的幂次（256, 512, 1024, 2048...）
百分比: 使用线性分布（10, 20, 30, 40...）
```

---

## 6. ExponentialHistogram（指数直方图）

### 6.1 定义与特性

**ExponentialHistogram**使用指数桶，自动适应值的范围。

**核心特性**：

```text
✅ 自动调整桶边界
✅ 更高精度
✅ 更小存储开销
✅ 适合wide range值
```

### 6.2 优势

与传统Histogram对比：

| 特性 | Histogram | ExponentialHistogram |
|------|-----------|----------------------|
| Bucket定义 | 固定预定义 | 动态调整 |
| 精度 | 取决于配置 | 高精度 |
| 存储 | 固定桶数 | 动态优化 |
| 适用范围 | 已知范围 | 未知/广泛范围 |

### 6.3 API使用

**Go SDK**：

```go
// ExponentialHistogram通常由SDK自动使用
// 在View配置中指定
import "go.opentelemetry.io/otel/sdk/metric"

provider := metric.NewMeterProvider(
    metric.WithReader(
        metric.NewPeriodicReader(exporter),
    ),
    metric.WithView(
        metric.NewView(
            metric.Instrument{Name: "http.server.duration"},
            metric.Stream{
                Aggregation: metric.AggregationExponentialHistogram{
                    MaxSize: 160,
                    MaxScale: 20,
                },
            },
        ),
    ),
)
```

---

## 7. Summary（摘要）

### 7.1 定义与特性

**Summary**在客户端计算百分位数。

**核心特性**：

```text
✅ 客户端计算百分位
✅ 精确百分位值
❌ 不支持服务器端聚合
❌ 高内存开销
```

**⚠️ 注意**: OpenTelemetry **不推荐**使用Summary，推荐使用Histogram。

### 7.2 使用场景

**适用场景**（罕见）：

```text
- 需要精确百分位且无法在服务器端聚合
- 单实例应用
```

### 7.3 与Histogram对比

| 特性 | Histogram | Summary |
|------|-----------|---------|
| 计算位置 | 服务器端 | 客户端 |
| 聚合能力 | ✅ 支持 | ❌ 不支持 |
| 百分位精度 | 近似 | 精确 |
| 内存开销 | 低 | 高 |
| 推荐度 | ⭐⭐⭐⭐⭐ | ⭐ |

---

## 8. 类型选择决策树

```text
开始
  │
  ├─ 需要计数？
  │   ├─ 只增不减？ → Counter
  │   └─ 可增可减？ → UpDownCounter
  │
  ├─ 需要当前值？
  │   ├─ 是瞬时测量？ → Gauge
  │   └─ 是增减计数？ → UpDownCounter
  │
  └─ 需要分布统计？
      ├─ 已知值范围？ → Histogram
      ├─ 未知/广泛范围？ → ExponentialHistogram
      └─ 需要精确百分位且单实例？ → Summary（不推荐）
```

**快速查找表**：

| 需求 | 类型 |
|------|------|
| 请求总数 | Counter |
| 错误总数 | Counter |
| 活跃连接 | UpDownCounter |
| 队列任务数 | UpDownCounter |
| CPU使用率 | Gauge |
| 内存使用量 | Gauge |
| 请求延迟 | Histogram |
| 响应大小 | Histogram |
| 未知范围延迟 | ExponentialHistogram |

---

## 9. 完整示例

### 9.1 Web应用监控

```go
package main

import (
    "context"
    "time"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

type WebMetrics struct {
    requestCounter     metric.Int64Counter
    activeRequests     metric.Int64UpDownCounter
    requestDuration    metric.Float64Histogram
    memoryUsage        metric.Int64ObservableGauge
}

func NewWebMetrics() *WebMetrics {
    meter := otel.Meter("web-server")
    
    // Counter: 请求总数
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Total HTTP requests"),
        metric.WithUnit("{request}"),
    )
    
    // UpDownCounter: 当前活跃请求
    activeRequests, _ := meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Currently active requests"),
        metric.WithUnit("{request}"),
    )
    
    // Histogram: 请求延迟
    requestDuration, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    
    // Gauge: 内存使用
    memoryUsage, _ := meter.Int64ObservableGauge(
        "process.memory.usage",
        metric.WithDescription("Process memory usage"),
        metric.WithUnit("By"),
        metric.WithInt64Callback(func(_ context.Context, observer metric.Int64Observer) error {
            var m runtime.MemStats
            runtime.ReadMemStats(&m)
            observer.Observe(int64(m.Alloc))
            return nil
        }),
    )
    
    return &WebMetrics{
        requestCounter:  requestCounter,
        activeRequests:  activeRequests,
        requestDuration: requestDuration,
        memoryUsage:     memoryUsage,
    }
}

func (m *WebMetrics) HandleRequest(ctx context.Context, method, route string) {
    // 增加活跃请求
    m.activeRequests.Add(ctx, 1)
    defer m.activeRequests.Add(ctx, -1)
    
    // 记录请求总数
    attrs := metric.WithAttributes(
        attribute.String("method", method),
        attribute.String("route", route),
    )
    m.requestCounter.Add(ctx, 1, attrs)
    
    // 测量延迟
    startTime := time.Now()
    defer func() {
        duration := float64(time.Since(startTime).Milliseconds())
        m.requestDuration.Record(ctx, duration, attrs)
    }()
    
    // 处理请求逻辑...
}
```

### 9.2 数据库连接池监控

```python
from opentelemetry import metrics
import time

class DatabasePoolMetrics:
    def __init__(self, pool):
        self.pool = pool
        meter = metrics.get_meter(__name__)
        
        # Counter: 连接创建总数
        self.connections_created = meter.create_counter(
            name="db.connections.created",
            description="Total database connections created",
            unit="{connection}"
        )
        
        # Counter: 连接错误总数
        self.connection_errors = meter.create_counter(
            name="db.connections.errors",
            description="Total connection errors",
            unit="{error}"
        )
        
        # UpDownCounter: 活跃连接
        self.active_connections = meter.create_up_down_counter(
            name="db.connections.active",
            description="Currently active connections",
            unit="{connection}"
        )
        
        # Gauge: 连接池使用率
        self.pool_usage = meter.create_observable_gauge(
            name="db.pool.usage",
            callbacks=[self._observe_pool_usage],
            description="Connection pool usage percentage",
            unit="%"
        )
        
        # Histogram: 连接获取时间
        self.acquire_duration = meter.create_histogram(
            name="db.connections.acquire.duration",
            description="Time to acquire connection",
            unit="ms"
        )
    
    def _observe_pool_usage(self, observer):
        """观察连接池使用率"""
        usage = (self.pool.size() / self.pool.maxsize) * 100
        observer.observe(usage, {
            "pool": self.pool.name
        })
    
    def acquire_connection(self):
        """获取连接"""
        start_time = time.time()
        
        try:
            # 获取连接
            conn = self.pool.get_connection()
            
            # 记录指标
            duration = (time.time() - start_time) * 1000
            self.acquire_duration.record(duration)
            self.active_connections.add(1)
            self.connections_created.add(1)
            
            return conn
        except Exception as e:
            self.connection_errors.add(1)
            raise
    
    def release_connection(self, conn):
        """释放连接"""
        self.pool.return_connection(conn)
        self.active_connections.add(-1)
```

### 9.3 API延迟监控

```java
import io.opentelemetry.api.metrics.*;
import io.opentelemetry.api.common.AttributeKey;
import io.opentelemetry.api.common.Attributes;

public class ApiMetrics {
    private final LongCounter requestCounter;
    private final LongUpDownCounter activeRequests;
    private final DoubleHistogram requestDuration;
    private final ObservableDoubleGauge errorRate;
    
    public ApiMetrics(Meter meter) {
        // Counter: API调用总数
        this.requestCounter = meter
            .counterBuilder("api.requests")
            .setDescription("Total API requests")
            .setUnit("{request}")
            .build();
        
        // UpDownCounter: 活跃请求
        this.activeRequests = meter
            .upDownCounterBuilder("api.active_requests")
            .setDescription("Currently active API requests")
            .setUnit("{request}")
            .build();
        
        // Histogram: 请求延迟
        this.requestDuration = meter
            .histogramBuilder("api.duration")
            .setDescription("API request duration")
            .setUnit("ms")
            .build();
        
        // Gauge: 错误率
        this.errorRate = meter
            .gaugeBuilder("api.error_rate")
            .setDescription("API error rate")
            .setUnit("%")
            .buildWithCallback(measurement -> {
                double rate = calculateErrorRate();
                measurement.record(rate);
            });
    }
    
    public void recordRequest(String endpoint, String method, long durationMs, boolean success) {
        Attributes attrs = Attributes.of(
            AttributeKey.stringKey("endpoint"), endpoint,
            AttributeKey.stringKey("method"), method,
            AttributeKey.stringKey("status"), success ? "success" : "error"
        );
        
        // 记录所有指标
        requestCounter.add(1, attrs);
        requestDuration.record(durationMs, attrs);
    }
    
    public void startRequest() {
        activeRequests.add(1);
    }
    
    public void endRequest() {
        activeRequests.add(-1);
    }
    
    private double calculateErrorRate() {
        // 计算错误率逻辑
        return 0.0;
    }
}
```

---

## 10. 参考资源

### 官方文档

- **OpenTelemetry Metrics API**: <https://opentelemetry.io/docs/specs/otel/metrics/api/>
- **Metrics Data Model**: <https://opentelemetry.io/docs/specs/otel/metrics/data-model/>
- **Metrics Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/general/metrics/>

### SDK文档

- **Go Metrics**: <https://pkg.go.dev/go.opentelemetry.io/otel/metric>
- **Python Metrics**: <https://opentelemetry-python.readthedocs.io/en/latest/sdk/metrics.html>
- **Java Metrics**: <https://opentelemetry.io/docs/instrumentation/java/manual/#metrics>

### 最佳实践

- **Prometheus Metric Types**: <https://prometheus.io/docs/concepts/metric_types/>
- **OpenMetrics Specification**: <https://github.com/OpenObservability/OpenMetrics>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

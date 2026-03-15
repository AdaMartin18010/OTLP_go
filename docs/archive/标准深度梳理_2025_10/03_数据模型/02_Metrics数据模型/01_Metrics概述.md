# Metrics数据模型概述

> **OTLP版本**: v1.0.0 (Stable)  
> **最后更新**: 2025年10月8日

---

## 目录

- [Metrics数据模型概述](#metrics数据模型概述)
  - [目录](#目录)
  - [1. 什么是Metrics](#1-什么是metrics)
    - [1.1 核心概念](#11-核心概念)
    - [1.2 Metrics vs Traces vs Logs](#12-metrics-vs-traces-vs-logs)
  - [2. Metric类型](#2-metric类型)
    - [2.1 Counter](#21-counter)
    - [2.2 UpDownCounter](#22-updowncounter)
    - [2.3 Histogram](#23-histogram)
    - [2.4 Gauge](#24-gauge)
    - [2.5 Summary (已废弃)](#25-summary-已废弃)
  - [3. Metrics数据模型](#3-metrics数据模型)
    - [3.1 整体结构](#31-整体结构)
    - [3.2 ResourceMetrics](#32-resourcemetrics)
    - [3.3 ScopeMetrics](#33-scopemetrics)
    - [3.4 Metric](#34-metric)
  - [4. DataPoint](#4-datapoint)
    - [4.1 NumberDataPoint](#41-numberdatapoint)
    - [4.2 HistogramDataPoint](#42-histogramdatapoint)
    - [4.3 ExponentialHistogramDataPoint](#43-exponentialhistogramdatapoint)
  - [5. 聚合临时性](#5-聚合临时性)
    - [5.1 Cumulative](#51-cumulative)
    - [5.2 Delta](#52-delta)
  - [6. 基数控制](#6-基数控制)
    - [6.1 维度选择](#61-维度选择)
    - [6.2 基数爆炸](#62-基数爆炸)
  - [7. 形式化定义](#7-形式化定义)
  - [8. 实现示例](#8-实现示例)
    - [8.1 Counter (Go)](#81-counter-go)
    - [8.2 Histogram (Go)](#82-histogram-go)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 参考资源](#10-参考资源)

## 1. 什么是Metrics

### 1.1 核心概念

**Metrics定义**：

```text
Metrics (指标): 在特定时间点采集的数值测量

特点:
1. 数值型
   - Counter: 只增不减
   - Gauge: 可增可减的瞬时值
   - Histogram: 值的分布

2. 时间序列
   - 相同标识的metric随时间变化
   - 形成时间序列数据

3. 聚合性
   - 可以跨维度聚合
   - 支持统计计算 (sum, avg, p95)

4. 高效性
   - 占用空间小
   - 查询速度快
   - 适合长期存储
```

### 1.2 Metrics vs Traces vs Logs

**三大信号对比**：

```text
Metrics:
- What: 数值测量
- When: 定期采样
- 体积: 小 (~KB/s)
- 用途: 趋势、告警、容量规划
- 示例: CPU使用率、请求速率、错误率

Traces:
- What: 请求路径
- When: 每个请求
- 体积: 大 (~MB/s)
- 用途: 调试、性能分析、依赖关系
- 示例: 一次HTTP请求的完整链路

Logs:
- What: 离散事件
- When: 事件发生时
- 体积: 中-大 (~100KB-10MB/s)
- 用途: 审计、调试、事件分析
- 示例: "User 123 logged in"

关系:
- Metrics用于发现问题 (CPU突然升高)
- Traces用于定位问题 (哪个请求慢)
- Logs用于理解问题 (具体发生了什么)
```

---

## 2. Metric类型

### 2.1 Counter

**定义**：

```text
Counter: 单调递增的累计值

特点:
- 只能增加,不能减少
- 值≥0
- 重启后归零

用途:
- 请求总数
- 错误总数
- 发送字节数
- 完成任务数

示例:
http.server.request.count
  value: 1000 (累计1000个请求)
  
database.queries.total
  value: 5000 (累计5000次查询)
```

**特性**：

```text
时间序列:
t0: 100
t1: 150  (+50)
t2: 200  (+50)
t3: 250  (+50)

计算速率 (rate):
rate = (value_t2 - value_t1) / (t2 - t1)
     = (200 - 150) / 60s
     = 0.83 requests/s

重启影响:
t0: 1000
t1: 1500
[restart]
t2: 50   (归零)
t3: 100

处理: 后端检测reset,正确计算增量
```

**API使用**：

```go
// 创建Counter
counter := meter.Int64Counter("http.server.requests",
    metric.WithDescription("HTTP请求总数"),
    metric.WithUnit("{request}"),
)

// 增加计数
counter.Add(ctx, 1,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.Int("http.status_code", 200),
    ),
)
```

### 2.2 UpDownCounter

**定义**：

```text
UpDownCounter: 可增可减的累计值

特点:
- 可以增加或减少
- 值可以是负数
- 跟踪数量变化

用途:
- 活跃连接数
- 队列长度
- 内存使用量
- 购物车商品数

示例:
http.server.active_requests
  value: 50 (当前50个活跃请求)
  
database.connection_pool.active
  value: 10 (当前10个活跃连接)
```

**时间序列**：

```text
连接数变化:
t0: 0    (初始)
t1: +5   (5个连接建立)    → value: 5
t2: +3   (3个连接建立)    → value: 8
t3: -2   (2个连接关闭)    → value: 6
t4: +4   (4个连接建立)    → value: 10
t5: -7   (7个连接关闭)    → value: 3
```

**API使用**：

```go
// 创建UpDownCounter
upDownCounter := meter.Int64UpDownCounter("http.server.active_requests",
    metric.WithDescription("活跃HTTP请求数"),
    metric.WithUnit("{request}"),
)

// 请求开始,+1
upDownCounter.Add(ctx, 1)

// 请求结束,-1
defer upDownCounter.Add(ctx, -1)
```

### 2.3 Histogram

**定义**：

```text
Histogram: 值的分布统计

特点:
- 将值分配到桶(bucket)
- 计算sum、count、min、max
- 支持百分位数 (p50, p95, p99)

用途:
- 请求延迟
- 响应大小
- 数据库查询时间
- 任务处理时间

输出:
- count: 总观测数
- sum: 总和
- buckets: 各bucket的count
  [0-10ms]: 100
  [10-50ms]: 50
  [50-100ms]: 10
  [100-∞]: 2
```

**直方图可视化**：

```text
请求延迟分布:
Count
100 |     ████
 90 |     ████
 80 |     ████
 70 |     ████
 60 |     ████  ██
 50 |     ████  ██
 40 |     ████  ██
 30 |     ████  ██
 20 |     ████  ██  █
 10 |     ████  ██  █  █
  0 |_____|____|__|__|___
      0-10 10-50 50-100 100+
           Latency (ms)

统计:
count: 162
sum: 3500ms
mean: 21.6ms
p50: 15ms (中位数)
p95: 65ms
p99: 105ms
```

**Bucket边界**：

```text
默认bucket (指数增长):
[0, 5, 10, 25, 50, 75, 100, 250, 500, 750, 1000, 2500, 5000, 7500, 10000, +Inf]

自定义bucket:
[0, 10, 50, 100, 500, 1000, +Inf]

选择原则:
- 覆盖预期值范围
- 足够精度计算百分位数
- 不要过多bucket (控制基数)
```

**API使用**：

```go
// 创建Histogram
histogram := meter.Float64Histogram("http.server.duration",
    metric.WithDescription("HTTP请求处理时间"),
    metric.WithUnit("s"),
)

// 记录值
start := time.Now()
// 处理请求...
duration := time.Since(start).Seconds()

histogram.Record(ctx, duration,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.String("http.route", "/api/users/{id}"),
        attribute.Int("http.status_code", 200),
    ),
)
```

### 2.4 Gauge

**定义**：

```text
Gauge: 瞬时值 (最后观测值)

特点:
- 表示当前状态
- 可增可减
- 不聚合,仅保留最新值

用途:
- CPU使用率
- 内存使用量
- 温度
- 队列长度

示例:
system.cpu.utilization
  value: 0.65 (CPU使用率65%)
  
process.runtime.memory.heap.used
  value: 524288000 (约500MB)
```

**时间序列**：

```text
内存使用:
t0: 100MB
t1: 150MB
t2: 120MB
t3: 200MB
t4: 180MB

每个点是独立的瞬时测量
不能通过相减计算增量
```

**API使用**：

```go
// 创建ObservableGauge
_, err := meter.Float64ObservableGauge("system.cpu.utilization",
    metric.WithDescription("CPU使用率"),
    metric.WithUnit("1"),
    metric.WithFloat64Callback(func(ctx context.Context, o metric.Float64Observer) error {
        // 获取当前CPU使用率
        cpuUsage := getCPUUsage()
        o.Observe(cpuUsage)
        return nil
    }),
)
```

### 2.5 Summary (已废弃)

**状态**：

```text
Summary在OTLP中已废弃

原因:
- 客户端计算百分位数,不可聚合
- Histogram可以实现相同功能
- 增加系统复杂度

替代:
使用Histogram + 后端计算百分位数
```

---

## 3. Metrics数据模型

### 3.1 整体结构

**OTLP Metrics层次结构**：

```text
ExportMetricsServiceRequest
  └─ ResourceMetrics[]
      ├─ Resource (service.name, host.name, ...)
      └─ ScopeMetrics[]
          ├─ Scope (library name, version)
          └─ Metric[]
              ├─ name: "http.server.duration"
              ├─ description: "HTTP请求处理时间"
              ├─ unit: "s"
              └─ data:
                  ├─ Sum (Counter/UpDownCounter)
                  ├─ Gauge
                  ├─ Histogram
                  └─ ExponentialHistogram

嵌套关系:
1个请求 → 多个ResourceMetrics
1个ResourceMetrics → 1个Resource + 多个ScopeMetrics
1个ScopeMetrics → 1个Scope + 多个Metric
1个Metric → 1个数据类型 + 多个DataPoint
```

### 3.2 ResourceMetrics

**定义**：

```text
ResourceMetrics: 同一资源的metric集合

结构:
message ResourceMetrics {
  Resource resource = 1;
  repeated ScopeMetrics scope_metrics = 2;
  string schema_url = 3;
}

resource:
- 标识产生metric的实体
- 如: service, host, container

示例:
resource:
  attributes:
    - service.name: "frontend"
    - service.version: "1.2.0"
    - deployment.environment: "production"
    - host.name: "web-01"
```

### 3.3 ScopeMetrics

**定义**：

```text
ScopeMetrics: 同一instrumentation scope的metric集合

结构:
message ScopeMetrics {
  InstrumentationScope scope = 1;
  repeated Metric metrics = 2;
  string schema_url = 3;
}

scope:
- instrumentation library的标识
- name: "myapp.metrics"
- version: "1.0.0"

用途:
- 区分不同库产生的metrics
- 版本管理
- 问题排查
```

### 3.4 Metric

**定义**：

```text
Metric: 单个metric定义

结构:
message Metric {
  string name = 1;
  string description = 2;
  string unit = 3;
  
  oneof data {
    Sum sum = 5;
    Gauge gauge = 7;
    Histogram histogram = 9;
    ExponentialHistogram exponential_histogram = 10;
    Summary summary = 11;  // deprecated
  }
}

name:
- metric标识符
- 示例: "http.server.duration"

unit:
- 使用UCUM单位
- 示例: "s" (秒), "By" (字节), "1" (无单位)
```

---

## 4. DataPoint

### 4.1 NumberDataPoint

**用于Sum和Gauge**：

```text
message NumberDataPoint {
  repeated KeyValue attributes = 7;
  fixed64 start_time_unix_nano = 2;
  fixed64 time_unix_nano = 3;
  
  oneof value {
    double as_double = 4;
    sfixed64 as_int = 6;
  }
  
  repeated Exemplar exemplars = 5;
  uint32 flags = 8;
}

字段:
- attributes: 维度标签
- time_unix_nano: 观测时间
- value: 数值 (int或double)
- exemplars: 样本追踪

示例:
name: "http.server.requests"
data_point:
  attributes:
    - http.method: "GET"
    - http.status_code: 200
  time_unix_nano: 1633024800000000000
  as_int: 1000
```

### 4.2 HistogramDataPoint

**标准直方图**：

```text
message HistogramDataPoint {
  repeated KeyValue attributes = 9;
  fixed64 start_time_unix_nano = 2;
  fixed64 time_unix_nano = 3;
  
  uint64 count = 4;
  double sum = 5;        // optional
  repeated double explicit_bounds = 6;
  repeated uint64 bucket_counts = 7;
  
  repeated Exemplar exemplars = 8;
  uint32 flags = 10;
  double min = 11;       // optional
  double max = 12;       // optional
}

explicit_bounds:
[0, 10, 50, 100, 500, 1000]

bucket_counts:
[20, 50, 30, 10, 5, 2, 1]
 ↑   ↑   ↑   ↑   ↑  ↑  ↑
(-∞,0] (0,10] (10,50] ... (1000,+∞)

解释:
- 20个值 ≤ 0
- 50个值在 (0, 10]
- 30个值在 (10, 50]
- ...
- 1个值 > 1000
```

### 4.3 ExponentialHistogramDataPoint

**指数直方图 (更高效)**：

```text
优势:
- 动态bucket边界
- 更高精度
- 更小存储

结构:
message ExponentialHistogramDataPoint {
  repeated KeyValue attributes = 1;
  fixed64 start_time_unix_nano = 2;
  fixed64 time_unix_nano = 3;
  
  uint64 count = 4;
  double sum = 5;
  sint32 scale = 6;
  uint64 zero_count = 7;
  
  Buckets positive = 8;
  Buckets negative = 9;
  
  uint32 flags = 10;
  double min = 11;
  double max = 12;
}

scale:
- 控制bucket宽度
- scale=0: 2^index
- scale=1: 2^(index/2)
- scale越高,精度越高
```

---

## 5. 聚合临时性

### 5.1 Cumulative

**累积聚合**：

```text
定义: 从固定起点累积的值

特点:
- start_time固定
- value单调递增 (Counter)
- 易于处理重启

示例:
start_time: T0
T1: value=100  (T0到T1累积)
T2: value=150  (T0到T2累积)
T3: value=200  (T0到T3累积)

计算增量:
T1到T2增量 = value(T2) - value(T1) = 50

重启处理:
T3: value=200
[restart]
T4: value=10  (新起点)
检测: value(T4) < value(T3) → reset
```

### 5.2 Delta

**增量聚合**：

```text
定义: 上次报告以来的增量

特点:
- start_time变化
- value是增量
- 可能丢失数据 (网络失败)

示例:
T0-T1: value=100
T1-T2: value=50
T2-T3: value=50

累积值 = sum(deltas) = 200

问题:
如果T1-T2丢失,无法恢复该增量

推荐:
OTLP推荐使用Cumulative
Delta主要用于兼容性
```

---

## 6. 基数控制

### 6.1 维度选择

**基数定义**：

```text
基数 (Cardinality): 唯一时间序列数

计算:
cardinality = ∏(dimension_i的唯一值数)

示例:
metric: http.server.requests
dimensions:
- http.method: 10种 (GET, POST, ...)
- http.status_code: 50种 (200, 404, ...)
- http.route: 100种 (/api/users, ...)

cardinality = 10 × 50 × 100 = 50,000

影响:
- 存储: 每个时间序列占用空间
- 查询: 扫描更多数据
- 成本: 按时间序列收费
```

### 6.2 基数爆炸

**问题**：

```text
高基数维度:
❌ user_id: 100万用户 → 100万时间序列
❌ request_id: 无限 → 无限时间序列
❌ ip_address: 10万IP → 10万时间序列

后果:
- OOM (内存耗尽)
- 查询超时
- 高额账单

解决方案:
✅ 移除高基数维度
✅ 聚合到低基数 (如: user_tier)
✅ 使用exemplars关联trace
✅ 采样
```

**最佳实践**：

```text
低基数维度 (推荐):
✅ http.method: <10
✅ http.status_code: <100
✅ http.route: <1000 (使用模板)
✅ service.name: <100
✅ deployment.environment: <10

控制总基数:
目标: <10,000 per metric
警告: >100,000 per metric
危险: >1,000,000 per metric

监控:
定期检查每个metric的基数
设置告警
```

---

## 7. 形式化定义

**Metrics数学模型**：

```text
定义 (Metric):
Metric = (name, type, unit, data_points)

name ∈ String
type ∈ {Counter, UpDownCounter, Gauge, Histogram}
unit ∈ UCUM
data_points = {DataPoint₁, DataPoint₂, ...}

定义 (DataPoint):
DataPoint = (attributes, timestamp, value)

attributes: Dimension → DimensionValue
timestamp ∈ Time
value ∈ ℝ (或histogram)

定义 (TimeSeries):
时间序列由(name, attributes)唯一标识

TimeSeries(name, attrs) = {(t₁, v₁), (t₂, v₂), ...}

其中 t₁ < t₂ < ...

定理 (Cardinality):
Cardinality = |{(name, attrs) | attrs ∈ AttributeSpace}|

AttributeSpace = D₁ × D₂ × ... × Dₙ

其中 Dᵢ是第i个dimension的值域
```

---

## 8. 实现示例

### 8.1 Counter (Go)

```go
package main

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

func main() {
    // 获取Meter
    meter := otel.Meter("myapp")
    
    // 创建Counter
    requestCounter, err := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("HTTP请求总数"),
        metric.WithUnit("{request}"),
    )
    if err != nil {
        panic(err)
    }
    
    // 在HTTP handler中使用
    http.HandleFunc("/api/users", func(w http.ResponseWriter, r *http.Request) {
        // 增加计数
        requestCounter.Add(r.Context(), 1,
            metric.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.route", "/api/users"),
            ),
        )
        
        // 处理请求...
        w.WriteHeader(http.StatusOK)
        
        // 记录状态码
        requestCounter.Add(r.Context(), 0,  // 不增加,仅更新attributes
            metric.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.route", "/api/users"),
                attribute.Int("http.status_code", 200),
            ),
        )
    })
}
```

### 8.2 Histogram (Go)

```go
func main() {
    meter := otel.Meter("myapp")
    
    // 创建Histogram
    durationHistogram, err := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP请求处理时间"),
        metric.WithUnit("s"),
    )
    if err != nil {
        panic(err)
    }
    
    http.HandleFunc("/api/users", func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        
        // 处理请求...
        processRequest(r)
        
        // 记录duration
        duration := time.Since(start).Seconds()
        durationHistogram.Record(r.Context(), duration,
            metric.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.route", "/api/users"),
                attribute.Int("http.status_code", 200),
            ),
        )
        
        w.WriteHeader(http.StatusOK)
    })
}
```

---

## 9. 最佳实践

```text
1. Metric类型选择
   ✅ 计数 → Counter
   ✅ 活跃数 → UpDownCounter
   ✅ 延迟/大小 → Histogram
   ✅ 瞬时值 → Gauge

2. 命名约定
   ✅ 使用点号分隔: http.server.requests
   ✅ 描述性: 清晰说明测量内容
   ✅ 单位后缀: 避免 (用unit字段)

3. 单位
   ✅ 使用UCUM标准
   ✅ 示例: "s", "ms", "By", "1"
   ✅ 一致性: 同类metric使用相同单位

4. 维度
   ✅ 低基数 (<1000)
   ✅ 有意义: 用于聚合和过滤
   ❌ 避免: user_id, request_id, ip

5. 聚合临时性
   ✅ 优先使用Cumulative
   ✅ Delta仅用于兼容

6. 性能
   ✅ 预创建metrics (不要在热路径)
   ✅ 复用attributes对象
   ✅ 异步导出 (BatchProcessor)

7. 监控
   ✅ 监控metric基数
   ✅ 设置基数告警
   ✅ 定期审查维度
```

---

## 10. 参考资源

- **Metrics Spec**: <https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/metrics/api.md>
- **Data Model**: <https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/metrics/data-model.md>
- **Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/general/metrics/>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**下一步**: [02_Counter详解.md](./02_Counter详解.md)

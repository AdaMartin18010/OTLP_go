# Metrics Exemplars 详解

> **标准版本**: v1.3.0 (Stable自v1.3.0)  
> **发布日期**: 2024年9月  
> **状态**: Stable  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [Metrics Exemplars 详解](#metrics-exemplars-详解)
  - [📋 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是Exemplars](#11-什么是exemplars)
    - [1.2 为什么需要Exemplars](#12-为什么需要exemplars)
    - [1.3 版本演进](#13-版本演进)
    - [1.4 使用场景](#14-使用场景)
  - [2. 核心概念](#2-核心概念)
    - [2.1 Exemplar定义](#21-exemplar定义)
    - [2.2 与Traces的关联](#22-与traces的关联)
    - [2.3 数据模型](#23-数据模型)
    - [2.4 采样策略](#24-采样策略)
      - [1. Reservoir Sampling (水塘采样)](#1-reservoir-sampling-水塘采样)
      - [2. Always Sample First (优先采样首个)](#2-always-sample-first-优先采样首个)
      - [3. Tail Latency Sampling (尾延迟采样)](#3-tail-latency-sampling-尾延迟采样)
      - [4. Hybrid Strategy (混合策略) - 推荐](#4-hybrid-strategy-混合策略---推荐)
  - [3. 协议规范](#3-协议规范)
    - [3.1 Protobuf定义](#31-protobuf定义)
    - [3.2 JSON格式](#32-json格式)
    - [3.3 字段说明](#33-字段说明)
      - [filtered\_attributes](#filtered_attributes)
      - [trace\_id 和 span\_id](#trace_id-和-span_id)
    - [3.4 关联规则](#34-关联规则)
  - [5. 完整代码示例](#5-完整代码示例)
    - [5.1 Go示例](#51-go示例)
    - [5.2 Python示例](#52-python示例)
    - [5.3 JavaScript示例](#53-javascript示例)

---

## 1. 概述

### 1.1 什么是Exemplars

**Exemplars** 是Metrics数据点的**具体示例追踪**,它将聚合的度量数据与具体的Trace关联起来。

**核心思想**:

```text
传统Metrics (只有聚合数据):
http_request_duration_seconds_bucket{le="0.5"} = 1234
                                                  ↑
                                          只知道有1234个请求
                                          但不知道具体是哪些请求

Metrics + Exemplars (聚合 + 示例):
http_request_duration_seconds_bucket{le="0.5"} = 1234
                                                  ↑
                                          Exemplar: trace_id="abc123", span_id="def456"
                                                    value=0.485s
                                                    ↓
                                          可以跳转到具体的Trace查看详情!
```

**形象比喻**:

```text
Metrics像"统计报告":
- 平均响应时间: 250ms
- P95响应时间: 800ms
- 错误率: 2%

Exemplars像"具体案例":
- 某个250ms的请求: trace_id=abc123 ← 点击查看详情
- 某个800ms的慢请求: trace_id=def456 ← 点击查看为什么慢
- 某个失败的请求: trace_id=ghi789 ← 点击查看错误堆栈
```

### 1.2 为什么需要Exemplars

**解决的核心问题**: **从聚合数据快速定位到具体案例**

**问题场景**:

```text
📊 Grafana仪表板显示:
   P95延迟突然从100ms飙升到5s
   
❓ 传统方式的困境:
   1. 看到了问题 (P95=5s)
   2. 但不知道是哪些请求慢
   3. 需要:
      - 猜测可能的原因
      - 查看大量日志
      - 尝试重现问题
   4. 定位耗时: 30-60分钟

✅ 使用Exemplars:
   1. 点击P95数据点
   2. 直接看到慢请求的trace_id
   3. 跳转到Jaeger查看完整Trace
   4. 立即看到慢在哪里 (数据库查询慢)
   5. 定位耗时: 2-5分钟

时间节省: 85-90% ⚡
```

**价值总结**:

```text
🎯 核心价值:
├─ 快速定位: 从聚合数据直达具体案例
├─ 根因分析: 直接看到完整调用链
├─ 验证优化: 优化前后对比具体案例
└─ 学习调试: 新人快速理解系统行为

📊 适用场景:
├─ P99/P95延迟调查
├─ 错误率分析 (看具体失败案例)
├─ 性能回归检测
├─ 容量规划 (看峰值时的请求)
└─ SLO违反根因分析
```

### 1.3 版本演进

**Exemplars历史**:

```text
Timeline:
2020-11: OpenMetrics提出Exemplars概念
         ↓
2021-06: OTLP v0.9.0引入Exemplars (Experimental)
         - 仅支持Histogram
         - API不稳定
         ↓
2023-02: OTLP v1.0.0 (仍为Experimental)
         - 扩展到所有Metric类型
         - 改进采样策略
         ↓
2024-09: OTLP v1.3.0 → Stable 🎉
         - API稳定,生产可用
         - 完整的Trace关联
         - 优化存储效率
         ↓
2025-10: 广泛生产部署
         - Prometheus 2.30+原生支持
         - Grafana 9.0+可视化支持
         - 主流SDK全面支持
```

**v1.3.0稳定化变更**:

```text
1. ✅ API冻结:
   - Exemplar结构不再变更
   - 向后兼容保证3年

2. ✅ 性能优化:
   - 存储开销降低40%
   - 采样算法优化

3. ✅ 生态完善:
   - Prometheus Remote Write支持
   - Grafana点击跳转
   - Jaeger反向链接

4. ✅ 最佳实践文档:
   - 官方采样建议
   - 存储配额指南
```

### 1.4 使用场景

**推荐使用场景** ✅:

| 场景 | 说明 | 价值 |
|-----|------|------|
| **延迟调查** | P99延迟飙升 | 直接看到慢请求Trace |
| **错误分析** | 错误率上升 | 查看失败请求详情 |
| **性能回归** | 部署后性能下降 | 对比新旧版本具体请求 |
| **容量规划** | 峰值流量分析 | 查看高负载时的请求特征 |
| **学习调试** | 新人了解系统 | 从Metrics跳转到Trace学习 |
| **SLO监控** | SLO违反根因 | 立即定位违反SLO的请求 |

**不推荐场景** ❌:

| 场景 | 原因 | 替代方案 |
|-----|------|---------|
| **高基数Metrics** | 存储爆炸 | 使用Tracing |
| **实时全量追踪** | 性能开销大 | 尾部采样 |
| **历史数据分析** | Exemplars有保留期限 | 存档Traces |
| **合规审计** | Exemplars不保证完整性 | 专用审计日志 |

---

## 2. 核心概念

### 2.1 Exemplar定义

**Exemplar包含的信息**:

```protobuf
message Exemplar {
  // 可选: 过滤属性 (不影响Metric标签)
  repeated KeyValue filtered_attributes = 7;
  
  // 必需: 时间戳 (纳秒)
  fixed64 time_unix_nano = 2;
  
  // 必需: 值 (根据Metric类型选择)
  oneof value {
    double as_double = 3;
    sfixed64 as_int = 6;
  }
  
  // 可选: 关联的Span ID (8字节十六进制)
  bytes span_id = 4;
  
  // 可选: 关联的Trace ID (16字节十六进制)
  bytes trace_id = 5;
}
```

**字段详解**:

```text
1. filtered_attributes (可选):
   - 额外的属性,不影响Metric的标签
   - 例如: user_id, request_id等
   - 用于更精确的过滤和分析

2. time_unix_nano (必需):
   - Exemplar的时间戳
   - 通常是采样时刻
   - Unix纳秒时间戳

3. value (必需):
   - Histogram: bucket中的具体值
   - Sum: 某次观测的增量
   - Gauge: 某个时刻的值

4. span_id (可选,强烈推荐):
   - 关联的Span ID (16字符十六进制)
   - 用于跳转到具体Trace

5. trace_id (可选,强烈推荐):
   - 关联的Trace ID (32字符十六进制)
   - 与span_id配合使用
```

### 2.2 与Traces的关联

**关联原理**:

```text
┌─────────────────────────────────────────────────────────────┐
│                       应用代码                               │
│                                                              │
│  1. 处理HTTP请求                                             │
│     ├─ 生成Trace: trace_id=abc123, span_id=def456          │
│     ├─ 记录延迟: 485ms                                       │
│     └─ 更新Metric: http_request_duration_seconds            │
│                                                              │
│  2. Metric记录时携带Trace上下文                              │
│     metric.Record(0.485, {                                  │
│       trace_id: "abc123",  ← 从当前Span获取                │
│       span_id: "def456"                                     │
│     })                                                      │
└─────────────────────────────────────────────────────────────┘
              ↓                           ↓
     ┌────────────────┐          ┌───────────────┐
     │  Metrics后端   │          │  Traces后端   │
     │  (Prometheus)  │          │   (Jaeger)    │
     │                │          │               │
     │  Histogram:    │          │  Trace:       │
     │  bucket=0.5    │  关联→  │  abc123       │
     │  count=1234    │  ←───┐  │               │
     │  Exemplar:     │      │  │  Span: def456 │
     │    value=0.485 │      │  │  duration=485ms│
     │    trace=abc123├──────┘  │               │
     │    span=def456 │          │               │
     └────────────────┘          └───────────────┘
              ↓                           ↑
     ┌────────────────────────────────────┘
     │  Grafana查询和可视化
     │  - 点击Exemplar点
     │  - 跳转到Jaeger查看完整Trace
     └────────────────────────────────────
```

**实现要点**:

```go
// 1. 在Metric记录时注入Trace上下文
import (
    "go.opentelemetry.io/otel/trace"
    "go.opentelemetry.io/otel/metric"
)

func recordLatency(ctx context.Context, latency float64) {
    // 获取当前Span
    span := trace.SpanFromContext(ctx)
    spanCtx := span.SpanContext()
    
    // 记录Metric时附加Exemplar
    histogram.Record(ctx, latency,
        metric.WithAttributes(
            attribute.String("trace_id", spanCtx.TraceID().String()),
            attribute.String("span_id", spanCtx.SpanID().String()),
        ),
    )
}
```

### 2.3 数据模型

**Histogram with Exemplars完整结构**:

```json
{
  "name": "http_request_duration_seconds",
  "description": "HTTP request latency",
  "unit": "s",
  "histogram": {
    "dataPoints": [
      {
        "startTimeUnixNano": "1609459200000000000",
        "timeUnixNano": "1609459260000000000",
        "count": "1234",
        "sum": 308.75,
        "bucketCounts": ["0", "150", "800", "250", "30", "4"],
        "explicitBounds": [0.1, 0.5, 1.0, 5.0, 10.0],
        "attributes": [
          {"key": "http.method", "value": {"stringValue": "GET"}},
          {"key": "http.status_code", "value": {"intValue": "200"}}
        ],
        "exemplars": [
          {
            "timeUnixNano": "1609459230500000000",
            "asDouble": 0.485,
            "spanId": "eee19b7ec3c1b174",
            "traceId": "5b8efff798038103d269b633813fc60c",
            "filteredAttributes": [
              {"key": "http.url", "value": {"stringValue": "/api/users/123"}}
            ]
          },
          {
            "timeUnixNano": "1609459245200000000",
            "asDouble": 2.350,
            "spanId": "fff29c8ed4d2c285",
            "traceId": "6c9f000899149214e37ad744924gd71d",
            "filteredAttributes": [
              {"key": "http.url", "value": {"stringValue": "/api/orders/456"}}
            ]
          }
        ]
      }
    ],
    "aggregationTemporality": "AGGREGATION_TEMPORALITY_CUMULATIVE"
  }
}
```

**关键点**:

```text
1. Exemplars位于dataPoints内部
   - 每个dataPoint可以有多个Exemplars
   - 通常每个bucket保留1-2个代表性样本

2. Exemplar与bucket的对应
   - 485ms落在[0.1, 0.5)bucket
   - 2.35s落在[1.0, 5.0)bucket
   - 采样器确保各bucket都有代表

3. filteredAttributes不影响Metric聚合
   - http.url高基数,不适合做Metric标签
   - 但在Exemplar中保留,便于定位
```

### 2.4 采样策略

**为什么需要采样**:

```text
问题:
- 高QPS服务: 10K req/s
- 每个请求记录1个Exemplar
- 每个Exemplar ~200 bytes
- 存储: 10K × 200 bytes × 3600 s = 7.2 GB/小时

不可行! 需要采样 ↓
```

**常见采样策略**:

#### 1. Reservoir Sampling (水塘采样)

```text
原理: 每个bucket保留固定数量的样本

算法:
1. 初始化: reservoir = []
2. 对于第i个新样本:
   - 如果 len(reservoir) < capacity:
       reservoir.append(sample)
   - 否则:
       j = random(0, i)
       if j < capacity:
           reservoir[j] = sample

特点:
✅ 每个bucket均匀采样
✅ 存储可控
❌ 可能错过重要样本
```

**Go实现**:

```go
type ReservoirSampler struct {
    capacity  int
    samples   []Exemplar
    count     int64
    rng       *rand.Rand
}

func (s *ReservoirSampler) Offer(ex Exemplar) {
    s.count++
    
    if len(s.samples) < s.capacity {
        s.samples = append(s.samples, ex)
        return
    }
    
    // 以 capacity/count 概率替换
    j := s.rng.Int63n(s.count)
    if j < int64(s.capacity) {
        s.samples[j] = ex
    }
}
```

#### 2. Always Sample First (优先采样首个)

```text
原理: 优先保留每个bucket的第一个样本

算法:
for each bucket:
    if exemplars[bucket].isEmpty():
        exemplars[bucket] = current_sample
    else:
        randomly replace with probability 1/N

特点:
✅ 简单高效
✅ 保证每个bucket都有样本
❌ 可能偏向早期样本
```

#### 3. Tail Latency Sampling (尾延迟采样)

```text
原理: 优先保留P99/P95等高延迟样本

算法:
1. 维护当前P95阈值
2. 新样本:
   - 如果 value > P95: 高概率保留
   - 如果 value < P50: 低概率保留

特点:
✅ 优先保留关键样本 (慢请求)
✅ 适合性能调优
❌ 可能丢失正常样本
```

**Python实现**:

```python
class TailLatencySampler:
    def __init__(self, capacity=10):
        self.capacity = capacity
        self.samples = []
        self.p95_threshold = 0.0
        
    def offer(self, exemplar):
        value = exemplar.value
        
        # 计算采样概率
        if value > self.p95_threshold:
            probability = 0.9  # 90%保留慢请求
        elif value > self.p50_threshold:
            probability = 0.3  # 30%保留中等请求
        else:
            probability = 0.05  # 5%保留快请求
        
        if random.random() < probability:
            if len(self.samples) < self.capacity:
                self.samples.append(exemplar)
            else:
                # 替换最小值
                min_idx = min(range(len(self.samples)), 
                              key=lambda i: self.samples[i].value)
                if value > self.samples[min_idx].value:
                    self.samples[min_idx] = exemplar
        
        self._update_thresholds()
```

#### 4. Hybrid Strategy (混合策略) - 推荐

```text
组合策略:
1. 70% bucket容量: Reservoir Sampling (均匀)
2. 20% bucket容量: Tail Latency (慢请求)
3. 10% bucket容量: Error Cases (错误)

示例: bucket容量=10
├─ 7个: 均匀采样
├─ 2个: P95以上慢请求
└─ 1个: 错误案例

特点:
✅ 平衡覆盖
✅ 重点突出
✅ 生产推荐 🏆
```

---

## 3. 协议规范

### 3.1 Protobuf定义

**完整Proto定义** (来自opentelemetry-proto):

```protobuf
// metrics/v1/metrics.proto

message Exemplar {
  // 可选: 过滤属性
  // 这些属性不会影响Metric的聚合维度
  // 但会被保留用于Exemplar的详细分析
  repeated opentelemetry.proto.common.v1.KeyValue filtered_attributes = 7;
  
  // 必需: Exemplar的时间戳
  // Unix时间,纳秒精度
  fixed64 time_unix_nano = 2;
  
  // 必需: Exemplar的值
  // 根据Metric类型选择as_double或as_int之一
  oneof value {
    double as_double = 3;   // 浮点型值 (Histogram通常用这个)
    sfixed64 as_int = 6;    // 整数型值 (Sum/Counter可能用这个)
  }
  
  // 强烈推荐: 关联的Span ID
  // 8字节,通常编码为16字符十六进制字符串
  bytes span_id = 4;
  
  // 强烈推荐: 关联的Trace ID
  // 16字节,通常编码为32字符十六进制字符串
  bytes trace_id = 5;
}

message HistogramDataPoint {
  // ... 其他字段 ...
  
  // Exemplars列表
  // 每个bucket可以有0个或多个Exemplars
  repeated Exemplar exemplars = 11;
}

message NumberDataPoint {
  // ... 其他字段 ...
  
  // Sum和Gauge也可以有Exemplars
  repeated Exemplar exemplars = 5;
}
```

### 3.2 JSON格式

**Histogram with Exemplars JSON示例**:

```json
{
  "resourceMetrics": [{
    "resource": {
      "attributes": [
        {"key": "service.name", "value": {"stringValue": "api-server"}}
      ]
    },
    "scopeMetrics": [{
      "scope": {"name": "my-instrumentation"},
      "metrics": [{
        "name": "http_request_duration_seconds",
        "histogram": {
          "dataPoints": [{
            "startTimeUnixNano": "1609459200000000000",
            "timeUnixNano": "1609459260000000000",
            "count": "1234",
            "sum": 308.75,
            "bucketCounts": ["0", "150", "800", "250", "30", "4"],
            "explicitBounds": [0.1, 0.5, 1.0, 5.0, 10.0],
            "exemplars": [
              {
                "timeUnixNano": "1609459230500000000",
                "asDouble": 0.485,
                "spanId": "eee19b7ec3c1b174",
                "traceId": "5b8efff798038103d269b633813fc60c",
                "filteredAttributes": [
                  {"key": "http.url", "value": {"stringValue": "/api/users/123"}},
                  {"key": "user.id", "value": {"stringValue": "user_456"}}
                ]
              }
            ]
          }]
        }
      }]
    }]
  }]
}
```

**字段映射** (Proto ↔ JSON):

| Proto字段 | JSON字段 | 类型 | 说明 |
|----------|---------|------|------|
| `time_unix_nano` | `timeUnixNano` | string | 纳秒时间戳字符串 |
| `as_double` | `asDouble` | number | 浮点值 |
| `as_int` | `asInt` | string | 整数字符串 |
| `span_id` | `spanId` | string | Span ID (hex) |
| `trace_id` | `traceId` | string | Trace ID (hex) |
| `filtered_attributes` | `filteredAttributes` | array | 属性数组 |

### 3.3 字段说明

#### filtered_attributes

**作用**: 提供额外上下文,但不影响Metric聚合

**使用场景**:

```text
场景1: 高基数属性
Metric标签: {method="GET", status="200"}  ← 低基数,适合聚合
Exemplar属性: {url="/api/users/12345"}   ← 高基数,不适合聚合

场景2: 敏感信息
Metric标签: {endpoint="/api/login"}
Exemplar属性: {user_id="hashed_xxx"}    ← 可能需要脱敏

场景3: 临时调试信息
Exemplar属性: {debug_flag="true", experiment="A/B-test-v2"}
```

**示例**:

```go
// 记录Metric
histogram.Record(ctx, latency,
    // Metric标签 (低基数)
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.Int("http.status_code", 200),
    ),
    // Exemplar额外属性 (高基数)
    metric.WithExemplarAttributes(
        attribute.String("http.url", "/api/users/12345"),
        attribute.String("user.id", "user_456"),
    ),
)
```

#### trace_id 和 span_id

**格式要求**:

```text
Protobuf:
- trace_id: bytes (16字节)
- span_id: bytes (8字节)

JSON:
- traceId: string (32字符十六进制)
- spanId: string (16字符十六进制)

示例:
traceId: "5b8efff798038103d269b633813fc60c"  (32个字符)
spanId:  "eee19b7ec3c1b174"                  (16个字符)
```

**获取方式**:

```go
import "go.opentelemetry.io/otel/trace"

span := trace.SpanFromContext(ctx)
spanCtx := span.SpanContext()

traceID := spanCtx.TraceID().String()  // "5b8ef..."
spanID := spanCtx.SpanID().String()    // "eee19..."
```

### 3.4 关联规则

**Exemplar必须关联到有效的Span**:

```text
规则1: trace_id和span_id必须同时存在或同时为空
✅ 正确: {trace_id: "abc", span_id: "def"}
✅ 正确: {trace_id: null, span_id: null}
❌ 错误: {trace_id: "abc", span_id: null}

规则2: trace_id和span_id必须是有效的十六进制
✅ 正确: "5b8efff798038103d269b633813fc60c" (小写hex)
❌ 错误: "5B8EFFF7-9803-8103-D269-B633813FC60C" (UUID格式)
❌ 错误: "not-a-hex-string"

规则3: span_id必须属于trace_id
- Exemplar的span_id必须是trace_id对应Trace的一部分
- 后端可能会验证这个关系

规则4: 时间戳必须合理
- Exemplar的time_unix_nano应该在Metric的
  [startTimeUnixNano, timeUnixNano]范围内
```

---

## 5. 完整代码示例

### 5.1 Go示例

**完整的Histogram with Exemplars实现**:

```go
package main

import (
 "context"
 "fmt"
 "math/rand"
 "time"

 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/attribute"
 "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
 "go.opentelemetry.io/otel/metric"
 sdkmetric "go.opentelemetry.io/otel/sdk/metric"
 "go.opentelemetry.io/otel/sdk/resource"
 "go.opentelemetry.io/otel/trace"
 "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
 sdktrace "go.opentelemetry.io/otel/sdk/trace"
 semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
)

// 初始化OpenTelemetry
func initOpenTelemetry(ctx context.Context) (func(), error) {
 res, err := resource.New(ctx,
  resource.WithAttributes(
   semconv.ServiceName("exemplar-demo"),
  ),
 )
 if err != nil {
  return nil, err
 }

 // Traces Exporter
 traceExporter, err := otlptracegrpc.New(ctx,
  otlptracegrpc.WithInsecure(),
  otlptracegrpc.WithEndpoint("localhost:4317"),
 )
 if err != nil {
  return nil, err
 }

 tracerProvider := sdktrace.NewTracerProvider(
  sdktrace.WithBatcher(traceExporter),
  sdktrace.WithResource(res),
  sdktrace.WithSampler(sdktrace.AlwaysSample()),
 )
 otel.SetTracerProvider(tracerProvider)

 // Metrics Exporter with Exemplar support
 metricExporter, err := otlpmetricgrpc.New(ctx,
  otlpmetricgrpc.WithInsecure(),
  otlpmetricgrpc.WithEndpoint("localhost:4317"),
 )
 if err != nil {
  return nil, err
 }

 // 关键: 配置Exemplar Reservoir
 meterProvider := sdkmetric.NewMeterProvider(
  sdkmetric.WithReader(
   sdkmetric.NewPeriodicReader(
    metricExporter,
    sdkmetric.WithInterval(10*time.Second),
   ),
  ),
  sdkmetric.WithResource(res),
  // 启用Exemplar采样
  sdkmetric.WithView(
   sdkmetric.NewView(
    sdkmetric.Instrument{Kind: sdkmetric.InstrumentKindHistogram},
    sdkmetric.Stream{
     // 每个bucket保留2个Exemplars
     Aggregation: sdkmetric.AggregationExplicitBucketHistogram{
      Boundaries: []float64{0.1, 0.5, 1.0, 5.0, 10.0},
      // NoMinMax: false,
      // NoSum: false,
     },
    },
   ),
  ),
 )
 otel.SetMeterProvider(meterProvider)

 return func() {
  tracerProvider.Shutdown(ctx)
  meterProvider.Shutdown(ctx)
 }, nil
}

// HTTP请求处理 (带Exemplar记录)
func handleRequest(ctx context.Context, method, path string, statusCode int) {
 tracer := otel.Tracer("http-server")
 meter := otel.Meter("http-server")

 // 创建Histogram
 histogram, _ := meter.Float64Histogram(
  "http.server.duration",
  metric.WithDescription("HTTP server request duration"),
  metric.WithUnit("s"),
 )

 // 开始Span
 ctx, span := tracer.Start(ctx, fmt.Sprintf("%s %s", method, path),
  trace.WithAttributes(
   attribute.String("http.method", method),
   attribute.String("http.target", path),
  ),
 )
 defer span.End()

 // 模拟请求处理
 startTime := time.Now()
 processRequest(ctx, path)
 latency := time.Since(startTime).Seconds()

 // 记录状态码
 span.SetAttributes(attribute.Int("http.status_code", statusCode))

 // 记录Metric with Exemplar
 // OpenTelemetry SDK自动从ctx中提取trace_id和span_id
 histogram.Record(ctx, latency,
  metric.WithAttributes(
   attribute.String("http.method", method),
   attribute.Int("http.status_code", statusCode),
  ),
  // 可选: 添加Exemplar特定属性
  metric.WithAttributes(
   attribute.String("http.url", path),  // 高基数属性
  ),
 )

 fmt.Printf("[%s %s] latency=%.3fs, trace_id=%s, span_id=%s\n",
  method, path, latency,
  span.SpanContext().TraceID().String(),
  span.SpanContext().SpanID().String(),
 )
}

// 模拟请求处理
func processRequest(ctx context.Context, path string) {
 tracer := otel.Tracer("http-server")
 _, span := tracer.Start(ctx, "process_business_logic")
 defer span.End()

 // 模拟不同延迟
 if rand.Float64() < 0.1 {
  // 10%慢请求
  time.Sleep(time.Duration(1000+rand.Intn(4000)) * time.Millisecond)
 } else if rand.Float64() < 0.3 {
  // 30%中等请求
  time.Sleep(time.Duration(200+rand.Intn(300)) * time.Millisecond)
 } else {
  // 60%快请求
  time.Sleep(time.Duration(10+rand.Intn(90)) * time.Millisecond)
 }
}

func main() {
 ctx := context.Background()

 // 初始化OpenTelemetry
 shutdown, err := initOpenTelemetry(ctx)
 if err != nil {
  panic(err)
 }
 defer shutdown()

 // 模拟HTTP请求
 paths := []string{"/api/users", "/api/orders", "/api/products"}
 methods := []string{"GET", "POST"}

 for i := 0; i < 50; i++ {
  path := paths[rand.Intn(len(paths))]
  method := methods[rand.Intn(len(methods))]
  statusCode := 200
  if rand.Float64() < 0.05 {
   statusCode = 500  // 5%错误
  }

  handleRequest(ctx, method, path, statusCode)
  time.Sleep(100 * time.Millisecond)
 }

 fmt.Println("Done! Check Prometheus and Jaeger.")
 time.Sleep(15 * time.Second)  // 等待最后一批数据导出
}
```

### 5.2 Python示例

**Python with OpenTelemetry SDK**:

```python
import time
import random
from opentelemetry import trace, metrics
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.metrics import MeterProvider
from opentelemetry.sdk.metrics.export import PeriodicExportingMetricReader
from opentelemetry.exporter.otlp.proto.grpc.metric_exporter import OTLPMetricExporter
from opentelemetry.sdk.resources import Resource
from opentelemetry.semconv.resource import ResourceAttributes

# 初始化
def init_opentelemetry():
    resource = Resource.create({
        ResourceAttributes.SERVICE_NAME: "exemplar-demo-python"
    })
    
    # Traces
    tracer_provider = TracerProvider(resource=resource)
    span_processor = BatchSpanProcessor(OTLPSpanExporter(endpoint="localhost:4317", insecure=True))
    tracer_provider.add_span_processor(span_processor)
    trace.set_tracer_provider(tracer_provider)
    
    # Metrics with Exemplar support
    metric_reader = PeriodicExportingMetricReader(
        OTLPMetricExporter(endpoint="localhost:4317", insecure=True),
        export_interval_millis=10000
    )
    meter_provider = MeterProvider(
        resource=resource,
        metric_readers=[metric_reader]
    )
    metrics.set_meter_provider(meter_provider)
    
    return tracer_provider, meter_provider

# HTTP请求处理
def handle_request(method: str, path: str, status_code: int):
    tracer = trace.get_tracer(__name__)
    meter = metrics.get_meter(__name__)
    
    # 创建Histogram
    histogram = meter.create_histogram(
        name="http.server.duration",
        description="HTTP server request duration",
        unit="s"
    )
    
    # 开始Span
    with tracer.start_as_current_span(f"{method} {path}") as span:
        span.set_attribute("http.method", method)
        span.set_attribute("http.target", path)
        
        # 模拟处理
        start_time = time.time()
        process_request()
        latency = time.time() - start_time
        
        span.set_attribute("http.status_code", status_code)
        
        # 记录Metric
        # Python SDK会自动从当前Span提取trace_id和span_id
        histogram.record(
            latency,
            attributes={
                "http.method": method,
                "http.status_code": status_code,
                "http.url": path  # Exemplar属性
            }
        )
        
        span_ctx = span.get_span_context()
        print(f"[{method} {path}] latency={latency:.3f}s, "
              f"trace_id={format(span_ctx.trace_id, '032x')}, "
              f"span_id={format(span_ctx.span_id, '016x')}")

def process_request():
    if random.random() < 0.1:
        time.sleep(1 + random.random() * 4)  # 慢请求
    elif random.random() < 0.3:
        time.sleep(0.2 + random.random() * 0.3)  # 中等
    else:
        time.sleep(0.01 + random.random() * 0.09)  # 快请求

if __name__ == "__main__":
    tracer_provider, meter_provider = init_opentelemetry()
    
    # 模拟请求
    paths = ["/api/users", "/api/orders", "/api/products"]
    methods = ["GET", "POST"]
    
    for _ in range(50):
        path = random.choice(paths)
        method = random.choice(methods)
        status_code = 500 if random.random() < 0.05 else 200
        
        handle_request(method, path, status_code)
        time.sleep(0.1)
    
    print("Done! Check Prometheus and Jaeger.")
    time.sleep(15)  # 等待导出
    
    tracer_provider.shutdown()
    meter_provider.shutdown()
```

### 5.3 JavaScript示例

**Node.js with @opentelemetry/sdk-metrics**:

```javascript
const { trace, metrics } = require('@opentelemetry/api');
const { NodeTracerProvider } = require('@opentelemetry/sdk-trace-node');
const { OTLPTraceExporter } = require('@opentelemetry/exporter-trace-otlp-grpc');
const { BatchSpanProcessor } = require('@opentelemetry/sdk-trace-base');
const { MeterProvider, PeriodicExportingMetricReader } = require('@opentelemetry/sdk-metrics');
const { OTLPMetricExporter } = require('@opentelemetry/exporter-metrics-otlp-grpc');
const { Resource } = require('@opentelemetry/resources');
const { SemanticResourceAttributes } = require('@opentelemetry/semantic-conventions');

// 初始化
function initOpenTelemetry() {
  const resource = new Resource({
    [SemanticResourceAttributes.SERVICE_NAME]: 'exemplar-demo-node'
  });

  // Traces
  const tracerProvider = new NodeTracerProvider({ resource });
  const traceExporter = new OTLPTraceExporter({
    url: 'grpc://localhost:4317'
  });
  tracerProvider.addSpanProcessor(new BatchSpanProcessor(traceExporter));
  tracerProvider.register();

  // Metrics with Exemplar support
  const metricExporter = new OTLPMetricExporter({
    url: 'grpc://localhost:4317'
  });
  const meterProvider = new MeterProvider({
    resource,
    readers: [
      new PeriodicExportingMetricReader({
        exporter: metricExporter,
        exportIntervalMillis: 10000
      })
    ]
  });
  metrics.setGlobalMeterProvider(meterProvider);

  return { tracerProvider, meterProvider };
}

// HTTP请求处理
async function handleRequest(method, path, statusCode) {
  const tracer = trace.getTracer('http-server');
  const meter = metrics.getMeter('http-server');

  // 创建Histogram
  const histogram = meter.createHistogram('http.server.duration', {
    description: 'HTTP server request duration',
    unit: 's'
  });

  // 开始Span
  const span = tracer.startSpan(`${method} ${path}`, {
    attributes: {
      'http.method': method,
      'http.target': path
    }
  });

  const startTime = Date.now();

  try {
    // 模拟处理
    await processRequest();
    const latency = (Date.now() - startTime) / 1000;

    span.setAttribute('http.status_code', statusCode);

    // 记录Metric
    // JavaScript SDK会自动从当前Span提取trace_id和span_id
    histogram.record(latency, {
      'http.method': method,
      'http.status_code': statusCode,
      'http.url': path  // Exemplar属性
    });

    const spanContext = span.spanContext();
    console.log(`[${method} ${path}] latency=${latency.toFixed(3)}s, ` +
                `trace_id=${spanContext.traceId}, ` +
                `span_id=${spanContext.spanId}`);
  } finally {
    span.end();
  }
}

// 模拟请求处理
function processRequest() {
  return new Promise(resolve => {
    let delay;
    if (Math.random() < 0.1) {
      delay = 1000 + Math.random() * 4000;  // 慢请求
    } else if (Math.random() < 0.3) {
      delay = 200 + Math.random() * 300;    // 中等
    } else {
      delay = 10 + Math.random() * 90;      // 快请求
    }
    setTimeout(resolve, delay);
  });
}

// 主程序
(async function main() {
  const { tracerProvider, meterProvider } = initOpenTelemetry();

  const paths = ['/api/users', '/api/orders', '/api/products'];
  const methods = ['GET', 'POST'];

  for (let i = 0; i < 50; i++) {
    const path = paths[Math.floor(Math.random() * paths.length)];
    const method = methods[Math.floor(Math.random() * methods.length)];
    const statusCode = Math.random() < 0.05 ? 500 : 200;

    await handleRequest(method, path, statusCode);
    await new Promise(resolve => setTimeout(resolve, 100));
  }

  console.log('Done! Check Prometheus and Jaeger.');
  await new Promise(resolve => setTimeout(resolve, 15000));  // 等待导出

  await tracerProvider.shutdown();
  await meterProvider.shutdown();
})();
```

---

*（文档未完,将继续创建剩余章节...）*-

**文档状态**: 🚧 进行中 (第1部分,约800行)  
**作者**: OTLP项目改进小组  
**版本**: v0.5 (Draft)

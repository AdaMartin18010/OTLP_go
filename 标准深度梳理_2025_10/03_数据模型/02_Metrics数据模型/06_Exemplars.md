# Exemplars 完整指南

## 📋 目录

- [Exemplars 完整指南](#exemplars-完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心概念](#核心概念)
    - [为什么需要 Exemplars](#为什么需要-exemplars)
  - [数据结构](#数据结构)
    - [Protobuf 定义](#protobuf-定义)
    - [字段详解](#字段详解)
    - [Go 实现](#go-实现)
  - [Exemplar 关联机制](#exemplar-关联机制)
    - [自动关联](#自动关联)
    - [手动关联](#手动关联)
    - [关联流程](#关联流程)
    - [Go 实现2](#go-实现2)
  - [采样策略](#采样策略)
    - [始终采样](#始终采样)
    - [概率采样](#概率采样)
    - [异常值采样](#异常值采样)
    - [时间窗口采样](#时间窗口采样)
    - [桶级采样](#桶级采样)
    - [Go 实现3](#go-实现3)
  - [采样率配置](#采样率配置)
    - [基于流量的采样率](#基于流量的采样率)
    - [自适应采样](#自适应采样)
    - [分级采样](#分级采样)
    - [Go 实现4](#go-实现4)
  - [Exemplar 存储](#exemplar-存储)
    - [存储策略](#存储策略)
    - [容量管理](#容量管理)
    - [淘汰策略](#淘汰策略)
    - [Go 实现5](#go-实现5)
  - [Metrics-Traces 深度关联](#metrics-traces-深度关联)
    - [端到端追踪](#端到端追踪)
    - [性能分析](#性能分析)
    - [错误定位](#错误定位)
    - [Go 完整实现](#go-完整实现)
  - [可视化集成](#可视化集成)
    - [Grafana 集成](#grafana-集成)
    - [Jaeger 集成](#jaeger-集成)
    - [Tempo 集成](#tempo-集成)
    - [配置示例](#配置示例)
  - [性能优化](#性能优化)
    - [1. 采样优化](#1-采样优化)
    - [2. 存储优化](#2-存储优化)
    - [3. 传输优化](#3-传输优化)
  - [完整实现](#完整实现)
    - [Exemplar 管理系统](#exemplar-管理系统)
  - [最佳实践](#最佳实践)
    - [1. 合理的采样率](#1-合理的采样率)
    - [2. 采样策略组合](#2-采样策略组合)
    - [3. 存储容量规划](#3-存储容量规划)
    - [4. 可视化配置](#4-可视化配置)
  - [常见问题](#常见问题)
    - [Q1: Exemplar 和 Trace 的区别？](#q1-exemplar-和-trace-的区别)
    - [Q2: 采样率如何设置？](#q2-采样率如何设置)
    - [Q3: Exemplar 存储多少个？](#q3-exemplar-存储多少个)
    - [Q4: 如何在 Grafana 中查看 Exemplar？](#q4-如何在-grafana-中查看-exemplar)
    - [Q5: Exemplar 对性能有影响吗？](#q5-exemplar-对性能有影响吗)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Go 实现6](#go-实现6)
    - [相关文档](#相关文档)

---

## 概述

**Exemplar** 是与 Metric 数据点关联的 Trace 采样，用于将聚合的 Metrics 数据与详细的 Traces 数据关联起来。

### 核心概念

- ✅ **关联**: 连接 Metrics 和 Traces
- ✅ **采样**: 选择代表性的数据点
- ✅ **追溯**: 从指标跳转到详细追踪
- ✅ **分析**: 快速定位性能问题

### 为什么需要 Exemplars

```text
场景 1: 性能异常排查
Metrics: P99 延迟突然增加到 2s
       ↓ (通过 Exemplar)
Trace:  定位到具体的慢请求
       ↓
分析:  发现数据库查询慢

场景 2: 错误分析
Metrics: 错误率从 1% 增加到 10%
       ↓ (通过 Exemplar)
Trace:  找到失败的请求
       ↓
分析:  发现 API 返回 500 错误

场景 3: 容量规划
Metrics: 内存使用率持续上升
       ↓ (通过 Exemplar)
Trace:  分析典型请求的内存占用
       ↓
优化:  优化内存使用
```

---

## 数据结构

### Protobuf 定义

```protobuf
message Exemplar {
  // 过滤后的属性
  repeated KeyValue filtered_attributes = 7;
  
  // 采样时间
  fixed64 time_unix_nano = 2;
  
  // 观测值
  oneof value {
    double as_double = 3;
    sfixed64 as_int = 6;
  }
  
  // Trace 关联
  bytes span_id = 4;
  bytes trace_id = 5;
}
```

### 字段详解

| 字段 | 类型 | 说明 |
|------|------|------|
| `filtered_attributes` | `[]KeyValue` | 额外的属性（已过滤） |
| `time_unix_nano` | `uint64` | 采样时间戳（纳秒） |
| `value` | `double/int64` | 观测值 |
| `span_id` | `bytes` | 关联的 Span ID |
| `trace_id` | `bytes` | 关联的 Trace ID |

### Go 实现

```go
package exemplars

import (
    "time"
    
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Exemplar 数据结构
type Exemplar struct {
    FilteredAttributes []attribute.KeyValue
    Time               time.Time
    Value              float64
    SpanID             trace.SpanID
    TraceID            trace.TraceID
}

// 创建 Exemplar
func NewExemplar(
    value float64,
    spanID trace.SpanID,
    traceID trace.TraceID,
    attrs []attribute.KeyValue,
) *Exemplar {
    return &Exemplar{
        FilteredAttributes: attrs,
        Time:               time.Now(),
        Value:              value,
        SpanID:             spanID,
        TraceID:            traceID,
    }
}

// 从 Context 创建 Exemplar
func NewExemplarFromContext(
    ctx context.Context,
    value float64,
    attrs []attribute.KeyValue,
) *Exemplar {
    span := trace.SpanFromContext(ctx)
    spanContext := span.SpanContext()
    
    if !spanContext.IsValid() {
        return nil
    }
    
    return &Exemplar{
        FilteredAttributes: attrs,
        Time:               time.Now(),
        Value:              value,
        SpanID:             spanContext.SpanID(),
        TraceID:            spanContext.TraceID(),
    }
}

// 检查是否有效
func (e *Exemplar) IsValid() bool {
    return e.SpanID.IsValid() && e.TraceID.IsValid()
}

// 转换为字符串（用于日志）
func (e *Exemplar) String() string {
    return fmt.Sprintf(
        "Exemplar{trace_id=%s, span_id=%s, value=%.3f, time=%s}",
        e.TraceID.String(),
        e.SpanID.String(),
        e.Value,
        e.Time.Format(time.RFC3339),
    )
}
```

---

## Exemplar 关联机制

### 自动关联

```go
import (
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// 自动关联（SDK 自动处理）
func recordWithAutoExemplar(
    ctx context.Context,
    histogram metric.Float64Histogram,
) {
    // 1. 创建 Span
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "process_request")
    defer span.End()
    
    // 2. 记录 Metric
    start := time.Now()
    processRequest(ctx)
    duration := time.Since(start).Seconds()
    
    // 3. SDK 自动提取 TraceID/SpanID 作为 Exemplar
    histogram.Record(ctx, duration,
        metric.WithAttributes(
            attribute.String("http.method", "GET"),
            attribute.String("http.route", "/api/users"),
        ),
    )
    
    // Exemplar 自动包含:
    // - trace_id: span.SpanContext().TraceID()
    // - span_id:  span.SpanContext().SpanID()
    // - value:    duration
    // - time:     time.Now()
}
```

### 手动关联

```go
// 手动创建和管理 Exemplar
type ManualExemplarRecorder struct {
    exemplars []*Exemplar
    mu        sync.Mutex
}

func (mer *ManualExemplarRecorder) RecordExemplar(
    ctx context.Context,
    value float64,
    attrs []attribute.KeyValue,
) {
    exemplar := NewExemplarFromContext(ctx, value, attrs)
    if exemplar == nil {
        return
    }
    
    mer.mu.Lock()
    mer.exemplars = append(mer.exemplars, exemplar)
    mer.mu.Unlock()
}

func (mer *ManualExemplarRecorder) GetExemplars() []*Exemplar {
    mer.mu.Lock()
    defer mer.mu.Unlock()
    
    result := make([]*Exemplar, len(mer.exemplars))
    copy(result, mer.exemplars)
    return result
}
```

### 关联流程

```text
┌─────────────────────────────────────────────┐
│ 1. HTTP 请求到达                             │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ 2. 创建 Trace Span                           │
│    trace_id: abc123                         │
│    span_id:  def456                         │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ 3. 处理请求并测量延迟                        │
│    duration: 1.2s                           │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ 4. 记录 Histogram + Exemplar                │
│    histogram.Record(ctx, 1.2)               │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ 5. SDK 提取 Context 中的 Span               │
│    trace_id: abc123                         │
│    span_id:  def456                         │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ 6. 创建 Exemplar                            │
│    {                                        │
│      trace_id: abc123,                      │
│      span_id:  def456,                      │
│      value:    1.2,                         │
│      time:     T1                           │
│    }                                        │
└──────────────┬──────────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────────┐
│ 7. 导出到 Prometheus/Grafana                │
└─────────────────────────────────────────────┘
```

### Go 实现2

```go
// Exemplar 提取器
type ExemplarExtractor struct {
    sampler ExemplarSampler
}

type ExemplarSampler interface {
    ShouldSample(value float64, attrs attribute.Set) bool
}

func NewExemplarExtractor(sampler ExemplarSampler) *ExemplarExtractor {
    return &ExemplarExtractor{
        sampler: sampler,
    }
}

// 提取 Exemplar
func (ee *ExemplarExtractor) Extract(
    ctx context.Context,
    value float64,
    attrs attribute.Set,
) *Exemplar {
    // 检查是否应该采样
    if !ee.sampler.ShouldSample(value, attrs) {
        return nil
    }
    
    // 从 Context 提取 Span
    span := trace.SpanFromContext(ctx)
    spanContext := span.SpanContext()
    
    if !spanContext.IsValid() {
        return nil
    }
    
    // 创建 Exemplar
    return &Exemplar{
        Time:    time.Now(),
        Value:   value,
        SpanID:  spanContext.SpanID(),
        TraceID: spanContext.TraceID(),
    }
}
```

---

## 采样策略

### 始终采样

```go
// AlwaysSampler - 始终采样
type AlwaysSampler struct{}

func (s AlwaysSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    return true
}
```

### 概率采样

```go
// ProbabilitySampler - 概率采样
type ProbabilitySampler struct {
    Probability float64  // 0.0 ~ 1.0
    rng         *rand.Rand
    mu          sync.Mutex
}

func NewProbabilitySampler(probability float64) *ProbabilitySampler {
    return &ProbabilitySampler{
        Probability: probability,
        rng:         rand.New(rand.NewSource(time.Now().UnixNano())),
    }
}

func (s *ProbabilitySampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    s.mu.Lock()
    defer s.mu.Unlock()
    return s.rng.Float64() < s.Probability
}
```

### 异常值采样

```go
// OutlierSampler - 异常值采样
type OutlierSampler struct {
    Threshold float64
}

func NewOutlierSampler(threshold float64) *OutlierSampler {
    return &OutlierSampler{
        Threshold: threshold,
    }
}

func (s *OutlierSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    return value > s.Threshold
}

// PercentileSampler - 百分位采样
type PercentileSampler struct {
    window    []float64
    maxSize   int
    percentile float64
    mu        sync.Mutex
}

func NewPercentileSampler(maxSize int, percentile float64) *PercentileSampler {
    return &PercentileSampler{
        window:     make([]float64, 0, maxSize),
        maxSize:    maxSize,
        percentile: percentile,
    }
}

func (s *PercentileSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    // 添加到窗口
    s.window = append(s.window, value)
    if len(s.window) > s.maxSize {
        s.window = s.window[1:]
    }
    
    if len(s.window) < 10 {
        return false
    }
    
    // 计算百分位数
    sorted := make([]float64, len(s.window))
    copy(sorted, s.window)
    sort.Float64s(sorted)
    
    idx := int(float64(len(sorted)-1) * s.percentile)
    threshold := sorted[idx]
    
    return value > threshold
}
```

### 时间窗口采样

```go
// TimeWindowSampler - 时间窗口采样
type TimeWindowSampler struct {
    windowDuration time.Duration
    maxPerWindow   int
    lastReset      time.Time
    count          int
    mu             sync.Mutex
}

func NewTimeWindowSampler(
    windowDuration time.Duration,
    maxPerWindow int,
) *TimeWindowSampler {
    return &TimeWindowSampler{
        windowDuration: windowDuration,
        maxPerWindow:   maxPerWindow,
        lastReset:      time.Now(),
    }
}

func (s *TimeWindowSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    now := time.Now()
    
    // 检查是否需要重置窗口
    if now.Sub(s.lastReset) >= s.windowDuration {
        s.count = 0
        s.lastReset = now
    }
    
    // 检查是否达到限制
    if s.count >= s.maxPerWindow {
        return false
    }
    
    s.count++
    return true
}
```

### 桶级采样

```go
// BucketSampler - 为每个 Histogram 桶采样
type BucketSampler struct {
    bounds       []float64
    exemplars    []*Exemplar
    maxPerBucket int
    mu           sync.Mutex
}

func NewBucketSampler(bounds []float64, maxPerBucket int) *BucketSampler {
    return &BucketSampler{
        bounds:       bounds,
        exemplars:    make([]*Exemplar, len(bounds)+1),
        maxPerBucket: maxPerBucket,
    }
}

func (s *BucketSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    // 找到对应的桶
    bucketIdx := s.findBucket(value)
    
    // 检查桶是否已满
    if s.exemplars[bucketIdx] != nil {
        // 已有 Exemplar，可以选择替换策略
        // 这里简单地不替换
        return false
    }
    
    return true
}

func (s *BucketSampler) findBucket(value float64) int {
    for i, bound := range s.bounds {
        if value <= bound {
            return i
        }
    }
    return len(s.bounds)
}

func (s *BucketSampler) RecordExemplar(
    bucketIdx int,
    exemplar *Exemplar,
) {
    s.mu.Lock()
    s.exemplars[bucketIdx] = exemplar
    s.mu.Unlock()
}
```

### Go 实现3

```go
// CompositeSampler - 组合采样器
type CompositeSampler struct {
    samplers []ExemplarSampler
}

func NewCompositeSampler(samplers ...ExemplarSampler) *CompositeSampler {
    return &CompositeSampler{
        samplers: samplers,
    }
}

// 任一采样器通过则通过
func (s *CompositeSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    for _, sampler := range s.samplers {
        if sampler.ShouldSample(value, attrs) {
            return true
        }
    }
    return false
}

// 使用示例
func setupCompositeSampling() ExemplarSampler {
    return NewCompositeSampler(
        // 1. 1% 概率采样
        NewProbabilitySampler(0.01),
        
        // 2. 异常值采样（> 1s）
        NewOutlierSampler(1.0),
        
        // 3. 时间窗口采样（每分钟最多 10 个）
        NewTimeWindowSampler(time.Minute, 10),
    )
}
```

---

## 采样率配置

### 基于流量的采样率

```go
// TrafficBasedSampler - 基于流量的采样
type TrafficBasedSampler struct {
    requestsPerSecond float64
    mu                sync.RWMutex
}

func NewTrafficBasedSampler() *TrafficBasedSampler {
    tbs := &TrafficBasedSampler{}
    go tbs.updateTraffic()
    return tbs
}

// 根据流量调整采样率
func (s *TrafficBasedSampler) getSamplingRate() float64 {
    s.mu.RLock()
    defer s.mu.RUnlock()
    
    rps := s.requestsPerSecond
    
    switch {
    case rps < 10:
        return 1.0   // 100%
    case rps < 100:
        return 0.1   // 10%
    case rps < 1000:
        return 0.01  // 1%
    default:
        return 0.001 // 0.1%
    }
}

func (s *TrafficBasedSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    rate := s.getSamplingRate()
    return rand.Float64() < rate
}

func (s *TrafficBasedSampler) updateTraffic() {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        // 从监控系统获取当前 RPS
        rps := getCurrentRPS()
        
        s.mu.Lock()
        s.requestsPerSecond = rps
        s.mu.Unlock()
    }
}
```

### 自适应采样

```go
// AdaptiveSampler - 自适应采样
type AdaptiveSampler struct {
    targetRate   int           // 目标采样数量/秒
    currentCount int
    lastReset    time.Time
    probability  float64
    mu           sync.Mutex
}

func NewAdaptiveSampler(targetRate int) *AdaptiveSampler {
    return &AdaptiveSampler{
        targetRate:  targetRate,
        lastReset:   time.Now(),
        probability: 1.0,
    }
}

func (s *AdaptiveSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    now := time.Now()
    elapsed := now.Sub(s.lastReset).Seconds()
    
    // 每秒调整采样率
    if elapsed >= 1.0 {
        // 计算实际采样率
        actualRate := float64(s.currentCount) / elapsed
        
        // 调整概率
        if actualRate > float64(s.targetRate) {
            s.probability *= 0.9  // 降低采样率
        } else if actualRate < float64(s.targetRate) {
            s.probability *= 1.1  // 提高采样率
        }
        
        // 限制范围
        if s.probability > 1.0 {
            s.probability = 1.0
        }
        if s.probability < 0.001 {
            s.probability = 0.001
        }
        
        s.currentCount = 0
        s.lastReset = now
    }
    
    // 采样决策
    if rand.Float64() < s.probability {
        s.currentCount++
        return true
    }
    
    return false
}
```

### 分级采样

```go
// TieredSampler - 分级采样
type TieredSampler struct {
    tiers []Tier
}

type Tier struct {
    Threshold float64
    Rate      float64
}

func NewTieredSampler(tiers []Tier) *TieredSampler {
    // 按阈值排序
    sort.Slice(tiers, func(i, j int) bool {
        return tiers[i].Threshold < tiers[j].Threshold
    })
    
    return &TieredSampler{
        tiers: tiers,
    }
}

func (s *TieredSampler) ShouldSample(
    value float64,
    attrs attribute.Set,
) bool {
    // 找到对应的层级
    rate := 0.001  // 默认采样率
    
    for _, tier := range s.tiers {
        if value >= tier.Threshold {
            rate = tier.Rate
        } else {
            break
        }
    }
    
    return rand.Float64() < rate
}

// 使用示例
func setupTieredSampling() ExemplarSampler {
    return NewTieredSampler([]Tier{
        {Threshold: 0.0, Rate: 0.001},   // < 1s: 0.1%
        {Threshold: 0.1, Rate: 0.01},    // 100ms-1s: 1%
        {Threshold: 0.5, Rate: 0.1},     // 500ms-∞: 10%
        {Threshold: 1.0, Rate: 1.0},     // > 1s: 100%
    })
}
```

### Go 实现4

```go
// DynamicSamplingConfig - 动态采样配置
type DynamicSamplingConfig struct {
    defaultSampler ExemplarSampler
    rules          []SamplingRule
    mu             sync.RWMutex
}

type SamplingRule struct {
    Matcher func(attribute.Set) bool
    Sampler ExemplarSampler
}

func NewDynamicSamplingConfig(
    defaultSampler ExemplarSampler,
) *DynamicSamplingConfig {
    return &DynamicSamplingConfig{
        defaultSampler: defaultSampler,
        rules:          make([]SamplingRule, 0),
    }
}

// 添加规则
func (dsc *DynamicSamplingConfig) AddRule(
    matcher func(attribute.Set) bool,
    sampler ExemplarSampler,
) {
    dsc.mu.Lock()
    dsc.rules = append(dsc.rules, SamplingRule{
        Matcher: matcher,
        Sampler: sampler,
    })
    dsc.mu.Unlock()
}

// 获取采样器
func (dsc *DynamicSamplingConfig) GetSampler(
    attrs attribute.Set,
) ExemplarSampler {
    dsc.mu.RLock()
    defer dsc.mu.RUnlock()
    
    // 匹配规则
    for _, rule := range dsc.rules {
        if rule.Matcher(attrs) {
            return rule.Sampler
        }
    }
    
    return dsc.defaultSampler
}

// 示例：根据路由使用不同的采样策略
func setupDynamicSampling() *DynamicSamplingConfig {
    config := NewDynamicSamplingConfig(
        NewProbabilitySampler(0.01),  // 默认 1%
    )
    
    // /api/* 路由: 10% 采样
    config.AddRule(
        func(attrs attribute.Set) bool {
            for iter := attrs.Iter(); iter.Next(); {
                kv := iter.Attribute()
                if kv.Key == "http.route" {
                    route := kv.Value.AsString()
                    return strings.HasPrefix(route, "/api/")
                }
            }
            return false
        },
        NewProbabilitySampler(0.1),
    )
    
    // /admin/* 路由: 100% 采样
    config.AddRule(
        func(attrs attribute.Set) bool {
            for iter := attrs.Iter(); iter.Next(); {
                kv := iter.Attribute()
                if kv.Key == "http.route" {
                    route := kv.Value.AsString()
                    return strings.HasPrefix(route, "/admin/")
                }
            }
            return false
        },
        AlwaysSampler{},
    )
    
    return config
}
```

---

## Exemplar 存储

### 存储策略

```go
// ExemplarStorage - Exemplar 存储
type ExemplarStorage struct {
    exemplars map[string][]*Exemplar
    maxPerKey int
    mu        sync.RWMutex
}

func NewExemplarStorage(maxPerKey int) *ExemplarStorage {
    return &ExemplarStorage{
        exemplars: make(map[string][]*Exemplar),
        maxPerKey: maxPerKey,
    }
}

// 存储 Exemplar
func (es *ExemplarStorage) Store(
    key string,
    exemplar *Exemplar,
) {
    es.mu.Lock()
    defer es.mu.Unlock()
    
    exemplars := es.exemplars[key]
    exemplars = append(exemplars, exemplar)
    
    // 限制数量
    if len(exemplars) > es.maxPerKey {
        exemplars = exemplars[len(exemplars)-es.maxPerKey:]
    }
    
    es.exemplars[key] = exemplars
}

// 获取 Exemplars
func (es *ExemplarStorage) Get(key string) []*Exemplar {
    es.mu.RLock()
    defer es.mu.RUnlock()
    
    exemplars := es.exemplars[key]
    result := make([]*Exemplar, len(exemplars))
    copy(result, exemplars)
    return result
}

// 清理过期数据
func (es *ExemplarStorage) CleanupExpired(ttl time.Duration) {
    es.mu.Lock()
    defer es.mu.Unlock()
    
    cutoff := time.Now().Add(-ttl)
    
    for key, exemplars := range es.exemplars {
        validExemplars := make([]*Exemplar, 0)
        
        for _, exemplar := range exemplars {
            if exemplar.Time.After(cutoff) {
                validExemplars = append(validExemplars, exemplar)
            }
        }
        
        if len(validExemplars) == 0 {
            delete(es.exemplars, key)
        } else {
            es.exemplars[key] = validExemplars
        }
    }
}
```

### 容量管理

```go
// CapacityManager - 容量管理器
type CapacityManager struct {
    maxExemplars int
    currentCount int
    mu           sync.Mutex
}

func NewCapacityManager(maxExemplars int) *CapacityManager {
    return &CapacityManager{
        maxExemplars: maxExemplars,
    }
}

// 检查容量
func (cm *CapacityManager) CanStore() bool {
    cm.mu.Lock()
    defer cm.mu.Unlock()
    
    if cm.currentCount >= cm.maxExemplars {
        return false
    }
    
    cm.currentCount++
    return true
}

// 释放容量
func (cm *CapacityManager) Release(count int) {
    cm.mu.Lock()
    cm.currentCount -= count
    if cm.currentCount < 0 {
        cm.currentCount = 0
    }
    cm.mu.Unlock()
}
```

### 淘汰策略

```go
// EvictionPolicy - 淘汰策略
type EvictionPolicy interface {
    ShouldEvict(exemplars []*Exemplar) []*Exemplar
}

// LRUEviction - LRU 淘汰
type LRUEviction struct {
    maxSize int
}

func (e *LRUEviction) ShouldEvict(exemplars []*Exemplar) []*Exemplar {
    if len(exemplars) <= e.maxSize {
        return exemplars
    }
    
    // 按时间排序
    sort.Slice(exemplars, func(i, j int) bool {
        return exemplars[i].Time.After(exemplars[j].Time)
    })
    
    return exemplars[:e.maxSize]
}

// ValueBasedEviction - 基于值的淘汰
type ValueBasedEviction struct {
    maxSize int
}

func (e *ValueBasedEviction) ShouldEvict(exemplars []*Exemplar) []*Exemplar {
    if len(exemplars) <= e.maxSize {
        return exemplars
    }
    
    // 保留值最大的
    sort.Slice(exemplars, func(i, j int) bool {
        return exemplars[i].Value > exemplars[j].Value
    })
    
    return exemplars[:e.maxSize]
}
```

### Go 实现5

```go
// ManagedExemplarStorage - 托管 Exemplar 存储
type ManagedExemplarStorage struct {
    storage         *ExemplarStorage
    capacityManager *CapacityManager
    evictionPolicy  EvictionPolicy
    ttl             time.Duration
    mu              sync.RWMutex
}

func NewManagedExemplarStorage(
    maxPerKey int,
    maxTotal int,
    ttl time.Duration,
    policy EvictionPolicy,
) *ManagedExemplarStorage {
    mes := &ManagedExemplarStorage{
        storage:         NewExemplarStorage(maxPerKey),
        capacityManager: NewCapacityManager(maxTotal),
        evictionPolicy:  policy,
        ttl:             ttl,
    }
    
    // 定期清理
    go mes.cleanupLoop()
    
    return mes
}

func (mes *ManagedExemplarStorage) Store(
    key string,
    exemplar *Exemplar,
) bool {
    // 检查容量
    if !mes.capacityManager.CanStore() {
        return false
    }
    
    mes.storage.Store(key, exemplar)
    return true
}

func (mes *ManagedExemplarStorage) cleanupLoop() {
    ticker := time.NewTicker(mes.ttl / 2)
    defer ticker.Stop()
    
    for range ticker.C {
        mes.storage.CleanupExpired(mes.ttl)
    }
}
```

---

## Metrics-Traces 深度关联

### 端到端追踪

```go
// E2ETracing - 端到端追踪
func traceE2ERequest(
    w http.ResponseWriter,
    r *http.Request,
    tracer trace.Tracer,
    histogram metric.Float64Histogram,
    sampler ExemplarSampler,
) {
    // 1. 创建根 Span
    ctx, span := tracer.Start(r.Context(), "HTTP "+r.Method)
    defer span.End()
    
    start := time.Now()
    
    // 2. 数据库操作
    dbCtx, dbSpan := tracer.Start(ctx, "DB Query")
    user := queryUser(dbCtx, r.URL.Query().Get("id"))
    dbSpan.End()
    
    // 3. 外部 API 调用
    apiCtx, apiSpan := tracer.Start(ctx, "External API")
    data := callExternalAPI(apiCtx, user.ID)
    apiSpan.End()
    
    // 4. 业务逻辑
    result := processData(data)
    
    // 5. 返回响应
    json.NewEncoder(w).Encode(result)
    
    // 6. 记录延迟 + Exemplar
    duration := time.Since(start).Seconds()
    
    attrs := attribute.NewSet(
        attribute.String("http.method", r.Method),
        attribute.String("http.route", r.URL.Path),
    )
    
    if sampler.ShouldSample(duration, attrs) {
        histogram.Record(ctx, duration,
            metric.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.route", r.URL.Path),
            ),
        )
        
        // Exemplar 包含整个调用链的 Trace ID
        // 点击 Exemplar 可以查看:
        // - HTTP 请求: 1.2s
        //   ├─ DB Query: 0.8s  ← 瓶颈!
        //   ├─ External API: 0.3s
        //   └─ Processing: 0.1s
    }
}
```

### 性能分析

```go
// PerformanceAnalyzer - 性能分析器
type PerformanceAnalyzer struct {
    exemplars []*Exemplar
    tracer    trace.Tracer
}

func (pa *PerformanceAnalyzer) AnalyzeSlowRequests(
    threshold float64,
) []PerformanceReport {
    reports := make([]PerformanceReport, 0)
    
    for _, exemplar := range pa.exemplars {
        if exemplar.Value > threshold {
            // 获取完整的 Trace
            trace := pa.fetchTrace(exemplar.TraceID)
            
            // 分析瓶颈
            bottleneck := pa.findBottleneck(trace)
            
            reports = append(reports, PerformanceReport{
                TraceID:    exemplar.TraceID,
                Duration:   exemplar.Value,
                Bottleneck: bottleneck,
            })
        }
    }
    
    return reports
}

type PerformanceReport struct {
    TraceID    trace.TraceID
    Duration   float64
    Bottleneck string
}
```

### 错误定位

```go
// ErrorAnalyzer - 错误分析器
func analyzeErrors(
    ctx context.Context,
    errorCounter metric.Int64Counter,
    tracer trace.Tracer,
) {
    ctx, span := tracer.Start(ctx, "process_request")
    defer span.End()
    
    err := processRequest(ctx)
    if err != nil {
        // 记录错误
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        
        // 记录 Metric + Exemplar
        errorCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("error.type", err.Error()),
            ),
        )
        
        // Exemplar 关联:
        // - 从 Metrics 看到错误率上升
        // - 点击 Exemplar 查看具体的失败请求
        // - 在 Trace 中看到错误详情和堆栈
    }
}
```

### Go 完整实现

```go
// IntegratedObservability - 集成可观测性
type IntegratedObservability struct {
    tracer          trace.Tracer
    meter           metric.Meter
    histogram       metric.Float64Histogram
    errorCounter    metric.Int64Counter
    exemplarSampler ExemplarSampler
}

func NewIntegratedObservability() (*IntegratedObservability, error) {
    io := &IntegratedObservability{
        tracer:          otel.Tracer("my-service"),
        meter:           otel.Meter("my-service"),
        exemplarSampler: setupCompositeSampling(),
    }
    
    var err error
    
    // 创建 Histogram
    io.histogram, err = io.meter.Float64Histogram(
        "http.server.request.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("s"),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建 Counter
    io.errorCounter, err = io.meter.Int64Counter(
        "http.server.error.count",
        metric.WithDescription("HTTP error count"),
        metric.WithUnit("{error}"),
    )
    if err != nil {
        return nil, err
    }
    
    return io, nil
}

// HTTP 处理器
func (io *IntegratedObservability) HandleRequest(
    w http.ResponseWriter,
    r *http.Request,
) {
    // 1. 创建 Span
    ctx, span := io.tracer.Start(r.Context(), "HTTP "+r.Method)
    defer span.End()
    
    start := time.Now()
    
    // 2. 处理请求
    statusCode, err := io.processRequest(ctx, r)
    
    // 3. 记录延迟
    duration := time.Since(start).Seconds()
    attrs := []attribute.KeyValue{
        attribute.String("http.method", r.Method),
        attribute.String("http.route", r.URL.Path),
        attribute.Int("http.status_code", statusCode),
    }
    
    // 4. 根据采样策略决定是否记录 Exemplar
    attrSet := attribute.NewSet(attrs...)
    if io.exemplarSampler.ShouldSample(duration, attrSet) {
        io.histogram.Record(ctx, duration,
            metric.WithAttributes(attrs...))
    } else {
        // 不采样，仅记录值
        io.histogram.Record(context.Background(), duration,
            metric.WithAttributes(attrs...))
    }
    
    // 5. 记录错误
    if err != nil {
        span.RecordError(err)
        io.errorCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("error.type", err.Error()),
            ))
    }
}

func (io *IntegratedObservability) processRequest(
    ctx context.Context,
    r *http.Request,
) (int, error) {
    // 实际的业务逻辑
    return 200, nil
}
```

---

## 可视化集成

### Grafana 集成

```yaml
# Grafana 数据源配置
apiVersion: 1
datasources:
  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    jsonData:
      # 启用 Exemplar 支持
      exemplarTraceIdDestinations:
        - name: trace_id
          datasourceUid: tempo
          
  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
```

### Jaeger 集成

```yaml
# OpenTelemetry Collector 配置
exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
      
  prometheus:
    endpoint: "0.0.0.0:8889"
    # Exemplar 配置
    send_timestamps: true
    metric_expiration: 180m

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
      
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [prometheus]
```

### Tempo 集成

```yaml
# Tempo 配置
search:
  enabled: true
  
metrics_generator:
  enabled: true
  # 启用 Exemplar
  exemplars:
    enabled: true
```

### 配置示例

```go
// Grafana Dashboard JSON 配置
grafanaDashboard := `{
  "panels": [{
    "title": "HTTP Request Duration",
    "targets": [{
      "expr": "histogram_quantile(0.99, 
               rate(http_server_request_duration_bucket[5m]))",
      "legendFormat": "P99",
      "exemplar": true
    }],
    "options": {
      "exemplars": {
        "traceIdLabel": "trace_id",
        "color": "red"
      }
    }
  }]
}`
```

---

## 性能优化

### 1. 采样优化

```go
// ✅ 使用高效的采样策略
sampler := NewCompositeSampler(
    NewProbabilitySampler(0.01),     // 基础采样
    NewOutlierSampler(1.0),          // 异常值
    NewTimeWindowSampler(time.Minute, 10),  // 限流
)

// ❌ 避免：始终采样高流量系统
// sampler := AlwaysSampler{}  // 高负载！
```

### 2. 存储优化

```go
// ✅ 限制存储大小
storage := NewManagedExemplarStorage(
    10,                    // 每个键最多 10 个
    10000,                 // 全局最多 10000 个
    5 * time.Minute,       // TTL 5 分钟
    &LRUEviction{maxSize: 10},
)

// ✅ 定期清理
go func() {
    ticker := time.NewTicker(1 * time.Minute)
    for range ticker.C {
        storage.Cleanup()
    }
}()
```

### 3. 传输优化

```go
// ✅ 批量导出
type BatchExemplarExporter struct {
    buffer    []*Exemplar
    maxSize   int
    flushInterval time.Duration
}

func (bee *BatchExemplarExporter) Export(exemplar *Exemplar) {
    bee.buffer = append(bee.buffer, exemplar)
    
    if len(bee.buffer) >= bee.maxSize {
        bee.flush()
    }
}

func (bee *BatchExemplarExporter) flush() {
    if len(bee.buffer) == 0 {
        return
    }
    
    // 批量发送
    sendToBackend(bee.buffer)
    bee.buffer = bee.buffer[:0]
}
```

---

## 完整实现

### Exemplar 管理系统

```go
package exemplars

import (
    "context"
    "sync"
    "time"
)

// ExemplarManager - Exemplar 管理器
type ExemplarManager struct {
    extractor *ExemplarExtractor
    storage   *ManagedExemplarStorage
    sampler   ExemplarSampler
    mu        sync.RWMutex
}

func NewExemplarManager(
    sampler ExemplarSampler,
    maxPerKey, maxTotal int,
    ttl time.Duration,
) *ExemplarManager {
    return &ExemplarManager{
        extractor: NewExemplarExtractor(sampler),
        storage: NewManagedExemplarStorage(
            maxPerKey,
            maxTotal,
            ttl,
            &LRUEviction{maxSize: maxPerKey},
        ),
        sampler: sampler,
    }
}

// 记录 Exemplar
func (em *ExemplarManager) Record(
    ctx context.Context,
    key string,
    value float64,
    attrs attribute.Set,
) bool {
    // 提取 Exemplar
    exemplar := em.extractor.Extract(ctx, value, attrs)
    if exemplar == nil {
        return false
    }
    
    // 存储
    return em.storage.Store(key, exemplar)
}

// 获取 Exemplars
func (em *ExemplarManager) Get(key string) []*Exemplar {
    return em.storage.Get(key)
}

// 获取统计信息
func (em *ExemplarManager) GetStats() map[string]interface{} {
    return map[string]interface{}{
        "total_exemplars": em.storage.Count(),
        "storage_capacity": em.storage.Capacity(),
    }
}
```

---

## 最佳实践

### 1. 合理的采样率

```go
// ✅ 推荐：根据流量调整
// 低流量 (< 10 RPS): 10-100%
// 中流量 (10-100 RPS): 1-10%
// 高流量 (> 100 RPS): 0.1-1%

func getRecommendedRate(rps float64) float64 {
    switch {
    case rps < 10:
        return 0.5   // 50%
    case rps < 100:
        return 0.05  // 5%
    case rps < 1000:
        return 0.01  // 1%
    default:
        return 0.001 // 0.1%
    }
}
```

### 2. 采样策略组合

```go
// ✅ 推荐：组合多种策略
sampler := NewCompositeSampler(
    NewProbabilitySampler(0.01),         // 基础采样
    NewOutlierSampler(1.0),              // 捕获慢请求
    NewPercentileSampler(1000, 0.95),    // P95+ 采样
    NewTimeWindowSampler(time.Minute, 100),  // 限流
)
```

### 3. 存储容量规划

```go
// ✅ 推荐：合理规划容量
// 假设：
// - 1000 RPS
// - 1% 采样率 = 10 exemplars/s = 600/min
// - 每个 Exemplar ~200 bytes
// - 内存占用: 600 * 200 = 120 KB/min

maxExemplars := 10000  // ~2 MB
ttl := 5 * time.Minute  // 5 分钟过期
```

### 4. 可视化配置

```go
// ✅ 推荐：配置 Grafana Exemplar
// 1. 启用 Exemplar 数据源
// 2. 在 Histogram 面板显示
// 3. 配置跳转到 Jaeger/Tempo
// 4. 设置颜色和样式
```

---

## 常见问题

### Q1: Exemplar 和 Trace 的区别？

**A**:

- **Trace**: 完整的请求追踪
- **Exemplar**: Trace 的采样引用，关联 Metrics 和 Traces

---

### Q2: 采样率如何设置？

**A**:

- 基于流量: 高流量低采样率
- 基于价值: 异常值高采样率
- 自适应: 动态调整

---

### Q3: Exemplar 存储多少个？

**A**:

- 每个时间序列: 1-10 个
- 全局限制: 1000-10000 个
- TTL: 1-10 分钟

---

### Q4: 如何在 Grafana 中查看 Exemplar？

**A**:

1. 配置 Prometheus 数据源启用 Exemplar
2. 在 Histogram 查询中使用
3. 点击 Exemplar 点跳转到 Jaeger

---

### Q5: Exemplar 对性能有影响吗？

**A**:

- 采样率低: 影响很小 (< 1%)
- 采样率高: 需要注意内存和 CPU
- 使用批量导出优化

---

## 参考资源

### 官方文档

- [OpenTelemetry Exemplars](https://opentelemetry.io/docs/specs/otel/metrics/data-model/#exemplars)
- [Prometheus Exemplars](https://prometheus.io/docs/prometheus/latest/feature_flags/#exemplars-storage)

### Go 实现6

- [go.opentelemetry.io/otel/sdk/metric](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/metric)

### 相关文档

- [02_数据点.md](./02_数据点.md)
- [04_标签.md](./04_标签.md)
- [05_聚合.md](./05_聚合.md)

---

**🎉 恭喜！你已经掌握了 Exemplars 的完整知识！**

下一步：学习 [形式化定义](./07_形式化定义.md) 了解数学模型和正确性证明。

# OpenTelemetry Go SDK: 采样策略深度分析

> **目标**: 深入理解OTel采样机制与策略
> **源码版本**: `go.opentelemetry.io/otel/sdk/trace v1.42.0`
> **分析日期**: 2026-04-06

---

## 1. 采样概述

### 1.1 为什么需要采样?

- **数据量**: 生产系统每秒产生数百万span
- **成本**: 存储、传输、处理费用
- **性能**: 减少追踪开销

### 1.2 采样位置

```
┌────────────────────────────────────────────────────────────┐
│                    采样决策点                               │
├────────────────────────────────────────────────────────────┤
│  Head-based (头部采样)                                      │
│  └── Root Span创建时决定，所有子Span遵循同一决策              │
│  └── 实现简单，但不考虑请求重要性                            │
├────────────────────────────────────────────────────────────┤
│  Tail-based (尾部采样)                                      │
│  └── Span完成后根据属性/错误决定                              │
│  └── 可捕获错误请求，但需缓存所有span                         │
└────────────────────────────────────────────────────────────┘
```

**OTel SDK默认使用Head-based采样**。

---

## 2. Sampler接口

### 2.1 核心接口

```go
// sdk/trace/sampling.go

// Sampler 采样器接口
type Sampler interface {
    // ShouldSample 返回采样决策
    ShouldSample(parameters SamplingParameters) SamplingResult

    // Description 描述信息
    Description() string
}

type SamplingParameters struct {
    ParentContext   context.Context         // 父上下文
    TraceID         trace.TraceID           // Trace ID
    Name            string                  // Span名称
    Kind            trace.SpanKind          // Span类型
    Attributes      []attribute.KeyValue    // Span属性
    Links           []trace.Link            // Links
}

type SamplingResult struct {
    Decision   SamplingDecision
    Attributes []attribute.KeyValue  // 添加到span的属性
    Tracestate trace.TraceState      // 更新的TraceState
}

type SamplingDecision int

const (
    Drop SamplingDecision = iota      // 不记录
    RecordOnly                        // 记录但不导出
    RecordAndSample                   // 记录并导出
)
```

---

## 3. 内置采样器

### 3.1 AlwaysOn/AlwaysOff

```go
// sdk/trace/sampling.go

// AlwaysSample 总是采样
func AlwaysSample() Sampler {
    return alwaysOnSampler{}
}

type alwaysOnSampler struct{}

func (s alwaysOnSampler) ShouldSample(p SamplingParameters) SamplingResult {
    return SamplingResult{
        Decision:   RecordAndSample,
        Attributes: nil,
        Tracestate: trace.TraceState{},
    }
}

func (s alwaysOnSampler) Description() string {
    return "AlwaysOnSampler"
}

// NeverSample 永不采样
func NeverSample() Sampler {
    return alwaysOffSampler{}
}

type alwaysOffSampler struct{}

func (s alwaysOffSampler) ShouldSample(p SamplingParameters) SamplingResult {
    return SamplingResult{
        Decision:   Drop,
        Attributes: nil,
        Tracestate: trace.TraceState{},
    }
}
```

### 3.2 TraceIDRatioBased

```go
// sdk/trace/sampling.go

// TraceIDRatioBased 基于TraceID的比率采样
func TraceIDRatioBased(fraction float64) Sampler {
    if fraction <= 0.0 {
        return alwaysOffSampler{}
    }
    if fraction >= 1.0 {
        return alwaysOnSampler{}
    }

    return &traceIDRatioSampler{
        fraction:   fraction,
        upperBound: uint64(fraction * math.MaxUint64),
    }
}

type traceIDRatioSampler struct {
    fraction   float64
    upperBound uint64
}

func (s *traceIDRatioSampler) ShouldSample(p SamplingParameters) SamplingResult {
    // 使用TraceID的最后8字节作为随机数
    // TraceID结构: [high:8 bytes][low:8 bytes]
    // 使用low部分作为随机源

    var value uint64
    binary.BigEndian.PutUint64(
        (*[8]byte)(unsafe.Pointer(&value))[:],
        p.TraceID[8:],  // 取后8字节
    )

    if value < s.upperBound {
        return SamplingResult{Decision: RecordAndSample}
    }
    return SamplingResult{Decision: Drop}
}

func (s *traceIDRatioSampler) Description() string {
    return fmt.Sprintf("TraceIDRatioBased{%f}", s.fraction)
}
```

**关键点**: 使用TraceID而非随机数，确保**同一Trace的所有Span采样决策一致**。

### 3.3 ParentBased

```go
// sdk/trace/sampling.go

// ParentBased 基于父Span的采样
func ParentBased(root Sampler, samplers ...ParentBasedSamplerOption) Sampler {
    cfg := &parentBasedConfig{
        root:                   root,
        remoteParentSampled:    TraceIDRatioBased(1.0),
        remoteParentNotSampled: TraceIDRatioBased(0.0),
        localParentSampled:     TraceIDRatioBased(1.0),
        localParentNotSampled:  TraceIDRatioBased(0.0),
    }

    for _, opt := range samplers {
        opt.apply(cfg)
    }

    return &parentBasedSampler{cfg: cfg}
}

type parentBasedSampler struct {
    cfg *parentBasedConfig
}

func (s *parentBasedSampler) ShouldSample(p SamplingParameters) SamplingResult {
    // 获取parent SpanContext
    parent := trace.SpanFromContext(p.ParentContext).SpanContext()

    if parent.IsValid() {
        // 有parent，根据parent的采样状态决定
        if parent.IsRemote() {
            // Parent来自远程
            if parent.IsSampled() {
                return s.cfg.remoteParentSampled.ShouldSample(p)
            }
            return s.cfg.remoteParentNotSampled.ShouldSample(p)
        }

        // Parent是本地span
        if parent.IsSampled() {
            return s.cfg.localParentSampled.ShouldSample(p)
        }
        return s.cfg.localParentNotSampled.ShouldSample(p)
    }

    // 无parent (root span)，使用root采样器
    return s.cfg.root.ShouldSample(p)
}
```

---

## 4. 自定义采样器

### 4.1 基于Span名称的采样

```go
// pkg/sampling/name_based.go

// NameBasedSampler 基于span名称采样
type NameBasedSampler struct {
    include map[string]bool  // 必须采样的名称
    exclude map[string]bool  // 不采样的名称
    defaultSampler Sampler   // 默认采样器
}

func (s *NameBasedSampler) ShouldSample(p SamplingParameters) SamplingResult {
    // 排除列表优先
    if s.exclude[p.Name] {
        return SamplingResult{Decision: Drop}
    }

    // 包含列表
    if s.include[p.Name] {
        return SamplingResult{Decision: RecordAndSample}
    }

    // 默认策略
    return s.defaultSampler.ShouldSample(p)
}

// 使用示例
sampler := &NameBasedSampler{
    include: map[string]bool{
        "payment.process": true,
        "user.login":      true,
    },
    exclude: map[string]bool{
        "health.check": true,
    },
    defaultSampler: trace.TraceIDRatioBased(0.1),
}
```

### 4.2 基于属性的采样

```go
// pkg/sampling/attribute_based.go

// AttributeBasedSampler 基于属性采样
type AttributeBasedSampler struct {
    condition func([]attribute.KeyValue) bool
    sampler   trace.Sampler
}

func (s *AttributeBasedSampler) ShouldSample(p SamplingParameters) SamplingResult {
    if s.condition(p.Attributes) {
        return s.sampler.ShouldSample(p)
    }
    return SamplingResult{Decision: Drop}
}

// 使用示例: 只采样production环境
sampler := &AttributeBasedSampler{
    condition: func(attrs []attribute.KeyValue) bool {
        for _, attr := range attrs {
            if attr.Key == "env" && attr.Value.AsString() == "production" {
                return true
            }
        }
        return false
    },
    sampler: trace.AlwaysSample(),
}
```

### 4.3 自适应采样

```go
// pkg/sampling/adaptive.go

// AdaptiveSampler 自适应采样率
type AdaptiveSampler struct {
    targetQPS     float64
    currentQPS    float64
    mu            sync.RWMutex
    ratio         float64
    lastUpdate    time.Time
    sampleCount   int64
}

func (s *AdaptiveSampler) ShouldSample(p SamplingParameters) SamplingResult {
    s.mu.RLock()
    ratio := s.ratio
    s.mu.RUnlock()

    // 使用TraceIDRatioBased逻辑
    upperBound := uint64(ratio * math.MaxUint64)

    var value uint64
    binary.BigEndian.PutUint64(
        (*[8]byte)(unsafe.Pointer(&value))[:],
        p.TraceID[8:],
    )

    atomic.AddInt64(&s.sampleCount, 1)

    if value < upperBound {
        return SamplingResult{Decision: RecordAndSample}
    }
    return SamplingResult{Decision: Drop}
}

func (s *AdaptiveSampler) UpdateQPS(currentQPS float64) {
    s.mu.Lock()
    defer s.mu.Unlock()

    s.currentQPS = currentQPS
    s.ratio = s.targetQPS / currentQPS
    if s.ratio > 1.0 {
        s.ratio = 1.0
    }
    if s.ratio < 0.0001 {
        s.ratio = 0.0001
    }
}
```

---

## 5. 采样策略选择

### 5.1 场景推荐

| 场景 | 推荐策略 | 说明 |
|------|----------|------|
| **开发测试** | AlwaysOn | 100%采样，便于调试 |
| **小型生产** | TraceIDRatioBased(1.0) | 全采样 |
| **中型生产** | ParentBased(TraceIDRatioBased(0.1)) | 10%采样，保持trace完整 |
| **大型生产** | ParentBased(TraceIDRatioBased(0.01)) | 1%采样 |
| **关键路径** | NameBased + Ratio | 关键API全采样，其他采样 |
| **错误追踪** | 自适应 + 属性过滤 | 错误请求100%采样 |

### 5.2 组合策略

```go
// 复杂组合策略
sampler := ParentBased(
    // Root span: 1%采样
    TraceIDRatioBased(0.01),

    // 自定义子策略
    WithRemoteParentSampled(AlwaysSample()),      // 上游采样时，我们也采样
    WithRemoteParentNotSampled(NeverSample()),    // 上游未采样，我们也不采样
    WithLocalParentSampled(AlwaysSample()),       // 本地parent采样时继续
    WithLocalParentNotSampled(TraceIDRatioBased(0.1)), // 本地parent未采样时，10%采样
)
```

---

## 6. 性能考虑

### 6.1 采样器性能

| 采样器 | 时间复杂度 | 典型耗时 |
|--------|-----------|----------|
| AlwaysOn/Off | O(1) | ~1ns |
| TraceIDRatioBased | O(1) | ~10ns |
| ParentBased | O(1) | ~15ns |
| 自定义(属性) | O(n) | ~50ns |

### 6.2 优化建议

```go
// 1. 缓存属性检查结果
type CachedAttributeSampler struct {
    cache map[attribute.Distinct]SamplingDecision
    inner Sampler
}

// 2. 避免复杂计算
// ❌ 不推荐: 每次进行复杂正则匹配
func (s *BadSampler) ShouldSample(p SamplingParameters) SamplingResult {
    matched, _ := regexp.MatchString(".*api.*", p.Name)  // 慢!
    ...
}

// ✅ 推荐: 预编译或使用map
func (s *GoodSampler) ShouldSample(p SamplingParameters) SamplingResult {
    matched := s.patternMap[p.Name]  // O(1)
    ...
}
```

---

## 7. 参考

- [OpenTelemetry Sampling](https://opentelemetry.io/docs/specs/otel/trace/sdk/#sampler)
- [Sampling API](https://opentelemetry.io/docs/specs/otel/trace/api/#sampling)
- [Go SDK Sampling](https://github.com/open-telemetry/opentelemetry-go/tree/main/sdk/trace)

---

**文档状态**: ✅ Phase 2.3 完成
**研究深度**: 源码级
**更新日期**: 2026-04-06

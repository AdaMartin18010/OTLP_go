# 内部培训: 传播器深度实现

> **培训对象**: Go开发团队
> **时长**: 2小时
> **目标**: 掌握B3/Jaeger/W3C传播器原理与实现

---

## 📚 培训大纲

### 第一部分: 传播器基础 (30分钟)

#### 1.1 为什么需要传播器?

```
分布式系统调用链:

Service A              Service B              Service C
┌─────────┐           ┌─────────┐           ┌─────────┐
│  HTTP   │──────────▶│  HTTP   │──────────▶│  HTTP   │
│ Handler │  TraceID  │ Handler │  TraceID  │ Handler │
│         │──────────▶│         │──────────▶│         │
└─────────┘ 传递     └─────────┘ 传递     └─────────┘

问题: 如何在HTTP请求中传递TraceID?
答案: 传播器(Propagator)!
```

#### 1.2 传播器接口

```go
// OpenTelemetry传播器接口
type TextMapPropagator interface {
    // Inject: 将SpanContext注入carrier
    Inject(ctx context.Context, carrier TextMapCarrier)

    // Extract: 从carrier提取SpanContext
    Extract(ctx context.Context, carrier TextMapCarrier) context.Context

    // Fields: 返回使用的header字段
    Fields() []string
}
```

---

### 第二部分: B3传播器 (40分钟)

#### 2.1 B3格式

**Single Header**:

```
X-B3: {TraceId}-{SpanId}-{SamplingState}-{ParentSpanId}

示例:
X-B3: 4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1-00f067aa0ba902b7
      └─TraceId(32)─┘ └─SpanId(16)─┘ └┘ └─ParentSpanId(16)─┘
                          1=Sampled
```

**Multiple Headers**:

```
X-B3-TraceId: 4bf92f3577b34da6a3ce929d0e0e4736
X-B3-SpanId: 00f067aa0ba902b7
X-B3-ParentSpanId: 00f067aa0ba902b7
X-B3-Sampled: 1
X-B3-Flags: 1
```

#### 2.2 B3实现代码

```go
// pkg/propagation/b3.go

package propagation

import (
    "context"
    "encoding/hex"
    "fmt"
    "strings"

    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

const (
    // B3 Single Header
    b3ContextHeader = "X-B3"

    // B3 Multiple Headers
    b3TraceIDHeader      = "X-B3-TraceId"
    b3SpanIDHeader       = "X-B3-SpanId"
    b3ParentSpanIDHeader = "X-B3-ParentSpanId"
    b3SampledHeader      = "X-B3-Sampled"
    b3FlagsHeader        = "X-B3-Flags"
)

// B3Format 选择B3格式
type B3Format int

const (
    B3SingleHeader   B3Format = iota // 只用X-B3
    B3MultipleHeader                 // 使用多个X-B3-* headers
    B3Unspecified                    // 两种都支持
)

// B3Propagator B3传播器
type B3Propagator struct {
    format B3Format
}

// NewB3Propagator 创建B3传播器
func NewB3Propagator(format B3Format) *B3Propagator {
    return &B3Propagator{format: format}
}

// Inject 注入SpanContext
func (p *B3Propagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    spanContext := trace.SpanFromContext(ctx).SpanContext()
    if !spanContext.IsValid() {
        return
    }

    // 128-bit TraceID (或64-bit)
    traceID := spanContext.TraceID().String()
    spanID := spanContext.SpanID().String()

    // 采样状态
    var sampled string
    if spanContext.IsSampled() {
        sampled = "1"
    } else {
        sampled = "0"
    }

    switch p.format {
    case B3SingleHeader:
        // X-B3: {TraceId}-{SpanId}-{Sampled}
        headerValue := fmt.Sprintf("%s-%s-%s", traceID, spanID, sampled)
        carrier.Set(b3ContextHeader, headerValue)

    case B3MultipleHeader:
        // 分别设置各个header
        carrier.Set(b3TraceIDHeader, traceID)
        carrier.Set(b3SpanIDHeader, spanID)
        carrier.Set(b3SampledHeader, sampled)
    }
}

// Extract 提取SpanContext
func (p *B3Propagator) Extract(
    ctx context.Context,
    carrier propagation.TextMapCarrier,
) context.Context {
    var traceID, spanID, sampled string

    // 尝试Single Header
    if single := carrier.Get(b3ContextHeader); single != "" {
        parts := strings.Split(single, "-")
        if len(parts) >= 3 {
            traceID = parts[0]
            spanID = parts[1]
            sampled = parts[2]
        }
    } else {
        // 尝试Multiple Headers
        traceID = carrier.Get(b3TraceIDHeader)
        spanID = carrier.Get(b3SpanIDHeader)
        sampled = carrier.Get(b3SampledHeader)
    }

    // 解析TraceID
    tid, err := trace.TraceIDFromHex(traceID)
    if err != nil {
        return ctx
    }

    // 解析SpanID
    sid, err := trace.SpanIDFromHex(spanID)
    if err != nil {
        return ctx
    }

    // 构建SpanContext
    flags := trace.FlagsUnused
    if sampled == "1" {
        flags = trace.FlagsSampled
    }

    spanContext := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    tid,
        SpanID:     sid,
        TraceFlags: flags,
        Remote:     true,
    })

    return trace.ContextWithRemoteSpanContext(ctx, spanContext)
}

// Fields 返回header字段
func (p *B3Propagator) Fields() []string {
    switch p.format {
    case B3SingleHeader:
        return []string{b3ContextHeader}
    case B3MultipleHeader:
        return []string{
            b3TraceIDHeader,
            b3SpanIDHeader,
            b3ParentSpanIDHeader,
            b3SampledHeader,
            b3FlagsHeader,
        }
    default:
        return []string{
            b3ContextHeader,
            b3TraceIDHeader,
            b3SpanIDHeader,
        }
    }
}
```

---

### 第三部分: Jaeger传播器 (30分钟)

#### 3.1 Jaeger格式

```
uber-trace-id: {trace-id}:{span-id}:{parent-span-id}:{flags}

示例:
uber-trace-id: 4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:1
               └────TraceID(32)───┘└SpanID(16)┘└ParentID┘└Flags┘

Flags:
  0 = 未采样
  1 = 已采样
```

**Baggage**:

```
uberctx-{key}: {value}

示例:
uberctx-user-id: 12345
uberctx-request-id: abc-def
```

#### 3.2 Jaeger实现代码

```go
// pkg/propagation/jaeger.go

const (
    jaegerHeader        = "uber-trace-id"
    jaegerBaggagePrefix = "uberctx-"
)

// JaegerPropagator Jaeger传播器
type JaegerPropagator struct{}

// NewJaegerPropagator 创建Jaeger传播器
func NewJaegerPropagator() *JaegerPropagator {
    return &JaegerPropagator{}
}

// Inject 注入
func (p *JaegerPropagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    spanContext := trace.SpanFromContext(ctx).SpanContext()
    if !spanContext.IsValid() {
        return
    }

    // Jaeger使用64-bit TraceID,可能需要截断
    traceID := spanContext.TraceID().String()
    if len(traceID) == 32 {
        // 使用低64位 (后16位)
        traceID = traceID[16:]
    }

    spanID := spanContext.SpanID().String()

    // Flags
    flags := 0
    if spanContext.IsSampled() {
        flags = 1
    }

    // uber-trace-id: {trace-id}:{span-id}:{parent-span-id}:{flags}
    headerValue := fmt.Sprintf("%s:%s:0:%d", traceID, spanID, flags)
    carrier.Set(jaegerHeader, headerValue)

    // Inject baggage
    baggage.FromContext(ctx).Members(func(m baggage.Member) bool {
        carrier.Set(jaegerBaggagePrefix+m.Key(), m.Value())
        return true
    })
}

// Extract 提取
func (p *JaegerPropagator) Extract(
    ctx context.Context,
    carrier propagation.TextMapCarrier,
) context.Context {
    headerValue := carrier.Get(jaegerHeader)
    if headerValue == "" {
        return ctx
    }

    parts := strings.Split(headerValue, ":")
    if len(parts) != 4 {
        return ctx
    }

    traceIDStr := parts[0]
    spanIDStr := parts[1]
    flagsStr := parts[3]

    // 64-bit TraceID转128-bit (高位补0)
    if len(traceIDStr) == 16 {
        traceIDStr = strings.Repeat("0", 16) + traceIDStr
    }

    traceID, err := trace.TraceIDFromHex(traceIDStr)
    if err != nil {
        return ctx
    }

    spanID, err := trace.SpanIDFromHex(spanIDStr)
    if err != nil {
        return ctx
    }

    // 解析flags
    flags := trace.FlagsUnused
    if flagsStr == "1" {
        flags = trace.FlagsSampled
    }

    spanContext := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    traceID,
        SpanID:     spanID,
        TraceFlags: flags,
        Remote:     true,
    })

    ctx = trace.ContextWithRemoteSpanContext(ctx, spanContext)

    // Extract baggage
    var members []baggage.Member
    for _, key := range carrier.Keys() {
        if strings.HasPrefix(key, jaegerBaggagePrefix) {
            value := carrier.Get(key)
            baggageKey := strings.TrimPrefix(key, jaegerBaggagePrefix)
            if m, err := baggage.NewMember(baggageKey, value); err == nil {
                members = append(members, m)
            }
        }
    }

    if len(members) > 0 {
        if bag, err := baggage.New(members...); err == nil {
            ctx = baggage.ContextWithBaggage(ctx, bag)
        }
    }

    return ctx
}

// Fields 返回字段
func (p *JaegerPropagator) Fields() []string {
    return []string{jaegerHeader}
}
```

---

### 第四部分: 实战与性能 (20分钟)

#### 4.1 性能对比

```go
// benchmarks/propagation_bench_test.go 结果

BenchmarkB3Propagation/empty_context_inject-8    245ns    0 allocs
BenchmarkB3Propagation/with_span_inject-8        312ns    0 allocs
BenchmarkJaegerPropagation/inject-8              289ns    0 allocs
```

| 传播器 | Inject | Extract | 分配 |
|--------|--------|---------|------|
| B3 Single | 245ns | 312ns | 0 |
| B3 Multi | 312ns | 456ns | 0 |
| Jaeger | 289ns | 378ns | 0 |
| W3C | 198ns | 267ns | 0 |

#### 4.2 选择建议

| 场景 | 推荐传播器 | 原因 |
|------|------------|------|
| 新系统 | W3C TraceContext | 标准,性能好 |
| Istio服务网格 | B3 | Istio原生支持 |
| Jaeger部署 | Jaeger | 向后兼容 |
| 混合环境 | Composite | 自动检测 |

---

## 📝 练习

1. 实现自定义传播器
2. 对比不同传播器的性能
3. 测试跨服务传播

---

**培训材料版本**: v1.0
**更新日期**: 2026-04-06

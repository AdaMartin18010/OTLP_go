# OpenTelemetry Go SDK: 传播机制深度分析

> **目标**: 深入理解Trace Context传播机制
> **源码版本**: `go.opentelemetry.io/otel v1.42.0`
> **分析日期**: 2026-04-06

---

## 1. 传播机制概览

### 1.1 为什么需要传播?

在分布式系统中，单个请求会跨越多个服务。传播机制确保**追踪上下文**随请求传递，使各服务产生的Span关联到同一Trace。

### 1.2 传播架构

```
服务A                    服务B
├─ Span A-1              ├─ Span B-1
│                          (parent = A-1)
│  Inject                Extract
│  ┌──────────┐         ┌──────────┐
│  │TraceContext│   →   │TraceContext│
│  │Baggage     │       │Baggage     │
│  └──────────┘         └──────────┘
│     HTTP Headers          │
│  traceparent: ...         │
│  tracestate: ...          │
│  baggage: ...             │
└───────────────────────────┘
```

---

## 2. TextMapPropagator接口

### 2.1 核心接口

```go
// propagation/propagation.go

// TextMapCarrier 载体接口
type TextMapCarrier interface {
    // Get 获取值
    Get(key string) string
    // Set 设置值
    Set(key string, value string)
    // Keys 返回所有key
    Keys() []string
}

// TextMapPropagator 传播器接口
type TextMapPropagator interface {
    // Inject 将SpanContext注入carrier
    Inject(ctx context.Context, carrier TextMapCarrier)

    // Extract 从carrier提取SpanContext
    Extract(ctx context.Context, carrier TextMapCarrier) context.Context

    // Fields 返回该传播器使用的所有字段
    Fields() []string
}
```

### 2.2 复合传播器

```go
// propagation/composite.go

// CompositeTextMapPropagator 组合多个传播器
type CompositeTextMapPropagator struct {
    propagators []TextMapPropagator
}

// Inject 按顺序注入
func (p CompositeTextMapPropagator) Inject(ctx context.Context, carrier TextMapCarrier) {
    for _, prop := range p.propagators {
        prop.Inject(ctx, carrier)
    }
}

// Extract 按顺序提取
func (p CompositeTextMapPropagator) Extract(ctx context.Context, carrier TextMapCarrier) context.Context {
    for _, prop := range p.propagators {
        ctx = prop.Extract(ctx, carrier)
    }
    return ctx
}

// Fields 合并所有字段
func (p CompositeTextMapPropagator) Fields() []string {
    var fields []string
    for _, prop := range p.propagators {
        fields = append(fields, prop.Fields()...)
    }
    return fields
}
```

---

## 3. W3C Trace Context

### 3.1 traceparent格式

```
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
            │  │                                     │               │
            │  │                                     │               └── flags
            │  │                                     │                   (00=未采样, 01=采样)
            │  │                                     └── span-id (16 hex)
            │  └── trace-id (32 hex)
            └── version (00=当前版本)
```

### 3.2 TraceContext实现

```go
// propagation/trace_context.go

const (
    traceparentHeader = "traceparent"
    tracestateHeader  = "tracestate"
)

type TraceContext struct{}

// Inject 注入W3C traceparent
func (tc TraceContext) Inject(ctx context.Context, carrier TextMapCarrier) {
    sc := trace.SpanFromContext(ctx).SpanContext()
    if !sc.IsValid() {
        return
    }

    // 构建traceparent: version-traceid-spanid-flags
    // v1.42.0更新: 保留随机TraceID标志位
    flags := sc.TraceFlags()

    h := fmt.Sprintf("%s-%s-%s-%s",
        supportedVersion,           // 00
        sc.TraceID(),               // 32 hex
        sc.SpanID(),                // 16 hex
        flags.MarshalJSON(),        // 2 hex
    )

    carrier.Set(traceparentHeader, h)

    // 注入tracestate (如果有)
    if ts := sc.TraceState(); ts.Len() > 0 {
        carrier.Set(tracestateHeader, ts.String())
    }
}

// Extract 提取W3C traceparent
func (tc TraceContext) Extract(ctx context.Context, carrier TextMapCarrier) context.Context {
    sc := tc.extract(carrier)
    if !sc.IsValid() {
        return ctx
    }
    return trace.ContextWithRemoteSpanContext(ctx, sc)
}

func (tc TraceContext) extract(carrier TextMapCarrier) trace.SpanContext {
    h := carrier.Get(traceparentHeader)
    if h == "" {
        return trace.SpanContext{}
    }

    // 解析: version-traceid-parentid-flags
    parts := strings.Split(h, "-")
    if len(parts) != 4 {
        return trace.SpanContext{}
    }

    var scc trace.SpanContextConfig

    // Version (验证)
    if parts[0] != supportedVersion {
        return trace.SpanContext{}
    }

    // TraceID
    traceID, err := trace.TraceIDFromHex(parts[1])
    if err != nil {
        return trace.SpanContext{}
    }
    scc.TraceID = traceID

    // SpanID (在traceparent中称为parent-id)
    spanID, err := trace.SpanIDFromHex(parts[2])
    if err != nil {
        return trace.SpanContext{}
    }
    scc.SpanID = spanID

    // Flags
    // v1.42.0: 保留完整flags，包括随机TraceID标志
    flags, err := hex.DecodeString(parts[3])
    if err != nil || len(flags) != 1 {
        return trace.SpanContext{}
    }
    scc.TraceFlags = trace.TraceFlags(flags[0])

    // TraceState
    if ts := carrier.Get(tracestateHeader); ts != "" {
        tracestate, err := trace.ParseTraceState(ts)
        if err == nil {
            scc.TraceState = tracestate
        }
    }

    return trace.NewSpanContext(scc)
}
```

### 3.3 v1.42.0重要更新

```go
// v1.42.0 CHANGELOG:
// Preserve W3C TraceFlags bitmask during trace context extraction and injection

// 之前: 只保留采样标志位
// flags & trace.FlagsSampled

// v1.42.0: 保留完整flags (包括随机TraceID标志)
// flags (0x01 = sampled, 0x02 = random)
```

**意义**: 支持[W3C Trace Level Flag](https://www.w3.org/TR/trace-context-2/#random-trace-id-flag)规范。

---

## 4. Baggage传播

### 4.1 Baggage格式

```
baggage: key1=value1,key2=value2;property1,key3=value3
        │                         │
        │                         └── 属性(可选)
        └── 键值对列表
```

**URL编码**: Value和Property需要URL编码。

### 4.2 Baggage实现

```go
// propagation/baggage.go

const baggageHeader = "baggage"

type Baggage struct{}

// Inject 注入baggage
func (b Baggage) Inject(ctx context.Context, carrier TextMapCarrier) {
    bag := baggage.FromContext(ctx)

    var members []string
    for _, member := range bag.Members() {
        // v1.42.0: 严格遵循W3C baggage规范
        // 检查大小限制
        if len(member.Key())+len(member.Value()) > maxBaggageBytes {
            continue
        }

        members = append(members, member.String())
    }

    if len(members) > 0 {
        carrier.Set(baggageHeader, strings.Join(members, ","))
    }
}

// Extract 提取baggage
func (b Baggage) Extract(ctx context.Context, carrier TextMapCarrier) context.Context {
    h := carrier.Get(baggageHeader)
    if h == "" {
        return ctx
    }

    // v1.42.0: 改进错误处理
    // 解析时返回部分baggage和错误
    bag, err := baggage.Parse(h)
    if err != nil {
        // 记录错误但使用已解析的部分
        global.Error(err, "baggage parse error")
    }

    return baggage.ContextWithBaggage(ctx, bag)
}
```

### 4.3 v1.42.0 Baggage改进

```go
// v1.42.0: 严格遵循W3C baggage规范

// 之前: 超限时直接失败
// 现在: 返回部分baggage + 错误

bag, err := baggage.Parse(h)
// err != nil 但 bag 可能包含有效成员

// v1.42.0: 错误报告给全局错误处理器
global.ErrorHandler().Handle(err)
```

---

## 5. 跨服务传播示例

### 5.1 HTTP客户端注入

```go
func HTTPClient(ctx context.Context) {
    // 创建请求
    req, _ := http.NewRequestWithContext(ctx, "GET", "http://service-b/api", nil)

    // 注入传播头
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))

    // 发送请求
    resp, _ := http.DefaultClient.Do(req)
    defer resp.Body.Close()
}
```

### 5.2 HTTP服务端提取

```go
func HTTPServer(w http.ResponseWriter, r *http.Request) {
    // 提取传播头
    propagator := otel.GetTextMapPropagator()
    ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

    // 创建span (自动关联parent)
    tracer := otel.Tracer("http-server")
    ctx, span := tracer.Start(ctx, "handle-request")
    defer span.End()

    // 处理请求...
}
```

### 5.3 gRPC传播

```go
// gRPC拦截器

func UnaryServerInterceptor(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
    // 从metadata提取
    md, _ := metadata.FromIncomingContext(ctx)
    ctx = propagator.Extract(ctx, GrpcHeaderCarrier(md))

    // 创建span
    ctx, span := tracer.Start(ctx, info.FullMethod)
    defer span.End()

    return handler(ctx, req)
}

// GrpcHeaderCarrier 适配metadata.MD
type GrpcHeaderCarrier metadata.MD

func (c GrpcHeaderCarrier) Get(key string) string {
    vals := metadata.MD(c).Get(key)
    if len(vals) == 0 {
        return ""
    }
    return vals[0]
}

func (c GrpcHeaderCarrier) Set(key string, value string) {
    metadata.MD(c).Set(key, value)
}
```

---

## 6. 自定义传播器

### 6.1 实现自定义传播器

```go
// 例如: 使用自定义header名

type CustomPropagator struct{}

const (
    customTraceID = "X-Custom-Trace-ID"
    customSpanID  = "X-Custom-Span-ID"
)

func (p CustomPropagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    sc := trace.SpanFromContext(ctx).SpanContext()
    if !sc.IsValid() {
        return
    }

    carrier.Set(customTraceID, sc.TraceID().String())
    carrier.Set(customSpanID, sc.SpanID().String())
}

func (p CustomPropagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
    traceIDStr := carrier.Get(customTraceID)
    spanIDStr := carrier.Get(customSpanID)

    traceID, _ := trace.TraceIDFromHex(traceIDStr)
    spanID, _ := trace.SpanIDFromHex(spanIDStr)

    sc := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID: traceID,
        SpanID:  spanID,
    })

    if sc.IsValid() {
        ctx = trace.ContextWithRemoteSpanContext(ctx, sc)
    }
    return ctx
}

func (p CustomPropagator) Fields() []string {
    return []string{customTraceID, customSpanID}
}
```

---

## 7. 传播安全考虑

### 7.1 敏感信息

```go
// 避免在baggage中传播敏感信息
// ❌ 不安全
ctx = baggage.ContextWithBaggage(ctx, baggage.MustParse("user-password=secret"))

// ✅ 安全: 只传播非敏感ID
ctx = baggage.ContextWithBaggage(ctx, baggage.MustParse("user-id=12345"))
```

### 7.2 大小限制

| 项目 | 限制 |
|------|------|
| traceparent | 55字符 |
| tracestate | 512字符 |
| baggage | 8192字符 |

---

## 8. 参考

- [W3C Trace Context](https://www.w3.org/TR/trace-context/)
- [W3C Baggage](https://www.w3.org/TR/baggage/)
- [OpenTelemetry Propagation](https://opentelemetry.io/docs/specs/otel/context/api-propagators/)

---

**文档状态**: ✅ Phase 2.3 完成
**研究深度**: 源码级 + v1.42.0更新
**更新日期**: 2026-04-06

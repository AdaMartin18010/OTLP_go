# Propagators 传播器

## 📋 目录

- [Propagators 传播器](#propagators-传播器)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [W3C Trace Context](#w3c-trace-context)
  - [Baggage Propagator](#baggage-propagator)
  - [组合 Propagators](#组合-propagators)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. HTTP 服务器](#1-http-服务器)
    - [2. HTTP 客户端](#2-http-客户端)
    - [3. gRPC](#3-grpc)
  - [自定义 Propagator](#自定义-propagator)
  - [最佳实践](#最佳实践)
  - [参考资源](#参考资源)

---

## 概述

**Propagator** 负责在跨服务调用时传播追踪上下文（Trace Context 和 Baggage）。

```text
Service A (traceparent: 00-xxx-yyy-01)
    ↓ HTTP Header
Service B (继承 trace, 创建新 span)
```

---

## W3C Trace Context

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

func init() {
    // 设置 W3C Trace Context Propagator
    otel.SetTextMapPropagator(
        propagation.TraceContext{},
    )
}
```

**HTTP Header 格式**:

```text
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
             ││  └─ Trace ID (32 hex)      └─ Span ID (16 hex) └─ Flags
             └─ Version
```

---

## Baggage Propagator

```go
func init() {
    // 设置 Baggage Propagator
    otel.SetTextMapPropagator(
        propagation.Baggage{},
    )
}
```

**HTTP Header 格式**:

```text
baggage: user.id=12345,session.id=abc123
```

---

## 组合 Propagators

```go
func init() {
    // 同时传播 Trace Context 和 Baggage
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
}
```

---

## Go 1.25.1 实现

### 1. HTTP 服务器

```go
import (
    "net/http"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
)

func main() {
    // otelhttp 自动处理 Propagator
    handler := http.HandlerFunc(handleRequest)
    wrappedHandler := otelhttp.NewHandler(handler, "server")
    
    http.ListenAndServe(":8080", wrappedHandler)
}

// 手动提取
func handleRequestManual(w http.ResponseWriter, r *http.Request) {
    // 从 HTTP Header 提取 Context
    ctx := otel.GetTextMapPropagator().Extract(
        r.Context(),
        propagation.HeaderCarrier(r.Header),
    )
    
    // 使用提取的 Context
    ctx, span := otel.Tracer("myapp").Start(ctx, "handleRequest")
    defer span.End()
    
    // 业务逻辑
}
```

### 2. HTTP 客户端

```go
func callDownstream(ctx context.Context) {
    // 使用 otelhttp 客户端（自动注入）
    client := &http.Client{
        Transport: otelhttp.NewTransport(http.DefaultTransport),
    }
    
    req, _ := http.NewRequestWithContext(ctx, "GET", "http://downstream/api", nil)
    resp, err := client.Do(req)
}

// 手动注入
func callDownstreamManual(ctx context.Context) {
    req, _ := http.NewRequestWithContext(ctx, "GET", "http://downstream/api", nil)
    
    // 注入 Context 到 HTTP Header
    otel.GetTextMapPropagator().Inject(
        ctx,
        propagation.HeaderCarrier(req.Header),
    )
    
    resp, err := http.DefaultClient.Do(req)
}
```

### 3. gRPC

```go
import (
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
)

// 服务器
func newGRPCServer() *grpc.Server {
    return grpc.NewServer(
        grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
        grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
    )
}

// 客户端
func newGRPCClient() (*grpc.ClientConn, error) {
    return grpc.Dial(
        "localhost:50051",
        grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
    )
}
```

---

## 自定义 Propagator

```go
type CustomPropagator struct{}

func (p CustomPropagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    span := trace.SpanFromContext(ctx)
    sc := span.SpanContext()
    
    if sc.IsValid() {
        // 注入自定义格式
        carrier.Set("x-trace-id", sc.TraceID().String())
        carrier.Set("x-span-id", sc.SpanID().String())
    }
}

func (p CustomPropagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
    traceID := carrier.Get("x-trace-id")
    spanID := carrier.Get("x-span-id")
    
    if traceID == "" || spanID == "" {
        return ctx
    }
    
    // 解析并创建 SpanContext
    tid, _ := trace.TraceIDFromHex(traceID)
    sid, _ := trace.SpanIDFromHex(spanID)
    
    sc := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID: tid,
        SpanID:  sid,
        Remote:  true,
    })
    
    return trace.ContextWithRemoteSpanContext(ctx, sc)
}

func (p CustomPropagator) Fields() []string {
    return []string{"x-trace-id", "x-span-id"}
}
```

---

## 最佳实践

```go
// ✅ 正确: 组合 Propagators
otel.SetTextMapPropagator(
    propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ),
)

// ✅ 正确: 使用 otelhttp 自动处理
handler := otelhttp.NewHandler(myHandler, "server")

// ✅ 正确: 使用 otelgrpc 自动处理
grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
)

// ❌ 错误: 忘记设置 Propagator
// 默认是 NoOp, 不会传播任何信息
```

---

## 参考资源

- [W3C Trace Context](https://www.w3.org/TR/trace-context/)
- [W3C Baggage](https://www.w3.org/TR/baggage/)
- [01_Context管理.md](./01_Context管理.md)

---

**🎉 完成！Propagators 知识掌握！**

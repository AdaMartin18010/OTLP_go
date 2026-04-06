# 内部培训: OpenTelemetry基础

> **培训对象**: Go开发团队
> **时长**: 2小时
> **目标**: 掌握OTel核心概念与Go SDK基础使用

---

## 📚 培训大纲

### 第一部分: 可观测性三支柱 (30分钟)

#### 1.1 什么是可观测性?

```
传统监控: 我们知道系统有问题
可观测性: 我们能理解为什么有问题

可观测性 = Traces + Metrics + Logs (+ Profiles)
```

#### 1.2 Traces (分布式追踪)

```
┌─────────────────────────────────────────────────────────────┐
│                      分布式追踪示意                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  [User] ──▶ [API Gateway] ──▶ [Order Svc] ──▶ [DB]        │
│     │          │               │                           │
│     │          ▼               ▼                           │
│     │      TraceID: abc    TraceID: abc                    │
│     │      SpanID: 001     SpanID: 002                     │
│     │      Parent: -       Parent: 001                     │
│     │                                                      │
│     └──────────────────────────────────────────▶           │
│              完整调用链可视化                               │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**关键概念**:

- **Trace**: 端到端请求链路
- **Span**: 单个操作单元
- **TraceID**: 全局唯一链路标识
- **SpanID**: 单个Span标识
- **ParentID**: 父子关系

#### 1.3 Metrics (指标)

| 类型 | 用途 | 示例 |
|------|------|------|
| Counter | 累计值 | 请求总数 |
| Gauge | 瞬时值 | 内存使用 |
| Histogram | 分布统计 | 请求延迟 |
| Summary | 分位数 | P99延迟 |

#### 1.4 Logs (日志)

```go
// 结构化日志 vs 传统日志
// 传统: "User 123 failed to login"
// 结构化: {user_id: 123, event: "login_failed", reason: "invalid_password"}
```

---

### 第二部分: OpenTelemetry架构 (30分钟)

#### 2.1 OTel组件架构

```
┌─────────────────────────────────────────────────────────────┐
│                    OpenTelemetry架构                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  Application Layer                                          │
│  ┌─────────────────────────────────────────────────────┐   │
│  │  Tracer    │   Meter    │   Logger   │   Profiler  │   │
│  │  API/SDK   │   API/SDK  │   API/SDK  │   API/SDK   │   │
│  └──────┬─────────────┬─────────────┬───────────────────┘   │
│         │             │             │                       │
│  ┌──────┴─────────────┴─────────────┴───────────────────┐   │
│  │              OpenTelemetry Collector                   │   │
│  │   Receive ──▶ Process ──▶ Export                      │   │
│  └───────────────────────────────────────────────────────┘   │
│                             │                               │
│  ┌──────────────────────────┼────────────────────────────┐  │
│  │  Jaeger  │ Prometheus │   Loki   │  Parca/Pyroscope  │  │
│  └────────────────────────────────────────────────────────┘  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 2.2 Go SDK核心组件

```go
// 1. TracerProvider - 创建Tracer的工厂
tracerProvider := trace.NewTracerProvider(
    trace.WithBatcher(exporter),
    trace.WithResource(resource),
)

// 2. Tracer - 创建Span
tracer := tracerProvider.Tracer("my-service")

// 3. Span - 单个操作
ctx, span := tracer.Start(ctx, "operation-name")
defer span.End()
```

---

### 第三部分: 实战演练 (45分钟)

#### 3.1 基础Trace

```go
package main

import (
    "context"
    "log"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func main() {
    ctx := context.Background()

    // 初始化
    shutdown := initTracer(ctx)
    defer shutdown(ctx)

    // 创建Trace
    tracer := otel.Tracer("demo-service")
    ctx, span := tracer.Start(ctx, "main-operation")
    defer span.End()

    // 业务逻辑
    doWork(ctx)
}

func initTracer(ctx context.Context) func(context.Context) error {
    // 创建exporter
    exp, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatal(err)
    }

    // 创建Provider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exp),
        sdktrace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceName("demo-service"),
        )),
    )

    otel.SetTracerProvider(tp)
    return tp.Shutdown
}

func doWork(ctx context.Context) {
    tracer := otel.Tracer("demo-service")
    _, span := tracer.Start(ctx, "doWork")
    defer span.End()

    // 添加属性
    span.SetAttributes(
        attribute.String("work.type", "computation"),
        attribute.Int("work.items", 100),
    )

    time.Sleep(100 * time.Millisecond)
}
```

#### 3.2 Span属性与事件

```go
// 设置属性
span.SetAttributes(
    attribute.String("user.id", "12345"),
    attribute.Int("order.amount", 1000),
    attribute.Float64("order.discount", 0.15),
    attribute.Bool("order.vip", true),
)

// 记录事件
span.AddEvent("payment_initiated", trace.WithAttributes(
    attribute.String("payment.method", "credit_card"),
    attribute.String("payment.provider", "stripe"),
))

// 记录错误
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, "operation failed")
}
```

#### 3.3 Context传播

```go
// HTTP服务自动传播
func handler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context() // 自动提取parent context

    tracer := otel.Tracer("http-service")
    ctx, span := tracer.Start(ctx, r.URL.Path)
    defer span.End()

    // 处理请求...
}

// HTTP客户端自动注入
func callService(ctx context.Context) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)

    // 自动注入trace header
    resp, err := http.DefaultClient.Do(req)
    // ...
}
```

---

### 第四部分: 最佳实践 (15分钟)

#### 4.1 Span命名规范

```go
// ✅ Good
"GET /api/users/{id}"
"db.query"
"payment.process"

// ❌ Bad
"handler"
"doSomething"
"process"
```

#### 4.2 属性命名规范

```go
// ✅ Good
http.method = "GET"
http.status_code = 200
db.statement = "SELECT * FROM users"

// ❌ Bad
method = "GET"
status = 200
query = "SELECT * FROM users"
```

#### 4.3 性能注意事项

```go
// ✅ 使用采样减少开销
sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.1)) // 10%采样

// ✅ 异步批量导出
sdktrace.WithBatcher(exporter,
    sdktrace.WithBatchTimeout(time.Second),
    sdktrace.WithExportTimeout(30*time.Second),
)

// ❌ 避免创建过多span
// 每个函数都创建span会导致过大开销
```

---

## 📝 练习题

### 练习1: 基础Trace

创建一个简单的HTTP服务，为每个请求创建span。

### 练习2: 属性与事件

在span中添加用户ID、请求路径等属性，并记录关键事件。

### 练习3: 错误处理

模拟错误场景，正确记录错误信息。

---

## 📚 参考资料

- [OTel Go官方文档](https://opentelemetry.io/docs/languages/go/)
- [OTel语义约定](https://opentelemetry.io/docs/specs/semconv/)
- 本项目: `docs/research/otel-sdk/otel-sdk-tracerprovider-init.md`

---

**培训材料版本**: v1.0
**更新日期**: 2026-04-06

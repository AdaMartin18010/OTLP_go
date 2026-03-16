# Go 1.25.1 可观测性埋点模式（Instrumentation Patterns）

## 目录

- [Go 1.25.1 可观测性埋点模式（Instrumentation Patterns）](#go-1251-可观测性埋点模式instrumentation-patterns)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 埋点模式分类](#2-埋点模式分类)
    - [2.1 手动埋点（Manual Instrumentation）](#21-手动埋点manual-instrumentation)
    - [2.2 自动埋点（Automatic Instrumentation）](#22-自动埋点automatic-instrumentation)
    - [2.3 库埋点（Library Instrumentation）](#23-库埋点library-instrumentation)
  - [3. 核心埋点模式](#3-核心埋点模式)
    - [3.1 函数级埋点（Function-Level Instrumentation）](#31-函数级埋点function-level-instrumentation)
    - [3.2 中间件埋点（Middleware Instrumentation）](#32-中间件埋点middleware-instrumentation)
    - [3.3 客户端埋点（Client Instrumentation）](#33-客户端埋点client-instrumentation)
    - [3.4 异步任务埋点（Async Task Instrumentation）](#34-异步任务埋点async-task-instrumentation)
  - [4. Go 1.25.1 特性增强的埋点模式](#4-go-1251-特性增强的埋点模式)
    - [4.1 Goroutine 标识追踪](#41-goroutine-标识追踪)
    - [4.2 Context 取消传播追踪](#42-context-取消传播追踪)
    - [4.3 容器感知的资源埋点](#43-容器感知的资源埋点)
  - [5. 设计模式与 OTLP 集成](#5-设计模式与-otlp-集成)
    - [5.1 装饰器模式（Decorator Pattern）](#51-装饰器模式decorator-pattern)
    - [5.2 责任链模式（Chain of Responsibility）](#52-责任链模式chain-of-responsibility)
    - [5.3 观察者模式（Observer Pattern）](#53-观察者模式observer-pattern)
  - [6. 性能优化策略](#6-性能优化策略)
    - [6.1 零成本抽象（Zero-Cost Abstraction）](#61-零成本抽象zero-cost-abstraction)
    - [6.2 延迟初始化（Lazy Initialization）](#62-延迟初始化lazy-initialization)
    - [6.3 批量处理（Batching）](#63-批量处理batching)
  - [7. 错误处理与可观测性](#7-错误处理与可观测性)
    - [7.1 错误传播追踪](#71-错误传播追踪)
    - [7.2 Panic 恢复与追踪](#72-panic-恢复与追踪)
    - [7.3 超时与取消](#73-超时与取消)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 Span 命名规范](#81-span-命名规范)
    - [8.2 Attribute 选择原则](#82-attribute-选择原则)
    - [8.3 采样策略](#83-采样策略)
  - [9. 反模式（Anti-Patterns）](#9-反模式anti-patterns)
    - [9.1 过度埋点](#91-过度埋点)
    - [9.2 阻塞导出](#92-阻塞导出)
    - [9.3 忽略 Context 传播](#93-忽略-context-传播)
  - [10. 工程案例](#10-工程案例)
    - [10.1 HTTP 服务完整埋点](#101-http-服务完整埋点)
    - [10.2 数据库访问埋点](#102-数据库访问埋点)
    - [10.3 消息队列埋点](#103-消息队列埋点)
  - [11. 总结](#11-总结)
    - [核心贡献](#核心贡献)
    - [工程价值](#工程价值)

---

## 1. 概述

**Instrumentation**（可观测性埋点）是指在代码中插入观测逻辑（Trace、Metric、Log），以捕获系统运行时的状态与行为。

**核心挑战**：

1. **低侵入性**：埋点代码不应干扰业务逻辑
2. **低性能开销**：生产环境下不能显著降低吞吐量
3. **一致性**：跨服务、跨团队的埋点标准统一

**本文档目标**：

- 定义 Go 1.25.1 的**标准埋点模式**（Instrumentation Patterns）
- 展示如何利用 Go CSP 模型的特性优化埋点性能
- 提供工业级的埋点最佳实践

---

## 2. 埋点模式分类

### 2.1 手动埋点（Manual Instrumentation）

**定义**：开发者显式调用 OpenTelemetry API

**适用场景**：

- 业务逻辑复杂，需要精细控制 Span 边界
- 需要记录自定义业务 Metric

**示例**：

```go
func ProcessOrder(ctx context.Context, orderID string) error {
    tracer := otel.Tracer("order-service")
    ctx, span := tracer.Start(ctx, "process-order",
        trace.WithAttributes(attribute.String("order.id", orderID)),
    )
    defer span.End()
    
    // 业务逻辑...
    if err := validateOrder(ctx, orderID); err != nil {
        span.RecordError(err)
        return err
    }
    
    return nil
}
```

---

### 2.2 自动埋点（Automatic Instrumentation）

**定义**：通过库/框架自动注入埋点代码

**实现方式**：

1. **Middleware/Interceptor**（HTTP、gRPC）
2. **Wrapper**（Database Driver）
3. **编译时代码生成**（AST 转换）

**示例**（HTTP Middleware）：

```go
import "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

func main() {
    handler := http.HandlerFunc(HandleRequest)
    
    // 自动埋点：每个请求自动创建 Span
    wrappedHandler := otelhttp.NewHandler(handler, "http-server")
    
    http.ListenAndServe(":8080", wrappedHandler)
}
```

---

### 2.3 库埋点（Library Instrumentation）

**定义**：在公共库中内置埋点逻辑

**OpenTelemetry Contrib 支持的库**：

- `net/http`：HTTP 客户端/服务端
- `google.golang.org/grpc`：gRPC
- `database/sql`：SQL 数据库
- `github.com/redis/go-redis`：Redis
- `github.com/confluentinc/confluent-kafka-go`：Kafka

**示例**（gRPC）：

```go
import "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"

// 客户端自动埋点
conn, _ := grpc.Dial(target,
    grpc.WithStatsHandler(otelgrpc.NewClientHandler()),
)
```

---

## 3. 核心埋点模式

### 3.1 函数级埋点（Function-Level Instrumentation）

**模式**：每个函数对应一个 Span

```go
func businessLogic(ctx context.Context, data Data) error {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "businessLogic")
    defer span.End()
    
    // 记录输入参数
    span.SetAttributes(
        attribute.String("data.id", data.ID),
        attribute.Int("data.size", len(data.Items)),
    )
    
    // 业务逻辑
    result, err := process(ctx, data)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    // 记录输出结果
    span.SetAttributes(attribute.String("result.id", result.ID))
    
    return nil
}
```

**何时使用**：

- ✅ 函数执行时间 > 10ms
- ✅ 函数涉及 I/O 操作（DB、RPC、文件）
- ❌ 纯计算函数（`sum(a, b int) int`）

---

### 3.2 中间件埋点（Middleware Instrumentation）

**模式**：在 HTTP/gRPC 中间件层统一埋点

```go
func TracingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        tracer := otel.Tracer("http-server")
        
        // 提取上游 Context
        ctx := otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
        
        // 创建 Span
        ctx, span := tracer.Start(ctx, r.Method+" "+r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.HTTPMethodKey.String(r.Method),
                semconv.HTTPTargetKey.String(r.URL.Path),
                semconv.HTTPSchemeKey.String(r.URL.Scheme),
                semconv.NetHostNameKey.String(r.Host),
            ),
        )
        defer span.End()
        
        // 包装 ResponseWriter 以捕获状态码
        wrw := &responseWriter{ResponseWriter: w, statusCode: 200}
        
        // 调用下一个 Handler
        next.ServeHTTP(wrw, r.WithContext(ctx))
        
        // 记录响应状态
        span.SetAttributes(semconv.HTTPStatusCodeKey.Int(wrw.statusCode))
        if wrw.statusCode >= 400 {
            span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", wrw.statusCode))
        }
    })
}

type responseWriter struct {
    http.ResponseWriter
    statusCode int
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}
```

---

### 3.3 客户端埋点（Client Instrumentation）

**模式**：在调用外部服务时注入 Context

```go
func CallExternalAPI(ctx context.Context, url string) (*Response, error) {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "HTTP GET",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.HTTPMethodKey.String("GET"),
            semconv.HTTPURLKey.String(url),
        ),
    )
    defer span.End()
    
    // 创建请求
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    // 注入 Context 到 HTTP Header
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    // 发送请求
    resp, err := http.DefaultClient.Do(req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    defer resp.Body.Close()
    
    // 记录响应状态
    span.SetAttributes(semconv.HTTPStatusCodeKey.Int(resp.StatusCode))
    
    return parseResponse(resp)
}
```

---

### 3.4 异步任务埋点（Async Task Instrumentation）

**挑战**：Goroutine 的 Context 需要显式传递

**模式 1**：通过 Channel 传递 Context

```go
type Task struct {
    Ctx  context.Context
    Data []byte
}

func Worker(tasks <-chan Task) {
    tracer := otel.Tracer("worker")
    
    for task := range tasks {
        // 使用任务携带的 Context
        ctx, span := tracer.Start(task.Ctx, "worker-task")
        
        process(ctx, task.Data)
        
        span.End()
    }
}

func Producer(ctx context.Context) {
    tasks := make(chan Task, 100)
    
    go Worker(tasks)
    
    // 生产任务时传递 Context
    tasks <- Task{Ctx: ctx, Data: []byte("data")}
}
```

**模式 2**：使用 Link 关联异步 Span

```go
func AsyncProcess(ctx context.Context, data []byte) {
    tracer := otel.Tracer("my-service")
    
    // 获取当前 SpanContext
    parentSC := trace.SpanContextFromContext(ctx)
    
    go func() {
        // 创建新 Span 并通过 Link 关联到父 Span
        _, span := tracer.Start(context.Background(), "async-task",
            trace.WithLinks(trace.Link{SpanContext: parentSC}),
        )
        defer span.End()
        
        // 异步逻辑
        process(data)
    }()
}
```

---

## 4. Go 1.25.1 特性增强的埋点模式

### 4.1 Goroutine 标识追踪

Go 1.25.1 没有暴露 goroutine ID，但可以通过 Context 传递唯一标识：

```go
type goroutineIDKey struct{}

func WithGoroutineID(ctx context.Context, id string) context.Context {
    return context.WithValue(ctx, goroutineIDKey{}, id)
}

func GetGoroutineID(ctx context.Context) string {
    if id, ok := ctx.Value(goroutineIDKey{}).(string); ok {
        return id
    }
    return ""
}

func SpawnGoroutine(ctx context.Context, task func(context.Context)) {
    goroutineID := uuid.New().String()
    ctx = WithGoroutineID(ctx, goroutineID)
    
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "goroutine",
        trace.WithAttributes(attribute.String("goroutine.id", goroutineID)),
    )
    
    go func() {
        defer span.End()
        task(ctx)
    }()
}
```

---

### 4.2 Context 取消传播追踪

```go
func ProcessWithTimeout(ctx context.Context, timeout time.Duration) error {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "process-with-timeout")
    defer span.End()
    
    // 设置超时
    ctx, cancel := context.WithTimeout(ctx, timeout)
    defer cancel()
    
    // 监听取消事件
    done := make(chan error, 1)
    go func() {
        done <- doWork(ctx)
    }()
    
    select {
    case err := <-done:
        return err
    case <-ctx.Done():
        span.AddEvent("context-cancelled",
            trace.WithAttributes(attribute.String("reason", ctx.Err().Error())),
        )
        span.SetStatus(codes.Error, "context cancelled")
        return ctx.Err()
    }
}
```

---

### 4.3 容器感知的资源埋点

```go
import (
    "runtime"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func NewContainerAwareResource() *resource.Resource {
    attrs := []attribute.KeyValue{
        semconv.ServiceNameKey.String("my-service"),
        semconv.ServiceVersionKey.String("1.0.0"),
        semconv.ProcessRuntimeName("go"),
        semconv.ProcessRuntimeVersion(runtime.Version()),
    }
    
    // Go 1.25.1 容器感知检测
    if isInContainer() {
        cpuQuota, cpuPeriod := readCgroupCPUQuota()
        memLimit := readCgroupMemoryLimit()
        
        attrs = append(attrs,
            attribute.Float64("container.cpu.limit", float64(cpuQuota)/float64(cpuPeriod)),
            attribute.Int64("container.memory.limit", memLimit),
            attribute.Bool("process.runtime.container_aware", true),
        )
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...)
}
```

---

## 5. 设计模式与 OTLP 集成

### 5.1 装饰器模式（Decorator Pattern）

**用途**：为现有函数添加埋点逻辑

```go
type BusinessFunc func(context.Context, Data) error

func WithTracing(name string, fn BusinessFunc) BusinessFunc {
    return func(ctx context.Context, data Data) error {
        tracer := otel.Tracer("my-service")
        ctx, span := tracer.Start(ctx, name)
        defer span.End()
        
        err := fn(ctx, data)
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        }
        
        return err
    }
}

// 使用
var ProcessOrder = WithTracing("process-order", func(ctx context.Context, data Data) error {
    // 业务逻辑...
    return nil
})
```

---

### 5.2 责任链模式（Chain of Responsibility）

**用途**：HTTP/gRPC 中间件链

```go
type Middleware func(http.Handler) http.Handler

func ChainMiddlewares(handler http.Handler, middlewares ...Middleware) http.Handler {
    for i := len(middlewares) - 1; i >= 0; i-- {
        handler = middlewares[i](handler)
    }
    return handler
}

func main() {
    handler := http.HandlerFunc(HandleRequest)
    
    // 组合多个中间件
    handler = ChainMiddlewares(handler,
        TracingMiddleware,
        MetricsMiddleware,
        LoggingMiddleware,
    )
    
    http.ListenAndServe(":8080", handler)
}
```

---

### 5.3 观察者模式（Observer Pattern）

**用途**：Metric 定期采样

```go
type MetricCollector struct {
    meter  metric.Meter
    gauges []metric.Float64ObservableGauge
}

func NewMetricCollector() *MetricCollector {
    meter := otel.Meter("my-service")
    
    cpuGauge, _ := meter.Float64ObservableGauge("process.cpu.usage")
    memGauge, _ := meter.Float64ObservableGauge("process.memory.usage")
    
    _, _ = meter.RegisterCallback(func(ctx context.Context, o metric.Observer) error {
        o.ObserveFloat64(cpuGauge, getCPUUsage())
        o.ObserveFloat64(memGauge, getMemoryUsage())
        return nil
    }, cpuGauge, memGauge)
    
    return &MetricCollector{meter: meter}
}
```

---

## 6. 性能优化策略

### 6.1 零成本抽象（Zero-Cost Abstraction）

**原则**：未启用追踪时，埋点代码应无性能开销

```go
// ❌ 错误：总是创建 Span
func BadExample(ctx context.Context) {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
    // ...
}

// ✅ 正确：通过 NoOp Provider 实现零成本
// 当 otel.SetTracerProvider(noop.NewTracerProvider()) 时，
// tracer.Start() 返回的是空操作（no-op）
```

---

### 6.2 延迟初始化（Lazy Initialization）

```go
var (
    tracerOnce sync.Once
    tracer     trace.Tracer
)

func getTracer() trace.Tracer {
    tracerOnce.Do(func() {
        tracer = otel.Tracer("my-service")
    })
    return tracer
}
```

---

### 6.3 批量处理（Batching）

```go
// 使用 BatchSpanProcessor 而非 SimpleSpanProcessor
tracerProvider := trace.NewTracerProvider(
    trace.WithBatcher(exporter,
        trace.WithMaxQueueSize(2048),
        trace.WithMaxExportBatchSize(512),
        trace.WithBatchTimeout(5*time.Second),
    ),
)
```

---

## 7. 错误处理与可观测性

### 7.1 错误传播追踪

```go
func ProcessRequest(ctx context.Context, req Request) error {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "process-request")
    defer span.End()
    
    if err := validate(ctx, req); err != nil {
        span.RecordError(err, trace.WithAttributes(
            attribute.String("error.type", "validation"),
        ))
        span.SetStatus(codes.Error, "validation failed")
        return fmt.Errorf("validate: %w", err)
    }
    
    if err := process(ctx, req); err != nil {
        span.RecordError(err, trace.WithAttributes(
            attribute.String("error.type", "processing"),
        ))
        span.SetStatus(codes.Error, "processing failed")
        return fmt.Errorf("process: %w", err)
    }
    
    return nil
}
```

---

### 7.2 Panic 恢复与追踪

```go
func SafeExecute(ctx context.Context, fn func(context.Context)) (err error) {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "safe-execute")
    defer span.End()
    
    defer func() {
        if r := recover(); r != nil {
            err = fmt.Errorf("panic: %v", r)
            span.RecordError(err, trace.WithAttributes(
                attribute.String("panic.value", fmt.Sprintf("%v", r)),
                attribute.String("panic.stack", string(debug.Stack())),
            ))
            span.SetStatus(codes.Error, "panic recovered")
        }
    }()
    
    fn(ctx)
    return nil
}
```

---

### 7.3 超时与取消

```go
func ProcessWithDeadline(ctx context.Context, deadline time.Duration) error {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "process-with-deadline")
    defer span.End()
    
    ctx, cancel := context.WithTimeout(ctx, deadline)
    defer cancel()
    
    resultCh := make(chan error, 1)
    go func() {
        resultCh <- doWork(ctx)
    }()
    
    select {
    case err := <-resultCh:
        return err
    case <-ctx.Done():
        span.AddEvent("deadline-exceeded")
        span.SetStatus(codes.Error, "deadline exceeded")
        return ctx.Err()
    }
}
```

---

## 8. 最佳实践

### 8.1 Span 命名规范

| 类型         | 命名规范                        | 示例                          |
|------------|---------------------------------|-------------------------------|
| **HTTP**   | `<METHOD> <route>`              | `GET /api/users/:id`          |
| **gRPC**   | `<package>.<service>/<method>`  | `user.UserService/GetUser`    |
| **数据库** | `<operation> <table>`           | `SELECT users`                |
| **函数**   | `<function-name>`               | `processPayment`              |
| **异步**   | `<task-type>`                   | `kafka-consume-order-events`  |

---

### 8.2 Attribute 选择原则

**高基数 Attribute**（❌ 避免）：

- 用户 ID、订单 ID（会导致时间序列爆炸）
- 时间戳（每个请求都不同）

**低基数 Attribute**（✅ 推荐）：

- HTTP Method (`GET`, `POST`)
- HTTP Status Code (`200`, `404`, `500`)
- 环境（`dev`, `staging`, `prod`）

**解决方案**：高基数数据放在 Span Event 而非 Attribute

```go
// ❌ 错误
span.SetAttributes(attribute.String("user.id", userID))

// ✅ 正确
span.AddEvent("user-identified", trace.WithAttributes(
    attribute.String("user.id", userID),
))
```

---

### 8.3 采样策略

```go
func NewSampler() trace.Sampler {
    return trace.ParentBased(
        // 根 Span 采样策略
        trace.TraceIDRatioBased(0.1),  // 10% 采样率
        trace.WithRemoteParentSampled(trace.AlwaysSample()),       // 上游已采样，继续采样
        trace.WithRemoteParentNotSampled(trace.NeverSample()),     // 上游未采样，不采样
        trace.WithLocalParentSampled(trace.AlwaysSample()),        // 本地父 Span 已采样，继续采样
        trace.WithLocalParentNotSampled(trace.NeverSample()),      // 本地父 Span 未采样，不采样
    )
}
```

---

## 9. 反模式（Anti-Patterns）

### 9.1 过度埋点

**❌ 错误示例**：

```go
func Sum(a, b int) int {
    tracer := otel.Tracer("my-service")
    _, span := tracer.Start(context.Background(), "sum")  // ← 不必要
    defer span.End()
    return a + b
}
```

**✅ 正确示例**：

```go
// 纯计算函数不需要埋点
func Sum(a, b int) int {
    return a + b
}
```

---

### 9.2 阻塞导出

**❌ 错误示例**：

```go
// SimpleSpanProcessor 同步导出（阻塞业务逻辑）
tracerProvider := trace.NewTracerProvider(
    trace.WithSyncer(exporter),  // ← 阻塞
)
```

**✅ 正确示例**：

```go
// BatchSpanProcessor 异步导出
tracerProvider := trace.NewTracerProvider(
    trace.WithBatcher(exporter),  // ← 非阻塞
)
```

---

### 9.3 忽略 Context 传播

**❌ 错误示例**：

```go
func HandleRequest(w http.ResponseWriter, r *http.Request) {
    // 直接创建新 Context，丢失上游 Trace
    ctx := context.Background()  // ← 错误
    ctx, span := tracer.Start(ctx, "handle")
    defer span.End()
}
```

**✅ 正确示例**：

```go
func HandleRequest(w http.ResponseWriter, r *http.Request) {
    // 提取上游 Context
    ctx := otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
    ctx, span := tracer.Start(ctx, "handle")
    defer span.End()
}
```

---

## 10. 工程案例

### 10.1 HTTP 服务完整埋点

```go
package main

import (
    "context"
    "net/http"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/propagation"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func main() {
    // 初始化 OTLP
    ctx := context.Background()
    exporter, _ := otlptracegrpc.New(ctx, otlptracegrpc.WithInsecure())
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithResource(newResource()),
        trace.WithSampler(trace.ParentBased(trace.TraceIDRatioBased(0.1))),
    )
    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    
    // 注册 Handler
    http.Handle("/api/orders", ChainMiddlewares(
        http.HandlerFunc(HandleOrders),
        TracingMiddleware,
        MetricsMiddleware,
    ))
    
    http.ListenAndServe(":8080", nil)
}

func HandleOrders(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("order-service")
    ctx, span := tracer.Start(ctx, "handle-orders")
    defer span.End()
    
    orders, err := fetchOrders(ctx)
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    json.NewEncoder(w).Encode(orders)
}

func fetchOrders(ctx context.Context) ([]Order, error) {
    tracer := otel.Tracer("order-service")
    ctx, span := tracer.Start(ctx, "fetch-orders")
    defer span.End()
    
    // 数据库查询...
    return queryDB(ctx, "SELECT * FROM orders")
}
```

---

### 10.2 数据库访问埋点

```go
import (
    "database/sql"
    "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func InitDB() (*sql.DB, error) {
    // 使用 otelsql 包装驱动
    driverName, err := otelsql.Register("postgres",
        otelsql.WithAttributes(semconv.DBSystemPostgreSQL),
    )
    if err != nil {
        return nil, err
    }
    
    db, err := sql.Open(driverName, "postgres://user:pass@localhost/db")
    if err != nil {
        return nil, err
    }
    
    // 记录 DB 连接池指标
    if err := otelsql.RecordStats(db); err != nil {
        return nil, err
    }
    
    return db, nil
}

func QueryUsers(ctx context.Context, db *sql.DB) ([]User, error) {
    // 自动创建 Span：database.sql.query
    rows, err := db.QueryContext(ctx, "SELECT id, name FROM users")
    if err != nil {
        return nil, err
    }
    defer rows.Close()
    
    var users []User
    for rows.Next() {
        var user User
        rows.Scan(&user.ID, &user.Name)
        users = append(users, user)
    }
    
    return users, nil
}
```

---

### 10.3 消息队列埋点

```go
func ProduceKafkaMessage(ctx context.Context, topic string, value []byte) error {
    tracer := otel.Tracer("kafka-producer")
    ctx, span := tracer.Start(ctx, "produce-message",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("kafka"),
            semconv.MessagingDestinationKey.String(topic),
        ),
    )
    defer span.End()
    
    msg := &kafka.Message{
        TopicPartition: kafka.TopicPartition{Topic: &topic},
        Value:          value,
    }
    
    // 注入 Context 到消息头
    otel.GetTextMapPropagator().Inject(ctx, &KafkaHeaderCarrier{msg})
    
    if err := producer.Produce(msg, nil); err != nil {
        span.RecordError(err)
        return err
    }
    
    return nil
}
```

---

## 11. 总结

### 核心贡献

1. **埋点模式分类**：
   - 手动埋点、自动埋点、库埋点的适用场景与实现方式
   - 函数级、中间件级、客户端、异步任务的埋点模式

2. **Go 1.25.1 特性集成**：
   - 容器感知的资源埋点
   - Context 取消传播追踪
   - Goroutine 标识传递

3. **设计模式应用**：
   - 装饰器模式（WithTracing）
   - 责任链模式（Middleware Chain）
   - 观察者模式（Metric Callback）

4. **性能优化**：
   - 零成本抽象（NoOp Provider）
   - 批量处理（BatchSpanProcessor）
   - 采样策略（TraceIDRatioBased）

### 工程价值

| 价值维度       | 具体体现                                                                 |
|--------------|-------------------------------------------------------------------------|
| **可维护性**   | 标准化埋点模式降低团队协作成本                                              |
| **性能**       | BatchSpanProcessor 降低 90% 的导出延迟                                    |
| **灵活性**     | 装饰器模式支持动态添加/移除埋点                                             |
| **兼容性**     | Contrib 库自动适配主流框架（HTTP、gRPC、SQL）                              |

---

**下一步**：

- [gRPC OTLP Integration](./03-grpc-otlp-integration.md)
- [Collector Pipeline Design](./04-collector-pipeline-design.md)

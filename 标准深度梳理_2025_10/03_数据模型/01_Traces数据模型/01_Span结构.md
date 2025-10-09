# Span 结构完整指南

## 📋 目录

- [概述](#概述)
- [Span 定义](#span-定义)
- [核心字段](#核心字段)
  - [标识字段](#标识字段)
  - [时间字段](#时间字段)
  - [元数据字段](#元数据字段)
  - [内容字段](#内容字段)
- [Span 生命周期](#span-生命周期)
- [Go 完整实现](#go-完整实现)
- [最佳实践](#最佳实践)
- [常见问题](#常见问题)
- [参考资源](#参考资源)

---

## 概述

**Span** 是 OpenTelemetry 追踪的基本单位，代表一个操作或工作单元。每个 Span 记录了操作的开始时间、结束时间、属性、事件和状态。

### 关键特性

- ✅ **层次结构**: Span 可以有父子关系，形成追踪树
- ✅ **分布式**: Span 可以跨越多个服务和进程
- ✅ **丰富的元数据**: 支持属性、事件、链接
- ✅ **因果关系**: 通过 SpanContext 传播因果关系

---

## Span 定义

### 形式化定义

```text
Span := {
    TraceID:         [16]byte         // 追踪标识符
    SpanID:          [8]byte          // Span 标识符
    ParentSpanID:    [8]byte          // 父 Span 标识符 (可选)
    Name:            string           // 操作名称
    Kind:            SpanKind         // Span 类型
    StartTime:       Timestamp        // 开始时间 (纳秒)
    EndTime:         Timestamp        // 结束时间 (纳秒)
    Attributes:      []Attribute      // 键值对属性
    Events:          []Event          // 时间点事件
    Links:           []Link           // 到其他 Span 的链接
    Status:          Status           // 状态
    Resource:        Resource         // 资源信息 (继承自 TracerProvider)
    InstrumentationScope: Scope       // 仪表库信息
}
```

### OTLP Protocol Buffers 定义

```protobuf
message Span {
  bytes trace_id = 1;                     // 16 bytes
  bytes span_id = 2;                      // 8 bytes
  string trace_state = 3;                 // W3C TraceState
  bytes parent_span_id = 4;               // 8 bytes (optional)
  string name = 5;                        // Operation name
  SpanKind kind = 6;                      // Span kind
  fixed64 start_time_unix_nano = 7;       // Start timestamp
  fixed64 end_time_unix_nano = 8;         // End timestamp
  repeated KeyValue attributes = 9;        // Attributes
  uint32 dropped_attributes_count = 10;
  repeated Event events = 11;              // Events
  uint32 dropped_events_count = 12;
  repeated Link links = 13;                // Links
  uint32 dropped_links_count = 14;
  Status status = 15;                      // Status
}
```

---

## 核心字段

### 标识字段

#### 1. TraceID

**定义**: 128-bit 全局唯一标识符，标识整个分布式追踪。

**格式**: 16 bytes (32 个十六进制字符)

**示例**: `4bf92f3577b34da6a3ce929d0e0e4736`

**Go 实现**:

```go
import (
    "go.opentelemetry.io/otel/trace"
    "crypto/rand"
)

// 生成 TraceID
func generateTraceID() trace.TraceID {
    var traceID trace.TraceID
    _, _ = rand.Read(traceID[:])
    return traceID
}

// 解析 TraceID
func parseTraceID(s string) (trace.TraceID, error) {
    return trace.TraceIDFromHex(s)
}

// 示例
func main() {
    traceID := generateTraceID()
    fmt.Printf("TraceID: %s\n", traceID.String())
    // Output: 4bf92f3577b34da6a3ce929d0e0e4736
}
```

#### 2. SpanID

**定义**: 64-bit 标识符，在 Trace 内唯一标识一个 Span。

**格式**: 8 bytes (16 个十六进制字符)

**示例**: `00f067aa0ba902b7`

**Go 实现**:

```go
// 生成 SpanID
func generateSpanID() trace.SpanID {
    var spanID trace.SpanID
    _, _ = rand.Read(spanID[:])
    return spanID
}

// 解析 SpanID
func parseSpanID(s string) (trace.SpanID, error) {
    return trace.SpanIDFromHex(s)
}
```

#### 3. ParentSpanID

**定义**: 父 Span 的 SpanID，用于建立层次关系。

**规则**:

- 根 Span 的 ParentSpanID 为空 (全零)
- 子 Span 的 ParentSpanID 指向父 Span

**示例**:

```go
// 创建根 Span
ctx, rootSpan := tracer.Start(context.Background(), "root-operation")
defer rootSpan.End()

// 创建子 Span (自动设置 ParentSpanID)
ctx, childSpan := tracer.Start(ctx, "child-operation")
defer childSpan.End()

// 检查层次关系
rootSpanContext := trace.SpanContextFromContext(ctx)
fmt.Printf("Root SpanID: %s\n", rootSpanContext.SpanID().String())
```

---

### 时间字段

#### 1. StartTime

**定义**: Span 开始时间，Unix 纳秒时间戳。

**类型**: `fixed64` (uint64, 纳秒)

**Go 实现**:

```go
import "time"

// 记录开始时间
startTime := time.Now()

// 转换为纳秒时间戳
startNano := startTime.UnixNano()

// 从纳秒时间戳恢复
recoveredTime := time.Unix(0, startNano)
```

#### 2. EndTime

**定义**: Span 结束时间，Unix 纳秒时间戳。

**规则**:

- EndTime >= StartTime
- 未结束的 Span，EndTime 为 0

**持续时间计算**:

```go
func spanDuration(span trace.Span) time.Duration {
    // OpenTelemetry SDK 自动计算
    // Duration = EndTime - StartTime
    return span.End() - span.Start()
}

// 手动计算
func calculateDuration(startNano, endNano uint64) time.Duration {
    return time.Duration(endNano - startNano)
}
```

---

### 元数据字段

#### 1. Name

**定义**: Span 的人类可读名称，描述操作。

**命名规范**:

- 使用小写字母
- 使用下划线分隔单词
- 避免高基数值 (如 URL 参数、用户 ID)

**示例**:

```go
// ✅ 推荐
tracer.Start(ctx, "http_request")
tracer.Start(ctx, "database_query")
tracer.Start(ctx, "process_payment")

// ❌ 避免
tracer.Start(ctx, "GET /users/123")      // 包含 ID (高基数)
tracer.Start(ctx, "query_user_12345")    // 包含 ID
```

#### 2. Kind

**定义**: Span 的类型，描述操作的角色。

**类型**:

- `INTERNAL`: 内部操作 (默认)
- `SERVER`: 服务器端 RPC
- `CLIENT`: 客户端 RPC
- `PRODUCER`: 消息生产者
- `CONSUMER`: 消息消费者

**Go 实现**:

```go
import "go.opentelemetry.io/otel/trace"

// 服务器端 Span
ctx, span := tracer.Start(ctx, "handle_request",
    trace.WithSpanKind(trace.SpanKindServer),
)

// 客户端 Span
ctx, span := tracer.Start(ctx, "call_api",
    trace.WithSpanKind(trace.SpanKindClient),
)

// 消息生产者
ctx, span := tracer.Start(ctx, "publish_message",
    trace.WithSpanKind(trace.SpanKindProducer),
)
```

#### 3. Resource

**定义**: 产生 Span 的资源 (服务、主机、容器等)。

**继承**: 从 TracerProvider 继承，所有 Span 共享。

**示例**:

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// 创建 Resource
res, _ := resource.New(ctx,
    resource.WithAttributes(
        semconv.ServiceNameKey.String("payment-service"),
        semconv.ServiceVersionKey.String("1.0.0"),
    ),
)

// 创建 TracerProvider (所有 Span 自动继承 Resource)
tp := sdktrace.NewTracerProvider(
    sdktrace.WithResource(res),
)
```

#### 4. InstrumentationScope

**定义**: 产生 Span 的仪表库信息。

**字段**:

- `Name`: 仪表库名称 (必需)
- `Version`: 仪表库版本 (可选)
- `SchemaURL`: 语义约定 Schema URL (可选)

**Go 实现**:

```go
// 创建 Tracer (自动设置 InstrumentationScope)
tracer := otel.Tracer(
    "github.com/myapp/orders",          // Name
    trace.WithInstrumentationVersion("1.2.3"),  // Version
    trace.WithSchemaURL(semconv.SchemaURL),     // SchemaURL
)

// 创建的所有 Span 都包含此 InstrumentationScope
ctx, span := tracer.Start(ctx, "process_order")
```

---

### 内容字段

#### 1. Attributes

**定义**: 键值对属性，描述 Span 的详细信息。

**类型**:

- String, Boolean, Int64, Float64
- Array of String, Boolean, Int64, Float64

**限制**:

- 默认最大数量: 128 个
- 默认最大值长度: 无限制 (建议 < 1KB)

**Go 实现**:

```go
import (
    "go.opentelemetry.io/otel/attribute"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

span.SetAttributes(
    // 标准属性
    semconv.HTTPMethodKey.String("GET"),
    semconv.HTTPURLKey.String("https://api.example.com/users"),
    semconv.HTTPStatusCodeKey.Int(200),
    
    // 自定义属性
    attribute.String("user.tier", "premium"),
    attribute.Int("retry.count", 3),
    attribute.Bool("cache.hit", true),
    attribute.Float64("response.time", 0.123),
    
    // 数组属性
    attribute.StringSlice("tags", []string{"urgent", "high-priority"}),
)
```

#### 2. Events

**定义**: Span 生命周期中的时间点事件。

**字段**:

- `Name`: 事件名称
- `Timestamp`: 事件时间 (纳秒)
- `Attributes`: 事件属性

**Go 实现**:

```go
// 添加事件
span.AddEvent("cache_miss", trace.WithAttributes(
    attribute.String("cache.key", "user:123"),
    attribute.String("cache.type", "redis"),
))

// 添加异常事件
span.RecordError(err, trace.WithAttributes(
    attribute.String("error.type", "database_timeout"),
))

// 添加带时间戳的事件
span.AddEvent("custom_event",
    trace.WithTimestamp(time.Now()),
    trace.WithAttributes(
        attribute.String("detail", "something happened"),
    ),
)
```

#### 3. Links

**定义**: 到其他 Span 的因果链接。

**用途**:

- 批处理：一个 Span 处理多个消息
- 异步操作：Span 之间不是父子关系
- 请求合并：多个请求合并为一个

**Go 实现**:

```go
// 创建 Link
link := trace.Link{
    SpanContext: linkedSpanContext,
    Attributes: []attribute.KeyValue{
        attribute.String("link.type", "follows_from"),
    },
}

// 创建带 Links 的 Span
ctx, span := tracer.Start(ctx, "batch_process",
    trace.WithLinks(link),
)
```

#### 4. Status

**定义**: Span 的最终状态。

**值**:

- `Unset`: 未设置 (默认)
- `Ok`: 成功
- `Error`: 错误

**Go 实现**:

```go
import "go.opentelemetry.io/otel/codes"

// 成功
span.SetStatus(codes.Ok, "")

// 错误
span.SetStatus(codes.Error, "Database connection failed")

// 未设置 (默认)
// 不需要显式设置
```

---

## Span 生命周期

### 1. 创建阶段

```go
// 1. 创建 Span
ctx, span := tracer.Start(ctx, "operation_name",
    trace.WithSpanKind(trace.SpanKindServer),
    trace.WithAttributes(
        semconv.HTTPMethodKey.String("GET"),
    ),
)
defer span.End()

// 2. 系统自动设置
// - TraceID (如果 ctx 中没有，则生成新的)
// - SpanID (始终生成新的)
// - ParentSpanID (从 ctx 中提取)
// - StartTime (当前时间)
```

### 2. 活跃阶段

```go
// 1. 添加属性
span.SetAttributes(
    attribute.String("user.id", "user123"),
)

// 2. 添加事件
span.AddEvent("cache_lookup")

// 3. 记录错误
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
}

// 4. 更新名称 (不推荐)
span.SetName("new_operation_name")
```

### 3. 结束阶段

```go
// 1. 显式结束
span.End()

// 2. 系统自动设置
// - EndTime (当前时间)

// 3. 延迟结束 (使用 defer)
ctx, span := tracer.Start(ctx, "operation")
defer span.End()  // 在函数返回时自动调用
```

### 完整示例

```go
func processRequest(ctx context.Context, req *Request) error {
    // 1. 创建 Span
    ctx, span := tracer.Start(ctx, "process_request",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    // 2. 添加初始属性
    span.SetAttributes(
        semconv.HTTPMethodKey.String(req.Method),
        semconv.HTTPURLKey.String(req.URL),
    )

    // 3. 执行操作
    span.AddEvent("start_validation")
    if err := validateRequest(req); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Validation failed")
        return err
    }

    span.AddEvent("start_processing")
    result, err := processData(ctx, req.Data)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Processing failed")
        return err
    }

    // 4. 记录成功
    span.SetAttributes(
        attribute.Int("result.count", len(result)),
    )
    span.SetStatus(codes.Ok, "")

    return nil
}
```

---

## Go 完整实现

### 基础 Span 创建

```go
package main

import (
    "context"
    "log"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 1. 创建导出器
    exporter, err := stdouttrace.New(
        stdouttrace.WithPrettyPrint(),
    )
    if err != nil {
        log.Fatal(err)
    }

    // 2. 创建 Resource
    res, err := resource.New(context.Background(),
        resource.WithAttributes(
            semconv.ServiceNameKey.String("span-demo"),
            semconv.ServiceVersionKey.String("1.0.0"),
        ),
    )
    if err != nil {
        log.Fatal(err)
    }

    // 3. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )
    defer func() {
        if err := tp.Shutdown(context.Background()); err != nil {
            log.Fatal(err)
        }
    }()
    otel.SetTracerProvider(tp)

    // 4. 创建 Tracer
    tracer := otel.Tracer("span-demo")

    // 5. 创建并使用 Span
    ctx := context.Background()
    demoSpan(ctx, tracer)
}

func demoSpan(ctx context.Context, tracer trace.Tracer) {
    // 创建根 Span
    ctx, rootSpan := tracer.Start(ctx, "root_operation",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer rootSpan.End()

    rootSpan.SetAttributes(
        semconv.HTTPMethodKey.String("GET"),
        semconv.HTTPURLKey.String("https://api.example.com/data"),
    )

    // 模拟处理
    time.Sleep(50 * time.Millisecond)
    rootSpan.AddEvent("processing_started")

    // 创建子 Span
    childSpanDemo(ctx, tracer)

    // 记录成功
    rootSpan.SetStatus(codes.Ok, "")
}

func childSpanDemo(ctx context.Context, tracer trace.Tracer) {
    ctx, span := tracer.Start(ctx, "child_operation",
        trace.WithSpanKind(trace.SpanKindInternal),
    )
    defer span.End()

    span.SetAttributes(
        attribute.String("operation.type", "database_query"),
    )

    time.Sleep(30 * time.Millisecond)
    span.AddEvent("query_executed")

    span.SetStatus(codes.Ok, "")
}
```

### 高级 Span 模式

```go
// 1. 条件化 Span 创建
func conditionalSpan(ctx context.Context, tracer trace.Tracer, debug bool) {
    if debug {
        var span trace.Span
        ctx, span = tracer.Start(ctx, "debug_operation")
        defer span.End()
    }
    
    // 执行操作
    doWork(ctx)
}

// 2. 跨 Goroutine 的 Span
func parallelSpans(ctx context.Context, tracer trace.Tracer) {
    ctx, span := tracer.Start(ctx, "parallel_parent")
    defer span.End()

    var wg sync.WaitGroup
    for i := 0; i < 3; i++ {
        wg.Add(1)
        go func(i int) {
            defer wg.Done()
            
            // 每个 Goroutine 创建自己的子 Span
            _, childSpan := tracer.Start(ctx, fmt.Sprintf("parallel_child_%d", i))
            defer childSpan.End()
            
            time.Sleep(time.Duration(i*10) * time.Millisecond)
        }(i)
    }
    wg.Wait()
}

// 3. 带超时的 Span
func spanWithTimeout(ctx context.Context, tracer trace.Tracer) error {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()

    ctx, span := tracer.Start(ctx, "timeout_operation")
    defer span.End()

    done := make(chan error, 1)
    go func() {
        done <- doLongOperation()
    }()

    select {
    case err := <-done:
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            return err
        }
        span.SetStatus(codes.Ok, "")
        return nil
    case <-ctx.Done():
        err := ctx.Err()
        span.RecordError(err)
        span.SetStatus(codes.Error, "Operation timeout")
        return err
    }
}
```

---

## 最佳实践

### 1. 使用 defer 结束 Span

```go
// ✅ 推荐
ctx, span := tracer.Start(ctx, "operation")
defer span.End()

// ❌ 避免
ctx, span := tracer.Start(ctx, "operation")
// ... 可能忘记调用 span.End()
```

### 2. 传递 Context

```go
// ✅ 推荐：始终传递 Context
func processRequest(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()
    
    doSubTask(ctx)  // 传递 ctx
}

// ❌ 避免：不传递 Context
func processRequest(ctx context.Context) {
    _, span := tracer.Start(ctx, "process")
    defer span.End()
    
    doSubTask(context.Background())  // 失去父子关系
}
```

### 3. 设置有意义的 Span 名称

```go
// ✅ 推荐：低基数、描述性名称
tracer.Start(ctx, "get_user")
tracer.Start(ctx, "update_order")
tracer.Start(ctx, "validate_payment")

// ❌ 避免：高基数名称
tracer.Start(ctx, fmt.Sprintf("get_user_%s", userID))  // 包含 ID
tracer.Start(ctx, req.URL.Path)                        // URL 路径
```

### 4. 合理使用 Attributes

```go
// ✅ 推荐：使用标准语义约定
span.SetAttributes(
    semconv.HTTPMethodKey.String("GET"),
    semconv.HTTPStatusCodeKey.Int(200),
)

// ✅ 允许：自定义属性 (低基数)
span.SetAttributes(
    attribute.String("user.tier", "premium"),
    attribute.String("region", "us-west"),
)

// ❌ 避免：高基数属性
span.SetAttributes(
    attribute.String("user.id", userID),      // 数百万不同值
    attribute.String("request.id", reqID),    // 每个请求都不同
)
```

### 5. 错误处理

```go
// ✅ 推荐：记录错误并设置状态
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    return err
}

// ❌ 避免：只设置状态
if err != nil {
    span.SetStatus(codes.Error, err.Error())
    // 没有调用 RecordError，丢失堆栈信息
    return err
}
```

---

## 常见问题

### Q1: Span 什么时候应该结束？

**A**: 在操作完成时立即结束，通常使用 `defer`。

```go
// ✅ 推荐
func operation() error {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()  // 在函数返回时自动结束
    
    // ... 操作代码
    return nil
}
```

---

### Q2: 如何处理跨 Goroutine 的 Span？

**A**: 每个 Goroutine 应该创建自己的子 Span。

```go
// ✅ 推荐
func parallelWork(ctx context.Context) {
    ctx, parentSpan := tracer.Start(ctx, "parent")
    defer parentSpan.End()
    
    var wg sync.WaitGroup
    for i := 0; i < 3; i++ {
        wg.Add(1)
        go func(i int) {
            defer wg.Done()
            
            // 每个 Goroutine 创建子 Span
            _, childSpan := tracer.Start(ctx, fmt.Sprintf("child_%d", i))
            defer childSpan.End()
            
            // 执行工作
        }(i)
    }
    wg.Wait()
}
```

---

### Q3: Span 可以在结束后修改吗？

**A**: 不可以。Span 结束后，所有修改都会被忽略。

```go
ctx, span := tracer.Start(ctx, "operation")
span.End()

// ❌ 这些操作都会被忽略
span.SetAttributes(attribute.String("late", "attribute"))
span.AddEvent("late_event")
span.SetStatus(codes.Error, "late_error")
```

---

### Q4: 如何避免 Span 泄漏？

**A**: 始终使用 `defer span.End()`。

```go
// ✅ 推荐
func operation() {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()  // 即使 panic 也会被调用
    
    // ... 操作代码
}

// ❌ 避免
func operation() {
    ctx, span := tracer.Start(ctx, "operation")
    
    // ... 操作代码
    
    span.End()  // 如果中间 return 或 panic，不会被调用
}
```

---

### Q5: Span 的属性数量有限制吗？

**A**: 有。默认限制是 128 个属性，可以配置。

```go
// 配置属性限制
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSpanLimits(sdktrace.SpanLimits{
        AttributeCountLimit:      128,    // 最大属性数
        AttributeValueLengthLimit: 1024,  // 最大属性值长度
    }),
)

// 超出限制的属性会被丢弃
span.SetAttributes(/* ... 129+ attributes ... */)
// 只有前 128 个被保留
```

---

## 参考资源

### 官方文档

- [OpenTelemetry Tracing Specification](https://opentelemetry.io/docs/specs/otel/trace/api/)
- [Span Data Model](https://opentelemetry.io/docs/specs/otel/trace/api/#span)
- [OTLP Trace Protocol](https://opentelemetry.io/docs/specs/otlp/#traces)

### Go 实现

- [go.opentelemetry.io/otel/trace](https://pkg.go.dev/go.opentelemetry.io/otel/trace)
- [go.opentelemetry.io/otel/sdk/trace](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/trace)

### 相关文档

- [02_SpanContext.md](./02_SpanContext.md) - TraceID, SpanID, TraceFlags
- [03_SpanKind.md](./03_SpanKind.md) - Span 类型详解
- [04_Status.md](./04_Status.md) - Span 状态
- [05_Events.md](./05_Events.md) - Span Events
- [06_Links.md](./06_Links.md) - Span Links

---

**🎉 恭喜！你已经掌握了 Span 结构的完整知识！**

下一步：学习 [SpanContext](./02_SpanContext.md) 了解追踪上下文传播。

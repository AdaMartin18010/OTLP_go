# Span Events 完整指南

## 📋 目录

- [Span Events 完整指南](#span-events-完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [关键特性](#关键特性)
    - [Event vs Span vs Attribute](#event-vs-span-vs-attribute)
  - [Event 定义](#event-定义)
    - [数据结构](#数据结构)
    - [OTLP Protocol Buffers](#otlp-protocol-buffers)
    - [形式化定义](#形式化定义)
  - [事件类型](#事件类型)
    - [1. 异常事件 (Exception Events)](#1-异常事件-exception-events)
      - [定义](#定义)
      - [Semantic Conventions](#semantic-conventions)
      - [Go 实现](#go-实现)
      - [完整示例](#完整示例)
    - [2. 日志事件 (Log Events)](#2-日志事件-log-events)
      - [定义2](#定义2)
      - [标准属性](#标准属性)
      - [Go 实现2](#go-实现2)
    - [3. 自定义业务事件](#3-自定义业务事件)
      - [定义3](#定义3)
      - [示例场景](#示例场景)
      - [Go 实现3](#go-实现3)
    - [4. 性能标记事件](#4-性能标记事件)
      - [定义4](#定义4)
      - [Go 实现4](#go-实现4)
  - [时间戳管理](#时间戳管理)
    - [自动时间戳](#自动时间戳)
    - [自定义时间戳](#自定义时间戳)
    - [时间戳约束](#时间戳约束)
  - [Go 完整实现](#go-完整实现)
    - [完整的订单处理示例](#完整的订单处理示例)
    - [Event 工具函数](#event-工具函数)
  - [最佳实践](#最佳实践)
    - [1. 事件命名规范](#1-事件命名规范)
    - [2. 适度使用 Events](#2-适度使用-events)
    - [3. 事件属性应该有意义](#3-事件属性应该有意义)
    - [4. 错误使用 RecordError](#4-错误使用-recorderror)
    - [5. 重要事件添加上下文](#5-重要事件添加上下文)
  - [常见问题](#常见问题)
    - [Q1: Event 和 Span 如何选择？](#q1-event-和-span-如何选择)
    - [Q2: 一个 Span 应该有多少个 Events？](#q2-一个-span-应该有多少个-events)
    - [Q3: Event 的时间戳可以晚于 Span.End() 吗？](#q3-event-的时间戳可以晚于-spanend-吗)
    - [Q4: 如何批量添加事件？](#q4-如何批量添加事件)
    - [Q5: Event 属性有数量限制吗？](#q5-event-属性有数量限制吗)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Go 实现5](#go-实现5)
    - [相关文档](#相关文档)

---

## 概述

**Span Events** 是 Span 生命周期中特定时间点发生的有意义的事件。
与 Span 的开始和结束不同，Events 记录了操作过程中的关键点。

### 关键特性

- ✅ **时间标记**: 每个 Event 都有精确的时间戳
- ✅ **属性携带**: 可以附加任意键值对属性
- ✅ **轻量级**: 不像 Span 那样重量级
- ✅ **有序**: 按时间顺序排列

### Event vs Span vs Attribute

| 特性 | Span | Event | Attribute |
|------|------|-------|-----------|
| **用途** | 表示操作 | 标记时间点 | 描述元数据 |
| **时间戳** | 开始+结束 | 单个时间点 | 无 |
| **嵌套** | 支持父子关系 | 附属于 Span | 键值对 |
| **开销** | 较高 | 中等 | 最低 |
| **示例** | HTTP 请求 | 重试尝试 | HTTP 方法 |

---

## Event 定义

### 数据结构

```go
type Event struct {
    Name       string                 // 事件名称
    Timestamp  time.Time              // 事件时间戳
    Attributes []attribute.KeyValue   // 事件属性
}
```

### OTLP Protocol Buffers

```protobuf
message Event {
  fixed64 time_unix_nano = 1;       // 时间戳（纳秒）
  string name = 2;                   // 事件名称
  repeated KeyValue attributes = 3;  // 事件属性
  uint32 dropped_attributes_count = 4;  // 丢弃的属性数
}
```

### 形式化定义

```text
Event := {
    Name:       string (必须)
    Timestamp:  uint64 (Unix 纳秒，必须)
    Attributes: Map[string, Value] (可选)
}

// 约束
Timestamp ≥ Span.StartTime
Timestamp ≤ Span.EndTime
```

---

## 事件类型

### 1. 异常事件 (Exception Events)

#### 定义

记录 Span 执行期间发生的异常或错误。

#### Semantic Conventions

```go
const (
    ExceptionEventName = "exception"
    ExceptionTypeKey   = "exception.type"     // string
    ExceptionMessageKey = "exception.message" // string
    ExceptionStacktraceKey = "exception.stacktrace" // string
    ExceptionEscapedKey = "exception.escaped" // bool
)
```

#### Go 实现

```go
import (
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// 方法1：使用 RecordError (推荐)
func handleError(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()

    if err := doSomething(); err != nil {
        // RecordError 自动创建 exception event
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    return nil
}

// 方法2：手动添加 exception event
func handleErrorManual(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()

    if err := doSomething(); err != nil {
        // 手动添加异常事件
        span.AddEvent("exception",
            trace.WithAttributes(
                attribute.String("exception.type", "*errors.errorString"),
                attribute.String("exception.message", err.Error()),
                attribute.String("exception.stacktrace", getStackTrace()),
            ),
        )
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    return nil
}
```

#### 完整示例

```go
func processWithExceptionHandling(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "process_data")
    defer span.End()

    defer func() {
        if r := recover(); r != nil {
            // 捕获 panic
            err := fmt.Errorf("panic: %v", r)
            span.RecordError(err)
            span.AddEvent("panic_recovered",
                trace.WithAttributes(
                    attribute.String("panic.value", fmt.Sprint(r)),
                    attribute.String("panic.stack", getStackTrace()),
                ),
            )
            span.SetStatus(codes.Error, "panic occurred")
        }
    }()

    // 可能 panic 的操作
    riskyOperation()

    return nil
}

func getStackTrace() string {
    buf := make([]byte, 4096)
    n := runtime.Stack(buf, false)
    return string(buf[:n])
}
```

---

### 2. 日志事件 (Log Events)

#### 定义2

记录应用程序日志消息作为 Span 事件。

#### 标准属性

```go
const (
    LogEventName = "log"
    LogMessageKey = "log.message"   // string
    LogSeverityKey = "log.severity" // string
    LogLevelKey = "log.level"       // int
)
```

#### Go 实现2

```go
// 添加日志事件
func addLogEvent(span trace.Span, level, message string) {
    span.AddEvent("log",
        trace.WithAttributes(
            attribute.String("log.message", message),
            attribute.String("log.severity", level),
        ),
    )
}

// 使用示例
func operationWithLogs(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()

    addLogEvent(span, "INFO", "Starting operation")

    if err := step1(); err != nil {
        addLogEvent(span, "ERROR", "Step1 failed: "+err.Error())
        return err
    }

    addLogEvent(span, "INFO", "Step1 completed successfully")

    if err := step2(); err != nil {
        addLogEvent(span, "WARN", "Step2 failed, retrying...")
        if err := step2(); err != nil {
            addLogEvent(span, "ERROR", "Step2 retry failed")
            return err
        }
    }

    addLogEvent(span, "INFO", "Operation completed")
    return nil
}
```

---

### 3. 自定义业务事件

#### 定义3

记录特定于业务逻辑的关键事件。

#### 示例场景

- 订单状态变更
- 支付处理阶段
- 用户行为跟踪
- 工作流步骤

#### Go 实现3

```go
// 1. 订单处理事件
func processOrder(ctx context.Context, order *Order) error {
    ctx, span := tracer.Start(ctx, "process_order")
    defer span.End()

    // 订单验证
    span.AddEvent("order.validated",
        trace.WithAttributes(
            attribute.String("order.id", order.ID),
            attribute.Float64("order.total", order.Total),
        ),
    )

    // 库存检查
    if err := checkInventory(order); err != nil {
        span.AddEvent("inventory.insufficient",
            trace.WithAttributes(
                attribute.String("product.id", order.ProductID),
            ),
        )
        return err
    }
    span.AddEvent("inventory.reserved")

    // 支付处理
    span.AddEvent("payment.initiated")
    if err := processPayment(order); err != nil {
        span.AddEvent("payment.failed")
        return err
    }
    span.AddEvent("payment.completed")

    // 订单确认
    span.AddEvent("order.confirmed",
        trace.WithAttributes(
            attribute.String("confirmation.id", generateConfirmationID()),
        ),
    )

    return nil
}

// 2. 用户行为事件
func userSession(ctx context.Context, userID string) {
    ctx, span := tracer.Start(ctx, "user_session")
    defer span.End()

    span.AddEvent("user.login",
        trace.WithAttributes(
            attribute.String("user.id", userID),
            attribute.String("login.method", "password"),
        ),
    )

    // 用户浏览产品
    span.AddEvent("product.viewed",
        trace.WithAttributes(
            attribute.String("product.id", "prod-123"),
            attribute.String("category", "electronics"),
        ),
    )

    // 添加到购物车
    span.AddEvent("cart.item_added",
        trace.WithAttributes(
            attribute.String("product.id", "prod-123"),
            attribute.Int("quantity", 2),
        ),
    )

    // 开始结账
    span.AddEvent("checkout.initiated")

    span.AddEvent("user.logout")
}

// 3. 数据处理管道事件
func dataPipeline(ctx context.Context, data []byte) error {
    ctx, span := tracer.Start(ctx, "data_pipeline")
    defer span.End()

    span.AddEvent("data.received",
        trace.WithAttributes(
            attribute.Int("data.size", len(data)),
        ),
    )

    // 数据验证
    if err := validate(data); err != nil {
        span.AddEvent("data.validation_failed")
        return err
    }
    span.AddEvent("data.validated")

    // 数据转换
    span.AddEvent("data.transformation_started")
    transformed := transform(data)
    span.AddEvent("data.transformation_completed",
        trace.WithAttributes(
            attribute.Int("output.size", len(transformed)),
        ),
    )

    // 数据存储
    span.AddEvent("data.storage_started")
    if err := store(transformed); err != nil {
        span.AddEvent("data.storage_failed")
        return err
    }
    span.AddEvent("data.storage_completed")

    return nil
}
```

---

### 4. 性能标记事件

#### 定义4

记录性能相关的关键时间点。

#### Go 实现4

```go
// 性能关键点标记
func performanceTracking(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "complex_operation")
    defer span.End()

    // 标记开始
    span.AddEvent("operation.phase1.start")
    phase1Result := doPhase1()
    span.AddEvent("operation.phase1.end",
        trace.WithAttributes(
            attribute.Int("phase1.result_count", len(phase1Result)),
        ),
    )

    // 标记第二阶段
    span.AddEvent("operation.phase2.start")
    phase2Result := doPhase2(phase1Result)
    span.AddEvent("operation.phase2.end",
        trace.WithAttributes(
            attribute.Int("phase2.result_count", len(phase2Result)),
        ),
    )

    // 标记缓存操作
    span.AddEvent("cache.lookup")
    if cached := lookupCache(); cached != nil {
        span.AddEvent("cache.hit")
        return nil
    }
    span.AddEvent("cache.miss")

    // 标记数据库查询
    span.AddEvent("database.query.start")
    result, err := queryDB()
    if err != nil {
        span.AddEvent("database.query.failed")
        return err
    }
    span.AddEvent("database.query.end",
        trace.WithAttributes(
            attribute.Int("rows.returned", len(result)),
        ),
    )

    return nil
}
```

---

## 时间戳管理

### 自动时间戳

```go
// 默认：使用当前时间
span.AddEvent("event_name")
// 等价于
span.AddEvent("event_name", trace.WithTimestamp(time.Now()))
```

### 自定义时间戳

```go
// 场景1：记录历史事件
func recordHistoricalEvent(span trace.Span, eventTime time.Time) {
    span.AddEvent("historical_event",
        trace.WithTimestamp(eventTime),
        trace.WithAttributes(
            attribute.String("event.source", "external_system"),
        ),
    )
}

// 场景2：批量处理消息
func processMessage(ctx context.Context, msg *Message) {
    ctx, span := tracer.Start(ctx, "process_message")
    defer span.End()

    // 记录消息接收时间（不是处理时间）
    span.AddEvent("message.received",
        trace.WithTimestamp(msg.Timestamp),
        trace.WithAttributes(
            attribute.String("message.id", msg.ID),
        ),
    )

    // 处理消息
    process(msg)

    // 记录处理完成（使用当前时间）
    span.AddEvent("message.processed")
}
```

### 时间戳约束

```go
// ✅ 正确：Event 时间戳在 Span 时间范围内
span := tracer.Start(ctx, "operation")  // t0
span.AddEvent("event1")                 // t0 <= t1 <= t2
span.End()                              // t2

// ⚠️ 注意：时间戳可以早于 Span 开始时间（用于记录历史事件）
span := tracer.Start(ctx, "operation")
span.AddEvent("historical_event",
    trace.WithTimestamp(time.Now().Add(-1*time.Hour)),  // 允许
)
```

---

## Go 完整实现

### 完整的订单处理示例

```go
package main

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("order-service")

type Order struct {
    ID          string
    UserID      string
    ProductID   string
    Quantity    int
    TotalAmount float64
    Status      string
}

func ProcessOrder(ctx context.Context, order *Order) error {
    ctx, span := tracer.Start(ctx, "process_order",
        trace.WithAttributes(
            attribute.String("order.id", order.ID),
            attribute.String("user.id", order.UserID),
        ),
    )
    defer span.End()

    // 1. 订单验证
    span.AddEvent("order.validation.started")
    if err := validateOrder(ctx, order); err != nil {
        span.AddEvent("order.validation.failed",
            trace.WithAttributes(
                attribute.String("error", err.Error()),
            ),
        )
        span.RecordError(err)
        span.SetStatus(codes.Error, "validation failed")
        return err
    }
    span.AddEvent("order.validation.succeeded")

    // 2. 库存检查
    span.AddEvent("inventory.check.started")
    available, err := checkInventory(ctx, order.ProductID, order.Quantity)
    if err != nil {
        span.AddEvent("inventory.check.failed")
        span.RecordError(err)
        span.SetStatus(codes.Error, "inventory check failed")
        return err
    }
    if !available {
        span.AddEvent("inventory.insufficient",
            trace.WithAttributes(
                attribute.String("product.id", order.ProductID),
                attribute.Int("requested", order.Quantity),
            ),
        )
        return fmt.Errorf("insufficient inventory")
    }
    span.AddEvent("inventory.reserved",
        trace.WithAttributes(
            attribute.String("product.id", order.ProductID),
            attribute.Int("quantity", order.Quantity),
        ),
    )

    // 3. 支付处理（带重试）
    span.AddEvent("payment.initiated",
        trace.WithAttributes(
            attribute.Float64("amount", order.TotalAmount),
            attribute.String("currency", "USD"),
        ),
    )

    var paymentErr error
    for attempt := 1; attempt <= 3; attempt++ {
        span.AddEvent("payment.attempt",
            trace.WithAttributes(
                attribute.Int("attempt.number", attempt),
            ),
        )

        paymentErr = processPayment(ctx, order)
        if paymentErr == nil {
            span.AddEvent("payment.succeeded",
                trace.WithAttributes(
                    attribute.Int("attempts.total", attempt),
                ),
            )
            break
        }

        span.AddEvent("payment.attempt.failed",
            trace.WithAttributes(
                attribute.Int("attempt.number", attempt),
                attribute.String("error", paymentErr.Error()),
            ),
        )

        if attempt < 3 {
            span.AddEvent("payment.retry.scheduled",
                trace.WithAttributes(
                    attribute.Int("retry.after.seconds", attempt),
                ),
            )
            time.Sleep(time.Duration(attempt) * time.Second)
        }
    }

    if paymentErr != nil {
        span.AddEvent("payment.failed",
            trace.WithAttributes(
                attribute.Int("attempts.total", 3),
            ),
        )
        span.RecordError(paymentErr)
        span.SetStatus(codes.Error, "payment failed after retries")
        return paymentErr
    }

    // 4. 更新订单状态
    order.Status = "confirmed"
    span.AddEvent("order.status.updated",
        trace.WithAttributes(
            attribute.String("status", order.Status),
        ),
    )

    // 5. 发送确认
    span.AddEvent("notification.sending")
    if err := sendConfirmation(ctx, order); err != nil {
        // 通知失败不影响订单处理
        span.AddEvent("notification.failed",
            trace.WithAttributes(
                attribute.String("error", err.Error()),
            ),
        )
    } else {
        span.AddEvent("notification.sent")
    }

    // 6. 订单完成
    span.AddEvent("order.completed",
        trace.WithAttributes(
            attribute.String("order.id", order.ID),
            attribute.String("status", order.Status),
        ),
    )

    span.SetStatus(codes.Ok, "")
    return nil
}

func validateOrder(ctx context.Context, order *Order) error {
    _, span := tracer.Start(ctx, "validate_order")
    defer span.End()

    if order.Quantity <= 0 {
        return fmt.Errorf("invalid quantity: %d", order.Quantity)
    }

    if order.TotalAmount <= 0 {
        return fmt.Errorf("invalid amount: %.2f", order.TotalAmount)
    }

    span.AddEvent("validation.rules.passed")
    return nil
}

func checkInventory(ctx context.Context, productID string, quantity int) (bool, error) {
    _, span := tracer.Start(ctx, "check_inventory",
        trace.WithAttributes(
            attribute.String("product.id", productID),
            attribute.Int("quantity.requested", quantity),
        ),
    )
    defer span.End()

    // 模拟库存检查
    span.AddEvent("database.query")
    available := 100 // 模拟可用数量

    span.AddEvent("inventory.checked",
        trace.WithAttributes(
            attribute.Int("quantity.available", available),
        ),
    )

    return available >= quantity, nil
}

func processPayment(ctx context.Context, order *Order) error {
    _, span := tracer.Start(ctx, "process_payment")
    defer span.End()

    // 模拟支付处理
    span.AddEvent("payment_gateway.request")
    
    // 模拟随机失败
    if time.Now().Unix()%3 == 0 {
        span.AddEvent("payment_gateway.error")
        return fmt.Errorf("payment gateway error")
    }

    span.AddEvent("payment_gateway.response")
    return nil
}

func sendConfirmation(ctx context.Context, order *Order) error {
    _, span := tracer.Start(ctx, "send_confirmation")
    defer span.End()

    span.AddEvent("email.sending",
        trace.WithAttributes(
            attribute.String("recipient", order.UserID),
        ),
    )

    // 模拟发送邮件
    time.Sleep(100 * time.Millisecond)

    span.AddEvent("email.sent")
    return nil
}
```

### Event 工具函数

```go
// 1. Event 构建器
type EventBuilder struct {
    name       string
    timestamp  *time.Time
    attributes []attribute.KeyValue
}

func NewEvent(name string) *EventBuilder {
    return &EventBuilder{name: name}
}

func (b *EventBuilder) WithTimestamp(ts time.Time) *EventBuilder {
    b.timestamp = &ts
    return b
}

func (b *EventBuilder) WithAttribute(key string, value interface{}) *EventBuilder {
    var attr attribute.KeyValue
    switch v := value.(type) {
    case string:
        attr = attribute.String(key, v)
    case int:
        attr = attribute.Int(key, v)
    case float64:
        attr = attribute.Float64(key, v)
    case bool:
        attr = attribute.Bool(key, v)
    }
    b.attributes = append(b.attributes, attr)
    return b
}

func (b *EventBuilder) AddTo(span trace.Span) {
    opts := []trace.EventOption{
        trace.WithAttributes(b.attributes...),
    }
    if b.timestamp != nil {
        opts = append(opts, trace.WithTimestamp(*b.timestamp))
    }
    span.AddEvent(b.name, opts...)
}

// 使用示例
func useEventBuilder(span trace.Span) {
    NewEvent("order.processed").
        WithAttribute("order.id", "12345").
        WithAttribute("amount", 99.99).
        WithTimestamp(time.Now()).
        AddTo(span)
}

// 2. 常用事件辅助函数
func AddRetryEvent(span trace.Span, attempt int, reason string) {
    span.AddEvent("retry",
        trace.WithAttributes(
            attribute.Int("retry.attempt", attempt),
            attribute.String("retry.reason", reason),
        ),
    )
}

func AddCacheEvent(span trace.Span, hit bool, key string) {
    eventName := "cache.miss"
    if hit {
        eventName = "cache.hit"
    }
    span.AddEvent(eventName,
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
}

func AddDatabaseEvent(span trace.Span, operation, table string, rowsAffected int) {
    span.AddEvent("database."+operation,
        trace.WithAttributes(
            attribute.String("db.table", table),
            attribute.Int("db.rows_affected", rowsAffected),
        ),
    )
}
```

---

## 最佳实践

### 1. 事件命名规范

```go
// ✅ 推荐：使用分层命名
"order.validation.started"
"payment.retry.scheduled"
"cache.lookup.completed"

// ❌ 避免：模糊的名称
"event1"
"something_happened"
"done"
```

### 2. 适度使用 Events

```go
// ✅ 推荐：关键点添加事件
span.AddEvent("payment.initiated")
span.AddEvent("payment.completed")

// ❌ 避免：过度使用
span.AddEvent("function.entered")
span.AddEvent("variable.initialized")
span.AddEvent("loop.started")
span.AddEvent("loop.iteration.1")
// ... 太多事件
```

### 3. 事件属性应该有意义

```go
// ✅ 推荐
span.AddEvent("order.validated",
    trace.WithAttributes(
        attribute.String("order.id", orderID),
        attribute.Float64("order.total", total),
    ),
)

// ❌ 避免：无意义的属性
span.AddEvent("order.validated",
    trace.WithAttributes(
        attribute.String("data", "some data"),
    ),
)
```

### 4. 错误使用 RecordError

```go
// ✅ 推荐：使用 RecordError
if err != nil {
    span.RecordError(err)  // 自动添加 exception event
    span.SetStatus(codes.Error, err.Error())
}

// ❌ 避免：手动添加错误事件
if err != nil {
    span.AddEvent("error",
        trace.WithAttributes(
            attribute.String("error.message", err.Error()),
        ),
    )
}
```

### 5. 重要事件添加上下文

```go
// ✅ 推荐：丰富的上下文
span.AddEvent("retry.scheduled",
    trace.WithAttributes(
        attribute.Int("retry.attempt", attempt),
        attribute.Int("retry.max_attempts", maxAttempts),
        attribute.String("retry.reason", reason),
        attribute.Int("retry.backoff_ms", backoffMs),
    ),
)

// ⚠️ 可以改进：缺少上下文
span.AddEvent("retry")
```

---

## 常见问题

### Q1: Event 和 Span 如何选择？

**A**:

- **Span**: 表示有持续时间的操作
- **Event**: 表示瞬时发生的事件

```go
// ✅ Span：数据库查询（有持续时间）
ctx, span := tracer.Start(ctx, "db.query")
defer span.End()

// ✅ Event：查询开始时间点
span.AddEvent("query.submitted")
```

---

### Q2: 一个 Span 应该有多少个 Events？

**A**: 没有硬性限制，但建议 < 20 个。过多会影响性能和可读性。

```go
// ✅ 推荐：合理数量（5-10个）
span.AddEvent("validation.started")
span.AddEvent("validation.completed")
span.AddEvent("processing.started")
span.AddEvent("processing.completed")

// ❌ 避免：过多事件（100+）
for i := 0; i < 100; i++ {
    span.AddEvent(fmt.Sprintf("iteration.%d", i))  // 太多
}
```

---

### Q3: Event 的时间戳可以晚于 Span.End() 吗？

**A**: 技术上可以，但不推荐。应该在 Span 结束前添加所有 Events。

```go
// ✅ 推荐
span.AddEvent("event")
span.End()

// ❌ 避免
span.End()
span.AddEvent("late_event")  // 不推荐
```

---

### Q4: 如何批量添加事件？

**A**: 逐个添加，或使用辅助函数。

```go
// 方案1：循环添加
for _, step := range steps {
    span.AddEvent(step.Name,
        trace.WithAttributes(
            attribute.String("step.result", step.Result),
        ),
    )
}

// 方案2：辅助函数
func AddStepEvents(span trace.Span, steps []Step) {
    for _, step := range steps {
        span.AddEvent(step.Name,
            trace.WithAttributes(
                attribute.String("step.result", step.Result),
            ),
        )
    }
}
```

---

### Q5: Event 属性有数量限制吗？

**A**: 理论上没有，但建议 < 10 个属性，避免过大。

---

## 参考资源

### 官方文档

- [OpenTelemetry Events](https://opentelemetry.io/docs/specs/otel/trace/api/#add-events)
- [Exception Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/exceptions/exceptions-spans/)

### Go 实现5

- [go.opentelemetry.io/otel/trace](https://pkg.go.dev/go.opentelemetry.io/otel/trace)

### 相关文档

- [01_Span结构.md](./01_Span结构.md)
- [04_Status.md](./04_Status.md)
- [06_Links.md](./06_Links.md)

---

**🎉 恭喜！你已经掌握了 Span Events 的完整知识！**

下一步：学习 [Links](./06_Links.md) 了解 Span 之间的关联。

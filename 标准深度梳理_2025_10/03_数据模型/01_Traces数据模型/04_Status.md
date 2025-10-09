# Span Status 完整指南

## 📋 目录

- [Span Status 完整指南](#span-status-完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [关键特性](#关键特性)
  - [Status 定义](#status-定义)
    - [数据结构](#数据结构)
    - [OTLP Protocol Buffers](#otlp-protocol-buffers)
    - [形式化定义](#形式化定义)
  - [三种状态](#三种状态)
    - [1. Unset (未设置)](#1-unset-未设置)
      - [定义](#定义)
      - [语义](#语义)
      - [使用场景](#使用场景)
      - [何时保持 Unset](#何时保持-unset)
    - [2. Ok (成功)](#2-ok-成功)
      - [定义2](#定义2)
      - [语义2](#语义2)
      - [使用场景2](#使用场景2)
      - [何时使用 Ok](#何时使用-ok)
    - [3. Error (错误)](#3-error-错误)
      - [定义3](#定义3)
      - [语义3](#语义3)
      - [使用场景3](#使用场景3)
      - [错误分类](#错误分类)
  - [状态设置规则](#状态设置规则)
    - [基本规则](#基本规则)
    - [HTTP 状态码映射](#http-状态码映射)
    - [gRPC 状态码映射](#grpc-状态码映射)
  - [Go 完整实现](#go-完整实现)
    - [基础状态设置](#基础状态设置)
    - [高级状态模式](#高级状态模式)
  - [最佳实践](#最佳实践)
    - [1. 错误必须设置 Error 状态](#1-错误必须设置-error-状态)
    - [2. Ok 状态用于关键操作](#2-ok-状态用于关键操作)
    - [3. 避免状态回退](#3-避免状态回退)
    - [4. 状态描述应该有意义](#4-状态描述应该有意义)
    - [5. 部分失败的处理](#5-部分失败的处理)
  - [常见问题](#常见问题)
    - [Q1: Unset 和 Ok 有什么区别？](#q1-unset-和-ok-有什么区别)
    - [Q2: RecordError 和 SetStatus 必须一起使用吗？](#q2-recorderror-和-setstatus-必须一起使用吗)
    - [Q3: 可以多次设置 Status 吗？](#q3-可以多次设置-status-吗)
    - [Q4: 如何处理预期的错误（如404）？](#q4-如何处理预期的错误如404)
    - [Q5: 子 Span 的错误应该传播到父 Span 吗？](#q5-子-span-的错误应该传播到父-span-吗)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Go 实现](#go-实现)
    - [相关文档](#相关文档)

---

## 概述

**Span Status** 表示 Span 代表的操作的最终状态，用于指示操作是成功还是失败。Status 对于错误追踪和 SLO 监控至关重要。

### 关键特性

- ✅ **三种状态**: Unset, Ok, Error
- ✅ **可选描述**: Error 状态可以包含描述信息
- ✅ **不可变**: 一旦设置为终态（Ok/Error），不应再改变
- ✅ **独立于异常**: RecordError 和 SetStatus 是独立的操作

---

## Status 定义

### 数据结构

```go
type Status struct {
    Code        StatusCode  // 状态码
    Description string      // 描述信息（仅用于 Error）
}

type StatusCode int

const (
    Unset StatusCode = 0  // 未设置（默认）
    Error StatusCode = 1  // 错误
    Ok    StatusCode = 2  // 成功
)
```

### OTLP Protocol Buffers

```protobuf
message Status {
  string message = 2;          // 错误描述
  StatusCode code = 3;         // 状态码
}

enum StatusCode {
  STATUS_CODE_UNSET = 0;
  STATUS_CODE_OK = 1;
  STATUS_CODE_ERROR = 2;
}
```

### 形式化定义

```text
Status := {
    Code:        StatusCode ∈ {Unset, Ok, Error}
    Description: string (仅当 Code = Error 时有效)
}

// 状态转换规则
Unset -> Ok    (✅ 允许)
Unset -> Error (✅ 允许)
Ok -> Error    (⚠️ 不推荐，但允许)
Error -> Ok    (⚠️ 不推荐，但允许)
Ok -> Ok       (✅ 幂等)
Error -> Error (✅ 幂等)
```

---

## 三种状态

### 1. Unset (未设置)

#### 定义

默认状态，表示 Span 的状态未被显式设置。

#### 语义

- **对于 SERVER 和 CONSUMER Span**: 通常表示成功
- **对于 CLIENT 和 PRODUCER Span**: 由后端决定（通常基于 HTTP 状态码等）
- **对于 INTERNAL Span**: 通常表示成功

#### 使用场景

```go
// 默认情况：不需要显式设置
ctx, span := tracer.Start(ctx, "operation")
defer span.End()

// Span 结束时状态为 Unset
// 后端会根据其他信息（如 HTTP 状态码）判断成功或失败
```

#### 何时保持 Unset

```go
// ✅ 推荐：HTTP 2xx 响应
func handleRequest(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "handle_request",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.HTTPStatusCodeKey.Int(200),
    )
    // 不需要设置 Status，Unset + 200 = 成功
    
    w.WriteHeader(200)
    w.Write([]byte("OK"))
}

// ✅ 推荐：无错误的内部操作
func processData(ctx context.Context, data []byte) {
    ctx, span := tracer.Start(ctx, "process_data")
    defer span.End()
    
    // 处理数据
    // 无错误，保持 Unset
}
```

---

### 2. Ok (成功)

#### 定义2

明确表示操作成功完成。

#### 语义2

- **必须**: 用于明确标记成功的操作
- **可选描述**: Description 应为空或被忽略

#### 使用场景2

```go
import "go.opentelemetry.io/otel/codes"

// 显式标记成功
ctx, span := tracer.Start(ctx, "operation")
defer span.End()

// 执行操作
result, err := doOperation()
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    return err
}

// ✅ 显式标记成功
span.SetStatus(codes.Ok, "")
return nil
```

#### 何时使用 Ok

```go
// ✅ 推荐：关键操作成功后
func criticalOperation(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "critical_operation")
    defer span.End()

    if err := doSomething(); err != nil {
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    // 明确标记成功
    span.SetStatus(codes.Ok, "")
    return nil
}

// ✅ 推荐：需要区分成功和未完成的场景
func retryableOperation(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "retryable_operation")
    defer span.End()

    for i := 0; i < 3; i++ {
        if err := attempt(); err != nil {
            span.AddEvent("retry", trace.WithAttributes(
                attribute.Int("attempt", i+1),
            ))
            continue
        }
        
        // 成功
        span.SetStatus(codes.Ok, "")
        return nil
    }

    // 所有重试失败
    span.SetStatus(codes.Error, "all retries failed")
    return errors.New("operation failed")
}
```

---

### 3. Error (错误)

#### 定义3

明确表示操作失败。

#### 语义3

- **必须**: 用于标记失败的操作
- **可选描述**: 应该包含错误原因

#### 使用场景3

```go
// 标记错误
ctx, span := tracer.Start(ctx, "operation")
defer span.End()

result, err := doOperation()
if err != nil {
    // 记录异常
    span.RecordError(err)
    
    // ✅ 设置 Error 状态
    span.SetStatus(codes.Error, err.Error())
    return err
}
```

#### 错误分类

```go
// 1. 客户端错误 (4xx)
func handleBadRequest(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "validate_input")
    defer span.End()

    if !isValid(input) {
        err := errors.New("invalid input")
        span.RecordError(err)
        span.SetStatus(codes.Error, "validation failed")
        span.SetAttributes(
            attribute.String("error.type", "validation_error"),
        )
        return err
    }
    return nil
}

// 2. 服务器错误 (5xx)
func handleServerError(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "database_query")
    defer span.End()

    if err := db.Query(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "database error")
        span.SetAttributes(
            attribute.String("error.type", "database_error"),
            attribute.Bool("error.temporary", true),
        )
        return err
    }
    return nil
}

// 3. 超时错误
func handleTimeout(ctx context.Context) error {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()

    ctx, span := tracer.Start(ctx, "external_api_call")
    defer span.End()

    resultCh := make(chan result, 1)
    go func() {
        resultCh <- callAPI()
    }()

    select {
    case res := <-resultCh:
        span.SetStatus(codes.Ok, "")
        return nil
    case <-ctx.Done():
        err := ctx.Err()
        span.RecordError(err)
        span.SetStatus(codes.Error, "request timeout")
        span.SetAttributes(
            attribute.String("error.type", "timeout"),
        )
        return err
    }
}
```

---

## 状态设置规则

### 基本规则

```go
// ✅ 规则1: Error 状态应该伴随 RecordError
if err != nil {
    span.RecordError(err)              // 记录异常
    span.SetStatus(codes.Error, err.Error())  // 设置状态
}

// ✅ 规则2: Ok 状态不需要描述
span.SetStatus(codes.Ok, "")  // 描述应为空

// ✅ 规则3: Unset 是默认值，通常不需要显式设置
// 不需要: span.SetStatus(codes.Unset, "")

// ⚠️ 规则4: 避免状态回退
span.SetStatus(codes.Error, "failed")
// 不推荐: span.SetStatus(codes.Ok, "")  // Error -> Ok
```

### HTTP 状态码映射

```go
func setHTTPStatus(span trace.Span, statusCode int) {
    span.SetAttributes(
        semconv.HTTPStatusCodeKey.Int(statusCode),
    )

    // HTTP 状态码到 Span Status 的映射
    switch {
    case statusCode >= 200 && statusCode < 400:
        // 2xx, 3xx: 成功，保持 Unset 或设置 Ok
        // 通常保持 Unset
        
    case statusCode >= 400 && statusCode < 500:
        // 4xx: 客户端错误
        span.SetStatus(codes.Error, fmt.Sprintf("client error: %d", statusCode))
        
    case statusCode >= 500:
        // 5xx: 服务器错误
        span.SetStatus(codes.Error, fmt.Sprintf("server error: %d", statusCode))
    }
}

// 使用示例
func httpHandler(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), r.URL.Path,
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    statusCode := processRequest(r)
    setHTTPStatus(span, statusCode)
    
    w.WriteHeader(statusCode)
}
```

### gRPC 状态码映射

```go
import "google.golang.org/grpc/codes"
import "google.golang.org/grpc/status"

func setGRPCStatus(span trace.Span, err error) {
    if err == nil {
        span.SetStatus(otlcodes.Ok, "")
        return
    }

    st, ok := status.FromError(err)
    if !ok {
        span.SetStatus(otlcodes.Error, err.Error())
        return
    }

    // gRPC 状态码到 Span Status 的映射
    switch st.Code() {
    case codes.OK:
        span.SetStatus(otlcodes.Ok, "")
        
    case codes.Canceled, codes.DeadlineExceeded, codes.Aborted:
        // 客户端取消或超时
        span.SetStatus(otlcodes.Error, st.Message())
        
    case codes.InvalidArgument, codes.NotFound, codes.AlreadyExists,
         codes.PermissionDenied, codes.Unauthenticated:
        // 客户端错误
        span.SetStatus(otlcodes.Error, st.Message())
        
    case codes.ResourceExhausted, codes.FailedPrecondition,
         codes.OutOfRange, codes.Unimplemented, codes.Internal,
         codes.Unavailable, codes.DataLoss:
        // 服务器错误
        span.SetStatus(otlcodes.Error, st.Message())
        
    default:
        span.SetStatus(otlcodes.Error, st.Message())
    }
    
    span.SetAttributes(
        semconv.RPCGRPCStatusCodeKey.Int(int(st.Code())),
    )
}
```

---

## Go 完整实现

### 基础状态设置

```go
package main

import (
    "context"
    "errors"
    "fmt"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("status-demo")

// 1. 基础错误处理
func basicErrorHandling(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "basic_operation")
    defer span.End()

    result, err := riskyOperation()
    if err != nil {
        // 记录错误和设置状态
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    // 成功
    span.SetAttributes(
        attribute.String("result", result),
    )
    span.SetStatus(codes.Ok, "")
    return nil
}

// 2. HTTP 请求状态
func httpClientStatus(ctx context.Context, url string) error {
    ctx, span := tracer.Start(ctx, "http_get",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    span.SetAttributes(
        semconv.HTTPMethodKey.String("GET"),
        semconv.HTTPURLKey.String(url),
    )

    resp, err := http.Get(url)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "HTTP request failed")
        return err
    }
    defer resp.Body.Close()

    span.SetAttributes(
        semconv.HTTPStatusCodeKey.Int(resp.StatusCode),
    )

    // 根据状态码设置 Status
    if resp.StatusCode >= 400 {
        span.SetStatus(codes.Error, 
            fmt.Sprintf("HTTP %d", resp.StatusCode))
        return fmt.Errorf("HTTP %d", resp.StatusCode)
    }

    // 2xx/3xx: 成功，可以保持 Unset 或设置 Ok
    span.SetStatus(codes.Ok, "")
    return nil
}

// 3. 重试逻辑状态
func retryWithStatus(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "retry_operation")
    defer span.End()

    var lastErr error
    for i := 0; i < 3; i++ {
        span.AddEvent("attempt", trace.WithAttributes(
            attribute.Int("attempt_number", i+1),
        ))

        if err := attemptOperation(); err != nil {
            lastErr = err
            span.AddEvent("attempt_failed", trace.WithAttributes(
                attribute.String("error", err.Error()),
            ))
            time.Sleep(time.Duration(i+1) * time.Second)
            continue
        }

        // 成功
        span.SetStatus(codes.Ok, "")
        span.SetAttributes(
            attribute.Int("successful_attempt", i+1),
        )
        return nil
    }

    // 所有重试失败
    span.RecordError(lastErr)
    span.SetStatus(codes.Error, "all retries exhausted")
    return lastErr
}

// 4. 部分失败状态
func batchProcessWithStatus(ctx context.Context, items []string) error {
    ctx, span := tracer.Start(ctx, "batch_process")
    defer span.End()

    var failed int
    for _, item := range items {
        if err := processItem(ctx, item); err != nil {
            failed++
            span.AddEvent("item_failed", trace.WithAttributes(
                attribute.String("item", item),
                attribute.String("error", err.Error()),
            ))
        }
    }

    span.SetAttributes(
        attribute.Int("total", len(items)),
        attribute.Int("failed", failed),
        attribute.Int("succeeded", len(items)-failed),
    )

    // 根据失败率设置状态
    failureRate := float64(failed) / float64(len(items))
    if failureRate > 0.5 {
        // 超过50%失败：Error
        span.SetStatus(codes.Error, 
            fmt.Sprintf("high failure rate: %.2f%%", failureRate*100))
        return fmt.Errorf("batch processing failed")
    } else if failed > 0 {
        // 部分失败：Ok，但记录警告
        span.SetStatus(codes.Ok, "")
        span.AddEvent("partial_failure", trace.WithAttributes(
            attribute.Int("failed_count", failed),
        ))
    } else {
        // 全部成功：Ok
        span.SetStatus(codes.Ok, "")
    }

    return nil
}

// 5. 超时处理状态
func timeoutWithStatus(ctx context.Context) error {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()

    ctx, span := tracer.Start(ctx, "timeout_operation")
    defer span.End()

    done := make(chan error, 1)
    go func() {
        done <- longRunningOperation()
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
        span.SetStatus(codes.Error, "operation timeout")
        span.SetAttributes(
            attribute.String("timeout.reason", err.Error()),
        )
        return err
    }
}

// 辅助函数
func riskyOperation() (string, error) {
    // 模拟操作
    return "success", nil
}

func attemptOperation() error {
    // 模拟可能失败的操作
    return nil
}

func processItem(ctx context.Context, item string) error {
    // 模拟处理单个项目
    return nil
}

func longRunningOperation() error {
    // 模拟长时间运行的操作
    time.Sleep(3 * time.Second)
    return nil
}
```

### 高级状态模式

```go
// 1. 自定义错误分类
type ErrorCategory string

const (
    ValidationError ErrorCategory = "validation"
    DatabaseError   ErrorCategory = "database"
    NetworkError    ErrorCategory = "network"
    TimeoutError    ErrorCategory = "timeout"
)

func setErrorStatus(span trace.Span, err error, category ErrorCategory, temporary bool) {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    span.SetAttributes(
        attribute.String("error.category", string(category)),
        attribute.Bool("error.temporary", temporary),
    )
}

// 使用
func operationWithErrorCategory(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()

    if err := validateInput(); err != nil {
        setErrorStatus(span, err, ValidationError, false)
        return err
    }

    if err := queryDatabase(); err != nil {
        setErrorStatus(span, err, DatabaseError, true)
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// 2. 条件状态设置
func conditionalStatus(ctx context.Context, threshold float64) error {
    ctx, span := tracer.Start(ctx, "conditional_operation")
    defer span.End()

    result := performCalculation()
    
    span.SetAttributes(
        attribute.Float64("result.value", result),
        attribute.Float64("threshold", threshold),
    )

    if result < threshold {
        span.SetStatus(codes.Error, "result below threshold")
        return fmt.Errorf("insufficient result: %.2f < %.2f", result, threshold)
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// 3. 链式操作状态
func chainedOperations(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "chained_operations")
    defer span.End()

    // 操作1
    if err := operation1(ctx); err != nil {
        span.SetStatus(codes.Error, "operation1 failed")
        return err
    }

    // 操作2
    if err := operation2(ctx); err != nil {
        span.SetStatus(codes.Error, "operation2 failed")
        return err
    }

    // 操作3
    if err := operation3(ctx); err != nil {
        span.SetStatus(codes.Error, "operation3 failed")
        return err
    }

    // 全部成功
    span.SetStatus(codes.Ok, "")
    return nil
}

func operation1(ctx context.Context) error {
    _, span := tracer.Start(ctx, "operation1")
    defer span.End()
    // ...
    span.SetStatus(codes.Ok, "")
    return nil
}

func operation2(ctx context.Context) error {
    _, span := tracer.Start(ctx, "operation2")
    defer span.End()
    // ...
    span.SetStatus(codes.Ok, "")
    return nil
}

func operation3(ctx context.Context) error {
    _, span := tracer.Start(ctx, "operation3")
    defer span.End()
    // ...
    span.SetStatus(codes.Ok, "")
    return nil
}

func performCalculation() float64 {
    return 42.0
}

func validateInput() error {
    return nil
}

func queryDatabase() error {
    return nil
}
```

---

## 最佳实践

### 1. 错误必须设置 Error 状态

```go
// ✅ 推荐
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    return err
}

// ❌ 避免：只记录错误，不设置状态
if err != nil {
    span.RecordError(err)  // 缺少 SetStatus
    return err
}
```

### 2. Ok 状态用于关键操作

```go
// ✅ 推荐：关键操作明确标记成功
func criticalPayment(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "process_payment")
    defer span.End()

    if err := chargeCard(); err != nil {
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")  // 明确标记成功
    return nil
}

// ⚠️ 可选：常规操作可以保持 Unset
func regularOperation(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "regular_op")
    defer span.End()

    // 操作成功，保持 Unset
    return nil
}
```

### 3. 避免状态回退

```go
// ❌ 避免：状态回退
span.SetStatus(codes.Error, "failed")
// ... 一些逻辑
span.SetStatus(codes.Ok, "")  // Error -> Ok 不推荐

// ✅ 推荐：使用正确的控制流
if err != nil {
    span.SetStatus(codes.Error, err.Error())
    return err
}
span.SetStatus(codes.Ok, "")
```

### 4. 状态描述应该有意义

```go
// ✅ 推荐：有意义的描述
span.SetStatus(codes.Error, "database connection timeout after 30s")
span.SetStatus(codes.Error, "invalid user input: email format incorrect")

// ❌ 避免：无意义的描述
span.SetStatus(codes.Error, "error")
span.SetStatus(codes.Error, "failed")
```

### 5. 部分失败的处理

```go
// ✅ 推荐：根据失败率决定
func batchProcess(ctx context.Context, items []Item) error {
    ctx, span := tracer.Start(ctx, "batch_process")
    defer span.End()

    failed := 0
    for _, item := range items {
        if err := process(item); err != nil {
            failed++
        }
    }

    if failed > len(items)/2 {
        // 超过一半失败：Error
        span.SetStatus(codes.Error, "majority failed")
        return errors.New("batch failed")
    }

    // 全部成功或少量失败：Ok
    span.SetStatus(codes.Ok, "")
    return nil
}
```

---

## 常见问题

### Q1: Unset 和 Ok 有什么区别？

**A**:

- **Unset**: 默认状态，让后端根据其他信息判断
- **Ok**: 明确标记成功，用于关键操作

```go
// HTTP 200: 通常保持 Unset（后端会认为成功）
span.SetAttributes(semconv.HTTPStatusCodeKey.Int(200))
// 不需要: span.SetStatus(codes.Ok, "")

// 关键支付操作: 明确标记 Ok
if err := processPayment(); err != nil {
    span.SetStatus(codes.Error, err.Error())
} else {
    span.SetStatus(codes.Ok, "")  // 明确标记
}
```

---

### Q2: RecordError 和 SetStatus 必须一起使用吗？

**A**: 不是必须，但强烈推荐。

```go
// ✅ 推荐：一起使用
span.RecordError(err)
span.SetStatus(codes.Error, err.Error())

// ⚠️ 可以：只用 RecordError（用于记录但不视为失败的错误）
span.RecordError(err)
span.AddEvent("recovered_from_error")
span.SetStatus(codes.Ok, "")  // 已恢复

// ❌ 避免：只用 SetStatus（丢失堆栈信息）
span.SetStatus(codes.Error, err.Error())  // 缺少 RecordError
```

---

### Q3: 可以多次设置 Status 吗？

**A**: 技术上可以，但不推荐。应该在 Span 结束前设置一次。

```go
// ❌ 避免：多次设置
span.SetStatus(codes.Error, "temp error")
// ... 一些逻辑
span.SetStatus(codes.Ok, "recovered")

// ✅ 推荐：一次设置
if err := operation(); err != nil {
    span.SetStatus(codes.Error, err.Error())
} else {
    span.SetStatus(codes.Ok, "")
}
```

---

### Q4: 如何处理预期的错误（如404）？

**A**: 取决于业务语义。

```go
// 方案1：视为成功（404是预期的）
user, err := getUserByID(id)
if err == ErrNotFound {
    span.SetAttributes(attribute.Bool("user.found", false))
    span.SetStatus(codes.Ok, "")  // 预期的结果
    return nil
}

// 方案2：视为错误（404是异常的）
user, err := getUserByID(id)
if err == ErrNotFound {
    span.RecordError(err)
    span.SetStatus(codes.Error, "user not found")
    return err
}
```

---

### Q5: 子 Span 的错误应该传播到父 Span 吗？

**A**: 不会自动传播，需要手动处理。

```go
func parentOperation(ctx context.Context) error {
    ctx, parentSpan := tracer.Start(ctx, "parent")
    defer parentSpan.End()

    // 子操作失败
    if err := childOperation(ctx); err != nil {
        // 父 Span 也应该标记为失败
        parentSpan.RecordError(err)
        parentSpan.SetStatus(codes.Error, "child operation failed")
        return err
    }

    parentSpan.SetStatus(codes.Ok, "")
    return nil
}

func childOperation(ctx context.Context) error {
    _, childSpan := tracer.Start(ctx, "child")
    defer childSpan.End()

    err := doSomething()
    if err != nil {
        childSpan.RecordError(err)
        childSpan.SetStatus(codes.Error, err.Error())
        return err  // 错误返回给父操作
    }

    childSpan.SetStatus(codes.Ok, "")
    return nil
}
```

---

## 参考资源

### 官方文档

- [OpenTelemetry Span Status](https://opentelemetry.io/docs/specs/otel/trace/api/#set-status)
- [Status Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/general/trace/)

### Go 实现

- [go.opentelemetry.io/otel/codes](https://pkg.go.dev/go.opentelemetry.io/otel/codes)

### 相关文档

- [01_Span结构.md](./01_Span结构.md)
- [03_SpanKind.md](./03_SpanKind.md)
- [05_Events.md](./05_Events.md)

---

**🎉 恭喜！你已经掌握了 Span Status 的完整知识！**

下一步：学习 [Events](./05_Events.md) 了解 Span 事件。

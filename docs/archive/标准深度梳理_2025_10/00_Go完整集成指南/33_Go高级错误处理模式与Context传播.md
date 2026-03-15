# Go 高级错误处理模式与 Context 传播

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [Go 高级错误处理模式与 Context 传播](#go-高级错误处理模式与-context-传播)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [错误类型设计](#错误类型设计)
    - [1. 自定义错误类型](#1-自定义错误类型)
    - [2. 领域特定错误](#2-领域特定错误)
  - [错误包装与追踪](#错误包装与追踪)
    - [完整的错误包装实现](#完整的错误包装实现)
  - [多错误聚合](#多错误聚合)
    - [Go 1.20+ errors.Join 集成](#go-120-errorsjoin-集成)
  - [Context 取消传播](#context-取消传播)
    - [完整的 Context 取消管理](#完整的-context-取消管理)
  - [超时与截止时间](#超时与截止时间)
    - [完整的超时管理](#完整的超时管理)
  - [错误恢复策略](#错误恢复策略)
  - [最佳实践](#最佳实践)
    - [1. 错误检查](#1-错误检查)
    - [2. Context 传播](#2-context-传播)
    - [3. 错误记录](#3-错误记录)
  - [总结](#总结)

---

## 概述

Go 1.25.1 提供了强大的错误处理机制，本文档展示如何结合 Context 和 OpenTelemetry 实现完整的错误处理和传播。

**核心特性**:

```text
✅ errors.Is/As - 错误检查
✅ errors.Join - 多错误合并 (Go 1.20+)
✅ fmt.Errorf %w - 错误包装
✅ context.WithCause - 带原因的取消 (Go 1.20+)
✅ context.Cause - 获取取消原因 (Go 1.20+)
✅ context.WithoutCancel - 分离 Context (Go 1.21+)
✅ context.AfterFunc - 清理回调 (Go 1.21+)
```

---

## 错误类型设计

### 1. 自定义错误类型

```go
package errors

import (
    "fmt"
    "time"

    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ErrorCategory 错误分类
type ErrorCategory string

const (
    CategoryValidation   ErrorCategory = "validation"
    CategoryDatabase     ErrorCategory = "database"
    CategoryNetwork      ErrorCategory = "network"
    CategoryAuthorization ErrorCategory = "authorization"
    CategoryInternal     ErrorCategory = "internal"
    CategoryTimeout      ErrorCategory = "timeout"
)

// TracedError 带追踪信息的错误
type TracedError struct {
    Category    ErrorCategory
    Operation   string
    Message     string
    Cause       error
    TraceID     string
    SpanID      string
    Timestamp   time.Time
    Attributes  map[string]interface{}
    Retryable   bool
}

// Error 实现 error 接口
func (e *TracedError) Error() string {
    if e.Cause != nil {
        return fmt.Sprintf("[%s] %s: %s: %v", 
            e.Category, e.Operation, e.Message, e.Cause)
    }
    return fmt.Sprintf("[%s] %s: %s", 
        e.Category, e.Operation, e.Message)
}

// Unwrap 实现 errors.Unwrap 接口
func (e *TracedError) Unwrap() error {
    return e.Cause
}

// Is 实现 errors.Is 接口
func (e *TracedError) Is(target error) bool {
    t, ok := target.(*TracedError)
    if !ok {
        return false
    }
    return e.Category == t.Category
}

// ToSpanAttributes 转换为 Span 属性
func (e *TracedError) ToSpanAttributes() []attribute.KeyValue {
    attrs := []attribute.KeyValue{
        attribute.String("error.category", string(e.Category)),
        attribute.String("error.operation", e.Operation),
        attribute.String("error.message", e.Message),
        attribute.Bool("error.retryable", e.Retryable),
    }
    
    if e.TraceID != "" {
        attrs = append(attrs, attribute.String("error.trace_id", e.TraceID))
    }
    
    if e.SpanID != "" {
        attrs = append(attrs, attribute.String("error.span_id", e.SpanID))
    }
    
    for k, v := range e.Attributes {
        attrs = append(attrs, attribute.String("error."+k, fmt.Sprintf("%v", v)))
    }
    
    return attrs
}

// NewTracedError 创建带追踪的错误
func NewTracedError(
    category ErrorCategory,
    operation string,
    message string,
    cause error,
    span trace.Span,
) *TracedError {
    spanContext := span.SpanContext()
    
    return &TracedError{
        Category:   category,
        Operation:  operation,
        Message:    message,
        Cause:      cause,
        TraceID:    spanContext.TraceID().String(),
        SpanID:     spanContext.SpanID().String(),
        Timestamp:  time.Now(),
        Attributes: make(map[string]interface{}),
        Retryable:  IsRetryableCategory(category),
    }
}

// IsRetryableCategory 判断错误类别是否可重试
func IsRetryableCategory(category ErrorCategory) bool {
    switch category {
    case CategoryNetwork, CategoryTimeout:
        return true
    default:
        return false
    }
}
```

### 2. 领域特定错误

```go
package errors

import (
    "fmt"
)

// ValidationError 验证错误
type ValidationError struct {
    Field   string
    Message string
    Value   interface{}
}

func (e *ValidationError) Error() string {
    return fmt.Sprintf("validation failed for field '%s': %s (value: %v)", 
        e.Field, e.Message, e.Value)
}

// DatabaseError 数据库错误
type DatabaseError struct {
    Operation string
    Table     string
    Query     string
    Cause     error
}

func (e *DatabaseError) Error() string {
    return fmt.Sprintf("database %s failed on table %s: %v", 
        e.Operation, e.Table, e.Cause)
}

func (e *DatabaseError) Unwrap() error {
    return e.Cause
}

// NetworkError 网络错误
type NetworkError struct {
    URL        string
    Method     string
    StatusCode int
    Cause      error
}

func (e *NetworkError) Error() string {
    return fmt.Sprintf("network request %s %s failed with status %d: %v", 
        e.Method, e.URL, e.StatusCode, e.Cause)
}

func (e *NetworkError) Unwrap() error {
    return e.Cause
}

// TimeoutError 超时错误
type TimeoutError struct {
    Operation string
    Timeout   time.Duration
    Elapsed   time.Duration
}

func (e *TimeoutError) Error() string {
    return fmt.Sprintf("operation '%s' timed out after %v (expected: %v)", 
        e.Operation, e.Elapsed, e.Timeout)
}

func (e *TimeoutError) Timeout() bool {
    return true
}

func (e *TimeoutError) Temporary() bool {
    return true
}
```

---

## 错误包装与追踪

### 完整的错误包装实现

```go
package errors

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// WrapError 包装错误并记录到 Span
func WrapError(
    ctx context.Context,
    err error,
    category ErrorCategory,
    operation string,
    message string,
) error {
    if err == nil {
        return nil
    }
    
    span := trace.SpanFromContext(ctx)
    
    // 创建追踪错误
    tracedErr := NewTracedError(category, operation, message, err, span)
    
    // 记录到 Span
    span.RecordError(tracedErr)
    span.SetStatus(codes.Error, tracedErr.Error())
    span.SetAttributes(tracedErr.ToSpanAttributes()...)
    
    return tracedErr
}

// WrapWithSpan 创建新 Span 并包装错误
func WrapWithSpan(
    ctx context.Context,
    operationName string,
    category ErrorCategory,
    fn func(context.Context) error,
) error {
    tracer := otel.Tracer("error-wrapper")
    
    ctx, span := tracer.Start(ctx, operationName)
    defer span.End()
    
    err := fn(ctx)
    if err != nil {
        return WrapError(ctx, err, category, operationName, "operation failed")
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// RecordError 记录错误但不返回
func RecordError(ctx context.Context, err error) {
    if err == nil {
        return
    }
    
    span := trace.SpanFromContext(ctx)
    span.RecordError(err)
    
    if tracedErr, ok := err.(*TracedError); ok {
        span.SetAttributes(tracedErr.ToSpanAttributes()...)
    }
}

// ErrorChain 错误链追踪
type ErrorChain struct {
    errors []error
    tracer trace.Tracer
}

// NewErrorChain 创建错误链
func NewErrorChain() *ErrorChain {
    return &ErrorChain{
        errors: make([]error, 0),
        tracer: otel.Tracer("error-chain"),
    }
}

// Add 添加错误到链
func (ec *ErrorChain) Add(ctx context.Context, err error) {
    if err == nil {
        return
    }
    
    ec.errors = append(ec.errors, err)
    
    span := trace.SpanFromContext(ctx)
    span.RecordError(err)
    span.AddEvent("error added to chain", trace.WithAttributes(
        attribute.Int("chain.length", len(ec.errors)),
    ))
}

// HasErrors 检查是否有错误
func (ec *ErrorChain) HasErrors() bool {
    return len(ec.errors) > 0
}

// Errors 返回所有错误
func (ec *ErrorChain) Errors() []error {
    return ec.errors
}

// Join 合并所有错误
func (ec *ErrorChain) Join() error {
    if len(ec.errors) == 0 {
        return nil
    }
    
    if len(ec.errors) == 1 {
        return ec.errors[0]
    }
    
    // 使用 errors.Join (Go 1.20+)
    return errors.Join(ec.errors...)
}
```

---

## 多错误聚合

### Go 1.20+ errors.Join 集成

```go
package errors

import (
    "context"
    "errors"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// MultiError 多错误聚合器
type MultiError struct {
    Operation string
    Errors    []error
    tracer    trace.Tracer
}

// NewMultiError 创建多错误聚合器
func NewMultiError(operation string) *MultiError {
    return &MultiError{
        Operation: operation,
        Errors:    make([]error, 0),
        tracer:    otel.Tracer("multi-error"),
    }
}

// Add 添加错误
func (me *MultiError) Add(ctx context.Context, err error) {
    if err == nil {
        return
    }
    
    me.Errors = append(me.Errors, err)
    
    span := trace.SpanFromContext(ctx)
    span.RecordError(err)
}

// Join 合并所有错误
func (me *MultiError) Join(ctx context.Context) error {
    if len(me.Errors) == 0 {
        return nil
    }
    
    span := trace.SpanFromContext(ctx)
    span.SetAttributes(
        attribute.Int("errors.count", len(me.Errors)),
        attribute.String("errors.operation", me.Operation),
    )
    
    // 使用 errors.Join
    joined := errors.Join(me.Errors...)
    
    span.RecordError(joined)
    
    return joined
}

// HasErrors 检查是否有错误
func (me *MultiError) HasErrors() bool {
    return len(me.Errors) > 0
}

// Count 返回错误数量
func (me *MultiError) Count() int {
    return len(me.Errors)
}

// ParallelExecute 并行执行多个操作并聚合错误
func ParallelExecute(
    ctx context.Context,
    operation string,
    tasks []func(context.Context) error,
) error {
    tracer := otel.Tracer("parallel-execute")
    
    ctx, span := tracer.Start(ctx, operation,
        trace.WithAttributes(
            attribute.Int("tasks.count", len(tasks)),
        ),
    )
    defer span.End()
    
    me := NewMultiError(operation)
    errorsCh := make(chan error, len(tasks))
    
    // 并行执行所有任务
    for i, task := range tasks {
        go func(index int, fn func(context.Context) error) {
            err := fn(ctx)
            if err != nil {
                errorsCh <- fmt.Errorf("task %d: %w", index, err)
            } else {
                errorsCh <- nil
            }
        }(i, task)
    }
    
    // 收集错误
    for range tasks {
        if err := <-errorsCh; err != nil {
            me.Add(ctx, err)
        }
    }
    
    return me.Join(ctx)
}
```

---

## Context 取消传播

### 完整的 Context 取消管理

```go
package context

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// CancellationManager Context 取消管理器
type CancellationManager struct {
    tracer trace.Tracer
}

// NewCancellationManager 创建取消管理器
func NewCancellationManager() *CancellationManager {
    return &CancellationManager{
        tracer: otel.Tracer("cancellation-manager"),
    }
}

// WithCancellationReason 创建带取消原因的 Context
func (cm *CancellationManager) WithCancellationReason(
    parent context.Context,
    reason string,
) (context.Context, context.CancelFunc) {
    ctx, span := cm.tracer.Start(parent, "context.with_cancellation",
        trace.WithAttributes(
            attribute.String("cancellation.reason", reason),
        ),
    )
    
    // 创建可取消的 context
    ctx, cancel := context.WithCancel(ctx)
    
    // 包装 cancel 函数以记录取消
    wrappedCancel := func() {
        span.AddEvent("context cancelled", trace.WithAttributes(
            attribute.String("reason", reason),
        ))
        span.End()
        cancel()
    }
    
    return ctx, wrappedCancel
}

// WithDeadlineAndCause 创建带截止时间和原因的 Context (Go 1.21+)
func (cm *CancellationManager) WithDeadlineAndCause(
    parent context.Context,
    deadline time.Time,
    cause error,
) (context.Context, context.CancelFunc) {
    ctx, span := cm.tracer.Start(parent, "context.with_deadline_cause",
        trace.WithAttributes(
            attribute.String("deadline", deadline.Format(time.RFC3339)),
            attribute.String("cause", cause.Error()),
        ),
    )
    
    // Go 1.21+ WithDeadlineCause
    ctx, cancel := context.WithDeadlineCause(ctx, deadline, cause)
    
    // 监听取消
    go func() {
        <-ctx.Done()
        
        if cause := context.Cause(ctx); cause != nil {
            span.RecordError(cause)
            span.SetAttributes(
                attribute.String("cancellation.cause", cause.Error()),
            )
        }
        
        span.End()
    }()
    
    return ctx, cancel
}

// WithTimeoutAndCause 创建带超时和原因的 Context
func (cm *CancellationManager) WithTimeoutAndCause(
    parent context.Context,
    timeout time.Duration,
    cause error,
) (context.Context, context.CancelFunc) {
    deadline := time.Now().Add(timeout)
    return cm.WithDeadlineAndCause(parent, deadline, cause)
}

// WithoutCancellation 创建不可取消的 Context (Go 1.21+)
func (cm *CancellationManager) WithoutCancellation(
    parent context.Context,
    reason string,
) context.Context {
    ctx, span := cm.tracer.Start(parent, "context.without_cancel",
        trace.WithAttributes(
            attribute.String("reason", reason),
        ),
    )
    defer span.End()
    
    // Go 1.21+ WithoutCancel
    detached := context.WithoutCancel(ctx)
    
    span.AddEvent("context detached from parent cancellation")
    
    return detached
}

// MonitorCancellation 监控 Context 取消
func (cm *CancellationManager) MonitorCancellation(
    ctx context.Context,
    operationName string,
    onCancel func(error),
) {
    go func() {
        ctx, span := cm.tracer.Start(ctx, "monitor.cancellation",
            trace.WithAttributes(
                attribute.String("operation", operationName),
            ),
        )
        defer span.End()
        
        <-ctx.Done()
        
        cause := context.Cause(ctx)
        
        span.AddEvent("context cancelled")
        span.SetAttributes(
            attribute.String("cancel.reason", fmt.Sprintf("%v", cause)),
        )
        
        if onCancel != nil {
            onCancel(cause)
        }
    }()
}

// AfterCancel 在 Context 取消后执行清理 (Go 1.21+)
func (cm *CancellationManager) AfterCancel(
    ctx context.Context,
    cleanup func(),
) context.StopFunc {
    span := trace.SpanFromContext(ctx)
    
    // Go 1.21+ AfterFunc
    stop := context.AfterFunc(ctx, func() {
        span.AddEvent("cleanup triggered by cancellation")
        cleanup()
    })
    
    return stop
}
```

---

## 超时与截止时间

### 完整的超时管理

```go
package timeout

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TimeoutManager 超时管理器
type TimeoutManager struct {
    tracer trace.Tracer
}

// NewTimeoutManager 创建超时管理器
func NewTimeoutManager() *TimeoutManager {
    return &TimeoutManager{
        tracer: otel.Tracer("timeout-manager"),
    }
}

// WithTimeout 执行带超时的操作
func (tm *TimeoutManager) WithTimeout(
    ctx context.Context,
    timeout time.Duration,
    operation string,
    fn func(context.Context) error,
) error {
    ctx, span := tm.tracer.Start(ctx, operation,
        trace.WithAttributes(
            attribute.Float64("timeout_ms", float64(timeout.Milliseconds())),
        ),
    )
    defer span.End()
    
    // 创建超时错误作为原因
    timeoutErr := &TimeoutError{
        Operation: operation,
        Timeout:   timeout,
    }
    
    // 创建带超时和原因的 context
    ctx, cancel := context.WithTimeoutCause(ctx, timeout, timeoutErr)
    defer cancel()
    
    // 记录开始时间
    start := time.Now()
    
    // 执行函数
    err := fn(ctx)
    elapsed := time.Since(start)
    
    span.SetAttributes(
        attribute.Float64("elapsed_ms", float64(elapsed.Milliseconds())),
    )
    
    // 检查超时
    if ctx.Err() != nil {
        timeoutErr.Elapsed = elapsed
        span.RecordError(timeoutErr)
        span.SetStatus(codes.Error, "timeout")
        span.SetAttributes(attribute.Bool("timeout", true))
        return timeoutErr
    }
    
    // 检查其他错误
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// WithDeadline 执行带截止时间的操作
func (tm *TimeoutManager) WithDeadline(
    ctx context.Context,
    deadline time.Time,
    operation string,
    fn func(context.Context) error,
) error {
    timeout := time.Until(deadline)
    if timeout <= 0 {
        return fmt.Errorf("deadline already passed")
    }
    
    return tm.WithTimeout(ctx, timeout, operation, fn)
}

// WithRetryOnTimeout 超时重试
func (tm *TimeoutManager) WithRetryOnTimeout(
    ctx context.Context,
    timeout time.Duration,
    maxRetries int,
    operation string,
    fn func(context.Context) error,
) error {
    ctx, span := tm.tracer.Start(ctx, "retry.timeout",
        trace.WithAttributes(
            attribute.String("operation", operation),
            attribute.Int("max_retries", maxRetries),
            attribute.Float64("timeout_ms", float64(timeout.Milliseconds())),
        ),
    )
    defer span.End()
    
    var lastErr error
    
    for attempt := 0; attempt <= maxRetries; attempt++ {
        span.AddEvent("attempt", trace.WithAttributes(
            attribute.Int("attempt", attempt),
        ))
        
        err := tm.WithTimeout(ctx, timeout, operation, fn)
        
        if err == nil {
            span.SetAttributes(
                attribute.Int("successful_attempt", attempt),
            )
            return nil
        }
        
        lastErr = err
        
        // 检查是否是超时错误
        var timeoutErr *TimeoutError
        if !errors.As(err, &timeoutErr) {
            // 非超时错误，不重试
            span.RecordError(err)
            return err
        }
        
        if attempt < maxRetries {
            backoff := time.Duration(attempt+1) * 100 * time.Millisecond
            time.Sleep(backoff)
        }
    }
    
    span.RecordError(lastErr)
    span.SetAttributes(
        attribute.Int("failed_attempts", maxRetries+1),
    )
    
    return lastErr
}

// CascadingTimeout 级联超时（为不同阶段设置不同超时）
func (tm *TimeoutManager) CascadingTimeout(
    ctx context.Context,
    stages []Stage,
) error {
    ctx, span := tm.tracer.Start(ctx, "cascading.timeout",
        trace.WithAttributes(
            attribute.Int("stages.count", len(stages)),
        ),
    )
    defer span.End()
    
    for i, stage := range stages {
        span.AddEvent("executing stage", trace.WithAttributes(
            attribute.Int("stage.index", i),
            attribute.String("stage.name", stage.Name),
        ))
        
        err := tm.WithTimeout(ctx, stage.Timeout, stage.Name, stage.Fn)
        if err != nil {
            span.RecordError(err)
            span.SetAttributes(
                attribute.Int("failed.stage", i),
            )
            return fmt.Errorf("stage %d (%s) failed: %w", i, stage.Name, err)
        }
    }
    
    return nil
}

// Stage 阶段定义
type Stage struct {
    Name    string
    Timeout time.Duration
    Fn      func(context.Context) error
}
```

---

## 错误恢复策略

```go
package recovery

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// RecoveryStrategy 恢复策略接口
type RecoveryStrategy interface {
    ShouldRetry(error) bool
    GetBackoff(attempt int) time.Duration
    MaxAttempts() int
}

// ExponentialBackoff 指数退避策略
type ExponentialBackoff struct {
    InitialBackoff time.Duration
    MaxBackoff     time.Duration
    Multiplier     float64
    MaxAttempts_   int
}

func (eb *ExponentialBackoff) ShouldRetry(err error) bool {
    // 检查错误是否可重试
    if tracedErr, ok := err.(*TracedError); ok {
        return tracedErr.Retryable
    }
    return false
}

func (eb *ExponentialBackoff) GetBackoff(attempt int) time.Duration {
    backoff := time.Duration(float64(eb.InitialBackoff) * 
        math.Pow(eb.Multiplier, float64(attempt)))
    
    if backoff > eb.MaxBackoff {
        backoff = eb.MaxBackoff
    }
    
    return backoff
}

func (eb *ExponentialBackoff) MaxAttempts() int {
    return eb.MaxAttempts_
}

// ExecuteWithRecovery 执行带恢复的操作
func ExecuteWithRecovery(
    ctx context.Context,
    operation string,
    strategy RecoveryStrategy,
    fn func(context.Context) error,
) error {
    tracer := otel.Tracer("recovery")
    
    ctx, span := tracer.Start(ctx, "execute.with_recovery",
        trace.WithAttributes(
            attribute.String("operation", operation),
            attribute.Int("max_attempts", strategy.MaxAttempts()),
        ),
    )
    defer span.End()
    
    var lastErr error
    
    for attempt := 0; attempt < strategy.MaxAttempts(); attempt++ {
        span.AddEvent("attempt", trace.WithAttributes(
            attribute.Int("attempt", attempt),
        ))
        
        err := fn(ctx)
        
        if err == nil {
            span.SetAttributes(
                attribute.Int("successful_attempt", attempt),
            )
            return nil
        }
        
        lastErr = err
        
        // 检查是否应该重试
        if !strategy.ShouldRetry(err) {
            span.AddEvent("error not retryable")
            span.RecordError(err)
            return err
        }
        
        // 等待退避
        if attempt < strategy.MaxAttempts()-1 {
            backoff := strategy.GetBackoff(attempt)
            span.AddEvent("backing off", trace.WithAttributes(
                attribute.Float64("backoff_ms", float64(backoff.Milliseconds())),
            ))
            
            select {
            case <-time.After(backoff):
            case <-ctx.Done():
                return ctx.Err()
            }
        }
    }
    
    span.RecordError(lastErr)
    span.SetAttributes(
        attribute.Int("failed_attempts", strategy.MaxAttempts()),
    )
    
    return fmt.Errorf("all retry attempts failed: %w", lastErr)
}
```

---

## 最佳实践

### 1. 错误检查

```go
// ✅ 使用 errors.Is
if errors.Is(err, ErrNotFound) {
    // 处理
}

// ✅ 使用 errors.As
var netErr *NetworkError
if errors.As(err, &netErr) {
    // 处理网络错误
}

// ❌ 不要使用 ==
if err == ErrNotFound { // 可能错误
}
```

### 2. Context 传播

```go
// ✅ 传递 Context
func ProcessRequest(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()
    
    return doWork(ctx) // 传递 ctx
}

// ❌ 创建新 Context
func ProcessRequest(ctx context.Context) error {
    newCtx := context.Background() // 丢失追踪信息
    return doWork(newCtx)
}
```

### 3. 错误记录

```go
// ✅ 记录并返回
if err != nil {
    span.RecordError(err)
    return fmt.Errorf("operation failed: %w", err)
}

// ✅ 记录但不返回（已处理）
if err != nil {
    span.RecordError(err)
    // 降级处理
    return fallbackValue
}
```

---

## 总结

本文档提供了完整的 Go 高级错误处理与 Context 传播方案:

**核心特性**:

- ✅ 自定义错误类型
- ✅ 错误包装与追踪
- ✅ 多错误聚合 (errors.Join)
- ✅ Context 取消传播
- ✅ 超时管理
- ✅ 错误恢复策略

**Go 1.20+ 新特性**:

- ✅ errors.Join - 多错误合并
- ✅ context.WithCause - 带原因的取消
- ✅ context.Cause - 获取取消原因

**Go 1.21+ 新特性**:

- ✅ context.WithoutCancel - 分离 Context
- ✅ context.AfterFunc - 清理回调
- ✅ context.WithDeadlineCause - 带原因的截止时间

**相关文档**:

- [Go错误处理与OTLP集成](./13_Go错误处理与OTLP集成.md)
- [Go_Context高级模式与最佳实践](./14_Go_Context高级模式与最佳实践.md)
- [Go高级并发模式与OTLP完整集成](./31_Go高级并发模式与OTLP完整集成.md)

---

**最后更新**: 2025年10月10日  
**维护者**: OTLP Go 集成项目组

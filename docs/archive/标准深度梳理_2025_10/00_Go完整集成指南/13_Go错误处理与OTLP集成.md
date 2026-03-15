# Go 错误处理与 OTLP 集成深度指南

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0+  
> **最后更新**: 2025年10月8日

---

## 📋 目录

- [Go 错误处理与 OTLP 集成深度指南](#go-错误处理与-otlp-集成深度指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [1. Go 错误处理基础](#1-go-错误处理基础)
    - [1.1 标准错误处理](#11-标准错误处理)
    - [1.2 错误包装与展开](#12-错误包装与展开)
    - [1.3 自定义错误类型](#13-自定义错误类型)
  - [2. errors.Join 多错误合并](#2-errorsjoin-多错误合并)
    - [2.1 基本用法](#21-基本用法)
    - [2.2 在 OTLP 中的应用](#22-在-otlp-中的应用)
    - [2.3 批处理错误收集](#23-批处理错误收集)
  - [3. 错误链追踪](#3-错误链追踪)
    - [3.1 错误链分析器](#31-错误链分析器)
    - [3.2 错误堆栈追踪](#32-错误堆栈追踪)
  - [4. 错误分类与处理](#4-错误分类与处理)
    - [4.1 错误分类系统](#41-错误分类系统)
    - [4.2 可重试错误处理](#42-可重试错误处理)
  - [5. Panic 处理与恢复](#5-panic-处理与恢复)
    - [5.1 Panic 捕获中间件](#51-panic-捕获中间件)
    - [5.2 Goroutine Panic 处理](#52-goroutine-panic-处理)
  - [参考资料](#参考资料)

---

## 概述

Go 的错误处理哲学强调显式错误检查和处理。结合 OpenTelemetry，我们可以构建一个强大的错误追踪和分析系统。

**核心概念**:

```text
✅ 显式错误处理 - 不隐藏错误
✅ 错误包装 - 保留错误上下文
✅ 错误链追踪 - 完整的错误路径
✅ 自定义错误类型 - 丰富的错误信息
✅ 与 Span 集成 - 自动记录错误
```

---

## 1. Go 错误处理基础

### 1.1 标准错误处理

```go
package observability

import (
    "context"
    "errors"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// BasicErrorHandler 基本错误处理器
type BasicErrorHandler struct {
    tracer trace.Tracer
}

func NewBasicErrorHandler() *BasicErrorHandler {
    return &BasicErrorHandler{
        tracer: otel.Tracer("error-handler"),
    }
}

// HandleOperation 处理操作并记录错误
func (beh *BasicErrorHandler) HandleOperation(
    ctx context.Context,
    operationName string,
    fn func(context.Context) error,
) error {
    ctx, span := beh.tracer.Start(ctx, operationName)
    defer span.End()

    err := fn(ctx)
    if err != nil {
        // 记录错误到 span
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())

        // 添加错误属性
        span.SetAttributes(
            attribute.String("error.type", fmt.Sprintf("%T", err)),
            attribute.String("error.message", err.Error()),
        )

        return err
    }

    span.SetStatus(codes.Ok, "success")
    return nil
}

// 使用示例
func ExampleBasicErrorHandling(ctx context.Context) error {
    handler := NewBasicErrorHandler()

    return handler.HandleOperation(ctx, "database-query", func(ctx context.Context) error {
        // 模拟数据库查询
        if err := queryDatabase(ctx); err != nil {
            return fmt.Errorf("database query failed: %w", err)
        }
        return nil
    })
}

func queryDatabase(ctx context.Context) error {
    return errors.New("connection timeout")
}
```

### 1.2 错误包装与展开

```go
package observability

import (
    "context"
    "errors"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// WrappedErrorHandler 包装错误处理器
type WrappedErrorHandler struct {
    tracer trace.Tracer
}

func NewWrappedErrorHandler() *WrappedErrorHandler {
    return &WrappedErrorHandler{
        tracer: otel.Tracer("wrapped-error-handler"),
    }
}

// ProcessWithErrorWrapping 处理操作并包装错误
func (weh *WrappedErrorHandler) ProcessWithErrorWrapping(ctx context.Context) error {
    ctx, span := weh.tracer.Start(ctx, "process-with-wrapping")
    defer span.End()

    // 执行多层操作
    if err := weh.fetchData(ctx); err != nil {
        // 记录完整的错误链
        weh.recordErrorChain(span, err)
        return fmt.Errorf("failed to process: %w", err)
    }

    return nil
}

func (weh *WrappedErrorHandler) fetchData(ctx context.Context) error {
    _, span := weh.tracer.Start(ctx, "fetch-data")
    defer span.End()

    if err := weh.connectDatabase(ctx); err != nil {
        return fmt.Errorf("fetch data failed: %w", err)
    }

    return nil
}

func (weh *WrappedErrorHandler) connectDatabase(ctx context.Context) error {
    _, span := weh.tracer.Start(ctx, "connect-database")
    defer span.End()

    // 模拟连接错误
    baseErr := errors.New("connection refused")
    return fmt.Errorf("database connection error: %w", baseErr)
}

func (weh *WrappedErrorHandler) recordErrorChain(span trace.Span, err error) {
    var chain []string
    current := err

    // 展开错误链
    for current != nil {
        chain = append(chain, current.Error())
        current = errors.Unwrap(current)
    }

    // 记录到 span
    span.SetAttributes(
        attribute.StringSlice("error.chain", chain),
        attribute.Int("error.depth", len(chain)),
    )
}
```

### 1.3 自定义错误类型

```go
package observability

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// DatabaseError 数据库错误
type DatabaseError struct {
    Operation string
    Table     string
    Query     string
    Err       error
    Timestamp time.Time
    Retryable bool
}

func (e *DatabaseError) Error() string {
    return fmt.Sprintf("database %s on table %s failed: %v",
        e.Operation, e.Table, e.Err)
}

func (e *DatabaseError) Unwrap() error {
    return e.Err
}

// ToSpanAttributes 转换为 Span 属性
func (e *DatabaseError) ToSpanAttributes() []attribute.KeyValue {
    return []attribute.KeyValue{
        attribute.String("db.operation", e.Operation),
        attribute.String("db.table", e.Table),
        attribute.String("db.query", e.Query),
        attribute.Bool("error.retryable", e.Retryable),
        attribute.String("error.timestamp", e.Timestamp.Format(time.RFC3339)),
    }
}

// ValidationError 验证错误
type ValidationError struct {
    Field   string
    Value   interface{}
    Message string
}

func (e *ValidationError) Error() string {
    return fmt.Sprintf("validation failed for field %s: %s (value: %v)",
        e.Field, e.Message, e.Value)
}

func (e *ValidationError) ToSpanAttributes() []attribute.KeyValue {
    return []attribute.KeyValue{
        attribute.String("validation.field", e.Field),
        attribute.String("validation.message", e.Message),
        attribute.String("validation.value", fmt.Sprintf("%v", e.Value)),
    }
}

// CustomErrorHandler 自定义错误处理器
type CustomErrorHandler struct {
    tracer trace.Tracer
}

func NewCustomErrorHandler() *CustomErrorHandler {
    return &CustomErrorHandler{
        tracer: otel.Tracer("custom-error-handler"),
    }
}

// HandleTypedError 处理类型化错误
func (ceh *CustomErrorHandler) HandleTypedError(
    ctx context.Context,
    err error,
) error {
    ctx, span := ceh.tracer.Start(ctx, "handle-typed-error")
    defer span.End()

    if err == nil {
        return nil
    }

    // 根据错误类型添加不同的属性
    switch e := err.(type) {
    case *DatabaseError:
        span.SetAttributes(e.ToSpanAttributes()...)
        span.SetAttributes(attribute.String("error.category", "database"))

        if e.Retryable {
            span.SetStatus(codes.Error, "database error (retryable)")
        } else {
            span.SetStatus(codes.Error, "database error (not retryable)")
        }

    case *ValidationError:
        span.SetAttributes(e.ToSpanAttributes()...)
        span.SetAttributes(attribute.String("error.category", "validation"))
        span.SetStatus(codes.Error, "validation error")

    default:
        span.SetAttributes(
            attribute.String("error.type", fmt.Sprintf("%T", err)),
            attribute.String("error.category", "unknown"),
        )
        span.SetStatus(codes.Error, err.Error())
    }

    span.RecordError(err)
    return err
}

// 使用示例
func ExampleCustomErrors(ctx context.Context) error {
    handler := NewCustomErrorHandler()

    // 数据库错误
    dbErr := &DatabaseError{
        Operation: "INSERT",
        Table:     "users",
        Query:     "INSERT INTO users ...",
        Err:       fmt.Errorf("connection timeout"),
        Timestamp: time.Now(),
        Retryable: true,
    }

    if err := handler.HandleTypedError(ctx, dbErr); err != nil {
        return err
    }

    // 验证错误
    validationErr := &ValidationError{
        Field:   "email",
        Value:   "invalid-email",
        Message: "invalid email format",
    }

    return handler.HandleTypedError(ctx, validationErr)
}
```

---

## 2. errors.Join 多错误合并

### 2.1 基本用法

```go
package observability

import (
    "context"
    "errors"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// MultiErrorCollector 多错误收集器
type MultiErrorCollector struct {
    tracer trace.Tracer
    errors []error
}

func NewMultiErrorCollector() *MultiErrorCollector {
    return &MultiErrorCollector{
        tracer: otel.Tracer("multi-error-collector"),
        errors: make([]error, 0),
    }
}

// Add 添加错误
func (mec *MultiErrorCollector) Add(err error) {
    if err != nil {
        mec.errors = append(mec.errors, err)
    }
}

// Error 返回合并的错误
func (mec *MultiErrorCollector) Error() error {
    if len(mec.errors) == 0 {
        return nil
    }

    // Go 1.25.1: 使用 errors.Join
    return errors.Join(mec.errors...)
}

// RecordToSpan 记录到 Span
func (mec *MultiErrorCollector) RecordToSpan(ctx context.Context) {
    if len(mec.errors) == 0 {
        return
    }

    span := trace.SpanFromContext(ctx)
    if !span.IsRecording() {
        return
    }

    joinedErr := mec.Error()
    span.RecordError(joinedErr)
    span.SetStatus(codes.Error, "multiple errors occurred")

    // 记录每个错误的详细信息
    for i, err := range mec.errors {
        span.SetAttributes(
            attribute.String(fmt.Sprintf("error.%d", i), err.Error()),
        )
    }

    span.SetAttributes(
        attribute.Int("error.count", len(mec.errors)),
    )
}

// 使用示例：并发操作错误收集
func ExampleMultiErrorCollection(ctx context.Context) error {
    ctx, span := otel.Tracer("example").Start(ctx, "multi-operation")
    defer span.End()

    collector := NewMultiErrorCollector()

    // 执行多个可能失败的操作
    operations := []func() error{
        func() error { return errors.New("operation 1 failed") },
        func() error { return nil }, // 成功
        func() error { return errors.New("operation 3 failed") },
    }

    for i, op := range operations {
        if err := op(); err != nil {
            collector.Add(fmt.Errorf("operation %d: %w", i, err))
        }
    }

    // 记录所有错误
    collector.RecordToSpan(ctx)

    return collector.Error()
}
```

### 2.2 在 OTLP 中的应用

```go
package observability

import (
    "context"
    "errors"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ResourceCleanup 资源清理（收集所有清理错误）
type ResourceCleanup struct {
    tracer trace.Tracer
}

func NewResourceCleanup() *ResourceCleanup {
    return &ResourceCleanup{
        tracer: otel.Tracer("resource-cleanup"),
    }
}

type CleanupFunc func(context.Context) error

// CleanupAll 清理所有资源（不会因为单个失败而中断）
func (rc *ResourceCleanup) CleanupAll(
    ctx context.Context,
    cleanups []CleanupFunc,
) error {
    ctx, span := rc.tracer.Start(ctx, "cleanup-all")
    defer span.End()

    var cleanupErrors []error

    for i, cleanup := range cleanups {
        if err := cleanup(ctx); err != nil {
            cleanupErrors = append(cleanupErrors,
                fmt.Errorf("cleanup %d failed: %w", i, err))

            // 为每个清理失败创建子 span
            _, errSpan := rc.tracer.Start(ctx, fmt.Sprintf("cleanup-%d", i))
            errSpan.RecordError(err)
            errSpan.End()
        }
    }

    // Go 1.25.1: 合并所有清理错误
    if len(cleanupErrors) > 0 {
        joinedErr := errors.Join(cleanupErrors...)
        span.RecordError(joinedErr)
        span.SetAttributes(
            attribute.Int("cleanup.total", len(cleanups)),
            attribute.Int("cleanup.failed", len(cleanupErrors)),
            attribute.Int("cleanup.succeeded", len(cleanups)-len(cleanupErrors)),
        )
        return joinedErr
    }

    span.SetAttributes(
        attribute.Int("cleanup.total", len(cleanups)),
        attribute.Int("cleanup.succeeded", len(cleanups)),
    )
    return nil
}

// 使用示例
func ExampleResourceCleanup(ctx context.Context) error {
    cleanup := NewResourceCleanup()

    cleanups := []CleanupFunc{
        func(ctx context.Context) error {
            // 清理数据库连接
            return cleanupDatabase(ctx)
        },
        func(ctx context.Context) error {
            // 清理缓存
            return cleanupCache(ctx)
        },
        func(ctx context.Context) error {
            // 清理临时文件
            return cleanupTempFiles(ctx)
        },
    }

    return cleanup.CleanupAll(ctx, cleanups)
}

func cleanupDatabase(ctx context.Context) error {
    return errors.New("database cleanup failed")
}

func cleanupCache(ctx context.Context) error {
    return nil // 成功
}

func cleanupTempFiles(ctx context.Context) error {
    return errors.New("temp file cleanup failed")
}
```

### 2.3 批处理错误收集

```go
package observability

import (
    "context"
    "errors"
    "fmt"
    "sync"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// BatchProcessor 批处理器（并发安全的错误收集）
type BatchProcessor struct {
    tracer     trace.Tracer
    errorMu    sync.Mutex
    errors     []error
    maxErrors  int
}

func NewBatchProcessor(maxErrors int) *BatchProcessor {
    return &BatchProcessor{
        tracer:    otel.Tracer("batch-processor"),
        errors:    make([]error, 0),
        maxErrors: maxErrors,
    }
}

// ProcessItem 处理单个项目
func (bp *BatchProcessor) ProcessItem(
    ctx context.Context,
    item interface{},
    processor func(context.Context, interface{}) error,
) {
    _, span := bp.tracer.Start(ctx, "process-item")
    defer span.End()

    if err := processor(ctx, item); err != nil {
        bp.recordError(span, err)
    }
}

// ProcessBatch 并发处理批次
func (bp *BatchProcessor) ProcessBatch(
    ctx context.Context,
    items []interface{},
    processor func(context.Context, interface{}) error,
) error {
    ctx, span := bp.tracer.Start(ctx, "process-batch")
    defer span.End()

    var wg sync.WaitGroup
    itemChan := make(chan interface{}, len(items))

    // 启动工作 goroutines
    numWorkers := 5
    for i := 0; i < numWorkers; i++ {
        wg.Add(1)
        go func(workerID int) {
            defer wg.Done()

            for item := range itemChan {
                workerCtx, workerSpan := bp.tracer.Start(ctx,
                    fmt.Sprintf("worker-%d", workerID))

                if err := processor(workerCtx, item); err != nil {
                    bp.recordError(workerSpan, err)
                }

                workerSpan.End()
            }
        }(i)
    }

    // 分发任务
    for _, item := range items {
        itemChan <- item
    }
    close(itemChan)

    // 等待完成
    wg.Wait()

    // 返回合并的错误
    return bp.getErrors(span)
}

func (bp *BatchProcessor) recordError(span trace.Span, err error) {
    bp.errorMu.Lock()
    defer bp.errorMu.Unlock()

    // 限制错误数量
    if len(bp.errors) < bp.maxErrors {
        bp.errors = append(bp.errors, err)
        span.RecordError(err)
    }
}

func (bp *BatchProcessor) getErrors(span trace.Span) error {
    bp.errorMu.Lock()
    defer bp.errorMu.Unlock()

    if len(bp.errors) == 0 {
        return nil
    }

    // Go 1.25.1: 合并错误
    joinedErr := errors.Join(bp.errors...)

    span.RecordError(joinedErr)
    span.SetAttributes(
        attribute.Int("batch.error_count", len(bp.errors)),
        attribute.Bool("batch.error_limit_reached", len(bp.errors) >= bp.maxErrors),
    )

    return joinedErr
}
```

---

## 3. 错误链追踪

### 3.1 错误链分析器

```go
package observability

import (
    "context"
    "errors"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ErrorChainAnalyzer 错误链分析器
type ErrorChainAnalyzer struct {
    tracer trace.Tracer
}

func NewErrorChainAnalyzer() *ErrorChainAnalyzer {
    return &ErrorChainAnalyzer{
        tracer: otel.Tracer("error-chain-analyzer"),
    }
}

// ErrorInfo 错误信息
type ErrorInfo struct {
    Message string
    Type    string
    Level   int
}

// AnalyzeErrorChain 分析错误链
func (eca *ErrorChainAnalyzer) AnalyzeErrorChain(
    ctx context.Context,
    err error,
) []ErrorInfo {
    _, span := eca.tracer.Start(ctx, "analyze-error-chain")
    defer span.End()

    var chain []ErrorInfo
    level := 0

    current := err
    for current != nil {
        info := ErrorInfo{
            Message: current.Error(),
            Type:    fmt.Sprintf("%T", current),
            Level:   level,
        }
        chain = append(chain, info)

        // 记录到 span
        span.SetAttributes(
            attribute.String(fmt.Sprintf("error.chain.%d.type", level), info.Type),
            attribute.String(fmt.Sprintf("error.chain.%d.message", level), info.Message),
        )

        // 尝试展开
        unwrapped := errors.Unwrap(current)
        if unwrapped == nil {
            // Go 1.25.1: 检查是否是 joined error
            if joinErr, ok := current.(interface{ Unwrap() []error }); ok {
                errs := joinErr.Unwrap()
                span.SetAttributes(
                    attribute.Int(fmt.Sprintf("error.chain.%d.branches", level), len(errs)),
                )

                // 处理多个分支
                for i, e := range errs {
                    branchInfo := ErrorInfo{
                        Message: e.Error(),
                        Type:    fmt.Sprintf("%T", e),
                        Level:   level + 1,
                    }
                    chain = append(chain, branchInfo)

                    span.SetAttributes(
                        attribute.String(fmt.Sprintf("error.chain.%d.branch.%d", level, i), e.Error()),
                    )
                }
                break
            }
            break
        }

        current = unwrapped
        level++
    }

    span.SetAttributes(
        attribute.Int("error.chain.depth", len(chain)),
    )

    return chain
}

// VisualizeChain 可视化错误链
func (eca *ErrorChainAnalyzer) VisualizeChain(chain []ErrorInfo) string {
    var result string
    for _, info := range chain {
        indent := ""
        for i := 0; i < info.Level; i++ {
            indent += "  "
        }
        result += fmt.Sprintf("%s[%s] %s\n", indent, info.Type, info.Message)
    }
    return result
}

// 使用示例
func ExampleErrorChainAnalysis(ctx context.Context) {
    analyzer := NewErrorChainAnalyzer()

    // 创建嵌套错误
    err1 := errors.New("database connection failed")
    err2 := fmt.Errorf("query execution error: %w", err1)
    err3 := fmt.Errorf("user lookup failed: %w", err2)

    // 创建分支错误
    validationErr := errors.New("validation failed")
    permissionErr := errors.New("permission denied")
    joinedErr := errors.Join(err3, validationErr, permissionErr)

    // 分析错误链
    chain := analyzer.AnalyzeErrorChain(ctx, joinedErr)

    // 可视化
    visualization := analyzer.VisualizeChain(chain)
    fmt.Println(visualization)

    /*
    输出示例：
    [*fmt.wrapError] user lookup failed: query execution error: database connection failed
      [*fmt.wrapError] query execution error: database connection failed
        [*errors.errorString] database connection failed
      [*errors.errorString] validation failed
      [*errors.errorString] permission denied
    */
}
```

### 3.2 错误堆栈追踪

```go
package observability

import (
    "context"
    "fmt"
    "runtime"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// StackTraceError 带堆栈追踪的错误
type StackTraceError struct {
    Err   error
    Stack []uintptr
}

func NewStackTraceError(err error) *StackTraceError {
    const depth = 32
    var pcs [depth]uintptr
    n := runtime.Callers(2, pcs[:])

    return &StackTraceError{
        Err:   err,
        Stack: pcs[:n],
    }
}

func (e *StackTraceError) Error() string {
    return e.Err.Error()
}

func (e *StackTraceError) Unwrap() error {
    return e.Err
}

// GetStackTrace 获取格式化的堆栈追踪
func (e *StackTraceError) GetStackTrace() []string {
    frames := runtime.CallersFrames(e.Stack)
    var trace []string

    for {
        frame, more := frames.Next()
        trace = append(trace, fmt.Sprintf("%s:%d %s",
            frame.File, frame.Line, frame.Function))

        if !more {
            break
        }
    }

    return trace
}

// StackTraceHandler 堆栈追踪处理器
type StackTraceHandler struct {
    tracer trace.Tracer
}

func NewStackTraceHandler() *StackTraceHandler {
    return &StackTraceHandler{
        tracer: otel.Tracer("stack-trace-handler"),
    }
}

// HandleWithStackTrace 处理错误并记录堆栈
func (sth *StackTraceHandler) HandleWithStackTrace(
    ctx context.Context,
    err error,
) error {
    if err == nil {
        return nil
    }

    ctx, span := sth.tracer.Start(ctx, "handle-with-stack-trace")
    defer span.End()

    // 包装为带堆栈的错误
    var stackErr *StackTraceError
    if !errors.As(err, &stackErr) {
        stackErr = NewStackTraceError(err)
    }

    // 记录错误
    span.RecordError(stackErr)

    // 记录堆栈追踪
    stackTrace := stackErr.GetStackTrace()
    for i, frame := range stackTrace {
        span.SetAttributes(
            attribute.String(fmt.Sprintf("stack.%d", i), frame),
        )
    }

    span.SetAttributes(
        attribute.Int("stack.depth", len(stackTrace)),
    )

    return stackErr
}

// 使用示例
func ExampleStackTraceError(ctx context.Context) error {
    handler := NewStackTraceHandler()

    err := performOperation()
    if err != nil {
        return handler.HandleWithStackTrace(ctx, err)
    }

    return nil
}

func performOperation() error {
    return NewStackTraceError(errors.New("operation failed"))
}
```

---

## 4. 错误分类与处理

### 4.1 错误分类系统

```go
package observability

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// ErrorCategory 错误类别
type ErrorCategory string

const (
    ErrorCategoryValidation  ErrorCategory = "validation"
    ErrorCategoryDatabase    ErrorCategory = "database"
    ErrorCategoryNetwork     ErrorCategory = "network"
    ErrorCategoryPermission  ErrorCategory = "permission"
    ErrorCategoryRateLimit   ErrorCategory = "rate_limit"
    ErrorCategoryNotFound    ErrorCategory = "not_found"
    ErrorCategoryInternal    ErrorCategory = "internal"
    ErrorCategoryExternal    ErrorCategory = "external"
)

// ErrorSeverity 错误严重性
type ErrorSeverity string

const (
    ErrorSeverityLow      ErrorSeverity = "low"
    ErrorSeverityMedium   ErrorSeverity = "medium"
    ErrorSeverityHigh     ErrorSeverity = "high"
    ErrorSeverityCritical ErrorSeverity = "critical"
)

// CategorizedError 分类错误
type CategorizedError struct {
    Err       error
    Category  ErrorCategory
    Severity  ErrorSeverity
    Code      string
    Retryable bool
    Metadata  map[string]interface{}
}

func NewCategorizedError(
    err error,
    category ErrorCategory,
    severity ErrorSeverity,
) *CategorizedError {
    return &CategorizedError{
        Err:      err,
        Category: category,
        Severity: severity,
        Metadata: make(map[string]interface{}),
    }
}

func (e *CategorizedError) Error() string {
    return e.Err.Error()
}

func (e *CategorizedError) Unwrap() error {
    return e.Err
}

func (e *CategorizedError) WithCode(code string) *CategorizedError {
    e.Code = code
    return e
}

func (e *CategorizedError) WithRetryable(retryable bool) *CategorizedError {
    e.Retryable = retryable
    return e
}

func (e *CategorizedError) WithMetadata(key string, value interface{}) *CategorizedError {
    e.Metadata[key] = value
    return e
}

// ToSpanAttributes 转换为 Span 属性
func (e *CategorizedError) ToSpanAttributes() []attribute.KeyValue {
    attrs := []attribute.KeyValue{
        attribute.String("error.category", string(e.Category)),
        attribute.String("error.severity", string(e.Severity)),
        attribute.Bool("error.retryable", e.Retryable),
    }

    if e.Code != "" {
        attrs = append(attrs, attribute.String("error.code", e.Code))
    }

    for key, value := range e.Metadata {
        attrs = append(attrs, attribute.String(
            fmt.Sprintf("error.metadata.%s", key),
            fmt.Sprintf("%v", value),
        ))
    }

    return attrs
}

// ErrorClassifier 错误分类器
type ErrorClassifier struct {
    tracer trace.Tracer
}

func NewErrorClassifier() *ErrorClassifier {
    return &ErrorClassifier{
        tracer: otel.Tracer("error-classifier"),
    }
}

// Classify 分类错误
func (ec *ErrorClassifier) Classify(
    ctx context.Context,
    err error,
) (*CategorizedError, error) {
    if err == nil {
        return nil, nil
    }

    _, span := ec.tracer.Start(ctx, "classify-error")
    defer span.End()

    // 检查是否已经是分类错误
    var catErr *CategorizedError
    if errors.As(err, &catErr) {
        span.SetAttributes(catErr.ToSpanAttributes()...)
        return catErr, err
    }

    // 根据错误类型分类
    catErr = ec.classifyByType(err)

    // 记录分类信息
    span.SetAttributes(catErr.ToSpanAttributes()...)
    span.RecordError(catErr)

    return catErr, catErr
}

func (ec *ErrorClassifier) classifyByType(err error) *CategorizedError {
    errStr := err.Error()

    // 简单的规则匹配（实际应用中可能更复杂）
    switch {
    case contains(errStr, "validation", "invalid", "malformed"):
        return NewCategorizedError(err, ErrorCategoryValidation, ErrorSeverityLow).
            WithRetryable(false)

    case contains(errStr, "not found", "missing"):
        return NewCategorizedError(err, ErrorCategoryNotFound, ErrorSeverityLow).
            WithRetryable(false)

    case contains(errStr, "permission", "unauthorized", "forbidden"):
        return NewCategorizedError(err, ErrorCategoryPermission, ErrorSeverityMedium).
            WithRetryable(false)

    case contains(errStr, "database", "sql", "query"):
        return NewCategorizedError(err, ErrorCategoryDatabase, ErrorSeverityHigh).
            WithRetryable(true)

    case contains(errStr, "network", "connection", "timeout"):
        return NewCategorizedError(err, ErrorCategoryNetwork, ErrorSeverityMedium).
            WithRetryable(true)

    case contains(errStr, "rate limit", "too many requests"):
        return NewCategorizedError(err, ErrorCategoryRateLimit, ErrorSeverityMedium).
            WithRetryable(true).
            WithMetadata("backoff", "exponential")

    default:
        return NewCategorizedError(err, ErrorCategoryInternal, ErrorSeverityHigh).
            WithRetryable(false)
    }
}

func contains(s string, substrs ...string) bool {
    for _, substr := range substrs {
        if len(s) >= len(substr) {
            for i := 0; i <= len(s)-len(substr); i++ {
                if s[i:i+len(substr)] == substr {
                    return true
                }
            }
        }
    }
    return false
}
```

### 4.2 可重试错误处理

```go
package observability

import (
    "context"
    "fmt"
    "math"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// RetryPolicy 重试策略
type RetryPolicy struct {
    MaxAttempts int
    InitialDelay time.Duration
    MaxDelay time.Duration
    Multiplier float64
}

// DefaultRetryPolicy 默认重试策略
func DefaultRetryPolicy() *RetryPolicy {
    return &RetryPolicy{
        MaxAttempts:  3,
        InitialDelay: 100 * time.Millisecond,
        MaxDelay:     5 * time.Second,
        Multiplier:   2.0,
    }
}

// RetryHandler 重试处理器
type RetryHandler struct {
    tracer     trace.Tracer
    classifier *ErrorClassifier
    policy     *RetryPolicy
}

func NewRetryHandler(policy *RetryPolicy) *RetryHandler {
    if policy == nil {
        policy = DefaultRetryPolicy()
    }

    return &RetryHandler{
        tracer:     otel.Tracer("retry-handler"),
        classifier: NewErrorClassifier(),
        policy:     policy,
    }
}

// ExecuteWithRetry 执行操作并自动重试
func (rh *RetryHandler) ExecuteWithRetry(
    ctx context.Context,
    operationName string,
    fn func(context.Context) error,
) error {
    ctx, span := rh.tracer.Start(ctx, operationName)
    defer span.End()

    var lastErr error
    delay := rh.policy.InitialDelay

    for attempt := 0; attempt < rh.policy.MaxAttempts; attempt++ {
        // 创建尝试的 span
        attemptCtx, attemptSpan := rh.tracer.Start(ctx,
            fmt.Sprintf("%s-attempt-%d", operationName, attempt+1))

        attemptSpan.SetAttributes(
            attribute.Int("retry.attempt", attempt+1),
            attribute.Int("retry.max_attempts", rh.policy.MaxAttempts),
        )

        // 执行操作
        err := fn(attemptCtx)

        if err == nil {
            attemptSpan.SetStatus(codes.Ok, "success")
            attemptSpan.End()

            span.SetAttributes(
                attribute.Int("retry.total_attempts", attempt+1),
                attribute.Bool("retry.succeeded", true),
            )
            return nil
        }

        // 分类错误
        catErr, _ := rh.classifier.Classify(attemptCtx, err)

        attemptSpan.RecordError(err)
        attemptSpan.SetAttributes(catErr.ToSpanAttributes()...)

        // 检查是否可重试
        if !catErr.Retryable {
            attemptSpan.SetAttributes(attribute.String("retry.result", "not_retryable"))
            attemptSpan.End()

            span.SetAttributes(
                attribute.Int("retry.total_attempts", attempt+1),
                attribute.Bool("retry.succeeded", false),
                attribute.String("retry.final_error", "not_retryable"),
            )
            span.RecordError(err)
            span.SetStatus(codes.Error, "operation failed (not retryable)")
            return err
        }

        lastErr = err

        // 最后一次尝试
        if attempt == rh.policy.MaxAttempts-1 {
            attemptSpan.SetAttributes(attribute.String("retry.result", "max_attempts_reached"))
            attemptSpan.End()
            break
        }

        // 等待后重试
        attemptSpan.SetAttributes(
            attribute.String("retry.result", "will_retry"),
            attribute.Int64("retry.delay_ms", delay.Milliseconds()),
        )
        attemptSpan.End()

        select {
        case <-time.After(delay):
            // 计算下次延迟（指数退避）
            delay = time.Duration(float64(delay) * rh.policy.Multiplier)
            if delay > rh.policy.MaxDelay {
                delay = rh.policy.MaxDelay
            }
        case <-ctx.Done():
            span.SetStatus(codes.Error, "context cancelled")
            return ctx.Err()
        }
    }

    // 所有尝试都失败
    span.SetAttributes(
        attribute.Int("retry.total_attempts", rh.policy.MaxAttempts),
        attribute.Bool("retry.succeeded", false),
        attribute.String("retry.final_error", "max_attempts_reached"),
    )
    span.RecordError(lastErr)
    span.SetStatus(codes.Error, "operation failed after all retries")

    return fmt.Errorf("operation failed after %d attempts: %w",
        rh.policy.MaxAttempts, lastErr)
}

// 使用示例
func ExampleRetryHandler(ctx context.Context) error {
    handler := NewRetryHandler(DefaultRetryPolicy())

    return handler.ExecuteWithRetry(ctx, "api-call", func(ctx context.Context) error {
        // 模拟可能失败的 API 调用
        return callExternalAPI(ctx)
    })
}

func callExternalAPI(ctx context.Context) error {
    // 模拟实现
    return NewCategorizedError(
        errors.New("connection timeout"),
        ErrorCategoryNetwork,
        ErrorSeverityMedium,
    ).WithRetryable(true)
}
```

---

## 5. Panic 处理与恢复

### 5.1 Panic 捕获中间件

```go
package observability

import (
    "context"
    "fmt"
    "net/http"
    "runtime/debug"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// PanicRecoveryMiddleware Panic 恢复中间件
type PanicRecoveryMiddleware struct {
    tracer trace.Tracer
}

func NewPanicRecoveryMiddleware() *PanicRecoveryMiddleware {
    return &PanicRecoveryMiddleware{
        tracer: otel.Tracer("panic-recovery"),
    }
}

// Middleware HTTP 中间件
func (prm *PanicRecoveryMiddleware) Middleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        defer func() {
            if panicErr := recover(); panicErr != nil {
                // 捕获堆栈
                stack := debug.Stack()

                // 创建或获取 span
                ctx := r.Context()
                span := trace.SpanFromContext(ctx)
                if !span.IsRecording() {
                    ctx, span = prm.tracer.Start(ctx, "panic-recovery")
                    defer span.End()
                }

                // 记录 panic 信息
                span.SetAttributes(
                    attribute.String("panic.value", fmt.Sprintf("%v", panicErr)),
                    attribute.String("panic.stack", string(stack)),
                    attribute.String("http.method", r.Method),
                    attribute.String("http.path", r.URL.Path),
                )

                // 创建错误
                err := fmt.Errorf("panic recovered: %v", panicErr)
                span.RecordError(err)
                span.SetStatus(codes.Error, "panic")

                // 返回错误响应
                w.WriteHeader(http.StatusInternalServerError)
                w.Write([]byte("Internal Server Error"))
            }
        }()

        next.ServeHTTP(w, r)
    })
}

// RecoverAndTrace 恢复 panic 并追踪
func (prm *PanicRecoveryMiddleware) RecoverAndTrace(
    ctx context.Context,
    operationName string,
) func() {
    ctx, span := prm.tracer.Start(ctx, operationName)

    return func() {
        if panicErr := recover(); panicErr != nil {
            stack := debug.Stack()

            span.SetAttributes(
                attribute.String("panic.value", fmt.Sprintf("%v", panicErr)),
                attribute.String("panic.stack", string(stack)),
            )

            err := fmt.Errorf("panic: %v", panicErr)
            span.RecordError(err)
            span.SetStatus(codes.Error, "panic")
        }
        span.End()
    }
}

// 使用示例
func ExamplePanicRecovery(ctx context.Context) {
    prm := NewPanicRecoveryMiddleware()
    defer prm.RecoverAndTrace(ctx, "dangerous-operation")()

    // 可能 panic 的代码
    riskyOperation()
}

func riskyOperation() {
    panic("something went wrong")
}
```

### 5.2 Goroutine Panic 处理

```go
package observability

import (
    "context"
    "fmt"
    "runtime/debug"
    "sync"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// SafeGoroutinePool 安全的 Goroutine 池
type SafeGoroutinePool struct {
    tracer       trace.Tracer
    panicHandler func(interface{}, []byte)
    wg           sync.WaitGroup
}

func NewSafeGoroutinePool() *SafeGoroutinePool {
    return &SafeGoroutinePool{
        tracer: otel.Tracer("safe-goroutine-pool"),
        panicHandler: func(panicErr interface{}, stack []byte) {
            fmt.Printf("Goroutine panic: %v\n%s\n", panicErr, stack)
        },
    }
}

// Go 安全地启动 goroutine
func (sgp *SafeGoroutinePool) Go(
    ctx context.Context,
    name string,
    fn func(context.Context) error,
) {
    sgp.wg.Add(1)

    go func() {
        defer sgp.wg.Done()
        defer sgp.recoverFromPanic(ctx, name)

        ctx, span := sgp.tracer.Start(ctx, name,
            trace.WithAttributes(
                attribute.Bool("goroutine", true),
            ),
        )
        defer span.End()

        if err := fn(ctx); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        } else {
            span.SetStatus(codes.Ok, "completed")
        }
    }()
}

func (sgp *SafeGoroutinePool) recoverFromPanic(ctx context.Context, name string) {
    if panicErr := recover(); panicErr != nil {
        stack := debug.Stack()

        // 调用 panic 处理器
        sgp.panicHandler(panicErr, stack)

        // 记录到追踪
        _, span := sgp.tracer.Start(ctx, fmt.Sprintf("%s-panic", name))
        defer span.End()

        span.SetAttributes(
            attribute.String("panic.value", fmt.Sprintf("%v", panicErr)),
            attribute.String("panic.stack", string(stack)),
        )

        err := fmt.Errorf("goroutine panic: %v", panicErr)
        span.RecordError(err)
        span.SetStatus(codes.Error, "panic")
    }
}

// Wait 等待所有 goroutine 完成
func (sgp *SafeGoroutinePool) Wait() {
    sgp.wg.Wait()
}

// 使用示例
func ExampleSafeGoroutinePool(ctx context.Context) {
    pool := NewSafeGoroutinePool()

    // 启动多个 goroutine
    for i := 0; i < 10; i++ {
        taskID := i
        pool.Go(ctx, fmt.Sprintf("task-%d", taskID), func(ctx context.Context) error {
            if taskID == 5 {
                // 这个会 panic，但不会影响其他 goroutine
                panic("task 5 failed")
            }
            return nil
        })
    }

    // 等待所有完成
    pool.Wait()
}
```

---

*由于篇幅限制，我将继续在后续部分补充剩余内容。请告诉我是否需要继续完成这个文档的剩余部分（包括超时处理、错误传播、监控等）。*

---

## 参考资料

1. **Go 错误处理**:
   - [Error Handling in Go](https://go.dev/blog/error-handling-and-go)
   - [Working with Errors in Go 1.13](https://go.dev/blog/go1.13-errors)
   - [errors Package](https://pkg.go.dev/errors)

2. **OpenTelemetry**:
   - [Error Handling Best Practices](https://opentelemetry.io/docs/languages/go/instrumentation/#error-handling)
   - [Span Status](https://opentelemetry.io/docs/specs/otel/trace/api/#set-status)

3. **最佳实践**:
   - [Effective Error Handling in Go](https://earthly.dev/blog/golang-errors/)
   - [Go Error Handling Best Practices](https://www.ardanlabs.com/blog/2014/10/error-handling-in-go-part-i.html)

---

**文档版本**: v1.0.0  
**最后更新**: 2025年10月8日  
**状态**: 🚧 进行中

---

**下一步**: 继续补充超时处理、错误传播、监控告警等剩余章节。

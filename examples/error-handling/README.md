# Go 错误处理与 OTLP 集成示例

本示例演示了 Go 语言的高级错误处理模式与 OpenTelemetry 的深度集成。

## 🎯 功能特性

### 1. 自定义错误类型

实现可追踪的错误类型,包含分类、操作、时间戳等元数据:

```go
type TracedError struct {
    Category   ErrorCategory
    Operation  string
    Message    string
    Underlying error
    Timestamp  time.Time
}

err := NewTracedError(ErrCategoryDatabase, "query", "database query failed", baseErr)
err.RecordToSpan(span) // 自动记录到 Span
```

### 2. errors.Join 多错误收集

使用 Go 1.20+ 的 `errors.Join` 合并多个错误:

```go
collector := &MultiOperationError{}
collector.Add(err1)
collector.Add(err2)
collector.Add(err3)

if joinedErr := collector.Join(); joinedErr != nil {
    span.RecordError(joinedErr)
    // 处理合并后的错误
}
```

### 3. 错误链分析

遍历和分析错误链:

```go
currentErr := error(serviceErr)
depth := 0
for currentErr != nil {
    var tracedErr *TracedError
    if errors.As(currentErr, &tracedErr) {
        // 处理 TracedError
    }
    currentErr = errors.Unwrap(currentErr)
    depth++
}
```

### 4. 重试机制与指数退避

实现带追踪的重试机制:

```go
err := RetryWithBackoff(ctx, tracer, RetryConfig{
    MaxAttempts:  5,
    InitialDelay: 100 * time.Millisecond,
    MaxDelay:     5 * time.Second,
    Multiplier:   2.0,
}, func() error {
    return riskyOperation()
})
```

特性:
- ✅ 指数退避
- ✅ 随机抖动 (±25%)
- ✅ 最大延迟限制
- ✅ 每次尝试都创建独立 Span

### 5. Panic 恢复与追踪

安全执行操作并追踪 panic:

```go
err := SafeOperation(ctx, tracer, "risky-operation", func() error {
    // 可能会 panic 的代码
    panic("something went wrong")
})
// Panic 会被捕获并记录到追踪
```

### 6. 错误分类

自动分类错误:

```go
classifier := &ErrorClassifier{tracer: tracer}
category := classifier.Classify(ctx, err)
// 返回: ErrCategoryNetwork, ErrCategoryDatabase, ErrCategoryValidation 等
```

## 🚀 运行示例

### 前置要求

- Go 1.25.1 或更高版本

### 运行

```bash
cd examples/error-handling
go run main.go
```

### 预期输出

```text
================================================================================
🚀 Error Handling with OTLP Demo
================================================================================

--- errors.Join Demo ---
❌ 3 operations failed:
[business] validate-input: validate-input failed
[business] query-database: query-database failed
[business] send-notification: send-notification failed

--- Error Chain Analysis Demo ---
📋 Error chain analysis:
  Top error: [network] initialize: service initialization failed (caused by: [database] connect: failed to connect to database (caused by: connection refused))
  [Depth 0] [network] initialize: service initialization failed (caused by: [database] connect: failed to connect to database (caused by: connection refused))
  [Depth 1] [database] connect: failed to connect to database (caused by: connection refused)
  [Depth 2] connection refused
  Total depth: 3

--- Retry with Exponential Backoff Demo ---
⚠️  Attempt 1 failed: temporary failure (attempt 1)
⏳ Waiting 112ms before retry...
⚠️  Attempt 2 failed: temporary failure (attempt 2)
⏳ Waiting 187ms before retry...
⚠️  Attempt 3 failed: temporary failure (attempt 3)
⏳ Waiting 401ms before retry...
✅ Operation succeeded on attempt 4
✅ Operation succeeded after retries

--- Panic Recovery Demo ---
✅ Normal operation completed
🚨 Panic recovered: something went terribly wrong!
✅ Panic was caught and traced

--- Error Classification Demo ---
  [1] Error: connection timeout -> Category: network
  [2] Error: [database] query: database query failed -> Category: database
  [3] Error: invalid input format -> Category: validation
  [4] Error: business logic violation -> Category: business

================================================================================
✅ All demos completed successfully
================================================================================
```

## 📖 相关文档

- [13_Go错误处理与OTLP集成](../../标准深度梳理_2025_10/00_Go完整集成指南/13_Go错误处理与OTLP集成.md)

## 💡 最佳实践

### 错误包装

```go
// ✅ 好: 使用 %w 包装错误,保留错误链
return fmt.Errorf("failed to process data: %w", err)

// ❌ 坏: 使用 %v,丢失错误链
return fmt.Errorf("failed to process data: %v", err)
```

### 错误检查

```go
// ✅ 好: 使用 errors.Is 检查特定错误
if errors.Is(err, context.DeadlineExceeded) {
    // 处理超时
}

// ✅ 好: 使用 errors.As 检查错误类型
var tracedErr *TracedError
if errors.As(err, &tracedErr) {
    // 处理 TracedError
}
```

### Span 错误记录

```go
// ✅ 好: 记录错误并设置状态
span.RecordError(err)
span.SetStatus(codes.Error, err.Error())

// ✅ 更好: 添加额外属性
span.RecordError(err)
span.SetStatus(codes.Error, "Operation failed")
span.SetAttributes(
    attribute.String("error.category", "database"),
    attribute.String("error.operation", "query"),
)
```

### 重试策略

```go
// ✅ 好: 使用指数退避 + 随机抖动
RetryConfig{
    MaxAttempts:  5,
    InitialDelay: 100 * time.Millisecond,
    MaxDelay:     5 * time.Second,
    Multiplier:   2.0, // 指数因子
}
// 实际延迟: 100ms, 200ms, 400ms, 800ms, 1600ms (带抖动)
```

### Panic 处理

```go
// ✅ 好: 使用 defer + recover 捕获 panic
defer func() {
    if r := recover(); r != nil {
        span.RecordError(fmt.Errorf("panic: %v", r))
        // 记录堆栈信息
    }
}()
```

## 🎓 学习目标

完成本示例后,你将学会:

- ✅ 设计可追踪的自定义错误类型
- ✅ 使用 errors.Join 合并多个错误
- ✅ 分析和遍历错误链
- ✅ 实现带追踪的重试机制
- ✅ 捕获和追踪 panic
- ✅ 错误分类与结构化处理

## 🔗 相关示例

- [go125-features/](../go125-features/) - Go 1.25.1 新特性
- [advanced-context/](../advanced-context/) - Context 高级模式
- [resilience/retry/](../resilience/retry/) - 弹性重试模式

## 📊 性能考虑

### 错误创建开销

```go
// 低开销: 简单错误
err := errors.New("simple error")

// 中等开销: 包装错误
err := fmt.Errorf("wrapped: %w", baseErr)

// 高开销: 自定义错误 + 堆栈追踪
err := NewTracedError(category, op, msg, baseErr)
```

### 建议

- ✅ 关键路径使用简单错误
- ✅ 边界处使用包装错误
- ✅ 错误处理点使用自定义错误
- ✅ 避免在热路径捕获堆栈


# Go 1.25.1 新特性与 OTLP 集成示例

本示例演示了 Go 1.25.1 的最新特性如何与 OpenTelemetry 集成。

## 🎯 功能特性

### 1. 泛型 (Generics)

- **泛型 Tracer 包装器**: 类型安全的追踪操作
- **泛型 Exporter**: 通用导出器接口
- **泛型结果类型**: 统一的返回值处理

```go
genericTracer := NewGenericTracer[string](tracer)
result := genericTracer.Trace(ctx, "operation", func(ctx context.Context) (string, error) {
    return "success", nil
})
```

### 2. Context 增强功能

#### WithoutCancel

分离后台任务,即使父 Context 被取消,后台任务仍继续执行:

```go
backgroundCtx := context.WithoutCancel(parentCtx)
go func() {
    // 后台任务不受父 Context 取消影响
    _, span := tracer.Start(backgroundCtx, "background-task")
    defer span.End()
    // ...
}()
```

#### WithDeadlineCause

设置带原因的超时,便于追踪 SLA 违规:

```go
slaViolation := errors.New("SLA violation: response time > 100ms")
ctx, cancel := context.WithDeadlineCause(ctx, deadline, slaViolation)

// 检查超时原因
if ctx.Err() != nil {
    cause := context.Cause(ctx) // 获取具体原因
    span.RecordError(cause)
}
```

#### AfterFunc

Context 取消时自动执行清理函数:

```go
ctx, cancel := context.WithCancel(parentCtx)
stop := context.AfterFunc(ctx, func() {
    // 自动清理逻辑
    log.Println("Auto cleanup triggered")
})
defer stop()
```

### 3. 新并发原语

#### sync.OnceFunc

确保函数只执行一次:

```go
initTracer := sync.OnceFunc(func() {
    log.Println("Initializing tracer (called once)")
})

// 多次调用,只执行一次
initTracer()
initTracer()
```

#### sync.OnceValue

确保值只计算一次:

```go
getExpensiveValue := sync.OnceValue(func() string {
    // 昂贵的计算
    return "result"
})

// 多次调用,只计算一次
value := getExpensiveValue()
```

#### sync.OnceValues

返回多个值,只计算一次:

```go
getConfig := sync.OnceValues(func() (string, int) {
    return "production", 8080
})

env, port := getConfig()
```

### 4. errors.Join

合并多个错误:

```go
var errs []error
// 收集多个操作的错误
errs = append(errs, err1, err2, err3)

// 合并所有错误
combinedErr := errors.Join(errs...)
span.RecordError(combinedErr)
```

## 🚀 运行示例

### 前置要求

- Go 1.25.1 或更高版本

### 运行

```bash
cd examples/go125-features
go run main.go
```

### 预期输出

```text
================================================================================
🚀 Go 1.25.1 Features with OTLP Demo
================================================================================

--- 1. Generic Tracer Demo ---
✅ Generic tracer result: success

--- 2. Context Enhancements ---
✅ Background task completed (not affected by parent cancellation)
⚠️  Timeout cause: SLA violation: response time > 100ms
🧹 Auto cleanup triggered

--- 3. New Concurrency Primitives ---
🔧 Initializing tracer (called once)
💰 Computing expensive value (called once)
📦 Got value: expensive-result (call 1)
📦 Got value: expensive-result (call 2)
📦 Got value: expensive-result (call 3)
⚙️  Loading configuration (called once)
🌍 Config: env=production, port=8080 (call 1)
🌍 Config: env=production, port=8080 (call 2)
🌍 Config: env=production, port=8080 (call 3)

--- 4. errors.Join Demo ---
❌ Multiple errors occurred:
database-query failed: connection timeout
cache-read failed: cache miss
api-call failed: rate limit exceeded

--- 5. Generic Exporter Demo ---
📤 Exporting 3 items of type string
  [0]: trace-1
  [1]: trace-2
  [2]: trace-3
📤 Exporting 3 items of type int
  [0]: 100
  [1]: 200
  [2]: 300
📤 Exporting 2 items of type main.MetricData
  [0]: {Name:cpu.usage Value:45.2}
  [1]: {Name:memory.used Value:1024.5}

================================================================================
✅ All demos completed successfully
================================================================================
```

## 📖 相关文档

- [12_Go_1.25.1新特性完整应用指南](../../标准深度梳理_2025_10/00_Go完整集成指南/12_Go_1.25.1新特性完整应用指南.md)

## 💡 最佳实践

1. **使用泛型**: 提高代码复用性和类型安全
2. **WithoutCancel**: 用于后台任务,如日志刷新、指标上报
3. **WithDeadlineCause**: 用于 SLA 监控和超时分析
4. **AfterFunc**: 用于资源自动清理
5. **sync.Once***: 用于单次初始化,避免锁竞争
6. **errors.Join**: 用于批处理错误收集

## 🎓 学习目标

完成本示例后,你将学会:

- ✅ 使用泛型设计类型安全的 OTLP 组件
- ✅ 应用 Context 增强功能优化追踪
- ✅ 使用新并发原语提高性能
- ✅ 合并和追踪多个错误
- ✅ 设计泛型导出器接口

## 🔗 相关示例

- [error-handling/](../error-handling/) - 错误处理进阶
- [advanced-context/](../advanced-context/) - Context 高级模式
- [memory-optimization/](../memory-optimization/) - 内存优化

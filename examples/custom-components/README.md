# 自定义 OTLP 组件示例

本示例演示如何实现自定义的 OpenTelemetry 组件,包括 Exporter、Processor 和 Sampler。

## 🎯 功能特性

### 1. 自定义 Exporter

实现文件导出器:

```go
type FileExporter struct {
    mu       sync.Mutex
    spans    []sdktrace.ReadOnlySpan
    maxSpans int
}

exporter := NewFileExporter(20)
```

**特点**:

- ✅ 缓冲 Span 到内存
- ✅ 达到阈值自动刷新
- ✅ 打印详细的 Span 信息
- ✅ 线程安全

### 2. 过滤 Processor

过滤不需要的 Span:

```go
filterProcessor := NewFilterProcessor(
    next,
    func(span sdktrace.ReadOnlySpan) bool {
        // 只保留错误状态的 Span
        return span.Status().Code == codes.Error
    },
)
```

**用途**:

- ✅ 过滤低价值 Span
- ✅ 减少存储成本
- ✅ 统计过滤率
- ✅ 灵活的过滤规则

### 3. 数据脱敏 Processor

自动脱敏敏感数据:

```go
sanitizeProcessor := NewSanitizeProcessor(
    next,
    []string{"password", "credit_card", "ssn", "api_key"},
)

// 使用
span.SetAttributes(
    attribute.String("username", "alice"),
    attribute.String("password", "secret123"), // 将被替换为 "***REDACTED***"
)
```

**特点**:

- ✅ 自动检测敏感属性
- ✅ 替换为脱敏值
- ✅ 支持自定义敏感键
- ✅ 统计脱敏次数

### 4. 动态采样器

运行时动态调整采样率:

```go
sampler := NewDynamicSampler(0.5) // 50% 采样率

// 动态调整
sampler.SetRate(0.8) // 调整到 80%

// 获取统计
total, sampled, rate := sampler.GetStats()
```

**优势**:

- ✅ 运行时动态调整
- ✅ 基于 TraceID 采样
- ✅ 线程安全
- ✅ 实时统计

### 5. 基于规则的采样器

按 Span 名称模式采样:

```go
sampler := NewRuleBasedSampler([]SamplingRule{
    {NamePattern: "error", Rate: 1.0, Priority: 1},      // 100% 采样错误
    {NamePattern: "slow", Rate: 1.0, Priority: 2},       // 100% 采样慢请求
    {NamePattern: "healthcheck", Rate: 0.01, Priority: 3}, // 1% 采样健康检查
})
```

**特点**:

- ✅ 基于名称模式匹配
- ✅ 每个规则独立采样率
- ✅ 优先级支持
- ✅ 灵活的规则配置

## 🚀 运行示例

### 前置要求

- Go 1.25.1 或更高版本

### 运行

```bash
cd examples/custom-components
go run main.go
```

### 预期输出

```text
================================================================================
🚀 Custom Components Demo
================================================================================

--- Custom Exporter Demo ---
📤 Exporting 1 spans to file
  [12345678] operation-0 (Duration: 10ms)
    iteration: 0
    type: demo
📤 Exporting 1 spans to file
  [23456789] operation-1 (Duration: 10ms)
    iteration: 1
    type: demo
...
✅ Custom exporter demo completed

--- Filter Processor Demo ---
🚫 Filtered span: normal-operation
📤 Exporting 1 spans to file
  [34567890] error-operation (Duration: 1ms)
🚫 Filtered span: slow-operation
📤 Exporting 1 spans to file
  [45678901] failed-operation (Duration: 1ms)
✅ Filter processor demo completed

--- Sanitize Processor Demo ---
🔒 Sanitized attribute: password
🔒 Sanitized attribute: credit_card
📤 Exporting 1 spans to file
  [56789012] user-login (Duration: 1ms)
    username: alice
    password: ***REDACTED***
    email: alice@example.com
    credit_card: ***REDACTED***
✅ Sanitize processor demo completed

--- Dynamic Sampler Demo ---
📊 Sampler stats - Total: 100, Sampled: 48, Rate: 0.50, Actual: 0.48

--- Adjusting Sampling Rate ---
📊 Sampling rate updated to 0.80
📊 Updated sampler stats - Total: 150, Sampled: 88, Rate: 0.80, Actual: 0.59

📊 Filter stats - Processed: 110, Filtered: 2, Passed: 108
🔒 Sanitized 2 attributes
🔄 Shutting down FileExporter, exported 108 spans

================================================================================
✅ All demos completed successfully
================================================================================
```

## 📖 相关文档

- [16_Go接口与抽象层设计模式](../../标准深度梳理_2025_10/00_Go完整集成指南/16_Go接口与抽象层设计模式.md)

## 💡 最佳实践

### 自定义 Exporter

```go
// ✅ 好: 实现必需的接口方法
type CustomExporter struct{}

func (e *CustomExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
    // 导出逻辑
    return nil
}

func (e *CustomExporter) Shutdown(ctx context.Context) error {
    // 清理资源
    return nil
}

// ✅ 好: 使用批处理
type BatchExporter struct {
    buffer []sdktrace.ReadOnlySpan
    batchSize int
}
```

### 自定义 Processor

```go
// ✅ 好: 实现完整接口
type CustomProcessor struct {
    next sdktrace.SpanProcessor
}

func (p *CustomProcessor) OnStart(ctx context.Context, s sdktrace.ReadWriteSpan) {
    // 在 Span 开始时处理
    p.next.OnStart(ctx, s)
}

func (p *CustomProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
    // 在 Span 结束时处理
    p.next.OnEnd(s)
}

func (p *CustomProcessor) Shutdown(ctx context.Context) error {
    return p.next.Shutdown(ctx)
}

func (p *CustomProcessor) ForceFlush(ctx context.Context) error {
    return p.next.ForceFlush(ctx)
}
```

### 自定义 Sampler

```go
// ✅ 好: 基于 TraceID 采样(一致性)
func (s *CustomSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    traceID := params.TraceID
    // 使用 TraceID 确保同一 Trace 的所有 Span 采样决策一致
    // ...
}

// ❌ 坏: 基于随机数(不一致)
func (s *BadSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    if rand.Float64() < 0.5 {  // 每次调用结果可能不同
        return sdktrace.RecordAndSample
    }
    return sdktrace.Drop
}
```

### 线程安全

```go
// ✅ 好: 使用互斥锁保护共享状态
type SafeExporter struct {
    mu    sync.Mutex
    count int
}

func (e *SafeExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
    e.mu.Lock()
    defer e.mu.Unlock()
    
    e.count += len(spans)
    return nil
}

// ✅ 更好: 使用读写锁(读多写少)
type RWExporter struct {
    mu    sync.RWMutex
    count int
}

func (e *RWExporter) GetCount() int {
    e.mu.RLock()
    defer e.mu.RUnlock()
    return e.count
}
```

## 🎓 学习目标

完成本示例后,你将学会:

- ✅ 实现自定义 Exporter 导出到任意目标
- ✅ 创建 Processor 过滤和处理 Span
- ✅ 实现数据脱敏保护敏感信息
- ✅ 设计动态采样器优化性能
- ✅ 使用规则引擎灵活控制采样

## 🔗 相关示例

- [go125-features/](../go125-features/) - Go 1.25.1 新特性
- [memory-optimization/](../memory-optimization/) - 内存优化
- [error-handling/](../error-handling/) - 错误处理

## 📊 性能考虑

### Processor 性能

```go
// ✅ 高性能: 最小化锁持有时间
func (p *FastProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
    // 快速检查
    if !p.shouldProcess(s) {
        return
    }
    
    // 只在必要时加锁
    p.mu.Lock()
    p.buffer = append(p.buffer, s)
    p.mu.Unlock()
}

// ❌ 低性能: 长时间持锁
func (p *SlowProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
    p.mu.Lock()
    defer p.mu.Unlock()
    
    // 耗时操作在锁内执行
    p.doExpensiveWork(s)
}
```

### Sampler 性能

```go
// ✅ 高性能: O(1) 时间复杂度
func (s *FastSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 简单的阈值比较
    return sdktrace.SamplingResult{
        Decision: sdktrace.RecordAndSample,
    }
}

// ❌ 低性能: O(n) 时间复杂度
func (s *SlowSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 遍历大量规则
    for _, rule := range s.manyRules { // 可能有数千条规则
        if rule.Match(params) {
            return rule.Decision
        }
    }
    return sdktrace.Drop
}
```

## ⚠️ 注意事项

### 资源清理

```go
// ✅ 好: 在 Shutdown 中清理资源
func (e *CustomExporter) Shutdown(ctx context.Context) error {
    e.mu.Lock()
    defer e.mu.Unlock()
    
    // 关闭连接
    if e.conn != nil {
        e.conn.Close()
    }
    
    // 清空缓冲区
    e.buffer = nil
    
    return nil
}
```

### 错误处理

```go
// ✅ 好: 记录错误但不中断
func (e *ResilientExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
    for _, span := range spans {
        if err := e.exportOne(span); err != nil {
            // 记录错误,继续处理
            log.Printf("Failed to export span: %v", err)
            continue
        }
    }
    return nil
}
```

### 采样一致性

```go
// ✅ 好: 基于 TraceID 确保一致性
func (s *ConsistentSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 同一个 Trace 的所有 Span 都使用相同的 TraceID
    traceID := params.TraceID
    // ... 基于 traceID 的采样逻辑
}
```

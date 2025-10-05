# 自定义处理器示例

演示如何实现自定义 SpanProcessor 进行数据处理和过滤。

## SpanProcessor 接口

```go
type SpanProcessor interface {
    OnStart(parent context.Context, s ReadWriteSpan)
    OnEnd(s ReadOnlySpan)
    Shutdown(ctx context.Context) error
    ForceFlush(ctx context.Context) error
}
```

## 运行示例

```bash
go run main.go
```

## 输出示例

```text
[MyProcessor] Span started: fast-operation
[MyProcessor] Span ended: fast-operation (duration: 10ms)

[MyProcessor] Span started: slow-operation
[MyProcessor] Span ended: slow-operation (duration: 150ms)
[MyProcessor] ⚠️  SLOW SPAN: slow-operation took 150ms

[MyProcessor] Span started: error-operation
[MyProcessor] Span ended: error-operation (duration: 20ms)
[MyProcessor] ❌ ERROR SPAN: error-operation

=== Metrics Summary ===
Total Spans: 13
Error Spans: 1
Average Latency: 25ms
Error Rate: 7.69%
```

## 使用场景

### 1. 数据过滤

```go
func (p *CustomProcessor) OnStart(parent context.Context, s ReadWriteSpan) {
    // 过滤敏感信息
    p.filterSensitiveData(s)
}
```

### 2. 性能监控

```go
func (p *CustomProcessor) OnEnd(s ReadOnlySpan) {
    duration := s.EndTime().Sub(s.StartTime())
    if duration > threshold {
        log.Printf("Slow span detected: %s", s.Name())
    }
}
```

### 3. 指标收集

```go
type MetricsProcessor struct {
    spanCount  int64
    errorCount int64
}
```

### 4. 数据增强

```go
func (p *CustomProcessor) OnStart(parent context.Context, s ReadWriteSpan) {
    s.SetAttributes(
        attribute.String("environment", "production"),
        attribute.String("version", "1.0.0"),
    )
}
```

## 最佳实践

1. **性能优化**: 避免在 OnStart/OnEnd 中执行耗时操作
2. **错误处理**: 确保处理器不会抛出异常
3. **资源管理**: 在 Shutdown 中清理资源
4. **并发安全**: 使用互斥锁保护共享状态

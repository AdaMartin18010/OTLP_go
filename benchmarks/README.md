# 性能基准测试

本目录包含 OTLP_go 的性能基准测试，用于评估追踪系统的性能开销。

## 测试类别

### Span 性能测试 (`span_test.go`)

- **SpanCreation**: 基础 Span 创建
- **SpanWithAttributes**: 带属性的 Span
- **SpanWithEvents**: 带事件的 Span
- **NestedSpans**: 嵌套 Span
- **ConcurrentSpans**: 并发 Span 创建
- **SpanSetAttributes**: 设置属性性能
- **SpanWithSampling**: 不同采样率的性能

### 导出性能测试 (`export_test.go`)

- **BatchExport**: 不同批量大小的导出性能
- **ExportWithAttributes**: 不同属性数量的导出性能
- **ExportWithEvents**: 不同事件数量的导出性能
- **ConcurrentExport**: 并发导出性能
- **ExportLatency**: 导出延迟测试
- **MemoryUsage**: 内存使用测试

## 运行基准测试

### 运行所有测试

```bash
go test -bench=. -benchmem
```

### 运行特定测试

```bash
# Span 创建测试
go test -bench=BenchmarkSpanCreation -benchmem

# 批量导出测试
go test -bench=BenchmarkBatchExport -benchmem

# 并发测试
go test -bench=Concurrent -benchmem
```

### 生成性能报告

```bash
# 生成 CPU profile
go test -bench=. -cpuprofile=cpu.prof

# 生成内存 profile
go test -bench=. -memprofile=mem.prof

# 分析 profile
go tool pprof cpu.prof
```

## 性能目标

### Span 创建性能

| 操作 | 目标 | 内存分配 |
|-----|------|---------|
| 基础 Span | < 500 ns/op | < 200 B/op |
| 带属性 Span | < 1000 ns/op | < 500 B/op |
| 嵌套 Span (3层) | < 2000 ns/op | < 1000 B/op |

### 导出性能

| 批量大小 | 吞吐量 | 延迟 |
|---------|-------|------|
| 100 | 10,000 spans/s | < 10ms |
| 512 | 50,000 spans/s | < 20ms |
| 1024 | 100,000 spans/s | < 50ms |

### 并发性能

- **目标**: 支持 10,000+ 并发 Goroutine
- **内存**: < 100MB (10,000 spans)
- **CPU**: < 5% 开销

## 示例输出

```text
BenchmarkSpanCreation-8                 2000000    450 ns/op    180 B/op    3 allocs/op
BenchmarkSpanWithAttributes-8           1000000    850 ns/op    420 B/op    6 allocs/op
BenchmarkNestedSpans-8                   500000   1800 ns/op    950 B/op   12 allocs/op
BenchmarkConcurrentSpans-8              5000000    320 ns/op    180 B/op    3 allocs/op
BenchmarkBatchExport/512-8              1000000   2500 ns/op    800 B/op   10 allocs/op
BenchmarkConcurrentExport-8             3000000    400 ns/op    250 B/op    5 allocs/op
```

## 性能优化建议

### 1. 使用批量导出

```go
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        sdktrace.WithMaxExportBatchSize(512),
        sdktrace.WithBatchTimeout(5 * time.Second),
    ),
)
```

### 2. 合理的采样率

```go
// 生产环境建议 10% 采样
sampler := sdktrace.TraceIDRatioBased(0.1)
```

### 3. 预分配属性

```go
// 避免
span.SetAttributes(attribute.String("key1", "value1"))
span.SetAttributes(attribute.String("key2", "value2"))

// 推荐
span.SetAttributes(
    attribute.String("key1", "value1"),
    attribute.String("key2", "value2"),
)
```

### 4. 使用 Span 池化

参考 [examples/performance/span-pool](../examples/performance/span-pool/)

## 持续监控

### 生产环境指标

```yaml
# Prometheus 指标
- otel_span_creation_duration_seconds
- otel_export_batch_size
- otel_export_duration_seconds
- otel_memory_usage_bytes
```

### 告警规则

```yaml
- alert: HighSpanCreationLatency
  expr: otel_span_creation_duration_seconds > 0.001
  for: 5m

- alert: HighMemoryUsage
  expr: otel_memory_usage_bytes > 100000000
  for: 5m
```

---

**最后更新**: 2025-10-04  
**维护者**: OTLP_go Team

# Span 池化优化示例

演示如何使用对象池减少内存分配和 GC 压力。

## 性能对比

```text
=== Without Pooling ===
Time: 45ms
Allocations: 50,000
Total Allocated: 8,000,000 bytes

=== With Pooling ===
Time: 12ms
Allocations: 2,500
Total Allocated: 400,000 bytes

Performance Improvement:
- Time: 73% faster
- Allocations: 95% reduction
- Memory: 95% reduction
```

## 关键技术

### 1. sync.Pool

```go
pool := sync.Pool{
    New: func() interface{} {
        return &SpanData{
            Attributes: make([]attribute.KeyValue, 0, 16),
        }
    },
}
```

### 2. 对象复用

```go
// Acquire
span := pool.Get().(*SpanData)

// Use
span.Name = "operation"

// Release
span.Reset()
pool.Put(span)
```

### 3. 预分配容量

```go
Attributes: make([]attribute.KeyValue, 0, 16) // 预分配 16 个容量
Events: make([]Event, 0, 8)                    // 预分配 8 个容量
```

## 适用场景

- 高并发场景 (> 10,000 QPS)
- 内存敏感应用
- 需要低 GC 暂停时间
- 微服务架构

## 最佳实践

1. **合理的预分配大小**: 根据实际使用情况调整
2. **及时释放**: 使用完立即归还池
3. **重置状态**: 确保对象被正确清理
4. **监控效果**: 使用 pprof 验证优化效果

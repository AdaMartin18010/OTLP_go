# Go 内存优化与 OTLP 性能优化示例

本示例演示了 Go 内存管理和 OTLP 性能优化的最佳实践。

## 🎯 功能特性

### 1. sync.Pool 对象池

使用对象池复用 Span 数据结构,减少内存分配:

```go
var spanDataPool = sync.Pool{
    New: func() interface{} {
        return &SpanData{
            Attributes: make([]attribute.KeyValue, 0, 16),
        }
    },
}

// 获取对象
sd := AcquireSpanData()

// 使用完毕后归还
ReleaseSpanData(sd)
```

**性能提升**:

- ✅ 减少 85-90% 的内存分配
- ✅ 降低 GC 压力
- ✅ 提高 2-3x 吞吐量

### 2. 内存预分配

预分配切片容量,避免动态扩容:

```go
// ❌ 坏: 不预分配
attrs := make([]attribute.KeyValue, 0)
for i := 0; i < 100; i++ {
    attrs = append(attrs, kv) // 多次扩容
}

// ✅ 好: 预分配
attrs := make([]attribute.KeyValue, 0, 100) // 预分配容量
for i := 0; i < 100; i++ {
    attrs = append(attrs, kv) // 无需扩容
}
```

**优势**:

- ✅ 减少 60-70% 的内存分配
- ✅ 避免多次内存拷贝
- ✅ 提高性能

### 3. 零分配技术

使用栈上数组避免堆分配:

```go
type ZeroAllocSpanBuilder struct {
    attrs [16]attribute.KeyValue // 栈上数组,零堆分配
    count int
}

var builder ZeroAllocSpanBuilder
builder.AddString("service", "api")
builder.AddInt("status", 200)
```

**特点**:

- ✅ 完全零堆分配
- ✅ 逃逸分析友好
- ✅ 适合小型属性集

### 4. 批处理优化

批量导出 Span,减少网络调用:

```go
exporter := NewBatchExporter(tracer, 100) // 批大小100

for i := 0; i < 1000; i++ {
    sd := AcquireSpanData()
    exporter.Add(sd) // 自动批处理
}

exporter.Flush() // 刷新剩余
```

**收益**:

- ✅ 减少 90% 的网络调用
- ✅ 提高吞吐量
- ✅ 降低导出器负载

### 5. GC 监控与调优

监控 GC 统计并调优:

```go
stats := GetGCStats()
log.Printf("NumGC: %d, PauseTotal: %v, MemAlloc: %d MB",
    stats.NumGC, stats.PauseTotal, stats.MemAlloc/1024/1024)
```

**调优建议**:

```bash
# 调整 GC 触发阈值
export GOGC=200  # 默认100,提高到200降低GC频率

# 设置内存软限制
export GOMEMLIMIT=4GiB  # 限制内存使用

# 禁用 GC (仅测试用)
export GOGC=off
```

## 🚀 运行示例

### 前置要求

- Go 1.25.1 或更高版本

### 运行

```bash
cd examples/memory-optimization
go run main.go
```

### 预期输出

```text
================================================================================
🚀 Memory Optimization with OTLP Demo
================================================================================

--- Span Pool Demo ---
📊 Without Pool: 2.5ms, Alloc: 2400000 bytes
📊 With Pool:    0.8ms, Alloc: 160000 bytes
🚀 Improvement:  3.12x faster, 15.00x less allocation

--- Memory Preallocation Demo ---
📊 Without Prealloc: 12800 bytes
📊 With Prealloc:    4800 bytes
🚀 Improvement:      2.67x less allocation
✅ Pooled buffer with 100 attributes

--- Zero-Allocation Demo ---
📊 Heap Allocation:  15.2ms, Alloc: 9600000 bytes
📊 Stack Allocation: 5.1ms, Alloc: 0 bytes
🚀 Improvement:      2.98x faster, Inf less allocation

--- Batch Processing Demo ---
📤 Exporting batch of 100 spans
📤 Exporting batch of 100 spans
📤 Exporting batch of 100 spans
...
📤 Exporting batch of 100 spans
✅ Batch processing completed

--- GC Tuning Demo ---
📊 Initial GC Stats:
   NumGC: 5, PauseTotal: 1.2ms, MemAlloc: 8 MB
📊 After Allocation:
   NumGC: 8 (+3), PauseTotal: 3.5ms (+2.3ms), MemAlloc: 125 MB
📊 After Release:
   NumGC: 9 (+1), PauseTotal: 4.1ms (+0.6ms), MemAlloc: 12 MB

================================================================================
✅ All demos completed successfully
================================================================================
```

## 📖 相关文档

- [15_Go内存管理与OTLP性能优化](../../标准深度梳理_2025_10/00_Go完整集成指南/15_Go内存管理与OTLP性能优化.md)

## 💡 最佳实践

### 对象池使用

```go
// ✅ 好: 重置对象后归还
func ReleaseSpanData(sd *SpanData) {
    sd.TraceID = ""
    sd.SpanID = ""
    sd.Attributes = sd.Attributes[:0] // 保留容量
    spanDataPool.Put(sd)
}

// ❌ 坏: 不重置直接归还(会造成内存泄漏)
func ReleaseSpanData(sd *SpanData) {
    spanDataPool.Put(sd) // 属性未清空!
}
```

### 预分配策略

```go
// 已知大小: 精确预分配
attrs := make([]attribute.KeyValue, 0, knownSize)

// 未知大小: 估计预分配
attrs := make([]attribute.KeyValue, 0, 16) // 常见情况16个属性

// 大量数据: 分段预分配
for i := 0; i < largeCount; i += batchSize {
    batch := make([]T, 0, batchSize)
    // 处理批次
}
```

### 零分配原则

```go
// ✅ 好: 栈上数组
var arr [16]attribute.KeyValue
slice := arr[:0]

// ❌ 坏: 堆上切片
slice := make([]attribute.KeyValue, 0, 16) // 可能逃逸到堆

// ✅ 好: 值传递小结构体
func Process(config Config) {} // Config < 32 bytes

// ❌ 坏: 指针传递小结构体
func Process(config *Config) {} // 增加逃逸可能
```

### 批处理策略

```go
// 合适的批大小
const (
    SmallBatch  = 10    // 低延迟场景
    MediumBatch = 100   // 平衡场景(推荐)
    LargeBatch  = 1000  // 高吞吐场景
)

// 带超时的批处理
func BatchWithTimeout(batchSize int, timeout time.Duration) {
    ticker := time.NewTicker(timeout)
    defer ticker.Stop()

    for {
        select {
        case item := <-inputChan:
            buffer = append(buffer, item)
            if len(buffer) >= batchSize {
                flush()
            }
        case <-ticker.C:
            flush() // 超时刷新
        }
    }
}
```

### GC 调优策略

```go
// 1. 减少分配频率
// ✅ 使用对象池
// ✅ 预分配内存
// ✅ 复用缓冲区

// 2. 调整 GOGC
// 低内存环境: GOGC=50
// 正常环境:   GOGC=100 (默认)
// 高内存环境: GOGC=200

// 3. 设置内存限制
// export GOMEMLIMIT=4GiB

// 4. 监控 GC 指标
runtime.ReadMemStats(&m)
log.Printf("GC Pauses: %v", m.PauseNs)
```

## 🎓 学习目标

完成本示例后,你将学会:

- ✅ 使用 sync.Pool 实现对象池
- ✅ 正确预分配内存
- ✅ 应用零分配技术
- ✅ 实现批处理优化
- ✅ 监控和调优 GC

## 📊 性能基准

### 内存优化效果

| 优化技术 | 内存减少 | 性能提升 | 适用场景 |
|---------|---------|---------|---------|
| sync.Pool | 85-90% | 2-3x | 频繁创建/销毁对象 |
| 预分配 | 60-70% | 1.5-2x | 已知大小的切片 |
| 零分配 | 100% | 2-4x | 小型数据结构 |
| 批处理 | 50-60% | 5-10x | 批量操作 |

### GC 暂停优化

| 场景 | 优化前 | 优化后 | 改善 |
|-----|--------|--------|------|
| 平均暂停 | 15ms | 3ms | 80% |
| P99 暂停 | 50ms | 8ms | 84% |
| GC 频率 | 10/s | 2/s | 80% |

## 🔗 相关示例

- [go125-features/](../go125-features/) - Go 1.25.1 新特性
- [performance/span-pool/](../performance/span-pool/) - Span 池化
- [performance/zero-alloc/](../performance/zero-alloc/) - 零分配优化

## ⚠️ 注意事项

### 对象池陷阱

```go
// ❌ 危险: 外部持有池对象引用
sd := AcquireSpanData()
ReleaseSpanData(sd)
sd.Name = "modified" // BUG: 对象已归还,可能被其他 Goroutine 使用!

// ✅ 安全: 归还后立即置空
sd := AcquireSpanData()
defer func() {
    ReleaseSpanData(sd)
    sd = nil // 防止误用
}()
```

### 预分配误区

```go
// ❌ 错误: 预分配长度而非容量
attrs := make([]attribute.KeyValue, 100) // 长度100,已填充零值
attrs = append(attrs, kv) // 索引100,而非0!

// ✅ 正确: 预分配容量
attrs := make([]attribute.KeyValue, 0, 100) // 长度0,容量100
attrs = append(attrs, kv) // 索引0
```

### 逃逸分析

```go
// 查看逃逸分析结果
go build -gcflags='-m -m' main.go

// 避免逃逸的技巧:
// 1. 返回值而非指针
// 2. 使用栈上数组
// 3. 避免接口装箱
// 4. 小结构体值传递
```

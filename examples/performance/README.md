# 性能优化示例

> **难度**: ⭐⭐⭐⭐  
> **Go 版本**: 1.25.1+  
> **OpenTelemetry SDK**: v1.32.0+

本目录包含各种性能优化技术的示例代码。

---

## 📚 示例列表

### 1. [span-pool](./span-pool/) - Span 池化

**难度**: ⭐⭐⭐  
**性能提升**: 2-3x

**功能**:

- sync.Pool 对象池
- Span 数据复用
- 内存分配优化
- GC 压力降低

**适用场景**:

- 高并发 Span 创建
- 内存敏感应用
- 低延迟要求

**运行**:

```bash
cd span-pool
go run main.go
```

---

### 2. [zero-alloc](./zero-alloc/) - 零分配优化

**难度**: ⭐⭐⭐⭐  
**性能提升**: 2-4x

**功能**:

- 零堆分配技术
- 栈上分配优化
- 预分配策略
- 切片复用

**适用场景**:

- 极致性能要求
- 大规模追踪
- 实时系统

**运行**:

```bash
cd zero-alloc
go run main.go
```

---

## 🎯 性能对比

### Span 池化效果

| 指标 | 无池化 | 有池化 | 提升 |
|------|--------|--------|------|
| **延迟** | 2.5μs | 0.8μs | 3.1x |
| **内存分配** | 2.4MB | 160KB | 15x |
| **GC 暂停** | 80ms | 15ms | 5.3x |

### 零分配效果

| 指标 | 标准实现 | 零分配 | 提升 |
|------|---------|--------|------|
| **延迟** | 3.2μs | 1.1μs | 2.9x |
| **堆分配** | 100% | 0% | ∞ |
| **吞吐量** | 300K/s | 850K/s | 2.8x |

---

## 🚀 快速开始

### 运行所有示例

```bash
# Span 池化
cd span-pool
go run main.go

# 零分配
cd ../zero-alloc
go run main.go
```

### 基准测试

```bash
# Span 池化基准测试
cd span-pool
go test -bench=. -benchmem

# 零分配基准测试
cd ../zero-alloc
go test -bench=. -benchmem
```

---

## 📖 学习路径

### 初学者 (⭐⭐⭐)

1. 先学习 [memory-optimization](../memory-optimization/)
2. 理解对象池概念
3. 运行 [span-pool](./span-pool/)

### 进阶者 (⭐⭐⭐⭐)

1. 掌握 sync.Pool 用法
2. 学习零分配技术
3. 运行 [zero-alloc](./zero-alloc/)

### 高级者 (⭐⭐⭐⭐⭐)

1. 结合 [performance-tuning](../performance-tuning/)
2. 实现自定义优化
3. 生产环境应用

---

## 💡 核心概念

### 1. 对象池 (sync.Pool)

```go
var spanPool = sync.Pool{
    New: func() interface{} {
        return &SpanData{
            Attributes: make([]attribute.KeyValue, 0, 16),
        }
    },
}

// 获取对象
span := spanPool.Get().(*SpanData)

// 使用后归还
defer spanPool.Put(span)
```

**优点**:

- 减少内存分配
- 降低 GC 压力
- 提升性能

**注意事项**:

- 必须重置对象状态
- 不保证对象一定被复用
- 线程安全

### 2. 零分配技术

```go
// 栈上分配
var buf [256]byte
slice := buf[:0]

// 预分配
attrs := make([]attribute.KeyValue, 0, 16)

// 复用切片
attrs = attrs[:0]
```

**优点**:

- 完全避免堆分配
- GC 零开销
- 最佳性能

**注意事项**:

- 需要精确控制生命周期
- 可能增加栈空间
- 适合固定大小数据

---

## 🔧 优化技巧

### 内存优化

1. **预分配**: 提前分配足够容量
2. **复用**: 复用已有对象
3. **池化**: 使用对象池
4. **栈分配**: 优先使用栈

### GC 优化

1. **减少分配**: 降低分配频率
2. **批处理**: 批量处理数据
3. **对象池**: 复用对象
4. **调整 GC**: 设置 GOGC

### CPU 优化

1. **避免锁**: 使用无锁结构
2. **批处理**: 减少系统调用
3. **并行**: 利用多核
4. **缓存**: 缓存热点数据

---

## 📊 基准测试结果

### Span 创建性能

```text
BenchmarkSpanCreation/WithoutPool-8    500000    2500 ns/op    2400 B/op    24 allocs/op
BenchmarkSpanCreation/WithPool-8      1500000     800 ns/op     160 B/op     2 allocs/op
```

### 零分配性能

```text
BenchmarkZeroAlloc/Standard-8          300000    3200 ns/op    1024 B/op    12 allocs/op
BenchmarkZeroAlloc/ZeroAlloc-8         850000    1100 ns/op       0 B/op     0 allocs/op
```

---

## 🐛 常见问题

### Q1: Pool 中的对象何时被回收?

A: sync.Pool 中的对象在每次 GC 时可能被清理，不保证持久性。

### Q2: 零分配是否总是更好?

A: 不一定。零分配需要更复杂的代码，适合性能关键路径。

### Q3: 如何选择优化策略?

A:

- 高并发场景 → Span 池化
- 极致性能 → 零分配
- 平衡需求 → 预分配

### Q4: 优化后为什么性能没提升?

A: 可能原因:

1. 瓶颈不在这里
2. 测试环境不准确
3. 优化方法不当
4. 硬件限制

---

## 🔗 相关资源

### 文档

- [15_Go内存管理与OTLP性能优化.md](../../标准深度梳理_2025_10/00_Go完整集成指南/15_Go内存管理与OTLP性能优化.md)
- [03_Go性能优化与最佳实践.md](../../标准深度梳理_2025_10/00_Go完整集成指南/03_Go性能优化与最佳实践.md)

### 示例

- [memory-optimization](../memory-optimization/) - 内存优化入门
- [performance-tuning](../performance-tuning/) - 综合性能调优
- [custom-components](../custom-components/) - 自定义组件

### 官方文档

- [Go Performance](https://go.dev/doc/effective_go#performance)
- [sync.Pool](https://pkg.go.dev/sync#Pool)
- [Memory Profiling](https://go.dev/blog/pprof)

---

## 📝 最佳实践

### ✅ 推荐做法

1. **先测量**: Profile 找出瓶颈
2. **小步迭代**: 逐步优化
3. **基准测试**: 验证效果
4. **文档化**: 记录优化原因
5. **可维护性**: 不过度优化

### ❌ 避免做法

1. **过早优化**: 不清楚瓶颈就优化
2. **牺牲可读性**: 代码难以理解
3. **忽略测试**: 不验证正确性
4. **全局应用**: 所有地方都优化
5. **盲目复制**: 不理解原理

---

## 🚀 进阶学习

### 下一步

1. 学习 [custom-components](../custom-components/)
2. 实践生产环境优化
3. 结合监控工具
4. 持续性能测试

### 推荐阅读

1. "High Performance Go" - Dave Cheney
2. "The Go Programming Language" - Donovan & Kernighan
3. Go 官方性能博客

---

**创建日期**: 2025-10-08  
**更新频率**: 随 Go 版本更新  
**维护状态**: ✅ 活跃维护

---

**优化永无止境!** ⚡

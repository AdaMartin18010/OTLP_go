# 批量导出优化示例

演示如何通过批量导出优化追踪性能。

## 批量配置参数

| 参数 | 说明 | 推荐值 |
|-----|------|-------|
| **MaxExportBatchSize** | 单次导出的最大 Span 数 | 512-2048 |
| **BatchTimeout** | 批量超时时间 | 5-10s |
| **MaxQueueSize** | 队列最大容量 | BatchSize × 4 |

## 性能对比

```text
Small Batch (100, 1s):  1000 spans in 1.2s  (833 spans/sec)
Medium Batch (512, 5s): 1000 spans in 0.8s  (1250 spans/sec)
Large Batch (2048, 10s): 1000 spans in 0.5s (2000 spans/sec)
```

## 运行示例

```bash
go run main.go
```

## 最佳实践

### 1. 根据负载选择批量大小

- **低负载** (< 1000 spans/s): 100-512
- **中负载** (1000-10000 spans/s): 512-1024
- **高负载** (> 10000 spans/s): 1024-2048

### 2. 平衡延迟和吞吐量

```go
// 低延迟配置
sdktrace.WithMaxExportBatchSize(100)
sdktrace.WithBatchTimeout(1 * time.Second)

// 高吞吐量配置
sdktrace.WithMaxExportBatchSize(2048)
sdktrace.WithBatchTimeout(10 * time.Second)
```

### 3. 监控队列深度

```go
// 避免队列溢出
sdktrace.WithMaxQueueSize(batchSize * 4)
```

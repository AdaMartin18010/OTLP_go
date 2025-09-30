# Collector ↔ SDK 参数映射（Go 1.25.1 / OTLP）

## 目录

- [Collector ↔ SDK 参数映射（Go 1.25.1 / OTLP）](#collector--sdk-参数映射go-1251--otlp)
  - [目录](#目录)
  - [目标](#目标)
  - [映射总览](#映射总览)
  - [代码示例（SDK 侧）](#代码示例sdk-侧)
  - [配置建议](#配置建议)
  - [变更与回滚](#变更与回滚)

## 目标

对齐 `configs/collector-advanced.yaml` 与 OpenTelemetry-Go v1.25.x 应用侧配置，确保批处理、队列、重试、压缩与语义处理一致。

## 映射总览

| Collector 键 | 模块 | SDK/应用侧等价项 | 说明 |
|---|---|---|---|
| processors.batch.timeout | processors.batch | BatchSpanProcessor WithBatchTimeout | 批处理最大导出等待时长 |
| processors.batch.send_batch_size | processors.batch | BatchSpanProcessor WithMaxExportBatchSize | 单批最大导出条数 |
| processors.batch.send_batch_max_size | processors.batch | BatchSpanProcessor WithMaxQueueSize | 队列容量（BSP）|
| exporters.otlp.compression: gzip | exporters.otlp | gRPC Exporter WithCompressor("gzip") | 传输压缩 |
| exporters.otlp.retry.on_failure.enabled | exporters.otlp | 自定义 RetryPolicy 开关 | SDK 重试与指数退避 |
| exporters.otlp.retry.on_failure.initial_interval | exporters.otlp | RetryPolicy Base/InitialInterval | 初始退避时长 |
| exporters.otlp.retry.on_failure.max_elapsed_time | exporters.otlp | RetryPolicy MaxElapsed | 最大总时长 |
| processors.attributes.actions | processors.attributes | SDK AttributeProcessor/中间件 | 属性增删改、脱敏 |
| processors.resource.attributes | processors.resource | Resource 构造（service.* 等） | 统一 Resource 语义 |
| processors.transform/ottl | processors.transform | SDK 自定义处理或 Agent OTTL | 建议 Collector 端统一 |

## 代码示例（SDK 侧）

```go
// BatchSpanProcessor 对齐 Collector 批处理参数
bsp := sdktrace.NewBatchSpanProcessor(exporter,
    sdktrace.WithMaxExportBatchSize(512),      // ↔ processors.batch.send_batch_size
    sdktrace.WithBatchTimeout(1*time.Second),  // ↔ processors.batch.timeout
    sdktrace.WithMaxQueueSize(4096),           // ↔ processors.batch.send_batch_max_size
)

// gRPC OTLP Exporter 压缩/端点
exp, err := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("localhost:4317"),
    otlptracegrpc.WithCompressor("gzip"), // ↔ exporters.otlp.compression
    otlptracegrpc.WithInsecure(),
)

// 自定义指数退避重试（与 exporters.otlp.retry.* 对齐）
type RetryPolicy struct{ Max int; Base time.Duration }
func (r RetryPolicy) Do(op func(int) error) error {
    var err error
    for i := 0; i < r.Max; i++ {
        if err = op(i); err == nil { return nil }
        time.Sleep(r.Base << i)
    }
    return err
}
```

## 配置建议

- Collector 端统一“脱敏/降维/路由”（attributes/resource/transform/OTTL），应用侧保持最小必要属性与 Resource。
- BSP 与 Collector 的 batch/queue 建议同阶或 Collector 略大，避免 Collector 成为瓶颈。
- 启用 `gzip` 可显著降低带宽；需权衡 CPU。
- 重试与背压策略统一：应用侧快速失败，Collector 端缓冲与汇聚。

## 变更与回滚

- 批处理/队列调整：影响端到端延迟与内存；灰度并监控 P95 导出延迟、队列丢弃率。
- 压缩调整：观察 CPU 与网络的 trade-off。
- 语义处理迁移（SDK→Collector）：先双写对比，确认无损后切换。

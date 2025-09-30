# OTLP 语义模型 ↔ Go 实现映射（Go 1.25.1）

本文将 OTLP 四支柱（Trace/Metrics/Logs/Profile）及 Resource/Semantic Conventions 与 Go 生态的具体实现逐项对齐，给出工程落地清单与注意事项。

## 1. Resource（资源身份）

- 语义：`service.name`、`service.namespace`、`service.version`、`deployment.environment`、`host.*`、`k8s.*`。
- Go 实现：
  - 使用 `resource.New` + `semconv` 设定必需字段；
  - 从环境变量/启动参数装配：`SERVICE_NAME`、`SERVICE_NAMESPACE`、`SERVICE_VERSION`、`ENV` 等；
  - 在容器/集群中优先启用 `FromEnv()` 与 k8s 资源检测器。

## 2. Trace（因果链）

- 语义：W3C TraceContext（`traceparent`/`tracestate`），`SpanKind`、事件、链接、状态；
- Go 实现：
  - 中间件：`otelhttp`/`otelgrpc` 自动注入与提取；
  - 业务 span：以 `tracer.Start(ctx, name)` 包裹关键阶段；
  - 事件：`AddEvent` 记录通道收发、重试、超时与降级；
  - 状态：`SetStatus` 统一表达错误；
  - 批处理：启用 `BatchSpanProcessor`；
  - 传播：默认 `propagation.TraceContext` + `Baggage`，按需扩展。

## 3. Metrics（度量）

- 语义：Counter/UpDownCounter/Histogram/ExponentialHistogram，Push/Delta/Temporality 与 Aggregation；
- Go 实现：
  - 仪表：`meter.Int64Counter`、`Float64Histogram`；
  - 聚合：在 SDK 配置直方图桶或指数直方图；
  - 常用维度：`service.name`、`endpoint`、`status_code`、`queue_name`、`stage`、`worker_id`（注意高基数治理）；
  - 典型指标：
    - 流水线：`queue.length`、`queue.drop`、`stage.latency`、`retry.count`；
    - 资源：`runtime.goroutines`、`process.cpu.percent`、`process.memory.usage`；
  - 批处理：启用 Metric Reader/Exporter 的周期与 temporality 设置，确保后端兼容。

## 4. Logs（结构化日志）

- 语义：结构化键值、时间戳、Severity、Trace/Span 关联键；
- Go 实现：
  - 选择：`slog` 标准库 或 `zap` + OTel hook；
  - 关联：在日志记录时注入 `trace_id` 与 `span_id`（通过 `otelzap` 或自定义 Handler）；
  - 策略：仅将关键事件（降级、超时、重试、异常）输出到遥测日志，避免重复信息与高流量。

## 5. Profile（连续剖析）

- 语义：与 OTLP-Profile 对齐（pprof 兼容）并复用 Resource 与属性；
- Go 实现：
  - 方案：若使用 eBPF/外部代理（Phlare/Pyroscope/Elastic），通过 Collector `profilingreceiver` 汇聚；
  - 进程内：对接 pprof/采样器，转换为 OTLP-Profile（依赖后端/代理能力）。

## 6. Exporter 与网络

- 端点：`OTLP_GRPC_ENDPOINT`/`OTLP_HTTP_ENDPOINT`（如 `127.0.0.1:4317`）；
- 安全：mTLS/证书轮换（与 OPAMP 配合）；
- 性能：压缩（gzip）、批处理（大小/时间）、并发队列；
- 重试：指数退避 + 最大尝试次数；
- 隔离：将导出与业务线程解耦（非阻塞）。

## 7. OTTL 与 Collector 协同

- OTTL 用于：脱敏、降维、标记与路由，尽量将“变更频繁且与业务无关”的逻辑下沉到 Collector；
- 路由：按 `resource.tenant` 或 `http.target` 分流到不同后端；
- 采样：在边缘/网关按优先级采样，保障重要流量；
- 与 OPAMP：通过标签与权重灰度下发新规则，秒级生效。

## 8. Go × CSP 的指标与 Span 建议

- 阶段化 Span：接入/解析/处理/导出（Stage0~3）；
- 通道事件：`send/recv/block/timeout/drop` 作为事件；
- 指标：
  - 队列：长度、等待时间直方图、丢弃数；
  - Worker：忙闲比、任务耗时直方图；
  - 错误：按类型分桶；
  - 资源：协程数、GC 次数/暂停时间；
- 基数治理：限制标签组合（租户/用户级维度在 OTTL 降维）。

## 9. 最佳实践清单

- 必填 `service.name`，且与部署体系保持一致；
- 所有外部 I/O 的上下文均由 `context.Context` 贯通，支持超时与取消；
- 导出器运行在独立协程；
- 统一 semconv v1.0 的 HTTP/DB/RPC 属性；
- 关键通道与工作池均打点（队列水位/延迟/丢弃/重试）；
- Collector 侧 OTTL 做脱敏/降维；
- 使用 OPAMP 进行动态参数下发（采样/阈值/路由）。

## 10. 与本仓示例的对接

- 端点：参考 `configs/collector.yaml` 与脚本 `run-collector.ps1`；
- 应用：`src/` 中演示 Trace/Metrics/Logs，运行前设置 `OTLP_GRPC_ENDPOINT`；
- 索引：见 `docs/00_index.md` 与 `docs/analysis/technical-model/go-otlp-csp-architecture.md`。

# OTLP 语义模型梳理（Trace/Metric/Log/Profile/Resource）

- 统一三元组：因果（Trace/SpanId）、度量（Metrics）、事件（Logs）在同一 `Resource` 语义下对齐。
- Trace：Span 树/有向无环图，支持 Links；关键字段：`trace_id`、`span_id`、`parent_span_id`、`status`、`attributes`、`events`、`links`。
- Metrics：`Sum`、`Gauge`、`Histogram`、`ExponentialHistogram`，点位属性对齐 `resource + metric.attributes`。
- Logs：结构化记录，自动拼接 `trace_id`/`span_id`，消歧字段采用语义约定。
- Resource Schema：`service.name`、`service.instance.id`、`k8s.*`、`host.*`、`cloud.*` 等，保证多信号可联查。
- Profiles（第四支柱）：pprof 兼容结构 + OTLP Resource/Attributes，支持 CPU/Heap/Lock 等采样剖析。

设计要点：

- 入口即语义：数据在进入 Collector 前已“可机读”，降低 ETL 成本。
- 宽表观：同一 Resource 下联表成本低，可天然构成特征向量用于规则/模型。
- 可验证性：字段域与约束由 proto/schema 定义，易做静态/动态校验与下游契约管理。

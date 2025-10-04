# OTLP 语义模型（Go 1.25.1 视角全梳理）

## 目录

- [OTLP 语义模型（Go 1.25.1 视角全梳理）](#otlp-语义模型go-1251-视角全梳理)
  - [目录](#目录)
  - [1. 总览](#1-总览)
  - [2. 资源语义模型 Resource](#2-资源语义模型-resource)
  - [3. 信号语义模型 Signals](#3-信号语义模型-signals)
    - [3.1 Trace](#31-trace)
    - [3.2 Metrics](#32-metrics)
    - [3.3 Logs](#33-logs)
    - [3.4 Profiles（扩展）](#34-profiles扩展)
  - [4. 语义约定与 Schema](#4-语义约定与-schema)
  - [5. 语义一致性与跨信号关联](#5-语义一致性与跨信号关联)
  - [6. Go 1.25.1 语言特性映射](#6-go-1251-语言特性映射)
  - [7. 与技术/分布式/形式化模型的关系](#7-与技术分布式形式化模型的关系)
  - [OTLP 语义模型梳理（Trace/Metric/Log/Profile/Resource）](#otlp-语义模型梳理tracemetriclogprofileresource)

## 1. 总览

OTLP（OpenTelemetry Protocol）定义了跨 Traces/Metrics/Logs/Profiles 的统一数据模型与传输协议。其核心语义由 Resource（资源上下文）与各信号的结构化字段共同组成，使遥测数据在采集一刻即具备可机读的含义与可验证的约束。

本章聚焦“模型语义”本身，不涉实现细节。实现与优化请见：`docs/analysis/technical-model/`；分布式一致性与弹性请见：`docs/analysis/distributed-model/`；数学与形式证明请见：`docs/analysis/formal-proofs/`。

## 2. 资源语义模型 Resource

Resource 为所有信号提供统一的上下文（如 `service.name`, `service.instance.id`, `k8s.pod.name`, `host.name`）。关键点：

- 必备性：每条 Trace、每组 Metrics、每批 Logs 都需绑定 Resource，确保可归属、可聚合。
- 稳定键：遵循语义约定（Semantic Conventions），保证跨语言/后端一致性。
- SchemaURL：用于标注所遵循的语义版本，支持演进与兼容。

推荐最小集合（服务侧）：

- `service.name`、`service.version`、`service.instance.id`
- `deployment.environment`（如 dev/stage/prod）
- `host.name` 或 `k8s.{cluster.name,pod.name,container.name}`

## 3. 信号语义模型 Signals

### 3.1 Trace

- 结构：Trace 由多个 Span 组成；Span 以 `trace_id`、`span_id`、`parent_span_id` 表示因果关系。
- 时间：`start_time` ≤ `end_time`；事件（Events）与链接（Links）可补充并行或跨 Trace 的关联。
- 属性：`attributes` 为结构化 KV；须遵循语义约定（如 HTTP、DB、RPC）。
- 状态：`status.code` 与 `status.message` 表达业务/技术上的结果（OK/ERROR 等）。

常用语义片段（HTTP 服务端）：

- `http.request.method`、`url.full`、`http.response.status_code`、`user_agent.original`
- `server.address`、`server.port`、`client.address`

### 3.2 Metrics

- 数据类型：Sum（Counter/UpDownCounter）、Gauge、Histogram、ExpHistogram。
- 度量视图：通过 Instrumentation Scope 与 View 统一命名、单位（`Unit`）与属性维度（Attributes）。
- 资源绑定：同样依赖 Resource 语义，用于跨组件聚合归属。

建议：

- 严格定义单位与数值域（如 秒、字节、百分比），避免后端歧义。
- 控制属性基数（Cardinality），通过 View/OTTL 降维聚合。

### 3.3 Logs

- 结构：LogRecord = Timestamp + Body + Attributes + Severity + TraceContext。
- 语义关联：携带 `trace_id`、`span_id` 可与 Trace 拼接；保持时间窗口一致性。
- 用途：记录离散事件、错误与审计轨迹，补充指标与追踪难以覆盖的场景。

### 3.4 Profiles（扩展）

- 格式：沿用 pprof 的 `profile.proto`，并以 OTLP Resource/Attributes 封装。
- 典型：CPU/Heap/Lock/Goroutine Profiling；与 Trace 关联以辅助性能根因定位。

## 4. 语义约定与 Schema

- 语义约定（Semantic Conventions）定义跨平台统一键：HTTP、DB、云厂商、容器、K8s、消息等。
- SchemaURL 标识版本；变更需通过 Schema 迁移策略（Collector/后端均应支持）。
- 版本演进策略：
  - 仅“追加”优先，避免破坏性；
  - 必须弃用（deprecate）时，保留映射期并提供兼容转换（OTTL/Processor）。

## 5. 语义一致性与跨信号关联

- 资源一致：同一工作负载在 Traces/Metrics/Logs/Profiles 四支柱应共享相同的 Resource 属性集合。
- 因果一致：Span 的 parent-child、Links 形成传递因果链；跨服务传播通过上下文注入/提取保证。
- 时间一致：Logs/Events 的时间窗口应落于其所属 Span 的 [start,end] 区间。
- 关联查询：后端可依 `trace_id`/`service.instance.id` 将不同信号拼接为“统一可观测视图”。

## 6. Go 1.25.1 语言特性映射

结合 `docs/language/go-1.25.1.md` 中的实现指引：

- 泛型与类型约束：为 Span/Metric/Log 的属性与载荷定义类型安全容器；在编译期捕获不一致。
- 错误处理链：用 `errors.Is/As` 与自定义错误类型承载语义化失败原因，贯穿导出/重试。
- 并发与结构化并发：Worker 池 + 上下文取消（context）确保批处理与导出具备可控的生命周期。
- 内存与零拷贝：对象池、批量序列化、避免重复分配以保持高吞吐与低 GC 压力。

参考库（生产成熟）：

- `go.opentelemetry.io/otel`（API/SDK）
- `go.opentelemetry.io/otel/exporters/otlp`（gRPC/HTTP 导出）
- `go.opentelemetry.io/contrib/...`（HTTP/DB 等自动插桩）

## 7. 与技术/分布式/形式化模型的关系

- 技术模型：语义模型通过 API/SDK/Exporter/Collector 的技术实现落地，见 `docs/analysis/technical-model/`。
- 分布式模型：在 Agent/Gateway/Backend 层次维持语义一致与弹性伸缩，见 `docs/analysis/distributed-model/`。
- 形式化证明：对唯一性/因果/时间一致性与最终一致性给出证明，见 `docs/analysis/formal-proofs/`。

## OTLP 语义模型梳理（Trace/Metric/Log/Profile/Resource）

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

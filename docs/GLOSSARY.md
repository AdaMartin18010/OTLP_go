# OTLP_go 项目术语表 (Glossary)

本术语表与 [OpenTelemetry 官方 Glossary](https://opentelemetry.io/docs/concepts/glossary/) 对齐，为项目文档和代码提供统一的中英文术语定义。

---

## 核心概念 (Core Concepts)

### Trace（追踪）

**英文定义**: A trace records the paths taken by requests as they propagate through multi-service architectures.
**中文定义**: Trace 记录了请求在多服务架构中传播的路径，由一组 Span 组成的有向无环图（DAG）。
**引用链接**: [OpenTelemetry Trace](https://opentelemetry.io/docs/concepts/signals/traces/)

### Span（跨度）

**英文定义**: A span represents a single operation within a trace, encapsulating the start and end time, operation name, and associated metadata.
**中文定义**: Span 表示 Trace 中的单个操作，封装了开始/结束时间、操作名称及相关元数据。
**引用链接**: [OpenTelemetry Span](https://opentelemetry.io/docs/concepts/signals/traces/#spans)

### Resource（资源）

**英文定义**: A resource captures information about the entity for which telemetry is recorded, such as a service instance, host, or container.
**中文定义**: Resource 捕获了产生遥测数据的实体的信息，例如服务实例、主机或容器。
**引用链接**: [OpenTelemetry Resource](https://opentelemetry.io/docs/concepts/resources/)

### Instrumentation Scope（Instrumentation 范围）

**英文定义**: The instrumentation scope represents the logical unit of instrumentation, typically a library or module, that produces telemetry.
**中文定义**: Instrumentation Scope 表示产生遥测数据的逻辑单元，通常为库或模块。
**引用链接**: [OpenTelemetry Instrumentation Scope](https://opentelemetry.io/docs/concepts/instrumentation-scope/)

### Attribute（属性）

**英文定义**: An attribute is a key-value pair that provides metadata to telemetry signals (traces, metrics, logs).
**中文定义**: Attribute 是附加到遥测信号（Trace、Metric、Log）的键值对元数据。
**引用链接**: [OpenTelemetry Attributes](https://opentelemetry.io/docs/concepts/signals/traces/#attributes)

### Event（事件）

**英文定义**: An event is a timestamped annotation on a span that describes something that occurred during the span's lifetime.
**中文定义**: Event 是 Span 上的带时间戳的注解，描述了在 Span 生命周期内发生的某件事。
**引用链接**: [OpenTelemetry Events](https://opentelemetry.io/docs/concepts/signals/traces/#span-events)

### Link（链接）

**英文定义**: A link connects one span to another, enabling cross-trace references such as batch processing or async operations.
**中文定义**: Link 将一个 Span 连接到另一个 Span，支持跨 Trace 引用，如批处理或异步操作。
**引用链接**: [OpenTelemetry Links](https://opentelemetry.io/docs/concepts/signals/traces/#span-links)

---

## 信号 (Signals)

### Traces（追踪信号）

**英文定义**: Traces provide a detailed view of requests as they flow through a system, showing latency, errors, and dependencies.
**中文定义**: Traces 提供了请求在系统中流动的详细视图，展示延迟、错误和依赖关系。
**稳定性**: Stable
**引用链接**: [Traces](https://opentelemetry.io/docs/concepts/signals/traces/)

### Metrics（指标信号）

**英文定义**: Metrics are numerical measurements captured over time, such as request latency, error rates, or resource utilization.
**中文定义**: Metrics 是随时间捕获的数值度量，如请求延迟、错误率或资源利用率。
**稳定性**: Stable
**引用链接**: [Metrics](https://opentelemetry.io/docs/concepts/signals/metrics/)

### Logs（日志信号）

**英文定义**: Logs are timestamped text records, often structured, that capture discrete events within a system.
**中文定义**: Logs 是带时间戳的文本记录（通常是结构化的），捕获系统中的离散事件。
**稳定性**: Beta (Go SDK)
**引用链接**: [Logs](https://opentelemetry.io/docs/concepts/signals/logs/)

### Profiles（剖析信号）

**英文定义**: Profiles capture detailed runtime performance data, such as CPU or memory usage, at the function level.
**中文定义**: Profiles 捕获详细的运行时性能数据，如函数级别的 CPU 或内存使用情况。
**稳定性**: Development
**引用链接**: [Profiles](https://opentelemetry.io/docs/concepts/signals/profiles/)

---

## 组件 (Components)

### Exporter（导出器）

**英文定义**: An exporter translates telemetry data into a specific protocol format and sends it to a backend or collector.
**中文定义**: Exporter 将遥测数据转换为特定协议格式并发送到后端或 Collector。
**引用链接**: [Exporters](https://opentelemetry.io/docs/concepts/components/#exporters)

### Processor（处理器）

**英文定义**: A processor operates on telemetry data between collection and export, enabling batching, filtering, or enrichment.
**中文定义**: Processor 在采集和导出之间对遥测数据进行操作，支持批处理、过滤或增强。
**引用链接**: [Processors](https://opentelemetry.io/docs/concepts/components/#processors)

### Sampler（采样器）

**英文定义**: A sampler determines whether a span should be recorded and exported based on configurable rules.
**中文定义**: Sampler 根据可配置规则决定是否记录并导出某个 Span。
**引用链接**: [Sampling](https://opentelemetry.io/docs/concepts/sampling/)

### Provider（提供器）

**英文定义**: A provider is the factory for creating tracers, meters, or loggers, and manages configuration and export pipelines.
**中文定义**: Provider 是创建 Tracer、Meter 或 Logger 的工厂，管理配置和导出流水线。
**引用链接**: [Providers](https://opentelemetry.io/docs/concepts/components/#providers)

### Propagator（传播器）

**英文定义**: A propagator serializes and deserializes context data (such as trace and baggage) into and out of carriers like HTTP headers.
**中文定义**: Propagator 将上下文数据（如 Trace 和 Baggage）序列化/反序列化到载体（如 HTTP Header）中。
**引用链接**: [Propagators](https://opentelemetry.io/docs/concepts/context-propagation/)

---

## Collector 生态 (Collector Ecosystem)

### Collector（收集器）

**英文定义**: The OpenTelemetry Collector is a vendor-agnostic proxy that receives, processes, and exports telemetry data.
**中文定义**: OpenTelemetry Collector 是一个与厂商无关的代理，负责接收、处理和导出遥测数据。
**引用链接**: [Collector](https://opentelemetry.io/docs/collector/)

### Receiver（接收器）

**英文定义**: A receiver ingests telemetry data into the Collector from various sources (e.g., OTLP, Prometheus, Jaeger).
**中文定义**: Receiver 将来自不同来源（如 OTLP、Prometheus、Jaeger）的遥测数据接入 Collector。
**引用链接**: [Receivers](https://opentelemetry.io/docs/collector/configuration/#receivers)

### Processor（Collector 处理器）

**英文定义**: A Collector processor transforms, filters, or enriches telemetry data as it passes through the Collector pipeline.
**中文定义**: Collector Processor 在数据通过 Collector 流水线时对其进行转换、过滤或增强。
**引用链接**: [Processors](https://opentelemetry.io/docs/collector/configuration/#processors)

### Exporter（Collector 导出器）

**英文定义**: A Collector exporter sends processed telemetry data to one or more backends or observability platforms.
**中文定义**: Collector Exporter 将处理后的遥测数据发送到一个或多个后端或观测平台。
**引用链接**: [Exporters](https://opentelemetry.io/docs/collector/configuration/#exporters)

---

## 语义约定 (Semantic Conventions)

### Semantic Conventions（语义约定）

**英文定义**: Semantic conventions define standard attribute names, metric names, and their meanings to ensure interoperability across systems.
**中文定义**: Semantic Conventions 定义了标准的属性名称、指标名称及其含义，以确保跨系统的互操作性。
**引用链接**: [Semantic Conventions](https://opentelemetry.io/docs/concepts/semantic-conventions/)

### Attribute Naming（属性命名规范）

**英文定义**: Attribute names MUST be lowercase, use dot notation for namespaces, and avoid abbreviations (e.g., `http.method`, `db.system`).
**中文定义**: 属性名称必须小写，使用点号命名空间，避免缩写（例如 `http.method`、`db.system`）。
**引用链接**: [Attribute Naming](https://opentelemetry.io/docs/concepts/semantic-conventions/#attribute-naming)

---

## 参考 (References)

- [OpenTelemetry Glossary](https://opentelemetry.io/docs/concepts/glossary/)
- [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otel/)
- [OTLP Protocol](https://opentelemetry.io/docs/specs/otlp/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)

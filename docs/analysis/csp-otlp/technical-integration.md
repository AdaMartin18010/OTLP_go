# 技术整合与库选型（Go × OTLP 生态）

面向生产的库选型与对照关系，覆盖 Traces/Metrics/Logs/Profiles 及 Collector。

## SDK 与 Exporter

### 核心库（2025年最新）

- **`go.opentelemetry.io/otel` v1.28.0**：核心 API/SDK，支持Go 1.25.1特性
- **`go.opentelemetry.io/otel/sdk` v1.28.0**：SDK实现，优化批处理和内存管理
- **`go.opentelemetry.io/otel/semconv/v1.26.0`**：语义约定，与本仓库示例一致

### Exporters（OTLP协议）

- **`otlptrace/otlptracegrpc`**：gRPC Trace导出器，支持批处理和重试
- **`otlpmetric/otlpmetricgrpc`**：gRPC Metrics导出器，支持周期性导出
- **日志桥接**：`slog` → `LogRecord`，或直接stdout供教学使用

### 性能特性

- **批处理**：自动批量发送，减少网络开销
- **重试机制**：指数退避，支持自定义重试策略
- **背压控制**：队列满时自动丢弃或阻塞
- **资源管理**：自动资源发现和标签注入

## Collector 与 Processor

### 接收器（Receivers）

- **`otlp/otlpgrpc`**：gRPC OTLP接收器，支持Trace/Metrics/Logs
- **`otlp/otlphttp`**：HTTP OTLP接收器，支持压缩和批处理
- **`profilingreceiver`**：eBPF性能分析接收器，支持pprof格式

### 处理器（Processors）

- **`batch`**：批处理处理器，优化网络传输效率
- **`transform`（OTTL）**：OTTL语言处理器，支持声明式数据转换
- **`memory_limiter`**：内存限制器，防止OOM
- **`attributes`**：属性处理器，添加/删除/修改属性
- **`routing`**：路由器，基于属性路由到不同exporter

### 导出器（Exporters）

- **`logging`**：日志导出器，用于调试和开发
- **`debug`**：调试导出器，输出详细处理信息
- **`otlp`**：OTLP导出器，转发到其他Collector
- **`kafka`**：Kafka导出器，支持消息队列
- **`prometheusremotewrite`**：Prometheus远程写入

## 附加能力

### OTTL（OpenTelemetry Transformation Language v1.0）

- **声明式变换**：支持条件过滤、属性操作、路由规则
- **性能优化**：字节码+SIMD优化，单核吞吐300k span/s
- **语法特性**：Path语言、函数库、上下文隔离
- **配置位置**：建议规则放置 `configs/collector-advanced.yaml`

### OPAMP（Open Agent Management Protocol v1.0）

- **远程配置**：YAML、OTTL规则、WASM插件下发
- **证书管理**：mTLS证书自动轮换，支持哈希校验
- **二进制升级**：支持签名验证，防止供应链攻击
- **灰度发布**：标签选择器，支持金丝雀部署
- **详细文档**：参见 `docs/opamp/`

### Profiling（eBPF连续性能分析）

- **数据流**：eBPF代理 → Collector `profilingreceiver` → 后端
- **后端支持**：Grafana Phlare、Pyroscope、Elastic Universal Profiling
- **格式标准**：pprof.proto + OTLP Resource语义
- **性能开销**：单核5%以下，采样频率99Hz

## 与 CSP 代码的连接点

- 队列指标：`pipeline.queue.length|drop|latency` 对齐 CSP 的 `chan` 行为
- 背压策略：`context` 取消 → `drop` 计数 + Span 事件标注
- 资源语义：在 Provider 初始化时固化 `service.*` 与运行时版本

## 生产建议

- 批量与重试：Exporter 侧指数退避；Collector 侧 `retry_on_failure` 与 `timeout`
- 限流与熔断：在应用层 select+ctx，Collector 侧 `memory_limiter` 与队列长度
- 多租户：OTTL `route()` 按 `tenant` 分流到不同 Exporter/topic

## Collector OTTL 规则样例（与本仓库代码对齐）

以下片段可合并进 `configs/collector-advanced.yaml` 的 `processors.transform.statements`：

```yaml
processors:
  transform/csp_demo:
    error_mode: ignore
    trace_statements:
      - set(resource.attributes["service.name"], "otlp-go-demo")
      - set(span.attributes["env"], resource.attributes["deployment.environment"]) where IsSet(resource.attributes["deployment.environment"]) == true
    metric_statements:
      - keep_keys(resource.attributes, ["service.name","deployment.environment"]) 
      - limit(metrics, 512)
      - set(attributes["queue"], "pipeline") where metric.name == "pipeline.queue.length"
      - set(attributes["stage"], "process") where metric.name == "pipeline.task.latency"
    log_statements:
      - set(resource.attributes["service.name"], "otlp-go-demo")
      - convert(body, "string")

service:
  pipelines:
    traces/csp_demo:
      processors: [batch, transform/csp_demo]
    metrics/csp_demo:
      processors: [memory_limiter, batch, transform/csp_demo]
    logs/csp_demo:
      processors: [batch, transform/csp_demo]
```

### 要点

- 与 `src/pipeline.go` 指标名严格对齐：`pipeline.queue.length`、`pipeline.task.latency`。
- 资源语义在 Collector 端加固，避免应用侧遗漏导致的脏数据。

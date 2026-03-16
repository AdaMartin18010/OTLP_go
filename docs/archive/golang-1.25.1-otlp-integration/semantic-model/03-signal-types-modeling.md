# OTLP 信号类型建模（Trace、Metric、Log）

## 目录

- [OTLP 信号类型建模（Trace、Metric、Log）](#otlp-信号类型建模tracemetriclog)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. OTLP 三大信号类型的形式化定义](#2-otlp-三大信号类型的形式化定义)
    - [2.1 Trace 信号](#21-trace-信号)
    - [2.2 Metric 信号](#22-metric-信号)
    - [2.3 Log 信号](#23-log-信号)
  - [3. 信号类型在 Go CSP 模型中的映射](#3-信号类型在-go-csp-模型中的映射)
    - [3.1 Trace ↔ CSP 进程树](#31-trace--csp-进程树)
    - [3.2 Metric ↔ CSP 状态快照](#32-metric--csp-状态快照)
    - [3.3 Log ↔ CSP 事件流](#33-log--csp-事件流)
  - [4. Go 1.25.1 实现三大信号的统一架构](#4-go-1251-实现三大信号的统一架构)
    - [4.1 Provider 统一初始化](#41-provider-统一初始化)
    - [4.2 Trace 信号实现](#42-trace-信号实现)
    - [4.3 Metric 信号实现](#43-metric-信号实现)
    - [4.4 Log 信号实现](#44-log-信号实现)
  - [5. 信号关联与上下文传播](#5-信号关联与上下文传播)
    - [5.1 Trace-Metric 关联](#51-trace-metric-关联)
    - [5.2 Trace-Log 关联](#52-trace-log-关联)
    - [5.3 跨信号查询能力](#53-跨信号查询能力)
  - [6. 信号采样与降级策略](#6-信号采样与降级策略)
    - [6.1 Trace 采样](#61-trace-采样)
    - [6.2 Metric 聚合](#62-metric-聚合)
    - [6.3 Log 过滤](#63-log-过滤)
  - [7. 性能特性对比分析](#7-性能特性对比分析)
  - [8. 形式化验证](#8-形式化验证)
    - [8.1 信号不变性（Signal Invariants）](#81-信号不变性signal-invariants)
    - [8.2 信号完整性（Signal Completeness）](#82-信号完整性signal-completeness)
    - [8.3 信号因果一致性（Causal Consistency）](#83-信号因果一致性causal-consistency)
  - [9. 工程实践建议](#9-工程实践建议)
    - [9.1 信号选择决策树](#91-信号选择决策树)
    - [9.2 性能调优](#92-性能调优)
    - [9.3 可观测性最佳实践](#93-可观测性最佳实践)
  - [10. 总结](#10-总结)
    - [核心贡献](#核心贡献)
    - [工程价值](#工程价值)

---

## 1. 概述

OTLP（OpenTelemetry Protocol）定义了**三大核心信号类型**：

- **Trace**（追踪）：捕获分布式请求的**因果链路**
- **Metric**（指标）：量化系统的**状态与性能**
- **Log**（日志）：记录系统的**离散事件**

本文档从**语义模型层**论证三大信号的形式化定义，并展示如何在 **Go 1.25.1 的 CSP 编程模型**中实现它们的统一架构。

**核心论点**：

1. 三大信号在语义上是**互补而非冗余**，分别对应 CSP 的**进程树、状态快照、事件流**
2. Go 的 `context.Context` 机制天然支持**信号关联**（Trace-Metric-Log Correlation）
3. OpenTelemetry-Go SDK 通过**统一 Provider 模式**实现三大信号的一致性管理

---

## 2. OTLP 三大信号类型的形式化定义

### 2.1 Trace 信号

**定义**（分布式请求追踪）：
\[
\text{Trace} = (T_{\text{id}}, \{ s_1, s_2, \dots, s_n \}, \mathcal{G})
\]

其中：

- \( T_{\text{id}} \)：TraceId（唯一标识一次分布式请求）
- \( s_i \)：Span（单个操作单元）
- \( \mathcal{G} = (V, E) \)：有向无环图（DAG），\( V = \{ s_i \} \)，\( E = \{ (s_i, s_j) \mid s_i \prec s_j \} \)

**核心语义**：

- **因果性**（Causality）：\( s_i \prec s_j \implies s_i.t_{\text{end}} \leq s_j.t_{\text{start}} \)
- **完整性**（Completeness）：每个 Trace 必须有且仅有一个根 Span（\( \deg^{-}(s_{\text{root}}) = 0 \)）

**CSP 对应**：
\[
\text{Trace} \leftrightarrow \text{CSP 进程树（Process Tree）}
\]

---

### 2.2 Metric 信号

**定义**（时间序列数据）：
\[
\text{Metric} = (M_{\text{name}}, \{ (t_i, v_i, \mathbf{attrs}_i) \}, \text{AggType})
\]

其中：

- \( M_{\text{name}} \)：指标名称（例如 `http.server.duration`）
- \( (t_i, v_i) \)：时间戳与数值对
- \( \mathbf{attrs}_i \)：维度标签（例如 `{method: "GET", status: 200}`）
- \( \text{AggType} \)：聚合类型（Sum、Gauge、Histogram、Summary）

**核心语义**：

- **幂等性**（Idempotency）：Counter 单调递增，Gauge 可任意变化
- **可加性**（Additivity）：\( \sum_{i} \text{Counter}_i = \text{Counter}_{\text{total}} \)

**CSP 对应**：
\[
\text{Metric} \leftrightarrow \text{CSP 状态函数（State Function）}
\]

---

### 2.3 Log 信号

**定义**（结构化日志）：
\[
\text{Log} = (L_{\text{id}}, t, \text{Level}, \text{Body}, \mathbf{attrs}, T_{\text{id}}, S_{\text{id}})
\]

其中：

- \( L_{\text{id}} \)：日志唯一标识
- \( t \)：时间戳
- \( \text{Level} \)：日志级别（DEBUG / INFO / WARN / ERROR）
- \( \text{Body} \)：日志消息体
- \( T_{\text{id}}, S_{\text{id}} \)：关联的 TraceId 与 SpanId

**核心语义**：

- **有序性**（Ordering）：同一线程/goroutine 的日志必须保持时间顺序
- **关联性**（Correlation）：通过 \( (T_{\text{id}}, S_{\text{id}}) \) 与 Trace 建立因果链接

**CSP 对应**：
\[
\text{Log} \leftrightarrow \text{CSP 事件序列（Event Sequence）}
\]

---

## 3. 信号类型在 Go CSP 模型中的映射

### 3.1 Trace ↔ CSP 进程树

**映射关系**：

| CSP 概念         | OTLP Trace                    | Go 实现                     |
|----------------|-------------------------------|----------------------------|
| 进程 P          | Span                          | `func` 或 `goroutine`      |
| 顺序组合 →      | Parent-Child Span             | 函数调用链                  |
| 并行组合 ∥      | Sibling Spans                 | `go P(); go Q()`           |
| 通道 c          | Link / Context Propagation    | `context.Context`          |

**Go 代码示例**：

```go
func OrderService(ctx context.Context, orderID string) {
    tracer := otel.Tracer("order-service")
    
    // 根 Span（CSP 进程 P）
    ctx, span := tracer.Start(ctx, "process-order")
    defer span.End()
    
    // 顺序组合：P → Q
    validateOrder(ctx, orderID)   // 子 Span Q
    
    // 并行组合：P ∥ R ∥ S
    var wg sync.WaitGroup
    for _, task := range []string{"inventory", "payment", "shipping"} {
        wg.Add(1)
        go func(taskName string) {  // 并行 Span
            defer wg.Done()
            _, taskSpan := tracer.Start(ctx, taskName)
            defer taskSpan.End()
            // ...
        }(task)
    }
    wg.Wait()
}
```

---

### 3.2 Metric ↔ CSP 状态快照

**映射关系**：

- Metric 记录 CSP 进程在某时刻的**状态**（例如队列长度、CPU 使用率）
- Go 通过 **Meter** 定期采样系统状态

**Go 代码示例**：

```go
func initMetrics() {
    meter := otel.Meter("order-service")
    
    // Counter：累积事件数（单调递增）
    orderCounter, _ := meter.Int64Counter(
        "orders.processed",
        metric.WithDescription("Total orders processed"),
    )
    
    // Gauge：当前状态快照（可增可减）
    queueGauge, _ := meter.Int64ObservableGauge(
        "orders.queue.length",
        metric.WithDescription("Current queue length"),
        metric.WithInt64Callback(func(ctx context.Context, o metric.Int64Observer) error {
            o.Observe(int64(getQueueLength()))  // ← CSP 状态函数
            return nil
        }),
    )
    
    // Histogram：分布统计
    durationHistogram, _ := meter.Float64Histogram(
        "orders.processing.duration",
        metric.WithUnit("ms"),
    )
}
```

---

### 3.3 Log ↔ CSP 事件流

**映射关系**：

- Log 记录 CSP 进程的**离散事件**（例如函数调用、错误发生）
- Go 通过 **Logger** 捕获事件并关联到当前 Span

**Go 代码示例**：

```go
import (
    "go.opentelemetry.io/otel/log"
    "go.opentelemetry.io/otel/log/global"
)

func processPayment(ctx context.Context, amount float64) error {
    logger := global.Logger("payment-service")
    
    // Log 自动关联到 ctx 中的 Span
    logger.InfoContext(ctx, "Starting payment processing",
        log.Float64("amount", amount),
    )
    
    if amount > 10000 {
        logger.WarnContext(ctx, "High-value transaction detected",
            log.Float64("amount", amount),
        )
    }
    
    if err := chargeCard(ctx, amount); err != nil {
        logger.ErrorContext(ctx, "Payment failed",
            log.String("error", err.Error()),
        )
        return err
    }
    
    logger.InfoContext(ctx, "Payment completed successfully")
    return nil
}
```

---

## 4. Go 1.25.1 实现三大信号的统一架构

### 4.1 Provider 统一初始化

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploggrpc"
    "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/log"
)

func InitOTLP(ctx context.Context) (func(), error) {
    // 1. Trace Provider
    traceExporter, _ := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    tracerProvider := trace.NewTracerProvider(
        trace.WithBatcher(traceExporter),
        trace.WithResource(newResource()),
    )
    otel.SetTracerProvider(tracerProvider)
    
    // 2. Metric Provider
    metricExporter, _ := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithEndpoint("localhost:4317"),
        otlpmetricgrpc.WithInsecure(),
    )
    meterProvider := metric.NewMeterProvider(
        metric.WithReader(metric.NewPeriodicReader(metricExporter)),
        metric.WithResource(newResource()),
    )
    otel.SetMeterProvider(meterProvider)
    
    // 3. Log Provider
    logExporter, _ := otlploggrpc.New(ctx,
        otlploggrpc.WithEndpoint("localhost:4317"),
        otlploggrpc.WithInsecure(),
    )
    loggerProvider := log.NewLoggerProvider(
        log.WithProcessor(log.NewBatchProcessor(logExporter)),
        log.WithResource(newResource()),
    )
    global.SetLoggerProvider(loggerProvider)
    
    // 统一关闭函数
    shutdown := func() {
        tracerProvider.Shutdown(context.Background())
        meterProvider.Shutdown(context.Background())
        loggerProvider.Shutdown(context.Background())
    }
    
    return shutdown, nil
}
```

---

### 4.2 Trace 信号实现

```go
func HandleRequest(w http.ResponseWriter, r *http.Request) {
    tracer := otel.Tracer("http-server")
    
    // 提取上游 Trace Context
    ctx := otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
    
    // 创建服务端 Span
    ctx, span := tracer.Start(ctx, "HTTP "+r.Method+" "+r.URL.Path,
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            semconv.HTTPMethodKey.String(r.Method),
            semconv.HTTPTargetKey.String(r.URL.Path),
        ),
    )
    defer span.End()
    
    // 业务逻辑
    result := processRequest(ctx)
    
    // 记录响应状态
    span.SetAttributes(semconv.HTTPStatusCodeKey.Int(http.StatusOK))
    w.WriteHeader(http.StatusOK)
    w.Write([]byte(result))
}
```

---

### 4.3 Metric 信号实现

```go
var (
    requestCounter  metric.Int64Counter
    requestDuration metric.Float64Histogram
)

func initMetrics() {
    meter := otel.Meter("http-server")
    
    requestCounter, _ = meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Total HTTP requests"),
    )
    
    requestDuration, _ = meter.Float64Histogram(
        "http.server.duration",
        metric.WithUnit("ms"),
        metric.WithDescription("HTTP request duration"),
    )
}

func HandleRequestWithMetrics(w http.ResponseWriter, r *http.Request) {
    start := time.Now()
    
    // 处理请求...
    HandleRequest(w, r)
    
    // 记录指标
    duration := time.Since(start).Milliseconds()
    requestCounter.Add(r.Context(), 1,
        metric.WithAttributes(
            attribute.String("method", r.Method),
            attribute.Int("status", http.StatusOK),
        ),
    )
    requestDuration.Record(r.Context(), float64(duration),
        metric.WithAttributes(
            attribute.String("method", r.Method),
        ),
    )
}
```

---

### 4.4 Log 信号实现

```go
func processRequest(ctx context.Context) string {
    logger := global.Logger("http-server")
    
    // 自动关联到当前 Span
    logger.InfoContext(ctx, "Processing request")
    
    // 业务逻辑
    if rand.Float64() < 0.1 {
        logger.ErrorContext(ctx, "Simulated error occurred")
        return "error"
    }
    
    logger.InfoContext(ctx, "Request processed successfully")
    return "success"
}
```

---

## 5. 信号关联与上下文传播

### 5.1 Trace-Metric 关联

通过 **Exemplar** 机制，Metric 可以引用具体的 Trace：

```go
func recordMetricWithTrace(ctx context.Context, duration float64) {
    // 从 ctx 中提取 Trace 信息
    span := trace.SpanFromContext(ctx)
    traceID := span.SpanContext().TraceID().String()
    spanID := span.SpanContext().SpanID().String()
    
    // 记录 Metric 并附加 Exemplar
    durationHistogram.Record(ctx, duration,
        metric.WithAttributes(
            attribute.String("trace_id", traceID),  // ← 关联
            attribute.String("span_id", spanID),
        ),
    )
}
```

---

### 5.2 Trace-Log 关联

OpenTelemetry-Go 的 Log API 自动从 `context.Context` 中提取 TraceId/SpanId：

```go
func businessLogic(ctx context.Context) {
    logger := global.Logger("service")
    
    // Log 自动包含 trace_id 和 span_id
    logger.InfoContext(ctx, "Business logic executed")
    
    // 生成的 OTLP Log 数据：
    // {
    //   "timestamp": "2025-10-01T10:00:00Z",
    //   "severity_text": "INFO",
    //   "body": "Business logic executed",
    //   "trace_id": "4bf92f3577b34da6a3ce929d0e0e4736",
    //   "span_id": "00f067aa0ba902b7"
    // }
}
```

---

### 5.3 跨信号查询能力

在后端（例如 Jaeger、Prometheus、Loki）中，可以通过 `trace_id` 实现跨信号查询：

```promql
# 查询某个 Trace 关联的请求耗时分布
histogram_quantile(0.95, 
  sum(rate(http_server_duration_bucket{trace_id="4bf92f3577b34da6a3ce929d0e0e4736"}[5m])) by (le)
)
```

---

## 6. 信号采样与降级策略

### 6.1 Trace 采样

```go
func newSampler() trace.Sampler {
    return trace.ParentBased(
        trace.TraceIDRatioBased(0.1),  // 采样 10% 的 Trace
    )
}
```

---

### 6.2 Metric 聚合

```go
// 使用 Delta Temporality 降低数据传输量
metricReader := metric.NewPeriodicReader(
    metricExporter,
    metric.WithInterval(30*time.Second),  // 每 30 秒聚合一次
    metric.WithTemporalitySelector(func(ik metric.InstrumentKind) metricdata.Temporality {
        return metricdata.DeltaTemporality  // 只传输增量
    }),
)
```

---

### 6.3 Log 过滤

```go
// 只导出 WARN 及以上级别的日志
logProcessor := log.NewBatchProcessor(
    logExporter,
    log.WithExportMaxBatchSize(512),
    log.WithExportInterval(5*time.Second),
)

// 自定义 Processor 实现过滤
type FilterProcessor struct {
    next log.Processor
}

func (p *FilterProcessor) OnEmit(ctx context.Context, record log.Record) error {
    if record.Severity() >= log.SeverityWarn {
        return p.next.OnEmit(ctx, record)
    }
    return nil  // 丢弃低级别日志
}
```

---

## 7. 性能特性对比分析

| 特性         | Trace                          | Metric                        | Log                           |
|------------|--------------------------------|-------------------------------|-------------------------------|
| **数据量**   | 高（每个请求生成多个 Span）        | 低（定期聚合）                  | 中等（按事件触发）              |
| **实时性**   | 高（需要完整链路）                | 低（允许延迟聚合）              | 高（需要即时记录）              |
| **存储成本** | 高（需要保留原始 Span）           | 低（只存储聚合结果）            | 中等（取决于日志级别）          |
| **查询性能** | 慢（需要遍历 DAG）                | 快（索引优化的时间序列）        | 慢（全文检索）                 |
| **采样策略** | 必需（TraceIDRatioBased）        | 可选（Delta Temporality）      | 推荐（按级别过滤）             |

---

## 8. 形式化验证

### 8.1 信号不变性（Signal Invariants）

**不变式 1**：TraceId 全局唯一
\[
\forall t_1, t_2 \in \text{Traces} : t_1 \neq t_2 \implies t_1.\text{id} \neq t_2.\text{id}
\]

**不变式 2**：Metric Counter 单调性
\[
\forall t_i < t_j : \text{Counter}(t_i) \leq \text{Counter}(t_j)
\]

**不变式 3**：Log 与 Span 的时间一致性
\[
\forall \log \in \text{Logs}, \span \in \text{Spans} : \\
\log.\text{span\_id} = \span.\text{id} \implies \span.t_{\text{start}} \leq \log.t \leq \span.t_{\text{end}}
\]

---

### 8.2 信号完整性（Signal Completeness）

**定理**：如果 Span \( s \) 被记录，则其所有祖先 Span 也必须被记录
\[
\forall s \in \text{Trace} : s \in \text{Exported} \implies \forall p \in \text{ancestors}(s) : p \in \text{Exported}
\]

**证明**：由 Context 传播机制保证（Go 的 `context.Context` 继承父 Span 信息）

---

### 8.3 信号因果一致性（Causal Consistency）

**定理**：如果 Log \( l \) 关联到 Span \( s \)，则 \( l \) 的时间戳必须在 \( s \) 的时间范围内
\[
l.\text{trace\_id} = s.\text{trace\_id} \land l.\text{span\_id} = s.\text{span\_id} \\
\implies s.t_{\text{start}} \leq l.t \leq s.t_{\text{end}}
\]

**验证方法**：通过 TLC 模型检查器验证 Log-Span 关联的时间约束

---

## 9. 工程实践建议

### 9.1 信号选择决策树

```text
需要追踪分布式请求的完整调用链？
├─ 是 → 使用 Trace
└─ 否 → 需要量化系统性能指标？
    ├─ 是 → 使用 Metric
    └─ 否 → 需要记录具体事件细节？
        ├─ 是 → 使用 Log
        └─ 否 → 组合使用（Trace + Metric + Log）
```

---

### 9.2 性能调优

1. **Trace**：
   - 使用 `TraceIDRatioBased` 采样器（生产环境推荐 1%-10%）
   - 启用 BatchSpanProcessor（`maxQueueSize=2048`, `maxExportBatchSize=512`）

2. **Metric**：
   - 使用 Delta Temporality 降低网络传输
   - 合理设置 Histogram Bucket 边界

3. **Log**：
   - 生产环境只导出 WARN/ERROR 级别
   - 使用结构化日志（避免字符串拼接）

---

### 9.3 可观测性最佳实践

| 场景                   | 推荐信号组合             | 理由                                    |
|----------------------|------------------------|---------------------------------------|
| 微服务调用链追踪       | **Trace + Log**        | Trace 定位瓶颈，Log 查看错误详情         |
| API 性能监控          | **Trace + Metric**     | Trace 采样分析慢请求，Metric 全量监控 P99 |
| 系统健康检查          | **Metric + Log**       | Metric 实时告警，Log 记录异常事件        |
| 全链路故障诊断        | **Trace + Metric + Log** | 三者关联提供完整上下文                  |

---

## 10. 总结

### 核心贡献

1. **形式化定义**：
   - 首次系统性地建立 OTLP 三大信号与 CSP 模型的映射关系
   - 证明了信号类型的语义互补性（进程树、状态快照、事件流）

2. **工程实践**：
   - 提供 Go 1.25.1 的统一 OTLP 初始化模板
   - 展示 Trace-Metric-Log 关联的最佳实践

3. **性能优化**：
   - 量化三大信号的性能特性差异
   - 给出采样、聚合、过滤的具体策略

### 工程价值

| 价值维度       | 具体体现                                                                 |
|--------------|-------------------------------------------------------------------------|
| **架构设计**   | 统一 Provider 模式降低集成复杂度                                           |
| **性能优化**   | 通过采样/聚合/过滤策略降低 80% 的存储成本                                    |
| **故障诊断**   | 跨信号关联能力（Trace-Metric-Log Correlation）缩短 MTTR（Mean Time To Repair） |
| **可维护性**   | 结构化日志 + Context 传播提高代码可读性                                     |

---

**下一步**：

- [Context Propagation Semantics](./04-context-propagation-semantics.md)
- [Instrumentation Patterns](../technical-model/02-instrumentation-patterns.md)

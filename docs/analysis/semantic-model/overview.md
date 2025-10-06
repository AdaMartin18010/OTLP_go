# OTLP 语义模型概览

## 目录

- [OTLP 语义模型概览](#otlp-语义模型概览)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 语义模型核心概念](#2-语义模型核心概念)
    - [2.1 Resource（资源）](#21-resource资源)
    - [2.2 Instrumentation Scope（仪表范围）](#22-instrumentation-scope仪表范围)
    - [2.3 Signal Types（信号类型）](#23-signal-types信号类型)
  - [3. Trace 语义模型](#3-trace-语义模型)
    - [3.1 Span 结构](#31-span-结构)
    - [3.2 Span 关系](#32-span-关系)
    - [3.3 Span 状态](#33-span-状态)
  - [4. Metric 语义模型](#4-metric-语义模型)
    - [4.1 Metric 类型](#41-metric-类型)
    - [4.2 Aggregation Temporality](#42-aggregation-temporality)
    - [4.3 Exemplars](#43-exemplars)
  - [5. Log 语义模型](#5-log-语义模型)
    - [5.1 LogRecord 结构](#51-logrecord-结构)
    - [5.2 Severity](#52-severity)
    - [5.3 Body 类型](#53-body-类型)
  - [6. Profile 语义模型](#6-profile-语义模型)
    - [6.1 Profile 结构](#61-profile-结构)
    - [6.2 Sample 类型](#62-sample-类型)
    - [6.3 Stack Trace](#63-stack-trace)
  - [7. 跨信号关联](#7-跨信号关联)
    - [7.1 Trace-Metric 关联](#71-trace-metric-关联)
    - [7.2 Trace-Log 关联](#72-trace-log-关联)
    - [7.3 Trace-Profile 关联](#73-trace-profile-关联)
  - [8. 语义约定](#8-语义约定)
    - [8.1 Resource Attributes](#81-resource-attributes)
    - [8.2 Span Attributes](#82-span-attributes)
    - [8.3 Metric Attributes](#83-metric-attributes)
  - [9. 数据模型演进](#9-数据模型演进)
    - [9.1 版本兼容性](#91-版本兼容性)
    - [9.2 Schema URL](#92-schema-url)
    - [9.3 迁移策略](#93-迁移策略)
  - [10. 参考资料](#10-参考资料)

## 1. 引言

OTLP（OpenTelemetry Protocol）语义模型定义了可观测性数据的标准化表示方式。本文档提供了 OTLP 语义模型的全面概览，涵盖 Trace、Metric、Log 和 Profile 四种信号类型。

**语义模型的核心目标**：

1. **标准化** - 统一的数据表示格式
2. **互操作性** - 跨系统、跨语言的数据交换
3. **可扩展性** - 支持未来的功能扩展
4. **向后兼容** - 保证版本间的兼容性

## 2. 语义模型核心概念

### 2.1 Resource（资源）

Resource 描述了生成遥测数据的实体（服务、主机、容器等）。

**核心属性**：

```protobuf
message Resource {
  repeated KeyValue attributes = 1;
  uint32 dropped_attributes_count = 2;
}
```

**常见 Resource 属性**：

| 属性 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `service.name` | string | 服务名称 | `payment-service` |
| `service.version` | string | 服务版本 | `1.2.3` |
| `service.namespace` | string | 服务命名空间 | `production` |
| `deployment.environment` | string | 部署环境 | `prod`, `staging` |
| `host.name` | string | 主机名 | `server-01` |
| `host.id` | string | 主机 ID | `i-1234567890abcdef0` |
| `k8s.pod.name` | string | Pod 名称 | `payment-service-7d9f8b-xyz` |
| `k8s.namespace.name` | string | K8s 命名空间 | `default` |
| `cloud.provider` | string | 云提供商 | `aws`, `gcp`, `azure` |
| `cloud.region` | string | 云区域 | `us-west-2` |

### 2.2 Instrumentation Scope（仪表范围）

Instrumentation Scope 标识生成遥测数据的库或模块。

```protobuf
message InstrumentationScope {
  string name = 1;
  string version = 2;
  repeated KeyValue attributes = 3;
  uint32 dropped_attributes_count = 4;
}
```

**示例**：

```go
scope := instrumentation.Scope{
    Name:    "github.com/myorg/payment-service",
    Version: "1.0.0",
}
```

### 2.3 Signal Types（信号类型）

OTLP 支持四种主要信号类型：

| 信号类型 | 用途 | 典型场景 |
|---------|------|---------|
| **Trace** | 分布式追踪 | 请求链路、性能分析 |
| **Metric** | 指标监控 | CPU、内存、QPS |
| **Log** | 结构化日志 | 错误日志、审计日志 |
| **Profile** | 性能剖析 | CPU、内存、Goroutine |

## 3. Trace 语义模型

### 3.1 Span 结构

Span 是 Trace 的基本单位，表示一个操作或工作单元。

```protobuf
message Span {
  bytes trace_id = 1;                    // 128-bit Trace ID
  bytes span_id = 2;                     // 64-bit Span ID
  string trace_state = 3;                // W3C Trace State
  bytes parent_span_id = 4;              // 父 Span ID
  string name = 5;                       // Span 名称
  SpanKind kind = 6;                     // Span 类型
  fixed64 start_time_unix_nano = 7;     // 开始时间
  fixed64 end_time_unix_nano = 8;       // 结束时间
  repeated KeyValue attributes = 9;      // 属性
  repeated Event events = 10;            // 事件
  repeated Link links = 11;              // 链接
  Status status = 12;                    // 状态
}
```

### 3.2 Span 关系

**Span 类型（SpanKind）**：

```go
const (
    SpanKindUnspecified SpanKind = 0
    SpanKindInternal    SpanKind = 1  // 内部操作
    SpanKindServer      SpanKind = 2  // 服务端接收
    SpanKindClient      SpanKind = 3  // 客户端发送
    SpanKindProducer    SpanKind = 4  // 消息生产者
    SpanKindConsumer    SpanKind = 5  // 消息消费者
)
```

**Span 关系图**：

```text
Trace (trace_id: abc123)
│
├─ Span A (Server)
│  ├─ Span B (Internal)
│  │  └─ Span C (Client) → 调用外部服务
│  └─ Span D (Internal)
│     └─ Span E (Client) → 数据库查询
```

### 3.3 Span 状态

```protobuf
message Status {
  string message = 2;
  StatusCode code = 3;
}

enum StatusCode {
  STATUS_CODE_UNSET = 0;
  STATUS_CODE_OK = 1;
  STATUS_CODE_ERROR = 2;
}
```

## 4. Metric 语义模型

### 4.1 Metric 类型

OTLP 支持六种 Metric 类型：

| 类型 | 说明 | 用途 | 示例 |
|------|------|------|------|
| **Gauge** | 瞬时值 | 当前状态 | CPU 使用率、内存使用 |
| **Sum** | 累计值 | 单调递增/任意变化 | 请求总数、错误计数 |
| **Histogram** | 分布统计 | 延迟、大小分布 | HTTP 响应时间 |
| **ExponentialHistogram** | 指数直方图 | 高精度分布 | 精确延迟分布 |
| **Summary** | 摘要统计 | 分位数 | P50、P95、P99 |

**Metric 数据结构**：

```protobuf
message Metric {
  string name = 1;
  string description = 2;
  string unit = 3;
  oneof data {
    Gauge gauge = 5;
    Sum sum = 7;
    Histogram histogram = 9;
    ExponentialHistogram exponential_histogram = 10;
    Summary summary = 11;
  }
}
```

### 4.2 Aggregation Temporality

**聚合时间性**定义了 Metric 数据点的时间语义：

```go
const (
    // 未指定
    AggregationTemporalityUnspecified AggregationTemporality = 0
    
    // Delta：增量值（两次采集之间的变化）
    AggregationTemporalityDelta AggregationTemporality = 1
    
    // Cumulative：累计值（从开始到现在的总和）
    AggregationTemporalityCumulative AggregationTemporality = 2
)
```

**对比**：

| 特性 | Delta | Cumulative |
|------|-------|------------|
| 存储效率 | 高 | 低 |
| 查询复杂度 | 需要聚合 | 直接查询 |
| 适用场景 | 短期监控 | 长期趋势 |

### 4.3 Exemplars

Exemplars 将 Metric 与具体的 Trace 关联：

```protobuf
message Exemplar {
  repeated KeyValue filtered_attributes = 7;
  fixed64 time_unix_nano = 2;
  oneof value {
    double as_double = 3;
    sfixed64 as_int = 6;
  }
  bytes span_id = 4;      // 关联的 Span ID
  bytes trace_id = 5;     // 关联的 Trace ID
}
```

## 5. Log 语义模型

### 5.1 LogRecord 结构

```protobuf
message LogRecord {
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 11;
  SeverityNumber severity_number = 2;
  string severity_text = 3;
  AnyValue body = 5;
  repeated KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  uint32 flags = 8;
  bytes trace_id = 9;
  bytes span_id = 10;
}
```

### 5.2 Severity

**Severity 级别**：

| 级别 | 数值范围 | 说明 |
|------|---------|------|
| TRACE | 1-4 | 最详细的调试信息 |
| DEBUG | 5-8 | 调试信息 |
| INFO | 9-12 | 一般信息 |
| WARN | 13-16 | 警告信息 |
| ERROR | 17-20 | 错误信息 |
| FATAL | 21-24 | 致命错误 |

### 5.3 Body 类型

LogRecord 的 Body 支持多种类型：

```protobuf
message AnyValue {
  oneof value {
    string string_value = 1;
    bool bool_value = 2;
    int64 int_value = 3;
    double double_value = 4;
    ArrayValue array_value = 5;
    KeyValueList kvlist_value = 6;
    bytes bytes_value = 7;
  }
}
```

## 6. Profile 语义模型

### 6.1 Profile 结构

Profile 数据基于 pprof 格式：

```protobuf
message Profile {
  repeated ValueType sample_type = 1;
  repeated Sample sample = 2;
  repeated Mapping mapping = 3;
  repeated Location location = 4;
  repeated Function function = 5;
  repeated string string_table = 6;
  int64 time_nanos = 9;
  int64 duration_nanos = 10;
  ValueType period_type = 11;
  int64 period = 12;
}
```

### 6.2 Sample 类型

常见的 Profile 类型：

| 类型 | 说明 | 单位 |
|------|------|------|
| `cpu` | CPU 使用 | nanoseconds |
| `alloc_objects` | 分配对象数 | count |
| `alloc_space` | 分配内存 | bytes |
| `inuse_objects` | 使用中对象数 | count |
| `inuse_space` | 使用中内存 | bytes |
| `goroutine` | Goroutine 数量 | count |

### 6.3 Stack Trace

```protobuf
message Sample {
  repeated uint64 location_id = 1;
  repeated int64 value = 2;
  repeated Label label = 3;
}

message Location {
  uint64 id = 1;
  uint64 mapping_id = 2;
  uint64 address = 3;
  repeated Line line = 4;
}
```

## 7. 跨信号关联

### 7.1 Trace-Metric 关联

通过 Exemplars 将 Metric 与 Trace 关联：

```go
// Metric 数据点包含 Exemplar
exemplar := Exemplar{
    TraceID: span.SpanContext().TraceID(),
    SpanID:  span.SpanContext().SpanID(),
    Value:   latency,
}
```

### 7.2 Trace-Log 关联

LogRecord 包含 Trace 上下文：

```go
logRecord := LogRecord{
    TraceID: span.SpanContext().TraceID(),
    SpanID:  span.SpanContext().SpanID(),
    Body:    "Payment processed successfully",
}
```

### 7.3 Trace-Profile 关联

Profile 样本包含 Trace 标签：

```go
labels := pprof.Labels(
    "trace_id", span.SpanContext().TraceID().String(),
    "span_id", span.SpanContext().SpanID().String(),
)
pprof.Do(ctx, labels, func(ctx context.Context) {
    // 执行需要 profiling 的代码
})
```

## 8. 语义约定

### 8.1 Resource Attributes

**通用属性**：

- `service.*` - 服务相关
- `deployment.*` - 部署相关
- `host.*` - 主机相关
- `container.*` - 容器相关
- `k8s.*` - Kubernetes 相关
- `cloud.*` - 云平台相关

### 8.2 Span Attributes

**HTTP 属性**：

- `http.method` - HTTP 方法
- `http.url` - 完整 URL
- `http.status_code` - 状态码
- `http.request.body.size` - 请求体大小
- `http.response.body.size` - 响应体大小

**数据库属性**：

- `db.system` - 数据库系统（mysql, postgresql）
- `db.name` - 数据库名称
- `db.statement` - SQL 语句
- `db.operation` - 操作类型（SELECT, INSERT）

### 8.3 Metric Attributes

**系统指标**：

- `system.cpu.utilization` - CPU 使用率
- `system.memory.usage` - 内存使用
- `system.disk.io` - 磁盘 I/O
- `system.network.io` - 网络 I/O

## 9. 数据模型演进

### 9.1 版本兼容性

OTLP 遵循语义化版本控制：

- **主版本** - 不兼容的 API 变更
- **次版本** - 向后兼容的功能新增
- **修订版本** - 向后兼容的问题修复

### 9.2 Schema URL

Schema URL 标识数据模型版本：

```go
resource := resource.NewWithAttributes(
    semconv.SchemaURL,  // "https://opentelemetry.io/schemas/1.24.0"
    semconv.ServiceName("my-service"),
)
```

### 9.3 迁移策略

**平滑迁移步骤**：

1. **评估影响** - 检查 API 变更
2. **更新依赖** - 升级 SDK 版本
3. **测试验证** - 在测试环境验证
4. **灰度发布** - 逐步推广到生产
5. **监控观察** - 确保数据正确性

## 10. 参考资料

- **OTLP 规范**: <https://github.com/open-telemetry/opentelemetry-proto>
- **语义约定**: <https://github.com/open-telemetry/semantic-conventions>
- **Go SDK**: <https://github.com/open-telemetry/opentelemetry-go>
- **详细实现**: `docs/otlp/semantic-model.md`
- **形式化定义**: `docs/analysis/semantic-model/formal-definition.md`
- **Go 实现映射**: `docs/analysis/semantic-model/go-implementation.md`

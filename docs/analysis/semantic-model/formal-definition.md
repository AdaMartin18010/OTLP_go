# OTLP 语义模型形式化定义

## 目录

- [OTLP 语义模型形式化定义](#otlp-语义模型形式化定义)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 基础类型定义](#2-基础类型定义)
    - [2.1 基本类型](#21-基本类型)
    - [2.2 Resource 定义](#22-resource-定义)
  - [3. Trace 形式化定义](#3-trace-形式化定义)
    - [3.1 Span 定义](#31-span-定义)
    - [3.2 Trace 定义](#32-trace-定义)
    - [3.3 Span 关系](#33-span-关系)
    - [3.4 时间约束](#34-时间约束)
  - [4. Metric 形式化定义](#4-metric-形式化定义)
    - [4.1 Metric 基础定义](#41-metric-基础定义)
    - [4.2 Gauge 定义](#42-gauge-定义)
    - [4.3 Sum 定义](#43-sum-定义)
    - [4.4 Histogram 定义](#44-histogram-定义)
  - [5. Log 形式化定义](#5-log-形式化定义)
    - [5.1 LogRecord 定义](#51-logrecord-定义)
    - [5.2 Severity 层次](#52-severity-层次)
  - [6. 不变量与约束](#6-不变量与约束)
    - [6.1 全局不变量](#61-全局不变量)
    - [6.2 时间一致性](#62-时间一致性)
    - [6.3 关联一致性](#63-关联一致性)
    - [6.4 数据完整性](#64-数据完整性)
  - [7. 参考资料](#7-参考资料)

## 1. 引言

本文档提供 OTLP 语义模型的形式化数学定义，为系统验证和正确性证明提供基础。

## 2. 基础类型定义

### 2.1 基本类型

```math
// 时间戳（纳秒）
Timestamp = ℕ

// 标识符
TraceID = {0,1}^128
SpanID = {0,1}^64

// 属性
Attribute = String × Value
where Value = String | Int64 | Float64 | Bool | Array[Value] | Map[String, Value]
```

### 2.2 Resource 定义

```math
Resource = {
    attributes: Set[Attribute],
    dropped_attributes_count: ℕ
}

// 不变量
∀r ∈ Resource: |r.attributes| + r.dropped_attributes_count ≥ 0
```

## 3. Trace 形式化定义

### 3.1 Span 定义

```math
Span = {
    trace_id: TraceID,
    span_id: SpanID,
    parent_span_id: Option[SpanID],
    name: String,
    kind: SpanKind,
    start_time: Timestamp,
    end_time: Timestamp,
    attributes: Set[Attribute],
    events: Seq[Event],
    links: Set[Link],
    status: Status
}

where
    SpanKind ∈ {INTERNAL, SERVER, CLIENT, PRODUCER, CONSUMER}
    Status = {code: StatusCode, message: String}
    StatusCode ∈ {UNSET, OK, ERROR}
```

### 3.2 Trace 定义

```math
Trace = {
    trace_id: TraceID,
    spans: Set[Span]
}

// 约束条件
∀t ∈ Trace, ∀s ∈ t.spans: s.trace_id = t.trace_id
```

### 3.3 Span 关系

```math
// 父子关系
parent_of: Span × Span → Bool
parent_of(s1, s2) ≡ s2.parent_span_id = Some(s1.span_id) ∧ s1.trace_id = s2.trace_id

// 祖先关系（传递闭包）
ancestor_of: Span × Span → Bool
ancestor_of(s1, s2) ≡ parent_of(s1, s2) ∨ ∃s3: parent_of(s1, s3) ∧ ancestor_of(s3, s2)

// 根 Span
is_root: Span → Bool
is_root(s) ≡ s.parent_span_id = None
```

### 3.4 时间约束

```math
// Span 时间有效性
∀s ∈ Span: s.start_time ≤ s.end_time

// 父子 Span 时间包含关系
∀s1, s2 ∈ Span: parent_of(s1, s2) ⟹ 
    s1.start_time ≤ s2.start_time ∧ s2.end_time ≤ s1.end_time
```

## 4. Metric 形式化定义

### 4.1 Metric 基础定义

```math
Metric = {
    name: String,
    description: String,
    unit: String,
    data: MetricData
}

where MetricData = Gauge | Sum | Histogram | ExponentialHistogram | Summary
```

### 4.2 Gauge 定义

```math
Gauge = {
    data_points: Seq[NumberDataPoint]
}

NumberDataPoint = {
    attributes: Set[Attribute],
    start_time: Timestamp,
    time: Timestamp,
    value: Float64 | Int64,
    exemplars: Seq[Exemplar]
}
```

### 4.3 Sum 定义

```math
Sum = {
    data_points: Seq[NumberDataPoint],
    aggregation_temporality: AggregationTemporality,
    is_monotonic: Bool
}

where AggregationTemporality ∈ {DELTA, CUMULATIVE}

// 单调性约束
∀s ∈ Sum: s.is_monotonic = true ⟹
    ∀i, j: i < j ⟹ s.data_points[i].value ≤ s.data_points[j].value
```

### 4.4 Histogram 定义

```math
Histogram = {
    data_points: Seq[HistogramDataPoint],
    aggregation_temporality: AggregationTemporality
}

HistogramDataPoint = {
    attributes: Set[Attribute],
    start_time: Timestamp,
    time: Timestamp,
    count: ℕ,
    sum: Float64,
    bucket_counts: Seq[ℕ],
    explicit_bounds: Seq[Float64],
    exemplars: Seq[Exemplar],
    min: Option[Float64],
    max: Option[Float64]
}

// 约束条件
∀h ∈ HistogramDataPoint:
    // 桶数量一致性
    |h.bucket_counts| = |h.explicit_bounds| + 1 ∧
    // 总计数一致性
    h.count = Σ h.bucket_counts ∧
    // 边界单调性
    ∀i, j: i < j ⟹ h.explicit_bounds[i] < h.explicit_bounds[j]
```

## 5. Log 形式化定义

### 5.1 LogRecord 定义

```math
LogRecord = {
    time: Timestamp,
    observed_time: Timestamp,
    severity_number: SeverityNumber,
    severity_text: String,
    body: AnyValue,
    attributes: Set[Attribute],
    trace_id: Option[TraceID],
    span_id: Option[SpanID],
    flags: ℕ
}

where SeverityNumber ∈ [1, 24] ∩ ℕ
```

### 5.2 Severity 层次

```math
// Severity 级别映射
severity_level: SeverityNumber → Level
severity_level(n) = 
    | TRACE if 1 ≤ n ≤ 4
    | DEBUG if 5 ≤ n ≤ 8
    | INFO  if 9 ≤ n ≤ 12
    | WARN  if 13 ≤ n ≤ 16
    | ERROR if 17 ≤ n ≤ 20
    | FATAL if 21 ≤ n ≤ 24

// Severity 比较
severity_compare: SeverityNumber × SeverityNumber → {LT, EQ, GT}
severity_compare(n1, n2) = 
    | LT if n1 < n2
    | EQ if n1 = n2
    | GT if n1 > n2
```

## 6. 不变量与约束

### 6.1 全局不变量

```math
// 1. TraceID 唯一性
∀t1, t2 ∈ Trace: t1 ≠ t2 ⟹ t1.trace_id ≠ t2.trace_id

// 2. SpanID 在 Trace 内唯一
∀t ∈ Trace, ∀s1, s2 ∈ t.spans: s1 ≠ s2 ⟹ s1.span_id ≠ s2.span_id

// 3. Trace 无环
∀t ∈ Trace, ∀s ∈ t.spans: ¬ancestor_of(s, s)

// 4. 每个 Trace 有且仅有一个根 Span
∀t ∈ Trace: |{s ∈ t.spans | is_root(s)}| = 1
```

### 6.2 时间一致性

```math
// 1. 观察时间不早于事件时间
∀l ∈ LogRecord: l.time ≤ l.observed_time

// 2. Metric 数据点时间单调
∀m ∈ Metric, ∀i, j: i < j ⟹ 
    m.data.data_points[i].time ≤ m.data.data_points[j].time
```

### 6.3 关联一致性

```math
// 1. Log-Trace 关联有效性
∀l ∈ LogRecord: 
    l.trace_id ≠ None ⟹ ∃t ∈ Trace: t.trace_id = l.trace_id

// 2. Exemplar-Trace 关联有效性
∀e ∈ Exemplar:
    e.trace_id ≠ None ⟹ ∃t ∈ Trace: t.trace_id = e.trace_id
```

### 6.4 数据完整性

```math
// 1. 属性数量一致性
∀x ∈ {Resource, Span, LogRecord}:
    |x.attributes| + x.dropped_attributes_count = total_attributes(x)

// 2. Histogram 数据一致性
∀h ∈ HistogramDataPoint:
    h.min ≤ h.max ∧
    (h.count > 0 ⟹ h.min ≠ None ∧ h.max ≠ None)
```

## 7. 参考资料

- **OTLP 规范**: <https://github.com/open-telemetry/opentelemetry-proto>
- **TLA+ 规范**: `docs/formal/tla/pipeline.tla`
- **Go 实现**: `docs/analysis/semantic-model/go-implementation.md`
- **验证方法**: `docs/analysis/semantic-model/validation.md`

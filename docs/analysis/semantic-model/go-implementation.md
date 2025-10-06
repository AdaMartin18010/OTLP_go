# OTLP 语义模型 Go 实现映射

## 目录

- [OTLP 语义模型 Go 实现映射](#otlp-语义模型-go-实现映射)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 类型映射](#2-类型映射)
    - [2.1 基础类型映射](#21-基础类型映射)
    - [2.2 ID 类型映射](#22-id-类型映射)
  - [3. Trace 实现](#3-trace-实现)
    - [3.1 Span 数据结构](#31-span-数据结构)
    - [3.2 SpanContext 实现](#32-spancontext-实现)
    - [3.3 Span 实现示例](#33-span-实现示例)
  - [4. Metric 实现](#4-metric-实现)
    - [4.1 Metric 接口](#41-metric-接口)
    - [4.2 Counter 实现](#42-counter-实现)
    - [4.3 Histogram 实现](#43-histogram-实现)
  - [5. Log 实现](#5-log-实现)
    - [5.1 Logger 接口](#51-logger-接口)
    - [5.2 LogRecord 构建](#52-logrecord-构建)
    - [5.3 与标准库集成](#53-与标准库集成)
  - [6. 性能优化](#6-性能优化)
    - [6.1 对象池](#61-对象池)
    - [6.2 零拷贝序列化](#62-零拷贝序列化)
    - [6.3 批量处理](#63-批量处理)
  - [7. 参考资料](#7-参考资料)

## 1. 引言

本文档详细说明 OTLP 语义模型在 Go 语言中的实现映射，包括数据结构、API 设计和性能优化。

## 2. 类型映射

### 2.1 基础类型映射

| OTLP 类型 | Go 类型 | 说明 |
|-----------|---------|------|
| `bytes` | `[]byte` | 字节数组 |
| `string` | `string` | UTF-8 字符串 |
| `int64` | `int64` | 64 位整数 |
| `uint64` | `uint64` | 64 位无符号整数 |
| `fixed64` | `uint64` | 固定 64 位 |
| `double` | `float64` | 双精度浮点 |
| `bool` | `bool` | 布尔值 |

### 2.2 ID 类型映射

```go
// TraceID: 128-bit 唯一标识符
type TraceID [16]byte

func (t TraceID) IsValid() bool {
    return t != [16]byte{}
}

func (t TraceID) String() string {
    return hex.EncodeToString(t[:])
}

// SpanID: 64-bit 唯一标识符
type SpanID [8]byte

func (s SpanID) IsValid() bool {
    return s != [8]byte{}
}

func (s SpanID) String() string {
    return hex.EncodeToString(s[:])
}
```

## 3. Trace 实现

### 3.1 Span 数据结构

```go
package trace

import (
    "time"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// ReadOnlySpan 提供只读访问
type ReadOnlySpan interface {
    Name() string
    SpanContext() SpanContext
    Parent() SpanContext
    SpanKind() SpanKind
    StartTime() time.Time
    EndTime() time.Time
    Attributes() []attribute.KeyValue
    Links() []Link
    Events() []Event
    Status() Status
    InstrumentationScope() instrumentation.Scope
    Resource() *resource.Resource
}

// ReadWriteSpan 提供读写访问
type ReadWriteSpan interface {
    ReadOnlySpan
    
    SetName(string)
    SetStatus(codes.Code, string)
    SetAttributes(...attribute.KeyValue)
    AddEvent(string, ...EventOption)
    AddLink(Link)
    End(...SpanEndOption)
}
```

### 3.2 SpanContext 实现

```go
// SpanContext 包含 Span 的不可变标识信息
type SpanContext struct {
    traceID    TraceID
    spanID     SpanID
    traceFlags TraceFlags
    traceState TraceState
    remote     bool
}

func (sc SpanContext) TraceID() TraceID {
    return sc.traceID
}

func (sc SpanContext) SpanID() SpanID {
    return sc.spanID
}

func (sc SpanContext) IsValid() bool {
    return sc.traceID.IsValid() && sc.spanID.IsValid()
}

func (sc SpanContext) IsSampled() bool {
    return sc.traceFlags&FlagsSampled == FlagsSampled
}
```

### 3.3 Span 实现示例

```go
// recordingSpan 是 Span 的具体实现
type recordingSpan struct {
    mu sync.Mutex
    
    // 不可变字段
    spanContext SpanContext
    parent      SpanContext
    spanKind    SpanKind
    startTime   time.Time
    
    // 可变字段（需要锁保护）
    name          string
    attributes    []attribute.KeyValue
    events        []Event
    links         []Link
    status        Status
    endTime       time.Time
    ended         bool
    
    // 元数据
    instrumentationScope instrumentation.Scope
    resource            *resource.Resource
}

func (s *recordingSpan) SetAttributes(attrs ...attribute.KeyValue) {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    if s.ended {
        return
    }
    
    s.attributes = append(s.attributes, attrs...)
}

func (s *recordingSpan) End(options ...SpanEndOption) {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    if s.ended {
        return
    }
    
    config := NewSpanEndConfig(options...)
    s.endTime = config.Timestamp()
    if s.endTime.IsZero() {
        s.endTime = time.Now()
    }
    
    s.ended = true
}
```

## 4. Metric 实现

### 4.1 Metric 接口

```go
package metric

// Meter 提供 Metric 仪表
type Meter interface {
    // Counter 创建单调递增计数器
    Int64Counter(name string, options ...InstrumentOption) (Int64Counter, error)
    Float64Counter(name string, options ...InstrumentOption) (Float64Counter, error)
    
    // UpDownCounter 创建可增可减计数器
    Int64UpDownCounter(name string, options ...InstrumentOption) (Int64UpDownCounter, error)
    Float64UpDownCounter(name string, options ...InstrumentOption) (Float64UpDownCounter, error)
    
    // Histogram 创建直方图
    Int64Histogram(name string, options ...InstrumentOption) (Int64Histogram, error)
    Float64Histogram(name string, options ...InstrumentOption) (Float64Histogram, error)
    
    // Gauge 创建瞬时值
    Int64ObservableGauge(name string, options ...InstrumentOption) (Int64ObservableGauge, error)
    Float64ObservableGauge(name string, options ...InstrumentOption) (Float64ObservableGauge, error)
}
```

### 4.2 Counter 实现

```go
// Int64Counter 单调递增计数器
type Int64Counter interface {
    Add(ctx context.Context, incr int64, options ...AddOption)
}

type int64Counter struct {
    instrument
    aggregator Aggregator
}

func (c *int64Counter) Add(ctx context.Context, incr int64, options ...AddOption) {
    if incr < 0 {
        // Counter 必须单调递增
        return
    }
    
    config := NewAddConfig(options...)
    attrs := config.Attributes()
    
    c.aggregator.Aggregate(ctx, incr, attrs)
}
```

### 4.3 Histogram 实现

```go
// Float64Histogram 直方图
type Float64Histogram interface {
    Record(ctx context.Context, value float64, options ...RecordOption)
}

type float64Histogram struct {
    instrument
    aggregator HistogramAggregator
}

func (h *float64Histogram) Record(ctx context.Context, value float64, options ...RecordOption) {
    config := NewRecordConfig(options...)
    attrs := config.Attributes()
    
    h.aggregator.RecordValue(ctx, value, attrs)
}

// HistogramAggregator 聚合直方图数据
type HistogramAggregator struct {
    mu sync.Mutex
    
    bounds []float64
    counts []uint64
    sum    float64
    count  uint64
    min    float64
    max    float64
}

func (a *HistogramAggregator) RecordValue(ctx context.Context, value float64, attrs attribute.Set) {
    a.mu.Lock()
    defer a.mu.Unlock()
    
    // 更新统计信息
    a.count++
    a.sum += value
    
    if a.count == 1 || value < a.min {
        a.min = value
    }
    if a.count == 1 || value > a.max {
        a.max = value
    }
    
    // 找到对应的桶
    bucket := sort.SearchFloat64s(a.bounds, value)
    a.counts[bucket]++
}
```

## 5. Log 实现

### 5.1 Logger 接口

```go
package log

// Logger 提供结构化日志记录
type Logger interface {
    Emit(ctx context.Context, record Record)
}

// Record 表示一条日志记录
type Record struct {
    timestamp         time.Time
    observedTimestamp time.Time
    severity          Severity
    severityText      string
    body              Value
    attributes        []KeyValue
    traceID           trace.TraceID
    spanID            trace.SpanID
}
```

### 5.2 LogRecord 构建

```go
// RecordBuilder 构建 LogRecord
type RecordBuilder struct {
    record Record
}

func NewRecordBuilder() *RecordBuilder {
    return &RecordBuilder{
        record: Record{
            timestamp:         time.Now(),
            observedTimestamp: time.Now(),
        },
    }
}

func (b *RecordBuilder) WithTimestamp(t time.Time) *RecordBuilder {
    b.record.timestamp = t
    return b
}

func (b *RecordBuilder) WithSeverity(severity Severity) *RecordBuilder {
    b.record.severity = severity
    return b
}

func (b *RecordBuilder) WithBody(body Value) *RecordBuilder {
    b.record.body = body
    return b
}

func (b *RecordBuilder) WithAttributes(attrs ...KeyValue) *RecordBuilder {
    b.record.attributes = append(b.record.attributes, attrs...)
    return b
}

func (b *RecordBuilder) WithTraceContext(ctx context.Context) *RecordBuilder {
    span := trace.SpanFromContext(ctx)
    if span.SpanContext().IsValid() {
        b.record.traceID = span.SpanContext().TraceID()
        b.record.spanID = span.SpanContext().SpanID()
    }
    return b
}

func (b *RecordBuilder) Build() Record {
    return b.record
}
```

### 5.3 与标准库集成

```go
// slog 集成
import "log/slog"

type OTELHandler struct {
    logger log.Logger
}

func (h *OTELHandler) Handle(ctx context.Context, r slog.Record) error {
    // 转换 slog.Record 到 OTEL Record
    record := log.Record{
        timestamp:    r.Time,
        severity:     convertSeverity(r.Level),
        severityText: r.Level.String(),
        body:         log.StringValue(r.Message),
    }
    
    // 添加属性
    r.Attrs(func(a slog.Attr) bool {
        record.attributes = append(record.attributes, 
            log.String(a.Key, a.Value.String()))
        return true
    })
    
    // 添加 Trace 上下文
    if span := trace.SpanFromContext(ctx); span.SpanContext().IsValid() {
        record.traceID = span.SpanContext().TraceID()
        record.spanID = span.SpanContext().SpanID()
    }
    
    h.logger.Emit(ctx, record)
    return nil
}
```

## 6. 性能优化

### 6.1 对象池

```go
// Span 对象池
var spanPool = sync.Pool{
    New: func() interface{} {
        return &recordingSpan{
            attributes: make([]attribute.KeyValue, 0, 16),
            events:     make([]Event, 0, 8),
            links:      make([]Link, 0, 4),
        }
    },
}

func acquireSpan() *recordingSpan {
    return spanPool.Get().(*recordingSpan)
}

func releaseSpan(s *recordingSpan) {
    // 重置状态
    s.name = ""
    s.attributes = s.attributes[:0]
    s.events = s.events[:0]
    s.links = s.links[:0]
    s.ended = false
    
    spanPool.Put(s)
}
```

### 6.2 零拷贝序列化

```go
// 使用 protobuf 的零拷贝特性
func (s *recordingSpan) MarshalTo(buf []byte) (int, error) {
    // 直接写入预分配的缓冲区
    n := 0
    
    // TraceID
    copy(buf[n:], s.spanContext.traceID[:])
    n += 16
    
    // SpanID
    copy(buf[n:], s.spanContext.spanID[:])
    n += 8
    
    // ... 其他字段
    
    return n, nil
}
```

### 6.3 批量处理

```go
// BatchSpanProcessor 批量处理 Span
type BatchSpanProcessor struct {
    queue   chan ReadOnlySpan
    batch   []ReadOnlySpan
    timer   *time.Timer
    maxSize int
    timeout time.Duration
}

func (bsp *BatchSpanProcessor) OnEnd(s ReadOnlySpan) {
    select {
    case bsp.queue <- s:
    default:
        // 队列满，丢弃
    }
}

func (bsp *BatchSpanProcessor) processQueue() {
    for {
        select {
        case span := <-bsp.queue:
            bsp.batch = append(bsp.batch, span)
            
            if len(bsp.batch) >= bsp.maxSize {
                bsp.flush()
            }
            
        case <-bsp.timer.C:
            if len(bsp.batch) > 0 {
                bsp.flush()
            }
            bsp.timer.Reset(bsp.timeout)
        }
    }
}

func (bsp *BatchSpanProcessor) flush() {
    // 批量导出
    bsp.exporter.ExportSpans(context.Background(), bsp.batch)
    bsp.batch = bsp.batch[:0]
}
```

## 7. 参考资料

- **OpenTelemetry Go SDK**: <https://github.com/open-telemetry/opentelemetry-go>
- **Go 1.25.1 特性**: `docs/language/go-1.25.1.md`
- **语义模型**: `docs/otlp/semantic-model.md`
- **性能优化**: `docs/implementation/PHASE2_OPTIMIZATION_SUMMARY.md`

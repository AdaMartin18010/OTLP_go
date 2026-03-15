# LogRecord 结构

## 📋 目录

- [LogRecord 结构](#logrecord-结构)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 LogRecord](#什么是-logrecord)
    - [为什么需要 LogRecord](#为什么需要-logrecord)
  - [LogRecord 数据结构](#logrecord-数据结构)
    - [1. 完整字段定义](#1-完整字段定义)
    - [2. Protocol Buffers 定义](#2-protocol-buffers-定义)
    - [3. Go 结构体定义](#3-go-结构体定义)
  - [核心字段详解](#核心字段详解)
    - [1. Timestamp (时间戳)](#1-timestamp-时间戳)
    - [2. ObservedTimestamp (观测时间戳)](#2-observedtimestamp-观测时间戳)
    - [3. SeverityNumber (严重性数值)](#3-severitynumber-严重性数值)
    - [4. SeverityText (严重性文本)](#4-severitytext-严重性文本)
    - [5. Body (日志主体)](#5-body-日志主体)
    - [6. Attributes (属性)](#6-attributes-属性)
    - [7. TraceID 和 SpanID](#7-traceid-和-spanid)
    - [8. TraceFlags](#8-traceflags)
    - [9. DroppedAttributesCount](#9-droppedattributescount)
  - [LogRecord 生命周期](#logrecord-生命周期)
    - [1. 创建阶段](#1-创建阶段)
    - [2. 填充阶段](#2-填充阶段)
    - [3. 处理阶段](#3-处理阶段)
    - [4. 导出阶段](#4-导出阶段)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本实现](#1-基本实现)
    - [2. LogRecord 构建器](#2-logrecord-构建器)
    - [3. 与 slog 集成](#3-与-slog-集成)
    - [4. 批处理实现](#4-批处理实现)
  - [高级特性](#高级特性)
    - [1. 结构化 Body](#1-结构化-body)
    - [2. 嵌套属性](#2-嵌套属性)
    - [3. 数组和 Map](#3-数组和-map)
    - [4. 自定义类型](#4-自定义类型)
  - [性能优化](#性能优化)
    - [1. 零分配日志](#1-零分配日志)
    - [2. 对象池复用](#2-对象池复用)
    - [3. 批量处理](#3-批量处理)
    - [4. 延迟字段计算](#4-延迟字段计算)
  - [最佳实践](#最佳实践)
    - [1. 字段使用规范](#1-字段使用规范)
    - [2. Body 设计](#2-body-设计)
    - [3. Attributes 管理](#3-attributes-管理)
    - [4. 时间戳处理](#4-时间戳处理)
  - [常见问题](#常见问题)
    - [Q1: Timestamp 和 ObservedTimestamp 的区别？](#q1-timestamp-和-observedtimestamp-的区别)
    - [Q2: Body 应该使用 string 还是结构化数据？](#q2-body-应该使用-string-还是结构化数据)
    - [Q3: 如何关联 Logs 和 Traces？](#q3-如何关联-logs-和-traces)
    - [Q4: 如何处理大量属性？](#q4-如何处理大量属性)
    - [Q5: 如何优化日志性能？](#q5-如何优化日志性能)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 LogRecord

**LogRecord** 是 OpenTelemetry Logs 数据模型的核心数据结构，代表单个日志条目。

```text
LogRecord = {
  时间信息 + 严重性 + 日志主体 + 属性 + 追踪上下文
}
```

### 为什么需要 LogRecord

```text
传统日志的问题:
❌ 格式不统一 (纯文本, JSON, 自定义)
❌ 缺乏结构化
❌ 难以与追踪关联
❌ 没有标准化字段

OpenTelemetry LogRecord 的优势:
✅ 标准化数据结构
✅ 完整的结构化支持
✅ 内置追踪关联 (TraceID/SpanID)
✅ 丰富的元数据 (Attributes)
✅ 统一的严重性级别
```

---

## LogRecord 数据结构

### 1. 完整字段定义

| 字段 | 类型 | 必需 | 描述 |
|------|------|------|------|
| `Timestamp` | uint64 | 否 | 日志事件发生的时间 (Unix 纳秒) |
| `ObservedTimestamp` | uint64 | 是 | 日志被观测/收集的时间 (Unix 纳秒) |
| `SeverityNumber` | enum | 否 | 严重性数值 (1-24) |
| `SeverityText` | string | 否 | 严重性文本 (INFO, ERROR, etc.) |
| `Body` | AnyValue | 否 | 日志主体内容 |
| `Attributes` | KeyValue[] | 否 | 键值对属性 |
| `DroppedAttributesCount` | uint32 | 否 | 被丢弃的属性数量 |
| `TraceId` | bytes | 否 | 追踪 ID (16 bytes) |
| `SpanId` | bytes | 否 | Span ID (8 bytes) |
| `TraceFlags` | uint32 | 否 | 追踪标志 |

### 2. Protocol Buffers 定义

```protobuf
message LogRecord {
  // 时间信息
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 11;
  
  // 严重性
  SeverityNumber severity_number = 2;
  string severity_text = 3;
  
  // 内容
  opentelemetry.proto.common.v1.AnyValue body = 5;
  
  // 属性
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  
  // 追踪上下文
  bytes trace_id = 8;
  bytes span_id = 9;
  uint32 flags = 10;
}

enum SeverityNumber {
  SEVERITY_NUMBER_UNSPECIFIED = 0;
  SEVERITY_NUMBER_TRACE = 1;
  SEVERITY_NUMBER_TRACE2 = 2;
  SEVERITY_NUMBER_TRACE3 = 3;
  SEVERITY_NUMBER_TRACE4 = 4;
  SEVERITY_NUMBER_DEBUG = 5;
  SEVERITY_NUMBER_DEBUG2 = 6;
  SEVERITY_NUMBER_DEBUG3 = 7;
  SEVERITY_NUMBER_DEBUG4 = 8;
  SEVERITY_NUMBER_INFO = 9;
  SEVERITY_NUMBER_INFO2 = 10;
  SEVERITY_NUMBER_INFO3 = 11;
  SEVERITY_NUMBER_INFO4 = 12;
  SEVERITY_NUMBER_WARN = 13;
  SEVERITY_NUMBER_WARN2 = 14;
  SEVERITY_NUMBER_WARN3 = 15;
  SEVERITY_NUMBER_WARN4 = 16;
  SEVERITY_NUMBER_ERROR = 17;
  SEVERITY_NUMBER_ERROR2 = 18;
  SEVERITY_NUMBER_ERROR3 = 19;
  SEVERITY_NUMBER_ERROR4 = 20;
  SEVERITY_NUMBER_FATAL = 21;
  SEVERITY_NUMBER_FATAL2 = 22;
  SEVERITY_NUMBER_FATAL3 = 23;
  SEVERITY_NUMBER_FATAL4 = 24;
}
```

### 3. Go 结构体定义

```go
package logmodel

import (
    "time"
    
    "go.opentelemetry.io/otel/trace"
    "go.opentelemetry.io/proto/otlp/common/v1"
    "go.opentelemetry.io/proto/otlp/logs/v1"
)

// LogRecord 表示单个日志条目
type LogRecord struct {
    // 时间信息
    Timestamp         time.Time // 日志事件发生时间
    ObservedTimestamp time.Time // 日志被观测时间
    
    // 严重性
    SeverityNumber SeverityNumber // 严重性数值
    SeverityText   string         // 严重性文本
    
    // 内容
    Body *AnyValue // 日志主体
    
    // 属性
    Attributes              map[string]*AnyValue // 属性键值对
    DroppedAttributesCount  uint32               // 被丢弃的属性数量
    
    // 追踪上下文
    TraceID    trace.TraceID // 追踪 ID
    SpanID     trace.SpanID  // Span ID
    TraceFlags trace.TraceFlags // 追踪标志
}

// SeverityNumber 严重性数值 (1-24)
type SeverityNumber int32

const (
    SeverityNumberUnspecified SeverityNumber = 0
    SeverityNumberTrace       SeverityNumber = 1
    SeverityNumberTrace2      SeverityNumber = 2
    SeverityNumberTrace3      SeverityNumber = 3
    SeverityNumberTrace4      SeverityNumber = 4
    SeverityNumberDebug       SeverityNumber = 5
    SeverityNumberDebug2      SeverityNumber = 6
    SeverityNumberDebug3      SeverityNumber = 7
    SeverityNumberDebug4      SeverityNumber = 8
    SeverityNumberInfo        SeverityNumber = 9
    SeverityNumberInfo2       SeverityNumber = 10
    SeverityNumberInfo3       SeverityNumber = 11
    SeverityNumberInfo4       SeverityNumber = 12
    SeverityNumberWarn        SeverityNumber = 13
    SeverityNumberWarn2       SeverityNumber = 14
    SeverityNumberWarn3       SeverityNumber = 15
    SeverityNumberWarn4       SeverityNumber = 16
    SeverityNumberError       SeverityNumber = 17
    SeverityNumberError2      SeverityNumber = 18
    SeverityNumberError3      SeverityNumber = 19
    SeverityNumberError4      SeverityNumber = 20
    SeverityNumberFatal       SeverityNumber = 21
    SeverityNumberFatal2      SeverityNumber = 22
    SeverityNumberFatal3      SeverityNumber = 23
    SeverityNumberFatal4      SeverityNumber = 24
)

// AnyValue 可以是任意类型的值
type AnyValue struct {
    // 只有一个字段会被设置
    StringValue  *string
    BoolValue    *bool
    IntValue     *int64
    DoubleValue  *float64
    ArrayValue   *ArrayValue
    KvListValue  *KeyValueList
    BytesValue   []byte
}

// ArrayValue 数组值
type ArrayValue struct {
    Values []*AnyValue
}

// KeyValueList 键值对列表
type KeyValueList struct {
    Values []*KeyValue
}

// KeyValue 键值对
type KeyValue struct {
    Key   string
    Value *AnyValue
}
```

---

## 核心字段详解

### 1. Timestamp (时间戳)

**定义**: 日志事件实际发生的时间。

**特点**:

- 类型: `uint64` (Unix 纳秒)
- 可选字段 (如果未设置，使用 ObservedTimestamp)
- 由日志生成者设置

**使用场景**:

```text
✅ 应用程序记录事件时间
✅ 重放历史日志
✅ 精确的事件排序
```

**Go 实现**:

```go
// 设置 Timestamp
record.Timestamp = time.Now()

// 从 Unix 纳秒转换
record.Timestamp = time.Unix(0, int64(timestampNanos))

// 转换为 Unix 纳秒
nanos := uint64(record.Timestamp.UnixNano())
```

### 2. ObservedTimestamp (观测时间戳)

**定义**: 日志被 SDK/Collector 观测到的时间。

**特点**:

- 类型: `uint64` (Unix 纳秒)
- **必需字段** (唯一必需的时间戳)
- 由日志收集器设置

**使用场景**:

```text
✅ 日志收集时间记录
✅ 计算传输延迟 (ObservedTimestamp - Timestamp)
✅ 时间校准
```

**Go 实现**:

```go
// 设置 ObservedTimestamp (通常由 SDK 自动设置)
record.ObservedTimestamp = time.Now()

// 计算延迟
delay := record.ObservedTimestamp.Sub(record.Timestamp)
fmt.Printf("Log delay: %v\n", delay)
```

### 3. SeverityNumber (严重性数值)

**定义**: 标准化的严重性级别 (1-24)。

**级别映射**:

```text
 1-4:  TRACE  (最详细的调试信息)
 5-8:  DEBUG  (调试信息)
 9-12: INFO   (正常信息)
13-16: WARN   (警告)
17-20: ERROR  (错误)
21-24: FATAL  (致命错误)
```

**Go 实现**:

```go
// 设置 SeverityNumber
record.SeverityNumber = SeverityNumberInfo

// 从 slog.Level 转换
func SlogLevelToSeverity(level slog.Level) SeverityNumber {
    switch {
    case level < slog.LevelDebug:
        return SeverityNumberTrace
    case level < slog.LevelInfo:
        return SeverityNumberDebug
    case level < slog.LevelWarn:
        return SeverityNumberInfo
    case level < slog.LevelError:
        return SeverityNumberWarn
    default:
        return SeverityNumberError
    }
}
```

### 4. SeverityText (严重性文本)

**定义**: 原始的严重性文本 (如 "INFO", "ERROR")。

**特点**:

- 保留原始日志系统的级别名称
- 方便人类阅读
- 可以自定义 (如 "CRITICAL", "NOTICE")

**Go 实现**:

```go
record.SeverityText = "INFO"

// 从 SeverityNumber 生成默认文本
func (s SeverityNumber) String() string {
    switch {
    case s >= SeverityNumberFatal:
        return "FATAL"
    case s >= SeverityNumberError:
        return "ERROR"
    case s >= SeverityNumberWarn:
        return "WARN"
    case s >= SeverityNumberInfo:
        return "INFO"
    case s >= SeverityNumberDebug:
        return "DEBUG"
    case s >= SeverityNumberTrace:
        return "TRACE"
    default:
        return "UNSPECIFIED"
    }
}
```

### 5. Body (日志主体)

**定义**: 日志的主要内容。

**类型**:

```text
✅ String:  纯文本消息
✅ Int:     整数值
✅ Double:  浮点数
✅ Bool:    布尔值
✅ Bytes:   二进制数据
✅ Array:   数组
✅ KvList:  键值对列表 (结构化日志)
```

**Go 实现**:

```go
// 字符串 Body
record.Body = &AnyValue{
    StringValue: strPtr("User login successful"),
}

// 结构化 Body
record.Body = &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "event", Value: &AnyValue{StringValue: strPtr("user.login")}},
            {Key: "user_id", Value: &AnyValue{StringValue: strPtr("12345")}},
            {Key: "success", Value: &AnyValue{BoolValue: boolPtr(true)}},
        },
    },
}

func strPtr(s string) *string { return &s }
func boolPtr(b bool) *bool { return &b }
```

### 6. Attributes (属性)

**定义**: 日志的附加元数据。

**常用属性**:

```text
✅ http.method          - HTTP 方法
✅ http.status_code     - HTTP 状态码
✅ user.id              - 用户 ID
✅ error.type           - 错误类型
✅ db.statement         - 数据库语句
```

**Go 实现**:

```go
record.Attributes = map[string]*AnyValue{
    "http.method": {StringValue: strPtr("GET")},
    "http.url": {StringValue: strPtr("/api/users")},
    "http.status_code": {IntValue: int64Ptr(200)},
    "user.id": {StringValue: strPtr("12345")},
}

func int64Ptr(i int64) *int64 { return &i }
```

### 7. TraceID 和 SpanID

**定义**: 关联日志到分布式追踪。

**特点**:

- TraceID: 16 bytes (128 bits)
- SpanID: 8 bytes (64 bits)
- 支持 W3C Trace Context

**Go 实现**:

```go
import (
    "context"
    "go.opentelemetry.io/otel/trace"
)

// 从 Context 提取 TraceID/SpanID
func ExtractTraceContext(ctx context.Context, record *LogRecord) {
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        record.TraceID = spanCtx.TraceID()
        record.SpanID = spanCtx.SpanID()
        record.TraceFlags = spanCtx.TraceFlags()
    }
}

// 使用
ctx := context.Background()
span := trace.SpanFromContext(ctx)
ExtractTraceContext(ctx, record)
```

### 8. TraceFlags

**定义**: 追踪标志位。

**标志**:

- `0x01`: Sampled (已采样)
- 其他位保留

**Go 实现**:

```go
// 检查是否被采样
if record.TraceFlags.IsSampled() {
    // 日志被采样，导出到后端
}
```

### 9. DroppedAttributesCount

**定义**: 因限制而被丢弃的属性数量。

**使用场景**:

```text
✅ 监控属性丢失
✅ 调整属性限制
✅ 检测基数问题
```

**Go 实现**:

```go
const MaxAttributes = 128

func AddAttribute(record *LogRecord, key string, value *AnyValue) {
    if len(record.Attributes) >= MaxAttributes {
        record.DroppedAttributesCount++
        return
    }
    record.Attributes[key] = value
}
```

---

## LogRecord 生命周期

### 1. 创建阶段

```go
// 创建 LogRecord
func NewLogRecord() *LogRecord {
    return &LogRecord{
        ObservedTimestamp: time.Now(), // 必需
        Attributes:        make(map[string]*AnyValue),
    }
}
```

### 2. 填充阶段

```go
// 填充字段
record := NewLogRecord()
record.Timestamp = time.Now()
record.SeverityNumber = SeverityNumberInfo
record.SeverityText = "INFO"
record.Body = &AnyValue{StringValue: strPtr("User login")}
record.Attributes["user.id"] = &AnyValue{StringValue: strPtr("12345")}

// 从 Context 提取追踪信息
ExtractTraceContext(ctx, record)
```

### 3. 处理阶段

```go
// 处理器处理 LogRecord
type Processor interface {
    Process(record *LogRecord) error
}

type FilterProcessor struct {
    minSeverity SeverityNumber
}

func (p *FilterProcessor) Process(record *LogRecord) error {
    if record.SeverityNumber < p.minSeverity {
        return errors.New("filtered")
    }
    return nil
}
```

### 4. 导出阶段

```go
// 导出器导出 LogRecord
type Exporter interface {
    Export(ctx context.Context, records []*LogRecord) error
}

type OTLPExporter struct {
    client otlplog.LogsServiceClient
}

func (e *OTLPExporter) Export(ctx context.Context, records []*LogRecord) error {
    req := &otlplog.ExportLogsServiceRequest{
        ResourceLogs: []*otlplog.ResourceLogs{
            {
                ScopeLogs: []*otlplog.ScopeLogs{
                    {
                        LogRecords: convertToProto(records),
                    },
                },
            },
        },
    }
    
    _, err := e.client.Export(ctx, req)
    return err
}
```

---

## Go 1.25.1 实现

### 1. 基本实现

```go
package otellog

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel/trace"
)

// Logger 日志记录器
type Logger struct {
    instrumentationScope string
    processor            Processor
}

// Emit 发出日志
func (l *Logger) Emit(ctx context.Context, record *LogRecord) error {
    // 自动设置 ObservedTimestamp
    if record.ObservedTimestamp.IsZero() {
        record.ObservedTimestamp = time.Now()
    }
    
    // 自动设置 Timestamp (如果未设置)
    if record.Timestamp.IsZero() {
        record.Timestamp = record.ObservedTimestamp
    }
    
    // 自动提取追踪上下文
    if record.TraceID.IsValid() == false {
        ExtractTraceContext(ctx, record)
    }
    
    // 处理
    return l.processor.Process(record)
}

// Info 记录 INFO 级别日志
func (l *Logger) Info(ctx context.Context, msg string, attrs ...KeyValue) error {
    record := &LogRecord{
        SeverityNumber: SeverityNumberInfo,
        SeverityText:   "INFO",
        Body:           &AnyValue{StringValue: &msg},
        Attributes:     make(map[string]*AnyValue),
    }
    
    for _, attr := range attrs {
        record.Attributes[attr.Key] = attr.Value
    }
    
    return l.Emit(ctx, record)
}

// Error 记录 ERROR 级别日志
func (l *Logger) Error(ctx context.Context, msg string, err error, attrs ...KeyValue) error {
    record := &LogRecord{
        SeverityNumber: SeverityNumberError,
        SeverityText:   "ERROR",
        Body:           &AnyValue{StringValue: &msg},
        Attributes:     make(map[string]*AnyValue),
    }
    
    // 添加错误信息
    if err != nil {
        errMsg := err.Error()
        record.Attributes["error.message"] = &AnyValue{StringValue: &errMsg}
    }
    
    for _, attr := range attrs {
        record.Attributes[attr.Key] = attr.Value
    }
    
    return l.Emit(ctx, record)
}
```

### 2. LogRecord 构建器

```go
// RecordBuilder LogRecord 构建器
type RecordBuilder struct {
    record *LogRecord
}

// NewRecordBuilder 创建构建器
func NewRecordBuilder() *RecordBuilder {
    return &RecordBuilder{
        record: &LogRecord{
            ObservedTimestamp: time.Now(),
            Attributes:        make(map[string]*AnyValue),
        },
    }
}

// WithTimestamp 设置时间戳
func (b *RecordBuilder) WithTimestamp(t time.Time) *RecordBuilder {
    b.record.Timestamp = t
    return b
}

// WithSeverity 设置严重性
func (b *RecordBuilder) WithSeverity(num SeverityNumber, text string) *RecordBuilder {
    b.record.SeverityNumber = num
    b.record.SeverityText = text
    return b
}

// WithBody 设置主体
func (b *RecordBuilder) WithBody(body string) *RecordBuilder {
    b.record.Body = &AnyValue{StringValue: &body}
    return b
}

// WithStructuredBody 设置结构化主体
func (b *RecordBuilder) WithStructuredBody(kvs ...*KeyValue) *RecordBuilder {
    b.record.Body = &AnyValue{
        KvListValue: &KeyValueList{Values: kvs},
    }
    return b
}

// WithAttribute 添加属性
func (b *RecordBuilder) WithAttribute(key string, value *AnyValue) *RecordBuilder {
    b.record.Attributes[key] = value
    return b
}

// WithTraceContext 设置追踪上下文
func (b *RecordBuilder) WithTraceContext(ctx context.Context) *RecordBuilder {
    ExtractTraceContext(ctx, b.record)
    return b
}

// Build 构建 LogRecord
func (b *RecordBuilder) Build() *LogRecord {
    return b.record
}

// 使用示例
record := NewRecordBuilder().
    WithTimestamp(time.Now()).
    WithSeverity(SeverityNumberInfo, "INFO").
    WithBody("User logged in").
    WithAttribute("user.id", &AnyValue{StringValue: strPtr("12345")}).
    WithAttribute("http.method", &AnyValue{StringValue: strPtr("POST")}).
    WithTraceContext(ctx).
    Build()
```

### 3. 与 slog 集成

```go
import (
    "context"
    "log/slog"
)

// SlogHandler OpenTelemetry slog Handler
type SlogHandler struct {
    logger *Logger
    attrs  []slog.Attr
}

// NewSlogHandler 创建 slog Handler
func NewSlogHandler(logger *Logger) *SlogHandler {
    return &SlogHandler{
        logger: logger,
    }
}

// Enabled 检查是否启用该级别
func (h *SlogHandler) Enabled(ctx context.Context, level slog.Level) bool {
    return true // 简化实现
}

// Handle 处理日志记录
func (h *SlogHandler) Handle(ctx context.Context, r slog.Record) error {
    record := &LogRecord{
        Timestamp:      r.Time,
        SeverityNumber: SlogLevelToSeverity(r.Level),
        SeverityText:   r.Level.String(),
        Body:           &AnyValue{StringValue: strPtr(r.Message)},
        Attributes:     make(map[string]*AnyValue),
    }
    
    // 添加预设属性
    for _, attr := range h.attrs {
        record.Attributes[attr.Key] = SlogValueToAnyValue(attr.Value)
    }
    
    // 添加记录属性
    r.Attrs(func(attr slog.Attr) bool {
        record.Attributes[attr.Key] = SlogValueToAnyValue(attr.Value)
        return true
    })
    
    return h.logger.Emit(ctx, record)
}

// WithAttrs 返回带有附加属性的新 Handler
func (h *SlogHandler) WithAttrs(attrs []slog.Attr) slog.Handler {
    newAttrs := make([]slog.Attr, 0, len(h.attrs)+len(attrs))
    newAttrs = append(newAttrs, h.attrs...)
    newAttrs = append(newAttrs, attrs...)
    return &SlogHandler{
        logger: h.logger,
        attrs:  newAttrs,
    }
}

// WithGroup 返回带有组的新 Handler
func (h *SlogHandler) WithGroup(name string) slog.Handler {
    // 简化实现
    return h
}

// 辅助函数
func SlogValueToAnyValue(v slog.Value) *AnyValue {
    switch v.Kind() {
    case slog.KindString:
        s := v.String()
        return &AnyValue{StringValue: &s}
    case slog.KindInt64:
        i := v.Int64()
        return &AnyValue{IntValue: &i}
    case slog.KindFloat64:
        f := v.Float64()
        return &AnyValue{DoubleValue: &f}
    case slog.KindBool:
        b := v.Bool()
        return &AnyValue{BoolValue: &b}
    default:
        s := v.String()
        return &AnyValue{StringValue: &s}
    }
}

// 使用示例
logger := NewLogger("app")
handler := NewSlogHandler(logger)
slogLogger := slog.New(handler)

slogLogger.Info("User logged in", "user_id", "12345", "ip", "192.168.1.1")
```

### 4. 批处理实现

```go
// BatchProcessor 批处理器
type BatchProcessor struct {
    exporter    Exporter
    batch       []*LogRecord
    batchSize   int
    flushTimer  *time.Timer
    flushPeriod time.Duration
    mu          sync.Mutex
}

// NewBatchProcessor 创建批处理器
func NewBatchProcessor(exporter Exporter, batchSize int, flushPeriod time.Duration) *BatchProcessor {
    p := &BatchProcessor{
        exporter:    exporter,
        batch:       make([]*LogRecord, 0, batchSize),
        batchSize:   batchSize,
        flushPeriod: flushPeriod,
    }
    
    p.flushTimer = time.AfterFunc(flushPeriod, p.flush)
    return p
}

// Process 处理 LogRecord
func (p *BatchProcessor) Process(record *LogRecord) error {
    p.mu.Lock()
    defer p.mu.Unlock()
    
    p.batch = append(p.batch, record)
    
    if len(p.batch) >= p.batchSize {
        return p.flushLocked()
    }
    
    return nil
}

// flush 刷新批次
func (p *BatchProcessor) flush() {
    p.mu.Lock()
    defer p.mu.Unlock()
    
    p.flushLocked()
    p.flushTimer.Reset(p.flushPeriod)
}

func (p *BatchProcessor) flushLocked() error {
    if len(p.batch) == 0 {
        return nil
    }
    
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    
    err := p.exporter.Export(ctx, p.batch)
    p.batch = p.batch[:0] // 清空
    return err
}

// Shutdown 关闭处理器
func (p *BatchProcessor) Shutdown(ctx context.Context) error {
    p.flushTimer.Stop()
    return p.flushLocked()
}
```

---

## 高级特性

### 1. 结构化 Body

```go
// 结构化事件日志
record := &LogRecord{
    SeverityNumber: SeverityNumberInfo,
    SeverityText:   "INFO",
    Body: &AnyValue{
        KvListValue: &KeyValueList{
            Values: []*KeyValue{
                {Key: "event_name", Value: &AnyValue{StringValue: strPtr("user.login")}},
                {Key: "user_id", Value: &AnyValue{StringValue: strPtr("12345")}},
                {Key: "timestamp", Value: &AnyValue{IntValue: int64Ptr(time.Now().Unix())}},
                {Key: "success", Value: &AnyValue{BoolValue: boolPtr(true)}},
            },
        },
    },
}
```

### 2. 嵌套属性

```go
// 嵌套的用户信息
userInfo := &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "id", Value: &AnyValue{StringValue: strPtr("12345")}},
            {Key: "name", Value: &AnyValue{StringValue: strPtr("John Doe")}},
            {Key: "email", Value: &AnyValue{StringValue: strPtr("john@example.com")}},
        },
    },
}

record.Attributes["user"] = userInfo
```

### 3. 数组和 Map

```go
// 数组属性
tags := &AnyValue{
    ArrayValue: &ArrayValue{
        Values: []*AnyValue{
            {StringValue: strPtr("production")},
            {StringValue: strPtr("critical")},
            {StringValue: strPtr("security")},
        },
    },
}
record.Attributes["tags"] = tags

// Map 属性
metadata := &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "version", Value: &AnyValue{StringValue: strPtr("1.0.0")}},
            {Key: "build", Value: &AnyValue{StringValue: strPtr("20250109")}},
        },
    },
}
record.Attributes["metadata"] = metadata
```

### 4. 自定义类型

```go
// LogValuer 接口 (类似 slog.LogValuer)
type LogValuer interface {
    LogValue() *AnyValue
}

// 实现 LogValuer
type User struct {
    ID    string
    Name  string
    Email string
}

func (u User) LogValue() *AnyValue {
    return &AnyValue{
        KvListValue: &KeyValueList{
            Values: []*KeyValue{
                {Key: "id", Value: &AnyValue{StringValue: &u.ID}},
                {Key: "name", Value: &AnyValue{StringValue: &u.Name}},
                {Key: "email", Value: &AnyValue{StringValue: &u.Email}},
            },
        },
    }
}

// 使用
user := User{ID: "12345", Name: "John", Email: "john@example.com"}
record.Attributes["user"] = user.LogValue()
```

---

## 性能优化

### 1. 零分配日志

```go
// 使用 sync.Pool 复用 LogRecord
var logRecordPool = sync.Pool{
    New: func() interface{} {
        return &LogRecord{
            Attributes: make(map[string]*AnyValue, 16),
        }
    },
}

// 获取 LogRecord
func AcquireLogRecord() *LogRecord {
    r := logRecordPool.Get().(*LogRecord)
    r.ObservedTimestamp = time.Now()
    return r
}

// 释放 LogRecord
func ReleaseLogRecord(r *LogRecord) {
    r.Timestamp = time.Time{}
    r.ObservedTimestamp = time.Time{}
    r.SeverityNumber = 0
    r.SeverityText = ""
    r.Body = nil
    for k := range r.Attributes {
        delete(r.Attributes, k)
    }
    r.DroppedAttributesCount = 0
    r.TraceID = trace.TraceID{}
    r.SpanID = trace.SpanID{}
    r.TraceFlags = 0
    
    logRecordPool.Put(r)
}
```

### 2. 对象池复用

```go
// AnyValue 池
var anyValuePool = sync.Pool{
    New: func() interface{} {
        return &AnyValue{}
    },
}

func NewStringValue(s string) *AnyValue {
    v := anyValuePool.Get().(*AnyValue)
    v.StringValue = &s
    return v
}

func ReleaseAnyValue(v *AnyValue) {
    *v = AnyValue{} // 清空
    anyValuePool.Put(v)
}
```

### 3. 批量处理

```go
// 批量导出
type BatchExporter struct {
    batchSize   int
    flushPeriod time.Duration
    records     chan *LogRecord
    exporter    Exporter
}

func (e *BatchExporter) Start(ctx context.Context) {
    batch := make([]*LogRecord, 0, e.batchSize)
    ticker := time.NewTicker(e.flushPeriod)
    defer ticker.Stop()
    
    for {
        select {
        case record := <-e.records:
            batch = append(batch, record)
            if len(batch) >= e.batchSize {
                e.exporter.Export(ctx, batch)
                batch = batch[:0]
            }
            
        case <-ticker.C:
            if len(batch) > 0 {
                e.exporter.Export(ctx, batch)
                batch = batch[:0]
            }
            
        case <-ctx.Done():
            return
        }
    }
}
```

### 4. 延迟字段计算

```go
// LazyValue 延迟计算的值
type LazyValue struct {
    fn func() *AnyValue
}

func (lv *LazyValue) Compute() *AnyValue {
    return lv.fn()
}

// 使用
record.Attributes["expensive_value"] = &LazyValue{
    fn: func() *AnyValue {
        // 只在需要时才计算
        result := expensiveComputation()
        return &AnyValue{StringValue: &result}
    },
}.Compute()
```

---

## 最佳实践

### 1. 字段使用规范

```go
// ✅ 正确：设置所有关键字段
record := &LogRecord{
    Timestamp:      time.Now(),
    ObservedTimestamp: time.Now(),
    SeverityNumber: SeverityNumberInfo,
    SeverityText:   "INFO",
    Body:           &AnyValue{StringValue: strPtr("User login")},
}

// ❌ 错误：缺少 ObservedTimestamp
record := &LogRecord{
    Timestamp: time.Now(),
    Body:      &AnyValue{StringValue: strPtr("User login")},
}
```

### 2. Body 设计

```go
// ✅ 简单消息：使用字符串 Body
record.Body = &AnyValue{StringValue: strPtr("User login successful")}

// ✅ 结构化事件：使用 KvList Body
record.Body = &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "event", Value: &AnyValue{StringValue: strPtr("user.login")}},
            {Key: "status", Value: &AnyValue{StringValue: strPtr("success")}},
        },
    },
}

// ❌ 错误：Body 过大
record.Body = &AnyValue{StringValue: strPtr(hugeData)} // 避免
```

### 3. Attributes 管理

```go
// ✅ 正确：使用标准化属性键
record.Attributes = map[string]*AnyValue{
    "http.method":      {StringValue: strPtr("GET")},
    "http.status_code": {IntValue: int64Ptr(200)},
    "user.id":          {StringValue: strPtr("12345")},
}

// ❌ 错误：使用非标准键
record.Attributes = map[string]*AnyValue{
    "method": {StringValue: strPtr("GET")}, // 应该是 http.method
    "status": {IntValue: int64Ptr(200)},    // 应该是 http.status_code
}

// ✅ 正确：限制属性数量
const MaxAttributes = 128
if len(record.Attributes) > MaxAttributes {
    // 丢弃低优先级属性
}
```

### 4. 时间戳处理

```go
// ✅ 正确：使用高精度时间戳
record.Timestamp = time.Now()

// ✅ 正确：从事件源获取时间
record.Timestamp = eventTime
record.ObservedTimestamp = time.Now()

// ❌ 错误：使用秒级精度
record.Timestamp = time.Unix(time.Now().Unix(), 0) // 丢失纳秒精度
```

---

## 常见问题

### Q1: Timestamp 和 ObservedTimestamp 的区别？

**A**:

- **Timestamp**: 日志事件**实际发生**的时间（由应用程序设置）
- **ObservedTimestamp**: 日志被 SDK/Collector **观测到**的时间（由收集器设置）

**使用建议**:

```go
// 应用程序记录事件时间
record.Timestamp = eventTime

// SDK 自动设置观测时间
record.ObservedTimestamp = time.Now()

// 计算传输延迟
delay := record.ObservedTimestamp.Sub(record.Timestamp)
```

### Q2: Body 应该使用 string 还是结构化数据？

**A**:

```text
简单消息 → String Body:
  "User login successful"
  "Database connection failed"

结构化事件 → KvList Body:
  {
    "event": "user.login",
    "user_id": "12345",
    "success": true
  }

规则：
- 人类可读的消息 → String
- 机器可解析的事件 → Structured
```

### Q3: 如何关联 Logs 和 Traces？

**A**:

```go
// 从 Context 自动提取
func LogWithTrace(ctx context.Context, msg string) {
    record := NewLogRecord()
    record.Body = &AnyValue{StringValue: &msg}
    
    // 自动关联
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        record.TraceID = spanCtx.TraceID()
        record.SpanID = spanCtx.SpanID()
        record.TraceFlags = spanCtx.TraceFlags()
    }
    
    logger.Emit(ctx, record)
}
```

### Q4: 如何处理大量属性？

**A**:

```go
// 策略 1: 限制数量
const MaxAttributes = 128

func AddAttribute(record *LogRecord, key string, value *AnyValue) {
    if len(record.Attributes) >= MaxAttributes {
        record.DroppedAttributesCount++
        return
    }
    record.Attributes[key] = value
}

// 策略 2: 优先级
type AttributePriority int
const (
    Low AttributePriority = iota
    Medium
    High
)

// 优先保留 High 属性

// 策略 3: 采样
if rand.Float64() < 0.1 { // 10% 采样
    record.Attributes["expensive_attr"] = value
}
```

### Q5: 如何优化日志性能？

**A**:

```go
// 1. 使用对象池
record := AcquireLogRecord()
defer ReleaseLogRecord(record)

// 2. 批量处理
processor := NewBatchProcessor(exporter, 100, time.Second)

// 3. 异步导出
go exporter.Export(ctx, records)

// 4. 级别过滤
if record.SeverityNumber < MinSeverity {
    return // 快速返回
}

// 5. 延迟计算
record.Attributes["value"] = &LazyValue{fn: expensiveFunc}
```

---

## 参考资源

- [OpenTelemetry Logs Data Model](https://opentelemetry.io/docs/specs/otel/logs/data-model/)
- [OpenTelemetry Logs SDK Specification](https://opentelemetry.io/docs/specs/otel/logs/sdk/)
- [OTLP Logs Protocol](https://opentelemetry.io/docs/specs/otlp/#logs)
- [Go slog Package](https://pkg.go.dev/log/slog)
- [02_SeverityNumber.md](./02_SeverityNumber.md)
- [03_Body与Attributes.md](./03_Body与Attributes.md)

---

**🎉 恭喜！你已经掌握了 LogRecord 的完整结构！**

现在你可以：

- ✅ 理解 LogRecord 的所有字段
- ✅ 使用 Go 1.25.1 实现日志记录
- ✅ 关联 Logs 和 Traces
- ✅ 优化日志性能
- ✅ 遵循最佳实践

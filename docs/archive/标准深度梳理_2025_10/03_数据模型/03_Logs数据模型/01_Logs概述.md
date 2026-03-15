# OpenTelemetry Logs 数据模型详解

> **规范版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry Logs 数据模型详解](#opentelemetry-logs-数据模型详解)
  - [目录](#目录)
  - [1. Logs概述](#1-logs概述)
    - [1.1 什么是Logs](#11-什么是logs)
    - [1.2 为什么需要标准化Logs](#12-为什么需要标准化logs)
  - [2. 核心数据结构](#2-核心数据结构)
    - [2.1 LogRecord结构](#21-logrecord结构)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 字段详解](#3-字段详解)
    - [3.1 时间戳字段](#31-时间戳字段)
    - [3.2 严重性 (Severity)](#32-严重性-severity)
    - [3.3 Body字段](#33-body字段)
    - [3.4 Attributes字段](#34-attributes字段)
    - [3.5 TraceContext](#35-tracecontext)
  - [4. LogRecord实现](#4-logrecord实现)
    - [4.1 Go实现](#41-go实现)
    - [4.2 Python实现](#42-python实现)
    - [4.3 Java实现](#43-java实现)
  - [5. 与现有日志系统集成](#5-与现有日志系统集成)
    - [5.1 与结构化日志集成](#51-与结构化日志集成)
    - [5.2 与传统日志集成](#52-与传统日志集成)
  - [6. 日志与Trace关联](#6-日志与trace关联)
    - [6.1 自动关联](#61-自动关联)
    - [6.2 手动关联](#62-手动关联)
  - [7. 语义约定](#7-语义约定)
  - [8. 性能优化](#8-性能优化)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 参考资源](#10-参考资源)

---

## 1. Logs概述

### 1.1 什么是Logs

**定义**：

```text
Logs (日志):
记录应用程序运行时事件的时间序列数据

OpenTelemetry Logs特点:
1. 标准化数据模型
2. 与Traces/Metrics统一
3. 支持结构化和非结构化日志
4. 内置TraceContext关联
5. 多后端兼容

日志类型:
- 应用日志 (Application Logs)
- 系统日志 (System Logs)
- 审计日志 (Audit Logs)
- 访问日志 (Access Logs)
- 错误日志 (Error Logs)
```

**三大信号对比**：

```text
┌──────────────────────────────────────────────────────────┐
│                     三大信号对比                          │
├──────────┬─────────────┬─────────────┬──────────────────┤
│ 信号类型  │   Traces    │   Metrics   │      Logs        │
├──────────┼─────────────┼─────────────┼──────────────────┤
│ 数据类型  │ 事件序列    │ 数值聚合     │ 事件记录          │
│ 时间粒度  │ 请求级别    │ 时间序列     │ 事件级别          │
│ 存储成本  │ 高          │ 低          │ 中-高             │
│ 查询能力  │ 精确追踪     │ 趋势分析    │ 全文搜索          │
│ 采样需求  │ 需要        │ 不需要      │ 可选              │
│ 关联能力  │ 原生        │ 标签        │ TraceContext      │
└──────────┴─────────────┴─────────────┴──────────────────┘

Logs的独特价值:
- 详细的事件信息
- 任意格式支持
- 历史日志兼容
- 调试和审计
```

### 1.2 为什么需要标准化Logs

**标准化的价值**：

```text
1. 统一数据模型
   问题: 每个日志框架格式不同
   解决: OTLP统一格式

2. 统一传输协议
   问题: 多种日志传输协议 (syslog, fluentd, etc.)
   解决: OTLP gRPC/HTTP

3. 统一关联
   问题: 日志与Trace无法关联
   解决: 内置TraceContext

4. 统一后端
   问题: 多个日志后端 (ELK, Loki, Splunk)
   解决: Collector统一路由

示例场景:
应用日志 → OTLP → Collector → Loki + Elasticsearch
                              ↓
                         自动关联Trace
```

---

## 2. 核心数据结构

### 2.1 LogRecord结构

**完整结构**：

```protobuf
message LogRecord {
  // 时间戳 (纳秒)
  fixed64 time_unix_nano = 1;
  
  // 观测时间戳 (可选)
  fixed64 observed_time_unix_nano = 11;
  
  // 严重性级别
  SeverityNumber severity_number = 2;
  
  // 严重性文本
  string severity_text = 3;
  
  // 日志内容 (核心)
  AnyValue body = 5;
  
  // 属性
  repeated KeyValue attributes = 6;
  
  // 已删除属性数量
  uint32 dropped_attributes_count = 7;
  
  // Flags (包含TraceFlags)
  fixed32 flags = 8;
  
  // TraceId (关联Trace)
  bytes trace_id = 9;  // 16字节
  
  // SpanId (关联Span)
  bytes span_id = 10;  // 8字节
}
```

**字段说明**：

```text
核心字段:
1. time_unix_nano: 日志生成时间
2. severity_number: 严重性级别 (1-24)
3. body: 日志内容 (任意类型)
4. attributes: 键值对属性

关联字段:
5. trace_id: 关联的TraceId
6. span_id: 关联的SpanId
7. flags: Trace标志

元数据:
8. observed_time_unix_nano: 收集时间
9. severity_text: 严重性文本 (DEBUG, INFO, etc.)
10. dropped_attributes_count: 丢弃的属性数量
```

### 2.2 形式化定义

**数学模型**：

```text
LogRecord定义:
L = (T, S, B, A, C)

其中:
T: Timestamp (时间戳)
  T = (t_event, t_observed)
  t_event: 事件发生时间
  t_observed: 观测时间

S: Severity (严重性)
  S = (number, text)
  number ∈ {1..24}
  text ∈ {"TRACE", "DEBUG", "INFO", "WARN", "ERROR", "FATAL"}

B: Body (内容)
  B: AnyValue
  支持: string, int, double, bool, bytes, array, map

A: Attributes (属性)
  A = {(k₁,v₁), (k₂,v₂), ..., (kₙ,vₙ)}
  kᵢ: string (键)
  vᵢ: AnyValue (值)

C: Context (上下文)
  C = (trace_id, span_id, flags)
  trace_id: 16 bytes
  span_id: 8 bytes
  flags: 4 bytes

关系约束:
1. t_event ≤ t_observed (观测时间不早于事件时间)
2. number和text需要对应
3. 如果有trace_id，则必须有span_id
```

---

## 3. 字段详解

### 3.1 时间戳字段

**两个时间戳**：

```text
1. time_unix_nano (事件时间)
   - 日志事件发生的时间
   - 由应用程序生成
   - 必填字段

2. observed_time_unix_nano (观测时间)
   - 日志被SDK/Collector收集的时间
   - 可选字段
   - 用于检测时钟偏移

为什么需要两个时间戳:
- 检测时钟不同步
- 计算日志延迟
- 时序分析

示例:
event_time: 2025-10-08T10:00:00.000Z
observed_time: 2025-10-08T10:00:00.100Z
延迟: 100ms
```

### 3.2 严重性 (Severity)

**严重性级别**：

```text
SeverityNumber枚举:
┌───────┬────────────┬─────────────────────────────┐
│ 数值  │ 名称       │ 描述                        │
├───────┼────────────┼─────────────────────────────┤
│  1-4  │ TRACE      │ 最详细的跟踪信息            │
│  5-8  │ DEBUG      │ 调试信息                    │
│  9-12 │ INFO       │ 一般信息                    │
│ 13-16 │ WARN       │ 警告信息                    │
│ 17-20 │ ERROR      │ 错误信息                    │
│ 21-24 │ FATAL      │ 致命错误                    │
└───────┴────────────┴─────────────────────────────┘

推荐映射:
TRACE  → 1
DEBUG  → 5
INFO   → 9
WARN   → 13
ERROR  → 17
FATAL  → 21

为什么需要范围:
- 支持子级别 (如: INFO1, INFO2, INFO3, INFO4)
- 灵活性
- 未来扩展
```

### 3.3 Body字段

**Body类型**：

```text
Body: AnyValue类型
支持的值类型:
1. string: "Error occurred"
2. int: 12345
3. double: 3.14159
4. bool: true
5. bytes: [0x01, 0x02, 0x03]
6. array: ["item1", "item2"]
7. map: {"key": "value"}

最常用: string

示例:
// 简单字符串
body: "User login successful"

// 结构化对象
body: {
  "message": "Order created",
  "order_id": "ORD-12345",
  "amount": 99.99
}

// 数组
body: ["Error 1", "Error 2", "Error 3"]
```

### 3.4 Attributes字段

**常用属性**：

```text
通用属性:
- log.file.name: 日志文件名
- log.file.path: 日志文件路径
- log.iostream: stdout/stderr
- code.function: 函数名
- code.filepath: 源文件路径
- code.lineno: 行号

应用属性:
- service.name: 服务名
- service.version: 服务版本
- deployment.environment: 环境 (prod/staging/dev)

自定义属性:
- user.id: 用户ID
- session.id: 会话ID
- request.id: 请求ID
- error.type: 错误类型
- error.message: 错误消息
- error.stack: 堆栈跟踪

示例:
attributes:
  - service.name: "order-service"
  - deployment.environment: "production"
  - user.id: "user-123"
  - code.function: "createOrder"
  - code.lineno: 42
```

### 3.5 TraceContext

**关联Trace**：

```text
TraceContext字段:
1. trace_id: 16字节 (128位)
2. span_id: 8字节 (64位)
3. flags: 4字节

作用:
- 将日志关联到特定Trace
- 将日志关联到特定Span
- 实现分布式追踪

查询场景:
1. 查看某个Trace的所有日志
   WHERE trace_id = "abc123..."

2. 查看某个Span的所有日志
   WHERE span_id = "def456..."

3. 通过日志找到对应Trace
   logs → trace_id → Jaeger查看完整调用链

价值:
问题排查时，可以:
1. 从日志跳转到Trace
2. 从Trace查看相关日志
3. 完整上下文还原
```

---

## 4. LogRecord实现

### 4.1 Go实现

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploggrpc"
    "go.opentelemetry.io/otel/sdk/log"
    api "go.opentelemetry.io/otel/log"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 1. 创建OTLP Exporter
    exporter, err := otlploggrpc.New(context.Background(),
        otlploggrpc.WithEndpoint("localhost:4317"),
        otlploggrpc.WithInsecure(),
    )
    if err != nil {
        panic(err)
    }
    
    // 2. 创建LoggerProvider
    provider := log.NewLoggerProvider(
        log.WithProcessor(log.NewBatchProcessor(exporter)),
    )
    defer provider.Shutdown(context.Background())
    
    // 3. 获取Logger
    logger := provider.Logger("my-service")
    
    // 4. 基础日志
    logger.Emit(context.Background(), api.Record{
        Timestamp:         time.Now(),
        ObservedTimestamp: time.Now(),
        Severity:          api.SeverityInfo,
        SeverityText:      "INFO",
        Body:              api.StringValue("User login successful"),
        Attributes: []api.KeyValue{
            api.String("user.id", "user-123"),
            api.String("user.email", "user@example.com"),
        },
    })
    
    // 5. 关联Trace的日志
    ctx := context.Background()
    span := trace.SpanFromContext(ctx)
    spanContext := span.SpanContext()
    
    logger.Emit(ctx, api.Record{
        Timestamp:    time.Now(),
        Severity:     api.SeverityError,
        SeverityText: "ERROR",
        Body:         api.StringValue("Order creation failed"),
        Attributes: []api.KeyValue{
            api.String("order.id", "ORD-12345"),
            api.String("error.type", "DatabaseError"),
        },
        TraceID: spanContext.TraceID(),
        SpanID:  spanContext.SpanID(),
        TraceFlags: spanContext.TraceFlags(),
    })
}

// 结构化日志示例
func logStructured(logger api.Logger) {
    logger.Emit(context.Background(), api.Record{
        Timestamp:    time.Now(),
        Severity:     api.SeverityInfo,
        SeverityText: "INFO",
        Body: api.MapValue(
            api.String("event", "order_created"),
            api.String("order_id", "ORD-12345"),
            api.Float64("amount", 99.99),
            api.String("currency", "USD"),
        ),
        Attributes: []api.KeyValue{
            api.String("service.name", "order-service"),
        },
    })
}
```

### 4.2 Python实现

```python
from opentelemetry import trace
from opentelemetry.sdk.logs import LoggerProvider, LoggingHandler
from opentelemetry.exporter.otlp.proto.grpc.logs_exporter import OTLPLogExporter
from opentelemetry.sdk.logs.export import BatchLogRecordProcessor
import logging

# 1. 设置LoggerProvider
log_exporter = OTLPLogExporter(
    endpoint="localhost:4317",
    insecure=True
)

logger_provider = LoggerProvider()
logger_provider.add_log_record_processor(
    BatchLogRecordProcessor(log_exporter)
)

# 2. 集成Python logging
handler = LoggingHandler(logger_provider=logger_provider)
logging.getLogger().addHandler(handler)
logging.getLogger().setLevel(logging.INFO)

# 3. 基础日志
logging.info("User login successful", extra={
    "user.id": "user-123",
    "user.email": "user@example.com"
})

# 4. 关联Trace的日志
tracer = trace.get_tracer(__name__)

with tracer.start_as_current_span("create_order") as span:
    # 日志自动关联当前Span
    logging.error("Order creation failed", extra={
        "order.id": "ORD-12345",
        "error.type": "DatabaseError"
    })

# 5. 结构化日志
logging.info("Order created", extra={
    "event": "order_created",
    "order.id": "ORD-12345",
    "amount": 99.99,
    "currency": "USD"
})
```

### 4.3 Java实现

```java
import io.opentelemetry.api.logs.Logger;
import io.opentelemetry.api.logs.Severity;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.common.AttributeKey;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.sdk.logs.SdkLoggerProvider;
import io.opentelemetry.sdk.logs.export.BatchLogRecordProcessor;
import io.opentelemetry.exporter.otlp.logs.OtlpGrpcLogRecordExporter;

public class LoggingExample {
    public static void main(String[] args) {
        // 1. 创建Exporter
        OtlpGrpcLogRecordExporter exporter = OtlpGrpcLogRecordExporter.builder()
            .setEndpoint("http://localhost:4317")
            .build();
        
        // 2. 创建LoggerProvider
        SdkLoggerProvider loggerProvider = SdkLoggerProvider.builder()
            .addLogRecordProcessor(BatchLogRecordProcessor.builder(exporter).build())
            .build();
        
        // 3. 获取Logger
        Logger logger = loggerProvider.get("my-service");
        
        // 4. 基础日志
        logger.logRecordBuilder()
            .setSeverity(Severity.INFO)
            .setSeverityText("INFO")
            .setBody("User login successful")
            .setAttributes(Attributes.builder()
                .put("user.id", "user-123")
                .put("user.email", "user@example.com")
                .build())
            .emit();
        
        // 5. 关联Trace的日志
        Span span = Span.current();
        logger.logRecordBuilder()
            .setSeverity(Severity.ERROR)
            .setSeverityText("ERROR")
            .setBody("Order creation failed")
            .setAttributes(Attributes.builder()
                .put("order.id", "ORD-12345")
                .put("error.type", "DatabaseError")
                .build())
            .setContext(span.getSpanContext())
            .emit();
    }
}
```

---

## 5. 与现有日志系统集成

### 5.1 与结构化日志集成

**集成logrus (Go)**：

```go
import (
    "github.com/sirupsen/logrus"
    "go.opentelemetry.io/contrib/bridges/otellogrus"
)

func main() {
    // 1. 创建logrus logger
    logger := logrus.New()
    
    // 2. 添加OpenTelemetry Hook
    hook := otellogrus.NewHook()
    logger.AddHook(hook)
    
    // 3. 正常使用logrus
    logger.WithFields(logrus.Fields{
        "user.id": "user-123",
        "order.id": "ORD-12345",
    }).Info("Order created")
    
    // 日志自动发送到OTLP
}
```

**集成zap (Go)**：

```go
import (
    "go.uber.org/zap"
    "go.opentelemetry.io/contrib/bridges/otelzap"
)

func main() {
    // 1. 创建zap logger
    zapLogger, _ := zap.NewProduction()
    
    // 2. 包装为OTEL logger
    logger := otelzap.New(zapLogger)
    
    // 3. 正常使用
    logger.Info("Order created",
        zap.String("user.id", "user-123"),
        zap.String("order.id", "ORD-12345"),
    )
}
```

### 5.2 与传统日志集成

**Collector收集文件日志**：

```yaml
receivers:
  filelog:
    include:
      - /var/log/app/*.log
    operators:
      # 解析JSON日志
      - type: json_parser
        parse_from: body
      
      # 提取严重性
      - type: severity_parser
        parse_from: attributes.level
      
      # 提取时间戳
      - type: time_parser
        parse_from: attributes.timestamp
        layout: '%Y-%m-%d %H:%M:%S'

processors:
  batch:

exporters:
  otlp:
    endpoint: backend:4317

service:
  pipelines:
    logs:
      receivers: [filelog]
      processors: [batch]
      exporters: [otlp]
```

---

## 6. 日志与Trace关联

### 6.1 自动关联

**SDK自动关联**：

```go
// Go SDK自动关联
tracer := otel.Tracer("my-service")
logger := otel.Logger("my-service")

ctx, span := tracer.Start(context.Background(), "process_order")
defer span.End()

// 从context自动提取TraceContext
logger.Emit(ctx, api.Record{
    Severity: api.SeverityInfo,
    Body:     api.StringValue("Processing order"),
})
// trace_id和span_id自动填充
```

```python
# Python SDK自动关联
with tracer.start_as_current_span("process_order"):
    # logging会自动关联当前Span
    logging.info("Processing order")
```

### 6.2 手动关联

**手动注入TraceContext**：

```go
// 手动关联
span := trace.SpanFromContext(ctx)
sc := span.SpanContext()

logger.Emit(context.Background(), api.Record{
    Severity:   api.SeverityInfo,
    Body:       api.StringValue("Manual trace association"),
    TraceID:    sc.TraceID(),
    SpanID:     sc.SpanID(),
    TraceFlags: sc.TraceFlags(),
})
```

---

## 7. 语义约定

**推荐属性**：

```text
日志属性语义约定:

1. 代码位置
   - code.function: 函数名
   - code.filepath: 文件路径
   - code.lineno: 行号
   - code.namespace: 命名空间/包名

2. 异常信息
   - exception.type: 异常类型
   - exception.message: 异常消息
   - exception.stacktrace: 堆栈跟踪
   - exception.escaped: 是否逃逸

3. HTTP请求
   - http.method: GET/POST
   - http.url: 请求URL
   - http.status_code: 状态码
   - http.user_agent: User-Agent

4. 数据库操作
   - db.system: MySQL/PostgreSQL
   - db.statement: SQL语句
   - db.operation: SELECT/INSERT
   - db.name: 数据库名

5. 消息队列
   - messaging.system: Kafka/RabbitMQ
   - messaging.destination: 队列/主题名
   - messaging.operation: send/receive
```

---

## 8. 性能优化

```text
1. 批处理
   使用BatchLogRecordProcessor
   减少网络请求

2. 采样
   不需要发送所有DEBUG日志
   INFO以上级别全量
   DEBUG级别采样10%

3. 异步导出
   不阻塞应用主流程
   使用队列缓冲

4. 属性限制
   限制属性数量 (< 128)
   限制属性大小 (< 1KB)

5. Body大小
   限制Body大小 (< 10KB)
   大内容使用引用

性能基准:
- 同步日志: 1000 logs/s
- 异步日志: 100,000 logs/s
- 批处理(100): 500,000 logs/s
```

---

## 9. 最佳实践

```text
1. 结构化日志
   ✅ 使用结构化格式 (JSON)
   ❌ 避免纯文本拼接

2. 一致的严重性
   ✅ 遵循Severity定义
   ❌ 避免滥用级别

3. 有意义的属性
   ✅ 添加上下文属性
   ❌ 避免冗余信息

4. 关联Trace
   ✅ 自动关联TraceContext
   ❌ 不要手动拼接trace_id

5. 避免敏感信息
   ✅ 脱敏PII数据
   ❌ 不要记录密码/Token

6. 适度采样
   ✅ DEBUG日志采样
   ❌ 不要100%采样

7. 错误日志完整
   ✅ 记录堆栈跟踪
   ✅ 记录错误上下文
   ❌ 不要吞掉异常

8. 性能监控
   ✅ 监控日志量
   ✅ 监控导出延迟
   ❌ 不要忽略背压

示例好日志:
{
  "severity": "ERROR",
  "body": "Order creation failed",
  "attributes": {
    "order.id": "ORD-12345",
    "user.id": "user-123",
    "error.type": "DatabaseConnectionError",
    "error.message": "Connection timeout after 30s",
    "code.function": "createOrder",
    "code.lineno": 42
  },
  "trace_id": "abc123...",
  "span_id": "def456..."
}
```

---

## 10. 参考资源

- **Logs规范**: <https://opentelemetry.io/docs/specs/otel/logs/>
- **Logs API**: <https://opentelemetry.io/docs/specs/otel/logs/api/>
- **日志语义约定**: <https://opentelemetry.io/docs/specs/semconv/general/logs/>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [Span结构](../01_Traces数据模型/01_Span结构.md), [Metrics概述](../02_Metrics数据模型/01_Metrics概述.md)

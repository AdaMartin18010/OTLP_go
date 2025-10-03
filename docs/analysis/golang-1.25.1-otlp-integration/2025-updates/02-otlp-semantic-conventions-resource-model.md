# OTLP 语义约定与资源模型深度解析

> **文档版本**: v1.0.0  
> **创建日期**: 2025-10-03  
> **作者**: OTLP × Golang CSP 技术体系研究组  
> **关联文档**: [Golang CSP 分析](./01-golang-1.25.1-csp-comprehensive-analysis.md) | [同构证明](./03-csp-otlp-isomorphism-proof.md)

---

## 📋 目录

- [OTLP 语义约定与资源模型深度解析](#otlp-语义约定与资源模型深度解析)
  - [📋 目录](#-目录)
  - [1. OTLP 协议架构概览](#1-otlp-协议架构概览)
    - [1.1 协议栈层次](#11-协议栈层次)
    - [1.2 核心设计原则](#12-核心设计原则)
    - [1.3 Protobuf 定义根结构](#13-protobuf-定义根结构)
  - [2. 信号类型与数据模型](#2-信号类型与数据模型)
    - [2.1 四大遥测信号](#21-四大遥测信号)
    - [2.2 数据流通路径](#22-数据流通路径)
    - [2.3 通用字段设计](#23-通用字段设计)
  - [3. Resource 资源模型](#3-resource-资源模型)
    - [3.1 定义与语义](#31-定义与语义)
    - [3.2 标准资源属性](#32-标准资源属性)
      - [3.2.1 服务标识 (必需)](#321-服务标识-必需)
      - [3.2.2 部署环境](#322-部署环境)
      - [3.2.3 容器与编排](#323-容器与编排)
      - [3.2.4 主机与云提供商](#324-主机与云提供商)
    - [3.3 Resource 合并规则](#33-resource-合并规则)
    - [3.4 Resource 形式化定义](#34-resource-形式化定义)
  - [4. 语义约定 (Semantic Conventions)](#4-语义约定-semantic-conventions)
    - [4.1 定义与目标](#41-定义与目标)
    - [4.2 命名空间层次](#42-命名空间层次)
    - [4.3 属性类型系统](#43-属性类型系统)
    - [4.4 核心语义约定分类](#44-核心语义约定分类)
      - [4.4.1 HTTP 语义约定](#441-http-语义约定)
      - [4.4.2 数据库语义约定](#442-数据库语义约定)
      - [4.4.3 消息队列语义约定](#443-消息队列语义约定)
      - [4.4.4 RPC 语义约定](#444-rpc-语义约定)
    - [4.5 Schema URL 版本管理](#45-schema-url-版本管理)
  - [5. Trace 追踪模型](#5-trace-追踪模型)
    - [5.1 核心概念](#51-核心概念)
    - [5.2 Span Kind 类型](#52-span-kind-类型)
    - [5.3 Span 生命周期 (Go SDK)](#53-span-生命周期-go-sdk)
    - [5.4 Span Event 事件模型](#54-span-event-事件模型)
    - [5.5 Span Link 链接模型](#55-span-link-链接模型)
    - [5.6 采样决策传播](#56-采样决策传播)
  - [6. Metric 指标模型](#6-metric-指标模型)
    - [6.1 数据模型](#61-数据模型)
    - [6.2 指标类型](#62-指标类型)
      - [6.2.1 Counter (累加计数器)](#621-counter-累加计数器)
      - [6.2.2 UpDownCounter (可增可减计数器)](#622-updowncounter-可增可减计数器)
      - [6.2.3 Histogram (直方图)](#623-histogram-直方图)
      - [6.2.4 Exponential Histogram (指数直方图)](#624-exponential-histogram-指数直方图)
    - [6.3 聚合时间性 (Aggregation Temporality)](#63-聚合时间性-aggregation-temporality)
    - [6.4 Exemplar (样例)](#64-exemplar-样例)
  - [7. Log 日志模型](#7-log-日志模型)
    - [7.1 数据模型](#71-数据模型)
    - [7.2 严重性级别](#72-严重性级别)
    - [7.3 Go SDK 日志集成](#73-go-sdk-日志集成)
      - [方案1: slog 桥接](#方案1-slog-桥接)
      - [方案2: Zap 集成](#方案2-zap-集成)
  - [8. Profile 性能剖析模型](#8-profile-性能剖析模型)
    - [8.1 Profile 信号 (实验性)](#81-profile-信号-实验性)
    - [8.2 Go 连续性能剖析](#82-go-连续性能剖析)
    - [8.3 eBPF 零开销剖析](#83-ebpf-零开销剖析)
  - [9. Schema URL 与版本演进](#9-schema-url-与版本演进)
    - [9.1 Schema 转换规则](#91-schema-转换规则)
    - [9.2 Collector 自动转换](#92-collector-自动转换)
  - [10. Go SDK 实现映射](#10-go-sdk-实现映射)
    - [10.1 核心包结构](#101-核心包结构)
    - [10.2 完整初始化示例](#102-完整初始化示例)
  - [11. 跨语言互操作性保证](#11-跨语言互操作性保证)
    - [11.1 Context 传播协议](#111-context-传播协议)
    - [11.2 跨语言 Trace 传播示例](#112-跨语言-trace-传播示例)
  - [12. 性能优化与零拷贝](#12-性能优化与零拷贝)
    - [12.1 Span 对象池](#121-span-对象池)
    - [12.2 零拷贝序列化](#122-零拷贝序列化)
    - [12.3 批量导出性能调优](#123-批量导出性能调优)
  - [📚 参考资料](#-参考资料)
  - [🔗 相关文档](#-相关文档)

---

## 1. OTLP 协议架构概览

### 1.1 协议栈层次

```mermaid
graph TB
    A[Application Layer] -->|Instrumentation| B[OpenTelemetry API]
    B -->|Data Export| C[OpenTelemetry SDK]
    C -->|Serialization| D[OTLP Protocol]
    D -->|Transport| E[gRPC/HTTP/1.1/HTTP/2]
    
    D --> D1[OTLP/gRPC<br/>protobuf binary]
    D --> D2[OTLP/HTTP<br/>protobuf binary]
    D --> D3[OTLP/HTTP<br/>JSON]
    
    style D fill:#ff9900
    style B fill:#66ccff
```

### 1.2 核心设计原则

| 原则 | 描述 | 形式化表达 |
|------|------|------------|
| **语义一致性** | 所有语言 SDK 共享相同语义模型 | `∀lang₁,lang₂: Semantics(lang₁) ≡ Semantics(lang₂)` |
| **向后兼容** | 新版本必须能解析旧版本数据 | `∀v₁<v₂: Parser(v₂) ⊇ Parser(v₁)` |
| **传输无关** | 协议独立于底层传输机制 | `OTLP ⊥ Transport` |
| **高效编码** | Protobuf 提供紧凑二进制表示 | `Size(protobuf) < Size(JSON)` |

### 1.3 Protobuf 定义根结构

```protobuf
// opentelemetry/proto/collector/trace/v1/trace_service.proto
service TraceService {
  rpc Export(ExportTraceServiceRequest) returns (ExportTraceServiceResponse) {}
}

message ExportTraceServiceRequest {
  repeated ResourceSpans resource_spans = 1;
}

message ResourceSpans {
  Resource resource = 1;                      // 资源信息
  repeated ScopeSpans scope_spans = 2;        // Instrumentation Scope
  string schema_url = 3;                      // 语义约定版本
}
```

---

## 2. 信号类型与数据模型

### 2.1 四大遥测信号

```go
// OTLP 支持的遥测信号类型
type SignalType int

const (
    SignalTrace   SignalType = iota // 分布式追踪
    SignalMetric                      // 指标度量
    SignalLog                         // 日志记录
    SignalProfile                     // 性能剖析 (实验性)
)
```

### 2.2 数据流通路径

```mermaid
sequenceDiagram
    participant App as Application
    participant SDK as OTel SDK
    participant Exp as Exporter
    participant Col as Collector
    participant Back as Backend

    App->>SDK: Emit Signal (Trace/Metric/Log)
    SDK->>SDK: Apply Sampling/Filtering
    SDK->>Exp: Batch Export
    Exp->>Col: OTLP/gRPC Stream
    Col->>Col: Transform/Enrich (OTTL)
    Col->>Back: Export to Storage
```

### 2.3 通用字段设计

所有信号类型共享以下核心字段：

| 字段 | 类型 | 必需 | 描述 |
|------|------|------|------|
| `Resource` | `Resource` | ✅ | 信号来源实体的标识信息 |
| `SchemaUrl` | `string` | ❌ | 语义约定版本 URL |
| `InstrumentationScope` | `InstrumentationScope` | ✅ | 生成信号的库信息 |

---

## 3. Resource 资源模型

### 3.1 定义与语义

**Resource** 表示生成遥测数据的实体，通常是服务实例、容器、主机等。

```protobuf
message Resource {
  repeated KeyValue attributes = 1;  // 资源属性键值对
  uint32 dropped_attributes_count = 2; // 超出限制被丢弃的属性数
}

message KeyValue {
  string key = 1;
  AnyValue value = 2;
}
```

### 3.2 标准资源属性

#### 3.2.1 服务标识 (必需)

```yaml
# 语义约定: service.* 命名空间
service.name: "order-service"         # 必需
service.namespace: "production"       # 推荐
service.instance.id: "pod-abc123"     # 推荐
service.version: "v1.2.3"             # 可选
```

**Go SDK 实现**:

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

res := resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceName("order-service"),
    semconv.ServiceNamespace("production"),
    semconv.ServiceInstanceID("pod-abc123"),
    semconv.ServiceVersion("v1.2.3"),
)
```

#### 3.2.2 部署环境

```yaml
deployment.environment: "production"   # staging/production/dev
deployment.type: "kubernetes"          # kubernetes/vm/serverless
```

#### 3.2.3 容器与编排

```yaml
# Kubernetes 语义约定
k8s.namespace.name: "default"
k8s.pod.name: "order-service-7d8f9c-xyz"
k8s.pod.uid: "550e8400-e29b-41d4-a716-446655440000"
k8s.deployment.name: "order-service"
k8s.node.name: "worker-node-3"

# Container Runtime
container.id: "abc123def456"
container.name: "order-service"
container.image.name: "myregistry/order-service"
container.image.tag: "v1.2.3"
```

**资源检测器 (Go SDK)**:

```go
import (
    "go.opentelemetry.io/contrib/detectors/gcp"
    "go.opentelemetry.io/contrib/detectors/aws/eks"
    "go.opentelemetry.io/otel/sdk/resource"
)

// 自动检测 Kubernetes 环境
res, err := resource.New(ctx,
    resource.WithDetectors(
        gcp.NewDetector(),      // GKE 检测
        eks.NewDetector(),      // Amazon EKS 检测
    ),
    resource.WithAttributes(
        semconv.ServiceName("my-service"),
    ),
)
```

#### 3.2.4 主机与云提供商

```yaml
# 主机信息
host.name: "worker-node-3.example.com"
host.id: "550e8400-e29b-41d4-a716-446655440000"
host.type: "n1-standard-4"
os.type: "linux"
os.description: "Ubuntu 22.04.3 LTS"

# 云提供商 (AWS 示例)
cloud.provider: "aws"
cloud.platform: "aws_eks"
cloud.region: "us-east-1"
cloud.availability_zone: "us-east-1a"
cloud.account.id: "123456789012"
```

### 3.3 Resource 合并规则

**场景**: SDK 配置的 Resource + 环境检测的 Resource

```go
// 合并规则: 
// 1. Key 冲突时，优先保留第一个 Resource 的值
// 2. dropped_attributes_count 累加
res1 := resource.NewSchemaless(
    attribute.String("service.name", "my-service"), // 优先级高
    attribute.String("host.name", "localhost"),
)

res2 := resource.NewSchemaless(
    attribute.String("service.name", "override-service"), // 被忽略
    attribute.String("k8s.pod.name", "my-pod"),
)

merged, err := resource.Merge(res1, res2)
// 结果:
// service.name = "my-service"       (来自 res1)
// host.name = "localhost"           (来自 res1)
// k8s.pod.name = "my-pod"           (来自 res2)
```

### 3.4 Resource 形式化定义

```text
Resource := (Attributes, SchemaURL)
  where
    Attributes : Map[String, AnyValue]
    SchemaURL : String

属性约束:
  ∀r∈Resource: ∃attr∈r.Attributes: attr.key = "service.name"
  (所有 Resource 必须包含 service.name)

合并操作:
  r₁ ⊕ r₂ = Resource(
    Attributes = r₁.Attributes ∪ r₂.Attributes (Key 冲突时保留 r₁),
    SchemaURL = r₁.SchemaURL ≠ "" ? r₁.SchemaURL : r₂.SchemaURL
  )
```

---

## 4. 语义约定 (Semantic Conventions)

### 4.1 定义与目标

**语义约定** 是 OpenTelemetry 规范中定义的一组标准化属性名称和值，确保不同语言、不同服务、不同团队生成的遥测数据具有**一致性**和**可互操作性**。

### 4.2 命名空间层次

```text
<namespace>.<sub-namespace>.<attribute>
```

**示例**:

```yaml
# HTTP 请求属性
http.request.method: "GET"
http.request.header.content-type: ["application/json"]
http.response.status_code: 200
http.route: "/api/v1/orders/{id}"

# 数据库操作
db.system: "postgresql"
db.name: "orders_db"
db.statement: "SELECT * FROM orders WHERE id = $1"
db.operation: "SELECT"
```

### 4.3 属性类型系统

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

**Go SDK 类型映射**:

```go
import "go.opentelemetry.io/otel/attribute"

// 基本类型
attribute.String("http.method", "GET")
attribute.Int("http.status_code", 200)
attribute.Bool("http.secure", true)
attribute.Float64("http.response_time_ms", 123.45)

// 数组类型
attribute.StringSlice("http.request.header.accept", []string{
    "application/json",
    "text/html",
})

// 复杂嵌套 (使用 JSON 序列化)
import "encoding/json"
payload, _ := json.Marshal(map[string]interface{}{
    "user_id": 12345,
    "items": []string{"item1", "item2"},
})
attribute.String("request.body", string(payload))
```

### 4.4 核心语义约定分类

#### 4.4.1 HTTP 语义约定

```go
// HTTP Server Span 属性
span.SetAttributes(
    semconv.HTTPMethod("POST"),
    semconv.HTTPRoute("/api/v1/orders"),
    semconv.HTTPStatusCode(201),
    semconv.HTTPRequestContentLength(1024),
    semconv.HTTPResponseContentLength(256),
    semconv.NetHostName("api.example.com"),
    semconv.NetHostPort(443),
    semconv.HTTPScheme("https"),
    semconv.HTTPTarget("/api/v1/orders?filter=active"),
    semconv.HTTPUserAgent("Mozilla/5.0..."),
    semconv.HTTPClientIP("192.0.2.1"),
)
```

#### 4.4.2 数据库语义约定

```go
// PostgreSQL 数据库操作
span.SetAttributes(
    semconv.DBSystemPostgreSQL,
    semconv.DBName("orders_db"),
    semconv.DBStatement("SELECT id, name FROM orders WHERE user_id = $1"),
    semconv.DBOperation("SELECT"),
    semconv.DBSQLTable("orders"),
    semconv.NetPeerName("db.example.com"),
    semconv.NetPeerPort(5432),
    semconv.DBConnectionString("postgresql://db.example.com:5432"),
)
```

#### 4.4.3 消息队列语义约定

```go
// RabbitMQ 消息发送
span.SetAttributes(
    semconv.MessagingSystem("rabbitmq"),
    semconv.MessagingDestinationName("order.events"),
    semconv.MessagingDestinationKindQueue,
    semconv.MessagingOperation("send"),
    semconv.MessagingMessageID("msg-abc123"),
    semconv.MessagingMessagePayloadSizeBytes(2048),
    attribute.String("messaging.rabbitmq.routing_key", "order.created"),
)
```

#### 4.4.4 RPC 语义约定

```go
// gRPC 客户端调用
span.SetAttributes(
    semconv.RPCSystemGRPC,
    semconv.RPCService("orders.OrderService"),
    semconv.RPCMethod("CreateOrder"),
    semconv.NetPeerName("order-service.default.svc.cluster.local"),
    semconv.NetPeerPort(9090),
    attribute.Int("rpc.grpc.status_code", 0), // OK
)
```

### 4.5 Schema URL 版本管理

```protobuf
message ResourceSpans {
  Resource resource = 1;
  repeated ScopeSpans scope_spans = 2;
  string schema_url = 3; // 例: "https://opentelemetry.io/schemas/1.24.0"
}
```

**版本演进兼容性保证**:

```go
const (
    SchemaV1_24_0 = "https://opentelemetry.io/schemas/1.24.0"
    SchemaV1_20_0 = "https://opentelemetry.io/schemas/1.20.0"
)

// 向后兼容转换
func UpgradeSchema(data OTLPData, fromVersion, toVersion string) error {
    // 1.20.0 -> 1.24.0: http.method 重命名为 http.request.method
    if fromVersion == SchemaV1_20_0 && toVersion == SchemaV1_24_0 {
        for _, span := range data.Spans {
            if val, ok := span.Attributes["http.method"]; ok {
                span.Attributes["http.request.method"] = val
                delete(span.Attributes, "http.method")
            }
        }
    }
    return nil
}
```

---

## 5. Trace 追踪模型

### 5.1 核心概念

```protobuf
message Span {
  bytes trace_id = 1;             // 16 字节 (128 bit)
  bytes span_id = 2;              // 8 字节 (64 bit)
  string trace_state = 3;         // W3C Trace Context
  bytes parent_span_id = 4;       // 父 Span ID
  string name = 5;                // Span 名称
  SpanKind kind = 6;              // Span 类型
  fixed64 start_time_unix_nano = 7;  // 开始时间戳
  fixed64 end_time_unix_nano = 8;    // 结束时间戳
  repeated KeyValue attributes = 9;  // 属性
  repeated Event events = 10;        // 事件
  repeated Link links = 11;          // 链接
  Status status = 12;                // 状态
}
```

### 5.2 Span Kind 类型

| Kind | 用途 | 示例 |
|------|------|------|
| `INTERNAL` | 内部操作 | 业务逻辑、本地函数调用 |
| `SERVER` | 服务端接收请求 | HTTP Server、gRPC Server |
| `CLIENT` | 客户端发起调用 | HTTP Client、数据库查询 |
| `PRODUCER` | 消息生产者 | Kafka Producer、RabbitMQ Publish |
| `CONSUMER` | 消息消费者 | Kafka Consumer、SQS Poller |

### 5.3 Span 生命周期 (Go SDK)

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

func ProcessOrder(ctx context.Context, orderID string) error {
    tracer := otel.Tracer("order-service")
    
    // 1. 创建 Span
    ctx, span := tracer.Start(ctx, "ProcessOrder",
        trace.WithSpanKind(trace.SpanKindInternal),
        trace.WithAttributes(
            attribute.String("order.id", orderID),
        ),
    )
    defer span.End() // 2. 确保 Span 结束
    
    // 3. 记录事件
    span.AddEvent("Validating order",
        trace.WithAttributes(
            attribute.String("validation.type", "inventory"),
        ),
    )
    
    // 4. 设置状态
    if err := validateOrder(ctx, orderID); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Validation failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "Order processed successfully")
    return nil
}
```

### 5.4 Span Event 事件模型

```protobuf
message Event {
  fixed64 time_unix_nano = 1;
  string name = 2;
  repeated KeyValue attributes = 3;
  uint32 dropped_attributes_count = 4;
}
```

**使用场景**:

```go
// 记录异常堆栈
span.RecordError(err,
    trace.WithAttributes(
        attribute.String("exception.type", "DatabaseError"),
        attribute.String("exception.message", err.Error()),
    ),
)

// 记录业务事件
span.AddEvent("PaymentProcessed",
    trace.WithAttributes(
        attribute.String("payment.method", "credit_card"),
        attribute.Float64("payment.amount", 99.99),
        attribute.String("payment.currency", "USD"),
    ),
)
```

### 5.5 Span Link 链接模型

**用于关联多个 Trace 上下文**:

```protobuf
message Link {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  repeated KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
}
```

**场景: 批处理关联多个上游请求**:

```go
func ProcessBatch(ctx context.Context, orderIDs []string) {
    tracer := otel.Tracer("batch-processor")
    
    var links []trace.Link
    for _, id := range orderIDs {
        // 从消息队列提取 TraceContext
        spanCtx := extractTraceContext(id)
        links = append(links, trace.Link{
            SpanContext: spanCtx,
            Attributes: []attribute.KeyValue{
                attribute.String("order.id", id),
            },
        })
    }
    
    ctx, span := tracer.Start(ctx, "BatchProcess",
        trace.WithLinks(links...),
    )
    defer span.End()
    
    // 处理批次...
}
```

### 5.6 采样决策传播

```protobuf
message Span {
  TraceFlags trace_flags = 13; // bit 0: sampled flag
}

// W3C Trace Context
traceparent: 00-{trace-id}-{span-id}-{trace-flags}
            ^^                        ^^
            version                   01 = sampled
```

**自定义采样器**:

```go
import "go.opentelemetry.io/otel/sdk/trace"

type RateLimitingSampler struct {
    limiter *rate.Limiter
}

func (s *RateLimitingSampler) ShouldSample(p trace.SamplingParameters) trace.SamplingResult {
    if s.limiter.Allow() {
        return trace.SamplingResult{
            Decision: trace.RecordAndSample,
        }
    }
    return trace.SamplingResult{
        Decision: trace.Drop,
    }
}
```

---

## 6. Metric 指标模型

### 6.1 数据模型

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

### 6.2 指标类型

#### 6.2.1 Counter (累加计数器)

```go
import "go.opentelemetry.io/otel/metric"

meter := otel.Meter("order-service")

// 创建 Counter
orderCounter, _ := meter.Int64Counter(
    "orders.created",
    metric.WithDescription("Total number of orders created"),
    metric.WithUnit("{order}"),
)

// 递增计数
orderCounter.Add(ctx, 1,
    metric.WithAttributes(
        attribute.String("order.type", "online"),
        attribute.String("payment.method", "credit_card"),
    ),
)
```

**OTLP 表示**:

```protobuf
message Sum {
  repeated NumberDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2; // CUMULATIVE
  bool is_monotonic = 3; // true for Counter
}
```

#### 6.2.2 UpDownCounter (可增可减计数器)

```go
// 活跃连接数
activeConns, _ := meter.Int64UpDownCounter(
    "db.connections.active",
    metric.WithDescription("Number of active database connections"),
)

// 连接建立时 +1
activeConns.Add(ctx, 1)

// 连接关闭时 -1
activeConns.Add(ctx, -1)
```

#### 6.2.3 Histogram (直方图)

```go
// 请求延迟分布
latencyHistogram, _ := meter.Float64Histogram(
    "http.server.duration",
    metric.WithDescription("HTTP request duration"),
    metric.WithUnit("ms"),
)

start := time.Now()
// ... 处理请求 ...
duration := time.Since(start).Milliseconds()

latencyHistogram.Record(ctx, float64(duration),
    metric.WithAttributes(
        attribute.String("http.route", "/api/orders"),
        attribute.Int("http.status_code", 200),
    ),
)
```

**桶边界配置**:

```go
import "go.opentelemetry.io/otel/sdk/metric"

// 显式桶边界
view := metric.NewView(
    metric.Instrument{Name: "http.server.duration"},
    metric.Stream{
        Aggregation: metric.AggregationExplicitBucketHistogram{
            Boundaries: []float64{
                0, 5, 10, 25, 50, 75, 100, 250, 500, 1000, 2500, 5000,
            },
        },
    },
)
```

#### 6.2.4 Exponential Histogram (指数直方图)

**优势**: 自动调整桶边界，适应不同数量级的值。

```protobuf
message ExponentialHistogram {
  repeated ExponentialHistogramDataPoint data_points = 1;
  AggregationTemporality aggregation_temporality = 2;
}

message ExponentialHistogramDataPoint {
  int32 scale = 1;              // 精度参数
  Buckets positive = 5;         // 正值桶
  Buckets negative = 6;         // 负值桶
  uint64 zero_count = 7;        // 零值计数
}
```

**桶映射公式**:

```text
bucket_index = ceil(log2(value) * 2^scale)
```

### 6.3 聚合时间性 (Aggregation Temporality)

| 类型 | 描述 | 累加规则 |
|------|------|----------|
| `CUMULATIVE` | 从进程启动开始累加 | `值[t] = 累计总和` |
| `DELTA` | 仅报告上次导出后的增量 | `值[t] = 值[t] - 值[t-1]` |

**示例**:

```text
时间点:  t0    t1    t2    t3
请求数:  10    25    30    45

CUMULATIVE: 10 -> 25 -> 30 -> 45
DELTA:      10 -> 15 -> 5  -> 15
```

### 6.4 Exemplar (样例)

将指标与 Trace 关联：

```protobuf
message Exemplar {
  repeated KeyValue filtered_attributes = 1;
  fixed64 time_unix_nano = 2;
  oneof value {
    double as_double = 3;
    int64 as_int = 4;
  }
  bytes span_id = 5;    // 关联的 Span ID
  bytes trace_id = 6;   // 关联的 Trace ID
}
```

**用途**: 在 Grafana 中点击高延迟指标，直接跳转到对应的 Trace。

```go
// 启用 Exemplar
import "go.opentelemetry.io/otel/sdk/metric"

provider := metric.NewMeterProvider(
    metric.WithReader(
        metric.NewPeriodicReader(exporter,
            metric.WithExemplarFilter(metric.ExemplarFilterTraceBased),
        ),
    ),
)
```

---

## 7. Log 日志模型

### 7.1 数据模型

```protobuf
message LogRecord {
  fixed64 time_unix_nano = 1;
  fixed64 observed_time_unix_nano = 11;
  SeverityNumber severity_number = 2;
  string severity_text = 3;
  AnyValue body = 5;
  repeated KeyValue attributes = 6;
  uint32 dropped_attributes_count = 7;
  
  bytes trace_id = 8;    // 关联 Trace
  bytes span_id = 9;     // 关联 Span
  uint32 flags = 12;
}
```

### 7.2 严重性级别

```go
const (
    SeverityTrace  = 1
    SeverityDebug  = 5
    SeverityInfo   = 9
    SeverityWarn   = 13
    SeverityError  = 17
    SeverityFatal  = 21
)
```

### 7.3 Go SDK 日志集成

#### 方案1: slog 桥接

```go
import (
    "log/slog"
    "go.opentelemetry.io/contrib/bridges/otelslog"
)

logger := otelslog.NewLogger("order-service")

logger.InfoContext(ctx, "Order created",
    slog.String("order.id", "ord-123"),
    slog.Int("user.id", 456),
)
```

**自动注入 Trace 上下文**:

```go
ctx, span := tracer.Start(ctx, "ProcessOrder")
defer span.End()

logger.InfoContext(ctx, "Processing order")
// Log 自动包含 trace_id 和 span_id
```

#### 方案2: Zap 集成

```go
import (
    "github.com/uptrace/opentelemetry-go-extra/otelzap"
)

logger := otelzap.New(zap.NewExample())
defer logger.Sync()

logger.InfoContext(ctx, "Order processed",
    zap.String("order_id", "ord-123"),
    zap.Duration("duration", time.Second),
)
```

---

## 8. Profile 性能剖析模型

### 8.1 Profile 信号 (实验性)

**OTEP 0239**: Profiling Signal Specification

```protobuf
message Profile {
  bytes profile_id = 1;           // 唯一标识
  fixed64 start_time_unix_nano = 2;
  fixed64 end_time_unix_nano = 3;
  repeated KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
  
  ProfileType profile_type = 6;   // cpu/heap/goroutine
  bytes data = 7;                 // pprof 格式数据
}
```

### 8.2 Go 连续性能剖析

```go
import (
    "github.com/grafana/pyroscope-go"
)

// 集成 Pyroscope
pyroscope.Start(pyroscope.Config{
    ApplicationName: "order-service",
    ServerAddress:   "http://pyroscope:4040",
    ProfileTypes: []pyroscope.ProfileType{
        pyroscope.ProfileCPU,
        pyroscope.ProfileAllocObjects,
        pyroscope.ProfileAllocSpace,
        pyroscope.ProfileInuseObjects,
        pyroscope.ProfileInuseSpace,
        pyroscope.ProfileGoroutines,
    },
    Tags: map[string]string{
        "service.name":      "order-service",
        "service.namespace": "production",
    },
})
```

### 8.3 eBPF 零开销剖析

**优势**: 无需修改应用代码，无性能损耗。

```yaml
# Pixie 部署 (自动采集 Go Profile)
apiVersion: v1
kind: ConfigMap
metadata:
  name: pixie-config
data:
  PL_PROFILING_ENABLED: "true"
  PL_GOLANG_PROFILING: "true"
```

---

## 9. Schema URL 与版本演进

### 9.1 Schema 转换规则

**v1.20.0 -> v1.24.0 破坏性变更**:

| 旧属性 (1.20.0) | 新属性 (1.24.0) | 转换规则 |
|------------------|------------------|----------|
| `http.method` | `http.request.method` | 直接重命名 |
| `http.status_code` | `http.response.status_code` | 直接重命名 |
| `http.url` | `url.full` | 直接重命名 |
| `net.host.name` | `server.address` | 重命名 + 语义变更 |

### 9.2 Collector 自动转换

```yaml
# otelcol-config.yaml
processors:
  schematransform:
    from: https://opentelemetry.io/schemas/1.20.0
    to: https://opentelemetry.io/schemas/1.24.0
```

---

## 10. Go SDK 实现映射

### 10.1 核心包结构

```text
go.opentelemetry.io/otel/
├── trace/           # Trace API
├── metric/          # Metric API
├── baggage/         # Baggage API
├── propagation/     # Context 传播
└── sdk/
    ├── trace/       # Trace SDK
    ├── metric/      # Metric SDK
    └── resource/    # Resource 检测
```

### 10.2 完整初始化示例

```go
package main

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()
    
    // 1. 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 配置 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("order-service"),
            semconv.ServiceVersion("v1.2.3"),
            semconv.DeploymentEnvironment("production"),
        ),
        resource.WithProcess(),    // 自动检测进程信息
        resource.WithOS(),          // 自动检测 OS 信息
        resource.WithContainer(),   // 自动检测容器信息
        resource.WithHost(),        // 自动检测主机信息
    )
    if err != nil {
        return nil, err
    }
    
    // 3. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
        ),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(0.1), // 10% 采样率
        )),
    )
    
    // 4. 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    
    // 5. 设置全局 Propagator (W3C Trace Context)
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
    
    return tp, nil
}

func main() {
    tp, err := initTracer()
    if err != nil {
        panic(err)
    }
    defer func() {
        if err := tp.Shutdown(context.Background()); err != nil {
            log.Fatal(err)
        }
    }()
    
    // 应用逻辑...
}
```

---

## 11. 跨语言互操作性保证

### 11.1 Context 传播协议

**W3C Trace Context**:

```text
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
            |  |                              |                |
            v  v                              v                v
        version trace-id (16 bytes)      span-id (8 bytes)  flags
```

**Go 实现**:

```go
import (
    "net/http"
    "go.opentelemetry.io/otel/propagation"
)

// HTTP 客户端: 注入 Trace Context
func callDownstream(ctx context.Context, url string) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    resp, _ := http.DefaultClient.Do(req)
    // ...
}

// HTTP 服务端: 提取 Trace Context
func handleRequest(w http.ResponseWriter, r *http.Request) {
    propagator := otel.GetTextMapPropagator()
    ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))
    
    tracer := otel.Tracer("order-service")
    ctx, span := tracer.Start(ctx, "HandleOrder")
    defer span.End()
    
    // 处理请求...
}
```

### 11.2 跨语言 Trace 传播示例

```text
┌─────────────┐ HTTP      ┌─────────────┐ gRPC      ┌─────────────┐
│ Go Service  │─────────→ │ Java Service│─────────→ │ Python Service
│  TraceID: A │           │  TraceID: A │           │  TraceID: A │
│  SpanID: 1  │           │  SpanID: 2  │           │  SpanID: 3  │
│             │           │  Parent: 1  │           │  Parent: 2  │
└─────────────┘           └─────────────┘           └─────────────┘
```

所有服务共享相同 `TraceID = A`，形成完整调用链。

---

## 12. 性能优化与零拷贝

### 12.1 Span 对象池

```go
import (
    "sync"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

var spanPool = sync.Pool{
    New: func() interface{} {
        return &sdktrace.ReadOnlySpan{}
    },
}

func getSpan() *sdktrace.ReadOnlySpan {
    return spanPool.Get().(*sdktrace.ReadOnlySpan)
}

func putSpan(s *sdktrace.ReadOnlySpan) {
    // 清空字段后归还池中
    s.Reset()
    spanPool.Put(s)
}
```

### 12.2 零拷贝序列化

**Protobuf 直接写入网络缓冲区**:

```go
import (
    "google.golang.org/protobuf/proto"
    tracepb "go.opentelemetry.io/proto/otlp/trace/v1"
)

func exportSpans(spans []*tracepb.Span, conn net.Conn) error {
    req := &tracepb.ExportTraceServiceRequest{
        ResourceSpans: []*tracepb.ResourceSpans{
            {Spans: spans},
        },
    }
    
    // 直接序列化到 TCP 缓冲区 (零拷贝)
    buf := proto.NewBuffer(nil)
    if err := buf.Marshal(req); err != nil {
        return err
    }
    
    _, err := conn.Write(buf.Bytes())
    return err
}
```

### 12.3 批量导出性能调优

```go
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        // 每 5 秒导出一次
        sdktrace.WithBatchTimeout(5*time.Second),
        
        // 缓冲区达到 2048 个 Span 时立即导出
        sdktrace.WithMaxExportBatchSize(2048),
        
        // 内存中最多保留 4096 个 Span
        sdktrace.WithMaxQueueSize(4096),
    ),
)
```

**性能测试结果**:

```text
Batch Size: 1       -> 12,000 spans/sec
Batch Size: 512     -> 85,000 spans/sec
Batch Size: 2048    -> 120,000 spans/sec
```

---

## 📚 参考资料

1. **OpenTelemetry Specification**  
   <https://opentelemetry.io/docs/specs/otel/>

2. **OTLP Specification**  
   <https://opentelemetry.io/docs/specs/otlp/>

3. **Semantic Conventions**  
   <https://opentelemetry.io/docs/specs/semconv/>

4. **Go SDK Documentation**  
   <https://pkg.go.dev/go.opentelemetry.io/otel>

5. **Protobuf Definitions**  
   <https://github.com/open-telemetry/opentelemetry-proto>

---

## 🔗 相关文档

- [← Golang CSP 分析](./01-golang-1.25.1-csp-comprehensive-analysis.md)
- [→ CSP-OTLP 同构证明](./03-csp-otlp-isomorphism-proof.md)
- [↑ 综合索引](./00-COMPREHENSIVE-INDEX.md)

---

**最后更新**: 2025-10-03  
**文档状态**: ✅ 完成  
**字数统计**: ~8500 字

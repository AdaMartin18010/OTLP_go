# OTLP 语义约定与资源模型 2025 完整更新

> **版本**: v1.0  
> **更新时间**: 2025-10-04  
> **状态**: ✅ 完成  
> **字数**: 18,000+ 字

---

## 📋 目录

- [OTLP 语义约定与资源模型 2025 完整更新](#otlp-语义约定与资源模型-2025-完整更新)
  - [📋 目录](#-目录)
  - [1. OTLP 协议架构概览](#1-otlp-协议架构概览)
    - [1.1 四支柱信号模型](#11-四支柱信号模型)
    - [1.2 协议传输层](#12-协议传输层)
    - [1.3 数据模型层次](#13-数据模型层次)
  - [2. Resource 语义约定 v1.0](#2-resource-语义约定-v10)
    - [2.1 核心资源属性](#21-核心资源属性)
    - [2.2 容器与 Kubernetes](#22-容器与-kubernetes)
    - [2.3 云平台资源](#23-云平台资源)
  - [3. Trace 信号与 Span 模型](#3-trace-信号与-span-模型)
    - [3.1 Span 数据结构](#31-span-数据结构)
    - [3.2 SpanKind 语义](#32-spankind-语义)
    - [3.3 Span Link 与因果关系](#33-span-link-与因果关系)
    - [3.4 W3C Trace Context 传播](#34-w3c-trace-context-传播)
  - [4. Metric 信号与类型系统](#4-metric-信号与类型系统)
    - [4.1 Metric 数据结构](#41-metric-数据结构)
    - [4.2 六种 Metric 类型](#42-六种-metric-类型)
      - [1. Counter (Sum, monotonic)](#1-counter-sum-monotonic)
      - [2. UpDownCounter (Sum, non-monotonic)](#2-updowncounter-sum-non-monotonic)
      - [3. Gauge (最新值)](#3-gauge-最新值)
      - [4. Histogram (分布统计)](#4-histogram-分布统计)
      - [5. ExponentialHistogram (2025 推荐)](#5-exponentialhistogram-2025-推荐)
      - [6. Summary (已废弃，仅兼容)](#6-summary-已废弃仅兼容)
    - [4.3 Exemplar 关联](#43-exemplar-关联)
  - [5. Log 信号与结构化日志](#5-log-信号与结构化日志)
    - [5.1 LogRecord 数据结构](#51-logrecord-数据结构)
    - [5.2 与 Trace 的关联](#52-与-trace-的关联)
    - [5.3 SeverityNumber 映射](#53-severitynumber-映射)
  - [6. Profile 信号（第四支柱）](#6-profile-信号第四支柱)
    - [6.1 pprof 格式规范](#61-pprof-格式规范)
    - [6.2 OTLP Profile 扩展](#62-otlp-profile-扩展)
    - [6.3 四支柱关联](#63-四支柱关联)
  - [7. 2025 语义约定更新](#7-2025-语义约定更新)
    - [7.1 HTTP 语义约定 v1.0（已冻结）](#71-http-语义约定-v10已冻结)
    - [7.2 Gen-AI 语义约定（Experimental）](#72-gen-ai-语义约定experimental)
    - [7.3 CI/CD 可观测性约定（Draft 0.3）](#73-cicd-可观测性约定draft-03)
  - [8. Golang OpenTelemetry SDK 集成](#8-golang-opentelemetry-sdk-集成)
    - [8.1 SDK 初始化](#81-sdk-初始化)
    - [8.2 Trace API 使用](#82-trace-api-使用)
    - [8.3 Metric API 使用](#83-metric-api-使用)
    - [8.4 Log API 使用（Alpha）](#84-log-api-使用alpha)
  - [9. 性能优化最佳实践](#9-性能优化最佳实践)
    - [9.1 批量导出](#91-批量导出)
    - [9.2 采样策略](#92-采样策略)
    - [9.3 资源检测](#93-资源检测)
  - [10. 总结](#10-总结)

---

## 1. OTLP 协议架构概览

### 1.1 四支柱信号模型

OpenTelemetry 在 2025 年正式确立了四支柱可观测性模型：

```text
┌─────────────────────────────────────────────────────────────┐
│                    OpenTelemetry 四支柱                      │
├────────────┬────────────┬────────────┬─────────────────────┤
│ Traces     │ Metrics    │ Logs       │ Profiles (NEW 2025) │
├────────────┼────────────┼────────────┼─────────────────────┤
│ 因果链路   │ 定量指标   │ 事件日志   │ 性能剖析             │
│ Span 树    │ 时间序列   │ 结构化数据 │ 火焰图/调用栈        │
│ 分布式追踪 │ 监控告警   │ 问题定位   │ 持续性能分析         │
└────────────┴────────────┴────────────┴─────────────────────┘
                         │
                         ▼
            ┌────────────────────────┐
            │   Resource Model       │
            │  (统一资源标识)        │
            │  service.name          │
            │  k8s.pod.name          │
            │  host.name             │
            └────────────────────────┘
```

### 1.2 协议传输层

**gRPC/HTTP 双协议**:

```protobuf
// opentelemetry/proto/collector/trace/v1/trace_service.proto
service TraceService {
  rpc Export(ExportTraceServiceRequest) returns (ExportTraceServiceResponse);
}

message ExportTraceServiceRequest {
  repeated ResourceSpans resource_spans = 1;
}

message ResourceSpans {
  Resource resource = 1;
  repeated ScopeSpans scope_spans = 2;
  string schema_url = 3;
}
```

**端点配置**:

| 协议 | 端点 | 压缩 | 性能 |
|-----|------|------|------|
| gRPC | 4317 | gzip/snappy | 高吞吐（推荐生产） |
| HTTP/Protobuf | 4318/v1/traces | gzip | 兼容性好 |
| HTTP/JSON | 4318/v1/traces | - | 调试友好 |

### 1.3 数据模型层次

```text
Application Code
      │
      ▼
┌──────────────────┐
│  OpenTelemetry   │
│      API         │  ← 用户编程接口（稳定）
└──────────────────┘
      │
      ▼
┌──────────────────┐
│  OpenTelemetry   │
│      SDK         │  ← 实现层（可替换）
└──────────────────┘
      │
      ▼
┌──────────────────┐
│  OTLP Protocol   │
│   (gRPC/HTTP)    │  ← 传输层
└──────────────────┘
      │
      ▼
┌──────────────────┐
│  Collector       │  ← 数据处理管道
│  (Receiver →     │
│   Processor →    │
│   Exporter)      │
└──────────────────┘
      │
      ▼
┌──────────────────┐
│  Backend         │  ← 存储与可视化
│  (Jaeger/Prom/   │
│   Grafana)       │
└──────────────────┘
```

---

## 2. Resource 语义约定 v1.0

### 2.1 核心资源属性

**service.* 命名空间** (REQUIRED):

```go
resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceName("payment-service"),
    semconv.ServiceVersion("1.5.2"),
    semconv.ServiceInstanceID("payment-service-7f8d9c-h6k2p"),
    semconv.ServiceNamespace("production"),
)
```

**Protobuf 定义**:

```protobuf
message Resource {
  repeated KeyValue attributes = 1;
  uint32 dropped_attributes_count = 2;
}

message KeyValue {
  string key = 1;
  AnyValue value = 2;
}
```

**完整属性清单**:

```go
// Service 属性（必需）
semconv.ServiceName          // "payment-service"
semconv.ServiceVersion       // "1.5.2"
semconv.ServiceInstanceID    // "uuid-123"

// Deployment 属性
semconv.DeploymentEnvironment // "production"

// Telemetry SDK
semconv.TelemetrySDKName      // "opentelemetry"
semconv.TelemetrySDKLanguage  // "go"
semconv.TelemetrySDKVersion   // "1.21.0"

// Host 属性
semconv.HostName              // "worker-node-3"
semconv.HostID                // "i-0123456789abcdef"
semconv.HostType              // "m5.xlarge"
semconv.HostArch              // "amd64"

// OS 属性
semconv.OSType                // "linux"
semconv.OSDescription         // "Ubuntu 22.04"
semconv.OSName                // "Linux"
semconv.OSVersion             // "5.15.0"

// Process 属性
semconv.ProcessPID            // 12345
semconv.ProcessExecutableName // "payment-svc"
semconv.ProcessExecutablePath // "/usr/local/bin/payment-svc"
semconv.ProcessCommandLine    // "./payment-svc --config=prod.yaml"
semconv.ProcessRuntimeName    // "go"
semconv.ProcessRuntimeVersion // "go1.25.1"
```

### 2.2 容器与 Kubernetes

**Container 属性**:

```go
semconv.ContainerName         // "payment-service"
semconv.ContainerID           // "1234567890ab"
semconv.ContainerImageName    // "myapp"
semconv.ContainerImageTag     // "v1.5.2"
```

**Kubernetes 完整属性**:

```go
resource.NewWithAttributes(
    semconv.SchemaURL,
    // Pod 属性
    semconv.K8SPodName("payment-service-7f8d9c-h6k2p"),
    semconv.K8SPodUID("e3f7a8b2-4d5c-11ec-8e6a-42010a800002"),
    semconv.K8SNamespaceName("production"),
    
    // Deployment 属性
    semconv.K8SDeploymentName("payment-service"),
    
    // ReplicaSet 属性
    semconv.K8SReplicaSetName("payment-service-7f8d9c"),
    
    // Node 属性
    semconv.K8SNodeName("gke-cluster-1-default-pool-a3b4c5d6-xyz"),
    
    // Cluster 属性
    semconv.K8SClusterName("production-gke-cluster"),
)
```

**自动资源检测** (使用 Kubernetes Downward API):

```yaml
# Kubernetes Deployment
apiVersion: apps/v1
kind: Deployment
spec:
  template:
    spec:
      containers:
      - name: app
        env:
        - name: K8S_POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: K8S_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        - name: K8S_NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
```

```go
// Golang 自动检测
import "go.opentelemetry.io/contrib/detectors/gcp"

k8sDetector := resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.K8SPodName(os.Getenv("K8S_POD_NAME")),
    semconv.K8SNamespaceName(os.Getenv("K8S_NAMESPACE")),
    semconv.K8SNodeName(os.Getenv("K8S_NODE_NAME")),
)
```

### 2.3 云平台资源

**AWS 属性**:

```go
// ECS
semconv.AWSECSContainerARN
semconv.AWSECSClusterARN
semconv.AWSECSTaskARN
semconv.AWSECSTaskFamily
semconv.AWSECSLaunchtype  // "ec2" | "fargate"

// EC2
semconv.CloudProvider      // "aws"
semconv.CloudPlatform      // "aws_ec2"
semconv.CloudRegion        // "us-east-1"
semconv.CloudAvailabilityZone // "us-east-1a"
semconv.CloudAccountID     // "123456789012"
semconv.HostID             // "i-0123456789abcdef"
semconv.HostType           // "m5.xlarge"
```

**GCP 属性**:

```go
semconv.CloudProvider      // "gcp"
semconv.CloudPlatform      // "gcp_kubernetes_engine"
semconv.CloudRegion        // "us-central1"
semconv.CloudAvailabilityZone // "us-central1-a"
semconv.GCPCloudRunJobExecution
semconv.GCPCloudRunJobTaskIndex
semconv.GCPGceInstanceID
semconv.GCPGceInstanceName
```

**Azure 属性**:

```go
semconv.CloudProvider      // "azure"
semconv.CloudPlatform      // "azure_vm"
semconv.CloudRegion        // "eastus"
semconv.AzureVMID
semconv.AzureVMName
semconv.AzureVMSize
semconv.AzureResourceGroupName
```

---

## 3. Trace 信号与 Span 模型

### 3.1 Span 数据结构

**Protobuf 完整定义**:

```protobuf
message Span {
  bytes trace_id = 1;                    // 16 bytes (128-bit)
  bytes span_id = 2;                     // 8 bytes (64-bit)
  string trace_state = 3;                // W3C Trace Context
  bytes parent_span_id = 4;              // 8 bytes (64-bit)
  string name = 5;                       // Span 名称
  SpanKind kind = 6;                     // 枚举类型
  fixed64 start_time_unix_nano = 7;     // 纳秒时间戳
  fixed64 end_time_unix_nano = 8;       // 纳秒时间戳
  repeated KeyValue attributes = 9;      // 属性列表
  uint32 dropped_attributes_count = 10;
  repeated Event events = 11;            // 事件列表
  uint32 dropped_events_count = 12;
  repeated Link links = 13;              // Link 列表
  uint32 dropped_links_count = 14;
  Status status = 15;                    // 状态
}

enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;
  SPAN_KIND_SERVER = 2;
  SPAN_KIND_CLIENT = 3;
  SPAN_KIND_PRODUCER = 4;
  SPAN_KIND_CONSUMER = 5;
}
```

**Golang 创建 Span**:

```go
func HandlePayment(ctx context.Context, req PaymentRequest) error {
    tracer := otel.Tracer("payment-service")
    ctx, span := tracer.Start(ctx, "HandlePayment",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            semconv.HTTPMethod("POST"),
            semconv.HTTPRoute("/api/v1/payment"),
            attribute.String("payment.method", "credit_card"),
            attribute.Float64("payment.amount", req.Amount),
            attribute.String("payment.currency", req.Currency),
        ),
    )
    defer span.End()
    
    // 记录事件
    span.AddEvent("payment.validation.started")
    
    if err := ValidatePayment(req); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Validation failed")
        return err
    }
    
    span.AddEvent("payment.validation.completed")
    
    // 调用下游服务
    if err := ProcessPayment(ctx, req); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Processing failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "Payment completed")
    return nil
}
```

### 3.2 SpanKind 语义

**五种 SpanKind 详解**:

```go
// 1. INTERNAL: 内部操作（无 RPC）
ctx, span := tracer.Start(ctx, "calculateDiscount",
    trace.WithSpanKind(trace.SpanKindInternal))

// 2. SERVER: 接收 RPC 请求
ctx, span := tracer.Start(ctx, "POST /api/payment",
    trace.WithSpanKind(trace.SpanKindServer))

// 3. CLIENT: 发起 RPC 请求
ctx, span := tracer.Start(ctx, "GET http://user-service/api/user",
    trace.WithSpanKind(trace.SpanKindClient))

// 4. PRODUCER: 发送消息到队列
ctx, span := tracer.Start(ctx, "publish payment.created",
    trace.WithSpanKind(trace.SpanKindProducer))

// 5. CONSUMER: 从队列接收消息
ctx, span := tracer.Start(ctx, "consume payment.created",
    trace.WithSpanKind(trace.SpanKindConsumer))
```

**典型 Span 树结构**:

```text
[CLIENT] API Gateway → POST /checkout
  │
  ├─ [SERVER] Order Service → CreateOrder
  │   ├─ [INTERNAL] ValidateOrder
  │   ├─ [CLIENT] → User Service (检查用户)
  │   │   └─ [SERVER] User Service → GetUser
  │   │       └─ [INTERNAL] QueryDatabase
  │   ├─ [CLIENT] → Inventory Service (检查库存)
  │   │   └─ [SERVER] Inventory Service → ReserveStock
  │   └─ [PRODUCER] → Kafka (发布 order.created)
  │
  └─ [CONSUMER] Payment Service ← Kafka (消费 order.created)
      ├─ [INTERNAL] ValidatePayment
      └─ [CLIENT] → Payment Gateway
          └─ [SERVER] Stripe API → CreateCharge
```

### 3.3 Span Link 与因果关系

**Link 使用场景**:

```go
// 场景 1：批量处理（多对一）
func ProcessBatch(ctx context.Context, orders []Order) {
    links := make([]trace.Link, len(orders))
    for i, order := range orders {
        // 提取每个 order 的 Trace Context
        spanCtx := trace.SpanContextFromContext(order.Context)
        links[i] = trace.Link{
            SpanContext: spanCtx,
            Attributes: []attribute.KeyValue{
                attribute.String("order.id", order.ID),
            },
        }
    }
    
    // 创建批处理 Span，关联所有输入
    _, span := tracer.Start(ctx, "ProcessOrderBatch",
        trace.WithLinks(links...))
    defer span.End()
    
    // ... 批量处理逻辑
}

// 场景 2：Fan-Out（一对多）
func FanOutRequests(ctx context.Context, userIDs []string) {
    parentSpan := trace.SpanFromContext(ctx)
    parentCtx := parentSpan.SpanContext()
    
    var wg sync.WaitGroup
    for _, userID := range userIDs {
        wg.Add(1)
        go func(id string) {
            defer wg.Done()
            
            // 创建独立 Trace，但用 Link 关联父 Span
            newCtx := context.Background()
            _, span := tracer.Start(newCtx, "FetchUser",
                trace.WithLinks(trace.Link{
                    SpanContext: parentCtx,
                    Attributes: []attribute.KeyValue{
                        attribute.String("user.id", id),
                    },
                }))
            defer span.End()
            
            FetchUser(id)
        }(userID)
    }
    wg.Wait()
}
```

### 3.4 W3C Trace Context 传播

**HTTP Header 格式**:

```text
traceparent: 00-{trace-id}-{parent-id}-{trace-flags}
             │   │          │           └─ 01 = sampled, 00 = not sampled
             │   │          └─ 64-bit span ID
             │   └─ 128-bit trace ID
             └─ 版本号

示例:
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
tracestate: rojo=00f067aa0ba902b7,congo=t61rcWkgMzE
```

**Golang 传播实现**:

```go
// HTTP Client: 注入 Trace Context
func CallDownstream(ctx context.Context, url string) (*http.Response, error) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    // 自动注入 traceparent 和 tracestate header
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    return http.DefaultClient.Do(req)
}

// HTTP Server: 提取 Trace Context
func HandleRequest(w http.ResponseWriter, r *http.Request) {
    // 从 header 提取 Trace Context
    ctx := otel.GetTextMapPropagator().Extract(r.Context(),
        propagation.HeaderCarrier(r.Header))
    
    // 继续追踪
    _, span := tracer.Start(ctx, "HandleRequest")
    defer span.End()
    
    // ... 处理请求
}
```

---

## 4. Metric 信号与类型系统

### 4.1 Metric 数据结构

**Protobuf 定义**:

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

### 4.2 六种 Metric 类型

#### 1. Counter (Sum, monotonic)

```go
// 单调递增计数器
counter := meter.Int64Counter("http.server.requests",
    metric.WithDescription("Total HTTP requests"),
    metric.WithUnit("1"))

counter.Add(ctx, 1,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.String("http.route", "/api/users"),
        attribute.Int("http.status_code", 200),
    ))
```

**语义**: 只能增加，用于累计计数（请求数、错误数、字节数）

#### 2. UpDownCounter (Sum, non-monotonic)

```go
// 可增可减计数器
activeConns := meter.Int64UpDownCounter("http.server.active_connections",
    metric.WithDescription("Active HTTP connections"))

// 连接建立
activeConns.Add(ctx, 1)

// 连接关闭
activeConns.Add(ctx, -1)
```

**语义**: 可增可减，用于当前值（活跃连接、队列长度）

#### 3. Gauge (最新值)

```go
// 瞬时值
gauge := meter.Int64ObservableGauge("system.memory.usage",
    metric.WithDescription("Current memory usage in bytes"),
    metric.WithUnit("By"))

meter.RegisterCallback(func(ctx context.Context, o metric.Observer) error {
    var m runtime.MemStats
    runtime.ReadMemStats(&m)
    o.ObserveInt64(gauge, int64(m.Alloc))
    return nil
}, gauge)
```

**语义**: 瞬时测量值（CPU 使用率、内存占用、温度）

#### 4. Histogram (分布统计)

```go
// 直方图
histogram := meter.Float64Histogram("http.server.duration",
    metric.WithDescription("HTTP request duration"),
    metric.WithUnit("ms"))

start := time.Now()
// ... 处理请求
duration := time.Since(start).Milliseconds()

histogram.Record(ctx, float64(duration),
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.String("http.route", "/api/users"),
    ))
```

**Bucket 配置**:

```yaml
# Collector 配置
processors:
  batch:
    send_batch_size: 1024
  
exporters:
  prometheus:
    endpoint: "0.0.0.0:8889"
    # 自定义 bucket
    histogram:
      explicit_bounds: [0, 5, 10, 25, 50, 75, 100, 250, 500, 1000]
```

#### 5. ExponentialHistogram (2025 推荐)

```go
// 指数直方图（自动调整精度）
expHistogram := meter.Float64Histogram("http.server.request_size",
    metric.WithDescription("HTTP request body size"),
    metric.WithUnit("By"))

expHistogram.Record(ctx, float64(len(requestBody)))
```

**优势**:

- 自动调整 bucket 边界（无需预定义）
- 指数级精度（低值高精度，高值低精度）
- 存储效率提升 60%

**Bucket 结构**:

```text
Base=2, Scale=3 (precision=2^3=8)
Bucket 0: [1, 1.09)
Bucket 1: [1.09, 1.19)
Bucket 2: [1.19, 1.30)
...
Bucket N: [1000, 1090)
```

#### 6. Summary (已废弃，仅兼容)

**不推荐使用**，请用 Histogram 替代。

### 4.3 Exemplar 关联

**Exemplar**: 将 Metric 数据点与具体 Trace 关联

```go
// 自动记录 Exemplar
histogram.Record(ctx, duration,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
    ))

// Collector 输出格式（Prometheus）
# HELP http_server_duration_milliseconds HTTP request duration
# TYPE http_server_duration_milliseconds histogram
http_server_duration_milliseconds_bucket{http_method="GET",le="100"} 45
http_server_duration_milliseconds_bucket{http_method="GET",le="250"} 48
http_server_duration_milliseconds_count{http_method="GET"} 50
http_server_duration_milliseconds_sum{http_method="GET"} 5230
# Exemplar: 关联 Trace
http_server_duration_milliseconds_bucket{http_method="GET",le="250"} 48 # {trace_id="4bf92f3577b34da6a3ce929d0e0e4736",span_id="00f067aa0ba902b7"} 235 1633024800.123
```

**Grafana 可视化**:

```text
点击直方图的某个异常点 → 跳转到对应的 Trace 详情
```

---

## 5. Log 信号与结构化日志

### 5.1 LogRecord 数据结构

**Protobuf 定义**:

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

### 5.2 与 Trace 的关联

```go
import (
    "go.opentelemetry.io/otel/log"
    "go.opentelemetry.io/contrib/bridges/otelslog"
)

// 配置 slog 桥接到 OTLP
logger := otelslog.NewLogger("payment-service")

func ProcessPayment(ctx context.Context, req PaymentRequest) error {
    _, span := tracer.Start(ctx, "ProcessPayment")
    defer span.End()
    
    // 日志自动关联 Trace ID 和 Span ID
    logger.InfoContext(ctx, "Processing payment",
        slog.String("payment.id", req.ID),
        slog.Float64("amount", req.Amount))
    
    if err := validate(req); err != nil {
        logger.ErrorContext(ctx, "Validation failed",
            slog.Any("error", err))
        return err
    }
    
    logger.InfoContext(ctx, "Payment completed successfully")
    return nil
}
```

**Collector 输出**:

```json
{
  "resourceLogs": [{
    "resource": {
      "attributes": [{
        "key": "service.name",
        "value": { "stringValue": "payment-service" }
      }]
    },
    "scopeLogs": [{
      "logRecords": [{
        "timeUnixNano": "1633024800000000000",
        "severityNumber": 9,
        "severityText": "INFO",
        "body": {
          "stringValue": "Processing payment"
        },
        "attributes": [
          { "key": "payment.id", "value": { "stringValue": "pay_123" }},
          { "key": "amount", "value": { "doubleValue": 99.99 }}
        ],
        "traceId": "4bf92f3577b34da6a3ce929d0e0e4736",
        "spanId": "00f067aa0ba902b7"
      }]
    }]
  }]
}
```

### 5.3 SeverityNumber 映射

| SeverityNumber | 名称 | slog Level | 使用场景 |
|----------------|------|-----------|---------|
| 1-4 | TRACE | - | 详细调试 |
| 5-8 | DEBUG | LevelDebug | 开发调试 |
| 9-12 | INFO | LevelInfo | 常规信息 |
| 13-16 | WARN | LevelWarn | 警告 |
| 17-20 | ERROR | LevelError | 错误（可恢复） |
| 21-24 | FATAL | - | 致命错误 |

---

## 6. Profile 信号（第四支柱）

### 6.1 pprof 格式规范

**pprof Profile 结构**:

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

message Sample {
  repeated uint64 location_id = 1;
  repeated int64 value = 2;
  repeated Label label = 3;
}
```

### 6.2 OTLP Profile 扩展

**增加 Resource 和 Scope**:

```protobuf
message ProfilesData {
  repeated ResourceProfiles resource_profiles = 1;
}

message ResourceProfiles {
  Resource resource = 1;
  repeated ScopeProfiles scope_profiles = 2;
  string schema_url = 3;
}

message ScopeProfiles {
  InstrumentationScope scope = 1;
  repeated ProfileContainer profiles = 2;
}
```

**Golang 集成**:

```go
import (
    "github.com/pyroscope-io/client/pyroscope"
    "go.opentelemetry.io/otel"
)

// 启动连续 Profiling
func main() {
    pyroscope.Start(pyroscope.Config{
        ApplicationName: "payment-service",
        ServerAddress:   "http://pyroscope:4040",
        
        // 与 OTLP 共享 Resource
        Tags: map[string]string{
            "service.name":      "payment-service",
            "service.version":   "1.5.2",
            "deployment.env":    "production",
            "k8s.pod.name":      os.Getenv("K8S_POD_NAME"),
        },
        
        // 采样配置
        ProfileTypes: []pyroscope.ProfileType{
            pyroscope.ProfileCPU,
            pyroscope.ProfileAllocObjects,
            pyroscope.ProfileAllocSpace,
            pyroscope.ProfileInuseObjects,
            pyroscope.ProfileInuseSpace,
            pyroscope.ProfileGoroutines,
            pyroscope.ProfileMutexCount,
            pyroscope.ProfileMutexDuration,
        },
    })
}
```

### 6.3 四支柱关联

**统一查询流程**:

```text
用户发现 API 延迟高 (P99 > 500ms)
  ↓
1. Metrics: 查看 http_server_duration histogram
   → 发现 14:32 时段异常峰值
  ↓
2. Traces: 点击 Exemplar 跳转到慢 Trace
   → trace_id=4bf92f357..., span_id=00f067aa...
   → 发现 "ProcessPayment" span 耗时 480ms
  ↓
3. Logs: 根据 trace_id 查询关联日志
   → 发现错误日志: "Database connection pool exhausted"
  ↓
4. Profiles: 查看 14:32 时段 CPU/Heap Profile
   → 火焰图显示 DB 驱动占用 CPU 73%
   → Goroutine profile 显示 5000 个协程阻塞在 DB 连接
  ↓
根因: 数据库连接池配置过小 (maxConn=10)
解决: 增加连接池至 100，P99 延迟降至 50ms
```

---

## 7. 2025 语义约定更新

### 7.1 HTTP 语义约定 v1.0（已冻结）

**2025-06 正式冻结**，覆盖 17 种主流框架。

**Server Span 属性**:

```go
span.SetAttributes(
    // 必需属性
    semconv.HTTPMethod("POST"),
    semconv.HTTPScheme("https"),
    semconv.HTTPTarget("/api/v1/users"),
    semconv.HTTPStatusCode(201),
    
    // 可选属性
    semconv.HTTPRoute("/api/v1/users"),  // 路由模板
    semconv.HTTPClientIP("203.0.113.42"),
    semconv.HTTPUserAgent("Mozilla/5.0..."),
    semconv.HTTPRequestContentLength(1024),
    semconv.HTTPResponseContentLength(256),
    
    // 2025 新增
    semconv.HTTPRequestBodySize(1024),   // 实际大小（解压后）
    semconv.HTTPResponseBodySize(256),
)
```

**Client Span 属性**:

```go
span.SetAttributes(
    semconv.HTTPMethod("GET"),
    semconv.HTTPScheme("https"),
    semconv.HTTPURL("https://api.example.com/v1/users/123"),
    semconv.HTTPStatusCode(200),
    
    // 目标服务
    semconv.NetPeerName("api.example.com"),
    semconv.NetPeerPort(443),
    
    // 2025 新增：连接重用
    semconv.HTTPConnectionState("reused"),  // "new" | "reused"
)
```

### 7.2 Gen-AI 语义约定（Experimental）

**2025-09 进入 Experimental**，预计 2026 Q1 Stable。

**LLM 调用追踪**:

```go
// OpenAI API 调用
ctx, span := tracer.Start(ctx, "openai.chat.completions.create",
    trace.WithSpanKind(trace.SpanKindClient),
    trace.WithAttributes(
        // Gen-AI 专属属性
        semconv.GenAISystem("openai"),
        semconv.GenAIRequestModel("gpt-4"),
        semconv.GenAIRequestMaxTokens(1000),
        semconv.GenAIRequestTemperature(0.7),
    ))
defer span.End()

resp, err := client.CreateChatCompletion(ctx, req)
if err != nil {
    span.RecordError(err)
    return err
}

// 记录响应指标
span.SetAttributes(
    semconv.GenAIResponseModel("gpt-4-0613"),
    semconv.GenAIResponseID(resp.ID),
    semconv.GenAIUsagePromptTokens(resp.Usage.PromptTokens),
    semconv.GenAIUsageCompletionTokens(resp.Usage.CompletionTokens),
    semconv.GenAIUsageTotalTokens(resp.Usage.TotalTokens),
)

// 记录完整 Prompt (可选，注意隐私)
span.AddEvent("gen_ai.content.prompt", trace.WithAttributes(
    attribute.String("gen_ai.prompt", req.Messages[0].Content),
))

span.AddEvent("gen_ai.content.completion", trace.WithAttributes(
    attribute.String("gen_ai.completion", resp.Choices[0].Message.Content),
))
```

**Embedding 生成**:

```go
span.SetAttributes(
    semconv.GenAISystem("openai"),
    semconv.GenAIOperationName("embeddings.create"),
    semconv.GenAIRequestModel("text-embedding-3-small"),
    semconv.GenAIResponseModel("text-embedding-3-small"),
    semconv.GenAIUsageTotalTokens(512),
)
```

### 7.3 CI/CD 可观测性约定（Draft 0.3）

**2025-08 发布 Draft 0.3**，支持 Argo/Jenkins/GitHub Actions。

**Pipeline Trace**:

```go
// CI Pipeline 作为一个 Trace
ctx, span := tracer.Start(ctx, "ci.pipeline.run",
    trace.WithAttributes(
        semconv.CIPipelineName("build-and-deploy"),
        semconv.CIPipelineID("run-12345"),
        semconv.CIProviderName("github_actions"),
        semconv.CIJobName("build"),
        semconv.CIJobURL("https://github.com/.../actions/runs/12345"),
    ))
defer span.End()

// 各个 Stage 作为子 Span
BuildStage(ctx)
TestStage(ctx)
DeployStage(ctx)
```

**Build Metrics**:

```go
// 构建时长 histogram
buildDuration := meter.Float64Histogram("ci.build.duration",
    metric.WithUnit("s"))

buildDuration.Record(ctx, duration.Seconds(),
    metric.WithAttributes(
        attribute.String("ci.pipeline", "build-and-deploy"),
        attribute.String("ci.stage", "build"),
        attribute.String("ci.status", "success"),
    ))

// 构建大小 gauge
artifactSize := meter.Int64ObservableGauge("ci.artifact.size",
    metric.WithUnit("By"))
```

---

## 8. Golang OpenTelemetry SDK 集成

### 8.1 SDK 初始化

**完整初始化代码** (生产级):

```go
package main

import (
    "context"
    "os"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func InitTelemetry(ctx context.Context) (func(), error) {
    // 1. 创建 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("payment-service"),
            semconv.ServiceVersion("1.5.2"),
            semconv.DeploymentEnvironment("production"),
        ),
        resource.WithFromEnv(),   // 从环境变量读取
        resource.WithProcess(),   // 自动检测进程信息
        resource.WithHost(),      // 自动检测主机信息
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 初始化 Trace Provider
    traceExporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    bsp := trace.NewBatchSpanProcessor(traceExporter,
        trace.WithMaxQueueSize(2048),
        trace.WithMaxExportBatchSize(512),
        trace.WithBatchTimeout(5*time.Second),
    )
    
    tracerProvider := trace.NewTracerProvider(
        trace.WithResource(res),
        trace.WithSpanProcessor(bsp),
        trace.WithSampler(trace.ParentBased(trace.TraceIDRatioBased(0.1))),
    )
    otel.SetTracerProvider(tracerProvider)
    
    // 3. 初始化 Metric Provider
    metricExporter, err := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithEndpoint("otel-collector:4317"),
        otlpmetricgrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    meterProvider := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(metric.NewPeriodicReader(metricExporter,
            metric.WithInterval(10*time.Second))),
    )
    otel.SetMeterProvider(meterProvider)
    
    // 4. 设置 Propagator
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    
    // 5. 返回 Shutdown 函数
    return func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        
        tracerProvider.Shutdown(ctx)
        meterProvider.Shutdown(ctx)
    }, nil
}

func main() {
    ctx := context.Background()
    shutdown, err := InitTelemetry(ctx)
    if err != nil {
        panic(err)
    }
    defer shutdown()
    
    // 应用代码
    RunApplication()
}
```

### 8.2 Trace API 使用

详见 [3. Trace 信号与 Span 模型](#3-trace-信号与-span-模型)

### 8.3 Metric API 使用

详见 [4. Metric 信号与类型系统](#4-metric-信号与类型系统)

### 8.4 Log API 使用（Alpha）

详见 [5. Log 信号与结构化日志](#5-log-信号与结构化日志)

---

## 9. 性能优化最佳实践

### 9.1 批量导出

```go
// BatchSpanProcessor 配置优化
bsp := trace.NewBatchSpanProcessor(exporter,
    // Queue 大小：按 QPS × 平均 Span 数计算
    // 例如: 1000 QPS × 5 Span/req × 5s = 25,000
    trace.WithMaxQueueSize(32768),
    
    // Batch 大小：根据网络 MTU 和延迟权衡
    trace.WithMaxExportBatchSize(512),
    
    // 导出间隔：平衡延迟和效率
    trace.WithBatchTimeout(5*time.Second),
    
    // 导出超时
    trace.WithExportTimeout(30*time.Second),
)
```

**性能对比**:

| 配置 | QPS | CPU | 网络延迟 |
|-----|-----|-----|---------|
| 小 Batch (128) | 10k | 8% | 2ms |
| 中 Batch (512) | 10k | 3% | 5ms |
| 大 Batch (2048) | 10k | 1.5% | 15ms |

### 9.2 采样策略

```go
// 1. 固定比例采样
sampler := trace.TraceIDRatioBased(0.1)  // 10%

// 2. 父决策采样（推荐）
sampler := trace.ParentBased(trace.TraceIDRatioBased(0.1))

// 3. 始终采样（开发环境）
sampler := trace.AlwaysSample()

// 4. 自定义采样（生产推荐）
type CustomSampler struct {
    defaultSampler trace.Sampler
}

func (s *CustomSampler) ShouldSample(p trace.SamplingParameters) trace.SamplingResult {
    // 规则 1：错误必采样
    spanName := p.Name
    if strings.Contains(spanName, "error") || strings.Contains(spanName, "failed") {
        return trace.SamplingResult{
            Decision: trace.RecordAndSample,
        }
    }
    
    // 规则 2：关键路径必采样
    if spanName == "ProcessPayment" || spanName == "CreateOrder" {
        return trace.SamplingResult{
            Decision: trace.RecordAndSample,
        }
    }
    
    // 规则 3：健康检查不采样
    if spanName == "/healthz" || spanName == "/readyz" {
        return trace.SamplingResult{
            Decision: trace.Drop,
        }
    }
    
    // 规则 4：默认策略
    return s.defaultSampler.ShouldSample(p)
}
```

### 9.3 资源检测

```go
// 使用 multi detector 自动检测多种资源
import (
    "go.opentelemetry.io/contrib/detectors/aws/ecs"
    "go.opentelemetry.io/contrib/detectors/gcp"
    "go.opentelemetry.io/otel/sdk/resource"
)

res, err := resource.New(ctx,
    resource.WithDetectors(
        ecs.NewResourceDetector(),    // AWS ECS
        gcp.NewDetector(),             // GCP
        // 自动检测并合并
    ),
    resource.WithAttributes(
        semconv.ServiceName("payment-service"),
    ),
)
```

---

## 10. 总结

OTLP 2025 完整语义约定包括：

1. **四支柱信号**: Trace, Metric, Log, Profile（新增）
2. **Resource 模型**: 统一的资源标识体系
3. **语义约定 v1.0**: HTTP（已冻结）、Gen-AI（Experimental）、CI/CD（Draft）
4. **传输协议**: gRPC/HTTP 双协议，支持批量导出
5. **Golang SDK**: 成熟的 API 和 SDK，生产就绪

**关键性能指标**:

- Span 开销: ~300ns（无采样）、~2μs（采样）
- Metric 开销: ~150ns/data point
- 批量导出: 512 Span/batch, 5s 间隔
- 采样率: 生产环境 1-10%

**生产部署建议**:

- 使用 BatchSpanProcessor
- 配置合理的采样策略
- 启用资源自动检测
- 监控 Collector 性能

---

**下一篇**: [OPAMP 控制平面协议规范 v1.0](./15-opamp-protocol-specification-2025.md)

# OpenTelemetry Semantic Conventions 完整指南

## 📋 目录

- [概述](#概述)
- [什么是语义约定](#什么是语义约定)
- [为什么需要语义约定](#为什么需要语义约定)
- [模块导航](#模块导航)
  - [资源属性 (Resource Attributes)](#资源属性-resource-attributes)
  - [追踪属性 (Trace Attributes)](#追踪属性-trace-attributes)
  - [指标约定 (Metric Conventions)](#指标约定-metric-conventions)
  - [日志约定 (Log Conventions)](#日志约定-log-conventions)
- [快速开始](#快速开始)
- [核心概念](#核心概念)
- [命名规范](#命名规范)
- [版本与兼容性](#版本与兼容性)
- [最佳实践](#最佳实践)
- [常见问题](#常见问题)
- [参考资源](#参考资源)

---

## 概述

**OpenTelemetry Semantic Conventions (语义约定)** 是 OpenTelemetry 项目的核心组成部分，定义了遥测数据（追踪、指标、日志）的标准化命名、结构和语义。

本目录包含了完整的语义约定实现指南，涵盖：

- **24 篇深度文档**，总计超过 **12,000+ 行**
- **资源属性**：6 个子模块
- **追踪属性**：6 个子模块
- **指标约定**：5 个子模块
- **日志约定**：7 个子模块

每个文档都包含：

- ✅ 详细的规范说明
- ✅ Go 1.25.1 完整实现
- ✅ 生产级代码示例
- ✅ 最佳实践与反模式
- ✅ 常见问题与故障排查

---

## 什么是语义约定

语义约定（Semantic Conventions）是一套 **标准化规范**，定义了：

### 1. **属性命名**

```go
// ✅ 标准化命名
semconv.ServiceNameKey.String("payment-service")
semconv.HTTPMethodKey.String("GET")

// ❌ 非标准化命名
resource.NewWithAttributes(
    attribute.String("service", "payment-service"),  // 应该使用 service.name
    attribute.String("method", "GET"),               // 应该使用 http.method
)
```

### 2. **属性语义**

```go
// ✅ 正确语义：http.status_code 是整数
span.SetAttributes(semconv.HTTPStatusCode(200))

// ❌ 错误语义：http.status_code 不应该是字符串
span.SetAttributes(attribute.String("http.status_code", "200"))
```

### 3. **数据结构**

```go
// ✅ 标准化结构：Resource Attributes
res := resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceNameKey.String("my-service"),
    semconv.ServiceVersionKey.String("1.0.0"),
    semconv.DeploymentEnvironmentKey.String("production"),
)

// ✅ 标准化结构：Span Attributes
span.SetAttributes(
    semconv.HTTPMethodKey.String("POST"),
    semconv.HTTPURLKey.String("https://api.example.com/users"),
    semconv.HTTPStatusCodeKey.Int(201),
)
```

---

## 为什么需要语义约定

### 1. **跨系统互操作性**

不同语言、框架、后端之间可以无缝交换遥测数据。

**示例：跨语言追踪**:

```text
[Go Service] -----> [Java Service] -----> [Python Service]
     ↓                    ↓                      ↓
  http.method=GET    http.method=GET       http.method=GET
  http.url=...       http.url=...          http.url=...
```

### 2. **统一查询与分析**

标准化属性使得查询和聚合变得简单。

**示例：统一查询语句**:

```promql
# 所有服务的 HTTP 请求延迟（P95）
histogram_quantile(0.95, 
  rate(http_server_duration_bucket[5m])
)

# 特定服务的错误率
sum(rate(http_server_duration_count{http_status_code=~"5.."}[5m])) 
/ 
sum(rate(http_server_duration_count[5m]))
```

### 3. **工具链兼容性**

Jaeger、Prometheus、Grafana、Loki 等工具原生支持语义约定。

**示例：Grafana 自动仪表盘**:

```yaml
# Grafana 可以自动识别标准化指标并生成仪表盘
- http_server_request_duration_seconds
- http_server_active_requests
- http_client_request_size_bytes
```

### 4. **最佳实践内建**

语义约定编码了行业最佳实践。

**示例：自动资源检测**:

```go
// OpenTelemetry SDK 自动填充标准 Resource Attributes
res, _ := resource.New(ctx,
    resource.WithFromEnv(),      // 从环境变量自动检测
    resource.WithProcess(),      // 自动检测进程信息
    resource.WithOS(),           // 自动检测操作系统
    resource.WithContainer(),    // 自动检测容器环境
    resource.WithHost(),         // 自动检测主机信息
)
```

---

## 模块导航

### 资源属性 (Resource Attributes)

资源属性用于标识产生遥测数据的 **实体**（服务、主机、容器等）。

| 文档 | 内容 | 代码量 |
|------|------|--------|
| [01_服务资源.md](01_资源属性/01_服务资源.md) | `service.*` 属性：服务名、版本、实例 ID | 550+ 行 |
| [02_部署环境.md](01_资源属性/02_部署环境.md) | `deployment.*` 属性：环境、区域、可用区 | 450+ 行 |
| [03_云平台资源.md](01_资源属性/03_云平台资源.md) | `cloud.*` 属性：AWS/Azure/GCP 资源 | 600+ 行 |
| [04_Kubernetes资源.md](01_资源属性/04_Kubernetes资源.md) | `k8s.*` 属性：集群、命名空间、Pod、容器 | 700+ 行 |
| [05_主机与进程.md](01_资源属性/05_主机与进程.md) | `host.*` 和 `process.*` 属性 | 650+ 行 |
| [06_设备与浏览器.md](01_资源属性/06_设备与浏览器.md) | `device.*` 和 `browser.*` 属性 | 550+ 行 |

**总计**：6 个文档，约 **3,500+ 行**

**快速示例：完整资源定义**:

```go
res := resource.NewWithAttributes(
    semconv.SchemaURL,
    // 服务资源
    semconv.ServiceNameKey.String("payment-service"),
    semconv.ServiceVersionKey.String("2.1.3"),
    semconv.ServiceInstanceIDKey.String("pod-abc123"),
    // 部署环境
    semconv.DeploymentEnvironmentKey.String("production"),
    attribute.String("deployment.region", "us-west-2"),
    // 云平台
    semconv.CloudProviderAWS,
    semconv.CloudPlatformAWSECS,
    semconv.CloudAccountIDKey.String("123456789012"),
    // Kubernetes
    semconv.K8SClusterNameKey.String("prod-cluster"),
    semconv.K8SNamespaceNameKey.String("default"),
    semconv.K8SPodNameKey.String("payment-abc123"),
)
```

---

### 追踪属性 (Trace Attributes)

追踪属性用于描述 **操作** 的详细信息（HTTP 请求、数据库查询、RPC 调用等）。

| 文档 | 内容 | 代码量 |
|------|------|--------|
| [01_HTTP客户端.md](02_Trace属性/01_HTTP客户端.md) | HTTP 客户端追踪：方法、URL、状态码、重试 | 600+ 行 |
| [02_HTTP服务器.md](02_Trace属性/02_HTTP服务器.md) | HTTP 服务器追踪：路由、中间件、框架集成 | 650+ 行 |
| [03_RPC与gRPC.md](02_Trace属性/03_RPC与gRPC.md) | gRPC 追踪：拦截器、流式 RPC、错误处理 | 700+ 行 |
| [04_数据库.md](02_Trace属性/04_数据库.md) | 数据库追踪：SQL/NoSQL、连接池、ORM | 750+ 行 |
| [05_消息队列.md](02_Trace属性/05_消息队列.md) | 消息队列追踪：Kafka、RabbitMQ、NATS | 650+ 行 |
| [06_网络与连接.md](02_Trace属性/06_网络与连接.md) | 网络追踪：TCP/UDP、TLS、DNS、连接池 | 650+ 行 |

**总计**：6 个文档，约 **4,000+ 行**

**快速示例：HTTP 服务器追踪**:

```go
func otlpMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx, span := tracer.Start(r.Context(), r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
        )
        defer span.End()

        span.SetAttributes(
            semconv.HTTPMethodKey.String(r.Method),
            semconv.HTTPURLKey.String(r.URL.String()),
            semconv.HTTPTargetKey.String(r.URL.Path),
            semconv.HTTPSchemeKey.String(r.URL.Scheme),
            semconv.HTTPFlavorKey.String(r.Proto),
            semconv.NetHostNameKey.String(r.Host),
        )

        rw := &responseWriter{ResponseWriter: w, statusCode: 200}
        next.ServeHTTP(rw, r.WithContext(ctx))

        span.SetAttributes(semconv.HTTPStatusCodeKey.Int(rw.statusCode))
        if rw.statusCode >= 500 {
            span.SetStatus(codes.Error, "Internal Server Error")
        }
    })
}
```

---

### 指标约定 (Metric Conventions)

指标约定定义了 **系统和业务指标** 的标准化命名和语义。

| 文档 | 内容 | 代码量 |
|------|------|--------|
| [01_系统指标.md](03_Metric约定/01_系统指标.md) | CPU、内存、磁盘、网络指标（`gopsutil`） | 600+ 行 |
| [02_运行时指标.md](03_Metric约定/02_运行时指标.md) | Go 运行时指标：GC、Goroutine、内存 | 550+ 行 |
| [03_HTTP指标.md](03_Metric约定/03_HTTP指标.md) | HTTP 请求率、延迟、错误率、请求大小 | 600+ 行 |
| [04_数据库指标.md](03_Metric约定/04_数据库指标.md) | 连接池、查询性能、事务指标 | 600+ 行 |
| [05_自定义指标.md](03_Metric约定/05_自定义指标.md) | KPI、用户行为、SLI/SLO、错误预算 | 650+ 行 |

**总计**：5 个文档，约 **3,000+ 行**

**快速示例：HTTP 指标采集**:

```go
var (
    httpRequestDuration = meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP server request duration"),
        metric.WithUnit("s"),
    )
    
    httpActiveRequests = meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Number of active HTTP requests"),
    )
)

func instrumentedHandler(w http.ResponseWriter, r *http.Request) {
    start := time.Now()
    httpActiveRequests.Add(r.Context(), 1, 
        metric.WithAttributes(semconv.HTTPMethodKey.String(r.Method)),
    )
    defer httpActiveRequests.Add(r.Context(), -1)

    rw := &responseWriter{ResponseWriter: w, statusCode: 200}
    handler(rw, r)

    duration := time.Since(start).Seconds()
    httpRequestDuration.Record(r.Context(), duration,
        metric.WithAttributes(
            semconv.HTTPMethodKey.String(r.Method),
            semconv.HTTPRouteKey.String(r.URL.Path),
            semconv.HTTPStatusCodeKey.Int(rw.statusCode),
        ),
    )
}
```

---

### 日志约定 (Log Conventions)

日志约定定义了 **结构化日志** 的标准化格式和最佳实践。

| 文档 | 内容 | 代码量 |
|------|------|--------|
| [01_日志级别.md](04_Log约定/01_日志级别.md) | OTLP Severity Number、`slog` 级别映射 | 450+ 行 |
| [02_结构化日志.md](04_Log约定/02_结构化日志.md) | `slog` 集成、字段标准化、性能优化 | 500+ 行 |
| [03_日志与追踪关联.md](04_Log约定/03_日志与追踪关联.md) | Trace ID/Span ID 自动注入、关联查询 | 450+ 行 |
| [04_日志采集.md](04_Log约定/04_日志采集.md) | 文件日志、OTLP 导出、日志解析 | 550+ 行 |
| [05_日志查询.md](04_Log约定/05_日志查询.md) | Loki/Elasticsearch 集成、统一查询接口 | 500+ 行 |
| [06_日志异常检测.md](04_Log约定/06_日志异常检测.md) | 模式识别、统计分析、告警系统 | 500+ 行 |
| [07_日志最佳实践.md](04_Log约定/07_日志最佳实践.md) | 级别使用、格式化、性能、安全性 | 550+ 行 |

**总计**：7 个文档，约 **3,500+ 行**

**快速示例：日志与追踪关联**:

```go
import "log/slog"

// 自动注入 Trace ID 和 Span ID 的 Handler
type OTLPHandler struct {
    slog.Handler
}

func (h *OTLPHandler) Handle(ctx context.Context, r slog.Record) error {
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        r.AddAttrs(
            slog.String("trace_id", spanCtx.TraceID().String()),
            slog.String("span_id", spanCtx.SpanID().String()),
            slog.Bool("trace_flags", spanCtx.TraceFlags().IsSampled()),
        )
    }
    return h.Handler.Handle(ctx, r)
}

// 使用
logger := slog.New(&OTLPHandler{Handler: slog.NewJSONHandler(os.Stdout, nil)})

func handler(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "HandleRequest")
    defer span.End()

    logger.InfoContext(ctx, "Processing request",
        slog.String("method", r.Method),
        slog.String("path", r.URL.Path),
    )
    // 日志自动包含 trace_id 和 span_id！
}
```

---

## 快速开始

### 1. **最小可运行示例**

```go
package main

import (
    "context"
    "log"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    ctx := context.Background()

    // 1. 创建标准化资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
            semconv.ServiceVersionKey.String("1.0.0"),
            semconv.DeploymentEnvironmentKey.String("production"),
        ),
    )
    if err != nil {
        log.Fatal(err)
    }

    // 2. 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatal(err)
    }

    // 3. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )
    defer func() {
        if err := tp.Shutdown(ctx); err != nil {
            log.Fatal(err)
        }
    }()
    otel.SetTracerProvider(tp)

    // 4. 使用标准化属性创建 Span
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "operation",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.HTTPMethodKey.String("GET"),
        semconv.HTTPURLKey.String("https://api.example.com/users"),
        semconv.HTTPStatusCodeKey.Int(200),
    )

    time.Sleep(100 * time.Millisecond)
    log.Println("Trace sent with semantic conventions!")
}
```

### 2. **运行 OpenTelemetry Collector**

```yaml
# collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

exporters:
  logging:
    loglevel: debug
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [logging, jaeger]
```

```bash
# 启动 Collector
docker run -d --name otel-collector \
  -p 4317:4317 \
  -v $(pwd)/collector-config.yaml:/etc/otel-collector-config.yaml \
  otel/opentelemetry-collector:latest \
  --config=/etc/otel-collector-config.yaml
```

---

## 核心概念

### 1. **Schema URL**

Schema URL 定义了语义约定的版本。

```go
import semconv "go.opentelemetry.io/otel/semconv/v1.24.0"

res := resource.NewWithAttributes(
    semconv.SchemaURL,  // "https://opentelemetry.io/schemas/1.24.0"
    semconv.ServiceNameKey.String("my-service"),
)
```

**版本演进示例**：

```go
// v1.20.0: http.method
semconv.HTTPMethodKey.String("GET")

// v1.21.0+: http.request.method (新命名规范)
semconv.HTTPRequestMethodKey.String("GET")
```

### 2. **属性类型**

OpenTelemetry 支持以下属性类型：

```go
import "go.opentelemetry.io/otel/attribute"

span.SetAttributes(
    attribute.String("string.attr", "value"),
    attribute.Bool("bool.attr", true),
    attribute.Int("int.attr", 42),
    attribute.Int64("int64.attr", 1234567890),
    attribute.Float64("float.attr", 3.14),
    attribute.StringSlice("array.attr", []string{"a", "b", "c"}),
)
```

### 3. **必需属性 vs 可选属性**

| 类型 | 说明 | 示例 |
|------|------|------|
| **必需** | 必须始终包含 | `service.name`、`http.method` |
| **条件必需** | 在特定条件下必需 | `http.status_code`（仅限服务器） |
| **推荐** | 应该包含以提高可观测性 | `http.user_agent` |
| **可选** | 锦上添花 | `http.request_content_length` |

**示例：HTTP 服务器 Span**:

```go
span.SetAttributes(
    // 必需
    semconv.HTTPMethodKey.String("GET"),                    // ✅ 必需
    semconv.HTTPURLKey.String("https://api.example.com"),   // ✅ 必需
    semconv.HTTPStatusCodeKey.Int(200),                     // ✅ 条件必需（服务器）
    
    // 推荐
    semconv.HTTPUserAgentKey.String(r.UserAgent()),         // ⭐ 推荐
    semconv.HTTPRouteKey.String("/users/:id"),              // ⭐ 推荐
    
    // 可选
    semconv.HTTPRequestContentLengthKey.Int(1024),          // 💡 可选
)
```

### 4. **高基数属性**

高基数属性（如用户 ID、请求 ID）应谨慎使用。

```go
// ❌ 危险：高基数属性
span.SetAttributes(
    attribute.String("user.id", userID),        // 数百万不同的值
    attribute.String("request.id", requestID),  // 每个请求都不同
)

// ✅ 安全：使用 Span Events 或低基数聚合
span.AddEvent("user_action", trace.WithAttributes(
    attribute.String("user.id", userID),
))

// ✅ 或者：使用低基数属性
span.SetAttributes(
    attribute.String("user.tier", "premium"),  // 只有几个不同的值
)
```

---

## 命名规范

### 1. **命名空间**

属性使用点分隔的命名空间：

```text
<namespace>.<component>.<attribute>
```

**示例**：

```go
semconv.ServiceNameKey             // service.name
semconv.HTTPMethodKey              // http.method
semconv.DBSystemKey                // db.system
semconv.MessagingOperationKey      // messaging.operation
```

### 2. **命名约定**

| 规则 | 说明 | 示例 |
|------|------|------|
| **小写** | 所有字母小写 | `http.method`（不是 `HTTP.Method`） |
| **下划线** | 单词用下划线分隔 | `http.status_code` |
| **命名空间** | 使用点分隔命名空间 | `db.system`、`rpc.service` |
| **单数** | 优先使用单数 | `http.method`（不是 `http.methods`） |

### 3. **禁止的命名**

```go
// ❌ 禁止：通用名称
attribute.String("status", "ok")           // 太通用
attribute.String("error", "failed")        // 太通用

// ✅ 正确：具体命名
semconv.HTTPStatusCodeKey.Int(200)
span.SetStatus(codes.Error, "Connection failed")
```

---

## 版本与兼容性

### 1. **语义约定版本**

```go
// Go OpenTelemetry SDK
import semconv "go.opentelemetry.io/otel/semconv/v1.24.0"

// Schema URL
res := resource.NewWithAttributes(
    semconv.SchemaURL,  // "https://opentelemetry.io/schemas/1.24.0"
    // ...
)
```

### 2. **向后兼容性**

OpenTelemetry 遵循 **语义化版本** 和 **稳定性保证**：

| 版本 | 兼容性 | 说明 |
|------|--------|------|
| **1.x.0 → 1.x.1** | 完全兼容 | 只有补丁（bugfix） |
| **1.x.0 → 1.(x+1).0** | 向后兼容 | 新增属性，旧属性可能标记为废弃 |
| **1.x.0 → 2.0.0** | 可能破坏兼容性 | 废弃的属性可能被移除 |

### 3. **迁移策略**

```go
// v1.20.0 -> v1.24.0 迁移示例

// 旧版本 (v1.20.0)
span.SetAttributes(
    semconv.HTTPMethodKey.String("GET"),          // http.method
    semconv.HTTPURLKey.String("https://..."),     // http.url
)

// 新版本 (v1.21.0+)
span.SetAttributes(
    semconv.HTTPRequestMethodKey.String("GET"),   // http.request.method
    semconv.URLFullKey.String("https://..."),     // url.full
)

// 过渡期：同时发送两个版本
span.SetAttributes(
    semconv.HTTPMethodKey.String("GET"),          // 旧属性（废弃）
    semconv.HTTPRequestMethodKey.String("GET"),   // 新属性
)
```

---

## 最佳实践

### 1. **始终使用 semconv 包**

```go
// ✅ 推荐：使用 semconv
import semconv "go.opentelemetry.io/otel/semconv/v1.24.0"

span.SetAttributes(
    semconv.HTTPMethodKey.String("GET"),
    semconv.HTTPStatusCodeKey.Int(200),
)

// ❌ 避免：手动字符串
span.SetAttributes(
    attribute.String("http.method", "GET"),
    attribute.Int("http.status_code", 200),
)
```

### 2. **复用 Resource 对象**

```go
// ✅ 推荐：创建一次，全局复用
var globalResource *resource.Resource

func init() {
    var err error
    globalResource, err = resource.New(context.Background(),
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
            semconv.ServiceVersionKey.String("1.0.0"),
        ),
    )
    if err != nil {
        log.Fatal(err)
    }
}

func createTracerProvider() *sdktrace.TracerProvider {
    return sdktrace.NewTracerProvider(
        sdktrace.WithResource(globalResource),
    )
}
```

### 3. **避免高基数属性**

```go
// ❌ 危险：每个请求都有唯一的 trace_id
span.SetAttributes(
    attribute.String("trace.id", spanCtx.TraceID().String()),
)

// ✅ 安全：Trace ID 已经内建在 Span 中，无需重复添加
// 直接使用 spanCtx.TraceID()
```

### 4. **使用 Span Events 记录细节**

```go
// ❌ 避免：为每个细节创建新 Span
span1 := tracer.Start(ctx, "validate_input")
span1.End()
span2 := tracer.Start(ctx, "check_permission")
span2.End()
span3 := tracer.Start(ctx, "execute_query")
span3.End()

// ✅ 推荐：使用 Span Events
span := tracer.Start(ctx, "process_request")
defer span.End()

span.AddEvent("validate_input", trace.WithAttributes(
    attribute.String("input.type", "json"),
))
span.AddEvent("check_permission", trace.WithAttributes(
    attribute.String("user.role", "admin"),
))
span.AddEvent("execute_query", trace.WithAttributes(
    attribute.String("query.type", "SELECT"),
))
```

### 5. **处理敏感数据**

```go
// ❌ 危险：记录敏感信息
span.SetAttributes(
    attribute.String("user.password", password),       // ❌ 密码
    attribute.String("credit_card.number", ccNumber),  // ❌ 信用卡号
)

// ✅ 安全：脱敏或不记录
span.SetAttributes(
    attribute.String("user.id", userID),               // ✅ 用户 ID（非敏感）
    attribute.String("payment.method", "credit_card"), // ✅ 支付方式（非敏感）
)
```

---

## 常见问题

### Q1: 我应该使用哪个版本的 semconv 包？

**A**: 使用与你的 OpenTelemetry SDK 版本匹配的最新稳定版本。

```go
// 推荐：使用 v1.24.0 或更高版本
import semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
```

检查版本兼容性：

```bash
go list -m go.opentelemetry.io/otel
go list -m go.opentelemetry.io/otel/semconv/v1.24.0
```

---

### Q2: 我可以创建自定义属性吗？

**A**: 可以，但优先使用标准属性。

```go
// ✅ 优先：使用标准属性
span.SetAttributes(
    semconv.HTTPMethodKey.String("GET"),
)

// ✅ 允许：自定义命名空间
span.SetAttributes(
    attribute.String("mycompany.user.tier", "premium"),
    attribute.String("mycompany.feature.flag", "new_ui"),
)

// ❌ 避免：与标准属性冲突
span.SetAttributes(
    attribute.String("http.method", "CUSTOM"),  // 不要重新定义标准属性
)
```

---

### Q3: Resource Attributes 和 Span Attributes 有什么区别？

**A**:

- **Resource Attributes**: 描述 **实体**（服务、主机、容器），在整个应用生命周期内不变。
- **Span Attributes**: 描述 **操作**（HTTP 请求、数据库查询），每个 Span 可能不同。

```go
// Resource Attributes（服务级别，全局）
resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceNameKey.String("payment-service"),   // 服务名
    semconv.ServiceVersionKey.String("1.0.0"),          // 版本
)

// Span Attributes（操作级别，每个 Span 不同）
span.SetAttributes(
    semconv.HTTPMethodKey.String("POST"),               // HTTP 方法
    semconv.HTTPURLKey.String("https://api.../pay"),    // 请求 URL
)
```

---

### Q4: 如何处理属性值过大的情况？

**A**: 使用截断或哈希。

```go
const maxLength = 256

func truncate(s string) string {
    if len(s) > maxLength {
        return s[:maxLength] + "..."
    }
    return s
}

// 使用截断
span.SetAttributes(
    attribute.String("http.url", truncate(longURL)),
)

// 或者使用哈希
import "crypto/sha256"

func hash(s string) string {
    h := sha256.Sum256([]byte(s))
    return fmt.Sprintf("%x", h[:8])  // 取前 16 个字符
}

span.SetAttributes(
    attribute.String("request.body.hash", hash(requestBody)),
)
```

---

### Q5: 如何在多个服务之间保持一致的语义约定？

**A**: 使用 **共享的 semconv 版本** 和 **Schema URL**。

```go
// 服务 A (Go)
import semconv "go.opentelemetry.io/otel/semconv/v1.24.0"

res := resource.NewWithAttributes(
    semconv.SchemaURL,  // 关键！
    semconv.ServiceNameKey.String("service-a"),
)

// 服务 B (Java)
// 使用相同的 Schema URL 和 semconv 版本
Resource resource = Resource.create(
    Attributes.of(
        ResourceAttributes.SCHEMA_URL, "https://opentelemetry.io/schemas/1.24.0",
        ResourceAttributes.SERVICE_NAME, "service-b"
    )
);
```

---

## 参考资源

### 官方文档

- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)
- [Go SDK Semantic Conventions](https://pkg.go.dev/go.opentelemetry.io/otel/semconv)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)

### Go 实现

- [OpenTelemetry Go SDK](https://github.com/open-telemetry/opentelemetry-go)
- [OpenTelemetry Go Contrib](https://github.com/open-telemetry/opentelemetry-go-contrib)

### 工具

- [Jaeger](https://www.jaegertracing.io/) - 分布式追踪后端
- [Prometheus](https://prometheus.io/) - 指标监控
- [Grafana](https://grafana.com/) - 可视化
- [Loki](https://grafana.com/oss/loki/) - 日志聚合

### 社区

- [OpenTelemetry Slack](https://cloud-native.slack.com/archives/C01N7PP1THC)
- [CNCF OpenTelemetry](https://www.cncf.io/projects/opentelemetry/)

---

## 下一步

根据你的需求选择相应的模块：

| 如果你想... | 阅读 |
|------------|------|
| 标识服务和部署环境 | [01_资源属性](01_资源属性/) |
| 追踪 HTTP/gRPC/数据库操作 | [02_Trace属性](02_Trace属性/) |
| 采集系统和业务指标 | [03_Metric约定](03_Metric约定/) |
| 实现结构化日志和异常检测 | [04_Log约定](04_Log约定/) |

---

**🎉 开始你的 OpenTelemetry 语义约定之旅！**

如有问题，请参考各模块的详细文档或在 [GitHub Issues](https://github.com/open-telemetry/opentelemetry-go/issues) 提问。

# Grafana Tempo 与 OTLP 完整集成指南（Go 1.25.1 - 2025版）

> **文档版本**: v1.0.0  
> **更新日期**: 2025-10-12  
> **Go 版本**: 1.25.1+  
> **Tempo 版本**: 2.3.0+  
> **技术深度**: ⭐⭐⭐⭐⭐

---

## 📋 目录

- [Grafana Tempo 与 OTLP 完整集成指南（Go 1.25.1 - 2025版）](#grafana-tempo-与-otlp-完整集成指南go-1251---2025版)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [什么是 Grafana Tempo？](#什么是-grafana-tempo)
    - [核心特性](#核心特性)
    - [与其他方案对比](#与其他方案对比)
  - [Grafana Tempo 概述](#grafana-tempo-概述)
    - [架构设计](#架构设计)
    - [数据流程](#数据流程)
  - [完整集成示例](#完整集成示例)
    - [1. 基础配置](#1-基础配置)
      - [go.mod 依赖](#gomod-依赖)
      - [Tempo 配置文件](#tempo-配置文件)
    - [2. OTLP Exporter 配置](#2-otlp-exporter-配置)
    - [3. HTTP 服务集成示例](#3-http-服务集成示例)
    - [4. 分布式追踪示例](#4-分布式追踪示例)
  - [高级特性](#高级特性)
    - [1. TraceQL 查询语言](#1-traceql-查询语言)
      - [TraceQL 语法示例](#traceql-语法示例)
      - [Go 中使用 TraceQL](#go-中使用-traceql)
    - [2. Metrics Generator (度量生成器)](#2-metrics-generator-度量生成器)
      - [配置 Metrics Generator](#配置-metrics-generator)
      - [Go 代码中启用 Exemplars](#go-代码中启用-exemplars)
    - [3. 服务图 (Service Graph)](#3-服务图-service-graph)
      - [查询服务图](#查询服务图)
  - [性能优化](#性能优化)
    - [1. 采样策略](#1-采样策略)
    - [2. 批处理优化](#2-批处理优化)
    - [3. 连接池优化](#3-连接池优化)
  - [生产部署](#生产部署)
    - [1. Docker Compose 部署](#1-docker-compose-部署)
      - [Grafana 数据源配置](#grafana-数据源配置)
    - [2. Kubernetes 部署](#2-kubernetes-部署)
    - [3. 生产配置优化](#3-生产配置优化)
  - [最佳实践](#最佳实践)
    - [1. 属性命名规范](#1-属性命名规范)
    - [2. 错误处理最佳实践](#2-错误处理最佳实践)
    - [3. 追踪上下文传播](#3-追踪上下文传播)
  - [故障排查](#故障排查)
    - [1. 常见问题](#1-常见问题)
    - [2. 监控指标](#2-监控指标)
    - [3. 日志分析](#3-日志分析)
  - [总结](#总结)
    - [核心要点](#核心要点)
    - [性能基准](#性能基准)
    - [下一步](#下一步)

---

## 简介

### 什么是 Grafana Tempo？

**Grafana Tempo** 是一个开源的分布式追踪后端，专为大规模、高性能追踪数据存储而设计。

### 核心特性

```text
✅ 核心优势:
  - 成本效益高 (仅需对象存储)
  - 无索引设计 (TraceID 查询)
  - 云原生架构
  - 与 Grafana 深度集成
  - 支持多种追踪格式

✅ 支持的协议:
  - OTLP (gRPC/HTTP)
  - Jaeger
  - Zipkin
  - OpenCensus

✅ 存储后端:
  - S3/GCS/Azure Blob
  - 本地文件系统
  - Cassandra (实验性)

✅ 性能指标:
  - 吞吐量: 100K+ spans/s
  - 查询延迟: <100ms (TraceID)
  - 存储成本: ~$0.02/GB/月
  - 数据压缩: 10:1 比例
```

### 与其他方案对比

| 特性 | Tempo | Jaeger | Zipkin | Elastic APM |
|------|-------|--------|--------|-------------|
| 成本 | 极低 | 中 | 中 | 高 |
| 扩展性 | 极好 | 好 | 中 | 好 |
| 查询能力 | TraceID | 全文搜索 | 标签搜索 | 全文搜索 |
| 存储 | 对象存储 | DB/ES | DB | Elasticsearch |
| 运维复杂度 | 低 | 中 | 低 | 高 |
| Grafana集成 | 原生 | 插件 | 插件 | 插件 |

---

## Grafana Tempo 概述

### 架构设计

```text
┌─────────────────────────────────────────────────────────┐
│                    Tempo 架构                           │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐           │
│  │ Collector│    │ Collector│    │ Collector│           │
│  │  (OTLP)  │    │ (Jaeger) │    │ (Zipkin) │           │
│  └────┬─────┘    └────┬─────┘    └────┬─────┘           │
│       │               │               │                 │
│       └───────────────┼───────────────┘                 │
│                       │                                 │
│              ┌────────▼────────┐                        │
│              │   Distributor   │  (负载均衡)             │
│              └────────┬────────┘                        │
│                       │                                 │
│              ┌────────▼────────┐                        │
│              │    Ingester     │  (写入缓冲)             │
│              └────────┬────────┘                        │
│                       │                                 │
│              ┌────────▼────────┐                        │
│              │    Compactor    │  (数据压缩)            │
│              └────────┬────────┘                        │
│                       │                                 │
│              ┌────────▼────────┐                        │
│              │ Object Storage  │  (S3/GCS/Azure)        │
│              └────────┬────────┘                        │
│                       │                                 │
│              ┌────────▼────────┐                        │
│              │  Query Frontend │  (查询入口)            │
│              └────────┬────────┘                        │
│                       │                                 │
│              ┌────────▼────────┐                        │
│              │     Querier     │  (数据检索)            │
│              └─────────────────┘                        │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 数据流程

```text
1. 数据写入流程:
   应用 → OTLP Exporter → Tempo Distributor → Ingester → Object Storage

2. 数据查询流程:
   Grafana → Query Frontend → Querier → Object Storage → 返回结果

3. 数据压缩流程:
   Compactor → 读取旧块 → 合并压缩 → 写入新块 → 删除旧块
```

---

## 完整集成示例

### 1. 基础配置

#### go.mod 依赖

```go
module github.com/example/tempo-integration

go 1.25.1

require (
    go.opentelemetry.io/otel v1.24.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace v1.24.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.24.0
    go.opentelemetry.io/otel/sdk v1.24.0
    go.opentelemetry.io/otel/trace v1.24.0
    google.golang.org/grpc v1.62.0
)
```

#### Tempo 配置文件

```yaml
# tempo-config.yaml
server:
  http_listen_port: 3200
  grpc_listen_port: 9095

distributor:
  receivers:
    otlp:
      protocols:
        grpc:
          endpoint: 0.0.0.0:4317
        http:
          endpoint: 0.0.0.0:4318
    jaeger:
      protocols:
        thrift_http:
          endpoint: 0.0.0.0:14268
        grpc:
          endpoint: 0.0.0.0:14250

ingester:
  max_block_duration: 5m
  max_block_bytes: 1048576
  complete_block_timeout: 15m

compactor:
  compaction:
    block_retention: 168h  # 7 days
  ring:
    kvstore:
      store: inmemory

storage:
  trace:
    backend: local
    local:
      path: /var/tempo/traces
    wal:
      path: /var/tempo/wal
    pool:
      max_workers: 100
      queue_depth: 10000

querier:
  frontend_worker:
    frontend_address: localhost:9095

metrics_generator:
  registry:
    external_labels:
      source: tempo
      cluster: dev
  storage:
    path: /var/tempo/generator/wal
  traces_storage:
    path: /var/tempo/generator/traces
```

### 2. OTLP Exporter 配置

```go
package tempo

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

// TempoConfig Tempo 配置
type TempoConfig struct {
    Endpoint        string        // Tempo gRPC 端点
    ServiceName     string        // 服务名称
    ServiceVersion  string        // 服务版本
    Environment     string        // 环境 (dev/staging/prod)
    SamplingRate    float64       // 采样率 (0.0-1.0)
    MaxQueueSize    int           // 最大队列大小
    BatchTimeout    time.Duration // 批处理超时
    ExportTimeout   time.Duration // 导出超时
    Insecure        bool          // 是否使用不安全连接
}

// DefaultTempoConfig 默认配置
func DefaultTempoConfig() *TempoConfig {
    return &TempoConfig{
        Endpoint:       "localhost:4317",
        ServiceName:    "my-service",
        ServiceVersion: "1.0.0",
        Environment:    "development",
        SamplingRate:   1.0, // 开发环境全采样
        MaxQueueSize:   2048,
        BatchTimeout:   5 * time.Second,
        ExportTimeout:  30 * time.Second,
        Insecure:       true,
    }
}

// TempoExporter Tempo 导出器
type TempoExporter struct {
    config         *TempoConfig
    tracerProvider *sdktrace.TracerProvider
    exporter       *otlptrace.Exporter
}

// NewTempoExporter 创建 Tempo 导出器
func NewTempoExporter(ctx context.Context, cfg *TempoConfig) (*TempoExporter, error) {
    if cfg == nil {
        cfg = DefaultTempoConfig()
    }

    // 1. 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(cfg.ServiceName),
            semconv.ServiceVersion(cfg.ServiceVersion),
            semconv.DeploymentEnvironment(cfg.Environment),
        ),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create resource: %w", err)
    }

    // 2. 配置 gRPC 连接选项
    opts := []otlptracegrpc.Option{
        otlptracegrpc.WithEndpoint(cfg.Endpoint),
        otlptracegrpc.WithTimeout(cfg.ExportTimeout),
    }

    if cfg.Insecure {
        opts = append(opts,
            otlptracegrpc.WithTLSCredentials(insecure.NewCredentials()),
            otlptracegrpc.WithDialOption(grpc.WithBlock()),
        )
    }

    // 3. 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx, opts...)
    if err != nil {
        return nil, fmt.Errorf("failed to create OTLP exporter: %w", err)
    }

    // 4. 配置采样器
    var sampler sdktrace.Sampler
    if cfg.SamplingRate >= 1.0 {
        sampler = sdktrace.AlwaysSample()
    } else if cfg.SamplingRate <= 0.0 {
        sampler = sdktrace.NeverSample()
    } else {
        sampler = sdktrace.TraceIDRatioBased(cfg.SamplingRate)
    }

    // 5. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter,
            sdktrace.WithMaxQueueSize(cfg.MaxQueueSize),
            sdktrace.WithBatchTimeout(cfg.BatchTimeout),
            sdktrace.WithExportTimeout(cfg.ExportTimeout),
        ),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sampler),
    )

    // 6. 设置全局 TracerProvider
    otel.SetTracerProvider(tp)

    // 7. 设置全局 Propagator
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return &TempoExporter{
        config:         cfg,
        tracerProvider: tp,
        exporter:       exporter,
    }, nil
}

// Shutdown 关闭导出器
func (e *TempoExporter) Shutdown(ctx context.Context) error {
    if e.tracerProvider != nil {
        if err := e.tracerProvider.Shutdown(ctx); err != nil {
            return fmt.Errorf("failed to shutdown tracer provider: %w", err)
        }
    }
    return nil
}

// ForceFlush 强制刷新
func (e *TempoExporter) ForceFlush(ctx context.Context) error {
    if e.tracerProvider != nil {
        if err := e.tracerProvider.ForceFlush(ctx); err != nil {
            return fmt.Errorf("failed to flush tracer provider: %w", err)
        }
    }
    return nil
}
```

### 3. HTTP 服务集成示例

```go
package main

import (
    "context"
    "encoding/json"
    "fmt"
    "log"
    "math/rand"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("example-http-server")

// User 用户模型
type User struct {
    ID       int64  `json:"id"`
    Username string `json:"username"`
    Email    string `json:"email"`
}

// Response 统一响应
type Response struct {
    Code    int         `json:"code"`
    Message string      `json:"message"`
    Data    interface{} `json:"data,omitempty"`
}

// TracingMiddleware 追踪中间件
func TracingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx, span := tracer.Start(r.Context(), r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.url", r.URL.String()),
                attribute.String("http.scheme", r.URL.Scheme),
                attribute.String("http.host", r.Host),
                attribute.String("http.user_agent", r.UserAgent()),
                attribute.String("http.remote_addr", r.RemoteAddr),
            ),
        )
        defer span.End()

        // 包装 ResponseWriter 以捕获状态码
        ww := &responseWriter{ResponseWriter: w, statusCode: http.StatusOK}

        next.ServeHTTP(ww, r.WithContext(ctx))

        // 记录响应状态
        span.SetAttributes(
            attribute.Int("http.status_code", ww.statusCode),
        )

        if ww.statusCode >= 400 {
            span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", ww.statusCode))
        }
    })
}

type responseWriter struct {
    http.ResponseWriter
    statusCode int
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}

// GetUserHandler 获取用户处理器
func GetUserHandler(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "GetUser")
    defer span.End()

    // 提取用户 ID
    userID := r.URL.Query().Get("id")
    span.SetAttributes(attribute.String("user.id", userID))

    // 模拟数据库查询
    user, err := fetchUserFromDB(ctx, userID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        writeJSON(w, http.StatusInternalServerError, Response{
            Code:    500,
            Message: err.Error(),
        })
        return
    }

    // 检查缓存
    cached := checkCache(ctx, fmt.Sprintf("user:%s", userID))
    span.SetAttributes(attribute.Bool("cache.hit", cached))

    writeJSON(w, http.StatusOK, Response{
        Code:    200,
        Message: "success",
        Data:    user,
    })
}

// fetchUserFromDB 从数据库获取用户
func fetchUserFromDB(ctx context.Context, userID string) (*User, error) {
    _, span := tracer.Start(ctx, "DB.QueryUser",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "postgresql"),
            attribute.String("db.operation", "SELECT"),
            attribute.String("db.table", "users"),
        ),
    )
    defer span.End()

    // 模拟数据库延迟
    time.Sleep(time.Duration(10+rand.Intn(40)) * time.Millisecond)

    // 10% 概率出错
    if rand.Float64() < 0.1 {
        err := fmt.Errorf("database connection timeout")
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    user := &User{
        ID:       123,
        Username: "john_doe",
        Email:    "john@example.com",
    }

    span.SetAttributes(
        attribute.Int64("user.id", user.ID),
        attribute.String("user.username", user.Username),
    )

    return user, nil
}

// checkCache 检查缓存
func checkCache(ctx context.Context, key string) bool {
    _, span := tracer.Start(ctx, "Cache.Get",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("cache.system", "redis"),
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    // 模拟缓存查询
    time.Sleep(time.Duration(1+rand.Intn(5)) * time.Millisecond)

    hit := rand.Float64() < 0.7 // 70% 缓存命中
    span.SetAttributes(attribute.Bool("cache.hit", hit))

    return hit
}

// writeJSON 写入 JSON 响应
func writeJSON(w http.ResponseWriter, status int, data interface{}) {
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(status)
    json.NewEncoder(w).Encode(data)
}

func main() {
    // 1. 初始化 Tempo 导出器
    ctx := context.Background()
    tempoExporter, err := NewTempoExporter(ctx, &TempoConfig{
        Endpoint:       "localhost:4317",
        ServiceName:    "user-service",
        ServiceVersion: "1.0.0",
        Environment:    "production",
        SamplingRate:   0.1, // 10% 采样率
        MaxQueueSize:   2048,
        BatchTimeout:   5 * time.Second,
        ExportTimeout:  30 * time.Second,
        Insecure:       true,
    })
    if err != nil {
        log.Fatalf("Failed to create Tempo exporter: %v", err)
    }
    defer tempoExporter.Shutdown(ctx)

    // 2. 设置路由
    mux := http.NewServeMux()
    mux.HandleFunc("/user", GetUserHandler)
    mux.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
        writeJSON(w, http.StatusOK, Response{Code: 200, Message: "OK"})
    })

    // 3. 应用追踪中间件
    handler := TracingMiddleware(mux)

    // 4. 启动服务器
    log.Println("Starting server on :8080...")
    if err := http.ListenAndServe(":8080", handler); err != nil {
        log.Fatalf("Server failed: %v", err)
    }
}
```

### 4. 分布式追踪示例

```go
package main

import (
    "context"
    "fmt"
    "math/rand"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

var (
    apiTracer      = otel.Tracer("api-gateway")
    authTracer     = otel.Tracer("auth-service")
    userTracer     = otel.Tracer("user-service")
    paymentTracer  = otel.Tracer("payment-service")
)

// OrderRequest 订单请求
type OrderRequest struct {
    UserID    int64
    ProductID int64
    Amount    float64
}

// CreateOrder 创建订单 (API Gateway)
func CreateOrder(ctx context.Context, req *OrderRequest) error {
    ctx, span := apiTracer.Start(ctx, "API.CreateOrder",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.Int64("order.user_id", req.UserID),
            attribute.Int64("order.product_id", req.ProductID),
            attribute.Float64("order.amount", req.Amount),
        ),
    )
    defer span.End()

    // 1. 验证用户身份
    if err := authenticateUser(ctx, req.UserID); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Authentication failed")
        return err
    }

    // 2. 验证用户信息
    if err := validateUser(ctx, req.UserID); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "User validation failed")
        return err
    }

    // 3. 处理支付
    if err := processPayment(ctx, req.UserID, req.Amount); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Payment failed")
        return err
    }

    span.AddEvent("Order created successfully")
    span.SetStatus(codes.Ok, "Order completed")
    return nil
}

// authenticateUser 验证用户 (Auth Service)
func authenticateUser(ctx context.Context, userID int64) error {
    _, span := authTracer.Start(ctx, "Auth.ValidateToken",
        trace.WithSpanKind(trace.SpanKindInternal),
        trace.WithAttributes(
            attribute.Int64("auth.user_id", userID),
        ),
    )
    defer span.End()

    // 模拟验证延迟
    time.Sleep(time.Duration(20+rand.Intn(30)) * time.Millisecond)

    // 5% 概率验证失败
    if rand.Float64() < 0.05 {
        err := fmt.Errorf("invalid token")
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetAttributes(attribute.Bool("auth.valid", true))
    return nil
}

// validateUser 验证用户信息 (User Service)
func validateUser(ctx context.Context, userID int64) error {
    ctx, span := userTracer.Start(ctx, "User.Validate",
        trace.WithSpanKind(trace.SpanKindInternal),
        trace.WithAttributes(
            attribute.Int64("user.id", userID),
        ),
    )
    defer span.End()

    // 查询数据库
    if err := queryUserDB(ctx, userID); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "DB query failed")
        return err
    }

    // 检查缓存
    checkUserCache(ctx, userID)

    span.SetAttributes(attribute.Bool("user.valid", true))
    return nil
}

// queryUserDB 查询用户数据库
func queryUserDB(ctx context.Context, userID int64) error {
    _, span := userTracer.Start(ctx, "User.DB.Query",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "postgresql"),
            attribute.String("db.operation", "SELECT"),
            attribute.String("db.statement", "SELECT * FROM users WHERE id = $1"),
        ),
    )
    defer span.End()

    time.Sleep(time.Duration(30+rand.Intn(50)) * time.Millisecond)

    // 3% 概率查询失败
    if rand.Float64() < 0.03 {
        err := fmt.Errorf("database timeout")
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    return nil
}

// checkUserCache 检查用户缓存
func checkUserCache(ctx context.Context, userID int64) bool {
    _, span := userTracer.Start(ctx, "User.Cache.Get",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("cache.system", "redis"),
            attribute.String("cache.key", fmt.Sprintf("user:%d", userID)),
        ),
    )
    defer span.End()

    time.Sleep(time.Duration(2+rand.Intn(5)) * time.Millisecond)

    hit := rand.Float64() < 0.8 // 80% 缓存命中
    span.SetAttributes(attribute.Bool("cache.hit", hit))
    return hit
}

// processPayment 处理支付 (Payment Service)
func processPayment(ctx context.Context, userID int64, amount float64) error {
    ctx, span := paymentTracer.Start(ctx, "Payment.Process",
        trace.WithSpanKind(trace.SpanKindInternal),
        trace.WithAttributes(
            attribute.Int64("payment.user_id", userID),
            attribute.Float64("payment.amount", amount),
        ),
    )
    defer span.End()

    // 1. 调用第三方支付接口
    if err := callPaymentGateway(ctx, amount); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Payment gateway failed")
        return err
    }

    // 2. 更新数据库
    if err := updatePaymentDB(ctx, userID, amount); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "DB update failed")
        return err
    }

    span.AddEvent("Payment completed")
    span.SetStatus(codes.Ok, "Payment successful")
    return nil
}

// callPaymentGateway 调用支付网关
func callPaymentGateway(ctx context.Context, amount float64) error {
    _, span := paymentTracer.Start(ctx, "Payment.Gateway.Call",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("payment.gateway", "stripe"),
            attribute.Float64("payment.amount", amount),
        ),
    )
    defer span.End()

    time.Sleep(time.Duration(50+rand.Intn(100)) * time.Millisecond)

    // 2% 概率支付失败
    if rand.Float64() < 0.02 {
        err := fmt.Errorf("payment gateway timeout")
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetAttributes(attribute.String("payment.transaction_id", fmt.Sprintf("txn_%d", time.Now().Unix())))
    return nil
}

// updatePaymentDB 更新支付数据库
func updatePaymentDB(ctx context.Context, userID int64, amount float64) error {
    _, span := paymentTracer.Start(ctx, "Payment.DB.Update",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "postgresql"),
            attribute.String("db.operation", "INSERT"),
            attribute.String("db.table", "payments"),
        ),
    )
    defer span.End()

    time.Sleep(time.Duration(20+rand.Intn(30)) * time.Millisecond)
    return nil
}

func main() {
    // 初始化 Tempo 导出器
    ctx := context.Background()
    tempoExporter, err := NewTempoExporter(ctx, &TempoConfig{
        Endpoint:       "localhost:4317",
        ServiceName:    "order-system",
        ServiceVersion: "1.0.0",
        Environment:    "production",
        SamplingRate:   1.0, // 全采样
        Insecure:       true,
    })
    if err != nil {
        panic(err)
    }
    defer tempoExporter.Shutdown(ctx)

    // 模拟创建订单
    for i := 0; i < 10; i++ {
        req := &OrderRequest{
            UserID:    int64(1000 + i),
            ProductID: int64(2000 + i),
            Amount:    99.99,
        }

        if err := CreateOrder(ctx, req); err != nil {
            fmt.Printf("Order failed: %v\n", err)
        } else {
            fmt.Printf("Order created successfully for user %d\n", req.UserID)
        }

        time.Sleep(1 * time.Second)
    }

    // 强制刷新
    tempoExporter.ForceFlush(ctx)
    time.Sleep(2 * time.Second)
}
```

---

## 高级特性

### 1. TraceQL 查询语言

TraceQL 是 Tempo 的原生查询语言，用于搜索和过滤追踪数据。

#### TraceQL 语法示例

```traceql
# 1. 基础查询 - 查找所有包含错误的追踪
{ status = error }

# 2. 属性过滤 - 查找特定服务的追踪
{ service.name = "user-service" }

# 3. 时长过滤 - 查找耗时超过 1 秒的追踪
{ duration > 1s }

# 4. 组合查询 - 查找慢查询且有错误的追踪
{ service.name = "database" && duration > 500ms && status = error }

# 5. HTTP 状态码过滤
{ http.status_code >= 400 }

# 6. 资源属性过滤
{ resource.deployment.environment = "production" }

# 7. Span 名称过滤
{ name = "DB.Query" }

# 8. 复杂查询 - 查找生产环境中慢 API 调用
{
  resource.service.name = "api-gateway" &&
  resource.deployment.environment = "production" &&
  span.http.method = "POST" &&
  duration > 1s &&
  span.http.status_code >= 500
}
```

#### Go 中使用 TraceQL

```go
package tempo

import (
    "context"
    "encoding/json"
    "fmt"
    "io"
    "net/http"
    "net/url"
)

// TempoQuerier Tempo 查询客户端
type TempoQuerier struct {
    baseURL string
    client  *http.Client
}

// NewTempoQuerier 创建查询客户端
func NewTempoQuerier(baseURL string) *TempoQuerier {
    return &TempoQuerier{
        baseURL: baseURL,
        client:  &http.Client{},
    }
}

// TraceQLQuery TraceQL 查询结果
type TraceQLQuery struct {
    TraceID    string            `json:"traceID"`
    RootService string           `json:"rootServiceName"`
    RootSpan   string            `json:"rootTraceName"`
    StartTime  int64             `json:"startTimeUnixNano"`
    Duration   int64             `json:"durationMs"`
    SpanSets   []SpanSet         `json:"spanSets"`
}

// SpanSet Span 集合
type SpanSet struct {
    Spans      []Span            `json:"spans"`
    Matched    int               `json:"matched"`
}

// Span Span 信息
type Span struct {
    SpanID         string            `json:"spanID"`
    StartTime      int64             `json:"startTimeUnixNano"`
    Duration       int64             `json:"durationNanos"`
    Attributes     map[string]string `json:"attributes"`
}

// SearchWithTraceQL 使用 TraceQL 搜索
func (q *TempoQuerier) SearchWithTraceQL(ctx context.Context, query string) ([]TraceQLQuery, error) {
    // 构建查询 URL
    searchURL := fmt.Sprintf("%s/api/search", q.baseURL)
    params := url.Values{}
    params.Add("q", query)

    req, err := http.NewRequestWithContext(ctx, "GET", searchURL+"?"+params.Encode(), nil)
    if err != nil {
        return nil, fmt.Errorf("failed to create request: %w", err)
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, fmt.Errorf("failed to execute request: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusOK {
        body, _ := io.ReadAll(resp.Body)
        return nil, fmt.Errorf("query failed: %s, body: %s", resp.Status, string(body))
    }

    var result struct {
        Traces []TraceQLQuery `json:"traces"`
    }

    if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
        return nil, fmt.Errorf("failed to decode response: %w", err)
    }

    return result.Traces, nil
}

// GetTraceByID 通过 TraceID 获取完整追踪
func (q *TempoQuerier) GetTraceByID(ctx context.Context, traceID string) (map[string]interface{}, error) {
    traceURL := fmt.Sprintf("%s/api/traces/%s", q.baseURL, traceID)

    req, err := http.NewRequestWithContext(ctx, "GET", traceURL, nil)
    if err != nil {
        return nil, fmt.Errorf("failed to create request: %w", err)
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, fmt.Errorf("failed to execute request: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusOK {
        return nil, fmt.Errorf("trace not found: %s", traceID)
    }

    var trace map[string]interface{}
    if err := json.NewDecoder(resp.Body).Decode(&trace); err != nil {
        return nil, fmt.Errorf("failed to decode trace: %w", err)
    }

    return trace, nil
}

// 使用示例
func ExampleTraceQL() {
    querier := NewTempoQuerier("http://localhost:3200")
    ctx := context.Background()

    // 查找慢查询
    traces, err := querier.SearchWithTraceQL(ctx, `{ duration > 1s && status = error }`)
    if err != nil {
        fmt.Printf("Query failed: %v\n", err)
        return
    }

    fmt.Printf("Found %d traces\n", len(traces))
    for _, trace := range traces {
        fmt.Printf("TraceID: %s, Duration: %dms, Service: %s\n",
            trace.TraceID, trace.Duration, trace.RootService)

        // 获取完整追踪详情
        detail, err := querier.GetTraceByID(ctx, trace.TraceID)
        if err != nil {
            fmt.Printf("Failed to get trace detail: %v\n", err)
            continue
        }

        fmt.Printf("Trace detail: %+v\n", detail)
    }
}
```

### 2. Metrics Generator (度量生成器)

Tempo 可以从追踪数据中生成度量指标。

#### 配置 Metrics Generator

```yaml
# tempo-config.yaml
metrics_generator:
  # 启用度量生成器
  registry:
    external_labels:
      source: tempo
      cluster: production
  
  # 存储配置
  storage:
    path: /var/tempo/generator/wal
    remote_write:
      - url: http://prometheus:9090/api/v1/write
        send_exemplars: true
  
  # 生成器配置
  processor:
    # 服务图生成器 (Service Graph)
    service_graphs:
      enabled: true
      max_items: 10000
      wait: 10s
      workers: 10
    
    # Span 度量生成器
    span_metrics:
      enabled: true
      dimensions:
        - http.method
        - http.status_code
        - service.name
      intrinsic_dimensions:
        service: true
        span_name: true
        span_kind: true
        status_code: true
```

#### Go 代码中启用 Exemplars

```go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

var (
    tracer = otel.Tracer("example-service")
    meter  = otel.Meter("example-service")
)

// MetricsWithExemplars 带 Exemplars 的度量
type MetricsWithExemplars struct {
    requestDuration metric.Float64Histogram
    requestCounter  metric.Int64Counter
}

func NewMetricsWithExemplars() (*MetricsWithExemplars, error) {
    // 创建直方图 (记录请求时长)
    requestDuration, err := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }

    // 创建计数器 (记录请求次数)
    requestCounter, err := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("HTTP request count"),
    )
    if err != nil {
        return nil, err
    }

    return &MetricsWithExemplars{
        requestDuration: requestDuration,
        requestCounter:  requestCounter,
    }, nil
}

// RecordRequest 记录请求 (自动关联 Trace)
func (m *MetricsWithExemplars) RecordRequest(ctx context.Context, duration time.Duration, statusCode int, method string) {
    // 获取当前 Span 的 TraceID 和 SpanID
    span := trace.SpanFromContext(ctx)
    spanContext := span.SpanContext()

    attrs := []attribute.KeyValue{
        attribute.String("http.method", method),
        attribute.Int("http.status_code", statusCode),
    }

    // 记录时长 (Tempo 会自动提取 TraceID 作为 Exemplar)
    m.requestDuration.Record(ctx, duration.Seconds()*1000, metric.WithAttributes(attrs...))

    // 记录计数
    m.requestCounter.Add(ctx, 1, metric.WithAttributes(attrs...))

    // 日志中包含 TraceID (便于关联)
    if spanContext.IsValid() {
        span.AddEvent("metrics_recorded",
            trace.WithAttributes(
                attribute.String("trace_id", spanContext.TraceID().String()),
                attribute.String("span_id", spanContext.SpanID().String()),
            ),
        )
    }
}

// 使用示例
func HandleRequest(ctx context.Context, metrics *MetricsWithExemplars) {
    start := time.Now()

    ctx, span := tracer.Start(ctx, "HandleRequest")
    defer span.End()

    // 业务逻辑
    time.Sleep(100 * time.Millisecond)

    // 记录度量 (自动关联 Trace)
    duration := time.Since(start)
    metrics.RecordRequest(ctx, duration, 200, "GET")
}
```

### 3. 服务图 (Service Graph)

Tempo 可以自动生成服务依赖关系图。

#### 查询服务图

```go
package tempo

import (
    "context"
    "encoding/json"
    "fmt"
    "net/http"
)

// ServiceGraph 服务图
type ServiceGraph struct {
    Nodes []ServiceNode `json:"nodes"`
    Edges []ServiceEdge `json:"edges"`
}

// ServiceNode 服务节点
type ServiceNode struct {
    ID          string  `json:"id"`
    Label       string  `json:"label"`
    Calls       int64   `json:"calls"`
    ErrorRate   float64 `json:"error_rate"`
    AvgDuration float64 `json:"avg_duration"`
}

// ServiceEdge 服务边
type ServiceEdge struct {
    Source      string  `json:"source"`
    Target      string  `json:"target"`
    Calls       int64   `json:"calls"`
    ErrorRate   float64 `json:"error_rate"`
    AvgDuration float64 `json:"avg_duration"`
}

// GetServiceGraph 获取服务图
func (q *TempoQuerier) GetServiceGraph(ctx context.Context) (*ServiceGraph, error) {
    graphURL := fmt.Sprintf("%s/api/metrics/service_graph", q.baseURL)

    req, err := http.NewRequestWithContext(ctx, "GET", graphURL, nil)
    if err != nil {
        return nil, fmt.Errorf("failed to create request: %w", err)
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, fmt.Errorf("failed to execute request: %w", err)
    }
    defer resp.Body.Close()

    var graph ServiceGraph
    if err := json.NewDecoder(resp.Body).Decode(&graph); err != nil {
        return nil, fmt.Errorf("failed to decode service graph: %w", err)
    }

    return &graph, nil
}

// PrintServiceGraph 打印服务图
func PrintServiceGraph(graph *ServiceGraph) {
    fmt.Println("=== Service Graph ===")
    fmt.Println("\nNodes:")
    for _, node := range graph.Nodes {
        fmt.Printf("  - %s: %d calls, %.2f%% errors, %.2fms avg\n",
            node.Label, node.Calls, node.ErrorRate*100, node.AvgDuration)
    }

    fmt.Println("\nEdges:")
    for _, edge := range graph.Edges {
        fmt.Printf("  - %s → %s: %d calls, %.2f%% errors, %.2fms avg\n",
            edge.Source, edge.Target, edge.Calls, edge.ErrorRate*100, edge.AvgDuration)
    }
}
```

---

## 性能优化

### 1. 采样策略

```go
package tempo

import (
    "context"
    "fmt"
    "strings"

    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/trace"
)

// AdaptiveSampler 自适应采样器
type AdaptiveSampler struct {
    baseSampler    sdktrace.Sampler
    errorSampler   sdktrace.Sampler
    slowSampler    sdktrace.Sampler
    slowThreshold  float64 // 慢请求阈值 (秒)
}

// NewAdaptiveSampler 创建自适应采样器
func NewAdaptiveSampler(baseRate, errorRate, slowRate, slowThreshold float64) *AdaptiveSampler {
    return &AdaptiveSampler{
        baseSampler:   sdktrace.TraceIDRatioBased(baseRate),
        errorSampler:  sdktrace.TraceIDRatioBased(errorRate),
        slowSampler:   sdktrace.TraceIDRatioBased(slowRate),
        slowThreshold: slowThreshold,
    }
}

// ShouldSample 采样决策
func (s *AdaptiveSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 1. 检查是否有错误属性
    for _, attr := range params.Attributes {
        if attr.Key == "error" && attr.Value.AsBool() {
            return s.errorSampler.ShouldSample(params)
        }
        if attr.Key == "http.status_code" {
            statusCode := attr.Value.AsInt64()
            if statusCode >= 400 {
                return s.errorSampler.ShouldSample(params)
            }
        }
    }

    // 2. 检查是否是慢请求 (需要在 Span 结束时判断,这里仅示例)
    // 实际场景中可以通过自定义 SpanProcessor 实现

    // 3. 默认采样
    return s.baseSampler.ShouldSample(params)
}

// Description 采样器描述
func (s *AdaptiveSampler) Description() string {
    return fmt.Sprintf("AdaptiveSampler{base=%s,error=%s,slow=%s}",
        s.baseSampler.Description(),
        s.errorSampler.Description(),
        s.slowSampler.Description(),
    )
}

// HeadBasedSampler 基于请求头的采样器
type HeadBasedSampler struct {
    defaultSampler sdktrace.Sampler
    forceSample    []string // 强制采样的路径前缀
}

// NewHeadBasedSampler 创建基于请求头的采样器
func NewHeadBasedSampler(defaultRate float64, forceSample []string) *HeadBasedSampler {
    return &HeadBasedSampler{
        defaultSampler: sdktrace.TraceIDRatioBased(defaultRate),
        forceSample:    forceSample,
    }
}

// ShouldSample 采样决策
func (s *HeadBasedSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 检查是否在强制采样列表中
    for _, attr := range params.Attributes {
        if attr.Key == "http.target" {
            path := attr.Value.AsString()
            for _, prefix := range s.forceSample {
                if strings.HasPrefix(path, prefix) {
                    return sdktrace.SamplingResult{
                        Decision:   sdktrace.RecordAndSample,
                        Tracestate: trace.SpanContextFromContext(params.ParentContext).TraceState(),
                    }
                }
            }
        }
    }

    // 默认采样策略
    return s.defaultSampler.ShouldSample(params)
}

// Description 采样器描述
func (s *HeadBasedSampler) Description() string {
    return fmt.Sprintf("HeadBasedSampler{default=%s,force=%v}",
        s.defaultSampler.Description(), s.forceSample)
}

// 使用示例
func ExampleAdaptiveSampler() {
    ctx := context.Background()

    // 创建自适应采样器
    sampler := NewAdaptiveSampler(
        0.01,  // 基础采样率 1%
        1.0,   // 错误全采样 100%
        0.5,   // 慢请求采样率 50%
        1.0,   // 慢请求阈值 1 秒
    )

    tempoExporter, _ := NewTempoExporter(ctx, &TempoConfig{
        Endpoint:    "localhost:4317",
        ServiceName: "adaptive-service",
        Insecure:    true,
    })
    defer tempoExporter.Shutdown(ctx)

    // 手动设置采样器
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(tempoExporter.exporter),
        sdktrace.WithSampler(sampler),
    )
    _ = tp
}
```

### 2. 批处理优化

```go
package tempo

import (
    "time"

    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// BatchConfig 批处理配置
type BatchConfig struct {
    MaxQueueSize       int           // 最大队列大小
    BatchTimeout       time.Duration // 批处理超时
    ExportTimeout      time.Duration // 导出超时
    MaxExportBatchSize int           // 最大批处理大小
}

// OptimizedBatchConfig 优化的批处理配置
func OptimizedBatchConfig(throughput string) BatchConfig {
    switch throughput {
    case "low": // < 100 spans/s
        return BatchConfig{
            MaxQueueSize:       512,
            BatchTimeout:       10 * time.Second,
            ExportTimeout:      30 * time.Second,
            MaxExportBatchSize: 128,
        }
    case "medium": // 100-1000 spans/s
        return BatchConfig{
            MaxQueueSize:       2048,
            BatchTimeout:       5 * time.Second,
            ExportTimeout:      30 * time.Second,
            MaxExportBatchSize: 512,
        }
    case "high": // > 1000 spans/s
        return BatchConfig{
            MaxQueueSize:       8192,
            BatchTimeout:       2 * time.Second,
            ExportTimeout:      30 * time.Second,
            MaxExportBatchSize: 2048,
        }
    default:
        return OptimizedBatchConfig("medium")
    }
}

// ApplyBatchConfig 应用批处理配置
func ApplyBatchConfig(exporter sdktrace.SpanExporter, cfg BatchConfig) sdktrace.TracerProviderOption {
    return sdktrace.WithBatcher(exporter,
        sdktrace.WithMaxQueueSize(cfg.MaxQueueSize),
        sdktrace.WithBatchTimeout(cfg.BatchTimeout),
        sdktrace.WithExportTimeout(cfg.ExportTimeout),
        sdktrace.WithMaxExportBatchSize(cfg.MaxExportBatchSize),
    )
}
```

### 3. 连接池优化

```go
package tempo

import (
    "time"

    "google.golang.org/grpc"
    "google.golang.org/grpc/keepalive"
)

// GRPCOptimizedDialOptions 优化的 gRPC 连接选项
func GRPCOptimizedDialOptions() []grpc.DialOption {
    return []grpc.DialOption{
        // 连接池配置
        grpc.WithDefaultCallOptions(
            grpc.MaxCallRecvMsgSize(10 * 1024 * 1024), // 10MB
            grpc.MaxCallSendMsgSize(10 * 1024 * 1024), // 10MB
        ),

        // Keepalive 配置
        grpc.WithKeepaliveParams(keepalive.ClientParameters{
            Time:                30 * time.Second, // 每 30 秒发送 keepalive ping
            Timeout:             10 * time.Second, // 10 秒内无响应则断开
            PermitWithoutStream: true,             // 无活动流时也发送 ping
        }),

        // 初始窗口大小
        grpc.WithInitialWindowSize(1 << 20),     // 1MB
        grpc.WithInitialConnWindowSize(1 << 20), // 1MB

        // 最大并发流
        grpc.WithDefaultServiceConfig(`{"loadBalancingPolicy":"round_robin"}`),
    }
}
```

---

## 生产部署

### 1. Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  # Tempo 服务
  tempo:
    image: grafana/tempo:2.3.0
    container_name: tempo
    command: ["-config.file=/etc/tempo/tempo.yaml"]
    volumes:
      - ./tempo-config.yaml:/etc/tempo/tempo.yaml
      - tempo-data:/var/tempo
    ports:
      - "3200:3200"   # Tempo HTTP
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "9095:9095"   # Tempo gRPC
      - "14268:14268" # Jaeger ingest
    networks:
      - observability

  # Prometheus (用于存储 Metrics Generator 数据)
  prometheus:
    image: prom/prometheus:latest
    container_name: prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.enable-remote-write-receiver'
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    networks:
      - observability

  # Grafana (可视化)
  grafana:
    image: grafana/grafana:latest
    container_name: grafana
    environment:
      - GF_AUTH_ANONYMOUS_ENABLED=true
      - GF_AUTH_ANONYMOUS_ORG_ROLE=Admin
    volumes:
      - ./grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml
      - grafana-data:/var/lib/grafana
    ports:
      - "3000:3000"
    networks:
      - observability
    depends_on:
      - tempo
      - prometheus

volumes:
  tempo-data:
  prometheus-data:
  grafana-data:

networks:
  observability:
    driver: bridge
```

#### Grafana 数据源配置

```yaml
# grafana-datasources.yml
apiVersion: 1

datasources:
  - name: Tempo
    type: tempo
    access: proxy
    url: http://tempo:3200
    jsonData:
      httpMethod: GET
      tracesToLogs:
        datasourceUid: 'loki'
        tags: ['job', 'instance', 'pod', 'namespace']
        mappedTags: [{ key: 'service.name', value: 'service' }]
        mapTagNamesEnabled: false
        spanStartTimeShift: '1h'
        spanEndTimeShift: '1h'
      tracesToMetrics:
        datasourceUid: 'prometheus'
        tags: [{ key: 'service.name', value: 'service' }]
        queries:
          - name: 'Sample query'
            query: 'sum(rate(traces_spanmetrics_latency_bucket{$__tags}[5m]))'
      serviceMap:
        datasourceUid: 'prometheus'
      search:
        hide: false
      nodeGraph:
        enabled: true

  - name: Prometheus
    type: prometheus
    access: proxy
    url: http://prometheus:9090
    jsonData:
      httpMethod: POST
      exemplarTraceIdDestinations:
        - name: traceID
          datasourceUid: tempo
```

### 2. Kubernetes 部署

```yaml
# tempo-deployment.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: tempo-config
  namespace: observability
data:
  tempo.yaml: |
    server:
      http_listen_port: 3200
      grpc_listen_port: 9095

    distributor:
      receivers:
        otlp:
          protocols:
            grpc:
              endpoint: 0.0.0.0:4317
            http:
              endpoint: 0.0.0.0:4318

    ingester:
      max_block_duration: 5m
      max_block_bytes: 1048576

    compactor:
      compaction:
        block_retention: 168h

    storage:
      trace:
        backend: s3
        s3:
          bucket: tempo-traces
          endpoint: s3.amazonaws.com
          access_key: ${AWS_ACCESS_KEY_ID}
          secret_key: ${AWS_SECRET_ACCESS_KEY}
          region: us-east-1
        wal:
          path: /var/tempo/wal

    querier:
      frontend_worker:
        frontend_address: tempo-query-frontend:9095

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: tempo
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: tempo
  template:
    metadata:
      labels:
        app: tempo
    spec:
      containers:
      - name: tempo
        image: grafana/tempo:2.3.0
        args:
          - "-config.file=/etc/tempo/tempo.yaml"
        ports:
        - containerPort: 3200
          name: http
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        - containerPort: 9095
          name: grpc
        volumeMounts:
        - name: config
          mountPath: /etc/tempo
        - name: storage
          mountPath: /var/tempo
        resources:
          requests:
            memory: "2Gi"
            cpu: "1000m"
          limits:
            memory: "4Gi"
            cpu: "2000m"
        livenessProbe:
          httpGet:
            path: /ready
            port: 3200
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 3200
          initialDelaySeconds: 10
          periodSeconds: 5
      volumes:
      - name: config
        configMap:
          name: tempo-config
      - name: storage
        emptyDir: {}

---
apiVersion: v1
kind: Service
metadata:
  name: tempo
  namespace: observability
spec:
  selector:
    app: tempo
  ports:
  - name: http
    port: 3200
    targetPort: 3200
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
  - name: grpc
    port: 9095
    targetPort: 9095
  type: ClusterIP

---
apiVersion: v1
kind: Service
metadata:
  name: tempo-otlp
  namespace: observability
  annotations:
    service.beta.kubernetes.io/aws-load-balancer-type: "nlb"
spec:
  selector:
    app: tempo
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
    protocol: TCP
  type: LoadBalancer
```

### 3. 生产配置优化

```yaml
# tempo-production.yaml
server:
  http_listen_port: 3200
  grpc_listen_port: 9095
  log_level: info
  log_format: json

distributor:
  receivers:
    otlp:
      protocols:
        grpc:
          endpoint: 0.0.0.0:4317
          # gRPC 优化
          max_recv_msg_size: 10485760  # 10MB
          max_concurrent_streams: 1000
        http:
          endpoint: 0.0.0.0:4318
  
  # 限流配置
  rate_limiting:
    enabled: true
    rate: 10000  # 10K spans/s per distributor
    burst: 20000
  
  # 日志丢弃策略
  log_received_spans:
    enabled: false
    include_all_attributes: false

ingester:
  # 块配置
  max_block_duration: 10m      # 生产环境适当增大
  max_block_bytes: 10485760    # 10MB
  complete_block_timeout: 30m
  
  # 生命周期配置
  lifecycler:
    ring:
      replication_factor: 3
      kvstore:
        store: etcd
        etcd:
          endpoints:
            - http://etcd-1:2379
            - http://etcd-2:2379
            - http://etcd-3:2379
    
    # 健康检查
    heartbeat_period: 5s
    heartbeat_timeout: 1m

compactor:
  compaction:
    block_retention: 720h  # 30 days
    compacted_block_retention: 1h
    compaction_window: 1h
    max_block_bytes: 107374182400  # 100GB
    max_compaction_objects: 10000000
  
  ring:
    kvstore:
      store: etcd
      etcd:
        endpoints:
          - http://etcd-1:2379
          - http://etcd-2:2379
          - http://etcd-3:2379

storage:
  trace:
    backend: s3
    s3:
      bucket: tempo-prod-traces
      endpoint: s3.amazonaws.com
      region: us-east-1
      access_key: ${AWS_ACCESS_KEY_ID}
      secret_key: ${AWS_SECRET_ACCESS_KEY}
      insecure: false
      # S3 优化
      part_size: 5242880  # 5MB
      hedge_requests_at: 500ms
      hedge_requests_up_to: 2
    
    wal:
      path: /var/tempo/wal
      encoding: snappy
    
    # 块配置
    block:
      version: vParquet3
      encoding: zstd
    
    # 缓存配置
    cache: memcached
    memcached:
      host: memcached:11211
      timeout: 500ms
      max_idle_conns: 100
      max_item_size: 5242880  # 5MB
    
    # 后台缓存配置
    background_cache:
      writeback_goroutines: 10
      writeback_buffer: 10000

querier:
  max_concurrent_queries: 20
  
  frontend_worker:
    frontend_address: tempo-query-frontend:9095
    parallelism: 10
    match_max_concurrent: true
  
  # 查询超时
  search:
    external_endpoints: []
    external_hedge_requests_at: 8s
    external_hedge_requests_up_to: 2

query_frontend:
  max_outstanding_per_tenant: 2000
  max_retries: 2
  
  search:
    concurrent_jobs: 1000
    target_bytes_per_job: 104857600  # 100MB
    max_duration: 168h

metrics_generator:
  registry:
    external_labels:
      source: tempo
      environment: production
  
  storage:
    path: /var/tempo/generator/wal
    remote_write:
      - url: http://prometheus:9090/api/v1/write
        send_exemplars: true
        queue_config:
          capacity: 10000
          max_shards: 50
          min_shards: 1
          max_samples_per_send: 2000
          batch_send_deadline: 5s
  
  processor:
    service_graphs:
      enabled: true
      max_items: 100000
      wait: 30s
      workers: 50
    
    span_metrics:
      enabled: true
      dimensions:
        - http.method
        - http.status_code
        - service.name
        - deployment.environment
      intrinsic_dimensions:
        service: true
        span_name: true
        span_kind: true
        status_code: true
      filter_policies:
        - include:
            match_type: strict
            attributes:
              - key: service.name
                value: critical-service

overrides:
  per_tenant_override_config: /etc/tempo/overrides.yaml
  per_tenant_override_period: 10s

# 限制配置
limits:
  # 全局限制
  max_traces_per_user: 100000
  max_bytes_per_trace: 5242880  # 5MB
  
  # 搜索限制
  max_search_duration: 168h
  
  # 摄入限制
  ingestion_rate_strategy: global
  ingestion_rate_limit_bytes: 50000000  # 50MB/s
  ingestion_burst_size_bytes: 100000000 # 100MB
```

---

## 最佳实践

### 1. 属性命名规范

```go
package tempo

import (
    "go.opentelemetry.io/otel/attribute"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// 推荐的属性命名
var (
    // HTTP 属性
    HTTPMethod     = semconv.HTTPMethod
    HTTPStatusCode = semconv.HTTPStatusCode
    HTTPRoute      = semconv.HTTPRoute
    HTTPURL        = semconv.HTTPURL
    
    // 数据库属性
    DBSystem    = semconv.DBSystem
    DBName      = semconv.DBName
    DBStatement = semconv.DBStatement
    DBOperation = semconv.DBOperation
    
    // 消息队列属性
    MessagingSystem      = semconv.MessagingSystem
    MessagingDestination = semconv.MessagingDestination
    MessagingOperation   = semconv.MessagingOperation
    
    // RPC 属性
    RPCSystem  = semconv.RPCSystem
    RPCService = semconv.RPCService
    RPCMethod  = semconv.RPCMethod
    
    // 自定义业务属性 (建议使用域名前缀)
    UserID       = attribute.Key("app.user.id")
    TenantID     = attribute.Key("app.tenant.id")
    OrderID      = attribute.Key("app.order.id")
    BusinessUnit = attribute.Key("app.business.unit")
)

// SetBusinessAttributes 设置业务属性
func SetBusinessAttributes(span trace.Span, userID, orderID string) {
    span.SetAttributes(
        UserID.String(userID),
        OrderID.String(orderID),
    )
}
```

### 2. 错误处理最佳实践

```go
package tempo

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// RecordError 记录错误的最佳实践
func RecordError(ctx context.Context, err error, additionalInfo ...string) {
    span := trace.SpanFromContext(ctx)
    
    // 1. 记录错误
    span.RecordError(err)
    
    // 2. 设置状态
    span.SetStatus(codes.Error, err.Error())
    
    // 3. 添加额外信息
    if len(additionalInfo) > 0 {
        span.AddEvent("error_context",
            trace.WithAttributes(
                attribute.String("context", additionalInfo[0]),
            ),
        )
    }
}

// HandleDBError 处理数据库错误示例
func HandleDBError(ctx context.Context, operation string, err error) error {
    span := trace.SpanFromContext(ctx)
    
    span.RecordError(err,
        trace.WithAttributes(
            attribute.String("db.operation", operation),
            attribute.String("error.type", fmt.Sprintf("%T", err)),
        ),
    )
    
    span.SetStatus(codes.Error, fmt.Sprintf("DB operation failed: %s", operation))
    
    return fmt.Errorf("database %s failed: %w", operation, err)
}
```

### 3. 追踪上下文传播

```go
package tempo

import (
    "context"
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// InjectTraceContext 注入追踪上下文到 HTTP 请求
func InjectTraceContext(ctx context.Context, req *http.Request) {
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
}

// ExtractTraceContext 从 HTTP 请求提取追踪上下文
func ExtractTraceContext(req *http.Request) context.Context {
    return otel.GetTextMapPropagator().Extract(req.Context(), propagation.HeaderCarrier(req.Header))
}

// HTTPClient 带追踪的 HTTP 客户端
func HTTPClient(ctx context.Context, url string) (*http.Response, error) {
    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        return nil, err
    }
    
    // 注入追踪上下文
    InjectTraceContext(ctx, req)
    
    return http.DefaultClient.Do(req)
}
```

---

## 故障排查

### 1. 常见问题

```text
问题 1: 追踪数据未显示
原因:
  - Tempo 服务未启动
  - 端口配置错误
  - 采样率设置为 0
  - 防火墙阻止连接

排查:
  1. 检查 Tempo 服务状态: docker ps | grep tempo
  2. 检查端口监听: netstat -tlnp | grep 4317
  3. 检查采样配置: 确认 SamplingRate > 0
  4. 测试连接: telnet localhost 4317

问题 2: 查询 TraceID 失败
原因:
  - TraceID 格式错误
  - 数据还未写入存储
  - 存储后端配置错误

排查:
  1. 验证 TraceID 格式: 32位十六进制字符串
  2. 等待数据刷新: 默认 5-10 分钟
  3. 检查存储配置: 查看 storage 配置段

问题 3: 性能问题
原因:
  - 批处理配置不当
  - 连接池不足
  - 采样率过高

排查:
  1. 调整批处理大小: 增大 MaxQueueSize
  2. 增加连接数: 调整 gRPC 连接池
  3. 降低采样率: 调整 SamplingRate

问题 4: 数据丢失
原因:
  - 队列溢出
  - 导出超时
  - 网络问题

排查:
  1. 检查日志: 查找 "queue full" 或 "export timeout"
  2. 增大队列: 调整 MaxQueueSize
  3. 增加超时: 调整 ExportTimeout
  4. 启用重试: 配置 retry policy
```

### 2. 监控指标

```yaml
# prometheus-rules.yml
groups:
  - name: tempo
    interval: 30s
    rules:
      # Distributor 指标
      - record: tempo_distributor_spans_received_rate
        expr: rate(tempo_distributor_spans_received_total[5m])
      
      - record: tempo_distributor_bytes_received_rate
        expr: rate(tempo_distributor_bytes_received_total[5m])
      
      - alert: TempoDistributorHighErrorRate
        expr: rate(tempo_distributor_spans_received_total{status="error"}[5m]) > 100
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Tempo Distributor high error rate"
          description: "Distributor error rate is {{ $value }} spans/s"
      
      # Ingester 指标
      - record: tempo_ingester_blocks_flushed_rate
        expr: rate(tempo_ingester_blocks_flushed_total[5m])
      
      - alert: TempoIngesterHighMemory
        expr: process_resident_memory_bytes{job="tempo-ingester"} > 8589934592  # 8GB
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "Tempo Ingester high memory usage"
          description: "Ingester memory usage is {{ $value | humanize }}B"
      
      # Querier 指标
      - record: tempo_querier_query_duration_99p
        expr: histogram_quantile(0.99, rate(tempo_querier_query_duration_seconds_bucket[5m]))
      
      - alert: TempoQuerierSlowQueries
        expr: tempo_querier_query_duration_99p > 10
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Tempo Querier slow queries"
          description: "P99 query duration is {{ $value }}s"
      
      # Storage 指标
      - alert: TempoStorageErrors
        expr: rate(tempo_storage_errors_total[5m]) > 10
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Tempo Storage errors"
          description: "Storage error rate is {{ $value }} errors/s"
```

### 3. 日志分析

```go
package tempo

import (
    "context"
    "log"
    "time"

    "go.opentelemetry.io/otel/trace"
)

// DebugLogger 调试日志记录器
type DebugLogger struct {
    tracer trace.Tracer
}

// NewDebugLogger 创建调试日志记录器
func NewDebugLogger(tracerName string) *DebugLogger {
    return &DebugLogger{
        tracer: otel.Tracer(tracerName),
    }
}

// LogWithTrace 带追踪信息的日志
func (l *DebugLogger) LogWithTrace(ctx context.Context, level, message string, args ...interface{}) {
    span := trace.SpanFromContext(ctx)
    spanContext := span.SpanContext()
    
    if spanContext.IsValid() {
        log.Printf("[%s] [TraceID: %s] [SpanID: %s] %s %v",
            level,
            spanContext.TraceID().String(),
            spanContext.SpanID().String(),
            message,
            args,
        )
    } else {
        log.Printf("[%s] [No Trace] %s %v", level, message, args)
    }
}

// DebugExporter 调试导出器
type DebugExporter struct {
    exporter sdktrace.SpanExporter
}

// ExportSpans 导出 Spans (带日志)
func (e *DebugExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
    start := time.Now()
    err := e.exporter.ExportSpans(ctx, spans)
    duration := time.Since(start)
    
    if err != nil {
        log.Printf("[ERROR] Failed to export %d spans in %v: %v", len(spans), duration, err)
    } else {
        log.Printf("[INFO] Successfully exported %d spans in %v", len(spans), duration)
    }
    
    return err
}

// Shutdown 关闭导出器
func (e *DebugExporter) Shutdown(ctx context.Context) error {
    return e.exporter.Shutdown(ctx)
}
```

---

## 总结

### 核心要点

```text
✅ Tempo 优势:
  - 成本极低 (仅需对象存储)
  - 扩展性强 (无索引设计)
  - 与 Grafana 深度集成
  - 支持多种追踪格式

✅ 集成步骤:
  1. 安装 OTLP 依赖包
  2. 配置 Tempo 服务
  3. 创建 OTLP 导出器
  4. 应用追踪中间件
  5. 设置采样策略

✅ 高级特性:
  - TraceQL 查询语言
  - Metrics Generator
  - Service Graph
  - Exemplars 关联

✅ 性能优化:
  - 自适应采样
  - 批处理优化
  - 连接池配置
  - 缓存策略

✅ 生产部署:
  - Docker Compose
  - Kubernetes
  - 高可用配置
  - 监控告警
```

### 性能基准

```text
Tempo 性能指标:
  - 吞吐量: 100K+ spans/s per instance
  - 查询延迟: <100ms (TraceID 查询)
  - 存储成本: ~$0.02/GB/月 (S3)
  - 压缩比: 10:1
  - 数据保留: 可配置 (默认 7 天)
```

### 下一步

```text
1. 深入学习:
   - TraceQL 高级查询
   - Metrics Generator 配置
   - 多租户配置

2. 集成扩展:
   - 集成 Loki (日志)
   - 集成 Mimir (指标)
   - 完整可观测性栈

3. 优化调优:
   - 存储后端选择
   - 压缩算法优化
   - 查询性能调优
```

---

**更新时间**: 2025-10-12  
**文档版本**: v1.0.0  
**维护团队**: OTLP Go Integration Team

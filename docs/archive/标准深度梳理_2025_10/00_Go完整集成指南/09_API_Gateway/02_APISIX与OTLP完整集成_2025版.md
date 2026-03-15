# APISIX 与 OTLP 完整集成指南 2025版

## 概述

Apache APISIX 是一个高性能、可扩展的云原生 API 网关。本指南详细介绍如何在 Go 1.25.1 应用中集成 APISIX 与 OpenTelemetry Protocol (OTLP)，实现完整的 API 网关可观测性。

## 目录

- [APISIX 与 OTLP 完整集成指南 2025版](#apisix-与-otlp-完整集成指南-2025版)
  - [概述](#概述)
  - [目录](#目录)
  - [APISIX 架构概述](#apisix-架构概述)
    - [核心组件](#核心组件)
    - [插件系统](#插件系统)
  - [快速开始](#快速开始)
    - [1. APISIX 安装和配置](#1-apisix-安装和配置)
      - [Docker Compose 部署](#docker-compose-部署)
      - [APISIX 配置文件](#apisix-配置文件)
    - [2. OpenTelemetry Collector 配置](#2-opentelemetry-collector-配置)
  - [APISIX 插件配置](#apisix-插件配置)
    - [OpenTelemetry 插件配置](#opentelemetry-插件配置)
    - [Prometheus 插件配置](#prometheus-插件配置)
  - [Go 应用 OTLP 集成](#go-应用-otlp-集成)
    - [1. 基础 HTTP 服务集成](#1-基础-http-服务集成)
    - [2. gRPC 服务集成](#2-grpc-服务集成)
  - [分布式追踪配置](#分布式追踪配置)
    - [1. 追踪上下文传播](#1-追踪上下文传播)
  - [API 网关可观测性](#api-网关可观测性)
    - [1. APISIX 指标监控](#1-apisix-指标监控)
  - [性能优化](#性能优化)
    - [1. 采样策略](#1-采样策略)
  - [生产部署](#生产部署)
    - [1. Docker Compose 部署](#1-docker-compose-部署)
    - [2. Kubernetes 部署](#2-kubernetes-部署)
  - [最佳实践](#最佳实践)
    - [1. 追踪设计原则](#1-追踪设计原则)
    - [2. 性能优化建议](#2-性能优化建议)
  - [总结](#总结)

## APISIX 架构概述

### 核心组件

```mermaid
graph TB
    A[客户端请求] --> B[APISIX Gateway]
    B --> C[插件系统]
    C --> D[上游服务]
    D --> E[Go 应用]
    E --> F[OTLP Exporter]
    F --> G[OpenTelemetry Collector]
    G --> H[后端存储]
    
    subgraph "APISIX 插件"
        I[OpenTelemetry Plugin]
        J[Zipkin Plugin]
        K[Jaeger Plugin]
        L[Prometheus Plugin]
        M[Rate Limiting]
        N[Authentication]
    end
    
    C --> I
    C --> J
    C --> K
    C --> L
    C --> M
    C --> N
```

### 插件系统

APISIX 提供丰富的插件生态系统，支持各种可观测性需求：

- **OpenTelemetry Plugin**: 原生 OTLP 支持
- **Zipkin Plugin**: Zipkin 格式追踪
- **Jaeger Plugin**: Jaeger 格式追踪
- **Prometheus Plugin**: 指标收集
- **SkyWalking Plugin**: SkyWalking 集成

## 快速开始

### 1. APISIX 安装和配置

#### Docker Compose 部署

```yaml
# docker-compose.apisix.yml
version: '3.8'

services:
  etcd:
    image: bitnami/etcd:3.5.9
    environment:
      ETCD_ENABLE_V2: "true"
      ALLOW_NONE_AUTHENTICATION: "yes"
      ETCD_ADVERTISE_CLIENT_URLS: "http://0.0.0.0:2379"
      ETCD_LISTEN_CLIENT_URLS: "http://0.0.0.0:2379"
    ports:
      - "2379:2379"
    networks:
      - apisix-net

  apisix:
    image: apache/apisix:3.4.0-debian
    ports:
      - "9080:9080"
      - "9180:9180"
    volumes:
      - ./configs/apisix.yaml:/usr/local/apisix/conf/config.yaml:ro
    depends_on:
      - etcd
    networks:
      - apisix-net

  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.88.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./configs/otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
    networks:
      - apisix-net

networks:
  apisix-net:
    driver: bridge
```

#### APISIX 配置文件

```yaml
# configs/apisix.yaml
apisix:
  node_listen: 9080
  enable_admin: true
  admin_key:
    - name: "admin"
      key: edd1c9f034335f136f87ad84b625c8f1
      role: admin
  enable_debug: false
  enable_admin_cors: true
  admin_listen:
    ip: "0.0.0.0"
    port: 9180
  enable_control: true
  control:
    ip: "0.0.0.0"
    port: 9090
  enable_server_tokens: false
  enable_admin_api_key: false
  config_center: etcd
  etcd:
    host:
      - "http://etcd:2379"
    prefix: "/apisix"
    timeout: 30
  deployment:
    role: traditional
    role_traditional:
      config_provider: etcd
    admin_listen:
      ip: "0.0.0.0"
      port: 9180
    http_admin:
      enable: true
      admin_key:
        - name: "admin"
          key: edd1c9f034335f136f87ad84b625c8f1
          role: admin
plugins:
  - opentelemetry
  - prometheus
  - zipkin
  - jaeger
  - skywalking
```

### 2. OpenTelemetry Collector 配置

```yaml
# configs/otel-collector-config.yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 1s
    send_batch_size: 1024
  memory_limiter:
    limit_mib: 512
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: upsert

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  prometheus:
    endpoint: "0.0.0.0:8889"
  logging:
    loglevel: debug

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [jaeger, logging]
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [prometheus, logging]
```

## APISIX 插件配置

### OpenTelemetry 插件配置

```bash
# 创建上游服务
curl -X POST http://localhost:9180/apisix/admin/upstreams/1 \
  -H "X-API-KEY: edd1c9f034335f136f87ad84b625c8f1" \
  -H "Content-Type: application/json" \
  -d '{
    "type": "roundrobin",
    "nodes": {
      "user-service:8080": 1
    }
  }'

# 创建路由
curl -X POST http://localhost:9180/apisix/admin/routes/1 \
  -H "X-API-KEY: edd1c9f034335f136f87ad84b625c8f1" \
  -H "Content-Type: application/json" \
  -d '{
    "uri": "/api/users/*",
    "methods": ["GET", "POST", "PUT", "DELETE"],
    "upstream_id": 1,
    "plugins": {
      "opentelemetry": {
        "endpoint": "http://otel-collector:4317",
        "sampling_ratio": 1.0,
        "batch_span_processor": {
          "max_export_batch_size": 512,
          "export_timeout": 30,
          "max_queue_size": 2048
        },
        "resource": {
          "service.name": "apisix-gateway",
          "service.version": "1.0.0"
        }
      }
    }
  }'
```

### Prometheus 插件配置

```bash
# 启用 Prometheus 插件
curl -X POST http://localhost:9180/apisix/admin/plugins/prometheus \
  -H "X-API-KEY: edd1c9f034335f136f87ad84b625c8f1" \
  -H "Content-Type: application/json" \
  -d '{
    "prefer_name": true
  }'
```

## Go 应用 OTLP 集成

### 1. 基础 HTTP 服务集成

```go
// main.go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/trace"
)

func initTracer() func() {
    ctx := context.Background()

    // 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatalf("Failed to create OTLP exporter: %v", err)
    }

    // 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            attribute.String("service.name", "user-service"),
            attribute.String("service.version", "1.0.0"),
            attribute.String("deployment.environment", "production"),
        ),
    )
    if err != nil {
        log.Fatalf("Failed to create resource: %v", err)
    }

    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(1.0)),
    )

    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return func() {
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }
}

func main() {
    // 初始化追踪
    cleanup := initTracer()
    defer cleanup()

    // 创建 HTTP 服务器
    mux := http.NewServeMux()
    mux.HandleFunc("/api/users", handleUsers)
    mux.HandleFunc("/health", handleHealth)

    // 添加中间件
    handler := tracingMiddleware(mux)

    log.Println("Starting server on :8080")
    if err := http.ListenAndServe(":8080", handler); err != nil {
        log.Fatalf("Server failed: %v", err)
    }
}

func tracingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 从请求头中提取追踪上下文
        ctx := otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
        
        // 创建新的 span
        tracer := otel.Tracer("user-service")
        ctx, span := tracer.Start(ctx, r.URL.Path,
            trace.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.url", r.URL.String()),
                attribute.String("http.user_agent", r.UserAgent()),
            ),
        )
        defer span.End()

        // 创建响应写入器来捕获状态码
        ww := &responseWriter{ResponseWriter: w, statusCode: 200}

        // 处理请求
        next.ServeHTTP(ww, r.WithContext(ctx))

        // 设置 span 属性
        span.SetAttributes(
            attribute.Int("http.status_code", ww.statusCode),
            attribute.String("http.route", r.URL.Path),
        )
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

func handleUsers(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("user-service")
    
    // 创建子 span
    _, span := tracer.Start(ctx, "get-users")
    defer span.End()

    // 模拟数据库查询
    time.Sleep(100 * time.Millisecond)
    
    // 设置响应
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusOK)
    w.Write([]byte(`{"users": [{"id": 1, "name": "John Doe"}]}`))
    
    span.SetAttributes(
        attribute.Int("users.count", 1),
        attribute.String("response.format", "json"),
    )
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
    w.WriteHeader(http.StatusOK)
    w.Write([]byte("OK"))
}
```

### 2. gRPC 服务集成

```go
// grpc_server.go
package main

import (
    "context"
    "log"
    "net"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
)

type UserService struct {
    UnimplementedUserServiceServer
}

func (s *UserService) GetUser(ctx context.Context, req *GetUserRequest) (*GetUserResponse, error) {
    tracer := otel.Tracer("user-service")
    
    // 创建 span
    ctx, span := tracer.Start(ctx, "get-user",
        trace.WithAttributes(
            attribute.String("user.id", req.Id),
            attribute.String("grpc.method", "GetUser"),
        ),
    )
    defer span.End()

    // 模拟业务逻辑
    user := &User{
        Id:   req.Id,
        Name: "John Doe",
        Email: "john@example.com",
    }

    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )

    return &GetUserResponse{User: user}, nil
}

func grpcTracingInterceptor() grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
        // 从 metadata 中提取追踪上下文
        md, ok := metadata.FromIncomingContext(ctx)
        if ok {
            ctx = otel.GetTextMapPropagator().Extract(ctx, metadataCarrier(md))
        }

        // 创建 span
        tracer := otel.Tracer("user-service")
        ctx, span := tracer.Start(ctx, info.FullMethod,
            trace.WithAttributes(
                attribute.String("grpc.method", info.FullMethod),
                attribute.String("grpc.service", info.Server),
            ),
        )
        defer span.End()

        // 处理请求
        resp, err := handler(ctx, req)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        } else {
            span.SetStatus(codes.Ok, "")
        }

        return resp, err
    }
}

type metadataCarrier metadata.MD

func (mc metadataCarrier) Get(key string) string {
    values := metadata.MD(mc).Get(key)
    if len(values) > 0 {
        return values[0]
    }
    return ""
}

func (mc metadataCarrier) Set(key, value string) {
    metadata.MD(mc).Set(key, value)
}

func (mc metadataCarrier) Keys() []string {
    keys := make([]string, 0, len(metadata.MD(mc)))
    for k := range metadata.MD(mc) {
        keys = append(keys, k)
    }
    return keys
}

func main() {
    // 初始化追踪
    cleanup := initTracer()
    defer cleanup()

    // 创建 gRPC 服务器
    server := grpc.NewServer(
        grpc.UnaryInterceptor(grpcTracingInterceptor()),
    )

    // 注册服务
    RegisterUserServiceServer(server, &UserService{})

    // 启动服务器
    lis, err := net.Listen("tcp", ":9090")
    if err != nil {
        log.Fatalf("Failed to listen: %v", err)
    }

    log.Println("Starting gRPC server on :9090")
    if err := server.Serve(lis); err != nil {
        log.Fatalf("Failed to serve: %v", err)
    }
}
```

## 分布式追踪配置

### 1. 追踪上下文传播

```go
// context_propagation.go
package main

import (
    "context"
    "fmt"
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/baggage"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

func propagateContext(ctx context.Context, w http.ResponseWriter, r *http.Request) {
    // 从请求中提取追踪上下文
    ctx = otel.GetTextMapPropagator().Extract(ctx, propagation.HeaderCarrier(r.Header))
    
    // 添加自定义 baggage
    ctx, err := baggage.New(ctx,
        baggage.Member("user.id", "12345"),
        baggage.Member("request.source", "mobile"),
    )
    if err != nil {
        log.Printf("Failed to create baggage: %v", err)
    }

    // 创建 span
    tracer := otel.Tracer("context-propagation")
    ctx, span := tracer.Start(ctx, "process-request",
        trace.WithAttributes(
            attribute.String("http.method", r.Method),
            attribute.String("http.url", r.URL.String()),
        ),
    )
    defer span.End()

    // 处理请求
    processRequest(ctx, w, r)
}

func processRequest(ctx context.Context, w http.ResponseWriter, r *http.Request) {
    // 获取 baggage 信息
    bag := baggage.FromContext(ctx)
    userID := bag.Member("user.id").Value()
    source := bag.Member("request.source").Value()

    // 创建子 span
    tracer := otel.Tracer("context-propagation")
    ctx, span := tracer.Start(ctx, "business-logic",
        trace.WithAttributes(
            attribute.String("user.id", userID),
            attribute.String("request.source", source),
        ),
    )
    defer span.End()

    // 模拟业务逻辑
    result := fmt.Sprintf("Processing request for user %s from %s", userID, source)
    
    w.WriteHeader(http.StatusOK)
    w.Write([]byte(result))
}
```

## API 网关可观测性

### 1. APISIX 指标监控

```go
// metrics.go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/prometheus"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/sdk/metric"
)

func initMetrics() func() {
    // 创建 Prometheus 导出器
    exporter, err := prometheus.New()
    if err != nil {
        log.Fatalf("Failed to create Prometheus exporter: %v", err)
    }

    // 创建 MeterProvider
    mp := metric.NewMeterProvider(
        metric.WithReader(exporter),
    )

    otel.SetMeterProvider(mp)

    // 启动 Prometheus 服务器
    go func() {
        http.Handle("/metrics", exporter)
        log.Println("Prometheus metrics server starting on :8888")
        if err := http.ListenAndServe(":8888", nil); err != nil {
            log.Printf("Prometheus server failed: %v", err)
        }
    }()

    return func() {
        if err := mp.Shutdown(context.Background()); err != nil {
            log.Printf("Error shutting down meter provider: %v", err)
        }
    }
}

func main() {
    // 初始化指标
    cleanup := initMetrics()
    defer cleanup()

    // 创建指标
    meter := otel.Meter("apisix-gateway")
    
    // 请求计数器
    requestCounter, err := meter.Int64Counter(
        "http_requests_total",
        metric.WithDescription("Total number of HTTP requests"),
    )
    if err != nil {
        log.Fatalf("Failed to create request counter: %v", err)
    }

    // 请求延迟直方图
    requestDuration, err := meter.Float64Histogram(
        "http_request_duration_seconds",
        metric.WithDescription("HTTP request duration in seconds"),
    )
    if err != nil {
        log.Fatalf("Failed to create request duration histogram: %v", err)
    }

    // 创建 HTTP 服务器
    mux := http.NewServeMux()
    mux.HandleFunc("/api/users", func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        
        // 记录请求
        requestCounter.Add(context.Background(), 1,
            metric.WithAttributes(
                attribute.String("method", r.Method),
                attribute.String("path", r.URL.Path),
                attribute.String("status", "200"),
            ),
        )

        // 处理请求
        time.Sleep(100 * time.Millisecond)
        w.WriteHeader(http.StatusOK)
        w.Write([]byte(`{"users": []}`))

        // 记录延迟
        duration := time.Since(start).Seconds()
        requestDuration.Record(context.Background(), duration,
            metric.WithAttributes(
                attribute.String("method", r.Method),
                attribute.String("path", r.URL.Path),
            ),
        )
    })

    log.Println("Starting server on :8080")
    if err := http.ListenAndServe(":8080", mux); err != nil {
        log.Fatalf("Server failed: %v", err)
    }
}
```

## 性能优化

### 1. 采样策略

```go
// sampling.go
package main

import (
    "context"
    "log"
    "math/rand"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/trace"
)

// 自定义采样器
type CustomSampler struct {
    baseSampler trace.Sampler
    rate        float64
}

func NewCustomSampler(rate float64) *CustomSampler {
    return &CustomSampler{
        baseSampler: trace.TraceIDRatioBased(rate),
        rate:        rate,
    }
}

func (s *CustomSampler) ShouldSample(params trace.SamplingParameters) trace.SamplingResult {
    // 对健康检查请求不采样
    if params.Name == "health-check" {
        return trace.SamplingResult{Decision: trace.Drop}
    }
    
    // 对错误请求总是采样
    if params.HasRemoteParent && params.ParentContext.IsValid() {
        if params.ParentContext.TraceID().IsValid() {
            return trace.SamplingResult{Decision: trace.RecordAndSample}
        }
    }
    
    // 使用基础采样器
    return s.baseSampler.ShouldSample(params)
}

func (s *CustomSampler) Description() string {
    return fmt.Sprintf("CustomSampler{rate=%f}", s.rate)
}

func initTracerWithSampling() func() {
    ctx := context.Background()

    // 创建自定义采样器
    sampler := NewCustomSampler(0.1) // 10% 采样率

    // 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithSampler(sampler),
    )

    otel.SetTracerProvider(tp)

    return func() {
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }
}
```

## 生产部署

### 1. Docker Compose 部署

```yaml
# docker-compose.prod.yml
version: '3.8'

services:
  etcd:
    image: bitnami/etcd:3.5.9
    environment:
      ETCD_ENABLE_V2: "true"
      ALLOW_NONE_AUTHENTICATION: "yes"
      ETCD_ADVERTISE_CLIENT_URLS: "http://0.0.0.0:2379"
      ETCD_LISTEN_CLIENT_URLS: "http://0.0.0.0:2379"
    volumes:
      - etcd_data:/bitnami/etcd
    networks:
      - apisix-net
    deploy:
      resources:
        limits:
          memory: 1G
          cpus: '0.5'
        reservations:
          memory: 512M
          cpus: '0.25'

  apisix:
    image: apache/apisix:3.4.0-debian
    ports:
      - "9080:9080"
      - "9180:9180"
    volumes:
      - ./configs/apisix.yaml:/usr/local/apisix/conf/config.yaml:ro
    depends_on:
      - etcd
    networks:
      - apisix-net
    deploy:
      replicas: 3
      resources:
        limits:
          memory: 2G
          cpus: '1.0'
        reservations:
          memory: 1G
          cpus: '0.5'
      restart_policy:
        condition: on-failure
        delay: 5s
        max_attempts: 3

  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.88.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./configs/otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
    networks:
      - apisix-net
    deploy:
      replicas: 2
      resources:
        limits:
          memory: 1G
          cpus: '0.5'
        reservations:
          memory: 512M
          cpus: '0.25'
      restart_policy:
        condition: on-failure
        delay: 5s
        max_attempts: 3

volumes:
  etcd_data:

networks:
  apisix-net:
    driver: bridge
```

### 2. Kubernetes 部署

```yaml
# k8s/apisix-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: apisix
  namespace: apisix
spec:
  replicas: 3
  selector:
    matchLabels:
      app: apisix
  template:
    metadata:
      labels:
        app: apisix
    spec:
      containers:
      - name: apisix
        image: apache/apisix:3.4.0-debian
        ports:
        - containerPort: 9080
          name: gateway
        - containerPort: 9180
          name: admin
        env:
        - name: APISIX_STAND_ALONE
          value: "false"
        - name: APISIX_ETCD_ENDPOINTS
          value: "http://etcd:2379"
        resources:
          requests:
            memory: "1Gi"
            cpu: "500m"
          limits:
            memory: "2Gi"
            cpu: "1000m"
        livenessProbe:
          httpGet:
            path: /apisix/admin/routes
            port: 9180
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /apisix/admin/routes
            port: 9180
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: apisix
  namespace: apisix
spec:
  selector:
    app: apisix
  ports:
  - name: gateway
    port: 9080
    targetPort: 9080
  - name: admin
    port: 9180
    targetPort: 9180
  type: LoadBalancer
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: apisix-hpa
  namespace: apisix
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: apisix
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

## 最佳实践

### 1. 追踪设计原则

```go
// tracing_principles.go
package main

import (
    "context"
    "log"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 1. 合理的 Span 命名
func handleUserRequest(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("user-service")
    
    // 好的命名：动词 + 名词
    ctx, span := tracer.Start(ctx, "get-user-profile")
    defer span.End()
    
    // 避免：过于宽泛或过于具体
    // ctx, span := tracer.Start(ctx, "request") // 太宽泛
    // ctx, span := tracer.Start(ctx, "get-user-profile-from-database-by-id-12345") // 太具体
}

// 2. 合理的属性设置
func processOrder(ctx context.Context, orderID string) error {
    tracer := otel.Tracer("order-service")
    ctx, span := tracer.Start(ctx, "process-order")
    defer span.End()
    
    // 好的属性：业务相关的关键信息
    span.SetAttributes(
        attribute.String("order.id", orderID),
        attribute.String("order.status", "processing"),
        attribute.String("user.id", getUserID(ctx)),
    )
    
    // 避免：过多的技术细节
    // span.SetAttributes(
    //     attribute.String("database.connection.pool.size", "10"),
    //     attribute.String("http.client.timeout", "30s"),
    // )
    
    return nil
}

// 3. 错误处理
func callExternalAPI(ctx context.Context, url string) error {
    tracer := otel.Tracer("external-api")
    ctx, span := tracer.Start(ctx, "call-external-api")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("external.api.url", url),
    )
    
    // 模拟 API 调用
    if time.Now().Unix()%2 == 0 {
        err := fmt.Errorf("external API error")
        span.RecordError(err)
        span.SetStatus(trace.StatusError, err.Error())
        return err
    }
    
    span.SetStatus(trace.StatusOk, "success")
    return nil
}
```

### 2. 性能优化建议

```go
// performance_optimization.go
package main

import (
    "context"
    "log"
    "net/http"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 1. 避免创建过多的 Span
func inefficientTracing(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("inefficient")
    
    // 避免：为每个小操作创建 span
    for i := 0; i < 100; i++ {
        ctx, span := tracer.Start(ctx, "small-operation")
        // 小操作
        time.Sleep(1 * time.Millisecond)
        span.End()
    }
}

func efficientTracing(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("efficient")
    
    // 好的做法：为整个操作创建一个 span
    ctx, span := tracer.Start(ctx, "batch-operation")
    defer span.End()
    
    // 批量处理
    for i := 0; i < 100; i++ {
        // 小操作
        time.Sleep(1 * time.Millisecond)
    }
    
    span.SetAttributes(
        attribute.Int("operations.count", 100),
        attribute.Int("total.duration_ms", 100),
    )
}

// 2. 使用异步导出
func initTracerWithAsyncExport() func() {
    ctx := context.Background()
    
    // 创建异步导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatalf("Failed to create OTLP exporter: %v", err)
    }
    
    // 使用批量导出器
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
            sdktrace.WithMaxQueueSize(2048),
        ),
    )
    
    otel.SetTracerProvider(tp)
    
    return func() {
        tp.Shutdown(ctx)
    }
}

// 3. 缓存 Tracer
var (
    tracerOnce sync.Once
    cachedTracer trace.Tracer
)

func getTracer() trace.Tracer {
    tracerOnce.Do(func() {
        cachedTracer = otel.Tracer("cached-tracer")
    })
    return cachedTracer
}

func useCachedTracer(ctx context.Context) {
    tracer := getTracer()
    ctx, span := tracer.Start(ctx, "cached-tracer-operation")
    defer span.End()
    
    // 使用缓存的 tracer
}
```

## 总结

本指南详细介绍了如何在 Go 1.25.1 应用中集成 APISIX 与 OpenTelemetry Protocol (OTLP)，包括：

1. **APISIX 架构和插件系统**：了解 APISIX 的核心组件和可观测性插件
2. **快速开始**：Docker Compose 部署和基础配置
3. **Go 应用集成**：HTTP 和 gRPC 服务的 OTLP 集成
4. **分布式追踪**：上下文传播和跨服务追踪
5. **可观测性**：指标监控和健康检查
6. **性能优化**：采样策略、批量导出和资源限制
7. **生产部署**：Docker Compose 和 Kubernetes 部署
8. **最佳实践**：追踪设计、性能优化和安全考虑

通过本指南，您可以构建一个完整的、可观测的 API 网关系统，实现端到端的分布式追踪和监控。

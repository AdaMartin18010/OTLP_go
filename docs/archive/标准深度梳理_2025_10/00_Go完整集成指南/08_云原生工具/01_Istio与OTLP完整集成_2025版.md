# Istio 与 OTLP 完整集成指南 (2025版)

> **最新更新**: 2025年10月  
> **Go版本**: 1.25.1  
> **Istio版本**: v1.23.0+  
> **OpenTelemetry SDK**: v1.31.0+

## 📋 目录

- [Istio 与 OTLP 完整集成指南 (2025版)](#istio-与-otlp-完整集成指南-2025版)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [Istio 简介](#istio-简介)
    - [为什么集成 OTLP？](#为什么集成-otlp)
    - [架构图](#架构图)
  - [Istio 架构概览](#istio-架构概览)
    - [核心组件](#核心组件)
  - [快速开始](#快速开始)
    - [1. 安装 Istio](#1-安装-istio)
    - [2. 部署 OpenTelemetry Collector](#2-部署-opentelemetry-collector)
    - [3. 配置 Istio 追踪](#3-配置-istio-追踪)
  - [Sidecar 自动注入追踪](#sidecar-自动注入追踪)
    - [1. 部署示例应用](#1-部署示例应用)
    - [2. 验证 Sidecar 注入](#2-验证-sidecar-注入)
  - [应用级 OTLP 集成](#应用级-otlp-集成)
    - [1. Go 应用集成 OTLP](#1-go-应用集成-otlp)
    - [2. Frontend 服务实现](#2-frontend-服务实现)
    - [3. Backend 服务实现](#3-backend-服务实现)
  - [分布式追踪配置](#分布式追踪配置)
    - [1. 采样策略](#1-采样策略)
    - [2. 按命名空间配置](#2-按命名空间配置)
    - [3. 按服务配置](#3-按服务配置)
  - [服务网格可观测性](#服务网格可观测性)
    - [1. Istio Metrics 集成](#1-istio-metrics-集成)
    - [2. 查询追踪数据](#2-查询追踪数据)
    - [3. Grafana 可视化](#3-grafana-可视化)
  - [性能优化](#性能优化)
    - [1. Envoy 追踪优化](#1-envoy-追踪优化)
    - [2. 批量导出优化](#2-批量导出优化)
    - [3. 资源限制](#3-资源限制)
  - [生产部署](#生产部署)
    - [1. 高可用部署](#1-高可用部署)
    - [2. 监控告警](#2-监控告警)
  - [最佳实践](#最佳实践)
    - [1. 采样策略1](#1-采样策略1)
    - [2. Span 命名规范](#2-span-命名规范)
    - [3. 属性添加](#3-属性添加)
    - [4. Context 传递](#4-context-传递)
  - [总结](#总结)
    - [Istio + OTLP 优势](#istio--otlp-优势)
    - [性能指标](#性能指标)
    - [推荐配置](#推荐配置)
  - [参考资源](#参考资源)

---

## 概述

### Istio 简介

**Istio** 是业界领先的服务网格 (Service Mesh) 解决方案，主要特点：

- **流量管理**: 智能路由、负载均衡、熔断限流
- **安全**: mTLS、认证授权、策略管理
- **可观测性**: 自动生成 metrics、traces、logs
- **无侵入**: Sidecar 模式，无需修改应用代码
- **多云支持**: 支持 Kubernetes、虚拟机等多种环境

### 为什么集成 OTLP？

1. **标准化**: OpenTelemetry 是云原生可观测性标准
2. **统一导出**: 统一追踪数据格式，支持多后端
3. **完整链路**: Istio Sidecar + 应用内追踪 = 完整分布式追踪
4. **灵活性**: 可以选择不同的追踪后端 (Jaeger、Tempo、Zipkin 等)

### 架构图

```text
┌─────────────────────────────────────────────────────────────┐
│                      Kubernetes Cluster                     │
│                                                             │
│  ┌────────────────────────────────────────────────────────┐ │
│  │  Namespace: app                                        │ │
│  │                                                        │ │
│  │  ┌──────────────────┐       ┌──────────────────┐      │ │
│  │  │  Pod: frontend   │       │  Pod: backend    │      │ │
│  │  │  ┌────────────┐  │       │  ┌────────────┐  │      │ │
│  │  │  │ App        │  │       │  │ App        │  │      │ │
│  │  │  │ (Go)       │◄─┼───────┼──┤ (Go)       │  │      │ │
│  │  │  └────────────┘  │       │  └────────────┘  │      │ │
│  │  │  ┌────────────┐  │       │  ┌────────────┐  │      │ │
│  │  │  │ Envoy Proxy│  │       │  │ Envoy Proxy│  │      │ │
│  │  │  │ (Sidecar)  │  │       │  │ (Sidecar)  │  │      │ │
│  │  │  │ • Trace    │  │       │  │ • Trace    │  │      │ │
│  │  │  │ • Metrics  │  │       │  │ • Metrics  │  │      │ │
│  │  │  └─────┬──────┘  │       │  └─────┬──────┘  │      │ │
│  │  └────────┼─────────┘       └────────┼─────────┘      │ │
│  └───────────┼──────────────────────────┼────────────────┘ │
│              │                           │                  │
│  ┌───────────▼───────────────────────────▼────────────────┐ │
│  │  Istio Control Plane (istiod)                           │ │
│  │  • Service Discovery                                    │ │
│  │  • Configuration Distribution                           │ │
│  │  • Certificate Management                               │ │
│  └─────────────────────────────────────────────────────────┘ │
│                           │                                  │
└───────────────────────────┼──────────────────────────────────┘
                            │
                ┌───────────▼───────────┐
                │  OTel Collector       │
                │  • Receive OTLP       │
                │  • Process & Export   │
                └───────────┬───────────┘
                            │
            ┌───────────────┴───────────────┐
            │                               │
    ┌───────▼──────┐              ┌────────▼────────┐
    │  Jaeger      │              │  Grafana Tempo  │
    │  UI          │              │  Storage        │
    └──────────────┘              └─────────────────┘
```

---

## Istio 架构概览

### 核心组件

1. **Data Plane (数据平面)**
   - **Envoy Proxy**: Sidecar 代理，拦截所有流量
   - 自动生成追踪数据 (B3、W3C Trace Context)
   - 自动传播追踪上下文

2. **Control Plane (控制平面)**
   - **istiod**: 统一控制平面
   - 配置管理和分发
   - 证书管理 (mTLS)
   - 服务发现

3. **可观测性组件**
   - **Telemetry**: 遥测数据收集
   - **Tracing**: 分布式追踪配置
   - **Metrics**: 指标收集

---

## 快速开始

### 1. 安装 Istio

```bash
# 下载 Istio
curl -L https://istio.io/downloadIstio | sh -
cd istio-1.23.0
export PATH=$PWD/bin:$PATH

# 安装 Istio (demo 配置)
istioctl install --set profile=demo -y

# 启用 Sidecar 自动注入
kubectl label namespace default istio-injection=enabled
```

### 2. 部署 OpenTelemetry Collector

```yaml
# otel-collector.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: istio-system
data:
  config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
      zipkin:
        endpoint: 0.0.0.0:9411

    processors:
      batch:
        timeout: 1s
        send_batch_size: 1024
      memory_limiter:
        check_interval: 1s
        limit_mib: 512

    exporters:
      otlp/jaeger:
        endpoint: jaeger-collector.observability:4317
        tls:
          insecure: true
      logging:
        loglevel: info

    service:
      pipelines:
        traces:
          receivers: [otlp, zipkin]
          processors: [memory_limiter, batch]
          exporters: [otlp/jaeger, logging]
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: istio-system
spec:
  replicas: 2
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.112.0
        args:
          - --config=/conf/config.yaml
        ports:
        - containerPort: 4317  # OTLP gRPC
        - containerPort: 4318  # OTLP HTTP
        - containerPort: 9411  # Zipkin
        volumeMounts:
        - name: config
          mountPath: /conf
        resources:
          requests:
            memory: "256Mi"
            cpu: "200m"
          limits:
            memory: "512Mi"
            cpu: "500m"
      volumes:
      - name: config
        configMap:
          name: otel-collector-config
---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: istio-system
spec:
  selector:
    app: otel-collector
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
  - name: zipkin
    port: 9411
    targetPort: 9411
```

### 3. 配置 Istio 追踪

```yaml
# istio-telemetry.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: mesh-default
  namespace: istio-system
spec:
  tracing:
  - providers:
    - name: otel-collector
    randomSamplingPercentage: 100.0  # 100% 采样（开发环境）
    customTags:
      environment:
        literal:
          value: "production"
      cluster:
        literal:
          value: "k8s-cluster-1"
---
apiVersion: install.istio.io/v1alpha1
kind: IstioOperator
metadata:
  name: istio-config
  namespace: istio-system
spec:
  meshConfig:
    enableTracing: true
    defaultConfig:
      tracing:
        sampling: 100.0
        zipkin:
          address: otel-collector.istio-system:9411
    extensionProviders:
    - name: otel-collector
      opentelemetry:
        service: otel-collector.istio-system.svc.cluster.local
        port: 4317
```

```bash
# 应用配置
kubectl apply -f istio-telemetry.yaml
```

---

## Sidecar 自动注入追踪

### 1. 部署示例应用

```yaml
# frontend-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: frontend
  namespace: default
spec:
  replicas: 2
  selector:
    matchLabels:
      app: frontend
  template:
    metadata:
      labels:
        app: frontend
        version: v1
    spec:
      containers:
      - name: frontend
        image: your-registry/frontend:latest
        ports:
        - containerPort: 8080
        env:
        - name: BACKEND_URL
          value: "http://backend:8080"
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "otel-collector.istio-system:4317"
        - name: OTEL_SERVICE_NAME
          value: "frontend"
---
apiVersion: v1
kind: Service
metadata:
  name: frontend
  namespace: default
spec:
  selector:
    app: frontend
  ports:
  - port: 8080
    targetPort: 8080
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: backend
  namespace: default
spec:
  replicas: 2
  selector:
    matchLabels:
      app: backend
  template:
    metadata:
      labels:
        app: backend
        version: v1
    spec:
      containers:
      - name: backend
        image: your-registry/backend:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "otel-collector.istio-system:4317"
        - name: OTEL_SERVICE_NAME
          value: "backend"
---
apiVersion: v1
kind: Service
metadata:
  name: backend
  namespace: default
spec:
  selector:
    app: backend
  ports:
  - port: 8080
    targetPort: 8080
```

### 2. 验证 Sidecar 注入

```bash
# 查看 Pod，确认有 2 个容器 (app + envoy)
kubectl get pods -n default

# 输出示例:
# NAME                        READY   STATUS    RESTARTS   AGE
# frontend-xxx-yyy            2/2     Running   0          1m
# backend-xxx-yyy             2/2     Running   0          1m

# 查看 Sidecar 日志
kubectl logs -n default frontend-xxx-yyy -c istio-proxy
```

---

## 应用级 OTLP 集成

### 1. Go 应用集成 OTLP

```go
// pkg/telemetry/tracer.go
package telemetry

import (
    "context"
    "os"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

func InitTracer(ctx context.Context) (func(context.Context) error, error) {
    serviceName := os.Getenv("OTEL_SERVICE_NAME")
    if serviceName == "" {
        serviceName = "unknown-service"
    }

    endpoint := os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT")
    if endpoint == "" {
        endpoint = "otel-collector.istio-system:4317"
    }

    // 创建 OTLP exporter
    conn, err := grpc.NewClient(endpoint,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
    )
    if err != nil {
        return nil, err
    }

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithGRPCConn(conn),
    )
    if err != nil {
        return nil, err
    }

    // 创建 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String(serviceName),
            semconv.ServiceVersionKey.String("1.0.0"),
            semconv.DeploymentEnvironmentKey.String("production"),
        ),
        resource.WithHost(),
        resource.WithProcess(),
        resource.WithContainer(),
        resource.WithOS(),
    )
    if err != nil {
        return nil, err
    }

    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
        ),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )

    otel.SetTracerProvider(tp)
    
    // 设置传播器 (兼容 Istio 的 B3 和 W3C)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},  // W3C Trace Context
        propagation.Baggage{},
        propagation.B3{},            // B3 (Zipkin)
    ))

    return tp.Shutdown, nil
}
```

### 2. Frontend 服务实现

```go
// cmd/frontend/main.go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "os"

    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-app/pkg/telemetry"
)

var tracer = otel.Tracer("frontend")

func main() {
    ctx := context.Background()

    // 初始化追踪
    shutdown, err := telemetry.InitTracer(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer shutdown(ctx)

    // 创建 HTTP 服务器
    mux := http.NewServeMux()
    mux.Handle("/", otelhttp.NewHandler(http.HandlerFunc(handleRoot), "root"))
    mux.Handle("/api/data", otelhttp.NewHandler(http.HandlerFunc(handleData), "api-data"))

    port := os.Getenv("PORT")
    if port == "" {
        port = "8080"
    }

    log.Printf("Frontend server starting on port %s...", port)
    if err := http.ListenAndServe(":"+port, mux); err != nil {
        log.Fatal(err)
    }
}

func handleRoot(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "handleRoot")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.url", r.URL.String()),
    )

    fmt.Fprintf(w, "Frontend service - Request from %s\n", r.RemoteAddr)
    span.SetStatus(codes.Ok, "Success")
}

func handleData(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "handleData")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.url", r.URL.String()),
    )

    // 调用后端服务
    backendURL := os.Getenv("BACKEND_URL")
    if backendURL == "" {
        backendURL = "http://backend:8080"
    }

    data, err := callBackend(ctx, backendURL+"/api/users")
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    span.SetAttributes(attribute.String("backend.response", data))
    span.SetStatus(codes.Ok, "Success")

    fmt.Fprintf(w, "Data from backend: %s\n", data)
}

func callBackend(ctx context.Context, url string) (string, error) {
    ctx, span := tracer.Start(ctx, "callBackend")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.url", url),
        attribute.String("http.method", "GET"),
    )

    // 创建 HTTP 客户端 (自动传播追踪上下文)
    client := http.Client{
        Transport: otelhttp.NewTransport(http.DefaultTransport),
    }

    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return "", err
    }

    resp, err := client.Do(req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return "", err
    }
    defer resp.Body.Close()

    span.SetAttributes(attribute.Int("http.status_code", resp.StatusCode))
    span.SetStatus(codes.Ok, "Success")

    return "backend data", nil
}
```

### 3. Backend 服务实现

```go
// cmd/backend/main.go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "os"
    "time"

    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-app/pkg/telemetry"
)

var tracer = otel.Tracer("backend")

func main() {
    ctx := context.Background()

    // 初始化追踪
    shutdown, err := telemetry.InitTracer(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer shutdown(ctx)

    // 创建 HTTP 服务器
    mux := http.NewServeMux()
    mux.Handle("/api/users", otelhttp.NewHandler(http.HandlerFunc(handleUsers), "api-users"))

    port := os.Getenv("PORT")
    if port == "" {
        port = "8080"
    }

    log.Printf("Backend server starting on port %s...", port)
    if err := http.ListenAndServe(":"+port, mux); err != nil {
        log.Fatal(err)
    }
}

func handleUsers(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "handleUsers")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.url", r.URL.String()),
    )

    // 模拟数据库查询
    users, err := queryDatabase(ctx)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    span.SetAttributes(attribute.Int("users.count", len(users)))
    span.SetStatus(codes.Ok, "Success")

    fmt.Fprintf(w, "Users: %v\n", users)
}

func queryDatabase(ctx context.Context) ([]string, error) {
    _, span := tracer.Start(ctx, "queryDatabase")
    defer span.End()

    span.SetAttributes(
        attribute.String("db.system", "postgresql"),
        attribute.String("db.operation", "SELECT"),
        attribute.String("db.table", "users"),
    )

    // 模拟数据库延迟
    time.Sleep(50 * time.Millisecond)

    users := []string{"Alice", "Bob", "Charlie"}
    span.SetAttributes(attribute.Int("db.rows_returned", len(users)))
    span.SetStatus(codes.Ok, "Query successful")

    return users, nil
}
```

---

## 分布式追踪配置

### 1. 采样策略

```yaml
# sampling-config.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: sampling-policy
  namespace: istio-system
spec:
  tracing:
  - providers:
    - name: otel-collector
    # 生产环境建议 1-10% 采样
    randomSamplingPercentage: 10.0
    customTags:
      # 添加自定义标签
      environment:
        literal:
          value: "production"
      region:
        literal:
          value: "us-west-2"
      cluster:
        environment:
          name: CLUSTER_NAME
          defaultValue: "k8s-prod"
```

### 2. 按命名空间配置

```yaml
# namespace-telemetry.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: high-priority-tracing
  namespace: payment  # 支付服务命名空间
spec:
  tracing:
  - providers:
    - name: otel-collector
    randomSamplingPercentage: 100.0  # 支付服务 100% 采样
---
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: low-priority-tracing
  namespace: logging
spec:
  tracing:
  - providers:
    - name: otel-collector
    randomSamplingPercentage: 1.0  # 日志服务 1% 采样
```

### 3. 按服务配置

```yaml
# service-telemetry.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: frontend-tracing
  namespace: default
spec:
  selector:
    matchLabels:
      app: frontend
  tracing:
  - providers:
    - name: otel-collector
    randomSamplingPercentage: 50.0  # Frontend 50% 采样
---
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: backend-tracing
  namespace: default
spec:
  selector:
    matchLabels:
      app: backend
  tracing:
  - providers:
    - name: otel-collector
    randomSamplingPercentage: 30.0  # Backend 30% 采样
```

---

## 服务网格可观测性

### 1. Istio Metrics 集成

```yaml
# metrics-config.yaml
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: mesh-metrics
  namespace: istio-system
spec:
  metrics:
  - providers:
    - name: prometheus
    overrides:
    - match:
        metric: ALL_METRICS
      tagOverrides:
        request_protocol:
          value: "request.protocol"
        response_code:
          value: "response.code"
        destination_service:
          value: "destination.service.name"
        destination_version:
          value: "destination.workload.name | unknown"
```

### 2. 查询追踪数据

```bash
# 使用 kubectl port-forward 访问 Jaeger UI
kubectl port-forward -n observability svc/jaeger-query 16686:16686

# 浏览器打开: http://localhost:16686
```

### 3. Grafana 可视化

```yaml
# grafana-dashboard-configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: istio-tracing-dashboard
  namespace: observability
data:
  istio-tracing.json: |
    {
      "dashboard": {
        "title": "Istio Distributed Tracing",
        "panels": [
          {
            "title": "Request Rate by Service",
            "targets": [
              {
                "expr": "rate(istio_requests_total[5m])"
              }
            ]
          },
          {
            "title": "P99 Latency",
            "targets": [
              {
                "expr": "histogram_quantile(0.99, rate(istio_request_duration_milliseconds_bucket[5m]))"
              }
            ]
          }
        ]
      }
    }
```

---

## 性能优化

### 1. Envoy 追踪优化

```yaml
# envoy-tracing-config.yaml
apiVersion: install.istio.io/v1alpha1
kind: IstioOperator
metadata:
  name: istio-performance
  namespace: istio-system
spec:
  meshConfig:
    defaultConfig:
      tracing:
        sampling: 10.0  # 10% 采样
        max_path_tag_length: 256
        custom_tags:
          cluster_id:
            environment:
              name: CLUSTER_ID
              defaultValue: "unknown"
    # Envoy 性能优化
    proxyMetadata:
      ISTIO_META_DNS_CAPTURE: "false"  # 禁用 DNS 捕获
      ISTIO_META_DNS_AUTO_ALLOCATE: "false"
```

### 2. 批量导出优化

```yaml
# otel-collector-performance.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: istio-system
data:
  config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
            max_recv_msg_size_mib: 64  # 增加接收缓冲区

    processors:
      batch:
        timeout: 1s
        send_batch_size: 2048  # 增大批次
      memory_limiter:
        check_interval: 1s
        limit_mib: 1024  # 增加内存限制
      # 采样处理器
      probabilistic_sampler:
        sampling_percentage: 10.0

    exporters:
      otlp:
        endpoint: jaeger-collector:4317
        sending_queue:
          enabled: true
          num_consumers: 10  # 增加并发导出
          queue_size: 5000

    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, probabilistic_sampler, batch]
          exporters: [otlp]
```

### 3. 资源限制

```yaml
# resource-limits.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: istio-system
spec:
  template:
    spec:
      containers:
      - name: otel-collector
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "1Gi"
            cpu: "1000m"
```

---

## 生产部署

### 1. 高可用部署

```yaml
# ha-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: istio-system
spec:
  replicas: 3  # 3 个副本
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
          - weight: 100
            podAffinityTerm:
              labelSelector:
                matchExpressions:
                - key: app
                  operator: In
                  values:
                  - otel-collector
              topologyKey: kubernetes.io/hostname
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.112.0
        resources:
          requests:
            memory: "512Mi"
            cpu: "500m"
          limits:
            memory: "1Gi"
            cpu: "1000m"
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: istio-system
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector
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

### 2. 监控告警

```yaml
# prometheus-rules.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: istio-tracing-alerts
  namespace: istio-system
spec:
  groups:
  - name: istio-tracing
    interval: 30s
    rules:
    - alert: HighTracingDropRate
      expr: |
        rate(otelcol_processor_dropped_spans[5m]) > 100
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "High tracing drop rate detected"
        description: "Tracing spans are being dropped at {{ $value }} spans/s"
    
    - alert: OtelCollectorDown
      expr: |
        up{job="otel-collector"} == 0
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "OpenTelemetry Collector is down"
        description: "OTel Collector has been down for more than 5 minutes"
```

---

## 最佳实践

### 1. 采样策略1

```go
// 基于错误的智能采样
type ErrorBasedSampler struct {
    defaultSampler sdktrace.Sampler
    errorSampler   sdktrace.Sampler
}

func (s *ErrorBasedSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 如果有错误，100% 采样
    for _, attr := range params.Attributes {
        if attr.Key == "error" && attr.Value.AsBool() {
            return s.errorSampler.ShouldSample(params)
        }
    }
    // 否则使用默认采样率
    return s.defaultSampler.ShouldSample(params)
}
```

### 2. Span 命名规范

```go
// ✅ 好的命名
tracer.Start(ctx, "HTTP GET /api/users")
tracer.Start(ctx, "Database.SelectUsers")
tracer.Start(ctx, "Cache.Get")

// ❌ 避免的命名
tracer.Start(ctx, "handler")
tracer.Start(ctx, "query")
```

### 3. 属性添加

```go
// ✅ 使用语义化属性
span.SetAttributes(
    semconv.HTTPMethodKey.String("GET"),
    semconv.HTTPRouteKey.String("/api/users"),
    semconv.HTTPStatusCodeKey.Int(200),
    semconv.NetPeerNameKey.String("backend.default.svc.cluster.local"),
)
```

### 4. Context 传递

```go
// ✅ 正确传递 context
func handler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()  // 使用请求的 context
    result, err := callService(ctx)  // 传递给下游
}

// ❌ 错误：创建新的 context
func handler(w http.ResponseWriter, r *http.Request) {
    ctx := context.Background()  // 丢失追踪上下文
    result, err := callService(ctx)
}
```

---

## 总结

### Istio + OTLP 优势

1. **无侵入**: Sidecar 自动注入，无需修改应用代码
2. **完整链路**: 服务网格 + 应用内追踪 = 完整分布式追踪
3. **灵活配置**: 支持按命名空间、服务粒度配置
4. **高可用**: 支持 HA 部署和自动扩缩容
5. **标准化**: 采用 OpenTelemetry 标准，多后端兼容

### 性能指标

| 指标 | 无 Istio | Istio + Tracing (10% 采样) |
|------|----------|---------------------------|
| P50 延迟 | 10ms | 11ms (+10%) |
| P99 延迟 | 50ms | 58ms (+16%) |
| CPU 开销 | 0 | ~200m per pod |
| 内存开销 | 0 | ~128Mi per pod |

### 推荐配置

- **开发环境**: 100% 采样
- **测试环境**: 50% 采样
- **生产环境**: 1-10% 采样（关键服务可提高至 30-50%）

---

## 参考资源

- [Istio 官方文档](https://istio.io/latest/docs/)
- [Istio Telemetry API](https://istio.io/latest/docs/reference/config/telemetry/)
- [OpenTelemetry Collector](https://opentelemetry.io/docs/collector/)
- [Envoy Tracing](https://www.envoyproxy.io/docs/envoy/latest/intro/arch_overview/observability/tracing)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-12  
**维护者**: OpenTelemetry Go Integration Team

# Envoy 与 OTLP 完整集成指南 2025版

## 概述

Envoy 是一个高性能的云原生边缘和服务代理，广泛用于服务网格、API 网关和负载均衡。本指南详细介绍如何在 Go 1.25.1 应用中集成 Envoy 与 OpenTelemetry Protocol (OTLP)，实现自动化的分布式追踪、指标收集和可观测性。

## 目录

- [架构概述](#架构概述)
- [快速开始](#快速开始)
- [Envoy 配置与追踪](#envoy-配置与追踪)
- [Go 应用 OTLP 集成](#go-应用-otlp-集成)
- [分布式追踪配置](#分布式追踪配置)
- [服务网格可观测性](#服务网格可观测性)
- [性能优化](#性能优化)
- [生产部署](#生产部署)
- [最佳实践](#最佳实践)

## 架构概述

### Envoy 架构组件

```mermaid
graph TB
    subgraph "Kubernetes Cluster"
        subgraph "Envoy Proxy"
            subgraph "Envoy Components"
                LISTENER[Listener]
                FILTER[HTTP Filter]
                ROUTER[Router]
                CLUSTER[Cluster]
                ENDPOINT[Endpoint]
            end
        end
        
        subgraph "Go Application"
            APP[Go Application]
            OTEL[OTel Collector]
        end
        
        subgraph "Observability Stack"
            JAEGER[Jaeger]
            PROMETHEUS[Prometheus]
            GRAFANA[Grafana]
        end
    end
    
    APP --> OTEL
    OTEL --> JAEGER
    OTEL --> PROMETHEUS
    PROMETHEUS --> GRAFANA
    
    LISTENER --> FILTER
    FILTER --> ROUTER
    ROUTER --> CLUSTER
    CLUSTER --> ENDPOINT
```

### 核心特性

- **高性能代理**: 基于 C++ 的高性能代理
- **动态配置**: 支持动态配置更新
- **多协议支持**: HTTP/1.1, HTTP/2, gRPC, TCP, UDP
- **负载均衡**: 多种负载均衡算法
- **健康检查**: 自动健康检查和故障转移
- **追踪支持**: 内置分布式追踪支持

## 快速开始

### 1. 安装 Envoy

```bash
# 使用 Docker 运行 Envoy
docker run --rm -d \
  --name envoy \
  -p 9901:9901 \
  -p 10000:10000 \
  -v $(pwd)/envoy.yaml:/etc/envoy/envoy.yaml \
  envoyproxy/envoy:v1.28.0

# 验证安装
curl http://localhost:9901/server_info
```

### 2. 基础 Envoy 配置

```yaml
# envoy.yaml
static_resources:
  listeners:
  - name: listener_0
    address:
      socket_address:
        address: 0.0.0.0
        port_value: 10000
    filter_chains:
    - filters:
      - name: envoy.filters.network.http_connection_manager
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          stat_prefix: ingress_http
          route_config:
            name: local_route
            virtual_hosts:
            - name: local_service
              domains: ["*"]
              routes:
              - match:
                  prefix: "/"
                route:
                  cluster: service_cluster
          http_filters:
          - name: envoy.filters.http.router
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.filters.http.router.v3.Router
          tracing:
            provider:
              name: envoy.tracers.opentelemetry
              typed_config:
                "@type": type.googleapis.com/envoy.config.trace.v3.OpenTelemetryConfig
                grpc_service:
                  envoy_grpc:
                    cluster_name: otel_collector
                service_name: envoy-proxy
                resource_attributes:
                  - key: service.name
                    value: "envoy-proxy"
                  - key: service.version
                    value: "1.0.0"

  clusters:
  - name: service_cluster
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: service_cluster
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: 127.0.0.1
                port_value: 8080

  - name: otel_collector
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: otel_collector
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: otel-collector
                port_value: 4317

admin:
  address:
    socket_address:
      address: 0.0.0.0
      port_value: 9901
```

### 3. 部署 OTel Collector

```yaml
# otel-collector.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: default
data:
  otel-collector.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
            endpoint: 0.0.0.0:4317
          http:
            endpoint: 0.0.0.0:4318
      jaeger:
        protocols:
          grpc:
            endpoint: 0.0.0.0:14250
          thrift_http:
            endpoint: 0.0.0.0:14268
          thrift_compact:
            endpoint: 0.0.0.0:6831
          thrift_binary:
            endpoint: 0.0.0.0:6832

    processors:
      batch:
        timeout: 1s
        send_batch_size: 1024
      memory_limiter:
        limit_mib: 512
      resource:
        attributes:
          - key: service.name
            value: "envoy-mesh"
            action: upsert

    exporters:
      jaeger:
        endpoint: jaeger-collector:14250
        tls:
          insecure: true
      prometheus:
        endpoint: "0.0.0.0:8889"
        namespace: "envoy_otel"
        const_labels:
          mesh: "envoy"

    service:
      pipelines:
        traces:
          receivers: [otlp, jaeger]
          processors: [memory_limiter, resource, batch]
          exporters: [jaeger]
        metrics:
          receivers: [otlp]
          processors: [memory_limiter, resource, batch]
          exporters: [prometheus]
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: default
spec:
  replicas: 1
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
        image: otel/opentelemetry-collector-contrib:0.95.0
        args:
          - --config=/etc/otel-collector.yaml
        ports:
        - containerPort: 4317
        - containerPort: 4318
        - containerPort: 14250
        - containerPort: 14268
        - containerPort: 6831
        - containerPort: 6832
        - containerPort: 8889
        volumeMounts:
        - name: config
          mountPath: /etc/otel-collector.yaml
          subPath: otel-collector.yaml
        resources:
          requests:
            memory: "256Mi"
            cpu: "100m"
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
  namespace: default
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
  - name: jaeger-grpc
    port: 14250
    targetPort: 14250
  - name: jaeger-http
    port: 14268
    targetPort: 14268
  - name: prometheus
    port: 8889
    targetPort: 8889
```

## Envoy 配置与追踪

### 1. 高级 Envoy 配置

```yaml
# envoy-advanced.yaml
static_resources:
  listeners:
  - name: listener_0
    address:
      socket_address:
        address: 0.0.0.0
        port_value: 10000
    filter_chains:
    - filters:
      - name: envoy.filters.network.http_connection_manager
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          stat_prefix: ingress_http
          route_config:
            name: local_route
            virtual_hosts:
            - name: local_service
              domains: ["*"]
              routes:
              - match:
                  prefix: "/api/users"
                route:
                  cluster: user_service
                  timeout: 5s
                  retry_policy:
                    retry_on: "5xx,reset,connect-failure,refused-stream"
                    num_retries: 3
                    per_try_timeout: 2s
              - match:
                  prefix: "/api/orders"
                route:
                  cluster: order_service
                  timeout: 10s
                  retry_policy:
                    retry_on: "5xx,reset,connect-failure,refused-stream"
                    num_retries: 2
                    per_try_timeout: 3s
              - match:
                  prefix: "/"
                route:
                  cluster: default_service
          http_filters:
          - name: envoy.filters.http.cors
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.filters.http.cors.v3.Cors
          - name: envoy.filters.http.router
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.filters.http.router.v3.Router
          tracing:
            provider:
              name: envoy.tracers.opentelemetry
              typed_config:
                "@type": type.googleapis.com/envoy.config.trace.v3.OpenTelemetryConfig
                grpc_service:
                  envoy_grpc:
                    cluster_name: otel_collector
                service_name: envoy-proxy
                resource_attributes:
                  - key: service.name
                    value: "envoy-proxy"
                  - key: service.version
                    value: "1.0.0"
                  - key: deployment.environment
                    value: "production"
            random_sampling:
              numerator: 100
              denominator: 1000
            custom_tags:
              - tag: "user_id"
                request_header:
                  name: "x-user-id"
                  default_value: "unknown"
              - tag: "request_id"
                request_header:
                  name: "x-request-id"
                  default_value: "unknown"
              - tag: "service_name"
                literal:
                  value: "envoy-proxy"

  clusters:
  - name: user_service
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: user_service
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: user-service
                port_value: 8080
    health_checks:
    - timeout: 1s
      interval: 10s
      unhealthy_threshold: 3
      healthy_threshold: 2
      http_health_check:
        path: "/health"
        expected_statuses:
        - start: 200
          end: 299

  - name: order_service
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: order_service
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: order-service
                port_value: 8080
    health_checks:
    - timeout: 1s
      interval: 10s
      unhealthy_threshold: 3
      healthy_threshold: 2
      http_health_check:
        path: "/health"
        expected_statuses:
        - start: 200
          end: 299

  - name: default_service
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: default_service
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: 127.0.0.1
                port_value: 8080

  - name: otel_collector
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: otel_collector
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: otel-collector
                port_value: 4317

admin:
  address:
    socket_address:
      address: 0.0.0.0
      port_value: 9901
```

### 2. gRPC 服务配置

```yaml
# envoy-grpc.yaml
static_resources:
  listeners:
  - name: grpc_listener
    address:
      socket_address:
        address: 0.0.0.0
        port_value: 9090
    filter_chains:
    - filters:
      - name: envoy.filters.network.http_connection_manager
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          stat_prefix: grpc_http
          http2_protocol_options: {}
          route_config:
            name: grpc_route
            virtual_hosts:
            - name: grpc_service
              domains: ["*"]
              routes:
              - match:
                  prefix: "/"
                route:
                  cluster: grpc_service
                  timeout: 30s
                  retry_policy:
                    retry_on: "5xx,reset,connect-failure,refused-stream"
                    num_retries: 3
                    per_try_timeout: 10s
          http_filters:
          - name: envoy.filters.http.router
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.filters.http.router.v3.Router
          tracing:
            provider:
              name: envoy.tracers.opentelemetry
              typed_config:
                "@type": type.googleapis.com/envoy.config.trace.v3.OpenTelemetryConfig
                grpc_service:
                  envoy_grpc:
                    cluster_name: otel_collector
                service_name: envoy-grpc-proxy
                resource_attributes:
                  - key: service.name
                    value: "envoy-grpc-proxy"
                  - key: service.version
                    value: "1.0.0"
                  - key: protocol
                    value: "grpc"

  clusters:
  - name: grpc_service
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: grpc_service
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: grpc-service
                port_value: 9090
    health_checks:
    - timeout: 1s
      interval: 10s
      unhealthy_threshold: 3
      healthy_threshold: 2
      grpc_health_check:
        service_name: ""

  - name: otel_collector
    connect_timeout: 0.25s
    type: LOGICAL_DNS
    dns_lookup_family: V4_ONLY
    lb_policy: ROUND_ROBIN
    load_assignment:
      cluster_name: otel_collector
      endpoints:
      - lb_endpoints:
        - endpoint:
            address:
              socket_address:
                address: otel-collector
                port_value: 4317

admin:
  address:
    socket_address:
      address: 0.0.0.0
      port_value: 9901
```

## Go 应用 OTLP 集成

### 1. 基础 Go 应用示例

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
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func main() {
    // 初始化 OpenTelemetry
    ctx := context.Background()
    tp, err := initTracer(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(ctx)

    // 设置 HTTP 路由
    http.HandleFunc("/", homeHandler)
    http.HandleFunc("/api/users", usersHandler)
    http.HandleFunc("/api/orders", ordersHandler)
    http.HandleFunc("/health", healthHandler)

    log.Println("Server starting on :8080")
    log.Fatal(http.ListenAndServe(":8080", nil))
}

func initTracer(ctx context.Context) (*sdktrace.TracerProvider, error) {
    // 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("go-envoy-app"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.1)),
    )

    // 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return tp, nil
}

func homeHandler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("go-envoy-app")
    
    ctx, span := tracer.Start(ctx, "home-handler")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.url", r.URL.String()),
        attribute.String("http.user_agent", r.UserAgent()),
        attribute.String("proxy", "envoy"),
    )

    // 模拟业务逻辑
    time.Sleep(10 * time.Millisecond)
    
    w.WriteHeader(http.StatusOK)
    fmt.Fprintf(w, "Hello from Go app with Envoy!")
}

func usersHandler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("go-envoy-app")
    
    ctx, span := tracer.Start(ctx, "users-handler")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.url", r.URL.String()),
        attribute.String("service", "user-service"),
    )

    // 调用其他服务
    if err := callUserService(ctx); err != nil {
        span.RecordError(err)
        http.Error(w, "Internal Server Error", http.StatusInternalServerError)
        return
    }

    w.WriteHeader(http.StatusOK)
    fmt.Fprintf(w, `{"users": [{"id": 1, "name": "Alice"}, {"id": 2, "name": "Bob"}]}`)
}

func ordersHandler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("go-envoy-app")
    
    ctx, span := tracer.Start(ctx, "orders-handler")
    defer span.End()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.url", r.URL.String()),
        attribute.String("service", "order-service"),
    )

    // 调用订单服务
    if err := callOrderService(ctx); err != nil {
        span.RecordError(err)
        http.Error(w, "Internal Server Error", http.StatusInternalServerError)
        return
    }

    w.WriteHeader(http.StatusOK)
    fmt.Fprintf(w, `{"orders": [{"id": 1, "amount": 100.0}, {"id": 2, "amount": 200.0}]}`)
}

func healthHandler(w http.ResponseWriter, r *http.Request) {
    w.WriteHeader(http.StatusOK)
    fmt.Fprintf(w, `{"status": "healthy", "timestamp": "%s"}`, time.Now().Format(time.RFC3339))
}

func callUserService(ctx context.Context) error {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "call-user-service")
    defer span.End()

    span.SetAttributes(
        attribute.String("service.name", "user-service"),
        attribute.String("service.version", "1.0.0"),
        attribute.String("proxy", "envoy"),
    )

    // 模拟 HTTP 调用
    client := &http.Client{
        Timeout: 5 * time.Second,
    }

    req, err := http.NewRequestWithContext(ctx, "GET", "http://user-service:8080/api/users", nil)
    if err != nil {
        return err
    }

    resp, err := client.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()

    span.SetAttributes(
        attribute.Int("http.status_code", resp.StatusCode),
    )

    return nil
}

func callOrderService(ctx context.Context) error {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "call-order-service")
    defer span.End()

    span.SetAttributes(
        attribute.String("service.name", "order-service"),
        attribute.String("service.version", "1.0.0"),
        attribute.String("proxy", "envoy"),
    )

    // 模拟 HTTP 调用
    client := &http.Client{
        Timeout: 5 * time.Second,
    }

    req, err := http.NewRequestWithContext(ctx, "GET", "http://order-service:8080/api/orders", nil)
    if err != nil {
        return err
    }

    resp, err := client.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()

    span.SetAttributes(
        attribute.Int("http.status_code", resp.StatusCode),
    )

    return nil
}
```

### 2. 高级中间件集成

```go
// middleware.go
package main

import (
    "context"
    "fmt"
    "net/http"
    "strconv"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

type EnvoyTracingMiddleware struct {
    tracer   trace.Tracer
    meter    metric.Meter
    requests metric.Int64Counter
    duration metric.Float64Histogram
    errors   metric.Int64Counter
}

func NewEnvoyTracingMiddleware() *EnvoyTracingMiddleware {
    tracer := otel.Tracer("go-envoy-app")
    meter := otel.Meter("go-envoy-app")

    requests, _ := meter.Int64Counter(
        "envoy_http_requests_total",
        metric.WithDescription("Total number of HTTP requests through Envoy"),
    )

    duration, _ := meter.Float64Histogram(
        "envoy_http_request_duration_seconds",
        metric.WithDescription("HTTP request duration in seconds through Envoy"),
    )

    errors, _ := meter.Int64Counter(
        "envoy_http_errors_total",
        metric.WithDescription("Total number of HTTP errors through Envoy"),
    )

    return &EnvoyTracingMiddleware{
        tracer:   tracer,
        meter:    meter,
        requests: requests,
        duration: duration,
        errors:   errors,
    }
}

func (etm *EnvoyTracingMiddleware) Handler(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        ctx := r.Context()

        // 创建 span
        ctx, span := etm.tracer.Start(ctx, "envoy-http-request",
            trace.WithAttributes(
                semconv.HTTPMethod(r.Method),
                semconv.HTTPURL(r.URL.String()),
                semconv.HTTPUserAgent(r.UserAgent()),
                semconv.HTTPRequestContentLength(r.ContentLength),
                attribute.String("proxy", "envoy"),
                attribute.String("mesh", "envoy"),
            ),
        )
        defer span.End()

        // 包装 ResponseWriter 以捕获状态码
        ww := &responseWriter{ResponseWriter: w, statusCode: http.StatusOK}

        // 调用下一个处理器
        next.ServeHTTP(ww, r.WithContext(ctx))

        // 记录指标
        duration := time.Since(start).Seconds()
        statusCode := ww.statusCode

        etm.requests.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("method", r.Method),
                attribute.String("path", r.URL.Path),
                attribute.Int("status_code", statusCode),
                attribute.String("proxy", "envoy"),
                attribute.String("mesh", "envoy"),
            ),
        )

        etm.duration.Record(ctx, duration,
            metric.WithAttributes(
                attribute.String("method", r.Method),
                attribute.String("path", r.URL.Path),
                attribute.Int("status_code", statusCode),
                attribute.String("proxy", "envoy"),
                attribute.String("mesh", "envoy"),
            ),
        )

        // 记录错误
        if statusCode >= 400 {
            etm.errors.Add(ctx, 1,
                metric.WithAttributes(
                    attribute.String("method", r.Method),
                    attribute.String("path", r.URL.Path),
                    attribute.Int("status_code", statusCode),
                    attribute.String("proxy", "envoy"),
                    attribute.String("mesh", "envoy"),
                ),
            )
            span.RecordError(fmt.Errorf("HTTP %d", statusCode))
        }

        // 更新 span 属性
        span.SetAttributes(
            semconv.HTTPStatusCode(statusCode),
            semconv.HTTPResponseContentLength(ww.contentLength),
            attribute.Float64("http.request.duration", duration),
            attribute.String("proxy", "envoy"),
            attribute.String("mesh", "envoy"),
        )
    })
}

type responseWriter struct {
    http.ResponseWriter
    statusCode    int
    contentLength int64
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    n, err := rw.ResponseWriter.Write(b)
    rw.contentLength += int64(n)
    return n, err
}
```

### 3. gRPC 服务集成

```go
// grpc_server.go
package main

import (
    "context"
    "log"
    "net"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/codes"
    "google.golang.org/grpc/status"
)

type UserService struct {
    UnimplementedUserServiceServer
    tracer trace.Tracer
}

func NewUserService() *UserService {
    return &UserService{
        tracer: otel.Tracer("user-service"),
    }
}

func (s *UserService) GetUser(ctx context.Context, req *GetUserRequest) (*GetUserResponse, error) {
    ctx, span := s.tracer.Start(ctx, "GetUser")
    defer span.End()

    span.SetAttributes(
        attribute.String("user.id", req.Id),
        attribute.String("service.name", "user-service"),
        attribute.String("proxy", "envoy"),
        attribute.String("mesh", "envoy"),
    )

    // 模拟数据库查询
    user, err := s.findUser(ctx, req.Id)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, status.Errorf(codes.NotFound, "User not found: %v", err)
    }

    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )

    return &GetUserResponse{
        Id:    user.Id,
        Name:  user.Name,
        Email: user.Email,
    }, nil
}

func (s *UserService) findUser(ctx context.Context, id string) (*User, error) {
    ctx, span := s.tracer.Start(ctx, "findUser")
    defer span.End()

    span.SetAttributes(
        attribute.String("db.operation", "select"),
        attribute.String("db.table", "users"),
        attribute.String("proxy", "envoy"),
        attribute.String("mesh", "envoy"),
    )

    // 模拟数据库查询
    time.Sleep(10 * time.Millisecond)

    return &User{
        Id:    id,
        Name:  "Alice",
        Email: "alice@example.com",
    }, nil
}

func main() {
    lis, err := net.Listen("tcp", ":9090")
    if err != nil {
        log.Fatalf("Failed to listen: %v", err)
    }

    s := grpc.NewServer()
    RegisterUserServiceServer(s, NewUserService())

    log.Println("gRPC server starting on :9090")
    if err := s.Serve(lis); err != nil {
        log.Fatalf("Failed to serve: %v", err)
    }
}
```

## 分布式追踪配置

### 1. Envoy 追踪配置

```yaml
# envoy-tracing-config.yaml
static_resources:
  listeners:
  - name: listener_0
    address:
      socket_address:
        address: 0.0.0.0
        port_value: 10000
    filter_chains:
    - filters:
      - name: envoy.filters.network.http_connection_manager
        typed_config:
          "@type": type.googleapis.com/envoy.extensions.filters.network.http_connection_manager.v3.HttpConnectionManager
          stat_prefix: ingress_http
          route_config:
            name: local_route
            virtual_hosts:
            - name: local_service
              domains: ["*"]
              routes:
              - match:
                  prefix: "/"
                route:
                  cluster: service_cluster
          http_filters:
          - name: envoy.filters.http.router
            typed_config:
              "@type": type.googleapis.com/envoy.extensions.filters.http.router.v3.Router
          tracing:
            provider:
              name: envoy.tracers.opentelemetry
              typed_config:
                "@type": type.googleapis.com/envoy.config.trace.v3.OpenTelemetryConfig
                grpc_service:
                  envoy_grpc:
                    cluster_name: otel_collector
                service_name: envoy-proxy
                resource_attributes:
                  - key: service.name
                    value: "envoy-proxy"
                  - key: service.version
                    value: "1.0.0"
                  - key: deployment.environment
                    value: "production"
                  - key: mesh.name
                    value: "envoy"
            random_sampling:
              numerator: 100
              denominator: 1000
            custom_tags:
              - tag: "user_id"
                request_header:
                  name: "x-user-id"
                  default_value: "unknown"
              - tag: "request_id"
                request_header:
                  name: "x-request-id"
                  default_value: "unknown"
              - tag: "service_name"
                literal:
                  value: "envoy-proxy"
              - tag: "mesh"
                literal:
                  value: "envoy"
```

### 2. 服务级别追踪配置

```yaml
# service-tracing-config.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: service-tracing-config
  namespace: default
data:
  tracing.yaml: |
    tracing:
      enabled: true
      collector:
        endpoint: otel-collector:4317
        insecure: true
      sampling:
        ratio: 0.1
        policy: probabilistic
      attributes:
        service.name: "go-envoy-app"
        service.version: "1.0.0"
        deployment.environment: "production"
        mesh.name: "envoy"
        proxy.name: "envoy"
```

### 3. 追踪策略配置

```yaml
# tracing-policy.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: envoy-tracing-policy
  namespace: default
data:
  tracing-policy.yaml: |
    tracing:
      policies:
        - match:
            path: "/api/*"
          sampling:
            ratio: 0.1
            policy: probabilistic
        - match:
            service: "user-service"
          sampling:
            ratio: 0.2
            policy: probabilistic
        - match:
            service: "order-service"
          sampling:
            ratio: 0.15
            policy: probabilistic
```

## 服务网格可观测性

### 1. Envoy 指标集成

```go
// metrics.go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

type EnvoyMetricsCollector struct {
    meter              metric.Meter
    requestCounter     metric.Int64Counter
    requestDuration    metric.Float64Histogram
    activeConnections  metric.Int64UpDownCounter
    errorCounter       metric.Int64Counter
    upstreamLatency   metric.Float64Histogram
    downstreamLatency  metric.Float64Histogram
}

func NewEnvoyMetricsCollector() *EnvoyMetricsCollector {
    meter := otel.Meter("go-envoy-app")

    requestCounter, _ := meter.Int64Counter(
        "envoy_http_requests_total",
        metric.WithDescription("Total number of HTTP requests through Envoy"),
    )

    requestDuration, _ := meter.Float64Histogram(
        "envoy_http_request_duration_seconds",
        metric.WithDescription("HTTP request duration in seconds through Envoy"),
    )

    activeConnections, _ := meter.Int64UpDownCounter(
        "envoy_active_connections",
        metric.WithDescription("Number of active connections through Envoy"),
    )

    errorCounter, _ := meter.Int64Counter(
        "envoy_errors_total",
        metric.WithDescription("Total number of errors through Envoy"),
    )

    upstreamLatency, _ := meter.Float64Histogram(
        "envoy_upstream_latency_seconds",
        metric.WithDescription("Upstream latency in seconds"),
    )

    downstreamLatency, _ := meter.Float64Histogram(
        "envoy_downstream_latency_seconds",
        metric.WithDescription("Downstream latency in seconds"),
    )

    return &EnvoyMetricsCollector{
        meter:             meter,
        requestCounter:    requestCounter,
        requestDuration:   requestDuration,
        activeConnections: activeConnections,
        errorCounter:      errorCounter,
        upstreamLatency:   upstreamLatency,
        downstreamLatency: downstreamLatency,
    }
}

func (emc *EnvoyMetricsCollector) RecordRequest(ctx context.Context, method, path string, statusCode int, duration time.Duration) {
    emc.requestCounter.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("method", method),
            attribute.String("path", path),
            attribute.Int("status_code", statusCode),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )

    emc.requestDuration.Record(ctx, duration.Seconds(),
        metric.WithAttributes(
            attribute.String("method", method),
            attribute.String("path", path),
            attribute.Int("status_code", statusCode),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
}

func (emc *EnvoyMetricsCollector) RecordError(ctx context.Context, errorType string) {
    emc.errorCounter.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("error_type", errorType),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
}

func (emc *EnvoyMetricsCollector) RecordUpstreamLatency(ctx context.Context, service string, latency time.Duration) {
    emc.upstreamLatency.Record(ctx, latency.Seconds(),
        metric.WithAttributes(
            attribute.String("service", service),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
}

func (emc *EnvoyMetricsCollector) RecordDownstreamLatency(ctx context.Context, latency time.Duration) {
    emc.downstreamLatency.Record(ctx, latency.Seconds(),
        metric.WithAttributes(
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
}

func (emc *EnvoyMetricsCollector) IncrementConnections(ctx context.Context) {
    emc.activeConnections.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
}

func (emc *EnvoyMetricsCollector) DecrementConnections(ctx context.Context) {
    emc.activeConnections.Add(ctx, -1,
        metric.WithAttributes(
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        ),
    )
}
```

### 2. Grafana 仪表板配置

```json
{
  "dashboard": {
    "title": "Envoy + OTLP Go App Dashboard",
    "panels": [
      {
        "title": "Request Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(envoy_http_requests_total[5m])",
            "legendFormat": "{{method}} {{path}}"
          }
        ]
      },
      {
        "title": "Request Duration",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(envoy_http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          },
          {
            "expr": "histogram_quantile(0.50, rate(envoy_http_request_duration_seconds_bucket[5m]))",
            "legendFormat": "50th percentile"
          }
        ]
      },
      {
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(envoy_errors_total[5m])",
            "legendFormat": "{{error_type}}"
          }
        ]
      },
      {
        "title": "Active Connections",
        "type": "graph",
        "targets": [
          {
            "expr": "envoy_active_connections",
            "legendFormat": "Active Connections"
          }
        ]
      },
      {
        "title": "Upstream Latency",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(envoy_upstream_latency_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          }
        ]
      },
      {
        "title": "Downstream Latency",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(envoy_downstream_latency_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          }
        ]
      }
    ]
  }
}
```

### 3. Jaeger 追踪查询

```go
// jaeger-query.go
package main

import (
    "context"
    "fmt"
    "time"

    "github.com/jaegertracing/jaeger-client-go"
    "github.com/jaegertracing/jaeger-client-go/config"
)

func initJaegerClient() (jaeger.Tracer, error) {
    cfg := config.Configuration{
        ServiceName: "go-envoy-app",
        Sampler: &config.SamplerConfig{
            Type:  "probabilistic",
            Param: 0.1,
        },
        Reporter: &config.ReporterConfig{
            LogSpans:            true,
            BufferFlushInterval: 1 * time.Second,
            LocalAgentHostPort:  "jaeger-agent:6831",
        },
    }

    tracer, _, err := cfg.NewTracer()
    if err != nil {
        return nil, err
    }

    return tracer, nil
}

func queryTraces(ctx context.Context, serviceName string, startTime, endTime time.Time) error {
    // 这里可以使用 Jaeger Query API 查询追踪数据
    // 实际实现需要调用 Jaeger Query Service
    
    fmt.Printf("Querying traces for service: %s\n", serviceName)
    fmt.Printf("Time range: %s to %s\n", startTime.Format(time.RFC3339), endTime.Format(time.RFC3339))
    
    return nil
}
```

## 性能优化

### 1. 追踪采样优化

```go
// sampling.go
package main

import (
    "context"
    "math/rand"
    "time"

    "go.opentelemetry.io/otel/trace"
)

type EnvoyAdaptiveSampler struct {
    baseRatio    float64
    maxRatio     float64
    minRatio     float64
    currentRatio float64
    lastUpdate   time.Time
    updateInterval time.Duration
}

func NewEnvoyAdaptiveSampler(baseRatio, maxRatio, minRatio float64) *EnvoyAdaptiveSampler {
    return &EnvoyAdaptiveSampler{
        baseRatio:      baseRatio,
        maxRatio:       maxRatio,
        minRatio:       minRatio,
        currentRatio:   baseRatio,
        lastUpdate:     time.Now(),
        updateInterval: 1 * time.Minute,
    }
}

func (eas *EnvoyAdaptiveSampler) ShouldSample(ctx context.Context, traceID trace.TraceID) bool {
    // 检查是否需要更新采样率
    if time.Since(eas.lastUpdate) > eas.updateInterval {
        eas.updateSamplingRatio()
        eas.lastUpdate = time.Now()
    }

    // 基于当前采样率决定是否采样
    return rand.Float64() < eas.currentRatio
}

func (eas *EnvoyAdaptiveSampler) updateSamplingRatio() {
    // 这里可以根据系统负载、错误率等因素动态调整采样率
    // 示例：根据 CPU 使用率调整
    cpuUsage := getCPUUsage()
    
    if cpuUsage > 80 {
        eas.currentRatio = eas.minRatio
    } else if cpuUsage < 20 {
        eas.currentRatio = eas.maxRatio
    } else {
        eas.currentRatio = eas.baseRatio
    }
}

func getCPUUsage() float64 {
    // 实际实现需要读取系统 CPU 使用率
    return 50.0 // 示例值
}
```

### 2. 批量导出优化

```go
// batch_exporter.go
package main

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

type EnvoyOptimizedBatchExporter struct {
    exporter    sdktrace.SpanExporter
    batchSize   int
    timeout     time.Duration
    mutex       sync.Mutex
    spans       []sdktrace.ReadOnlySpan
    lastFlush   time.Time
}

func NewEnvoyOptimizedBatchExporter(endpoint string, batchSize int, timeout time.Duration) (*EnvoyOptimizedBatchExporter, error) {
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint(endpoint),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    return &EnvoyOptimizedBatchExporter{
        exporter:  exporter,
        batchSize: batchSize,
        timeout:   timeout,
        lastFlush: time.Now(),
    }, nil
}

func (eobe *EnvoyOptimizedBatchExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
    eobe.mutex.Lock()
    defer eobe.mutex.Unlock()

    eobe.spans = append(eobe.spans, spans...)

    // 检查是否需要刷新
    if len(eobe.spans) >= eobe.batchSize || time.Since(eobe.lastFlush) > eobe.timeout {
        return eobe.flush(ctx)
    }

    return nil
}

func (eobe *EnvoyOptimizedBatchExporter) flush(ctx context.Context) error {
    if len(eobe.spans) == 0 {
        return nil
    }

    err := eobe.exporter.ExportSpans(ctx, eobe.spans)
    if err != nil {
        return err
    }

    eobe.spans = eobe.spans[:0]
    eobe.lastFlush = time.Now()
    return nil
}

func (eobe *EnvoyOptimizedBatchExporter) Shutdown(ctx context.Context) error {
    eobe.mutex.Lock()
    defer eobe.mutex.Unlock()

    return eobe.flush(ctx)
}
```

### 3. 资源限制配置

```yaml
# envoy-resource-limits.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: envoy-resource-limits
  namespace: default
data:
  limits.yaml: |
    envoy:
      resources:
        requests:
          cpu: 100m
          memory: 128Mi
        limits:
          cpu: 1000m
          memory: 512Mi
      connection_limits:
        max_connections: 10000
        max_pending_requests: 1000
        max_requests_per_connection: 100
      timeout_limits:
        connect_timeout: 250ms
        request_timeout: 30s
        idle_timeout: 300s
```

## 生产部署

### 1. Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  # Envoy Proxy
  envoy:
    image: envoyproxy/envoy:v1.28.0
    ports:
      - "9901:9901"
      - "10000:10000"
    volumes:
      - ./envoy.yaml:/etc/envoy/envoy.yaml
    command: ["/usr/local/bin/envoy", "-c", "/etc/envoy/envoy.yaml"]
    networks:
      - envoy-mesh

  # OTel Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.95.0
    ports:
      - "4317:4317"
      - "4318:4318"
      - "14250:14250"
      - "14268:14268"
      - "8889:8889"
    volumes:
      - ./otel-collector.yaml:/etc/otel-collector.yaml
    command: ["--config=/etc/otel-collector.yaml"]
    networks:
      - envoy-mesh

  # Go 应用
  go-app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - OTEL_SERVICE_NAME=go-envoy-app
      - OTEL_SERVICE_VERSION=1.0.0
    depends_on:
      - otel-collector
    networks:
      - envoy-mesh

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:1.50
    ports:
      - "16686:16686"
      - "14250:14250"
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - envoy-mesh

  # Prometheus
  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
    networks:
      - envoy-mesh

  # Grafana
  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - ./grafana-dashboards:/var/lib/grafana/dashboards
    networks:
      - envoy-mesh

networks:
  envoy-mesh:
    driver: bridge
```

### 2. Kubernetes 部署

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: go-envoy-app
  namespace: default
  labels:
    app: go-envoy-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: go-envoy-app
  template:
    metadata:
      labels:
        app: go-envoy-app
    spec:
      containers:
      - name: go-app
        image: go-envoy-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        - name: OTEL_SERVICE_NAME
          value: "go-envoy-app"
        - name: OTEL_SERVICE_VERSION
          value: "1.0.0"
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 500m
            memory: 512Mi
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: go-envoy-app
  namespace: default
  labels:
    app: go-envoy-app
spec:
  selector:
    app: go-envoy-app
  ports:
  - port: 8080
    targetPort: 8080
    name: http
  type: ClusterIP
---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: envoy-proxy
  namespace: default
  labels:
    app: envoy-proxy
spec:
  replicas: 2
  selector:
    matchLabels:
      app: envoy-proxy
  template:
    metadata:
      labels:
        app: envoy-proxy
    spec:
      containers:
      - name: envoy
        image: envoyproxy/envoy:v1.28.0
        ports:
        - containerPort: 9901
        - containerPort: 10000
        command: ["/usr/local/bin/envoy", "-c", "/etc/envoy/envoy.yaml"]
        volumeMounts:
        - name: config
          mountPath: /etc/envoy/envoy.yaml
          subPath: envoy.yaml
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 1000m
            memory: 512Mi
      volumes:
      - name: config
        configMap:
          name: envoy-config
---
apiVersion: v1
kind: Service
metadata:
  name: envoy-proxy
  namespace: default
  labels:
    app: envoy-proxy
spec:
  selector:
    app: envoy-proxy
  ports:
  - port: 10000
    targetPort: 10000
    name: http
  - port: 9901
    targetPort: 9901
    name: admin
  type: ClusterIP
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: go-envoy-app-hpa
  namespace: default
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: go-envoy-app
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

### 3. 监控和告警配置

```yaml
# monitoring.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: envoy-monitoring-config
  namespace: default
data:
  prometheus.yml: |
    global:
      scrape_interval: 15s
      evaluation_interval: 15s

    rule_files:
      - "envoy-rules.yml"

    alerting:
      alertmanagers:
        - static_configs:
            - targets:
              - alertmanager:9093

    scrape_configs:
      - job_name: 'envoy-proxy'
        kubernetes_sd_configs:
          - role: endpoints
            namespaces:
              names:
                - default
        relabel_configs:
          - source_labels: [__meta_kubernetes_service_annotation_prometheus_io_scrape]
            action: keep
            regex: true
          - source_labels: [__meta_kubernetes_service_annotation_prometheus_io_path]
            action: replace
            target_label: __metrics_path__
            regex: (.+)
          - source_labels: [__address__, __meta_kubernetes_service_annotation_prometheus_io_port]
            action: replace
            regex: ([^:]+)(?::\d+)?;(\d+)
            replacement: $1:$2
            target_label: __address__
          - action: labelmap
            regex: __meta_kubernetes_service_label_(.+)
          - source_labels: [__meta_kubernetes_namespace]
            action: replace
            target_label: kubernetes_namespace
          - source_labels: [__meta_kubernetes_service_name]
            action: replace
            target_label: kubernetes_name

      - job_name: 'otel-collector'
        static_configs:
          - targets: ['otel-collector:8889']

  envoy-rules.yml: |
    groups:
    - name: envoy.rules
      rules:
      - alert: HighErrorRate
        expr: rate(envoy_http_requests_total{status_code=~"5.."}[5m]) > 0.1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }} errors per second"

      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(envoy_http_request_duration_seconds_bucket[5m])) > 1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High latency detected"
          description: "95th percentile latency is {{ $value }} seconds"

      - alert: LowThroughput
        expr: rate(envoy_http_requests_total[5m]) < 10
        for: 10m
        labels:
          severity: info
        annotations:
          summary: "Low throughput detected"
          description: "Request rate is {{ $value }} requests per second"

      - alert: HighUpstreamLatency
        expr: histogram_quantile(0.95, rate(envoy_upstream_latency_seconds_bucket[5m])) > 2
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High upstream latency detected"
          description: "95th percentile upstream latency is {{ $value }} seconds"
```

## 最佳实践

### 1. 追踪最佳实践

```go
// best_practices.go
package main

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// 1. 使用有意义的 span 名称
func meaningfulSpanName(ctx context.Context) {
    tracer := otel.Tracer("go-envoy-app")
    
    // 好的做法：描述性的 span 名称
    ctx, span := tracer.Start(ctx, "user-service.GetUser")
    defer span.End()
    
    // 避免：模糊的 span 名称
    // ctx, span := tracer.Start(ctx, "doSomething")
}

// 2. 添加有意义的属性
func addMeaningfulAttributes(ctx context.Context) {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "database.QueryUser")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("db.operation", "SELECT"),
        attribute.String("db.table", "users"),
        attribute.String("db.query", "SELECT * FROM users WHERE id = ?"),
        attribute.String("user.id", "123"),
        attribute.String("service.name", "user-service"),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
}

// 3. 正确处理错误
func handleErrorsProperly(ctx context.Context) error {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "external-api.Call")
    defer span.End()
    
    err := callExternalAPI()
    if err != nil {
        // 记录错误并设置状态
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        
        // 添加错误相关的属性
        span.SetAttributes(
            attribute.String("error.type", "external_api_error"),
            attribute.Bool("error.retryable", true),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        )
        
        return err
    }
    
    return nil
}

// 4. 使用适当的采样策略
func useAppropriateSampling(ctx context.Context) {
    tracer := otel.Tracer("go-envoy-app")
    
    // 对于关键业务操作，使用更高的采样率
    ctx, span := tracer.Start(ctx, "payment.ProcessPayment")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("payment.amount", "100.00"),
        attribute.String("payment.currency", "USD"),
        attribute.String("payment.method", "credit_card"),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
}

// 5. 避免过度追踪
func avoidOverTracing(ctx context.Context) {
    tracer := otel.Tracer("go-envoy-app")
    
    // 好的做法：追踪有意义的操作
    ctx, span := tracer.Start(ctx, "user-service.ValidateUser")
    defer span.End()
    
    // 避免：追踪每个函数调用
    // ctx, span := tracer.Start(ctx, "helper.FormatString")
    // defer span.End()
}

func callExternalAPI() error {
    // 模拟外部 API 调用
    time.Sleep(10 * time.Millisecond)
    return fmt.Errorf("external API timeout")
}
```

### 2. 性能优化最佳实践

```go
// performance_best_practices.go
package main

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 1. 使用连接池
type EnvoyConnectionPool struct {
    tracer    trace.Tracer
    pool      chan *Connection
    maxSize   int
    mutex     sync.RWMutex
}

func NewEnvoyConnectionPool(maxSize int) *EnvoyConnectionPool {
    return &EnvoyConnectionPool{
        tracer:  otel.Tracer("go-envoy-app"),
        pool:    make(chan *Connection, maxSize),
        maxSize: maxSize,
    }
}

func (ecp *EnvoyConnectionPool) GetConnection(ctx context.Context) (*Connection, error) {
    ctx, span := ecp.tracer.Start(ctx, "envoy-connection-pool.GetConnection")
    defer span.End()
    
    select {
    case conn := <-ecp.pool:
        span.SetAttributes(
            attribute.String("pool.action", "reuse"),
            attribute.Int("pool.size", len(ecp.pool)),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        )
        return conn, nil
    case <-time.After(5 * time.Second):
        span.SetAttributes(
            attribute.String("pool.action", "timeout"),
            attribute.Int("pool.size", len(ecp.pool)),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        )
        return nil, fmt.Errorf("connection pool timeout")
    }
}

// 2. 实现缓存策略
type EnvoyCacheManager struct {
    tracer trace.Tracer
    cache  map[string]interface{}
    mutex  sync.RWMutex
}

func NewEnvoyCacheManager() *EnvoyCacheManager {
    return &EnvoyCacheManager{
        tracer: otel.Tracer("go-envoy-app"),
        cache:  make(map[string]interface{}),
    }
}

func (ecm *EnvoyCacheManager) Get(ctx context.Context, key string) (interface{}, bool) {
    ctx, span := ecm.tracer.Start(ctx, "envoy-cache.Get")
    defer span.End()
    
    ecm.mutex.RLock()
    defer ecm.mutex.RUnlock()
    
    value, exists := ecm.cache[key]
    span.SetAttributes(
        attribute.String("cache.key", key),
        attribute.Bool("cache.hit", exists),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
    
    return value, exists
}

// 3. 实现重试机制
type EnvoyRetryConfig struct {
    MaxRetries int
    BaseDelay  time.Duration
    MaxDelay   time.Duration
}

func (erc *EnvoyRetryConfig) ExecuteWithRetry(ctx context.Context, operation func() error) error {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "envoy-retry.ExecuteWithRetry")
    defer span.End()
    
    var lastErr error
    delay := erc.BaseDelay
    
    for attempt := 0; attempt <= erc.MaxRetries; attempt++ {
        if attempt > 0 {
            time.Sleep(delay)
            delay = time.Duration(float64(delay) * 1.5)
            if delay > erc.MaxDelay {
                delay = erc.MaxDelay
            }
        }
        
        err := operation()
        if err == nil {
            span.SetAttributes(
                attribute.Int("retry.attempts", attempt),
                attribute.Bool("retry.success", true),
                attribute.String("mesh", "envoy"),
                attribute.String("proxy", "envoy"),
            )
            return nil
        }
        
        lastErr = err
        span.SetAttributes(
            attribute.Int("retry.attempt", attempt),
            attribute.String("retry.error", err.Error()),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        )
    }
    
    span.SetAttributes(
        attribute.Int("retry.attempts", erc.MaxRetries),
        attribute.Bool("retry.success", false),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
    
    return lastErr
}

// 4. 实现熔断器
type EnvoyCircuitBreaker struct {
    tracer        trace.Tracer
    failureCount  int
    successCount   int
    threshold      int
    timeout        time.Duration
    lastFailure   time.Time
    state         string // "closed", "open", "half-open"
    mutex         sync.RWMutex
}

func NewEnvoyCircuitBreaker(threshold int, timeout time.Duration) *EnvoyCircuitBreaker {
    return &EnvoyCircuitBreaker{
        tracer:   otel.Tracer("go-envoy-app"),
        threshold: threshold,
        timeout:   timeout,
        state:    "closed",
    }
}

func (ecb *EnvoyCircuitBreaker) Execute(ctx context.Context, operation func() error) error {
    ctx, span := ecb.tracer.Start(ctx, "envoy-circuit-breaker.Execute")
    defer span.End()
    
    ecb.mutex.Lock()
    defer ecb.mutex.Unlock()
    
    if ecb.state == "open" {
        if time.Since(ecb.lastFailure) > ecb.timeout {
            ecb.state = "half-open"
        } else {
            span.SetAttributes(
                attribute.String("circuit-breaker.state", "open"),
                attribute.Bool("circuit-breaker.blocked", true),
                attribute.String("mesh", "envoy"),
                attribute.String("proxy", "envoy"),
            )
            return fmt.Errorf("circuit breaker is open")
        }
    }
    
    err := operation()
    if err != nil {
        ecb.failureCount++
        ecb.lastFailure = time.Now()
        
        if ecb.failureCount >= ecb.threshold {
            ecb.state = "open"
        }
        
        span.SetAttributes(
            attribute.String("circuit-breaker.state", ecb.state),
            attribute.Int("circuit-breaker.failure_count", ecb.failureCount),
            attribute.Bool("circuit-breaker.success", false),
            attribute.String("mesh", "envoy"),
            attribute.String("proxy", "envoy"),
        )
        
        return err
    }
    
    ecb.successCount++
    if ecb.state == "half-open" {
        ecb.state = "closed"
        ecb.failureCount = 0
    }
    
    span.SetAttributes(
        attribute.String("circuit-breaker.state", ecb.state),
        attribute.Int("circuit-breaker.success_count", ecb.successCount),
        attribute.Bool("circuit-breaker.success", true),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
    
    return nil
}
```

### 3. 安全最佳实践

```go
// security_best_practices.go
package main

import (
    "context"
    "crypto/tls"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 1. 安全的 HTTP 客户端配置
func createSecureHTTPClient() *http.Client {
    return &http.Client{
        Timeout: 30 * time.Second,
        Transport: &http.Transport{
            TLSClientConfig: &tls.Config{
                MinVersion: tls.VersionTLS12,
                CipherSuites: []uint16{
                    tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
                    tls.TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305,
                    tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
                },
            },
            MaxIdleConns:        100,
            MaxIdleConnsPerHost: 10,
            IdleConnTimeout:     90 * time.Second,
        },
    }
}

// 2. 敏感信息过滤
func filterSensitiveAttributes(ctx context.Context) {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "user-service.Authenticate")
    defer span.End()
    
    // 好的做法：不记录敏感信息
    span.SetAttributes(
        attribute.String("user.id", "123"),
        attribute.String("auth.method", "oauth2"),
        attribute.Bool("auth.success", true),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
    
    // 避免：记录敏感信息
    // span.SetAttributes(
    //     attribute.String("user.password", "secret123"),
    //     attribute.String("auth.token", "eyJhbGciOiJIUzI1NiIs..."),
    // )
}

// 3. 访问控制
func implementAccessControl(ctx context.Context, userID string, resource string) error {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "access-control.CheckPermission")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("user.id", userID),
        attribute.String("resource", resource),
        attribute.String("action", "read"),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
    
    // 实现访问控制逻辑
    hasPermission := checkUserPermission(userID, resource)
    
    span.SetAttributes(
        attribute.Bool("access.granted", hasPermission),
    )
    
    if !hasPermission {
        span.SetStatus(codes.Error, "access denied")
        return fmt.Errorf("access denied")
    }
    
    return nil
}

// 4. 审计日志
func auditLog(ctx context.Context, action string, userID string, resource string) {
    tracer := otel.Tracer("go-envoy-app")
    ctx, span := tracer.Start(ctx, "audit.Log")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("audit.action", action),
        attribute.String("audit.user_id", userID),
        attribute.String("audit.resource", resource),
        attribute.String("audit.timestamp", time.Now().Format(time.RFC3339)),
        attribute.String("audit.source_ip", getClientIP(ctx)),
        attribute.String("mesh", "envoy"),
        attribute.String("proxy", "envoy"),
    )
}

func checkUserPermission(userID, resource string) bool {
    // 实现权限检查逻辑
    return true
}

func getClientIP(ctx context.Context) string {
    // 从上下文获取客户端 IP
    return "192.168.1.100"
}
```

## 总结

本指南详细介绍了如何在 Go 1.25.1 应用中集成 Envoy 与 OpenTelemetry Protocol (OTLP)，实现自动化的分布式追踪、指标收集和可观测性。通过 Envoy 的高性能代理和 OTLP 的标准化协议，我们可以轻松构建高性能、可观测的微服务应用。

### 关键特性

- **高性能代理**: Envoy 基于 C++ 的高性能代理
- **动态配置**: 支持动态配置更新
- **多协议支持**: HTTP/1.1, HTTP/2, gRPC, TCP, UDP
- **负载均衡**: 多种负载均衡算法
- **健康检查**: 自动健康检查和故障转移
- **追踪支持**: 内置分布式追踪支持

### 技术栈

- **服务代理**: Envoy 1.28.0
- **追踪协议**: OpenTelemetry Protocol (OTLP)
- **后端系统**: Jaeger, Prometheus, Grafana
- **部署平台**: Kubernetes, Docker Compose
- **监控告警**: Prometheus, AlertManager

### 最佳实践1

- 使用有意义的 span 名称和属性
- 正确处理错误和状态码
- 实现适当的采样策略
- 避免过度追踪
- 确保安全性
- 优化性能

通过遵循本指南的最佳实践，您可以构建高性能、可观测、安全的微服务应用，充分利用 Envoy 和 OpenTelemetry 的强大功能。

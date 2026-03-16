# Golang 1.25.1 × OTLP 实战实现指南 (2025)

> **创建日期**: 2025-10-04  
> **难度**: ⭐⭐⭐  
> **目标**: 从理论到生产的完整实现路径

---

## 目录

- [Golang 1.25.1 × OTLP 实战实现指南 (2025)](#golang-1251--otlp-实战实现指南-2025)
  - [目录](#目录)
  - [1. 快速开始 (15 分钟)](#1-快速开始-15-分钟)
    - [1.1 环境准备](#11-环境准备)
    - [1.2 最小化示例](#12-最小化示例)
    - [1.3 启动 Collector](#13-启动-collector)
  - [2. CSP 并发模式实现](#2-csp-并发模式实现)
    - [2.1 Fan-Out/Fan-In](#21-fan-outfan-in)
    - [2.2 Pipeline 模式](#22-pipeline-模式)
    - [2.3 Worker Pool](#23-worker-pool)
  - [3. 分布式追踪实现](#3-分布式追踪实现)
    - [3.1 HTTP 服务端](#31-http-服务端)
    - [3.2 HTTP 客户端](#32-http-客户端)
    - [3.3 gRPC 集成](#33-grpc-集成)
  - [4. 性能优化实践](#4-性能优化实践)
    - [4.1 采样策略](#41-采样策略)
    - [4.2 Span 批量处理](#42-span-批量处理)
    - [4.3 资源池化](#43-资源池化)
  - [5. OTTL 实战配置](#5-ottl-实战配置)
    - [5.1 Collector 配置](#51-collector-配置)
    - [5.2 高级 OTTL 规则](#52-高级-ottl-规则)
  - [6. OPAMP Agent 实现](#6-opamp-agent-实现)
  - [7. 容器化部署](#7-容器化部署)
    - [7.1 Dockerfile](#71-dockerfile)
    - [7.2 Docker Compose](#72-docker-compose)
    - [7.3 Kubernetes 部署](#73-kubernetes-部署)
  - [8. 性能基准测试](#8-性能基准测试)
    - [8.1 基准测试代码](#81-基准测试代码)
    - [8.2 运行基准测试](#82-运行基准测试)
  - [9. 故障排查](#9-故障排查)
    - [9.1 常见问题](#91-常见问题)
      - [问题 1: Span 未导出](#问题-1-span-未导出)
      - [问题 2: 内存泄漏](#问题-2-内存泄漏)
    - [9.2 性能调优](#92-性能调优)
  - [10. 下一步学习](#10-下一步学习)
    - [10.1 深入理论](#101-深入理论)
    - [10.2 生产实践](#102-生产实践)
    - [10.3 社区资源](#103-社区资源)

## 1. 快速开始 (15 分钟)

### 1.1 环境准备

```bash
# 1. 安装 Golang 1.25.1
go version  # 验证: go version go1.25.1 windows/amd64

# 2. 创建项目
mkdir otlp-demo && cd otlp-demo
go mod init otlp-demo

# 3. 安装依赖
go get go.opentelemetry.io/otel@v1.31.0
go get go.opentelemetry.io/otel/sdk@v1.31.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.31.0
```

### 1.2 最小化示例

```go
// main.go
package main

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    ctx := context.Background()

    // 1. 初始化 TracerProvider
    tp, err := initTracer(ctx)
    if err != nil {
        panic(err)
    }
    defer tp.Shutdown(ctx)

    // 2. 获取 Tracer
    tracer := otel.Tracer("demo")

    // 3. 创建 Span
    ctx, span := tracer.Start(ctx, "main")
    defer span.End()

    // 4. 业务逻辑
    processOrder(ctx, "ORDER-123")
}

func initTracer(ctx context.Context) (*sdktrace.TracerProvider, error) {
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    res := resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceName("demo-service"),
        semconv.ServiceVersion("1.0.0"),
    )

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

func processOrder(ctx context.Context, orderID string) {
    tracer := otel.Tracer("demo")
    ctx, span := tracer.Start(ctx, "processOrder")
    defer span.End()

    span.SetAttributes(
        attribute.String("order.id", orderID),
        attribute.String("order.status", "pending"),
    )

    // 模拟处理
    time.Sleep(100 * time.Millisecond)

    span.AddEvent("Order validated",
        trace.WithAttributes(
            attribute.Bool("valid", true),
        ),
    )

    fmt.Printf("Processed order: %s\n", orderID)
}
```

### 1.3 启动 Collector

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

service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [logging]
```

```bash
# 启动 Collector
otelcol --config collector-config.yaml

# 运行程序
go run main.go
```

---

## 2. CSP 并发模式实现

### 2.1 Fan-Out/Fan-In

```go
// Fan-Out: 一个输入 → 多个处理器
func fanOut(ctx context.Context, input <-chan Order, n int) []<-chan Result {
    tracer := otel.Tracer("fanout")
    ctx, span := tracer.Start(ctx, "fanOut")
    defer span.End()

    outputs := make([]<-chan Result, n)
    for i := 0; i < n; i++ {
        outputs[i] = worker(ctx, fmt.Sprintf("worker-%d", i), input)
    }
    return outputs
}

// Fan-In: 多个输出 → 一个聚合
func fanIn(ctx context.Context, channels ...<-chan Result) <-chan Result {
    tracer := otel.Tracer("fanin")
    ctx, span := tracer.Start(ctx, "fanIn")
    defer span.End()

    out := make(chan Result)
    var wg sync.WaitGroup

    for _, ch := range channels {
        wg.Add(1)
        go func(c <-chan Result) {
            defer wg.Done()
            for result := range c {
                out <- result
            }
        }(ch)
    }

    go func() {
        wg.Wait()
        close(out)
    }()

    return out
}

// Worker 处理器
func worker(ctx context.Context, name string, input <-chan Order) <-chan Result {
    tracer := otel.Tracer("worker")
    out := make(chan Result)

    go func() {
        defer close(out)
        for order := range input {
            ctx, span := tracer.Start(ctx, "worker.process",
                trace.WithAttributes(
                    attribute.String("worker.name", name),
                    attribute.String("order.id", order.ID),
                ),
            )

            result := processOrderInternal(ctx, order)
            span.End()

            out <- result
        }
    }()

    return out
}
```

**OTLP Span 树**:

```text
fanOut
  ├─ worker-0.process (order-1)
  ├─ worker-1.process (order-2)
  └─ worker-2.process (order-3)
fanIn
  └─ (收集所有 worker 结果)
```

### 2.2 Pipeline 模式

```go
type Stage func(context.Context, <-chan interface{}) <-chan interface{}

func Pipeline(ctx context.Context, stages ...Stage) Stage {
    return func(ctx context.Context, in <-chan interface{}) <-chan interface{} {
        tracer := otel.Tracer("pipeline")
        ctx, span := tracer.Start(ctx, "Pipeline")
        defer span.End()

        out := in
        for i, stage := range stages {
            ctx, stageSpan := tracer.Start(ctx, fmt.Sprintf("stage-%d", i))
            out = stage(ctx, out)
            stageSpan.End()
        }
        return out
    }
}

// 使用示例
func main() {
    pipeline := Pipeline(ctx,
        validateStage,
        enrichStage,
        persistStage,
    )
    
    results := pipeline(ctx, orders)
}
```

### 2.3 Worker Pool

```go
type WorkerPool struct {
    workers   int
    taskQueue chan Task
    results   chan Result
    wg        sync.WaitGroup
    ctx       context.Context
    cancel    context.CancelFunc
}

func NewWorkerPool(ctx context.Context, workers int, queueSize int) *WorkerPool {
    ctx, cancel := context.WithCancel(ctx)
    return &WorkerPool{
        workers:   workers,
        taskQueue: make(chan Task, queueSize),
        results:   make(chan Result, queueSize),
        ctx:       ctx,
        cancel:    cancel,
    }
}

func (p *WorkerPool) Start() {
    tracer := otel.Tracer("workerpool")
    
    for i := 0; i < p.workers; i++ {
        p.wg.Add(1)
        go func(workerID int) {
            defer p.wg.Done()

            for {
                select {
                case task := <-p.taskQueue:
                    ctx, span := tracer.Start(p.ctx, "worker.execute",
                        trace.WithAttributes(
                            attribute.Int("worker.id", workerID),
                            attribute.String("task.id", task.ID),
                        ),
                    )

                    result := task.Execute(ctx)
                    p.results <- result

                    span.End()

                case <-p.ctx.Done():
                    return
                }
            }
        }(i)
    }
}

func (p *WorkerPool) Submit(task Task) {
    p.taskQueue <- task
}

func (p *WorkerPool) Shutdown() {
    close(p.taskQueue)
    p.cancel()
    p.wg.Wait()
    close(p.results)
}
```

---

## 3. 分布式追踪实现

### 3.1 HTTP 服务端

```go
import (
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
)

func main() {
    // 自动追踪 HTTP 请求
    handler := http.HandlerFunc(handleOrder)
    wrappedHandler := otelhttp.NewHandler(handler, "order-api")

    http.Handle("/orders", wrappedHandler)
    http.ListenAndServe(":8080", nil)
}

func handleOrder(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("order-api")

    // Context 已自动包含 Span
    ctx, span := tracer.Start(ctx, "handleOrder")
    defer span.End()

    // 提取 Baggage
    bag := baggage.FromContext(ctx)
    tenantID := bag.Member("tenant_id").Value()

    span.SetAttributes(
        attribute.String("http.method", r.Method),
        attribute.String("http.path", r.URL.Path),
        attribute.String("tenant.id", tenantID),
    )

    // 调用下游服务
    err := callPaymentService(ctx)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    w.WriteHeader(http.StatusOK)
}
```

### 3.2 HTTP 客户端

```go
func callPaymentService(ctx context.Context) error {
    tracer := otel.Tracer("order-api")
    ctx, span := tracer.Start(ctx, "callPaymentService",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    // 创建带追踪的 HTTP Client
    client := http.Client{
        Transport: otelhttp.NewTransport(http.DefaultTransport),
    }

    req, _ := http.NewRequestWithContext(ctx, "POST", "http://payment-service/charge", nil)
    
    // Propagator 自动注入 Header
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

### 3.3 gRPC 集成

```go
import (
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
)

// 服务端
func startGRPCServer() {
    server := grpc.NewServer(
        grpc.StatsHandler(otelgrpc.NewServerHandler()),
    )
    
    pb.RegisterOrderServiceServer(server, &orderServiceImpl{})
    server.Serve(listener)
}

// 客户端
func createGRPCClient() {
    conn, err := grpc.Dial("payment-service:9090",
        grpc.WithStatsHandler(otelgrpc.NewClientHandler()),
    )
    if err != nil {
        panic(err)
    }
    
    client := pb.NewPaymentServiceClient(conn)
}
```

---

## 4. 性能优化实践

### 4.1 采样策略

```go
// 自定义采样器
type CustomSampler struct {
    traceIDRatio float64
    errorSampler sdktrace.Sampler
}

func (s *CustomSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 1. 错误全采样
    if isError(p.Attributes) {
        return s.errorSampler.ShouldSample(p)
    }

    // 2. 慢请求全采样 (> 1s)
    if duration := getDuration(p.Attributes); duration > time.Second {
        return sdktrace.SamplingResult{
            Decision:   sdktrace.RecordAndSample,
            Attributes: p.Attributes,
        }
    }

    // 3. 正常请求按比例采样
    return sdktrace.TraceIDRatioBased(s.traceIDRatio).ShouldSample(p)
}

// 使用
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(&CustomSampler{
        traceIDRatio: 0.01,  // 1% 正常流量
        errorSampler: sdktrace.AlwaysSample(),
    }),
)
```

### 4.2 Span 批量处理

```go
// 配置 BatchSpanProcessor
bsp := sdktrace.NewBatchSpanProcessor(
    exporter,
    sdktrace.WithMaxQueueSize(2048),      // 队列大小
    sdktrace.WithBatchTimeout(5*time.Second),  // 批量超时
    sdktrace.WithMaxExportBatchSize(512),      // 单批最大 Span 数
    sdktrace.WithBlocking(),                   // 队列满时阻塞
)

tp := sdktrace.NewTracerProvider(
    sdktrace.WithSpanProcessor(bsp),
)
```

### 4.3 资源池化

```go
// Attribute 池化
var attrPool = sync.Pool{
    New: func() interface{} {
        return make([]attribute.KeyValue, 0, 16)
    },
}

func recordSpan(ctx context.Context, name string) {
    attrs := attrPool.Get().([]attribute.KeyValue)
    defer func() {
        attrs = attrs[:0]
        attrPool.Put(attrs)
    }()

    attrs = append(attrs,
        attribute.String("service", "order"),
        attribute.Int("version", 1),
    )

    _, span := tracer.Start(ctx, name,
        trace.WithAttributes(attrs...),
    )
    defer span.End()
}
```

---

## 5. OTTL 实战配置

### 5.1 Collector 配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  # 1. PII 脱敏
  transform/mask_pii:
    trace_statements:
      - context: span
        statements:
          # 信用卡脱敏
          - set(attributes["credit_card"], Mask(attributes["credit_card"], 4, 4)) 
            where attributes["credit_card"] != nil
          # Email 哈希
          - set(attributes["email"], SHA256(attributes["email"])) 
            where attributes["email"] != nil

  # 2. 动态采样
  transform/sampling:
    trace_statements:
      - context: span
        statements:
          # 错误标记
          - set(attributes["sample.priority"], 100) 
            where status.code == STATUS_CODE_ERROR
          # 慢请求标记
          - set(attributes["sample.priority"], 100) 
            where (end_time_unix_nano - start_time_unix_nano) > 1000000000

  # 3. 多租户路由
  routing/tenant:
    from_attribute: tenant_id
    table:
      - value: "tenant_a"
        exporters: [otlp/tenant_a]
      - value: "tenant_b"
        exporters: [otlp/tenant_b]
    default_exporters: [otlp/default]

exporters:
  otlp/tenant_a:
    endpoint: jaeger-tenant-a:4317
  otlp/tenant_b:
    endpoint: jaeger-tenant-b:4317
  otlp/default:
    endpoint: jaeger-default:4317

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [transform/mask_pii, transform/sampling, routing/tenant]
      exporters: [otlp/tenant_a, otlp/tenant_b, otlp/default]
```

### 5.2 高级 OTTL 规则

```yaml
# 聚合统计
transform/stats:
  trace_statements:
    - context: span
      statements:
        # 计算平均 Span 大小
        - set(attributes["span.size"], len(name) + len(attributes)) 
        
        # 标记高价值 Trace
        - set(attributes["high_value"], true) 
          where count(attributes) > 20 or len(events) > 10

# 动态属性丰富
transform/enrich:
  trace_statements:
    - context: resource
      statements:
        # 注入 K8s 元数据
        - set(attributes["k8s.cluster"], env("K8S_CLUSTER_NAME"))
        - set(attributes["k8s.namespace"], env("K8S_NAMESPACE"))
        
        # 注入地理位置
        - set(attributes["geo.region"], LookupGeo(attributes["host.ip"]))
```

---

## 6. OPAMP Agent 实现

```go
import (
    "github.com/open-telemetry/opamp-go/client"
    "github.com/open-telemetry/opamp-go/protobufs"
)

func startOPAMPAgent() {
    opampClient := client.NewHTTP(&client.HTTPSettings{
        OpAMPServerURL: "https://opamp-server:4320",
        Callbacks: client.CallbacksStruct{
            // 接收新配置
            OnMessageFunc: func(ctx context.Context, msg *protobufs.ServerToAgent) *protobufs.AgentToServer {
                if msg.RemoteConfig != nil {
                    applyNewConfig(msg.RemoteConfig.Config)
                }
                return createHeartbeat()
            },

            // 保存远程配置
            SaveRemoteConfigStatusFunc: func(ctx context.Context, status *protobufs.RemoteConfigStatus) {
                log.Printf("Config applied: hash=%x, status=%s",
                    status.LastRemoteConfigHash,
                    status.Status,
                )
            },
        },
    })

    err := opampClient.Start(context.Background())
    if err != nil {
        panic(err)
    }
}

func applyNewConfig(configBytes []byte) error {
    // 1. 解析配置
    var config CollectorConfig
    if err := yaml.Unmarshal(configBytes, &config); err != nil {
        return err
    }

    // 2. 验证配置
    if err := config.Validate(); err != nil {
        return err
    }

    // 3. 热重载 Collector
    if err := reloadCollector(&config); err != nil {
        return err
    }

    log.Println("Config applied successfully")
    return nil
}

func createHeartbeat() *protobufs.AgentToServer {
    return &protobufs.AgentToServer{
        InstanceUid: instanceUID,
        Capabilities: uint64(
            protobufs.AgentCapabilities_AcceptsRemoteConfig |
                protobufs.AgentCapabilities_ReportsHealth,
        ),
        Health: &protobufs.ComponentHealth{
            Healthy: true,
            StartTimeUnixNano: uint64(startTime.UnixNano()),
        },
    }
}
```

---

## 7. 容器化部署

### 7.1 Dockerfile

```dockerfile
# Multi-stage build
FROM golang:1.25.1-alpine AS builder

WORKDIR /build
COPY go.mod go.sum ./
RUN go mod download

COPY . .
RUN CGO_ENABLED=0 GOOS=linux go build -o app .

# Runtime
FROM alpine:latest
RUN apk --no-cache add ca-certificates

WORKDIR /app
COPY --from=builder /build/app .

EXPOSE 8080
CMD ["./app"]
```

### 7.2 Docker Compose

```yaml
version: '3.8'

services:
  # 业务服务
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
      - OTEL_SERVICE_NAME=demo-service
    depends_on:
      - otel-collector

  # OTLP Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.112.0
    command: ["--config=/etc/otel/config.yaml"]
    volumes:
      - ./collector-config.yaml:/etc/otel/config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Metrics
    depends_on:
      - jaeger

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686"  # UI
      - "14250:14250"  # gRPC
```

### 7.3 Kubernetes 部署

```yaml
# Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: demo-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: demo-service
  template:
    metadata:
      labels:
        app: demo-service
    spec:
      containers:
      - name: app
        image: demo-service:v1
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector.observability:4317"
        - name: OTEL_SERVICE_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "k8s.namespace=$(NAMESPACE),k8s.pod=$(POD_NAME)"

---
# Service
apiVersion: v1
kind: Service
metadata:
  name: demo-service
spec:
  selector:
    app: demo-service
  ports:
  - port: 80
    targetPort: 8080
```

---

## 8. 性能基准测试

### 8.1 基准测试代码

```go
// benchmarks/tracing_test.go
func BenchmarkSpanCreation(b *testing.B) {
    ctx := context.Background()
    tracer := otel.Tracer("bench")

    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        _, span := tracer.Start(ctx, "operation")
        span.End()
    }
}

func BenchmarkSpanWithAttributes(b *testing.B) {
    ctx := context.Background()
    tracer := otel.Tracer("bench")

    attrs := []attribute.KeyValue{
        attribute.String("key1", "value1"),
        attribute.Int("key2", 42),
        attribute.Bool("key3", true),
    }

    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        _, span := tracer.Start(ctx, "operation",
            trace.WithAttributes(attrs...),
        )
        span.End()
    }
}

func BenchmarkConcurrentSpans(b *testing.B) {
    ctx := context.Background()
    tracer := otel.Tracer("bench")

    b.RunParallel(func(pb *testing.PB) {
        for pb.Next() {
            _, span := tracer.Start(ctx, "operation")
            span.End()
        }
    })
}
```

### 8.2 运行基准测试

```bash
# 运行所有基准测试
go test -bench=. -benchmem ./benchmarks/

# 输出示例:
# BenchmarkSpanCreation-8           500000    2847 ns/op    1024 B/op    12 allocs/op
# BenchmarkSpanWithAttributes-8     300000    3921 ns/op    1536 B/op    16 allocs/op
# BenchmarkConcurrentSpans-8       1000000    1243 ns/op     512 B/op     8 allocs/op

# 生成 CPU Profile
go test -bench=. -cpuprofile=cpu.prof ./benchmarks/
go tool pprof cpu.prof
```

---

## 9. 故障排查

### 9.1 常见问题

#### 问题 1: Span 未导出

**症状**: 程序运行正常,但 Jaeger 中看不到 Trace

**排查步骤**:

```go
// 1. 检查 TracerProvider 是否正确关闭
defer func() {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    if err := tp.Shutdown(ctx); err != nil {
        log.Printf("Error shutting down tracer provider: %v", err)
    }
}()

// 2. 启用 SDK 日志
import "go.opentelemetry.io/otel/sdk/trace"
otel.SetLogger(logr.New(/* your logger */))

// 3. 检查采样配置
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(sdktrace.AlwaysSample()),  // 临时全采样
)
```

#### 问题 2: 内存泄漏

**症状**: 内存持续增长

**排查**:

```bash
# 1. 生成 Heap Profile
curl http://localhost:6060/debug/pprof/heap > heap.prof
go tool pprof -http=:8080 heap.prof

# 2. 检查 Goroutine 泄漏
curl http://localhost:6060/debug/pprof/goroutine?debug=2

# 3. 检查 Span 是否正确结束
# 使用 defer span.End() 确保释放
```

### 9.2 性能调优

```go
// 1. 调整批量处理参数
bsp := sdktrace.NewBatchSpanProcessor(
    exporter,
    sdktrace.WithMaxQueueSize(4096),          // 增加队列
    sdktrace.WithBatchTimeout(10*time.Second),  // 增加超时
    sdktrace.WithMaxExportBatchSize(1024),     // 增加批量大小
)

// 2. 使用采样降低开销
sampler := sdktrace.ParentBased(
    sdktrace.TraceIDRatioBased(0.05),  // 5% 采样
)

// 3. 池化 Attribute
var attrPool = sync.Pool{
    New: func() interface{} {
        return make([]attribute.KeyValue, 0, 32)  // 预分配
    },
}
```

---

## 10. 下一步学习

### 10.1 深入理论

- 阅读 [CSP-OTLP 同构证明](./03-csp-otlp-isomorphism-proof.md)
- 学习 [OTTL 转换语言](./06-ottl-transformation-language.md)
- 研究 [OPAMP 控制平面](./04-opamp-control-plane-design.md)

### 10.2 生产实践

- 参考 [生产部署最佳实践](./10-production-best-practices.md)
- 查看 [性能优化策略](./07-performance-optimization.md)
- 集成 [eBPF Profiling](./08-ebpf-profiling-integration.md)

### 10.3 社区资源

- OpenTelemetry 官方文档: <https://opentelemetry.io/docs/>
- Golang SDK 仓库: <https://github.com/open-telemetry/opentelemetry-go>
- OTTL 示例: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/pkg/ottl>

---

**文档维护**: OTLP_go 项目  
**最后更新**: 2025-10-04  
**版本**: v1.0

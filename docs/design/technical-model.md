# 技术模型（架构/实现/性能）

## 目录

- [技术模型（架构/实现/性能）](#技术模型架构实现性能)
  - [目录](#目录)
  - [1. 架构分层](#1-架构分层)
    - [1.1 五层架构设计](#11-五层架构设计)
    - [1.2 关键路径](#12-关键路径)
  - [2. SDK 层实现](#2-sdk-层实现)
    - [2.1 应用插桩](#21-应用插桩)
    - [2.2 自动插桩](#22-自动插桩)
  - [3. Agent/Sidecar 层](#3-agentsidecar-层)
    - [3.1 部署模式](#31-部署模式)
    - [3.2 本地聚合](#32-本地聚合)
  - [4. Collector 层](#4-collector-层)
    - [4.1 Pipeline 架构](#41-pipeline-架构)
    - [4.2 处理器类型](#42-处理器类型)
  - [5. Gateway 层](#5-gateway-层)
    - [5.1 区域汇聚](#51-区域汇聚)
    - [5.2 智能路由](#52-智能路由)
  - [6. Backend 层](#6-backend-层)
    - [6.1 存储选型](#61-存储选型)
    - [6.2 查询优化](#62-查询优化)
  - [7. 性能基线](#7-性能基线)
    - [7.1 吞吐量指标](#71-吞吐量指标)
    - [7.2 延迟预算](#72-延迟预算)
    - [7.3 资源消耗](#73-资源消耗)
  - [8. 可编程性](#8-可编程性)
    - [8.1 OTTL 转换](#81-ottl-转换)
    - [8.2 WASM 插件](#82-wasm-插件)
  - [9. 安全性](#9-安全性)
    - [9.1 传输安全](#91-传输安全)
    - [9.2 认证授权](#92-认证授权)
    - [9.3 多租户隔离](#93-多租户隔离)
  - [10. 运维性](#10-运维性)
    - [10.1 OPAMP 管理](#101-opamp-管理)
    - [10.2 灰度发布](#102-灰度发布)
    - [10.3 健康监控](#103-健康监控)
  - [11. 参考资料](#11-参考资料)

## 1. 架构分层

### 1.1 五层架构设计

```text
┌─────────────────────────────────────────────────────────────┐
│                      Application Layer                      │
│  • Business Logic                                           │
│  • OpenTelemetry SDK (Traces/Metrics/Logs/Profiles)         │
│  • Auto-instrumentation (HTTP/gRPC/DB)                      │
└──────────────────────────┬──────────────────────────────────┘
                           │ OTLP/gRPC or OTLP/HTTP
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                    Agent/Sidecar Layer                      │
│  • Local aggregation (per-node/per-pod)                     │
│  • Head-based sampling                                      │
│  • Basic filtering                                          │
│  • Batch processing                                         │
└──────────────────────────┬──────────────────────────────────┘
                           │ OTLP/gRPC (TLS)
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                      Collector Layer                        │
│  • Advanced processing (transform/filter/enrich)            │
│  • Tail-based sampling                                      │
│  • Data quality validation                                  │
│  • Protocol translation                                     │
└──────────────────────────┬──────────────────────────────────┘
                           │ OTLP/gRPC (mTLS)
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                       Gateway Layer                         │
│  • Regional aggregation (cross-AZ)                          │
│  • Intelligent routing (tenant/env/signal)                  │
│  • Load balancing                                           │
│  • Rate limiting                                            │
└──────────────────────────┬──────────────────────────────────┘
                           │ Backend-specific protocols
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                       Backend Layer                         │
│  • Jaeger/Tempo (Traces)                                    │
│  • Prometheus/Mimir (Metrics)                               │
│  • Loki/Elasticsearch (Logs)                                │
│  • Phlare/Pyroscope (Profiles)                              │
└─────────────────────────────────────────────────────────────┘
```

### 1.2 关键路径

**数据流向**：

```text
Application
    ↓ (1) Instrumentation
  Span/Metric/Log Created
    ↓ (2) SDK Processing
  Batching + Resource Attachment
    ↓ (3) OTLP Export (gRPC/HTTP + gzip)
  Network Transmission
    ↓ (4) Agent Reception
  Local Aggregation + Sampling
    ↓ (5) Collector Processing
  Transform + Filter + Enrich
    ↓ (6) Gateway Routing
  Tenant/Signal-based Routing
    ↓ (7) Backend Storage
  Persistent Storage + Indexing
```

**延迟分解**：

| 阶段 | 操作 | P50 | P95 | P99 |
|------|------|-----|-----|-----|
| (1) Instrumentation | Span 创建 | 50 μs | 100 μs | 200 μs |
| (2) SDK Processing | 批处理 + 序列化 | 500 μs | 1 ms | 2 ms |
| (3) OTLP Export | 网络传输 | 2 ms | 5 ms | 10 ms |
| (4) Agent Processing | 聚合 + 采样 | 1 ms | 2 ms | 5 ms |
| (5) Collector Processing | 转换 + 过滤 | 3 ms | 8 ms | 15 ms |
| (6) Gateway Routing | 路由决策 | 1 ms | 3 ms | 8 ms |
| (7) Backend Storage | 写入存储 | 10 ms | 30 ms | 100 ms |
| **总计** | **端到端** | **17.55 ms** | **49.1 ms** | **140.2 ms** |

## 2. SDK 层实现

### 2.1 应用插桩

**手动插桩示例**（Go 1.25.1）：

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func initTracer() (*sdktrace.TracerProvider, error) {
    // 1. 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    // 2. 创建 Resource
    res, err := resource.New(context.Background(),
        resource.WithAttributes(
            semconv.ServiceName("my-service"),
            semconv.ServiceVersion("v1.0.0"),
            semconv.DeploymentEnvironment("production"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 3. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(0.5), // 50% 采样
        )),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

func businessLogic(ctx context.Context) error {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "business-operation")
    defer span.End()

    // 业务逻辑
    span.SetAttributes(
        semconv.HTTPMethod("POST"),
        semconv.HTTPStatusCode(200),
    )

    return nil
}
```

### 2.2 自动插桩

**HTTP 服务器自动追踪**：

```go
import (
    "net/http"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
)

func main() {
    // 包装 HTTP Handler
    handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        w.Write([]byte("Hello, World!"))
    })

    wrappedHandler := otelhttp.NewHandler(handler, "my-service")
    http.ListenAndServe(":8080", wrappedHandler)
}
```

**数据库自动追踪**：

```go
import (
    "database/sql"
    "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"
)

func main() {
    // 注册带追踪的数据库驱动
    driverName, err := otelsql.Register("postgres",
        otelsql.WithAttributes(
            semconv.DBSystemPostgreSQL,
        ),
    )
    if err != nil {
        panic(err)
    }

    db, err := sql.Open(driverName, "postgres://...")
    // 所有 SQL 查询自动追踪
}
```

## 3. Agent/Sidecar 层

### 3.1 部署模式

**DaemonSet 模式**（Kubernetes）：

```yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-agent
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-agent
  template:
    metadata:
      labels:
        app: otel-agent
    spec:
      containers:
      - name: otel-agent
        image: otel/opentelemetry-collector:0.95.0
        resources:
          limits:
            cpu: 500m
            memory: 512Mi
          requests:
            cpu: 200m
            memory: 256Mi
        volumeMounts:
        - name: config
          mountPath: /etc/otelcol
      volumes:
      - name: config
        configMap:
          name: otel-agent-config
```

**Sidecar 模式**：

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: app-with-sidecar
spec:
  containers:
  - name: app
    image: my-app:latest
    env:
    - name: OTEL_EXPORTER_OTLP_ENDPOINT
      value: "http://localhost:4317"
  
  - name: otel-sidecar
    image: otel/opentelemetry-collector:0.95.0
    ports:
    - containerPort: 4317
```

### 3.2 本地聚合

**Agent 配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  probabilistic_sampler:
    sampling_percentage: 50

exporters:
  otlp:
    endpoint: collector.observability.svc.cluster.local:4317
    tls:
      insecure: false
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, probabilistic_sampler]
      exporters: [otlp]
```

## 4. Collector 层

### 4.1 Pipeline 架构

**Collector 组件模型**：

```text
┌──────────────────────────────────────────────────────────┐
│                      Receivers                           │
│  • OTLP (gRPC/HTTP)                                      │
│  • Jaeger, Zipkin, Prometheus, etc.                     │
└────────────────────┬─────────────────────────────────────┘
                     │
                     ▼
┌──────────────────────────────────────────────────────────┐
│                     Processors                           │
│  • batch, memory_limiter, transform (OTTL)              │
│  • tail_sampling, filter, attributes                    │
│  • groupbyattrs, routing, span                          │
└────────────────────┬─────────────────────────────────────┘
                     │
                     ▼
┌──────────────────────────────────────────────────────────┐
│                      Exporters                           │
│  • OTLP, Jaeger, Prometheus, Loki                       │
│  • File, Kafka, Cloud-specific                          │
└──────────────────────────────────────────────────────────┘
```

### 4.2 处理器类型

**Transform 处理器（OTTL）**：

```yaml
processors:
  transform:
    error_mode: ignore
    traces:
      # 脱敏
      - set(attributes["user.id"], SHA256(attributes["user.id"])) 
        where resource.attributes["env"] == "prod"
      
      # 超时标记
      - set(status.message, "timeout") 
        where duration > Duration("3s")
      
      # 删除敏感字段
      - delete_key(attributes, "http.request.header.authorization")
      - delete_key(attributes, "http.request.header.cookie")
```

**Tail Sampling 处理器**：

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    num_traces: 100000
    expected_new_traces_per_sec: 10000
    policies:
      # 保留所有错误
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 保留慢请求
      - name: slow
        type: latency
        latency:
          threshold_ms: 1000
      
      # 概率采样
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
```

## 5. Gateway 层

### 5.1 区域汇聚

**Gateway 部署**（跨 AZ）：

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-gateway
  namespace: observability
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxUnavailable: 1
      maxSurge: 1
  template:
    spec:
      affinity:
        podAntiAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
          - labelSelector:
              matchLabels:
                app: otel-gateway
            topologyKey: topology.kubernetes.io/zone
      containers:
      - name: otel-gateway
        image: otel/opentelemetry-collector-contrib:0.95.0
        resources:
          limits:
            cpu: 2000m
            memory: 4Gi
```

### 5.2 智能路由

**基于租户的路由**：

```yaml
processors:
  routing:
    from_attribute: tenant
    default_exporters: [otlp/default]
    table:
      - value: tenant-a
        exporters: [otlp/tenant-a]
      - value: tenant-b
        exporters: [otlp/tenant-b]

exporters:
  otlp/tenant-a:
    endpoint: backend-a.example.com:4317
    headers:
      x-tenant-id: tenant-a
  
  otlp/tenant-b:
    endpoint: backend-b.example.com:4317
    headers:
      x-tenant-id: tenant-b
```

## 6. Backend 层

### 6.1 存储选型

**Traces 存储对比**：

| 特性 | Jaeger | Tempo | Zipkin |
|------|--------|-------|--------|
| 存储后端 | Cassandra/Elasticsearch | S3/GCS/Azure Blob | MySQL/Cassandra |
| OTLP 支持 | ✓ (原生) | ✓ (原生) | ✗ (需转换) |
| 查询性能 | 高 | 中 | 中 |
| 成本 | 中 | 低 (对象存储) | 中 |
| 推荐场景 | 实时查询 | 长期存储 | 传统系统 |

**Metrics 存储对比**：

| 特性 | Prometheus | Mimir | Thanos |
|------|------------|-------|--------|
| 架构 | 单机 | 分布式 | 分布式 |
| 长期存储 | 有限 (2-4 周) | 无限 | 无限 |
| 查询性能 | 高 | 高 | 中 |
| 多租户 | ✗ | ✓ | ✓ |
| 推荐场景 | 小规模 | 大规模多租户 | 联邦查询 |

### 6.2 查询优化

**Trace 查询索引**：

```sql
-- Jaeger 索引策略
CREATE INDEX idx_trace_id ON spans(trace_id);
CREATE INDEX idx_service_operation ON spans(service_name, operation_name);
CREATE INDEX idx_duration ON spans(duration);
CREATE INDEX idx_tags ON spans USING GIN(tags);
```

**Metrics 查询优化**：

```yaml
# Prometheus 查询优化
global:
  scrape_interval: 15s
  evaluation_interval: 15s

# 使用 recording rules 预聚合
groups:
  - name: api_latency
    interval: 30s
    rules:
      - record: api:http_request_duration_seconds:p95
        expr: histogram_quantile(0.95, 
          rate(http_request_duration_seconds_bucket[5m]))
```

## 7. 性能基线

### 7.1 吞吐量指标

**单 Collector 实例**（4 CPU, 8GB RAM）：

| 信号类型 | 吞吐量 | CPU 使用率 | 内存使用 |
|---------|--------|-----------|---------|
| Traces | 200k span/s | 60% | 2GB |
| Metrics | 500k datapoint/s | 50% | 1.5GB |
| Logs | 100k record/s | 40% | 1GB |

**性能调优参数**：

```yaml
processors:
  batch:
    timeout: 10s
    send_batch_size: 1024      # 增大批次提高吞吐
    send_batch_max_size: 2048
  
exporters:
  otlp:
    sending_queue:
      enabled: true
      num_consumers: 10         # 增加并发消费者
      queue_size: 5000
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
```

### 7.2 延迟预算

**端到端延迟目标**：

- **P50**: < 20 ms
- **P95**: < 50 ms
- **P99**: < 150 ms

**各层延迟贡献**：

```text
Application (SDK)     ████ 2 ms
  ↓
Agent Processing      ██ 1 ms
  ↓
Network (Agent→Coll)  ████ 2 ms
  ↓
Collector Processing  ████████ 8 ms
  ↓
Network (Coll→GW)     ██ 1 ms
  ↓
Gateway Routing       ███ 3 ms
  ↓
Network (GW→Backend)  ██ 1 ms
  ↓
Backend Write         ████████████████████ 30 ms
```

### 7.3 资源消耗

**Agent 资源配额**（per node）：

```yaml
resources:
  requests:
    cpu: 200m
    memory: 256Mi
  limits:
    cpu: 500m
    memory: 512Mi
```

**Collector 资源配额**（per instance）：

```yaml
resources:
  requests:
    cpu: 1000m
    memory: 2Gi
  limits:
    cpu: 2000m
    memory: 4Gi
```

## 8. 可编程性

### 8.1 OTTL 转换

**OTTL 语言特性**：

```yaml
# 条件过滤
- set(attributes["filtered"], true) 
  where attributes["http.status_code"] >= 400

# 字符串操作
- set(attributes["service"], Substring(resource.attributes["service.name"], 0, 10))

# 数学运算
- set(attributes["duration_ms"], duration / 1000000)

# 哈希函数
- set(attributes["user_id_hash"], SHA256(attributes["user.id"]))

# 正则匹配
- set(attributes["is_api"], IsMatch(attributes["http.target"], "^/api/.*"))
```

### 8.2 WASM 插件

**自定义处理器**（Rust + WASM）：

```rust
use proxy_wasm::traits::*;
use proxy_wasm::types::*;

#[no_mangle]
pub fn _start() {
    proxy_wasm::set_root_context(|_| -> Box<dyn RootContext> {
        Box::new(CustomProcessor)
    });
}

struct CustomProcessor;

impl Context for CustomProcessor {}

impl RootContext for CustomProcessor {
    fn on_vm_start(&mut self, _: usize) -> bool {
        true
    }
}

impl HttpContext for CustomProcessor {
    fn on_http_request_headers(&mut self, _: usize) -> Action {
        // 自定义处理逻辑
        self.set_http_request_header("x-custom-header", Some("value"));
        Action::Continue
    }
}
```

**编译与部署**：

```bash
# 编译 WASM
cargo build --target wasm32-wasi --release

# 通过 OPAMP 分发
opamp-cli deploy-plugin \
  --name custom-processor \
  --version v1.0.0 \
  --file target/wasm32-wasi/release/custom_processor.wasm
```

## 9. 安全性

### 9.1 传输安全

**mTLS 配置**：

```yaml
exporters:
  otlp:
    endpoint: collector.example.com:4317
    tls:
      insecure: false
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key
      ca_file: /etc/certs/ca.crt
      min_version: "1.3"
      cipher_suites:
        - TLS_AES_128_GCM_SHA256
        - TLS_AES_256_GCM_SHA384
```

### 9.2 认证授权

**Bearer Token 认证**：

```yaml
exporters:
  otlp:
    endpoint: backend.example.com:4317
    headers:
      authorization: "Bearer ${OTLP_TOKEN}"
```

**OAuth2 认证**：

```go
import "golang.org/x/oauth2"

func createAuthenticatedExporter() {
    config := &oauth2.Config{
        ClientID:     "client-id",
        ClientSecret: "client-secret",
        Endpoint: oauth2.Endpoint{
            TokenURL: "https://auth.example.com/token",
        },
    }
    
    token, _ := config.Token(context.Background())
    // 使用 token 创建导出器
}
```

### 9.3 多租户隔离

**租户标签注入**：

```yaml
processors:
  resource:
    attributes:
      - key: tenant
        value: ${TENANT_ID}
        action: insert
      - key: env
        value: ${ENVIRONMENT}
        action: insert
```

**租户路由与隔离**：

```yaml
processors:
  routing:
    from_attribute: tenant
    table:
      - value: tenant-a
        exporters: [otlp/tenant-a]
      - value: tenant-b
        exporters: [otlp/tenant-b]

exporters:
  otlp/tenant-a:
    endpoint: tenant-a-backend.example.com:4317
  otlp/tenant-b:
    endpoint: tenant-b-backend.example.com:4317
```

## 10. 运维性

### 10.1 OPAMP 管理

**Agent 配置**：

```yaml
opamp:
  server:
    endpoint: wss://opamp.example.com:4320/v1/opamp
    tls:
      insecure: false
      cert_file: /etc/certs/agent.crt
      key_file: /etc/certs/agent.key
  
  agent:
    instance_id: ${HOSTNAME}
    labels:
      env: ${ENV}
      region: ${REGION}
  
  capabilities:
    accepts_remote_config: true
    reports_health: true
    accepts_packages: true
```

### 10.2 灰度发布

**分阶段发布策略**：

```yaml
rollout:
  strategy: canary
  stages:
    - name: staging
      selector: {env: staging}
      weight: 100%
      duration: 2h
    
    - name: prod_canary
      selector: {env: prod, region: us-west}
      weight: 10%
      duration: 1h
    
    - name: prod_full
      selector: {env: prod}
      weight: 100%
  
  auto_rollback:
    enabled: true
    triggers:
      - error_rate_spike: 2x
      - healthy_agents_below: 90%
```

### 10.3 健康监控

**Prometheus 指标**：

```yaml
# Collector 暴露指标
service:
  telemetry:
    metrics:
      address: 0.0.0.0:8888
      level: detailed
```

**关键指标**：

```promql
# 吞吐量
rate(otelcol_receiver_accepted_spans[5m])

# 错误率
rate(otelcol_exporter_send_failed_spans[5m]) / 
rate(otelcol_exporter_sent_spans[5m])

# 队列使用率
otelcol_exporter_queue_size / otelcol_exporter_queue_capacity

# 处理延迟
histogram_quantile(0.95, 
  rate(otelcol_processor_batch_batch_send_size_bucket[5m]))
```

## 11. 参考资料

- **详细技术架构**：`docs/analysis/technical-model/architecture.md`
- **Go 1.25.1 特性**：`docs/language/go-1.25.1.md`
- **Collector-SDK 映射**：`docs/analysis/technical-model/collector-sdk-mapping.md`
- **分布式模型**：`docs/design/distributed-model.md`
- **OPAMP 控制平面**：`docs/opamp/overview.md`
- **OTTL 示例**：`docs/otlp/ottl-examples.md`

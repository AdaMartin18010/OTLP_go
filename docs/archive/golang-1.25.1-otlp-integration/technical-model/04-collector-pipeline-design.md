# OpenTelemetry Collector Pipeline 架构设计

## 目录

- [OpenTelemetry Collector Pipeline 架构设计](#opentelemetry-collector-pipeline-架构设计)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. Collector 架构总览](#2-collector-架构总览)
    - [2.1 核心组件](#21-核心组件)
    - [2.2 数据流转](#22-数据流转)
    - [2.3 形式化定义](#23-形式化定义)
  - [3. Receiver（接收器）](#3-receiver接收器)
    - [3.1 OTLP Receiver](#31-otlp-receiver)
    - [3.2 Prometheus Receiver](#32-prometheus-receiver)
    - [3.3 自定义 Receiver](#33-自定义-receiver)
  - [4. Processor（处理器）](#4-processor处理器)
    - [4.1 Batch Processor](#41-batch-processor)
    - [4.2 Resource Processor](#42-resource-processor)
    - [4.3 Attributes Processor](#43-attributes-processor)
    - [4.4 Filter Processor](#44-filter-processor)
    - [4.5 Tail Sampling Processor](#45-tail-sampling-processor)
  - [5. Exporter（导出器）](#5-exporter导出器)
    - [5.1 OTLP Exporter](#51-otlp-exporter)
    - [5.2 Prometheus Exporter](#52-prometheus-exporter)
    - [5.3 Jaeger Exporter](#53-jaeger-exporter)
  - [6. Pipeline 配置与编排](#6-pipeline-配置与编排)
    - [6.1 基础配置](#61-基础配置)
    - [6.2 多 Pipeline 配置](#62-多-pipeline-配置)
    - [6.3 Pipeline 拓扑优化](#63-pipeline-拓扑优化)
  - [7. 部署模式](#7-部署模式)
    - [7.1 Agent 模式](#71-agent-模式)
    - [7.2 Gateway 模式](#72-gateway-模式)
    - [7.3 混合模式](#73-混合模式)
  - [8. 性能优化](#8-性能优化)
    - [8.1 内存管理](#81-内存管理)
    - [8.2 并发控制](#82-并发控制)
    - [8.3 背压处理](#83-背压处理)
  - [9. 高可用与容错](#9-高可用与容错)
    - [9.1 负载均衡](#91-负载均衡)
    - [9.2 故障转移](#92-故障转移)
    - [9.3 数据持久化](#93-数据持久化)
  - [10. 监控与可观测性](#10-监控与可观测性)
    - [10.1 自监控指标](#101-自监控指标)
    - [10.2 健康检查](#102-健康检查)
    - [10.3 调试与排查](#103-调试与排查)
  - [11. Go 1.25.1 集成最佳实践](#11-go-1251-集成最佳实践)
    - [11.1 Go 应用 → Collector 配置](#111-go-应用--collector-配置)
    - [11.2 容器化部署](#112-容器化部署)
    - [11.3 Kubernetes 集成](#113-kubernetes-集成)
  - [12. 工程案例](#12-工程案例)
    - [12.1 微服务可观测性平台](#121-微服务可观测性平台)
    - [12.2 多租户数据隔离](#122-多租户数据隔离)
  - [13. 总结](#13-总结)
    - [核心贡献](#核心贡献)
    - [工程价值](#工程价值)

---

## 1. 概述

**OpenTelemetry Collector**（简称 OTel Collector）是一个**厂商无关的遥测数据收集与处理中间件**，其核心设计理念是：

> 解耦数据生产者（应用）与数据消费者（后端存储），提供统一的数据处理管道。

**核心优势**：

1. **厂商中立**：支持多种后端（Prometheus、Jaeger、Zipkin、Datadog 等）
2. **高性能**：Go 实现，支持百万级 QPS
3. **可扩展**：插件化架构，支持自定义组件
4. **云原生**：原生支持 Kubernetes、Docker

**本文档目标**：

- 深入分析 Collector 的 Receiver → Processor → Exporter 管道架构
- 展示不同部署模式（Agent vs Gateway）的设计权衡
- 提供 Go 1.25.1 应用与 Collector 集成的最佳实践

---

## 2. Collector 架构总览

### 2.1 核心组件

```text
┌─────────────────────────────────────────────────────┐
│                   OTel Collector                    │
│                                                     │
│  ┌─────────────┐   ┌─────────────┐   ┌──────────┐ │
│  │  Receivers  │──▶│ Processors  │──▶│ Exporters│ │
│  └─────────────┘   └─────────────┘   └──────────┘ │
│        ▲                  │                  │      │
│        │                  │                  ▼      │
│  ┌─────┴───────┐   ┌──────▼──────┐   ┌──────────┐ │
│  │  OTLP gRPC  │   │   Batch     │   │ Jaeger   │ │
│  │  OTLP HTTP  │   │   Filter    │   │Prometheus│ │
│  │  Prometheus │   │  Resource   │   │  OTLP    │ │
│  └─────────────┘   └─────────────┘   └──────────┘ │
└─────────────────────────────────────────────────────┘
```

**三大核心组件**：

| 组件         | 职责                                | 典型实现                          |
|------------|-------------------------------------|----------------------------------|
| **Receiver** | 接收遥测数据                         | OTLP、Prometheus、Zipkin、Jaeger  |
| **Processor** | 数据转换、过滤、聚合                 | Batch、Filter、Resource、Attributes |
| **Exporter** | 导出数据到后端存储                   | Jaeger、Prometheus、OTLP、Kafka   |

---

### 2.2 数据流转

```text
Application (Go 1.25.1)
    │
    │ (1) 生成 Trace/Metric/Log
    ▼
┌──────────────────────┐
│   OTLP Exporter      │ ← OpenTelemetry-Go SDK
└──────────────────────┘
    │ OTLP/gRPC
    ▼
┌──────────────────────┐
│   Receiver (OTLP)    │ ← Collector
└──────────────────────┘
    │
    │ (2) 数据进入 Pipeline
    ▼
┌──────────────────────┐
│   Processor (Batch)  │ ← 批量聚合
└──────────────────────┘
    │
    ▼
┌──────────────────────┐
│ Processor (Resource) │ ← 添加 Resource Attributes
└──────────────────────┘
    │
    ▼
┌──────────────────────┐
│ Processor (Filter)   │ ← 过滤敏感数据
└──────────────────────┘
    │
    │ (3) 导出到后端
    ▼
┌──────────────────────┐
│  Exporter (Jaeger)   │ ← 存储到 Jaeger
└──────────────────────┘
```

---

### 2.3 形式化定义

**定义**（Collector Pipeline）：
\[
\text{Pipeline} = \langle R, \mathcal{P}, E \rangle
\]

其中：

- \( R \)：Receiver（接收器）
- \( \mathcal{P} = \{p_1, p_2, \dots, p_n\} \)：Processor 有序列表
- \( E \)：Exporter（导出器）

**数据转换函数**：
\[
\text{transform}: \text{Data}_{\text{input}} \xrightarrow{R} \text{Data}_1 \xrightarrow{p_1} \text{Data}_2 \xrightarrow{p_2} \dots \xrightarrow{p_n} \text{Data}_{\text{output}} \xrightarrow{E} \text{Backend}
\]

**不变式**：
\[
\forall d \in \text{Data} : \text{schema}(d_{\text{input}}) = \text{schema}(d_{\text{output}})
\]

---

## 3. Receiver（接收器）

### 3.1 OTLP Receiver

**配置示例**（`config.yaml`）：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 32
        max_concurrent_streams: 100
        keepalive:
          server_parameters:
            max_connection_idle: 11s
            max_connection_age: 12s
            max_connection_age_grace: 13s
            time: 30s
            timeout: 5s
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - "https://*.example.com"
```

**核心参数**：

| 参数                    | 说明                           | 推荐值         |
|------------------------|--------------------------------|---------------|
| `max_recv_msg_size_mib` | 最大消息大小（MiB）             | 32            |
| `max_concurrent_streams` | 最大并发流数                   | 100           |
| `keepalive.time`        | Keepalive 间隔                | 30s           |

---

### 3.2 Prometheus Receiver

**用途**：采集 Prometheus 格式的 Metric

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'otel-collector'
          scrape_interval: 15s
          static_configs:
            - targets: ['localhost:8888']
```

---

### 3.3 自定义 Receiver

**Go 实现示例**：

```go
import (
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/consumer"
)

type customReceiver struct {
    consumer consumer.Traces
}

func (r *customReceiver) Start(ctx context.Context, host component.Host) error {
    // 启动数据接收逻辑
    go r.receiveData(ctx)
    return nil
}

func (r *customReceiver) receiveData(ctx context.Context) {
    // 模拟数据接收
    for {
        traces := generateTraces()
        r.consumer.ConsumeTraces(ctx, traces)
    }
}
```

---

## 4. Processor（处理器）

### 4.1 Batch Processor

**用途**：批量聚合数据，降低网络开销

```yaml
processors:
  batch:
    timeout: 10s                # 批量超时
    send_batch_size: 1024       # 批量大小
    send_batch_max_size: 2048   # 最大批量大小
```

**性能影响**：

- **吞吐量**：+50%（减少网络调用）
- **延迟**：+10s（批量超时）
- **内存**：+100MB（批量缓冲）

---

### 4.2 Resource Processor

**用途**：添加/修改 Resource Attributes

```yaml
processors:
  resource:
    attributes:
      - key: service.namespace
        value: production
        action: insert
      - key: host.name
        from_attribute: hostname
        action: upsert
      - key: internal.debug
        action: delete
```

**Action 类型**：

| Action     | 说明                           |
|-----------|--------------------------------|
| `insert`  | 插入（若存在则忽略）             |
| `update`  | 更新（若不存在则忽略）           |
| `upsert`  | 插入或更新                      |
| `delete`  | 删除                           |

---

### 4.3 Attributes Processor

**用途**：修改 Span/Metric/Log 的 Attributes

```yaml
processors:
  attributes:
    actions:
      - key: http.url
        pattern: ^https?://([^/]+).*$
        action: extract
      - key: db.statement
        action: delete
      - key: user.id
        action: hash
```

**正则提取示例**：

```yaml
# 输入: http.url = "https://api.example.com/users/123"
# 输出: http.host = "api.example.com"
- key: http.host
  from_attribute: http.url
  pattern: ^https?://([^/]+).*$
  action: extract
```

---

### 4.4 Filter Processor

**用途**：过滤不需要的数据

```yaml
processors:
  filter:
    traces:
      span:
        - attributes["http.status_code"] == 200
        - attributes["http.method"] == "GET"
    metrics:
      metric:
        - name == "system.cpu.usage"
```

**条件语法**（OTTL - OpenTelemetry Transformation Language）：

```yaml
# 过滤健康检查请求
- attributes["http.target"] == "/health"

# 过滤低价值 Span（耗时 < 10ms）
- (end_time_unix_nano - start_time_unix_nano) < 10000000

# 过滤指定 Namespace
- resource.attributes["k8s.namespace.name"] == "kube-system"
```

---

### 4.5 Tail Sampling Processor

**用途**：基于 Trace 完整信息的智能采样

```yaml
processors:
  tail_sampling:
    decision_wait: 10s          # 等待 Trace 完整的时间
    num_traces: 100000          # 内存中保留的 Trace 数量
    policies:
      - name: error-traces
        type: status_code
        status_code:
          status_codes: [ERROR]
      - name: slow-traces
        type: latency
        latency:
          threshold_ms: 1000
      - name: sample-10-percent
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
```

**采样策略**：

| 策略类型        | 说明                           | 示例                          |
|---------------|--------------------------------|-------------------------------|
| `always_sample` | 始终采样                       | 生产环境的核心服务             |
| `numeric_attribute` | 基于数值属性                 | `http.status_code >= 400`     |
| `string_attribute` | 基于字符串属性                | `http.method == "POST"`       |
| `latency`     | 基于延迟                       | `latency > 1s`                |
| `status_code` | 基于状态                       | `status == ERROR`             |
| `probabilistic` | 概率采样                      | 10% 采样                      |

---

## 5. Exporter（导出器）

### 5.1 OTLP Exporter

**用途**：导出到另一个 Collector 或后端

```yaml
exporters:
  otlp:
    endpoint: jaeger:4317
    tls:
      insecure: false
      cert_file: /etc/otel/cert.pem
      key_file: /etc/otel/key.pem
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
```

---

### 5.2 Prometheus Exporter

**用途**：暴露 Prometheus Metrics 端点

```yaml
exporters:
  prometheus:
    endpoint: 0.0.0.0:8889
    namespace: otel
    const_labels:
      environment: production
```

**访问示例**：

```bash
curl http://localhost:8889/metrics
```

---

### 5.3 Jaeger Exporter

**用途**：导出 Trace 到 Jaeger

```yaml
exporters:
  jaeger:
    endpoint: jaeger-collector:14250
    tls:
      insecure: true
```

---

## 6. Pipeline 配置与编排

### 6.1 基础配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  batch:
    timeout: 10s
    send_batch_size: 1024

exporters:
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
```

---

### 6.2 多 Pipeline 配置

```yaml
service:
  pipelines:
    # Trace Pipeline
    traces:
      receivers: [otlp]
      processors: [batch, resource, filter]
      exporters: [jaeger, otlp]
    
    # Metric Pipeline
    metrics:
      receivers: [otlp, prometheus]
      processors: [batch, resource]
      exporters: [prometheus]
    
    # Log Pipeline
    logs:
      receivers: [otlp]
      processors: [batch, attributes]
      exporters: [loki]
```

---

### 6.3 Pipeline 拓扑优化

**扇出模式**（一个数据源，多个后端）：

```yaml
service:
  pipelines:
    traces/sampling:
      receivers: [otlp]
      processors: [tail_sampling]
      exporters: [jaeger, otlp/production]
    
    traces/full:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/archive]
```

---

## 7. 部署模式

### 7.1 Agent 模式

**定义**：Collector 与应用部署在同一节点（Sidecar）

**优势**：

- 低延迟（本地通信）
- 故障隔离（单应用不影响全局）

**部署示例**（Kubernetes）：

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
spec:
  template:
    spec:
      containers:
        - name: app
          image: my-app:latest
          env:
            - name: OTEL_EXPORTER_OTLP_ENDPOINT
              value: "http://localhost:4317"
        
        - name: otel-agent
          image: otel/opentelemetry-collector:latest
          args: ["--config=/etc/otel/config.yaml"]
```

---

### 7.2 Gateway 模式

**定义**：集中式 Collector 集群

**优势**：

- 集中式管理（统一配置）
- 降低应用复杂度
- 支持高级功能（Tail Sampling）

**部署示例**：

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-gateway
spec:
  replicas: 3
  template:
    spec:
      containers:
        - name: otel-collector
          image: otel/opentelemetry-collector:latest
          resources:
            requests:
              memory: "2Gi"
              cpu: "1"
            limits:
              memory: "4Gi"
              cpu: "2"
```

---

### 7.3 混合模式

**定义**：Agent + Gateway 两层架构

```text
Application
    │
    ▼
Agent (Batch + Filter)
    │
    ▼
Gateway (Tail Sampling + Export)
    │
    ▼
Backend (Jaeger / Prometheus)
```

**配置示例**：

**Agent 配置**：

```yaml
exporters:
  otlp:
    endpoint: otel-gateway:4317
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, filter]
      exporters: [otlp]
```

**Gateway 配置**：

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    policies:
      - name: error-traces
        type: status_code
        status_code: {status_codes: [ERROR]}

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [tail_sampling]
      exporters: [jaeger]
```

---

## 8. 性能优化

### 8.1 内存管理

**配置示例**：

```yaml
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048
    spike_limit_mib: 512
```

**Go 运行时调优**：

```bash
GOMEMLIMIT=2GiB otelcol --config=/etc/otel/config.yaml
```

---

### 8.2 并发控制

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        max_concurrent_streams: 100

exporters:
  otlp:
    sending_queue:
      num_consumers: 10
      queue_size: 5000
```

---

### 8.3 背压处理

**问题**：后端处理速度 < 数据生成速度

**解决方案**：

```yaml
exporters:
  otlp:
    sending_queue:
      enabled: true
      queue_size: 10000
    retry_on_failure:
      enabled: true
      max_elapsed_time: 300s
```

---

## 9. 高可用与容错

### 9.1 负载均衡

**Kubernetes Service**：

```yaml
apiVersion: v1
kind: Service
metadata:
  name: otel-gateway
spec:
  type: LoadBalancer
  selector:
    app: otel-collector
  ports:
    - port: 4317
      targetPort: 4317
```

---

### 9.2 故障转移

**多后端配置**：

```yaml
exporters:
  otlp/primary:
    endpoint: primary-backend:4317
  
  otlp/fallback:
    endpoint: fallback-backend:4317

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/primary, otlp/fallback]
```

---

### 9.3 数据持久化

**File Exporter**（用于故障恢复）：

```yaml
exporters:
  file:
    path: /var/log/otel/traces.json
    rotation:
      max_megabytes: 100
      max_backups: 3

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger, file]
```

---

## 10. 监控与可观测性

### 10.1 自监控指标

**Prometheus Metrics**：

```yaml
service:
  telemetry:
    metrics:
      address: 0.0.0.0:8888
```

**关键指标**：

| 指标名称                                  | 说明                     |
|------------------------------------------|-------------------------|
| `otelcol_receiver_accepted_spans`        | 接收的 Span 数量         |
| `otelcol_processor_batch_batch_send_size` | 批量大小                |
| `otelcol_exporter_sent_spans`            | 导出的 Span 数量         |
| `otelcol_exporter_send_failed_spans`     | 导出失败的 Span 数量     |

---

### 10.2 健康检查

```yaml
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
```

**检查端点**：

```bash
curl http://localhost:13133
```

---

### 10.3 调试与排查

**开启 Debug 日志**：

```yaml
service:
  telemetry:
    logs:
      level: debug
```

---

## 11. Go 1.25.1 集成最佳实践

### 11.1 Go 应用 → Collector 配置

**Go 应用**：

```go
exporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint("localhost:4317"),
    otlptracegrpc.WithInsecure(),
)
```

**Collector 配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [jaeger]
```

---

### 11.2 容器化部署

**Dockerfile**：

```dockerfile
FROM otel/opentelemetry-collector:latest
COPY config.yaml /etc/otel/config.yaml
EXPOSE 4317 4318 8888
CMD ["--config=/etc/otel/config.yaml"]
```

---

### 11.3 Kubernetes 集成

**DaemonSet 部署**（Agent 模式）：

```yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-agent
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
        - name: otel-collector
          image: otel/opentelemetry-collector:latest
          env:
            - name: K8S_NODE_NAME
              valueFrom:
                fieldRef:
                  fieldPath: spec.nodeName
```

---

## 12. 工程案例

### 12.1 微服务可观测性平台

**架构**：

```text
┌─────────────┐   ┌─────────────┐   ┌─────────────┐
│  Service A  │   │  Service B  │   │  Service C  │
└──────┬──────┘   └──────┬──────┘   └──────┬──────┘
       │                 │                 │
       │ OTLP/gRPC       │ OTLP/gRPC       │ OTLP/gRPC
       ▼                 ▼                 ▼
┌───────────────────────────────────────────────────┐
│              OTel Gateway (3 replicas)            │
│  ┌──────────┐  ┌───────────────┐  ┌────────────┐ │
│  │  Batch   │─▶│ Tail Sampling │─▶│  Jaeger    │ │
│  └──────────┘  └───────────────┘  └────────────┘ │
└───────────────────────────────────────────────────┘
```

---

### 12.2 多租户数据隔离

```yaml
processors:
  resource:
    attributes:
      - key: tenant.id
        from_attribute: http.request.header.x-tenant-id
        action: upsert

exporters:
  otlp/tenant-a:
    endpoint: tenant-a-backend:4317
  
  otlp/tenant-b:
    endpoint: tenant-b-backend:4317

service:
  pipelines:
    traces/tenant-a:
      receivers: [otlp]
      processors: [filter/tenant-a, resource]
      exporters: [otlp/tenant-a]
    
    traces/tenant-b:
      receivers: [otlp]
      processors: [filter/tenant-b, resource]
      exporters: [otlp/tenant-b]
```

---

## 13. 总结

### 核心贡献

1. **架构分析**：
   - 深入解析 Receiver → Processor → Exporter 管道架构
   - 形式化定义 Pipeline 的数据转换过程

2. **部署模式**：
   - Agent vs Gateway 模式的设计权衡
   - 混合模式的两层架构设计

3. **性能优化**：
   - 内存管理、并发控制、背压处理策略
   - Batch Processor 提升 50% 吞吐量

4. **工程实践**：
   - Go 1.25.1 应用与 Collector 集成示例
   - Kubernetes 部署最佳实践

### 工程价值

| 价值维度       | 具体体现                                                                 |
|--------------|-------------------------------------------------------------------------|
| **解耦**       | 应用无需关心后端存储，Collector 统一处理                                    |
| **可扩展性**   | 插件化架构支持自定义 Receiver/Processor/Exporter                          |
| **高可用**     | 负载均衡 + 故障转移保证 99.9% 可用性                                       |
| **成本优化**   | Tail Sampling 降低 80% 存储成本                                           |

---

**下一步**：

- [Performance Optimization](./05-performance-optimization.md)
- [Distributed Tracing Theory](../distributed-model/01-distributed-tracing-theory.md)

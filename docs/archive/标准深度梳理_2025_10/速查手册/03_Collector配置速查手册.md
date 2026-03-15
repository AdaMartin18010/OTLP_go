# 📘 OpenTelemetry Collector配置速查手册

> **Collector版本**: v0.113.0  
> **最后更新**: 2025年10月9日  
> **用途**: 快速配置OpenTelemetry Collector

---

## 🎯 速查目录

- [📘 OpenTelemetry Collector配置速查手册](#-opentelemetry-collector配置速查手册)
  - [🎯 速查目录](#-速查目录)
  - [📋 配置结构](#-配置结构)
    - [基本结构](#基本结构)
    - [配置优先级](#配置优先级)
  - [📥 Receivers](#-receivers)
    - [OTLP Receiver (推荐)](#otlp-receiver-推荐)
    - [Prometheus Receiver](#prometheus-receiver)
    - [Jaeger Receiver](#jaeger-receiver)
    - [File Log Receiver](#file-log-receiver)
    - [Journald Receiver (Linux系统日志)](#journald-receiver-linux系统日志)
    - [Kafka Receiver](#kafka-receiver)
  - [⚙️ Processors](#️-processors)
    - [Batch Processor (必备)](#batch-processor-必备)
    - [Memory Limiter (推荐)](#memory-limiter-推荐)
    - [Resource Processor](#resource-processor)
    - [Attributes Processor](#attributes-processor)
    - [Tail Sampling Processor](#tail-sampling-processor)
    - [Filter Processor](#filter-processor)
    - [Transform Processor (v0.80.0+)](#transform-processor-v0800)
  - [📤 Exporters](#-exporters)
    - [OTLP Exporter](#otlp-exporter)
    - [OTLP/HTTP Exporter](#otlphttp-exporter)
    - [Prometheus Exporter](#prometheus-exporter)
    - [Logging Exporter (调试用)](#logging-exporter-调试用)
    - [File Exporter](#file-exporter)
    - [Kafka Exporter](#kafka-exporter)
    - [Loki Exporter (Logs)](#loki-exporter-logs)
  - [🔌 Extensions](#-extensions)
    - [Health Check](#health-check)
    - [PProf (性能分析)](#pprof-性能分析)
    - [zPages (调试页面)](#zpages-调试页面)
    - [File Storage](#file-storage)
  - [🔄 Service Pipeline](#-service-pipeline)
    - [完整Pipeline示例](#完整pipeline示例)
  - [📝 常用配置模板](#-常用配置模板)
    - [1. 简单网关模式](#1-简单网关模式)
    - [2. 生产级配置 (带采样和过滤)](#2-生产级配置-带采样和过滤)
    - [3. Kubernetes DaemonSet模式](#3-kubernetes-daemonset模式)
    - [4. 多后端导出](#4-多后端导出)
  - [🏗️ 部署模式](#️-部署模式)
    - [1. Agent模式 (应用侧边车)](#1-agent模式-应用侧边车)
    - [2. Gateway模式 (集中式)](#2-gateway模式-集中式)
    - [3. 混合模式 (推荐生产环境)](#3-混合模式-推荐生产环境)
  - [🔍 配置验证](#-配置验证)
    - [验证配置文件](#验证配置文件)
    - [测试连通性](#测试连通性)
  - [📊 性能调优](#-性能调优)
    - [调优参数速查](#调优参数速查)
    - [资源配置建议](#资源配置建议)
  - [🎯 最佳实践](#-最佳实践)
  - [📚 参考资源](#-参考资源)

---

## 📋 配置结构

### 基本结构

```yaml
# config.yaml
receivers:        # 接收器: 如何接收数据
  otlp:
    protocols:
      grpc:
      http:

processors:       # 处理器: 如何处理数据
  batch:
  memory_limiter:

exporters:        # 导出器: 如何发送数据
  otlp:
    endpoint: backend:4317

extensions:       # 扩展: 健康检查、监控等
  health_check:
  pprof:

service:          # 服务: 组装Pipeline
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
  extensions: [health_check]
```

### 配置优先级

```text
1. 命令行参数 (最高)
   --config=config.yaml

2. 环境变量
   ${OTEL_EXPORTER_OTLP_ENDPOINT}

3. 配置文件
   config.yaml
```

---

## 📥 Receivers

### OTLP Receiver (推荐)

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 4   # 最大消息大小4MB
        max_concurrent_streams: 16  # 最大并发流
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - http://localhost:*
            - https://*.example.com
          allowed_headers:
            - Content-Type
            - Authorization
```

### Prometheus Receiver

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'my-app'
          scrape_interval: 30s
          static_configs:
            - targets: ['localhost:8080']
```

### Jaeger Receiver

```yaml
receivers:
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
      thrift_http:
        endpoint: 0.0.0.0:14268
```

### File Log Receiver

```yaml
receivers:
  filelog:
    include:
      - /var/log/app/*.log
    start_at: end
    operators:
      - type: regex_parser
        regex: '^(?P<time>\S+) (?P<level>\S+) (?P<message>.*)$'
        timestamp:
          parse_from: attributes.time
          layout: '%Y-%m-%d %H:%M:%S'
```

### Journald Receiver (Linux系统日志)

```yaml
receivers:
  journald:
    directory: /var/log/journal
    units:
      - kubelet
      - docker
```

### Kafka Receiver

```yaml
receivers:
  kafka:
    protocol_version: 2.8.0
    brokers:
      - kafka:9092
    topic: otel-traces
    group_id: otel-collector
    auth:
      sasl:
        username: ${KAFKA_USER}
        password: ${KAFKA_PASSWORD}
        mechanism: PLAIN
```

---

## ⚙️ Processors

### Batch Processor (必备)

```yaml
processors:
  batch:
    timeout: 10s               # 批处理超时
    send_batch_size: 1024      # 批次大小
    send_batch_max_size: 2048  # 最大批次
```

### Memory Limiter (推荐)

```yaml
processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 512           # 内存上限512MB
    spike_limit_mib: 128     # 峰值限制128MB
```

### Resource Processor

```yaml
processors:
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: upsert
      - key: service.namespace
        value: ecommerce
        action: insert
      - key: internal.token
        action: delete  # 删除敏感字段
```

### Attributes Processor

```yaml
processors:
  attributes:
    actions:
      - key: http.request.header.authorization
        action: delete  # 删除敏感头
      - key: user.id
        from_attribute: http.request.header.x-user-id
        action: extract  # 提取属性
      - key: http.url
        pattern: ^(.*)\?.*$
        action: extract  # 正则提取(去除查询字符串)
```

### Tail Sampling Processor

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    num_traces: 100
    expected_new_traces_per_sec: 10
    policies:
      # 策略1: 保留所有错误
      - name: errors-policy
        type: status_code
        status_code:
          status_codes:
            - ERROR
      
      # 策略2: 保留慢请求 (>500ms)
      - name: slow-traces-policy
        type: latency
        latency:
          threshold_ms: 500
      
      # 策略3: 采样10%正常请求
      - name: probabilistic-policy
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
```

### Filter Processor

```yaml
processors:
  filter:
    traces:
      span:
        - attributes["http.target"] == "/health"  # 过滤健康检查
        - attributes["http.target"] == "/ready"
    metrics:
      metric:
        - name == "http.server.active_requests"
          resource.attributes["service.name"] == "test-service"
```

### Transform Processor (v0.80.0+)

```yaml
processors:
  transform:
    trace_statements:
      - context: span
        statements:
          # 去除查询字符串
          - set(attributes["http.url"], split(attributes["http.url"], "?")[0])
          # 重命名属性
          - set(attributes["http.method"], attributes["http.request.method"])
          - delete_key(attributes, "http.request.method")
```

---

## 📤 Exporters

### OTLP Exporter

```yaml
exporters:
  otlp:
    endpoint: backend:4317
    compression: gzip  # 或 zstd
    timeout: 30s
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
```

### OTLP/HTTP Exporter

```yaml
exporters:
  otlphttp:
    endpoint: https://backend:4318
    headers:
      Authorization: Bearer ${API_TOKEN}
    compression: gzip
    timeout: 30s
```

### Prometheus Exporter

```yaml
exporters:
  prometheus:
    endpoint: 0.0.0.0:8889
    namespace: otel
    const_labels:
      environment: production
```

### Logging Exporter (调试用)

```yaml
exporters:
  logging:
    verbosity: detailed
    sampling_initial: 5    # 初始采样5条
    sampling_thereafter: 200  # 之后每200条采样1条
```

### File Exporter

```yaml
exporters:
  file:
    path: /var/log/otel/traces.json
    rotation:
      max_megabytes: 100
      max_days: 7
      max_backups: 3
```

### Kafka Exporter

```yaml
exporters:
  kafka:
    protocol_version: 2.8.0
    brokers:
      - kafka:9092
    topic: otel-traces
    encoding: otlp_proto  # 或 otlp_json
    compression: gzip
    auth:
      sasl:
        username: ${KAFKA_USER}
        password: ${KAFKA_PASSWORD}
```

### Loki Exporter (Logs)

```yaml
exporters:
  loki:
    endpoint: http://loki:3100/loki/api/v1/push
    labels:
      attributes:
        service.name: "service_name"
        log.level: "level"
```

---

## 🔌 Extensions

### Health Check

```yaml
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health
```

### PProf (性能分析)

```yaml
extensions:
  pprof:
    endpoint: 0.0.0.0:1777
```

### zPages (调试页面)

```yaml
extensions:
  zpages:
    endpoint: 0.0.0.0:55679
```

### File Storage

```yaml
extensions:
  file_storage:
    directory: /var/lib/otel/storage
    timeout: 1s
```

---

## 🔄 Service Pipeline

### 完整Pipeline示例

```yaml
service:
  extensions:
    - health_check
    - pprof
    - zpages
  
  pipelines:
    traces:
      receivers: [otlp, jaeger]
      processors:
        - memory_limiter
        - batch
        - resource
        - tail_sampling
      exporters: [otlp, logging]
    
    metrics:
      receivers: [otlp, prometheus]
      processors:
        - memory_limiter
        - batch
        - filter
      exporters: [otlp, prometheus]
    
    logs:
      receivers: [otlp, filelog]
      processors:
        - memory_limiter
        - batch
        - attributes
      exporters: [otlp, loki]
  
  telemetry:
    logs:
      level: info
      encoding: json
      output_paths:
        - stdout
        - /var/log/otel-collector.log
    metrics:
      level: detailed
      address: 0.0.0.0:8888
```

---

## 📝 常用配置模板

### 1. 简单网关模式

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
  memory_limiter:
    check_interval: 1s
    limit_mib: 512

exporters:
  otlp:
    endpoint: backend:4317
    compression: gzip

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp]
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp]
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [otlp]
```

### 2. 生产级配置 (带采样和过滤)

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 4
      http:
        endpoint: 0.0.0.0:4318

processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048
    spike_limit_mib: 512
  
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: upsert
      - key: cluster.name
        value: ${CLUSTER_NAME}
        action: upsert
  
  batch:
    timeout: 10s
    send_batch_size: 2048
    send_batch_max_size: 4096
  
  tail_sampling:
    decision_wait: 10s
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: slow
        type: latency
        latency: {threshold_ms: 500}
      - name: sample-10pct
        type: probabilistic
        probabilistic: {sampling_percentage: 10}
  
  filter:
    traces:
      span:
        - attributes["http.target"] == "/health"

exporters:
  otlp:
    endpoint: ${OTLP_ENDPOINT}
    compression: gzip
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
    sending_queue:
      enabled: true
      num_consumers: 20
      queue_size: 10000

extensions:
  health_check:
    endpoint: 0.0.0.0:13133

service:
  extensions: [health_check]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, filter, tail_sampling, batch]
      exporters: [otlp]
  telemetry:
    logs:
      level: info
    metrics:
      address: 0.0.0.0:8888
```

### 3. Kubernetes DaemonSet模式

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
  
  # 收集K8s日志
  filelog:
    include:
      - /var/log/pods/*/*/*.log
    start_at: end
    include_file_path: true
    operators:
      - type: router
        id: get-format
        routes:
          - output: parser-docker
            expr: 'body matches "^\\{"'
          - output: parser-crio
            expr: 'body matches "^[^ Z]+ "'
      
      - type: json_parser
        id: parser-docker
        output: extract_metadata_from_filepath
        timestamp:
          parse_from: attributes.time
          layout: '%Y-%m-%dT%H:%M:%S.%LZ'
      
      - type: regex_parser
        id: parser-crio
        regex: '^(?P<time>[^ Z]+) (?P<stream>stdout|stderr) (?P<logtag>[^ ]*) (?P<log>.*)$'
        output: extract_metadata_from_filepath
        timestamp:
          parse_from: attributes.time
          layout: '%Y-%m-%dT%H:%M:%S.%L%z'
      
      - type: regex_parser
        id: extract_metadata_from_filepath
        regex: '^.*\/(?P<namespace>[^_]+)_(?P<pod_name>[^_]+)_(?P<uid>[a-f0-9\-]+)\/(?P<container_name>[^\._]+)\/(?P<restart_count>\d+)\.log$'
        parse_from: attributes["log.file.path"]

processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
  
  k8sattributes:
    auth_type: serviceAccount
    passthrough: false
    extract:
      metadata:
        - k8s.namespace.name
        - k8s.pod.name
        - k8s.pod.uid
        - k8s.deployment.name
        - k8s.node.name
      labels:
        - tag_name: app
          key: app.kubernetes.io/name
          from: pod
  
  resource:
    attributes:
      - key: cluster.name
        value: ${K8S_CLUSTER_NAME}
        action: insert
  
  batch:
    timeout: 10s
    send_batch_size: 1024

exporters:
  otlp:
    endpoint: ${OTLP_ENDPOINT}
    compression: gzip

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, k8sattributes, resource, batch]
      exporters: [otlp]
    logs:
      receivers: [filelog, otlp]
      processors: [memory_limiter, k8sattributes, resource, batch]
      exporters: [otlp]
```

### 4. 多后端导出

```yaml
exporters:
  # 导出到SaaS后端
  otlp/saas:
    endpoint: saas-backend.example.com:4317
    headers:
      Authorization: Bearer ${SAAS_API_KEY}
    compression: gzip
  
  # 导出到内部Jaeger
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true
  
  # 导出到Prometheus
  prometheus:
    endpoint: 0.0.0.0:8889
  
  # 导出到Loki
  loki:
    endpoint: http://loki:3100/loki/api/v1/push

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/saas, otlp/jaeger]  # 多目标
    
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/saas, prometheus]
    
    logs:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/saas, loki]
```

---

## 🏗️ 部署模式

### 1. Agent模式 (应用侧边车)

```text
应用 → Collector (Agent) → Collector (Gateway) → 后端

特点:
✅ 低延迟
✅ 本地批处理
✅ 资源开销小
⚠️ 每个应用实例1个Agent

资源配置:
  CPU: 0.1-0.2 cores
  Memory: 128-256 MB
```

### 2. Gateway模式 (集中式)

```text
应用群 → Collector (Gateway) → 后端

特点:
✅ 集中管理
✅ 统一采样策略
✅ 减少后端连接数
⚠️ 单点故障风险

资源配置:
  CPU: 2-4 cores
  Memory: 4-8 GB
  副本: 2-3个 (HA)
```

### 3. 混合模式 (推荐生产环境)

```text
应用 → Collector (Agent) → Collector (Gateway) → 后端

特点:
✅ Agent做本地批处理和过滤
✅ Gateway做采样和路由
✅ 高可用性
✅ 灵活扩展

Agent配置:
  CPU: 0.1 cores
  Memory: 128 MB
  processors: [batch, filter]

Gateway配置:
  CPU: 2-4 cores
  Memory: 4-8 GB
  processors: [tail_sampling, load_balancing]
```

---

## 🔍 配置验证

### 验证配置文件

```bash
# 验证语法
otelcol validate --config=config.yaml

# 干运行
otelcol --config=config.yaml --dry-run
```

### 测试连通性

```bash
# 测试OTLP gRPC端点
grpcurl -plaintext localhost:4317 list

# 测试OTLP HTTP端点
curl -X POST http://localhost:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[]}'

# 测试健康检查
curl http://localhost:13133/health
```

---

## 📊 性能调优

### 调优参数速查

| 场景 | 推荐配置 |
|-----|---------|
| **低延迟** | `batch.timeout=1s`, `send_batch_size=256` |
| **高吞吐** | `batch.timeout=10s`, `send_batch_size=2048` |
| **内存受限** | `memory_limiter.limit_mib=256`, `queue_size=2000` |
| **网络受限** | `compression=gzip`, `retry.enabled=true` |

### 资源配置建议

```yaml
# 小规模 (<100 req/s)
memory_limiter:
  limit_mib: 256
batch:
  send_batch_size: 512
sending_queue:
  queue_size: 2000

# 中等规模 (100-1000 req/s)
memory_limiter:
  limit_mib: 1024
batch:
  send_batch_size: 1024
sending_queue:
  queue_size: 5000

# 大规模 (>1000 req/s)
memory_limiter:
  limit_mib: 4096
batch:
  send_batch_size: 2048
sending_queue:
  queue_size: 10000
```

---

## 🎯 最佳实践

```text
✅ 始终使用memory_limiter防止OOM
✅ 始终使用batch提升性能
✅ 生产环境启用health_check
✅ 使用环境变量管理敏感信息 (${API_KEY})
✅ 配置retry_on_failure确保数据可靠
✅ Gateway模式部署2+副本
✅ 监控Collector自身指标 (8888端口)
✅ 过滤健康检查等噪音数据
✅ 使用tail_sampling降低成本
✅ 定期更新Collector到最新稳定版
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **Collector文档** | <https://opentelemetry.io/docs/collector/> |
| **配置参考** | <https://opentelemetry.io/docs/collector/configuration/> |
| **Processor列表** | <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor> |
| **Receiver列表** | <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver> |
| **Exporter列表** | <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter> |

---

**最后更新**: 2025年10月9日  
**上一篇**: [Semantic Conventions速查手册](./02_Semantic_Conventions速查手册.md)  
**下一篇**: [故障排查速查手册](./04_故障排查速查手册.md)

# Collector Exporter 配置详解

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Collector Exporter 配置详解](#collector-exporter-配置详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. OTLP Exporter](#2-otlp-exporter)
    - [2.1 基础配置](#21-基础配置)
    - [2.2 TLS与认证](#22-tls与认证)
    - [2.3 重试与超时](#23-重试与超时)
    - [2.4 负载均衡](#24-负载均衡)
  - [3. Prometheus Exporter](#3-prometheus-exporter)
  - [4. Kafka Exporter](#4-kafka-exporter)
    - [4.1 基础配置](#41-基础配置)
    - [4.2 生产者配置](#42-生产者配置)
  - [5. Logging Exporter](#5-logging-exporter)
  - [6. File Exporter](#6-file-exporter)
  - [7. 商业后端Exporter](#7-商业后端exporter)
    - [7.1 Jaeger Exporter](#71-jaeger-exporter)
    - [7.2 Zipkin Exporter](#72-zipkin-exporter)
    - [7.3 Elasticsearch Exporter](#73-elasticsearch-exporter)
    - [7.4 AWS X-Ray Exporter](#74-aws-x-ray-exporter)
  - [8. Exporter最佳实践](#8-exporter最佳实践)
    - [8.1 高可用配置](#81-高可用配置)
    - [8.2 性能优化](#82-性能优化)
    - [8.3 错误处理](#83-错误处理)
  - [9. 完整配置示例](#9-完整配置示例)
    - [9.1 多后端导出配置](#91-多后端导出配置)
    - [9.2 生产环境HA配置](#92-生产环境ha配置)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [核心Exporter文档](#核心exporter文档)

---

## 1. 概述

**Exporter**是Collector的数据导出组件，负责将处理后的遥测数据发送到各种后端系统。

**处理流程**：

```text
Receiver → Processor → Exporter → 后端系统
```

**核心Exporter类型**：

```text
✅ otlp:            OpenTelemetry原生协议
✅ prometheus:      Prometheus远程写入
✅ prometheusremotewrite: Prometheus Remote Write
✅ kafka:           Kafka消息队列
✅ logging:         控制台日志输出
✅ file:            文件导出
✅ jaeger:          Jaeger后端
✅ zipkin:          Zipkin后端
✅ elasticsearch:   Elasticsearch
✅ awsxray:         AWS X-Ray
```

---

## 2. OTLP Exporter

**用途**: 将数据导出到支持OTLP协议的后端（如其他Collector、Jaeger、Grafana Tempo等）。

### 2.1 基础配置

```yaml
exporters:
  otlp:
    # 后端端点
    endpoint: otel-collector:4317
    
    # TLS设置
    tls:
      # 是否不安全连接
      insecure: false
      # CA证书
      ca_file: /path/to/ca.pem
      # 客户端证书
      cert_file: /path/to/cert.pem
      key_file: /path/to/key.pem
      # 跳过证书验证（不推荐生产环境）
      insecure_skip_verify: false
    
    # 压缩
    compression: gzip
    
    # 超时
    timeout: 30s
```

### 2.2 TLS与认证

**Bearer Token认证**：

```yaml
exporters:
  otlp:
    endpoint: backend.example.com:4317
    tls:
      insecure: false
    headers:
      authorization: "Bearer ${OTEL_API_TOKEN}"
```

**Basic认证**：

```yaml
exporters:
  otlp:
    endpoint: backend.example.com:4317
    tls:
      insecure: false
    headers:
      authorization: "Basic ${BASE64_CREDENTIALS}"
```

**mTLS配置**：

```yaml
exporters:
  otlp:
    endpoint: backend.example.com:4317
    tls:
      insecure: false
      ca_file: /certs/ca.pem
      cert_file: /certs/client-cert.pem
      key_file: /certs/client-key.pem
```

### 2.3 重试与超时

**完整重试配置**：

```yaml
exporters:
  otlp:
    endpoint: backend.example.com:4317
    
    # 超时配置
    timeout: 30s
    
    # 重试配置
    retry_on_failure:
      # 启用重试
      enabled: true
      # 初始间隔
      initial_interval: 5s
      # 最大间隔
      max_interval: 30s
      # 最大经过时间
      max_elapsed_time: 300s
    
    # 发送队列配置
    sending_queue:
      # 启用持久化队列
      enabled: true
      # 队列大小
      num_consumers: 10
      # 队列容量
      queue_size: 5000
      # 存储目录（持久化）
      storage: file_storage
```

### 2.4 负载均衡

**多端点配置**：

```yaml
exporters:
  # 主后端
  otlp/primary:
    endpoint: backend-1.example.com:4317
    tls:
      insecure: false
  
  # 备份后端
  otlp/backup:
    endpoint: backend-2.example.com:4317
    tls:
      insecure: false

# 使用loadbalancing exporter
exporters:
  loadbalancing:
    protocol:
      otlp:
        timeout: 10s
        tls:
          insecure: false
    resolver:
      static:
        hostnames:
          - backend-1.example.com:4317
          - backend-2.example.com:4317
```

---

## 3. Prometheus Exporter

**用途**: 暴露Prometheus格式的指标端点。

```yaml
exporters:
  # Prometheus导出器（暴露/metrics端点）
  prometheus:
    # 监听端点
    endpoint: "0.0.0.0:8889"
    # 命名空间
    namespace: "otel"
    # 常量标签
    const_labels:
      environment: production
      cluster: us-east-1
    
    # 资源到标签映射
    resource_to_telemetry_conversion:
      enabled: true
```

**Prometheus Remote Write**：

```yaml
exporters:
  prometheusremotewrite:
    # Remote Write端点
    endpoint: "https://prometheus.example.com/api/v1/write"
    
    # HTTP配置
    tls:
      insecure: false
      ca_file: /path/to/ca.pem
    
    # 认证
    headers:
      Authorization: "Bearer ${PROM_TOKEN}"
    
    # 重试配置
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
    
    # 资源属性作为标签
    resource_to_telemetry_conversion:
      enabled: true
```

---

## 4. Kafka Exporter

**用途**: 将遥测数据发送到Kafka消息队列。

### 4.1 基础配置

```yaml
exporters:
  kafka:
    # Kafka broker地址
    brokers:
      - kafka1.example.com:9092
      - kafka2.example.com:9092
      - kafka3.example.com:9092
    
    # 目标topic
    topic: otlp-traces
    
    # 编码格式
    encoding: otlp_proto
    
    # 协议版本
    protocol_version: 2.0.0
```

### 4.2 生产者配置

**高级配置**：

```yaml
exporters:
  kafka:
    brokers:
      - kafka.example.com:9092
    topic: otlp-traces
    encoding: otlp_proto
    
    # 认证
    auth:
      sasl:
        username: otel-producer
        password: ${KAFKA_PASSWORD}
        mechanism: SCRAM-SHA-512
      tls:
        insecure: false
        ca_file: /certs/ca.pem
    
    # 生产者配置
    producer:
      # 最大消息字节
      max_message_bytes: 10000000
      # 压缩类型
      compression: gzip
      # 确认级别
      required_acks: 1
      # 重试次数
      retry:
        max_retries: 3
        backoff: 100ms
    
    # 元数据
    metadata:
      full: false
      retry:
        max: 3
        backoff: 250ms
    
    # 超时
    timeout: 10s
```

**分topic导出**：

```yaml
exporters:
  # Traces到Kafka
  kafka/traces:
    brokers: [kafka.example.com:9092]
    topic: otlp-traces
    encoding: otlp_proto
  
  # Metrics到Kafka
  kafka/metrics:
    brokers: [kafka.example.com:9092]
    topic: otlp-metrics
    encoding: otlp_proto
  
  # Logs到Kafka
  kafka/logs:
    brokers: [kafka.example.com:9092]
    topic: otlp-logs
    encoding: otlp_proto
```

---

## 5. Logging Exporter

**用途**: 将遥测数据输出到控制台日志（用于调试）。

```yaml
exporters:
  logging:
    # 日志级别
    loglevel: debug
    # 采样初始值
    sampling_initial: 5
    # 采样后续值
    sampling_thereafter: 200
```

**详细输出配置**：

```yaml
exporters:
  logging:
    loglevel: debug
    # 输出详细信息
    verbosity: detailed
```

---

## 6. File Exporter

**用途**: 将遥测数据导出到文件。

```yaml
exporters:
  file:
    # 输出文件路径
    path: /var/log/otel/traces.json
    
    # 格式（json/proto）
    format: json
    
    # 压缩
    compression: gzip
    
    # 轮转配置
    rotation:
      # 最大文件大小（MB）
      max_megabytes: 100
      # 最大备份数
      max_backups: 10
      # 最大保留天数
      max_days: 7
```

---

## 7. 商业后端Exporter

### 7.1 Jaeger Exporter

```yaml
exporters:
  jaeger:
    # Jaeger gRPC端点
    endpoint: jaeger-collector:14250
    
    # TLS配置
    tls:
      insecure: false
      ca_file: /certs/ca.pem
    
    # 超时
    timeout: 10s
```

### 7.2 Zipkin Exporter

```yaml
exporters:
  zipkin:
    # Zipkin端点
    endpoint: http://zipkin:9411/api/v2/spans
    
    # 格式（json/proto）
    format: json
    
    # 超时
    timeout: 10s
```

### 7.3 Elasticsearch Exporter

```yaml
exporters:
  elasticsearch:
    # Elasticsearch端点
    endpoints:
      - https://elasticsearch:9200
    
    # 认证
    auth:
      authenticator: basicauth
    
    # 索引配置
    logs_index: otel-logs
    traces_index: otel-traces
    
    # 批量配置
    bulk:
      max_size: 5000
      flush_interval: 30s
    
    # 重试
    retry:
      enabled: true
      max_requests: 5
      initial_interval: 100ms
      max_interval: 1m

extensions:
  basicauth:
    client_auth:
      username: elastic
      password: ${ES_PASSWORD}
```

### 7.4 AWS X-Ray Exporter

```yaml
exporters:
  awsxray:
    # AWS区域
    region: us-east-1
    
    # 端点（可选）
    endpoint: ""
    
    # 索引全属性
    index_all_attributes: true
    
    # 索引的属性
    indexed_attributes:
      - http.method
      - http.status_code
      - error
    
    # IAM角色ARN
    role_arn: "arn:aws:iam::123456789012:role/OtelCollectorRole"
```

---

## 8. Exporter最佳实践

### 8.1 高可用配置

**主备配置**：

```yaml
exporters:
  # 主后端
  otlp/primary:
    endpoint: primary-backend:4317
    timeout: 10s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
  
  # 备份后端
  otlp/backup:
    endpoint: backup-backend:4317
    timeout: 10s
    retry_on_failure:
      enabled: true
      initial_interval: 5s

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      # 主备同时导出
      exporters: [otlp/primary, otlp/backup]
```

### 8.2 性能优化

**批处理与压缩**：

```yaml
processors:
  batch:
    timeout: 10s
    send_batch_size: 10000
    send_batch_max_size: 20000

exporters:
  otlp:
    endpoint: backend:4317
    # 启用压缩
    compression: gzip
    # 优化超时
    timeout: 30s
    # 并发发送
    sending_queue:
      enabled: true
      num_consumers: 20
      queue_size: 10000
```

### 8.3 错误处理

**持久化队列配置**：

```yaml
extensions:
  file_storage:
    directory: /var/lib/otelcol/queue
    timeout: 10s

exporters:
  otlp:
    endpoint: backend:4317
    
    # 重试配置
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    
    # 持久化队列
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
      # 使用文件存储
      storage: file_storage

service:
  extensions: [file_storage]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
```

---

## 9. 完整配置示例

### 9.1 多后端导出配置

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
    send_batch_size: 8192
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048

exporters:
  # 1. OTLP后端（主要）
  otlp/primary:
    endpoint: backend.example.com:4317
    tls:
      insecure: false
      ca_file: /certs/ca.pem
    headers:
      authorization: "Bearer ${OTEL_TOKEN}"
    compression: gzip
    timeout: 30s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
  
  # 2. Prometheus Remote Write
  prometheusremotewrite:
    endpoint: "https://prometheus.example.com/api/v1/write"
    headers:
      Authorization: "Bearer ${PROM_TOKEN}"
    resource_to_telemetry_conversion:
      enabled: true
  
  # 3. Kafka归档
  kafka:
    brokers: [kafka.example.com:9092]
    topic: otlp-telemetry
    encoding: otlp_proto
    compression: gzip
  
  # 4. Jaeger（遗留系统）
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  # 5. Logging（调试）
  logging:
    loglevel: info
    sampling_initial: 10
    sampling_thereafter: 1000

service:
  pipelines:
    # Traces Pipeline
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters:
        - otlp/primary      # 主后端
        - jaeger            # 遗留系统
        - kafka             # 归档
        - logging           # 调试
    
    # Metrics Pipeline
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters:
        - otlp/primary              # 主后端
        - prometheusremotewrite     # Prometheus
        - kafka                      # 归档
    
    # Logs Pipeline
    logs:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters:
        - otlp/primary      # 主后端
        - kafka             # 归档
```

### 9.2 生产环境HA配置

```yaml
extensions:
  # 持久化存储
  file_storage:
    directory: /var/lib/otelcol
    timeout: 10s
  
  # 健康检查
  health_check:
    endpoint: 0.0.0.0:13133
  
  # PPROFextensions
  pprof:
    endpoint: 0.0.0.0:1777

receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 16
        max_concurrent_streams: 500

processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048
    spike_limit_mib: 512
  
  batch:
    timeout: 10s
    send_batch_size: 8192
    send_batch_max_size: 16384
  
  # 资源检测
  resourcedetection:
    detectors: [env, system]
    timeout: 5s

exporters:
  # 主后端集群
  otlp/primary:
    endpoint: primary-backend.example.com:4317
    tls:
      insecure: false
      ca_file: /certs/ca.pem
    headers:
      authorization: "Bearer ${OTEL_PRIMARY_TOKEN}"
    compression: gzip
    timeout: 30s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 20
      queue_size: 10000
      storage: file_storage
  
  # 备份后端
  otlp/backup:
    endpoint: backup-backend.example.com:4317
    tls:
      insecure: false
      ca_file: /certs/ca.pem
    headers:
      authorization: "Bearer ${OTEL_BACKUP_TOKEN}"
    compression: gzip
    timeout: 30s
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
      storage: file_storage
  
  # Kafka归档（长期存储）
  kafka/archive:
    brokers:
      - kafka1.example.com:9092
      - kafka2.example.com:9092
      - kafka3.example.com:9092
    topic: otlp-telemetry-archive
    encoding: otlp_proto
    compression: gzip
    producer:
      max_message_bytes: 10000000
      required_acks: 1
    auth:
      sasl:
        username: otel-producer
        password: ${KAFKA_PASSWORD}
        mechanism: SCRAM-SHA-512
      tls:
        insecure: false
        ca_file: /certs/kafka-ca.pem

service:
  extensions: [file_storage, health_check, pprof]
  
  pipelines:
    traces:
      receivers: [otlp]
      processors:
        - memory_limiter
        - resourcedetection
        - batch
      exporters:
        - otlp/primary    # 主后端（实时）
        - otlp/backup     # 备份后端（实时）
        - kafka/archive   # Kafka（归档）
    
    metrics:
      receivers: [otlp]
      processors:
        - memory_limiter
        - resourcedetection
        - batch
      exporters:
        - otlp/primary
        - otlp/backup
        - kafka/archive
    
    logs:
      receivers: [otlp]
      processors:
        - memory_limiter
        - resourcedetection
        - batch
      exporters:
        - otlp/primary
        - otlp/backup
        - kafka/archive
  
  telemetry:
    logs:
      level: info
    metrics:
      address: 0.0.0.0:8888
```

---

## 10. 参考资源

### 官方文档

- **Exporter Overview**: <https://opentelemetry.io/docs/collector/configuration/#exporters>
- **Exporter Repository**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter>

### 核心Exporter文档

- **OTLP Exporter**: <https://github.com/open-telemetry/opentelemetry-collector/tree/main/exporter/otlpexporter>
- **Prometheus Exporter**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter/prometheusexporter>
- **Kafka Exporter**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter/kafkaexporter>
- **Jaeger Exporter**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter/jaegerexporter>
- **Elasticsearch Exporter**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/exporter/elasticsearchexporter>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

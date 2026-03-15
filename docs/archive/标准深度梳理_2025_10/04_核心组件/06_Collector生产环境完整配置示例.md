# OpenTelemetry Collector 生产环境完整配置示例

> **适用版本**: OpenTelemetry Collector v0.90.0+  
> **配置类型**: 生产级高可用部署  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry Collector 生产环境完整配置示例](#opentelemetry-collector-生产环境完整配置示例)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 单节点生产配置](#2-单节点生产配置)
    - [2.1 基础配置结构](#21-基础配置结构)
    - [2.2 完整配置文件](#22-完整配置文件)
  - [3. 高可用集群配置](#3-高可用集群配置)
    - [3.1 架构设计](#31-架构设计)
    - [3.2 Gateway Collector配置](#32-gateway-collector配置)
    - [3.3 Agent Collector配置](#33-agent-collector配置)
  - [4. 云平台部署配置](#4-云平台部署配置)
    - [4.1 Kubernetes部署](#41-kubernetes部署)
    - [4.2 Docker Compose部署](#42-docker-compose部署)
    - [4.3 AWS ECS部署](#43-aws-ecs部署)
  - [5. 性能优化配置](#5-性能优化配置)
    - [5.1 批处理优化](#51-批处理优化)
    - [5.2 内存管理](#52-内存管理)
    - [5.3 并发控制](#53-并发控制)
  - [6. 安全加固配置](#6-安全加固配置)
    - [6.1 TLS/mTLS配置](#61-tlsmtls配置)
    - [6.2 认证与授权](#62-认证与授权)
  - [7. 监控与可观测性](#7-监控与可观测性)
    - [7.1 Collector自监控](#71-collector自监控)
    - [7.2 健康检查](#72-健康检查)
  - [8. 场景化配置模板](#8-场景化配置模板)
    - [8.1 微服务追踪](#81-微服务追踪)
    - [8.2 日志聚合](#82-日志聚合)
    - [8.3 指标采集](#83-指标采集)
  - [9. 故障排查配置](#9-故障排查配置)
  - [10. 参考资源](#10-参考资源)

---

## 1. 概述

本文档提供OpenTelemetry Collector在生产环境中的完整配置示例，涵盖：

```text
✅ 单节点生产配置
✅ 高可用集群架构
✅ Kubernetes/Docker/云平台部署
✅ 性能优化与资源管理
✅ 安全加固与合规
✅ 监控与故障排查
```

---

## 2. 单节点生产配置

### 2.1 基础配置结构

```text
collector-config.yaml
├── receivers     # 数据接收器
├── processors    # 数据处理器
├── exporters     # 数据导出器
├── connectors    # 管道连接器
├── extensions    # 扩展组件
└── service       # 服务配置
    ├── pipelines # 数据管道
    ├── telemetry # 自监控
    └── extensions# 启用的扩展
```

### 2.2 完整配置文件

```yaml
# collector-production.yaml

# ============================================================
# 接收器配置
# ============================================================
receivers:
  # OTLP接收器 - 接收来自SDK的数据
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 4  # 4MB
        max_concurrent_streams: 100
        read_buffer_size: 524288  # 512KB
        write_buffer_size: 524288
        keepalive:
          server_parameters:
            max_connection_idle: 11s
            max_connection_age: 30s
            max_connection_age_grace: 5s
            time: 30s
            timeout: 5s
          enforcement_policy:
            min_time: 5s
            permit_without_stream: true
        # TLS配置（生产环境必需）
        tls:
          cert_file: /etc/otelcol/certs/server.crt
          key_file: /etc/otelcol/certs/server.key
          client_ca_file: /etc/otelcol/certs/ca.crt
          min_version: "1.3"
      
      http:
        endpoint: 0.0.0.0:4318
        max_request_body_size: 4194304  # 4MB
        include_metadata: true
        # CORS配置
        cors:
          allowed_origins:
            - https://app.example.com
            - https://dashboard.example.com
          allowed_headers:
            - "*"
          max_age: 7200
        # TLS配置
        tls:
          cert_file: /etc/otelcol/certs/server.crt
          key_file: /etc/otelcol/certs/server.key
          min_version: "1.3"

  # Prometheus接收器 - 抓取Prometheus格式指标
  prometheus:
    config:
      scrape_configs:
        - job_name: 'kubernetes-pods'
          kubernetes_sd_configs:
            - role: pod
          relabel_configs:
            - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
              action: keep
              regex: true
            - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
              action: replace
              target_label: __metrics_path__
              regex: (.+)
            - source_labels: [__address__, __meta_kubernetes_pod_annotation_prometheus_io_port]
              action: replace
              regex: ([^:]+)(?::\d+)?;(\d+)
              replacement: $1:$2
              target_label: __address__

  # Jaeger接收器 - 兼容Jaeger协议
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

  # Zipkin接收器 - 兼容Zipkin协议
  zipkin:
    endpoint: 0.0.0.0:9411

  # Kafka接收器 - 从Kafka消费数据
  kafka:
    protocol_version: 2.0.0
    brokers:
      - kafka-1.example.com:9092
      - kafka-2.example.com:9092
      - kafka-3.example.com:9092
    topic: otel-traces
    group_id: otel-collector
    encoding: otlp_proto
    auth:
      sasl:
        username: ${KAFKA_USERNAME}
        password: ${KAFKA_PASSWORD}
        mechanism: SCRAM-SHA-512
      tls:
        ca_file: /etc/otelcol/kafka/ca.crt
        cert_file: /etc/otelcol/kafka/client.crt
        key_file: /etc/otelcol/kafka/client.key

  # Filelog接收器 - 采集日志文件
  filelog:
    include:
      - /var/log/app/*.log
    exclude:
      - /var/log/app/*.gz
    start_at: end
    include_file_path: true
    include_file_name: false
    operators:
      # JSON解析
      - type: json_parser
        parse_from: body
        timestamp:
          parse_from: attributes.timestamp
          layout: '%Y-%m-%dT%H:%M:%S.%LZ'
      # 严重性映射
      - type: severity_parser
        parse_from: attributes.level
        mapping:
          debug: debug
          info: info
          warn: warn
          error: error
          fatal: fatal

  # Hostmetrics接收器 - 采集主机指标
  hostmetrics:
    collection_interval: 30s
    scrapers:
      cpu:
        metrics:
          system.cpu.utilization:
            enabled: true
      memory:
        metrics:
          system.memory.utilization:
            enabled: true
      disk:
        metrics:
          system.disk.io:
            enabled: true
      network:
        metrics:
          system.network.io:
            enabled: true
      process:
        mute_process_name_error: true
        metrics:
          process.cpu.utilization:
            enabled: true

# ============================================================
# 处理器配置
# ============================================================
processors:
  # Batch处理器 - 批量处理数据（性能关键）
  batch:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048

  # Memory Limiter - 内存保护（防止OOM）
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048  # 2GB
    spike_limit_mib: 512  # 允许512MB突发

  # Resource处理器 - 添加资源属性
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: upsert
      - key: service.namespace
        value: ecommerce
        action: upsert
      - key: cloud.provider
        value: aws
        action: upsert
      - key: cloud.region
        value: us-east-1
        action: upsert

  # Resource Detection - 自动检测资源信息
  resourcedetection:
    detectors:
      - env
      - system
      - docker
      - ec2
      - ecs
    timeout: 5s
    override: false

  # Attributes处理器 - 操作属性
  attributes/add:
    actions:
      - key: environment
        value: prod
        action: insert
      - key: collector.version
        value: 0.90.0
        action: insert

  # Filter处理器 - 过滤数据
  filter/health:
    traces:
      span:
        - 'attributes["http.target"] == "/health"'
        - 'attributes["http.target"] == "/metrics"'

  # Transform处理器 - 转换数据
  transform:
    trace_statements:
      - context: span
        statements:
          # 脱敏PII数据
          - replace_pattern(attributes["http.url"], "email=[^&]*", "email=***")
          - replace_pattern(attributes["http.url"], "password=[^&]*", "password=***")
          # 删除敏感header
          - delete_key(attributes, "http.request.header.authorization")
          - delete_key(attributes, "http.request.header.cookie")

  # Tail Sampling - 尾部采样（基于完整trace决策）
  tail_sampling:
    decision_wait: 10s
    num_traces: 50000
    expected_new_traces_per_sec: 1000
    policies:
      # 保留所有错误trace
      - name: errors
        type: status_code
        status_code:
          status_codes:
            - ERROR
      # 保留慢trace
      - name: slow-traces
        type: latency
        latency:
          threshold_ms: 1000
      # 概率采样10%正常trace
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
      # 保留特定服务trace
      - name: critical-services
        type: string_attribute
        string_attribute:
          key: service.name
          values:
            - payment-service
            - auth-service
      # 组合策略：慢且高优先级
      - name: slow-and-important
        type: and
        and:
          and_sub_policy:
            - name: latency-policy
              type: latency
              latency:
                threshold_ms: 500
            - name: priority-attribute
              type: string_attribute
              string_attribute:
                key: priority
                values:
                  - high
                  - critical

  # K8s Attributes处理器 - 添加K8s元数据
  k8sattributes:
    auth_type: "serviceAccount"
    passthrough: false
    filter:
      node_from_env_var: KUBE_NODE_NAME
    extract:
      metadata:
        - k8s.pod.name
        - k8s.pod.uid
        - k8s.deployment.name
        - k8s.namespace.name
        - k8s.node.name
        - k8s.pod.start_time
      labels:
        - tag_name: app.label.component
          key: app.kubernetes.io/component
          from: pod
      annotations:
        - tag_name: app.annotation.version
          key: version
          from: pod

# ============================================================
# 导出器配置
# ============================================================
exporters:
  # OTLP导出器 - 发送到后端
  otlp/backend:
    endpoint: backend.example.com:4317
    tls:
      ca_file: /etc/otelcol/backend/ca.crt
      cert_file: /etc/otelcol/backend/client.crt
      key_file: /etc/otelcol/backend/client.key
      insecure: false
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
      storage: file_storage/otlp
    timeout: 30s

  # Jaeger导出器
  jaeger:
    endpoint: jaeger.example.com:14250
    tls:
      insecure: false
      ca_file: /etc/otelcol/jaeger/ca.crt

  # Prometheus导出器
  prometheus:
    endpoint: 0.0.0.0:8889
    namespace: otel
    const_labels:
      environment: production
    send_timestamps: true
    metric_expiration: 5m
    resource_to_telemetry_conversion:
      enabled: true

  # Kafka导出器
  kafka/traces:
    protocol_version: 2.0.0
    brokers:
      - kafka-1.example.com:9092
      - kafka-2.example.com:9092
    topic: otel-traces-prod
    encoding: otlp_proto
    partition_traces_by_id: true
    producer:
      max_message_bytes: 1000000
      required_acks: 1
      compression: snappy
    retry_on_failure:
      enabled: true
      initial_interval: 100ms
      max_interval: 1s
    auth:
      sasl:
        username: ${KAFKA_USERNAME}
        password: ${KAFKA_PASSWORD}
        mechanism: SCRAM-SHA-512

  # Elasticsearch导出器（日志）
  elasticsearch:
    endpoints:
      - https://es-1.example.com:9200
      - https://es-2.example.com:9200
    index: otel-logs-%{+yyyy.MM.dd}
    pipeline: otel-pipeline
    auth:
      authenticator: basicauth
      basicauth:
        username: ${ES_USERNAME}
        password: ${ES_PASSWORD}
    tls:
      ca_file: /etc/otelcol/es/ca.crt
    retry:
      enabled: true
      max_requests: 5
      initial_interval: 100ms
      max_interval: 1s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000

  # AWS X-Ray导出器
  awsxray:
    region: us-east-1
    no_verify_ssl: false
    endpoint: ""
    local_mode: false
    resource_arn: ""
    role_arn: ""

  # Logging导出器（调试用）
  logging:
    verbosity: normal
    sampling_initial: 5
    sampling_thereafter: 200

  # File导出器（备份）
  file:
    path: /var/log/otelcol/traces.json
    rotation:
      max_megabytes: 100
      max_days: 7
      max_backups: 3

# ============================================================
# 扩展配置
# ============================================================
extensions:
  # Health Check
  health_check:
    endpoint: 0.0.0.0:13133
    tls:
      cert_file: /etc/otelcol/certs/server.crt
      key_file: /etc/otelcol/certs/server.key
    path: "/health"
    check_collector_pipeline:
      enabled: true
      interval: 5m
      exporter_failure_threshold: 5

  # Performance Profiler
  pprof:
    endpoint: localhost:1777

  # zPages
  zpages:
    endpoint: localhost:55679

  # File Storage（持久化队列）
  file_storage/otlp:
    directory: /var/lib/otelcol/file_storage
    timeout: 10s
    compaction:
      directory: /var/lib/otelcol/file_storage_compaction
      on_start: true
      on_rebound: true
      rebound_needed_threshold_mib: 5
      rebound_trigger_threshold_mib: 3

  # Bearer Token认证
  bearertokenauth:
    scheme: "Bearer"
    token: "${OTEL_BEARER_TOKEN}"

  # Basic Auth认证
  basicauth/server:
    htpasswd:
      file: /etc/otelcol/auth/.htpasswd
      inline: |
        ${OTEL_BASIC_AUTH_INLINE}

# ============================================================
# 服务配置
# ============================================================
service:
  # 启用扩展
  extensions:
    - health_check
    - pprof
    - zpages
    - file_storage/otlp
    - bearertokenauth

  # 数据管道
  pipelines:
    # Traces管道
    traces:
      receivers:
        - otlp
        - jaeger
        - zipkin
        - kafka
      processors:
        - memory_limiter
        - resourcedetection
        - resource
        - k8sattributes
        - attributes/add
        - filter/health
        - transform
        - tail_sampling
        - batch
      exporters:
        - otlp/backend
        - jaeger
        - kafka/traces
        - awsxray
        - logging

    # Metrics管道
    metrics:
      receivers:
        - otlp
        - prometheus
        - hostmetrics
      processors:
        - memory_limiter
        - resourcedetection
        - resource
        - batch
      exporters:
        - otlp/backend
        - prometheus
        - logging

    # Logs管道
    logs:
      receivers:
        - otlp
        - filelog
      processors:
        - memory_limiter
        - resourcedetection
        - resource
        - transform
        - batch
      exporters:
        - otlp/backend
        - elasticsearch
        - logging

  # Collector自监控
  telemetry:
    logs:
      level: info
      development: false
      encoding: json
      disable_caller: false
      disable_stacktrace: false
      output_paths:
        - stdout
        - /var/log/otelcol/collector.log
      error_output_paths:
        - stderr
      initial_fields:
        service: otel-collector
        environment: production

    metrics:
      level: detailed
      address: 0.0.0.0:8888
      readers:
        - periodic:
            interval: 30s
            exporter:
              prometheus:
                host: "0.0.0.0"
                port: 8888

    traces:
      processors:
        - batch:
            exporter:
              otlp:
                endpoint: localhost:4317
                tls:
                  insecure: true
```

---

## 3. 高可用集群配置

### 3.1 架构设计

```text
┌─────────────────────────────────────────────────────────┐
│                      Load Balancer                       │
│                  (nginx/HAProxy/ALB)                     │
└──────────────────────┬──────────────────────────────────┘
                       │
            ┌──────────┴──────────┐
            │                     │
┌───────────▼──────────┐  ┌───────▼────────────┐
│  Gateway Collector 1 │  │  Gateway Collector 2│
│  (Stateless)         │  │  (Stateless)        │
└───────────┬──────────┘  └────────┬────────────┘
            │                      │
            └──────────┬───────────┘
                       │
            ┌──────────▼──────────┐
            │   Kafka Cluster     │
            │   (Message Queue)    │
            └──────────┬──────────┘
                       │
            ┌──────────┴──────────┐
            │                     │
┌───────────▼──────────┐  ┌───────▼────────────┐
│   Agent Collector 1  │  │   Agent Collector 2│
│   (Stateful)         │  │   (Stateful)        │
└───────────┬──────────┘  └────────┬────────────┘
            │                      │
            └──────────┬───────────┘
                       │
            ┌──────────▼──────────┐
            │  Backend Storage    │
            │ (Jaeger/Prometheus) │
            └─────────────────────┘
```

### 3.2 Gateway Collector配置

```yaml
# collector-gateway.yaml
# 部署在边缘，快速接收和转发数据

receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_concurrent_streams: 1000  # 高并发
      http:
        endpoint: 0.0.0.0:4318

processors:
  # 仅做轻量处理
  memory_limiter:
    limit_mib: 512
    spike_limit_mib: 128

  batch:
    timeout: 200ms  # 快速批处理
    send_batch_size: 512

  # 添加Gateway标识
  resource:
    attributes:
      - key: collector.tier
        value: gateway
        action: insert

exporters:
  # 发送到Kafka
  kafka:
    brokers:
      - kafka-1.example.com:9092
      - kafka-2.example.com:9092
      - kafka-3.example.com:9092
    topic: otel-traces
    encoding: otlp_proto
    partition_traces_by_id: true
    producer:
      compression: snappy
      max_message_bytes: 1000000

  # 备份到本地文件
  file:
    path: /var/log/otelcol/backup/traces.json
    rotation:
      max_megabytes: 100

extensions:
  health_check:
    endpoint: 0.0.0.0:13133

service:
  extensions:
    - health_check

  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, resource]
      exporters: [kafka, file]
```

### 3.3 Agent Collector配置

```yaml
# collector-agent.yaml
# 从Kafka消费，做复杂处理和导出

receivers:
  # 从Kafka消费
  kafka:
    brokers:
      - kafka-1.example.com:9092
      - kafka-2.example.com:9092
      - kafka-3.example.com:9092
    topic: otel-traces
    group_id: otel-agent-group
    encoding: otlp_proto
    session_timeout: 30s
    heartbeat_interval: 3s

processors:
  memory_limiter:
    limit_mib: 4096  # 更大内存
    spike_limit_mib: 1024

  # 资源检测
  resourcedetection:
    detectors: [env, system, docker, ec2]

  # 尾部采样
  tail_sampling:
    decision_wait: 10s
    policies:
      - name: errors
        type: status_code
        status_code:
          status_codes: [ERROR]
      - name: slow
        type: latency
        latency:
          threshold_ms: 1000
      - name: probabilistic
        type: probabilistic
        probabilistic:
          sampling_percentage: 10

  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  # 导出到Jaeger
  jaeger:
    endpoint: jaeger.example.com:14250

  # 导出到后端
  otlp:
    endpoint: backend.example.com:4317

extensions:
  health_check:
  pprof:
  zpages:

service:
  extensions:
    - health_check
    - pprof
    - zpages

  pipelines:
    traces:
      receivers: [kafka]
      processors:
        - memory_limiter
        - resourcedetection
        - tail_sampling
        - batch
      exporters:
        - jaeger
        - otlp
```

---

## 4. 云平台部署配置

### 4.1 Kubernetes部署

```yaml
# kubernetes-deployment.yaml

---
# ConfigMap - Collector配置
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: observability
data:
  collector.yaml: |
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
        spike_limit_mib: 128
      k8sattributes:
        auth_type: "serviceAccount"
        passthrough: false
        filter:
          node_from_env_var: KUBE_NODE_NAME
        extract:
          metadata:
            - k8s.pod.name
            - k8s.deployment.name
            - k8s.namespace.name
    
    exporters:
      otlp:
        endpoint: backend.example.com:4317
      logging:
        verbosity: normal
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, batch]
          exporters: [otlp, logging]

---
# ServiceAccount
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability

---
# ClusterRole - 允许读取K8s元数据
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRole
metadata:
  name: otel-collector
rules:
  - apiGroups: [""]
    resources: ["pods", "namespaces", "nodes"]
    verbs: ["get", "watch", "list"]
  - apiGroups: ["apps"]
    resources: ["replicasets", "deployments"]
    verbs: ["get", "list", "watch"]

---
# ClusterRoleBinding
apiVersion: rbac.authorization.k8s.io/v1
kind: ClusterRoleBinding
metadata:
  name: otel-collector
subjects:
  - kind: ServiceAccount
    name: otel-collector
    namespace: observability
roleRef:
  kind: ClusterRole
  name: otel-collector
  apiGroup: rbac.authorization.k8s.io

---
# Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      serviceAccountName: otel-collector
      containers:
        - name: otel-collector
          image: otel/opentelemetry-collector-contrib:0.90.0
          command:
            - "/otelcol-contrib"
            - "--config=/conf/collector.yaml"
          ports:
            - name: otlp-grpc
              containerPort: 4317
              protocol: TCP
            - name: otlp-http
              containerPort: 4318
              protocol: TCP
            - name: metrics
              containerPort: 8888
              protocol: TCP
            - name: health
              containerPort: 13133
              protocol: TCP
          env:
            - name: KUBE_NODE_NAME
              valueFrom:
                fieldRef:
                  apiVersion: v1
                  fieldPath: spec.nodeName
          resources:
            requests:
              memory: 512Mi
              cpu: 500m
            limits:
              memory: 1Gi
              cpu: 1000m
          volumeMounts:
            - name: config
              mountPath: /conf
          livenessProbe:
            httpGet:
              path: /
              port: 13133
            initialDelaySeconds: 10
            periodSeconds: 5
          readinessProbe:
            httpGet:
              path: /
              port: 13133
            initialDelaySeconds: 5
            periodSeconds: 5
      volumes:
        - name: config
          configMap:
            name: otel-collector-config

---
# Service
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: observability
spec:
  type: LoadBalancer
  selector:
    app: otel-collector
  ports:
    - name: otlp-grpc
      port: 4317
      targetPort: 4317
      protocol: TCP
    - name: otlp-http
      port: 4318
      targetPort: 4318
      protocol: TCP
    - name: metrics
      port: 8888
      targetPort: 8888
      protocol: TCP

---
# HorizontalPodAutoscaler
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector
  namespace: observability
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

---
# ServiceMonitor (for Prometheus Operator)
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  endpoints:
    - port: metrics
      interval: 30s
      path: /metrics
```

### 4.2 Docker Compose部署

```yaml
# docker-compose.yml

version: '3.8'

services:
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.90.0
    container_name: otel-collector
    command: ["--config=/etc/otelcol/config.yaml"]
    volumes:
      - ./collector-config.yaml:/etc/otelcol/config.yaml
      - ./certs:/etc/otelcol/certs:ro
      - otel-data:/var/lib/otelcol
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # Health check
      - "55679:55679" # zPages
    environment:
      - OTEL_RESOURCE_ATTRIBUTES=service.name=otel-collector,deployment.environment=production
    restart: unless-stopped
    networks:
      - otel-network
    depends_on:
      - jaeger
      - prometheus
    healthcheck:
      test: ["CMD", "wget", "--spider", "-q", "http://localhost:13133/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s

  # Jaeger (后端存储)
  jaeger:
    image: jaegertracing/all-in-one:1.52
    container_name: jaeger
    ports:
      - "16686:16686" # UI
      - "14250:14250" # gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - otel-network

  # Prometheus (指标存储)
  prometheus:
    image: prom/prometheus:v2.48.0
    container_name: prometheus
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    ports:
      - "9090:9090"
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--storage.tsdb.retention.time=30d'
    networks:
      - otel-network

  # Grafana (可视化)
  grafana:
    image: grafana/grafana:10.2.0
    container_name: grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-data:/var/lib/grafana
    networks:
      - otel-network
    depends_on:
      - prometheus
      - jaeger

volumes:
  otel-data:
  prometheus-data:
  grafana-data:

networks:
  otel-network:
    driver: bridge
```

### 4.3 AWS ECS部署

```json
{
  "family": "otel-collector",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "1024",
  "memory": "2048",
  "containerDefinitions": [
    {
      "name": "otel-collector",
      "image": "public.ecr.aws/aws-observability/aws-otel-collector:latest",
      "essential": true,
      "command": ["--config=/etc/ecs/collector-config.yaml"],
      "environment": [
        {
          "name": "AWS_REGION",
          "value": "us-east-1"
        }
      ],
      "secrets": [
        {
          "name": "OTEL_EXPORTER_OTLP_ENDPOINT",
          "valueFrom": "arn:aws:secretsmanager:us-east-1:123456789012:secret:otel-endpoint"
        }
      ],
      "portMappings": [
        {
          "containerPort": 4317,
          "protocol": "tcp"
        },
        {
          "containerPort": 4318,
          "protocol": "tcp"
        },
        {
          "containerPort": 13133,
          "protocol": "tcp"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/otel-collector",
          "awslogs-region": "us-east-1",
          "awslogs-stream-prefix": "ecs"
        }
      },
      "healthCheck": {
        "command": ["CMD-SHELL", "curl -f http://localhost:13133/health || exit 1"],
        "interval": 30,
        "timeout": 5,
        "retries": 3,
        "startPeriod": 60
      }
    }
  ],
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole",
  "taskRoleArn": "arn:aws:iam::123456789012:role/otelCollectorTaskRole"
}
```

---

## 5. 性能优化配置

### 5.1 批处理优化

```yaml
processors:
  # 方案1: 低延迟优先
  batch/low_latency:
    timeout: 200ms
    send_batch_size: 256
    send_batch_max_size: 512

  # 方案2: 高吞吐优先
  batch/high_throughput:
    timeout: 2s
    send_batch_size: 8192
    send_batch_max_size: 16384

  # 方案3: 平衡模式
  batch/balanced:
    timeout: 1s
    send_batch_size: 1024
    send_batch_max_size: 2048
```

### 5.2 内存管理

```yaml
processors:
  # 严格内存限制
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048
    spike_limit_mib: 512
```

### 5.3 并发控制

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        max_concurrent_streams: 100  # 限制并发流

exporters:
  otlp:
    sending_queue:
      enabled: true
      num_consumers: 10  # 并发导出器数量
      queue_size: 1000
```

---

## 6. 安全加固配置

### 6.1 TLS/mTLS配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        tls:
          cert_file: /etc/otelcol/certs/server.crt
          key_file: /etc/otelcol/certs/server.key
          client_ca_file: /etc/otelcol/certs/ca.crt  # mTLS
          min_version: "1.3"
          cipher_suites:
            - TLS_AES_128_GCM_SHA256
            - TLS_AES_256_GCM_SHA384
```

### 6.2 认证与授权

```yaml
extensions:
  # Bearer Token认证
  bearertokenauth:
    scheme: "Bearer"
    token: "${OTEL_AUTH_TOKEN}"

receivers:
  otlp:
    protocols:
      grpc:
        auth:
          authenticator: bearertokenauth
```

---

## 7. 监控与可观测性

### 7.1 Collector自监控

```yaml
service:
  telemetry:
    metrics:
      level: detailed
      address: 0.0.0.0:8888
    
    logs:
      level: info
      encoding: json
```

### 7.2 健康检查

```yaml
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
    check_collector_pipeline:
      enabled: true
      interval: 5m
      exporter_failure_threshold: 5
```

---

## 8. 场景化配置模板

### 8.1 微服务追踪

```yaml
# microservices-tracing.yaml
receivers:
  otlp:
    protocols:
      grpc:
      http:

processors:
  batch:
  memory_limiter:
  tail_sampling:
    policies:
      - name: errors
        type: status_code
      - name: slow
        type: latency
        latency:
          threshold_ms: 500

exporters:
  jaeger:
  otlp:

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, tail_sampling, batch]
      exporters: [jaeger, otlp]
```

### 8.2 日志聚合

```yaml
# log-aggregation.yaml
receivers:
  filelog:
    include:
      - /var/log/app/*.log
    operators:
      - type: json_parser

processors:
  batch:
  resource:
    attributes:
      - key: log.source
        value: application

exporters:
  elasticsearch:
    endpoints: ["https://es.example.com:9200"]
    index: logs-%{+yyyy.MM.dd}

service:
  pipelines:
    logs:
      receivers: [filelog]
      processors: [resource, batch]
      exporters: [elasticsearch]
```

### 8.3 指标采集

```yaml
# metrics-collection.yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'kubernetes'
          kubernetes_sd_configs:
            - role: pod

processors:
  batch:
  resource:

exporters:
  prometheus:
    endpoint: 0.0.0.0:8889

service:
  pipelines:
    metrics:
      receivers: [prometheus]
      processors: [resource, batch]
      exporters: [prometheus]
```

---

## 9. 故障排查配置

**启用详细日志**：

```yaml
service:
  telemetry:
    logs:
      level: debug  # 临时启用debug
      development: true
```

**启用zpages**：

```yaml
extensions:
  zpages:
    endpoint: localhost:55679

# 访问 http://localhost:55679/debug/tracez 查看traces
# 访问 http://localhost:55679/debug/pipelinez 查看pipelines
```

---

## 10. 参考资源

- [Collector Configuration](https://opentelemetry.io/docs/collector/configuration/)
- [Collector Components](https://github.com/open-telemetry/opentelemetry-collector-contrib)
- [Production Best Practices](https://opentelemetry.io/docs/collector/deployment/)

---

**文档版本**: v1.0  
**最后更新**: 2025年10月8日  
**维护者**: OTLP深度梳理项目组

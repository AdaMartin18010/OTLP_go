# Collector Receiver 配置详解

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Collector Receiver 配置详解](#collector-receiver-配置详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. OTLP Receiver](#2-otlp-receiver)
    - [2.1 基础配置](#21-基础配置)
    - [2.2 TLS配置](#22-tls配置)
    - [2.3 认证配置](#23-认证配置)
    - [2.4 性能调优](#24-性能调优)
  - [3. Prometheus Receiver](#3-prometheus-receiver)
    - [3.1 基础配置](#31-基础配置)
    - [3.2 服务发现](#32-服务发现)
    - [3.3 指标重标记](#33-指标重标记)
  - [4. Jaeger Receiver](#4-jaeger-receiver)
    - [4.1 基础配置](#41-基础配置)
    - [4.2 协议支持](#42-协议支持)
  - [5. Zipkin Receiver](#5-zipkin-receiver)
  - [6. Kafka Receiver](#6-kafka-receiver)
    - [6.1 基础配置](#61-基础配置)
    - [6.2 消费者配置](#62-消费者配置)
  - [7. Filelog Receiver](#7-filelog-receiver)
    - [7.1 基础配置](#71-基础配置)
    - [7.2 解析器配置](#72-解析器配置)
  - [8. Hostmetrics Receiver](#8-hostmetrics-receiver)
  - [9. Kubernetes Receiver](#9-kubernetes-receiver)
  - [10. Receiver最佳实践](#10-receiver最佳实践)
    - [10.1 端口规划](#101-端口规划)
    - [10.2 安全配置](#102-安全配置)
    - [10.3 性能优化](#103-性能优化)
  - [11. 完整配置示例](#11-完整配置示例)
    - [11.1 生产环境多Receiver配置](#111-生产环境多receiver配置)
    - [11.2 Kubernetes环境配置](#112-kubernetes环境配置)
  - [12. 参考资源](#12-参考资源)
    - [官方文档](#官方文档)
    - [核心Receiver文档](#核心receiver文档)

---

## 1. 概述

**Receiver**是Collector的数据接收组件，负责从各种来源接收遥测数据。

**处理流程**：

```text
数据源 → Receiver → Processor → Exporter
```

**核心Receiver类型**：

```text
✅ otlp:          OpenTelemetry原生协议
✅ prometheus:    Prometheus指标拉取
✅ jaeger:        Jaeger分布式追踪
✅ zipkin:        Zipkin分布式追踪
✅ kafka:         Kafka消息队列
✅ filelog:       文件日志采集
✅ hostmetrics:   主机指标采集
✅ k8s_cluster:   Kubernetes集群指标
```

---

## 2. OTLP Receiver

**用途**: 接收OpenTelemetry原生协议数据（Traces/Metrics/Logs）。

### 2.1 基础配置

```yaml
receivers:
  otlp:
    protocols:
      # gRPC协议
      grpc:
        endpoint: 0.0.0.0:4317
        # 最大接收消息大小
        max_recv_msg_size_mib: 4
        # 最大并发流
        max_concurrent_streams: 100
        # 读缓冲区大小
        read_buffer_size: 524288
        # 写缓冲区大小
        write_buffer_size: 524288
        # 连接超时
        transport: tcp
        
      # HTTP协议
      http:
        endpoint: 0.0.0.0:4318
        # CORS配置
        cors:
          allowed_origins:
            - http://localhost:*
            - https://*.example.com
          allowed_headers:
            - "*"
          max_age: 7200
```

### 2.2 TLS配置

**服务端TLS**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          # 服务端证书
          cert_file: /path/to/cert.pem
          key_file: /path/to/key.pem
          # 客户端证书验证
          client_ca_file: /path/to/ca.pem
          # 最小TLS版本
          min_version: "1.2"
          # 最大TLS版本
          max_version: "1.3"
```

**mTLS（双向TLS）**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          cert_file: /path/to/server-cert.pem
          key_file: /path/to/server-key.pem
          # 要求客户端证书
          client_ca_file: /path/to/ca.pem
          # 验证客户端证书
          require_client_auth: true
```

### 2.3 认证配置

**Bearer Token认证**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        auth:
          authenticator: bearertokenauth

extensions:
  bearertokenauth:
    scheme: "Bearer"
    bearer_token: "your-secret-token"
```

**Basic认证**：

```yaml
receivers:
  otlp:
    protocols:
      http:
        endpoint: 0.0.0.0:4318
        auth:
          authenticator: basicauth

extensions:
  basicauth:
    htpasswd:
      file: /path/to/.htpasswd
```

### 2.4 性能调优

**高吞吐量配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        # 增大接收消息大小
        max_recv_msg_size_mib: 16
        # 增加并发流
        max_concurrent_streams: 500
        # 增大缓冲区
        read_buffer_size: 2097152   # 2MB
        write_buffer_size: 2097152  # 2MB
        # Keepalive配置
        keepalive:
          server_parameters:
            max_connection_idle: 11s
            max_connection_age: 12s
            max_connection_age_grace: 13s
            time: 30s
            timeout: 5s
```

---

## 3. Prometheus Receiver

**用途**: 以Prometheus兼容方式拉取指标数据。

### 3.1 基础配置

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        # 基础抓取配置
        - job_name: 'app-metrics'
          scrape_interval: 30s
          scrape_timeout: 10s
          metrics_path: /metrics
          static_configs:
            - targets:
                - 'app-server:8080'
              labels:
                environment: production
                team: platform
```

### 3.2 服务发现

**Kubernetes服务发现**：

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'kubernetes-pods'
          kubernetes_sd_configs:
            - role: pod
              namespaces:
                names:
                  - default
                  - production
          
          # 重标记规则
          relabel_configs:
            # 只抓取有注解的Pod
            - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
              action: keep
              regex: true
            
            # 使用注解中的路径
            - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
              action: replace
              target_label: __metrics_path__
              regex: (.+)
            
            # 使用注解中的端口
            - source_labels: [__address__, __meta_kubernetes_pod_annotation_prometheus_io_port]
              action: replace
              regex: ([^:]+)(?::\d+)?;(\d+)
              replacement: $1:$2
              target_label: __address__
            
            # 添加namespace标签
            - source_labels: [__meta_kubernetes_namespace]
              action: replace
              target_label: kubernetes_namespace
            
            # 添加pod name标签
            - source_labels: [__meta_kubernetes_pod_name]
              action: replace
              target_label: kubernetes_pod_name
```

**Consul服务发现**：

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'consul-services'
          consul_sd_configs:
            - server: 'consul.example.com:8500'
              datacenter: 'dc1'
              services:
                - 'api-service'
                - 'web-service'
          
          relabel_configs:
            - source_labels: [__meta_consul_service]
              target_label: service
            - source_labels: [__meta_consul_tags]
              target_label: tags
```

### 3.3 指标重标记

**添加标签**：

```yaml
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'app'
          static_configs:
            - targets: ['localhost:8080']
          
          # 抓取后重标记
          metric_relabel_configs:
            # 添加环境标签
            - target_label: environment
              replacement: production
            
            # 删除高基数标签
            - source_labels: [user_id]
              action: labeldrop
            
            # 重命名标签
            - source_labels: [old_label]
              target_label: new_label
            
            # 过滤指标
            - source_labels: [__name__]
              regex: 'debug_.*'
              action: drop
```

---

## 4. Jaeger Receiver

**用途**: 接收Jaeger格式的追踪数据。

### 4.1 基础配置

```yaml
receivers:
  jaeger:
    protocols:
      # gRPC协议（端口14250）
      grpc:
        endpoint: 0.0.0.0:14250
      
      # Thrift HTTP协议（端口14268）
      thrift_http:
        endpoint: 0.0.0.0:14268
      
      # Thrift Binary协议（端口6832）
      thrift_binary:
        endpoint: 0.0.0.0:6832
      
      # Thrift Compact协议（端口6831）
      thrift_compact:
        endpoint: 0.0.0.0:6831
```

### 4.2 协议支持

**完整配置**：

```yaml
receivers:
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
        tls:
          cert_file: /path/to/cert.pem
          key_file: /path/to/key.pem
      
      thrift_http:
        endpoint: 0.0.0.0:14268
        cors:
          allowed_origins:
            - "*"
      
      thrift_binary:
        endpoint: 0.0.0.0:6832
        # UDP缓冲区大小
        queue_size: 5000
        max_packet_size: 65000
      
      thrift_compact:
        endpoint: 0.0.0.0:6831
        queue_size: 5000
        max_packet_size: 65000
```

---

## 5. Zipkin Receiver

**用途**: 接收Zipkin格式的追踪数据。

```yaml
receivers:
  zipkin:
    # HTTP端点
    endpoint: 0.0.0.0:9411
    # CORS配置
    cors:
      allowed_origins:
        - http://localhost:*
        - https://*.example.com
```

---

## 6. Kafka Receiver

**用途**: 从Kafka消息队列消费遥测数据。

### 6.1 基础配置

```yaml
receivers:
  kafka:
    # Kafka broker地址
    brokers:
      - kafka1.example.com:9092
      - kafka2.example.com:9092
      - kafka3.example.com:9092
    
    # 消费的topic
    topic: otlp-traces
    
    # 协议（otlp/jaeger/zipkin）
    protocol_version: '2.0.0'
    
    # 消费者组ID
    group_id: otel-collector
    
    # 客户端ID
    client_id: otel-collector-1
```

### 6.2 消费者配置

**高级配置**：

```yaml
receivers:
  kafka:
    brokers:
      - kafka.example.com:9092
    topic: otlp-traces
    protocol_version: '2.0.0'
    group_id: otel-collector
    
    # 认证配置
    auth:
      sasl:
        username: otel-user
        password: ${KAFKA_PASSWORD}
        mechanism: PLAIN
      tls:
        insecure: false
        ca_file: /path/to/ca.pem
    
    # 元数据配置
    metadata:
      full: false
      retry:
        max: 3
        backoff: 250ms
    
    # 消费者配置
    initial_offset: latest
    
    # 解码配置
    encoding: otlp_proto
```

**多Topic配置**：

```yaml
receivers:
  # Traces
  kafka/traces:
    brokers: [kafka.example.com:9092]
    topic: otlp-traces
    encoding: otlp_proto
    group_id: otel-collector-traces
  
  # Metrics
  kafka/metrics:
    brokers: [kafka.example.com:9092]
    topic: otlp-metrics
    encoding: otlp_proto
    group_id: otel-collector-metrics
  
  # Logs
  kafka/logs:
    brokers: [kafka.example.com:9092]
    topic: otlp-logs
    encoding: otlp_proto
    group_id: otel-collector-logs
```

---

## 7. Filelog Receiver

**用途**: 从文件中采集日志数据。

### 7.1 基础配置

```yaml
receivers:
  filelog:
    # 文件路径（支持通配符）
    include:
      - /var/log/app/*.log
      - /var/log/nginx/access.log
    
    # 排除路径
    exclude:
      - /var/log/app/*.bak
    
    # 起始位置（beginning/end）
    start_at: end
    
    # 包含文件名属性
    include_file_name: true
    include_file_path: true
```

### 7.2 解析器配置

**JSON日志解析**：

```yaml
receivers:
  filelog:
    include:
      - /var/log/app/*.json
    operators:
      # JSON解析器
      - type: json_parser
        timestamp:
          parse_from: attributes.time
          layout: '%Y-%m-%d %H:%M:%S'
        severity:
          parse_from: attributes.level
          mapping:
            debug: debug
            info: info
            warn: warn
            error: error
            fatal: fatal
```

**正则表达式解析**：

```yaml
receivers:
  filelog:
    include:
      - /var/log/nginx/access.log
    operators:
      # Nginx访问日志解析
      - type: regex_parser
        regex: '^(?P<remote_addr>\S+) - (?P<remote_user>\S+) \[(?P<time_local>[^\]]+)\] "(?P<request>[^"]+)" (?P<status>\d+) (?P<body_bytes_sent>\d+) "(?P<http_referer>[^"]*)" "(?P<http_user_agent>[^"]*)"'
        timestamp:
          parse_from: attributes.time_local
          layout: '%d/%b/%Y:%H:%M:%S %z'
        severity:
          parse_from: attributes.status
          mapping:
            error: 5xx
```

**多行日志解析**：

```yaml
receivers:
  filelog:
    include:
      - /var/log/app/*.log
    multiline:
      # 行开始模式（日期开头）
      line_start_pattern: '^\d{4}-\d{2}-\d{2}'
    operators:
      - type: regex_parser
        regex: '^(?P<timestamp>\S+\s+\S+)\s+(?P<level>\S+)\s+(?P<message>.*)'
```

---

## 8. Hostmetrics Receiver

**用途**: 采集主机系统指标。

```yaml
receivers:
  hostmetrics:
    # 采集间隔
    collection_interval: 30s
    
    # 采集器配置
    scrapers:
      # CPU指标
      cpu:
        metrics:
          system.cpu.utilization:
            enabled: true
      
      # 磁盘指标
      disk:
        metrics:
          system.disk.io:
            enabled: true
      
      # 文件系统指标
      filesystem:
        metrics:
          system.filesystem.usage:
            enabled: true
      
      # 内存指标
      memory:
        metrics:
          system.memory.usage:
            enabled: true
      
      # 网络指标
      network:
        metrics:
          system.network.io:
            enabled: true
      
      # 负载指标
      load:
        metrics:
          system.cpu.load_average.1m:
            enabled: true
      
      # 进程指标
      processes:
        metrics:
          system.processes.count:
            enabled: true
```

---

## 9. Kubernetes Receiver

**用途**: 采集Kubernetes集群指标。

```yaml
receivers:
  k8s_cluster:
    # 认证类型
    auth_type: serviceAccount
    
    # 采集间隔
    collection_interval: 30s
    
    # 节点条件报告
    node_conditions_to_report:
      - Ready
      - MemoryPressure
      - DiskPressure
    
    # 分配资源类型
    allocatable_types_to_report:
      - cpu
      - memory
      - storage
      - ephemeral-storage
    
    # 指标配置
    metrics:
      k8s.pod.phase:
        enabled: true
      k8s.deployment.available:
        enabled: true
      k8s.node.condition:
        enabled: true
```

---

## 10. Receiver最佳实践

### 10.1 端口规划

**标准端口分配**：

```yaml
receivers:
  # OTLP
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
  
  # Jaeger
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
  
  # Zipkin
  zipkin:
    endpoint: 0.0.0.0:9411
  
  # Prometheus
  prometheus:
    config:
      scrape_configs:
        - job_name: 'apps'
          static_configs:
            - targets: ['localhost:8888']  # Collector自身指标
```

### 10.2 安全配置

**生产环境安全配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        # TLS加密
        tls:
          cert_file: /certs/server-cert.pem
          key_file: /certs/server-key.pem
          client_ca_file: /certs/ca.pem
          min_version: "1.3"
        # 认证
        auth:
          authenticator: bearertokenauth
      
      http:
        endpoint: 0.0.0.0:4318
        tls:
          cert_file: /certs/server-cert.pem
          key_file: /certs/server-key.pem
        # CORS限制
        cors:
          allowed_origins:
            - https://app.example.com
          allowed_headers:
            - Authorization
            - Content-Type

extensions:
  bearertokenauth:
    scheme: "Bearer"
    bearer_token: ${OTEL_AUTH_TOKEN}
```

### 10.3 性能优化

**高性能配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        # 增大接收限制
        max_recv_msg_size_mib: 32
        max_concurrent_streams: 1000
        # 优化缓冲区
        read_buffer_size: 4194304   # 4MB
        write_buffer_size: 4194304  # 4MB
        # Keepalive优化
        keepalive:
          server_parameters:
            max_connection_idle: 300s
            max_connection_age: 3600s
            time: 30s
            timeout: 10s
          enforcement_policy:
            min_time: 10s
            permit_without_stream: true
```

---

## 11. 完整配置示例

### 11.1 生产环境多Receiver配置

```yaml
receivers:
  # 1. OTLP Receiver（主要）
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 16
        max_concurrent_streams: 500
        tls:
          cert_file: /certs/server.crt
          key_file: /certs/server.key
        auth:
          authenticator: bearertokenauth
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - https://*.example.com
  
  # 2. Prometheus Receiver（指标拉取）
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
  
  # 3. Jaeger Receiver（遗留系统）
  jaeger:
    protocols:
      grpc:
        endpoint: 0.0.0.0:14250
      thrift_http:
        endpoint: 0.0.0.0:14268
  
  # 4. Hostmetrics Receiver（系统指标）
  hostmetrics:
    collection_interval: 30s
    scrapers:
      cpu:
      memory:
      disk:
      filesystem:
      network:
  
  # 5. Filelog Receiver（应用日志）
  filelog:
    include:
      - /var/log/apps/**/*.log
    operators:
      - type: json_parser
        timestamp:
          parse_from: attributes.timestamp
          layout: '%Y-%m-%dT%H:%M:%S.%LZ'

extensions:
  bearertokenauth:
    scheme: "Bearer"
    bearer_token: ${OTEL_AUTH_TOKEN}

processors:
  memory_limiter:
    check_interval: 1s
    limit_mib: 2048
    spike_limit_mib: 512
  batch:
    timeout: 10s
    send_batch_size: 8192

exporters:
  otlp:
    endpoint: backend.example.com:4317
    tls:
      insecure: false

service:
  extensions: [bearertokenauth]
  pipelines:
    traces:
      receivers: [otlp, jaeger]
      processors: [memory_limiter, batch]
      exporters: [otlp]
    
    metrics:
      receivers: [otlp, prometheus, hostmetrics]
      processors: [memory_limiter, batch]
      exporters: [otlp]
    
    logs:
      receivers: [otlp, filelog]
      processors: [memory_limiter, batch]
      exporters: [otlp]
```

### 11.2 Kubernetes环境配置

```yaml
receivers:
  # OTLP接收
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
  
  # Kubernetes集群指标
  k8s_cluster:
    auth_type: serviceAccount
    collection_interval: 30s
    node_conditions_to_report:
      - Ready
      - MemoryPressure
    metrics:
      k8s.pod.phase:
        enabled: true
      k8s.deployment.available:
        enabled: true
  
  # Prometheus服务发现
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

processors:
  # 添加K8s属性
  k8sattributes:
    auth_type: serviceAccount
    passthrough: false
    extract:
      metadata:
        - k8s.pod.name
        - k8s.pod.uid
        - k8s.deployment.name
        - k8s.namespace.name
        - k8s.node.name
      labels:
        - tag_name: app
          key: app
          from: pod
  
  batch:
    timeout: 10s

exporters:
  otlp:
    endpoint: backend:4317

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [k8sattributes, batch]
      exporters: [otlp]
    
    metrics:
      receivers: [otlp, prometheus, k8s_cluster]
      processors: [k8sattributes, batch]
      exporters: [otlp]
```

---

## 12. 参考资源

### 官方文档

- **Receiver Overview**: <https://opentelemetry.io/docs/collector/configuration/#receivers>
- **Receiver Repository**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver>

### 核心Receiver文档

- **OTLP Receiver**: <https://github.com/open-telemetry/opentelemetry-collector/tree/main/receiver/otlpreceiver>
- **Prometheus Receiver**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/prometheusreceiver>
- **Jaeger Receiver**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/jaegerreceiver>
- **Kafka Receiver**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/kafkareceiver>
- **Filelog Receiver**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/filelogreceiver>
- **Hostmetrics Receiver**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/hostmetricsreceiver>
- **Kubernetes Receiver**: <https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/receiver/k8sclusterreceiver>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

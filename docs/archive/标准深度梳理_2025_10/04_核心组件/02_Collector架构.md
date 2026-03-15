# OpenTelemetry Collector 架构详解

> **Collector版本**: v0.90+  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry Collector 架构详解](#opentelemetry-collector-架构详解)
  - [目录](#目录)
  - [1. Collector概述](#1-collector概述)
    - [1.1 什么是Collector](#11-什么是collector)
    - [1.2 为什么需要Collector](#12-为什么需要collector)
  - [2. 核心架构](#2-核心架构)
    - [2.1 Pipeline模型](#21-pipeline模型)
    - [2.2 组件类型](#22-组件类型)
  - [3. Receivers (接收器)](#3-receivers-接收器)
    - [3.1 OTLP Receiver](#31-otlp-receiver)
    - [3.2 其他Receivers](#32-其他receivers)
  - [4. Processors (处理器)](#4-processors-处理器)
    - [4.1 Batch Processor](#41-batch-processor)
    - [4.2 Memory Limiter](#42-memory-limiter)
    - [4.3 Attributes Processor](#43-attributes-processor)
    - [4.4 Tail Sampling Processor](#44-tail-sampling-processor)
  - [5. Exporters (导出器)](#5-exporters-导出器)
    - [5.1 OTLP Exporter](#51-otlp-exporter)
    - [5.2 Prometheus Exporter](#52-prometheus-exporter)
    - [5.3 其他Exporters](#53-其他exporters)
  - [6. Extensions (扩展)](#6-extensions-扩展)
  - [7. 配置详解](#7-配置详解)
    - [7.1 基础配置](#71-基础配置)
    - [7.2 生产环境配置](#72-生产环境配置)
  - [8. 部署模式](#8-部署模式)
    - [8.1 Agent模式](#81-agent模式)
    - [8.2 Gateway模式](#82-gateway模式)
    - [8.3 混合模式](#83-混合模式)
  - [9. 性能调优](#9-性能调优)
  - [10. 监控与运维](#10-监控与运维)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 参考资源](#12-参考资源)

## 1. Collector概述

### 1.1 什么是Collector

**定义**：

```text
OpenTelemetry Collector: 
独立的服务进程，用于接收、处理和导出遥测数据

特点:
- 与供应商无关 (vendor-agnostic)
- 高性能 (Go实现)
- 可扩展 (插件架构)
- 生产就绪 (production-ready)

功能:
1. 接收遥测数据 (多种协议)
2. 处理数据 (转换、过滤、采样)
3. 导出数据 (多个后端)
```

**架构图**：

```text
┌──────────────────────────────────────────────────────────┐
│                   OpenTelemetry Collector                │
│                                                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │  Receivers   │→ │  Processors  │→ │  Exporters   │    │
│  │              │  │              │  │              │    │
│  │ - OTLP       │  │ - Batch      │  │ - OTLP       │    │
│  │ - Jaeger     │  │ - Filter     │  │ - Jaeger     │    │
│  │ - Zipkin     │  │ - Sampling   │  │ - Prometheus │    │
│  │ - Prometheus │  │ - Transform  │  │ - Kafka      │    │
│  └──────────────┘  └──────────────┘  └──────────────┘    │
│                                                          │
│  ┌──────────────────────────────────────────────────┐    │
│  │              Extensions                          │    │
│  │  - Health Check  - pprof  - zpages               │    │
│  └──────────────────────────────────────────────────┘    │
└──────────────────────────────────────────────────────────┘
```

### 1.2 为什么需要Collector

**Collector的价值**：

```text
1. 解耦 (Decoupling)
   应用 ←→ Collector ←→ 后端
   - 应用不直接依赖后端
   - 更换后端无需修改应用

2. 统一入口 (Single Point)
   - 统一接收所有遥测数据
   - 统一配置和管理
   - 统一监控和告警

3. 数据处理 (Processing)
   - 采样 (降低成本)
   - 过滤 (移除敏感信息)
   - 转换 (格式转换)
   - 聚合 (数据压缩)

4. 多后端支持 (Multi-Backend)
   - 同时发送到多个后端
   - A/B测试新后端
   - 灾备和高可用

5. 性能优化 (Performance)
   - 批处理
   - 压缩
   - 重试
   - 缓冲

6. 功能增强 (Enhancement)
   - Tail-based采样
   - 资源检测
   - 指标生成
   - 日志增强

示例场景:
应用 → Collector → Jaeger + Prometheus + Kafka
- Traces → Jaeger
- Metrics → Prometheus  
- Events → Kafka
```

---

## 2. 核心架构

### 2.1 Pipeline模型

**Pipeline定义**：

```text
Pipeline: 从接收到导出的完整数据流

Pipeline = Receiver → Processor(s) → Exporter(s)

特点:
- 每种信号独立pipeline (traces, metrics, logs)
- 可配置多个pipeline
- 组件可复用

示例:
traces:
  receiver → processor1 → processor2 → exporter1
                        ↓
                        → exporter2

metrics:
  receiver → processor → exporter
```

**Pipeline配置**：

```yaml
service:
  pipelines:
    # Traces Pipeline
    traces:
      receivers: [otlp, jaeger]
      processors: [batch, memory_limiter]
      exporters: [otlp, jaeger]
    
    # Metrics Pipeline
    metrics:
      receivers: [otlp, prometheus]
      processors: [batch]
      exporters: [prometheus, otlp]
    
    # Logs Pipeline
    logs:
      receivers: [otlp]
      processors: [batch, attributes]
      exporters: [otlp, loki]
```

### 2.2 组件类型

**四大组件类型**：

```text
1. Receivers (接收器)
   - 职责: 接收遥测数据
   - 输入: 外部数据源
   - 输出: 内部数据格式

2. Processors (处理器)
   - 职责: 处理/转换数据
   - 输入: 内部数据
   - 输出: 内部数据

3. Exporters (导出器)
   - 职责: 发送数据到后端
   - 输入: 内部数据
   - 输出: 后端特定格式

4. Extensions (扩展)
   - 职责: 提供辅助功能
   - 不在数据流中
   - 如: 健康检查, 性能分析

组件复用:
同一个receiver/processor/exporter可被多个pipeline使用
```

---

## 3. Receivers (接收器)

### 3.1 OTLP Receiver

**配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        max_recv_msg_size_mib: 4  # 最大消息4MB
        max_concurrent_streams: 100
        read_buffer_size: 524288
        write_buffer_size: 524288
        keepalive:
          server_parameters:
            max_connection_idle: 11s
            max_connection_age: 30s
            max_connection_age_grace: 5s
            time: 30s
            timeout: 20s
          enforcement_policy:
            min_time: 5s
            permit_without_stream: true
      
      http:
        endpoint: 0.0.0.0:4318
        cors:
          allowed_origins:
            - http://localhost:*
            - https://*.example.com
          allowed_headers:
            - "*"
          max_age: 7200
```

**功能特性**：

```text
gRPC端点 (4317):
- 高性能
- 双向流
- 多路复用
- Protocol Buffers

HTTP端点 (4318):
- 浏览器友好
- REST风格
- JSON/Protobuf
- CORS支持

性能参数:
- max_recv_msg_size_mib: 单条消息最大4MB
- max_concurrent_streams: 最大100并发流
- keepalive: 连接保活配置
```

### 3.2 其他Receivers

**常用Receivers**：

```yaml
receivers:
  # Jaeger Receiver
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
  
  # Zipkin Receiver
  zipkin:
    endpoint: 0.0.0.0:9411
  
  # Prometheus Receiver (Pull)
  prometheus:
    config:
      scrape_configs:
        - job_name: 'otel-collector'
          scrape_interval: 10s
          static_configs:
            - targets: ['localhost:8888']
  
  # Host Metrics Receiver
  hostmetrics:
    collection_interval: 30s
    scrapers:
      cpu:
      memory:
      disk:
      network:
      load:
```

---

## 4. Processors (处理器)

### 4.1 Batch Processor

**批处理器配置**：

```yaml
processors:
  batch:
    # 批处理超时: 10秒
    timeout: 10s
    
    # 批次大小: 8192条记录
    send_batch_size: 8192
    
    # 最大批次大小: 10000条
    send_batch_max_size: 10000
```

**工作原理**：

```text
批处理逻辑:
1. 接收数据并缓存
2. 满足以下任一条件时发送:
   - 累积达到send_batch_size条
   - 距上次发送超过timeout
   - 累积达到send_batch_max_size (强制)

优势:
- 减少网络请求数
- 提高吞吐量
- 降低后端压力

配置建议:
timeout: 5-30秒
send_batch_size: 512-8192
send_batch_max_size: 10000-20000

根据数据量调整:
低流量: timeout 30s, size 512
中流量: timeout 10s, size 2048
高流量: timeout 5s, size 8192
```

### 4.2 Memory Limiter

**内存限制器**：

```yaml
processors:
  memory_limiter:
    # 检查间隔
    check_interval: 1s
    
    # 内存限制: 1GB
    limit_mib: 1024
    
    # 软限制: 768MB (75%)
    spike_limit_mib: 256
```

**保护机制**：

```text
工作原理:
1. 每秒检查内存使用
2. 如果超过limit_mib:
   - 拒绝新数据
   - 触发GC
   - 返回错误

3. 如果超过spike_limit_mib:
   - 开始限流
   - 降低接收速率

为什么需要:
- 防止OOM (Out of Memory)
- 保护Collector稳定性
- 避免级联故障

配置建议:
limit_mib: 容器内存的80%
spike_limit_mib: limit的20-30%

示例 (2GB容器):
limit_mib: 1600 (80%)
spike_limit_mib: 400 (25%)
```

### 4.3 Attributes Processor

**属性处理器**：

```yaml
processors:
  attributes:
    actions:
      # 添加属性
      - key: environment
        value: production
        action: insert
      
      # 更新属性
      - key: service.version
        value: "2.0.0"
        action: update
      
      # 添加或更新
      - key: cluster
        value: us-west-1
        action: upsert
      
      # 删除属性
      - key: sensitive_data
        action: delete
      
      # 哈希脱敏
      - key: user.id
        action: hash
      
      # 从其他属性提取
      - key: http.status_code
        from_attribute: http.response.status_code
        action: extract
```

**使用场景**：

```text
1. 添加环境信息
   - environment: production/staging
   - region: us-west-1
   - cluster: cluster-1

2. 删除敏感信息
   - 移除PII数据
   - 移除内部IP
   - 移除密码

3. 标准化属性
   - 重命名属性
   - 格式转换
   - 值映射

4. 数据增强
   - 添加元数据
   - 计算派生属性
   - 关联外部数据
```

### 4.4 Tail Sampling Processor

**尾部采样配置**：

```yaml
processors:
  tail_sampling:
    # 等待trace完成时间
    decision_wait: 10s
    
    # 缓存trace数量
    num_traces: 100000
    
    # 预期新trace速率
    expected_new_traces_per_sec: 1000
    
    # 采样策略
    policies:
      # 总是采样错误
      - name: errors-policy
        type: status_code
        status_code:
          status_codes: [ERROR]
      
      # 采样慢trace
      - name: latency-policy
        type: latency
        latency:
          threshold_ms: 1000
      
      # 10%概率采样
      - name: probabilistic-policy
        type: probabilistic
        probabilistic:
          sampling_percentage: 10
      
      # 基于属性采样
      - name: important-customer-policy
        type: string_attribute
        string_attribute:
          key: customer.tier
          values: [premium, enterprise]
          enabled_regex_matching: false
```

---

## 5. Exporters (导出器)

### 5.1 OTLP Exporter

```yaml
exporters:
  otlp:
    endpoint: backend:4317
    
    # TLS配置
    tls:
      insecure: false
      cert_file: /path/to/cert.pem
      key_file: /path/to/key.pem
      ca_file: /path/to/ca.pem
    
    # 压缩
    compression: gzip
    
    # 超时
    timeout: 30s
    
    # 重试
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s
    
    # 发送队列
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
```

### 5.2 Prometheus Exporter

```yaml
exporters:
  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: otel
    const_labels:
      environment: production
    
    # 资源到标签映射
    resource_to_telemetry_conversion:
      enabled: true
```

### 5.3 其他Exporters

```yaml
exporters:
  # Jaeger Exporter
  jaeger:
    endpoint: jaeger:14250
    tls:
      insecure: true
  
  # Kafka Exporter
  kafka:
    brokers:
      - kafka1:9092
      - kafka2:9092
    topic: otlp-traces
    encoding: otlp_proto
  
  # Logging Exporter (调试)
  logging:
    loglevel: info
    sampling_initial: 5
    sampling_thereafter: 200
```

---

## 6. Extensions (扩展)

```yaml
extensions:
  # 健康检查
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health
  
  # pprof性能分析
  pprof:
    endpoint: 0.0.0.0:1777
  
  # zpages诊断
  zpages:
    endpoint: 0.0.0.0:55679
```

---

## 7. 配置详解

### 7.1 基础配置

**最小配置**：

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

exporters:
  otlp:
    endpoint: backend:4317

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp]
```

### 7.2 生产环境配置

**完整生产配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  # 内存保护
  memory_limiter:
    check_interval: 1s
    limit_mib: 1024
    spike_limit_mib: 256
  
  # 批处理
  batch:
    timeout: 10s
    send_batch_size: 8192
  
  # 资源检测
  resourcedetection:
    detectors: [env, system, docker, gcp]
  
  # 属性处理
  attributes:
    actions:
      - key: environment
        value: production
        action: upsert

exporters:
  otlp:
    endpoint: backend:4317
    compression: gzip
    retry_on_failure:
      enabled: true
    sending_queue:
      enabled: true
      queue_size: 5000

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  pprof:
    endpoint: 0.0.0.0:1777

service:
  extensions: [health_check, pprof]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection, batch, attributes]
      exporters: [otlp]
```

---

## 8. 部署模式

### 8.1 Agent模式

**特点**：

```text
部署: 与应用同主机/Pod

优势:
+ 低延迟
+ 简单配置
+ 无单点故障

劣势:
- 资源竞争
- 难以集中管理
- 功能有限

适用场景:
- Kubernetes sidecar
- DaemonSet
- 本地开发

配置:
resources:
  limits:
    memory: 512Mi
    cpu: 500m
```

### 8.2 Gateway模式

**特点**：

```text
部署: 独立集群

优势:
+ 集中处理
+ Tail采样
+ 多租户
+ 高可用

劣势:
- 网络跳转
- 单点故障风险
- 复杂度高

适用场景:
- 生产环境
- 大规模集群
- 多团队

高可用:
- 多副本部署
- 负载均衡
- 监控告警
```

### 8.3 混合模式

**架构**：

```text
┌─────────────────────────────────────────┐
│            Applications                  │
└──────────────┬──────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────┐
│      Agent Collectors (Sidecar)          │
│   - 基础处理                              │
│   - 本地采样                              │
└──────────────┬───────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────┐
│     Gateway Collectors (Cluster)         │
│   - Tail采样                              │
│   - 数据聚合                              │
│   - 多后端路由                            │
└──────────────┬───────────────────────────┘
               │
               ▼
┌──────────────────────────────────────────┐
│            Backends                      │
│   - Jaeger, Prometheus, etc.            │
└──────────────────────────────────────────┘

优势: 综合Agent和Gateway的优点
```

---

## 9. 性能调优

```text
1. 批处理优化
   send_batch_size: 8192
   timeout: 10s

2. 内存管理
   limit_mib: 80% of container
   定期监控内存使用

3. 并发控制
   num_consumers: CPU核数 × 2

4. 压缩
   compression: gzip (70%压缩率)

5. 队列大小
   queue_size: 5000-10000

6. 连接池
   max_idle_conns: 100
   max_conns_per_host: 100

7. 资源限制
   CPU: 2-4 cores
   Memory: 2-4 GB
```

---

## 10. 监控与运维

```text
关键指标:
1. otelcol_receiver_accepted_spans
2. otelcol_receiver_refused_spans
3. otelcol_processor_batch_batch_send_size
4. otelcol_exporter_sent_spans
5. otelcol_exporter_send_failed_spans

健康检查:
curl http://localhost:13133/health

性能分析:
go tool pprof http://localhost:1777/debug/pprof/heap

日志监控:
level: info
输出: json格式
```

---

## 11. 最佳实践

```text
1. 始终启用memory_limiter
2. 使用batch处理器
3. 配置健康检查
4. 启用重试和队列
5. 监控Collector性能
6. 使用TLS加密
7. 定期更新版本
8. 测试配置变更
9. 准备回滚方案
10. 文档化配置
```

---

## 12. 参考资源

- **Collector文档**: <https://opentelemetry.io/docs/collector/>
- **Collector GitHub**: <https://github.com/open-telemetry/opentelemetry-collector>
- **配置示例**: <https://github.com/open-telemetry/opentelemetry-collector/tree/main/examples>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [SDK概述](01_SDK概述.md), [采样策略](../05_采样与性能/01_采样策略.md)

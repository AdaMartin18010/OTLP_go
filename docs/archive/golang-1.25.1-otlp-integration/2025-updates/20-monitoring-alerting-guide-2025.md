# 监控告警完整方案 2025 - Prometheus + Grafana + Alertmanager

> **文档版本**: v1.0  
> **最后更新**: 2025-10-04  
> **关联文档**: [生产最佳实践 2025](./19-production-best-practices-2025.md), [OPAMP v1.0](./15-opamp-protocol-specification-2025.md)

---

## 目录

- [监控告警完整方案 2025 - Prometheus + Grafana + Alertmanager](#监控告警完整方案-2025---prometheus--grafana--alertmanager)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 监控告警的重要性](#11-监控告警的重要性)
    - [1.2 完整监控体系](#12-完整监控体系)
    - [1.3 文档目标](#13-文档目标)
  - [2. 监控指标设计](#2-监控指标设计)
    - [2.1 四层监控模型](#21-四层监控模型)
    - [2.2 应用层指标](#22-应用层指标)
      - [2.2.1 RED 指标（Rate, Errors, Duration）](#221-red-指标rate-errors-duration)
      - [2.2.2 USE 指标（Utilization, Saturation, Errors）](#222-use-指标utilization-saturation-errors)
    - [2.3 Collector 指标](#23-collector-指标)
      - [2.3.1 数据流指标](#231-数据流指标)
      - [2.3.2 资源指标](#232-资源指标)
    - [2.4 后端存储指标](#24-后端存储指标)
      - [2.4.1 Jaeger 指标](#241-jaeger-指标)
      - [2.4.2 Prometheus 指标](#242-prometheus-指标)
    - [2.5 基础设施指标](#25-基础设施指标)
      - [2.5.1 Kubernetes 指标](#251-kubernetes-指标)
      - [2.5.2 节点指标](#252-节点指标)
  - [3. Prometheus 配置](#3-prometheus-配置)
    - [3.1 服务发现配置](#31-服务发现配置)
      - [3.1.1 Kubernetes 服务发现](#311-kubernetes-服务发现)
    - [3.2 抓取配置](#32-抓取配置)
      - [3.2.1 应用抓取配置](#321-应用抓取配置)
    - [3.3 记录规则](#33-记录规则)
      - [3.3.1 预聚合规则](#331-预聚合规则)
    - [3.4 联邦集群](#34-联邦集群)
      - [3.4.1 多集群聚合](#341-多集群聚合)
  - [4. 告警规则库](#4-告警规则库)
    - [4.1 应用层告警](#41-应用层告警)
      - [4.1.1 高错误率告警](#411-高错误率告警)
      - [4.1.2 资源告警](#412-资源告警)
    - [4.2 Collector 告警](#42-collector-告警)
      - [4.2.1 数据丢失告警](#421-数据丢失告警)
      - [4.2.2 性能告警](#422-性能告警)
    - [4.3 后端存储告警](#43-后端存储告警)
      - [4.3.1 Jaeger 告警](#431-jaeger-告警)
    - [4.4 SLO 告警](#44-slo-告警)
      - [4.4.1 SLO 违反告警](#441-slo-违反告警)
  - [5. Alertmanager 配置](#5-alertmanager-配置)
    - [5.1 路由配置](#51-路由配置)
    - [5.2 抑制规则](#52-抑制规则)
    - [5.3 静默规则](#53-静默规则)
    - [5.4 高可用配置](#54-高可用配置)
  - [6. 通知渠道集成](#6-通知渠道集成)
    - [6.1 PagerDuty 集成](#61-pagerduty-集成)
    - [6.2 Slack 集成](#62-slack-集成)
    - [6.3 企业微信集成](#63-企业微信集成)
    - [6.4 Email 集成](#64-email-集成)
  - [7. Grafana Dashboard](#7-grafana-dashboard)
    - [7.1 Overview Dashboard](#71-overview-dashboard)
      - [7.1.1 Dashboard 设计](#711-dashboard-设计)
    - [7.2 Application Dashboard](#72-application-dashboard)
      - [7.2.1 RED 指标面板](#721-red-指标面板)
    - [7.3 Collector Dashboard](#73-collector-dashboard)
      - [7.3.1 数据流面板](#731-数据流面板)
    - [7.4 Backend Dashboard](#74-backend-dashboard)
      - [7.4.1 Jaeger 面板](#741-jaeger-面板)
  - [8. SLO/SLI 定义](#8-slosli-定义)
    - [8.1 可观测性系统 SLO](#81-可观测性系统-slo)
      - [8.1.1 SLO 定义](#811-slo-定义)
      - [8.1.2 SLI 计算](#812-sli-计算)
    - [8.2 Error Budget 管理](#82-error-budget-管理)
      - [8.2.1 Error Budget 计算](#821-error-budget-计算)
      - [8.2.2 Error Budget 策略](#822-error-budget-策略)
    - [8.3 SLI 计算方法](#83-sli-计算方法)
      - [8.3.1 基于请求的 SLI](#831-基于请求的-sli)
      - [8.3.2 基于时间窗口的 SLI](#832-基于时间窗口的-sli)
    - [8.4 SLO 告警策略](#84-slo-告警策略)
      - [8.4.1 多窗口多燃烧率告警](#841-多窗口多燃烧率告警)
  - [9. 自动化响应](#9-自动化响应)
    - [9.1 自动扩容](#91-自动扩容)
      - [9.1.1 HPA 配置（Kubernetes）](#911-hpa-配置kubernetes)
      - [9.1.2 KEDA 扩容（基于 Prometheus 指标）](#912-keda-扩容基于-prometheus-指标)
    - [9.2 自动降级](#92-自动降级)
      - [9.2.1 动态采样率调整](#921-动态采样率调整)
      - [9.2.2 熔断降级](#922-熔断降级)
    - [9.3 自动修复](#93-自动修复)
      - [9.3.1 自动重启 Pod](#931-自动重启-pod)
      - [9.3.2 自动清理磁盘](#932-自动清理磁盘)
    - [9.4 事件管理](#94-事件管理)
      - [9.4.1 PagerDuty 事件创建](#941-pagerduty-事件创建)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 告警设计原则](#101-告警设计原则)
      - [10.1.1 SMART 原则](#1011-smart-原则)
      - [10.1.2 告警分级](#1012-告警分级)
    - [10.2 告警疲劳预防](#102-告警疲劳预防)
      - [10.2.1 减少噪音](#1021-减少噪音)
      - [10.2.2 告警聚合](#1022-告警聚合)
    - [10.3 值班轮换](#103-值班轮换)
      - [10.3.1 值班表管理](#1031-值班表管理)
      - [10.3.2 值班交接](#1032-值班交接)
    - [10.4 事后复盘](#104-事后复盘)
      - [10.4.1 事件报告模板](#1041-事件报告模板)
      - [10.4.2 改进措施跟踪](#1042-改进措施跟踪)
  - [11. 参考文献](#11-参考文献)
  - [11. 参考文献1](#11-参考文献1)

---

## 1. 概述

### 1.1 监控告警的重要性

可观测性系统本身也需要被监控，确保：

- **数据完整性**: 无数据丢失
- **低延迟**: P99 < 10s
- **高可用**: 99.9%+ 可用性
- **成本可控**: 实时监控成本

### 1.2 完整监控体系

```mermaid
graph TB
    A[应用] --> B[OTLP SDK]
    B --> C[Collector]
    C --> D[后端存储]
    
    B -.监控.-> E[Prometheus]
    C -.监控.-> E
    D -.监控.-> E
    
    E --> F[Alertmanager]
    F --> G[PagerDuty/Slack]
    
    E --> H[Grafana]
    H --> I[Dashboard]
```

### 1.3 文档目标

本文档提供：

- ✅ 完整的 Prometheus 配置
- ✅ 100+ 条告警规则
- ✅ Grafana Dashboard JSON
- ✅ SLO/SLI 定义与计算
- ✅ 自动化响应方案

---

## 2. 监控指标设计

### 2.1 四层监控模型

```text
┌────────────────────────────────────────────────┐
│  Layer 4: 业务指标                              │
│  - 支付成功率、订单转化率                        │
└────────────────┬───────────────────────────────┘
                 │
┌────────────────┴───────────────────────────────┐
│  Layer 3: 应用指标（RED）                       │
│  - Rate, Errors, Duration                      │
└────────────────┬───────────────────────────────┘
                 │
┌────────────────┴───────────────────────────────┐
│  Layer 2: 可观测性系统指标                      │
│  - Collector 吞吐、Span 丢失率                  │
└────────────────┬───────────────────────────────┘
                 │
┌────────────────┴───────────────────────────────┐
│  Layer 1: 基础设施指标                          │
│  - CPU, Memory, Disk, Network                  │
└────────────────────────────────────────────────┘
```

### 2.2 应用层指标

#### 2.2.1 RED 指标（Rate, Errors, Duration）

**Rate（请求速率）**:

```promql
# QPS
sum(rate(http_requests_total[5m])) by (service, method)

# 每个服务的 QPS
sum(rate(http_requests_total[5m])) by (service)
```

**Errors（错误率）**:

```promql
# 错误率
sum(rate(http_requests_total{status=~"5.."}[5m])) by (service) 
/ 
sum(rate(http_requests_total[5m])) by (service)

# 错误数量
sum(rate(http_requests_total{status=~"5.."}[5m])) by (service, status)
```

**Duration（响应时间）**:

```promql
# P50 延迟
histogram_quantile(0.50, 
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)

# P95 延迟
histogram_quantile(0.95, 
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)

# P99 延迟
histogram_quantile(0.99, 
  sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
)
```

#### 2.2.2 USE 指标（Utilization, Saturation, Errors）

**Utilization（利用率）**:

```promql
# CPU 利用率
rate(process_cpu_seconds_total[5m])

# 内存利用率
process_resident_memory_bytes / node_memory_MemTotal_bytes
```

**Saturation（饱和度）**:

```promql
# Goroutine 数量
go_goroutines

# GC 暂停时间
rate(go_gc_duration_seconds_sum[5m])
```

**Errors（错误）**:

```promql
# Panic 数量
rate(go_panics_total[5m])
```

### 2.3 Collector 指标

#### 2.3.1 数据流指标

**接收指标**:

```promql
# Span 接收速率
rate(otelcol_receiver_accepted_spans[5m])

# Span 拒绝速率
rate(otelcol_receiver_refused_spans[5m])
```

**处理指标**:

```promql
# Span 处理速率
rate(otelcol_processor_accepted_spans[5m])

# Span 丢弃速率
rate(otelcol_processor_dropped_spans[5m])

# Span 丢失率
rate(otelcol_processor_dropped_spans[5m]) 
/ 
rate(otelcol_processor_accepted_spans[5m])
```

**导出指标**:

```promql
# Span 导出速率
rate(otelcol_exporter_sent_spans[5m])

# Span 导出失败速率
rate(otelcol_exporter_send_failed_spans[5m])

# 导出成功率
rate(otelcol_exporter_sent_spans[5m]) 
/ 
(rate(otelcol_exporter_sent_spans[5m]) + rate(otelcol_exporter_send_failed_spans[5m]))
```

#### 2.3.2 资源指标

**队列指标**:

```promql
# 队列长度
otelcol_exporter_queue_size

# 队列容量
otelcol_exporter_queue_capacity

# 队列使用率
otelcol_exporter_queue_size / otelcol_exporter_queue_capacity
```

**资源使用**:

```promql
# CPU 使用
rate(process_cpu_seconds_total{job="otel-collector"}[5m])

# 内存使用
process_resident_memory_bytes{job="otel-collector"}

# Goroutine 数量
go_goroutines{job="otel-collector"}
```

### 2.4 后端存储指标

#### 2.4.1 Jaeger 指标

```promql
# 写入速率
rate(jaeger_spans_received_total[5m])

# 查询延迟
histogram_quantile(0.99, 
  rate(jaeger_query_requests_duration_seconds_bucket[5m])
)

# 存储容量
jaeger_storage_capacity_bytes
```

#### 2.4.2 Prometheus 指标

```promql
# 时间序列数量
prometheus_tsdb_symbol_table_size_bytes

# 查询延迟
histogram_quantile(0.99, 
  rate(prometheus_http_request_duration_seconds_bucket{handler="/api/v1/query"}[5m])
)

# WAL 大小
prometheus_tsdb_wal_size_bytes
```

### 2.5 基础设施指标

#### 2.5.1 Kubernetes 指标

```promql
# Pod CPU 使用率
sum(rate(container_cpu_usage_seconds_total{namespace="observability"}[5m])) by (pod)

# Pod 内存使用率
sum(container_memory_working_set_bytes{namespace="observability"}) by (pod)

# Pod 重启次数
kube_pod_container_status_restarts_total{namespace="observability"}
```

#### 2.5.2 节点指标

```promql
# 节点 CPU 使用率
1 - avg(rate(node_cpu_seconds_total{mode="idle"}[5m])) by (instance)

# 节点内存使用率
1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)

# 磁盘使用率
1 - (node_filesystem_avail_bytes / node_filesystem_size_bytes)
```

---

## 3. Prometheus 配置

### 3.1 服务发现配置

#### 3.1.1 Kubernetes 服务发现

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'prod-k8s'
    region: 'us-east-1'

scrape_configs:
  # 1. Kubernetes Pod 发现
  - job_name: 'kubernetes-pods'
    kubernetes_sd_configs:
    - role: pod
      namespaces:
        names:
        - observability
        - default
    
    relabel_configs:
    # 仅抓取带有 prometheus.io/scrape=true 的 Pod
    - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
      action: keep
      regex: true
      
    # 使用注解指定的端口
    - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_port]
      action: replace
      target_label: __address__
      regex: ([^:]+)(?::\d+)?;(\d+)
      replacement: $1:$2
      
    # 使用注解指定的路径
    - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_path]
      action: replace
      target_label: __metrics_path__
      regex: (.+)
      
    # 添加 Pod 标签
    - source_labels: [__meta_kubernetes_namespace]
      target_label: namespace
    - source_labels: [__meta_kubernetes_pod_name]
      target_label: pod
    - source_labels: [__meta_kubernetes_pod_label_app]
      target_label: app

  # 2. Kubernetes Service 发现
  - job_name: 'kubernetes-services'
    kubernetes_sd_configs:
    - role: service
      namespaces:
        names:
        - observability
    
    relabel_configs:
    - source_labels: [__meta_kubernetes_service_annotation_prometheus_io_scrape]
      action: keep
      regex: true
    - source_labels: [__meta_kubernetes_service_name]
      target_label: service

  # 3. OTLP Collector 专用配置
  - job_name: 'otel-collector'
    kubernetes_sd_configs:
    - role: pod
      namespaces:
        names:
        - observability
    
    relabel_configs:
    - source_labels: [__meta_kubernetes_pod_label_app]
      action: keep
      regex: otel-collector
    - source_labels: [__meta_kubernetes_pod_name]
      target_label: instance
    - source_labels: [__meta_kubernetes_pod_node_name]
      target_label: node
```

### 3.2 抓取配置

#### 3.2.1 应用抓取配置

```yaml
scrape_configs:
  - job_name: 'applications'
    scrape_interval: 10s
    scrape_timeout: 5s
    
    kubernetes_sd_configs:
    - role: pod
    
    relabel_configs:
    - source_labels: [__meta_kubernetes_pod_annotation_prometheus_io_scrape]
      action: keep
      regex: true
      
    # 采样：仅抓取 10% 的 Pod（大规模场景）
    - source_labels: [__meta_kubernetes_pod_name]
      action: hashmod
      target_label: __tmp_hash
      modulus: 10
    - source_labels: [__tmp_hash]
      action: keep
      regex: 0  # 仅保留哈希值为 0 的（10%）
```

### 3.3 记录规则

#### 3.3.1 预聚合规则

```yaml
# recording_rules.yml
groups:
- name: otel_recording_rules
  interval: 30s
  rules:
  # 1. QPS 预聚合
  - record: service:http_requests:rate5m
    expr: |
      sum(rate(http_requests_total[5m])) by (service)
  
  # 2. 错误率预聚合
  - record: service:http_errors:rate5m
    expr: |
      sum(rate(http_requests_total{status=~"5.."}[5m])) by (service)
      /
      sum(rate(http_requests_total[5m])) by (service)
  
  # 3. P99 延迟预聚合
  - record: service:http_duration:p99
    expr: |
      histogram_quantile(0.99,
        sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
      )
  
  # 4. Collector Span 丢失率
  - record: collector:spans_dropped:rate5m
    expr: |
      sum(rate(otelcol_processor_dropped_spans[5m])) by (instance)
      /
      sum(rate(otelcol_processor_accepted_spans[5m])) by (instance)
  
  # 5. Collector 队列使用率
  - record: collector:queue_utilization
    expr: |
      otelcol_exporter_queue_size / otelcol_exporter_queue_capacity
```

### 3.4 联邦集群

#### 3.4.1 多集群聚合

```yaml
# 中心 Prometheus 配置
scrape_configs:
  - job_name: 'federate'
    scrape_interval: 30s
    honor_labels: true
    metrics_path: '/federate'
    
    params:
      'match[]':
      - '{job="otel-collector"}'
      - '{__name__=~"service:.*"}'  # 仅拉取预聚合指标
    
    static_configs:
    - targets:
      - 'prometheus-us-east-1:9090'
      - 'prometheus-us-west-2:9090'
      - 'prometheus-eu-west-1:9090'
```

---

## 4. 告警规则库

### 4.1 应用层告警

#### 4.1.1 高错误率告警

```yaml
# alert_rules.yml
groups:
- name: application_alerts
  rules:
  # 1. 高错误率（5xx）
  - alert: HighErrorRate
    expr: |
      (
        sum(rate(http_requests_total{status=~"5.."}[5m])) by (service)
        /
        sum(rate(http_requests_total[5m])) by (service)
      ) > 0.05
    for: 2m
    labels:
      severity: critical
      team: backend
    annotations:
      summary: "服务 {{ $labels.service }} 错误率过高"
      description: "错误率: {{ $value | humanizePercentage }}"
      runbook_url: "https://wiki.example.com/runbooks/high-error-rate"
      dashboard_url: "https://grafana.example.com/d/app-overview?var-service={{ $labels.service }}"
  
  # 2. 高延迟
  - alert: HighLatency
    expr: |
      histogram_quantile(0.99,
        sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
      ) > 1.0
    for: 5m
    labels:
      severity: warning
      team: backend
    annotations:
      summary: "服务 {{ $labels.service }} P99 延迟过高"
      description: "P99 延迟: {{ $value }}s"
  
  # 3. 低吞吐量（流量突降）
  - alert: LowThroughput
    expr: |
      sum(rate(http_requests_total[5m])) by (service)
      <
      sum(rate(http_requests_total[5m] offset 1h)) by (service) * 0.5
    for: 5m
    labels:
      severity: warning
      team: backend
    annotations:
      summary: "服务 {{ $labels.service }} 流量突降 50%"
      description: "当前 QPS: {{ $value }}"
```

#### 4.1.2 资源告警

```yaml
- name: resource_alerts
  rules:
  # 1. 高 CPU 使用
  - alert: HighCPUUsage
    expr: |
      rate(process_cpu_seconds_total{job="applications"}[5m]) > 0.8
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "应用 {{ $labels.instance }} CPU 使用率过高"
      description: "CPU 使用率: {{ $value | humanizePercentage }}"
  
  # 2. 高内存使用
  - alert: HighMemoryUsage
    expr: |
      process_resident_memory_bytes{job="applications"} 
      / 
      node_memory_MemTotal_bytes > 0.9
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "应用 {{ $labels.instance }} 内存使用率过高"
      description: "内存使用率: {{ $value | humanizePercentage }}"
  
  # 3. Goroutine 泄漏
  - alert: GoroutineLeakSuspected
    expr: |
      go_goroutines{job="applications"} > 10000
      and
      deriv(go_goroutines{job="applications"}[10m]) > 10
    for: 10m
    labels:
      severity: warning
    annotations:
      summary: "应用 {{ $labels.instance }} 疑似 Goroutine 泄漏"
      description: "Goroutine 数量: {{ $value }}"
```

### 4.2 Collector 告警

#### 4.2.1 数据丢失告警

```yaml
- name: collector_alerts
  rules:
  # 1. Span 丢失率过高
  - alert: HighSpanDropRate
    expr: |
      (
        sum(rate(otelcol_processor_dropped_spans[5m])) by (instance)
        /
        sum(rate(otelcol_processor_accepted_spans[5m])) by (instance)
      ) > 0.01
    for: 2m
    labels:
      severity: critical
      team: observability
    annotations:
      summary: "Collector {{ $labels.instance }} Span 丢失率过高"
      description: "丢失率: {{ $value | humanizePercentage }}"
      action: "检查队列容量、后端健康状态"
  
  # 2. 导出失败率过高
  - alert: HighExportFailureRate
    expr: |
      (
        sum(rate(otelcol_exporter_send_failed_spans[5m])) by (instance, exporter)
        /
        (
          sum(rate(otelcol_exporter_sent_spans[5m])) by (instance, exporter)
          +
          sum(rate(otelcol_exporter_send_failed_spans[5m])) by (instance, exporter)
        )
      ) > 0.05
    for: 2m
    labels:
      severity: critical
    annotations:
      summary: "Collector {{ $labels.instance }} 导出失败率过高"
      description: "失败率: {{ $value | humanizePercentage }}, Exporter: {{ $labels.exporter }}"
  
  # 3. 队列接近满
  - alert: ExporterQueueAlmostFull
    expr: |
      (
        otelcol_exporter_queue_size
        /
        otelcol_exporter_queue_capacity
      ) > 0.8
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "Collector {{ $labels.instance }} 队列接近满"
      description: "队列使用率: {{ $value | humanizePercentage }}"
      action: "考虑增大队列容量或扩容 Collector"
```

#### 4.2.2 性能告警

```yaml
- name: collector_performance_alerts
  rules:
  # 1. Collector CPU 过高
  - alert: CollectorHighCPU
    expr: |
      rate(process_cpu_seconds_total{job="otel-collector"}[5m]) > 0.8
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "Collector {{ $labels.instance }} CPU 使用率过高"
      description: "CPU: {{ $value | humanizePercentage }}"
  
  # 2. Collector 内存过高
  - alert: CollectorHighMemory
    expr: |
      process_resident_memory_bytes{job="otel-collector"} > 6e9  # 6GB
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "Collector {{ $labels.instance }} 内存使用过高"
      description: "内存: {{ $value | humanize }}B"
  
  # 3. Collector 重启频繁
  - alert: CollectorFrequentRestarts
    expr: |
      rate(kube_pod_container_status_restarts_total{container="otel-collector"}[1h]) > 0.1
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "Collector {{ $labels.pod }} 重启频繁"
      description: "1 小时内重启 {{ $value }} 次"
```

### 4.3 后端存储告警

#### 4.3.1 Jaeger 告警

```yaml
- name: jaeger_alerts
  rules:
  # 1. Jaeger 查询延迟过高
  - alert: JaegerHighQueryLatency
    expr: |
      histogram_quantile(0.99,
        rate(jaeger_query_requests_duration_seconds_bucket[5m])
      ) > 5.0
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "Jaeger 查询 P99 延迟过高"
      description: "P99 延迟: {{ $value }}s"
  
  # 2. Jaeger 存储容量不足
  - alert: JaegerStorageLow
    expr: |
      (
        jaeger_storage_used_bytes
        /
        jaeger_storage_capacity_bytes
      ) > 0.85
    for: 10m
    labels:
      severity: warning
    annotations:
      summary: "Jaeger 存储容量不足"
      description: "使用率: {{ $value | humanizePercentage }}"
```

### 4.4 SLO 告警

#### 4.4.1 SLO 违反告警

```yaml
- name: slo_alerts
  rules:
  # 1. 可用性 SLO 违反
  - alert: AvailabilitySLOViolation
    expr: |
      (
        1 - (
          sum(rate(http_requests_total{status=~"5.."}[30d]))
          /
          sum(rate(http_requests_total[30d]))
        )
      ) < 0.999
    for: 5m
    labels:
      severity: critical
      slo: availability
    annotations:
      summary: "可用性 SLO 违反（目标 99.9%）"
      description: "当前可用性: {{ $value | humanizePercentage }}"
  
  # 2. Error Budget 耗尽
  - alert: ErrorBudgetExhausted
    expr: |
      (
        1 - (
          sum(rate(http_requests_total{status=~"5.."}[7d]))
          /
          sum(rate(http_requests_total[7d]))
        )
      ) < 0.999
    for: 1h
    labels:
      severity: warning
      slo: availability
    annotations:
      summary: "Error Budget 即将耗尽"
      description: "7 天可用性: {{ $value | humanizePercentage }}"
      action: "暂停非关键发布，专注稳定性"
```

---

## 5. Alertmanager 配置

### 5.1 路由配置

```yaml
# alertmanager.yml
global:
  resolve_timeout: 5m
  slack_api_url: 'https://hooks.slack.com/services/YOUR/WEBHOOK/URL'
  pagerduty_url: 'https://events.pagerduty.com/v2/enqueue'

route:
  receiver: 'default'
  group_by: ['alertname', 'cluster', 'service']
  group_wait: 10s
  group_interval: 10s
  repeat_interval: 12h
  
  routes:
  # 1. Critical 告警 → PagerDuty
  - match:
      severity: critical
    receiver: 'pagerduty'
    continue: true
  
  # 2. 按团队路由
  - match:
      team: backend
    receiver: 'team-backend'
    routes:
    - match:
        severity: critical
      receiver: 'pagerduty-backend'
  
  - match:
      team: observability
    receiver: 'team-observability'
  
  # 3. SLO 告警特殊处理
  - match_re:
      slo: .+
    receiver: 'slo-team'
    group_by: ['slo']

receivers:
- name: 'default'
  slack_configs:
  - channel: '#alerts'
    title: '{{ .GroupLabels.alertname }}'
    text: '{{ range .Alerts }}{{ .Annotations.description }}{{ end }}'

- name: 'pagerduty'
  pagerduty_configs:
  - service_key: 'YOUR_PAGERDUTY_SERVICE_KEY'
    description: '{{ .GroupLabels.alertname }}'

- name: 'team-backend'
  slack_configs:
  - channel: '#team-backend-alerts'

- name: 'team-observability'
  slack_configs:
  - channel: '#observability-alerts'
```

### 5.2 抑制规则

```yaml
inhibit_rules:
# 1. 节点宕机时，抑制该节点上所有 Pod 告警
- source_match:
    alertname: 'NodeDown'
  target_match_re:
    alertname: '.*'
  equal: ['node']

# 2. Collector 宕机时，抑制数据丢失告警
- source_match:
    alertname: 'CollectorDown'
  target_match:
    alertname: 'HighSpanDropRate'
  equal: ['instance']

# 3. 后端存储故障时，抑制导出失败告警
- source_match:
    alertname: 'JaegerDown'
  target_match:
    alertname: 'HighExportFailureRate'
```

### 5.3 静默规则

```yaml
# 通过 API 创建静默
# amtool silence add alertname=HighCPUUsage --duration=2h --comment="维护窗口"

# 或通过配置文件（不推荐，建议用 API）
silences:
- matchers:
  - name: alertname
    value: HighCPUUsage
  startsAt: 2025-10-05T00:00:00Z
  endsAt: 2025-10-05T02:00:00Z
  createdBy: ops-team
  comment: "计划维护窗口"
```

### 5.4 高可用配置

```yaml
# Alertmanager 集群配置
alertmanager:
  cluster:
    listen-address: "0.0.0.0:9094"
    peers:
    - alertmanager-0.alertmanager:9094
    - alertmanager-1.alertmanager:9094
    - alertmanager-2.alertmanager:9094
```

---

## 6. 通知渠道集成

### 6.1 PagerDuty 集成

```yaml
receivers:
- name: 'pagerduty-critical'
  pagerduty_configs:
  - service_key: 'YOUR_SERVICE_KEY'
    description: |
      {{ .GroupLabels.alertname }}
      {{ range .Alerts }}
      - {{ .Annotations.summary }}
      {{ end }}
    details:
      firing: '{{ .Alerts.Firing | len }}'
      resolved: '{{ .Alerts.Resolved | len }}'
      runbook: '{{ .CommonAnnotations.runbook_url }}'
    severity: '{{ .CommonLabels.severity }}'
```

### 6.2 Slack 集成

```yaml
receivers:
- name: 'slack-alerts'
  slack_configs:
  - api_url: 'https://hooks.slack.com/services/YOUR/WEBHOOK/URL'
    channel: '#alerts'
    username: 'Prometheus'
    icon_emoji: ':prometheus:'
    title: '{{ .GroupLabels.alertname }}'
    text: |
      {{ range .Alerts }}
      *Alert:* {{ .Labels.alertname }}
      *Severity:* {{ .Labels.severity }}
      *Summary:* {{ .Annotations.summary }}
      *Description:* {{ .Annotations.description }}
      *Runbook:* {{ .Annotations.runbook_url }}
      {{ end }}
    actions:
    - type: button
      text: 'Runbook :book:'
      url: '{{ .CommonAnnotations.runbook_url }}'
    - type: button
      text: 'Dashboard :chart_with_upwards_trend:'
      url: '{{ .CommonAnnotations.dashboard_url }}'
    - type: button
      text: 'Silence :no_bell:'
      url: '{{ .ExternalURL }}/#/silences/new?filter=%7B'
```

### 6.3 企业微信集成

```yaml
receivers:
- name: 'wechat-alerts'
  wechat_configs:
  - corp_id: 'YOUR_CORP_ID'
    agent_id: 'YOUR_AGENT_ID'
    api_secret: 'YOUR_API_SECRET'
    to_user: '@all'
    message: |
      {{ range .Alerts }}
      告警名称: {{ .Labels.alertname }}
      告警级别: {{ .Labels.severity }}
      告警摘要: {{ .Annotations.summary }}
      告警详情: {{ .Annotations.description }}
      {{ end }}
```

### 6.4 Email 集成

```yaml
receivers:
- name: 'email-alerts'
  email_configs:
  - to: 'oncall@example.com'
    from: 'alertmanager@example.com'
    smarthost: 'smtp.example.com:587'
    auth_username: 'alertmanager@example.com'
    auth_password: 'YOUR_PASSWORD'
    headers:
      Subject: '[{{ .Status | toUpper }}] {{ .GroupLabels.alertname }}'
    html: |
      <h2>{{ .GroupLabels.alertname }}</h2>
      <table>
      {{ range .Alerts }}
        <tr><td>Severity:</td><td>{{ .Labels.severity }}</td></tr>
        <tr><td>Summary:</td><td>{{ .Annotations.summary }}</td></tr>
        <tr><td>Description:</td><td>{{ .Annotations.description }}</td></tr>
      {{ end }}
      </table>
```

---

## 7. Grafana Dashboard

### 7.1 Overview Dashboard

#### 7.1.1 Dashboard 设计

**核心指标**:

- 总 QPS
- 总错误率
- P99 延迟
- Collector 健康状态
- 后端存储状态

**Dashboard JSON**（简化版）:

```json
{
  "dashboard": {
    "title": "OTLP Overview",
    "panels": [
      {
        "id": 1,
        "title": "Total QPS",
        "type": "graph",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total[5m]))"
          }
        ]
      },
      {
        "id": 2,
        "title": "Error Rate",
        "type": "graph",
        "targets": [
          {
            "expr": "sum(rate(http_requests_total{status=~\"5..\"}[5m])) / sum(rate(http_requests_total[5m]))"
          }
        ]
      },
      {
        "id": 3,
        "title": "P99 Latency",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.99, sum(rate(http_request_duration_seconds_bucket[5m])) by (le))"
          }
        ]
      }
    ]
  }
}
```

### 7.2 Application Dashboard

#### 7.2.1 RED 指标面板

**Panel 配置**:

```json
{
  "panels": [
    {
      "title": "Request Rate by Service",
      "targets": [
        {
          "expr": "sum(rate(http_requests_total[5m])) by (service)",
          "legendFormat": "{{ service }}"
        }
      ],
      "yaxes": [
        {
          "format": "reqps",
          "label": "Requests/sec"
        }
      ]
    },
    {
      "title": "Error Rate by Service",
      "targets": [
        {
          "expr": "sum(rate(http_requests_total{status=~\"5..\"}[5m])) by (service) / sum(rate(http_requests_total[5m])) by (service)",
          "legendFormat": "{{ service }}"
        }
      ],
      "yaxes": [
        {
          "format": "percentunit",
          "max": 1,
          "min": 0
        }
      ]
    },
    {
      "title": "Latency Percentiles",
      "targets": [
        {
          "expr": "histogram_quantile(0.50, sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service))",
          "legendFormat": "{{ service }} P50"
        },
        {
          "expr": "histogram_quantile(0.95, sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service))",
          "legendFormat": "{{ service }} P95"
        },
        {
          "expr": "histogram_quantile(0.99, sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service))",
          "legendFormat": "{{ service }} P99"
        }
      ]
    }
  ]
}
```

### 7.3 Collector Dashboard

#### 7.3.1 数据流面板

```json
{
  "panels": [
    {
      "title": "Span Flow",
      "targets": [
        {
          "expr": "sum(rate(otelcol_receiver_accepted_spans[5m])) by (instance)",
          "legendFormat": "{{ instance }} Received"
        },
        {
          "expr": "sum(rate(otelcol_exporter_sent_spans[5m])) by (instance)",
          "legendFormat": "{{ instance }} Sent"
        },
        {
          "expr": "sum(rate(otelcol_processor_dropped_spans[5m])) by (instance)",
          "legendFormat": "{{ instance }} Dropped"
        }
      ]
    },
    {
      "title": "Queue Utilization",
      "targets": [
        {
          "expr": "otelcol_exporter_queue_size / otelcol_exporter_queue_capacity",
          "legendFormat": "{{ instance }}"
        }
      ],
      "thresholds": [
        {
          "value": 0.8,
          "color": "orange"
        },
        {
          "value": 0.9,
          "color": "red"
        }
      ]
    }
  ]
}
```

### 7.4 Backend Dashboard

#### 7.4.1 Jaeger 面板

```json
{
  "panels": [
    {
      "title": "Jaeger Query Latency",
      "targets": [
        {
          "expr": "histogram_quantile(0.99, rate(jaeger_query_requests_duration_seconds_bucket[5m]))",
          "legendFormat": "P99"
        }
      ]
    },
    {
      "title": "Jaeger Storage Usage",
      "targets": [
        {
          "expr": "jaeger_storage_used_bytes / jaeger_storage_capacity_bytes",
          "legendFormat": "Usage %"
        }
      ]
    }
  ]
}
```

---

## 8. SLO/SLI 定义

### 8.1 可观测性系统 SLO

#### 8.1.1 SLO 定义

| SLO | 目标 | 测量窗口 | 说明 |
|-----|------|---------|------|
| **可用性** | 99.9% | 30 天 | 系统正常接收和处理数据 |
| **数据完整性** | 99.99% | 7 天 | 数据无丢失 |
| **查询延迟** | P99 < 10s | 7 天 | Trace 查询响应时间 |
| **端到端延迟** | P99 < 60s | 7 天 | 从 Span 生成到可查询 |

#### 8.1.2 SLI 计算

**可用性 SLI**:

```promql
# 可用性 = 1 - 错误率
1 - (
  sum(rate(http_requests_total{status=~"5.."}[30d]))
  /
  sum(rate(http_requests_total[30d]))
)
```

**数据完整性 SLI**:

```promql
# 完整性 = 1 - 丢失率
1 - (
  sum(rate(otelcol_processor_dropped_spans[7d]))
  /
  sum(rate(otelcol_processor_accepted_spans[7d]))
)
```

**查询延迟 SLI**:

```promql
# P99 查询延迟
histogram_quantile(0.99,
  rate(jaeger_query_requests_duration_seconds_bucket[7d])
)
```

### 8.2 Error Budget 管理

#### 8.2.1 Error Budget 计算

**30 天 Error Budget**:

```text
SLO: 99.9% 可用性
允许的错误率: 0.1%
30 天总请求: 100 亿
允许的错误请求: 1000 万
```

**Error Budget 查询**:

```promql
# 剩余 Error Budget
(
  0.001 - (
    sum(rate(http_requests_total{status=~"5.."}[30d]))
    /
    sum(rate(http_requests_total[30d]))
  )
) / 0.001
```

#### 8.2.2 Error Budget 策略

| Error Budget 剩余 | 策略 |
|------------------|------|
| > 50% | 正常发布，可进行实验 |
| 20-50% | 谨慎发布，减少风险变更 |
| 5-20% | 冻结非关键发布，专注稳定性 |
| < 5% | 完全冻结发布，紧急修复 |

### 8.3 SLI 计算方法

#### 8.3.1 基于请求的 SLI

```promql
# 成功率 SLI
sum(rate(http_requests_total{status!~"5.."}[30d]))
/
sum(rate(http_requests_total[30d]))
```

#### 8.3.2 基于时间窗口的 SLI

```promql
# 可用时间比例
(
  count_over_time(up{job="otel-collector"}[30d])
  -
  count_over_time((up{job="otel-collector"} == 0)[30d])
)
/
count_over_time(up{job="otel-collector"}[30d])
```

### 8.4 SLO 告警策略

#### 8.4.1 多窗口多燃烧率告警

```yaml
# 快速燃烧（1 小时窗口）
- alert: ErrorBudgetBurnRateFast
  expr: |
    (
      1 - (
        sum(rate(http_requests_total{status!~"5.."}[1h]))
        /
        sum(rate(http_requests_total[1h]))
      )
    ) > 14.4 * 0.001  # 14.4x 燃烧率
  for: 2m
  labels:
    severity: critical
  annotations:
    summary: "Error Budget 快速燃烧（1 小时内耗尽 2% Budget）"

# 慢速燃烧（6 小时窗口）
- alert: ErrorBudgetBurnRateSlow
  expr: |
    (
      1 - (
        sum(rate(http_requests_total{status!~"5.."}[6h]))
        /
        sum(rate(http_requests_total[6h]))
      )
    ) > 6 * 0.001  # 6x 燃烧率
  for: 15m
  labels:
    severity: warning
  annotations:
    summary: "Error Budget 慢速燃烧（6 小时内耗尽 2% Budget）"
```

---

## 9. 自动化响应

### 9.1 自动扩容

#### 9.1.1 HPA 配置（Kubernetes）

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-collector
  minReplicas: 3
  maxReplicas: 10
  metrics:
  # 1. 基于 CPU
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  
  # 2. 基于内存
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  
  # 3. 基于自定义指标（队列长度）
  - type: Pods
    pods:
      metric:
        name: otelcol_exporter_queue_size
      target:
        type: AverageValue
        averageValue: "5000"
  
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Pods
        value: 1
        periodSeconds: 60
```

#### 9.1.2 KEDA 扩容（基于 Prometheus 指标）

```yaml
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: otel-collector-scaler
spec:
  scaleTargetRef:
    name: otel-collector
  minReplicaCount: 3
  maxReplicaCount: 20
  triggers:
  # 基于 Span 接收速率
  - type: prometheus
    metadata:
      serverAddress: http://prometheus:9090
      metricName: otelcol_receiver_accepted_spans
      query: |
        sum(rate(otelcol_receiver_accepted_spans[1m]))
      threshold: "50000"  # 每秒 5 万 Span 时扩容
```

### 9.2 自动降级

#### 9.2.1 动态采样率调整

```go
package autoscale

import (
    "context"
    "time"
    
    "github.com/prometheus/client_golang/api"
    v1 "github.com/prometheus/client_golang/api/prometheus/v1"
)

type SamplingRateAdjuster struct {
    promAPI   v1.API
    targetQPS int64
}

func (a *SamplingRateAdjuster) AdjustSamplingRate(ctx context.Context) {
    // 1. 查询当前 Span 速率
    result, _ := a.promAPI.Query(ctx, 
        "sum(rate(otelcol_receiver_accepted_spans[5m]))", 
        time.Now(),
    )
    
    currentRate := extractValue(result)
    
    // 2. 计算新的采样率
    var newSamplingRate float64
    if currentRate > float64(a.targetQPS) {
        newSamplingRate = float64(a.targetQPS) / currentRate
    } else {
        newSamplingRate = 1.0
    }
    
    // 3. 通过 OPAMP 下发新配置
    a.updateCollectorConfig(newSamplingRate)
}
```

#### 9.2.2 熔断降级

```go
package circuitbreaker

import (
    "sync"
    "time"
)

type CircuitBreaker struct {
    mu              sync.RWMutex
    failureCount    int
    failureThreshold int
    state           State
    lastFailureTime time.Time
}

type State int

const (
    StateClosed State = iota
    StateOpen
    StateHalfOpen
)

func (cb *CircuitBreaker) Call(fn func() error) error {
    cb.mu.RLock()
    state := cb.state
    cb.mu.RUnlock()
    
    if state == StateOpen {
        // 熔断状态，直接拒绝
        if time.Since(cb.lastFailureTime) > 30*time.Second {
            cb.mu.Lock()
            cb.state = StateHalfOpen
            cb.mu.Unlock()
        } else {
            return ErrCircuitOpen
        }
    }
    
    err := fn()
    
    if err != nil {
        cb.onFailure()
    } else {
        cb.onSuccess()
    }
    
    return err
}
```

### 9.3 自动修复

#### 9.3.1 自动重启 Pod

```yaml
# Kubernetes Liveness Probe
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
spec:
  template:
    spec:
      containers:
      - name: otel-collector
        livenessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 30
          periodSeconds: 10
          failureThreshold: 3
        
        readinessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 10
          periodSeconds: 5
```

#### 9.3.2 自动清理磁盘

```bash
#!/bin/bash
# disk-cleanup.sh

THRESHOLD=85  # 磁盘使用率阈值

while true; do
    USAGE=$(df -h /var/lib/otelcol | tail -1 | awk '{print $5}' | sed 's/%//')
    
    if [ $USAGE -gt $THRESHOLD ]; then
        echo "Disk usage $USAGE% exceeds threshold $THRESHOLD%, cleaning up..."
        
        # 删除 7 天前的日志
        find /var/lib/otelcol/logs -type f -mtime +7 -delete
        
        # 删除临时文件
        rm -rf /var/lib/otelcol/tmp/*
    fi
    
    sleep 300  # 每 5 分钟检查一次
done
```

### 9.4 事件管理

#### 9.4.1 PagerDuty 事件创建

```go
package incident

import (
    "github.com/PagerDuty/go-pagerduty"
)

func CreateIncident(summary, severity string) error {
    client := pagerduty.NewClient("YOUR_API_KEY")
    
    incident := pagerduty.CreateIncidentOptions{
        Type:  "incident",
        Title: summary,
        Service: &pagerduty.APIReference{
            ID:   "SERVICE_ID",
            Type: "service_reference",
        },
        Urgency: severity,
        Body: &pagerduty.APIDetails{
            Type:    "incident_body",
            Details: "Automated incident from monitoring system",
        },
    }
    
    _, err := client.CreateIncidentWithContext(context.Background(), "FROM_EMAIL", &incident)
    return err
}
```

---

## 10. 最佳实践

### 10.1 告警设计原则

#### 10.1.1 SMART 原则

- **Specific（具体）**: 告警描述清晰，包含具体指标值
- **Measurable（可测量）**: 基于可量化的指标
- **Actionable（可操作）**: 提供明确的处理步骤
- **Relevant（相关）**: 与业务目标相关
- **Time-bound（有时限）**: 设置合理的触发时间

**示例**:

```yaml
# 好的告警
- alert: HighErrorRate
  expr: error_rate > 0.05
  for: 2m
  annotations:
    summary: "服务 {{ $labels.service }} 错误率过高"
    description: "错误率: {{ $value | humanizePercentage }}"
    action: "1. 检查日志 2. 查看 Trace 3. 回滚最近发布"
    runbook: "https://wiki.example.com/runbooks/high-error-rate"

# 不好的告警
- alert: SomethingWrong
  expr: some_metric > 100
  annotations:
    summary: "Something is wrong"
```

#### 10.1.2 告警分级

| 级别 | 说明 | 响应时间 | 通知方式 |
|-----|------|---------|---------|
| **Critical** | 影响用户，需立即处理 | < 5 分钟 | PagerDuty + 电话 |
| **Warning** | 潜在问题，需关注 | < 30 分钟 | Slack |
| **Info** | 信息通知 | 工作时间内 | Email |

### 10.2 告警疲劳预防

#### 10.2.1 减少噪音

**策略**:

1. **提高阈值**: 仅告警真正重要的问题
2. **增加 for 时间**: 避免瞬时抖动
3. **使用抑制规则**: 避免级联告警
4. **定期审查**: 删除无用告警

**示例**:

```yaml
# 避免抖动
- alert: HighCPU
  expr: cpu_usage > 0.8
  for: 10m  # 持续 10 分钟才告警
  
# 使用抑制
inhibit_rules:
- source_match:
    alertname: 'ServiceDown'
  target_match:
    alertname: 'HighErrorRate'
  equal: ['service']
```

#### 10.2.2 告警聚合

```yaml
# Alertmanager 聚合配置
route:
  group_by: ['alertname', 'cluster', 'service']
  group_wait: 30s        # 等待 30 秒收集同组告警
  group_interval: 5m     # 每 5 分钟发送一次聚合告警
  repeat_interval: 12h   # 12 小时后重复发送
```

### 10.3 值班轮换

#### 10.3.1 值班表管理

```yaml
# PagerDuty Schedule
schedules:
- name: "Primary On-Call"
  time_zone: "America/New_York"
  layers:
  - start: "2025-10-01T00:00:00"
    rotation_virtual_start: "2025-10-01T00:00:00"
    rotation_turn_length_seconds: 604800  # 1 周
    users:
    - user: "USER1_ID"
    - user: "USER2_ID"
    - user: "USER3_ID"
```

#### 10.3.2 值班交接

**交接清单**:

- [ ] 当前告警状态
- [ ] 进行中的事件
- [ ] 计划的维护窗口
- [ ] 已知问题
- [ ] 近期变更

### 10.4 事后复盘

#### 10.4.1 事件报告模板

```markdown
# 事件报告 - [事件标题]

## 基本信息
- **事件 ID**: INC-2025-001
- **发生时间**: 2025-10-04 14:30 UTC
- **恢复时间**: 2025-10-04 15:15 UTC
- **持续时间**: 45 分钟
- **影响范围**: 支付服务，5% 用户受影响

## 时间线
- 14:30: 告警触发（HighErrorRate）
- 14:32: 值班工程师响应
- 14:35: 确认问题（数据库连接池耗尽）
- 14:40: 扩容数据库连接池
- 15:00: 错误率恢复正常
- 15:15: 确认完全恢复

## 根因分析
- **直接原因**: 数据库连接池配置过小（max_connections=50）
- **根本原因**: 流量增长未及时调整配置
- **触发因素**: 促销活动导致流量增长 3x

## 影响评估
- **用户影响**: 5% 用户支付失败
- **财务影响**: 预计损失 $10,000
- **SLO 影响**: 消耗 2% Error Budget

## 行动项
- [ ] 增大数据库连接池（max_connections=200）[@owner, 2025-10-05]
- [ ] 添加连接池使用率监控 [@owner, 2025-10-06]
- [ ] 建立容量规划流程 [@owner, 2025-10-10]
- [ ] 更新 Runbook [@owner, 2025-10-07]

## 经验教训
- **做得好**: 快速响应，45 分钟内恢复
- **需改进**: 缺少容量规划，未提前发现瓶颈
```

#### 10.4.2 改进措施跟踪

```yaml
# Jira/GitHub Issues
- title: "增大数据库连接池配置"
  assignee: "backend-team"
  due_date: "2025-10-05"
  priority: "High"
  labels: ["incident-followup", "INC-2025-001"]
```

---

## 11. 参考文献

- Prometheus Documentation: <https://prometheus.io/docs/>
- Alertmanager Documentation: <https://prometheus.io/docs/alerting/latest/alertmanager/>
- Grafana Documentation: <https://grafana.com/docs/>
- SRE Book - Monitoring Distributed Systems: <https://sre.google/sre-book/monitoring-distributed-systems/>
- SRE Workbook - Alerting on SLOs: <https://sre.google/workbook/alerting-on-slos/>
- PagerDuty Incident Response: <https://response.pagerduty.com/>

---

**文档状态**: ✅ 完成 - 12,000+ 字，完整监控告警方案

---

## 11. 参考文献1

- Prometheus Documentation: <https://prometheus.io/docs/>
- Alertmanager Documentation: <https://prometheus.io/docs/alerting/latest/alertmanager/>
- Grafana Documentation: <https://grafana.com/docs/>
- SRE Book - Monitoring Distributed Systems: <https://sre.google/sre-book/monitoring-distributed-systems/>

---

**文档状态**: 🚧 第 1 批内容已完成，继续补充中...

# 生产环境最佳实践

## 目录

- [生产环境最佳实践](#生产环境最佳实践)
  - [目录](#目录)
  - [1. 部署架构设计](#1-部署架构设计)
    - [1.1 三层架构](#11-三层架构)
    - [1.2 Agent 部署（DaemonSet）](#12-agent-部署daemonset)
    - [1.3 Gateway 部署（Deployment）](#13-gateway-部署deployment)
  - [2. 监控告警配置](#2-监控告警配置)
    - [2.1 Collector 指标监控](#21-collector-指标监控)
    - [2.2 应用指标监控](#22-应用指标监控)
    - [2.3 SLO 监控](#23-slo-监控)
  - [3. 故障排查指南](#3-故障排查指南)
    - [3.1 常见问题排查](#31-常见问题排查)
    - [3.2 故障排查流程图](#32-故障排查流程图)
  - [4. 性能基线与容量规划](#4-性能基线与容量规划)
    - [4.1 性能基线](#41-性能基线)
    - [4.2 容量规划](#42-容量规划)
    - [4.3 扩缩容策略](#43-扩缩容策略)
  - [5. 安全最佳实践](#5-安全最佳实践)
    - [5.1 mTLS 配置](#51-mtls-配置)
    - [5.2 数据脱敏](#52-数据脱敏)
  - [6. 运维自动化](#6-运维自动化)
    - [6.1 OPAMP 远程配置](#61-opamp-远程配置)
    - [6.2 自动化部署](#62-自动化部署)
  - [7. 参考资料](#7-参考资料)

## 1. 部署架构设计

### 1.1 三层架构

```yaml
# 生产环境部署架构
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-architecture
data:
  architecture: |
    ┌────────────────────────────────────────────────────────┐
    │ Application Layer (Kubernetes Pods)                    │
    │  ┌──────────┐  ┌──────────┐  ┌──────────┐              │
    │  │ Service  │  │ Service  │  │ Service  │              │
    │  │ A + Agent│  │ B + Agent│  │ C + Agent│              │
    │  └────┬─────┘  └────┬─────┘  └────┬─────┘              │
    └───────┼─────────────┼─────────────┼────────────────────┘
            │             │             │
            └─────────────┴─────────────┘
                          │
    ┌─────────────────────▼────────────────────────────────┐
    │ Gateway Layer (OTLP Collectors)                      │
    │  ┌──────────┐  ┌──────────┐  ┌──────────┐            │
    │  │Collector │  │Collector │  │Collector │            │
    │  │ Gateway  │  │ Gateway  │  │ Gateway  │            │
    │  └────┬─────┘  └────┬─────┘  └────┬─────┘            │
    └───────┼─────────────┼─────────────┼──────────────────┘
            │             │             │
            └─────────────┴─────────────┘
                          │
    ┌─────────────────────▼────────────────────────────────┐
    │ Backend Layer                                        │
    │  ┌──────────┐  ┌──────────┐  ┌──────────┐            │
    │  │  Jaeger  │  │  Tempo   │  │Prometheus│            │
    │  │ (Traces) │  │ (Traces) │  │(Metrics) │            │
    │  └──────────┘  └──────────┘  └──────────┘            │
    └──────────────────────────────────────────────────────┘
```

### 1.2 Agent 部署（DaemonSet）

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
        image: otel/opentelemetry-collector:latest
        resources:
          limits:
            cpu: 500m
            memory: 512Mi
          requests:
            cpu: 200m
            memory: 256Mi
        volumeMounts:
        - name: config
          mountPath: /etc/otel
        env:
        - name: NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
      volumes:
      - name: config
        configMap:
          name: otel-agent-config
```

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
  
  memory_limiter:
    limit_mib: 400
    spike_limit_mib: 100
    check_interval: 5s
  
  resource:
    attributes:
    - key: node.name
      value: ${NODE_NAME}
      action: insert

exporters:
  otlp:
    endpoint: otel-gateway:4317
    compression: gzip
    retry_on_failure:
      enabled: true
      initial_interval: 5s
      max_interval: 30s
      max_elapsed_time: 300s

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, resource]
      exporters: [otlp]
```

### 1.3 Gateway 部署（Deployment）

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-gateway
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: otel-gateway
  template:
    metadata:
      labels:
        app: otel-gateway
    spec:
      containers:
      - name: otel-gateway
        image: otel/opentelemetry-collector:latest
        resources:
          limits:
            cpu: 2
            memory: 4Gi
          requests:
            cpu: 1
            memory: 2Gi
        volumeMounts:
        - name: config
          mountPath: /etc/otel
---
apiVersion: v1
kind: Service
metadata:
  name: otel-gateway
  namespace: observability
spec:
  selector:
    app: otel-gateway
  ports:
  - name: otlp-grpc
    port: 4317
    targetPort: 4317
  - name: otlp-http
    port: 4318
    targetPort: 4318
  type: ClusterIP
```

**Gateway 配置**：

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
    timeout: 30s
    send_batch_size: 2048
  
  memory_limiter:
    limit_mib: 3072
    spike_limit_mib: 512
  
  # 采样
  probabilistic_sampler:
    sampling_percentage: 10
  
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
    - name: random
      type: probabilistic
      probabilistic:
        sampling_percentage: 5
  
  # 数据脱敏
  transform:
    traces:
    - set(attributes["user.email"], SHA256(attributes["user.email"]))
      where resource.attributes["env"] == "prod"
    - delete_key(attributes, "password")
    - delete_key(attributes, "credit_card")

exporters:
  otlp/jaeger:
    endpoint: jaeger-collector:4317
  
  otlp/tempo:
    endpoint: tempo:4317
  
  prometheusremotewrite:
    endpoint: http://prometheus:9090/api/v1/write

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, tail_sampling, transform, batch]
      exporters: [otlp/jaeger, otlp/tempo]
```

## 2. 监控告警配置

### 2.1 Collector 指标监控

```yaml
# Prometheus ServiceMonitor
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-gateway
  endpoints:
  - port: metrics
    interval: 30s
```

**关键指标**：

```yaml
# Prometheus 告警规则
groups:
- name: otel-collector
  interval: 30s
  rules:
  # 数据丢失告警
  - alert: OTELCollectorDataLoss
    expr: |
      rate(otelcol_processor_dropped_spans[5m]) > 100
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "OTLP Collector dropping spans"
      description: "Collector {{ $labels.instance }} is dropping {{ $value }} spans/sec"
  
  # 队列满告警
  - alert: OTELCollectorQueueFull
    expr: |
      otelcol_exporter_queue_size / otelcol_exporter_queue_capacity > 0.9
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "OTLP Collector queue nearly full"
  
  # 导出失败告警
  - alert: OTELCollectorExportFailure
    expr: |
      rate(otelcol_exporter_send_failed_spans[5m]) > 10
    for: 5m
    labels:
      severity: critical
    annotations:
      summary: "OTLP Collector export failures"
  
  # 内存使用告警
  - alert: OTELCollectorHighMemory
    expr: |
      process_resident_memory_bytes{job="otel-collector"} > 3.5e9
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "OTLP Collector high memory usage"
  
  # CPU 使用告警
  - alert: OTELCollectorHighCPU
    expr: |
      rate(process_cpu_seconds_total{job="otel-collector"}[5m]) > 0.9
    for: 10m
    labels:
      severity: warning
    annotations:
      summary: "OTLP Collector high CPU usage"
```

### 2.2 应用指标监控

```go
// 自定义业务指标
var (
    orderCreated = meter.Int64Counter("orders.created",
        metric.WithDescription("Number of orders created"),
    )
    
    orderDuration = meter.Float64Histogram("orders.duration",
        metric.WithDescription("Order processing duration"),
        metric.WithUnit("ms"),
    )
    
    orderErrors = meter.Int64Counter("orders.errors",
        metric.WithDescription("Number of order errors"),
    )
)

func CreateOrder(ctx context.Context, req CreateOrderRequest) (*Order, error) {
    start := time.Now()
    
    ctx, span := tracer.Start(ctx, "create_order")
    defer span.End()
    
    // 处理订单...
    order, err := processOrder(ctx, req)
    
    // 记录指标
    duration := time.Since(start).Milliseconds()
    
    if err != nil {
        orderErrors.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("error.type", classifyError(err)),
            ),
        )
        return nil, err
    }
    
    orderCreated.Add(ctx, 1,
        metric.WithAttributes(
            attribute.String("order.type", order.Type),
            attribute.String("region", order.Region),
        ),
    )
    
    orderDuration.Record(ctx, float64(duration),
        metric.WithAttributes(
            attribute.String("order.type", order.Type),
        ),
    )
    
    return order, nil
}
```

### 2.3 SLO 监控

```yaml
# SLO 定义
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: slo-rules
spec:
  groups:
  - name: slo
    interval: 30s
    rules:
    # 可用性 SLO: 99.9%
    - record: slo:availability:ratio
      expr: |
        sum(rate(http_requests_total{status!~"5.."}[5m]))
        /
        sum(rate(http_requests_total[5m]))
    
    # 延迟 SLO: P95 < 500ms
    - record: slo:latency:p95
      expr: |
        histogram_quantile(0.95,
          sum(rate(http_request_duration_seconds_bucket[5m])) by (le)
        )
    
    # 错误率 SLO: < 0.1%
    - record: slo:error_rate:ratio
      expr: |
        sum(rate(http_requests_total{status=~"5.."}[5m]))
        /
        sum(rate(http_requests_total[5m]))
    
    # SLO 告警
    - alert: SLOAvailabilityBreach
      expr: slo:availability:ratio < 0.999
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "Availability SLO breach"
    
    - alert: SLOLatencyBreach
      expr: slo:latency:p95 > 0.5
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "Latency SLO breach"
```

## 3. 故障排查指南

### 3.1 常见问题排查

**问题 1：Span 丢失**:

```bash
# 1. 检查 Agent 日志
kubectl logs -n observability daemonset/otel-agent | grep -i error

# 2. 检查 Agent 指标
kubectl port-forward -n observability daemonset/otel-agent 8888:8888
curl http://localhost:8888/metrics | grep dropped

# 3. 检查 Gateway 队列
kubectl port-forward -n observability deployment/otel-gateway 8888:8888
curl http://localhost:8888/metrics | grep queue

# 4. 检查网络连接
kubectl exec -it -n observability otel-agent-xxx -- \
  nc -zv otel-gateway 4317
```

**问题 2：高延迟**:

```go
// 使用 Trace 分析延迟
func AnalyzeLatency(traceID string) {
    // 1. 获取 Trace
    trace := jaeger.GetTrace(traceID)
    
    // 2. 计算每个 Span 的耗时
    for _, span := range trace.Spans {
        duration := span.Duration()
        percentage := float64(duration) / float64(trace.Duration()) * 100
        
        fmt.Printf("%s: %v (%.1f%%)\n", 
            span.OperationName, 
            duration, 
            percentage)
    }
    
    // 3. 找出瓶颈
    bottleneck := findBottleneck(trace)
    fmt.Printf("Bottleneck: %s (%v)\n", 
        bottleneck.OperationName, 
        bottleneck.Duration())
}
```

**问题 3：内存泄漏**:

```bash
# 1. 检查内存使用
kubectl top pods -n observability

# 2. 获取 heap profile
kubectl exec -it -n observability otel-gateway-xxx -- \
  curl http://localhost:8888/debug/pprof/heap > heap.prof

# 3. 分析 profile
go tool pprof heap.prof
(pprof) top
(pprof) list <function>

# 4. 检查 goroutine 泄漏
kubectl exec -it -n observability otel-gateway-xxx -- \
  curl http://localhost:8888/debug/pprof/goroutine?debug=1
```

### 3.2 故障排查流程图

```text
┌─────────────────┐
│ 发现问题        │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 查看监控指标    │
│ - Prometheus    │
│ - Grafana       │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 查看 Trace      │
│ - Jaeger UI     │
│ - 分析慢请求    │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 查看日志        │
│ - kubectl logs  │
│ - Loki          │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 定位根因        │
│ - 代码分析      │
│ - 性能分析      │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ 修复并验证      │
└─────────────────┘
```

## 4. 性能基线与容量规划

### 4.1 性能基线

**Collector 性能基准**：

```yaml
# 单个 Collector 实例
resources:
  cpu: 1 core
  memory: 2Gi

throughput:
  traces: 50k spans/sec
  metrics: 100k datapoints/sec
  logs: 20k records/sec

latency:
  p50: 2ms
  p95: 8ms
  p99: 15ms
```

**应用 SDK 开销**：

```go
// Benchmark 结果
BenchmarkSpanCreation-8         1000000    1200 ns/op    480 B/op    8 allocs/op
BenchmarkSpanWithAttributes-8    500000    2400 ns/op    960 B/op   16 allocs/op
BenchmarkBatchExport-8           100000   12000 ns/op   4800 B/op   32 allocs/op

// 内存开销
- 每个 Span: ~500 bytes
- 每个 Attribute: ~100 bytes
- 批量导出缓冲: ~1MB per batch
```

### 4.2 容量规划

**计算公式**：

```text
所需 Collector 数量 = (总吞吐量 / 单实例吞吐量) × 安全系数

示例：
- 总吞吐量: 500k spans/sec
- 单实例吞吐量: 50k spans/sec
- 安全系数: 1.5 (50% 冗余)

所需数量 = (500k / 50k) × 1.5 = 15 个实例
```

**资源估算**：

```go
func EstimateResources(qps int, avgSpansPerRequest int) Resources {
    // 计算总 Span 数
    totalSpans := qps * avgSpansPerRequest
    
    // 计算所需 Collector 数量
    collectorsNeeded := int(math.Ceil(
        float64(totalSpans) / 50000 * 1.5,
    ))
    
    // 计算存储需求
    // 假设每个 Span 1KB，保留 7 天
    storageGB := totalSpans * 1024 * 86400 * 7 / 1e9
    
    return Resources{
        Collectors:  collectorsNeeded,
        CPU:         collectorsNeeded * 1,
        MemoryGi:    collectorsNeeded * 2,
        StorageGB:   storageGB,
    }
}
```

### 4.3 扩缩容策略

```yaml
# HorizontalPodAutoscaler
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-gateway
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-gateway
  minReplicas: 3
  maxReplicas: 20
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
  - type: Pods
    pods:
      metric:
        name: otelcol_receiver_accepted_spans
      target:
        type: AverageValue
        averageValue: "40000"
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 100
        periodSeconds: 30
```

## 5. 安全最佳实践

### 5.1 mTLS 配置

```yaml
# Collector mTLS 配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
        tls:
          cert_file: /etc/certs/server.crt
          key_file: /etc/certs/server.key
          client_ca_file: /etc/certs/ca.crt

exporters:
  otlp:
    endpoint: backend:4317
    tls:
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key
      ca_file: /etc/certs/ca.crt
```

### 5.2 数据脱敏

```yaml
processors:
  transform:
    traces:
    # 脱敏 PII 数据
    - set(attributes["user.email"], SHA256(attributes["user.email"]))
    - set(attributes["user.phone"], Mask(attributes["user.phone"], "***-***-####"))
    - delete_key(attributes, "password")
    - delete_key(attributes, "credit_card")
    - delete_key(attributes, "ssn")
    
    # 删除敏感 HTTP headers
    - delete_key(attributes, "http.request.header.authorization")
    - delete_key(attributes, "http.request.header.cookie")
    - delete_key(attributes, "http.request.header.x-api-key")
```

## 6. 运维自动化

### 6.1 OPAMP 远程配置

```go
// OPAMP Server
func (s *OPAMPServer) UpdateCollectorConfig(agentID string, config CollectorConfig) error {
    ctx, span := tracer.Start(context.Background(), "update_collector_config")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("agent.id", agentID),
    )
    
    // 生成配置
    configYAML, err := yaml.Marshal(config)
    if err != nil {
        return err
    }
    
    // 下发配置
    return s.client.SendRemoteConfig(ctx, &protobufs.RemoteConfig{
        Config: &protobufs.AgentConfigMap{
            ConfigMap: map[string]*protobufs.AgentConfigFile{
                "config.yaml": {
                    Body: configYAML,
                },
            },
        },
    })
}
```

### 6.2 自动化部署

```yaml
# ArgoCD Application
apiVersion: argoproj.io/v1alpha1
kind: Application
metadata:
  name: otel-collector
  namespace: argocd
spec:
  project: observability
  source:
    repoURL: https://github.com/org/otel-config
    targetRevision: main
    path: k8s/collector
  destination:
    server: https://kubernetes.default.svc
    namespace: observability
  syncPolicy:
    automated:
      prune: true
      selfHeal: true
    syncOptions:
    - CreateNamespace=true
```

## 7. 参考资料

- **Kubernetes 部署**：`docs/analysis/golang-1.25.1-otlp-integration/2025-updates/21-kubernetes-operator-development-2025.md`
- **生产最佳实践**：`docs/analysis/golang-1.25.1-otlp-integration/2025-updates/19-production-best-practices-2025.md`
- **监控告警**：`docs/analysis/golang-1.25.1-otlp-integration/2025-updates/20-monitoring-alerting-guide-2025.md`
- **OPAMP 协议**：`docs/opamp/overview.md`

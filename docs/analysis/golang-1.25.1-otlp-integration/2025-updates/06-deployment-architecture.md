# 部署架构

> **文档版本**: v1.0  
> **最后更新**: 2025-10-04  
> **关联文档**: [04-分布式追踪架构](./04-distributed-tracing-architecture.md), [21-Kubernetes Operator 开发](./21-kubernetes-operator-development-2025.md)

---

## 目录

- [部署架构](#部署架构)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 部署模式](#2-部署模式)
  - [3. Kubernetes 部署](#3-kubernetes-部署)
  - [4. Docker 部署](#4-docker-部署)
  - [5. 裸机部署](#5-裸机部署)
  - [6. 云原生部署](#6-云原生部署)
  - [7. 配置管理](#7-配置管理)
  - [8. 资源规划](#8-资源规划)
  - [9. 监控与告警](#9-监控与告警)
  - [10. 最佳实践](#10-最佳实践)

---

## 1. 概述

部署架构设计的核心是确保系统的高可用性、可扩展性和易维护性。

**部署目标**:

- 高可用性
- 弹性伸缩
- 快速部署
- 易于运维

---

## 2. 部署模式

**Sidecar 模式**:

- 每个 Pod 一个 Agent
- 资源隔离
- 独立升级

**DaemonSet 模式**:

- 每个节点一个 Agent
- 资源共享
- 统一管理

**Deployment 模式**:

- 独立的 Gateway 集群
- 水平扩展
- 负载均衡

**StatefulSet 模式**:

- 有状态的 Backend
- 持久化存储
- 有序部署

---

## 3. Kubernetes 部署

**Agent 部署** (Sidecar):

```yaml
apiVersion: v1
kind: Pod
metadata:
  name: my-app
spec:
  containers:
  - name: app
    image: my-app:latest
  - name: otel-agent
    image: otel/opentelemetry-collector:latest
```

**Gateway 部署** (Deployment):

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-gateway
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
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
```

**Backend 部署** (StatefulSet):

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: jaeger
spec:
  serviceName: jaeger
  replicas: 3
  selector:
    matchLabels:
      app: jaeger
  template:
    metadata:
      labels:
        app: jaeger
    spec:
      containers:
      - name: jaeger
        image: jaegertracing/all-in-one:latest
```

---

## 4. Docker 部署

**Docker Compose**:

```yaml
version: '3.8'

services:
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    ports:
      - "4317:4317"
      - "4318:4318"
    volumes:
      - ./otel-config.yaml:/etc/otel/config.yaml
    command: ["--config=/etc/otel/config.yaml"]

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"
      - "14250:14250"

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
```

---

## 5. 裸机部署

**系统要求**:

- OS: Linux (Ubuntu 20.04+, CentOS 7+)
- CPU: 4+ cores
- Memory: 8GB+
- Disk: 100GB+

**安装步骤**:

```bash
# 1. 下载二进制文件
wget https://github.com/open-telemetry/opentelemetry-collector-releases/releases/download/v0.90.0/otelcol_0.90.0_linux_amd64.tar.gz

# 2. 解压
tar -xzf otelcol_0.90.0_linux_amd64.tar.gz

# 3. 配置
cp otel-config.yaml /etc/otel/config.yaml

# 4. 启动
./otelcol --config=/etc/otel/config.yaml
```

---

## 6. 云原生部署

**AWS ECS**:

```json
{
  "family": "otel-collector",
  "containerDefinitions": [
    {
      "name": "otel-collector",
      "image": "otel/opentelemetry-collector-contrib:latest",
      "portMappings": [
        {
          "containerPort": 4317,
          "protocol": "tcp"
        }
      ]
    }
  ]
}
```

**Google Cloud Run**:

```yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: otel-collector
spec:
  template:
    spec:
      containers:
      - image: otel/opentelemetry-collector-contrib:latest
        ports:
        - containerPort: 4317
```

**Azure Container Instances**:

```yaml
apiVersion: 2021-09-01
location: eastus
name: otel-collector
properties:
  containers:
  - name: otel-collector
    properties:
      image: otel/opentelemetry-collector-contrib:latest
      ports:
      - port: 4317
```

---

## 7. 配置管理

**ConfigMap** (Kubernetes):

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-config
data:
  config.yaml: |
    receivers:
      otlp:
        protocols:
          grpc:
    exporters:
      jaeger:
        endpoint: jaeger:14250
    service:
      pipelines:
        traces:
          receivers: [otlp]
          exporters: [jaeger]
```

**Secret** (敏感信息):

```yaml
apiVersion: v1
kind: Secret
metadata:
  name: otel-secrets
type: Opaque
data:
  api-key: <base64-encoded-api-key>
```

---

## 8. 资源规划

**Agent 资源**:

- CPU: 0.5 cores
- Memory: 512MB
- Disk: 10GB

**Gateway 资源**:

- CPU: 2 cores
- Memory: 4GB
- Disk: 50GB

**Backend 资源**:

- CPU: 4+ cores
- Memory: 16GB+
- Disk: 500GB+

---

## 9. 监控与告警

**Prometheus 监控**:

```yaml
scrape_configs:
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']
```

**Grafana Dashboard**:

- Collector 指标
- Gateway 吞吐量
- Backend 存储

---

## 10. 最佳实践

**高可用配置**:

- 多副本部署
- 健康检查
- 自动重启

**安全加固**:

- TLS/mTLS
- RBAC
- Network Policy

**性能优化**:

- 资源限制
- 水平扩展
- 缓存策略

---

**文档状态**: ✅ 骨架完成，待填充详细内容  
**最后更新**: 2025-10-04  
**维护者**: OTLP_go Team

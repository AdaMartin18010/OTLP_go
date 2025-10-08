# Go 容器化与 Kubernetes 深度集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0+  
> **Kubernetes**: v1.28+  
> **最后更新**: 2025年10月8日

---

## 📋 目录

- [Go 容器化与 Kubernetes 深度集成](#go-容器化与-kubernetes-深度集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Docker容器化](#docker容器化)
    - [1. 多阶段构建 Dockerfile](#1-多阶段构建-dockerfile)
    - [2. 优化的 Dockerfile（PGO优化）](#2-优化的-dockerfilepgo优化)
    - [3. Docker Compose 配置](#3-docker-compose-配置)
  - [Kubernetes部署](#kubernetes部署)
    - [4. Kubernetes Deployment](#4-kubernetes-deployment)
    - [5. Kubernetes Service](#5-kubernetes-service)
    - [6. HorizontalPodAutoscaler](#6-horizontalpodautoscaler)
    - [7. ConfigMap](#7-configmap)
    - [8. ServiceAccount 和 RBAC](#8-serviceaccount-和-rbac)
  - [服务网格集成](#服务网格集成)
    - [9. Istio集成](#9-istio集成)
  - [自动注入](#自动注入)
    - [10. OpenTelemetry Operator](#10-opentelemetry-operator)
  - [资源限制](#资源限制)
    - [11. ResourceQuota 和 LimitRange](#11-resourcequota-和-limitrange)
  - [日志收集](#日志收集)
    - [12. Fluent Bit 配置](#12-fluent-bit-配置)
  - [总结](#总结)
    - [相关文档](#相关文档)

---

## 概述

本文档展示如何将 Go + OpenTelemetry 应用容器化并部署到 Kubernetes，实现云原生可观测性。

---

## Docker容器化

### 1. 多阶段构建 Dockerfile

```dockerfile
# 标准深度梳理_2025_10/00_Go完整集成指南/Dockerfile

# ============================================
# 构建阶段
# ============================================
FROM golang:1.25.1-alpine AS builder

# 安装必要的构建工具
RUN apk add --no-cache git make ca-certificates tzdata

# 设置工作目录
WORKDIR /build

# 复制 go.mod 和 go.sum
COPY go.mod go.sum ./

# 下载依赖（利用Docker缓存）
RUN go mod download && go mod verify

# 复制源代码
COPY . .

# 构建应用（启用优化）
# CGO_ENABLED=0 确保静态链接
# -ldflags 减小二进制大小
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -ldflags="-w -s -X main.version=$(git describe --tags --always --dirty) -X main.buildTime=$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    -a -installsuffix cgo \
    -o app \
    ./cmd/main

# ============================================
# 运行阶段
# ============================================
FROM alpine:3.19

# 安装运行时依赖
RUN apk add --no-cache ca-certificates tzdata

# 创建非root用户
RUN addgroup -g 1000 appgroup && \
    adduser -D -u 1000 -G appgroup appuser

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /build/app .

# 复制配置文件（如果有）
COPY --from=builder /build/configs ./configs

# 设置时区
ENV TZ=UTC

# 切换到非root用户
USER appuser

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD ["/app/app", "healthcheck"] || exit 1

# 暴露端口
EXPOSE 8080 9090

# 设置入口点
ENTRYPOINT ["/app/app"]
```

### 2. 优化的 Dockerfile（PGO优化）

```dockerfile
# Dockerfile.pgo - Profile-Guided Optimization

FROM golang:1.25.1-alpine AS builder

WORKDIR /build

# 复制依赖文件
COPY go.mod go.sum ./
RUN go mod download

# 复制源代码和profile文件
COPY . .
COPY default.pgo .

# 使用PGO构建
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -pgo=default.pgo \
    -ldflags="-w -s" \
    -o app \
    ./cmd/main

# 运行阶段同上...
FROM alpine:3.19
# ...（同上）
```

### 3. Docker Compose 配置

```yaml
# docker-compose.yml

version: '3.9'

services:
  # Go应用
  app:
    build:
      context: .
      dockerfile: Dockerfile
    container_name: go-otlp-app
    restart: unless-stopped
    ports:
      - "8080:8080"
      - "9090:9090"
    environment:
      # 应用配置
      - APP_NAME=my-go-app
      - APP_VERSION=1.0.0
      - APP_ENV=production
      
      # OTLP配置
      - OTLP_ENDPOINT=otel-collector:4317
      - OTLP_INSECURE=true
      - OTLP_COMPRESSION=true
      - OTLP_SAMPLE_RATE=1.0
      
      # 资源配置
      - MAX_CONCURRENCY=100
      - REQUEST_TIMEOUT=30s
      
      # 数据库配置
      - DATABASE_URL=postgres://user:pass@postgres:5432/mydb
      - DATABASE_MAX_CONNS=25
    depends_on:
      - otel-collector
      - postgres
    networks:
      - app-network
    healthcheck:
      test: ["CMD", "/app/app", "healthcheck"]
      interval: 30s
      timeout: 3s
      retries: 3
      start_period: 10s
    deploy:
      resources:
        limits:
          cpus: '2'
          memory: 1G
        reservations:
          cpus: '0.5'
          memory: 512M

  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.91.0
    container_name: otel-collector
    restart: unless-stopped
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./configs/otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # Health check
    networks:
      - app-network

  # Jaeger (追踪后端)
  jaeger:
    image: jaegertracing/all-in-one:1.52
    container_name: jaeger
    restart: unless-stopped
    ports:
      - "16686:16686" # Jaeger UI
      - "14250:14250" # gRPC
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - app-network

  # Prometheus (指标后端)
  prometheus:
    image: prom/prometheus:v2.48.0
    container_name: prometheus
    restart: unless-stopped
    volumes:
      - ./configs/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
    ports:
      - "9091:9090"
    networks:
      - app-network

  # Grafana (可视化)
  grafana:
    image: grafana/grafana:10.2.0
    container_name: grafana
    restart: unless-stopped
    volumes:
      - grafana-data:/var/lib/grafana
      - ./configs/grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_USERS_ALLOW_SIGN_UP=false
    ports:
      - "3000:3000"
    networks:
      - app-network

  # PostgreSQL
  postgres:
    image: postgres:16-alpine
    container_name: postgres
    restart: unless-stopped
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=pass
      - POSTGRES_DB=mydb
    volumes:
      - postgres-data:/var/lib/postgresql/data
    ports:
      - "5432:5432"
    networks:
      - app-network

networks:
  app-network:
    driver: bridge

volumes:
  prometheus-data:
  grafana-data:
  postgres-data:
```

---

## Kubernetes部署

### 4. Kubernetes Deployment

```yaml
# k8s/deployment.yaml

apiVersion: apps/v1
kind: Deployment
metadata:
  name: go-otlp-app
  namespace: production
  labels:
    app: go-otlp-app
    version: v1.0.0
spec:
  replicas: 3
  revisionHistoryLimit: 10
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  selector:
    matchLabels:
      app: go-otlp-app
  template:
    metadata:
      labels:
        app: go-otlp-app
        version: v1.0.0
      annotations:
        # Prometheus 抓取配置
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
        
        # Sidecar注入（如果使用）
        sidecar.opentelemetry.io/inject: "true"
    spec:
      # 服务账户
      serviceAccountName: go-otlp-app
      
      # 安全上下文
      securityContext:
        runAsNonRoot: true
        runAsUser: 1000
        fsGroup: 1000
      
      # 初始化容器
      initContainers:
        - name: wait-for-collector
          image: busybox:1.36
          command: ['sh', '-c', 'until nc -z otel-collector 4317; do sleep 2; done']
      
      # 应用容器
      containers:
        - name: app
          image: myregistry/go-otlp-app:1.0.0
          imagePullPolicy: IfNotPresent
          
          ports:
            - name: http
              containerPort: 8080
              protocol: TCP
            - name: metrics
              containerPort: 9090
              protocol: TCP
          
          # 环境变量
          env:
            - name: APP_NAME
              value: "go-otlp-app"
            - name: APP_VERSION
              value: "1.0.0"
            - name: APP_ENV
              value: "production"
            
            # OTLP配置
            - name: OTLP_ENDPOINT
              value: "otel-collector.observability:4317"
            - name: OTLP_INSECURE
              value: "false"
            - name: OTLP_SAMPLE_RATE
              value: "0.1"
            
            # Kubernetes元数据
            - name: POD_NAME
              valueFrom:
                fieldRef:
                  fieldPath: metadata.name
            - name: POD_NAMESPACE
              valueFrom:
                fieldRef:
                  fieldPath: metadata.namespace
            - name: POD_IP
              valueFrom:
                fieldRef:
                  fieldPath: status.podIP
            - name: NODE_NAME
              valueFrom:
                fieldRef:
                  fieldPath: spec.nodeName
          
          # 资源限制
          resources:
            requests:
              cpu: "500m"
              memory: "512Mi"
            limits:
              cpu: "2000m"
              memory: "1Gi"
          
          # 健康检查
          livenessProbe:
            httpGet:
              path: /healthz
              port: 8080
            initialDelaySeconds: 15
            periodSeconds: 20
            timeoutSeconds: 3
            failureThreshold: 3
          
          readinessProbe:
            httpGet:
              path: /readyz
              port: 8080
            initialDelaySeconds: 5
            periodSeconds: 10
            timeoutSeconds: 3
            failureThreshold: 3
          
          # 启动探针
          startupProbe:
            httpGet:
              path: /healthz
              port: 8080
            initialDelaySeconds: 0
            periodSeconds: 5
            timeoutSeconds: 3
            failureThreshold: 30
          
          # 挂载卷
          volumeMounts:
            - name: config
              mountPath: /app/configs
              readOnly: true
      
      # 卷定义
      volumes:
        - name: config
          configMap:
            name: go-otlp-app-config
      
      # Pod反亲和性（高可用）
      affinity:
        podAntiAffinity:
          preferredDuringSchedulingIgnoredDuringExecution:
            - weight: 100
              podAffinityTerm:
                labelSelector:
                  matchExpressions:
                    - key: app
                      operator: In
                      values:
                        - go-otlp-app
                topologyKey: kubernetes.io/hostname
```

### 5. Kubernetes Service

```yaml
# k8s/service.yaml

apiVersion: v1
kind: Service
metadata:
  name: go-otlp-app
  namespace: production
  labels:
    app: go-otlp-app
spec:
  type: ClusterIP
  selector:
    app: go-otlp-app
  ports:
    - name: http
      port: 80
      targetPort: 8080
      protocol: TCP
    - name: metrics
      port: 9090
      targetPort: 9090
      protocol: TCP
  sessionAffinity: None

---
# Headless Service (用于StatefulSet或服务发现)
apiVersion: v1
kind: Service
metadata:
  name: go-otlp-app-headless
  namespace: production
spec:
  clusterIP: None
  selector:
    app: go-otlp-app
  ports:
    - name: http
      port: 8080
      targetPort: 8080
```

### 6. HorizontalPodAutoscaler

```yaml
# k8s/hpa.yaml

apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: go-otlp-app-hpa
  namespace: production
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: go-otlp-app
  minReplicas: 3
  maxReplicas: 10
  metrics:
    # CPU利用率
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    
    # 内存利用率
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 80
    
    # 自定义指标（HTTP请求率）
    - type: Pods
      pods:
        metric:
          name: http_requests_per_second
        target:
          type: AverageValue
          averageValue: "1000"
  
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
        - type: Percent
          value: 50
          periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
        - type: Percent
          value: 100
          periodSeconds: 30
        - type: Pods
          value: 2
          periodSeconds: 30
      selectPolicy: Max
```

### 7. ConfigMap

```yaml
# k8s/configmap.yaml

apiVersion: v1
kind: ConfigMap
metadata:
  name: go-otlp-app-config
  namespace: production
data:
  app.yaml: |
    app:
      name: go-otlp-app
      version: 1.0.0
      environment: production
    
    server:
      port: 8080
      read_timeout: 30s
      write_timeout: 30s
      idle_timeout: 120s
    
    otlp:
      endpoint: otel-collector.observability:4317
      insecure: false
      compression: true
      sample_rate: 0.1
      batch:
        max_size: 512
        timeout: 5s
        max_queue: 2048
    
    database:
      url: postgres://user:pass@postgres:5432/mydb
      max_conns: 25
      max_idle: 5
      conn_max_lifetime: 5m
```

### 8. ServiceAccount 和 RBAC

```yaml
# k8s/rbac.yaml

apiVersion: v1
kind: ServiceAccount
metadata:
  name: go-otlp-app
  namespace: production

---
apiVersion: rbac.authorization.k8s.io/v1
kind: Role
metadata:
  name: go-otlp-app-role
  namespace: production
rules:
  - apiGroups: [""]
    resources: ["configmaps"]
    verbs: ["get", "list", "watch"]
  - apiGroups: [""]
    resources: ["secrets"]
    verbs: ["get"]

---
apiVersion: rbac.authorization.k8s.io/v1
kind: RoleBinding
metadata:
  name: go-otlp-app-rolebinding
  namespace: production
subjects:
  - kind: ServiceAccount
    name: go-otlp-app
    namespace: production
roleRef:
  kind: Role
  name: go-otlp-app-role
  apiGroup: rbac.authorization.k8s.io
```

---

## 服务网格集成

### 9. Istio集成

```yaml
# k8s/istio/virtualservice.yaml

apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: go-otlp-app
  namespace: production
spec:
  hosts:
    - go-otlp-app
    - go-otlp-app.production.svc.cluster.local
  http:
    - match:
        - headers:
            x-version:
              exact: canary
      route:
        - destination:
            host: go-otlp-app
            subset: v1-1-0
          weight: 10
        - destination:
            host: go-otlp-app
            subset: v1-0-0
          weight: 90
    - route:
        - destination:
            host: go-otlp-app
            subset: v1-0-0

---
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: go-otlp-app
  namespace: production
spec:
  host: go-otlp-app
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        http2MaxRequests: 100
        maxRequestsPerConnection: 2
    loadBalancer:
      simple: LEAST_REQUEST
    outlierDetection:
      consecutiveErrors: 5
      interval: 30s
      baseEjectionTime: 30s
      maxEjectionPercent: 50
  subsets:
    - name: v1-0-0
      labels:
        version: v1.0.0
    - name: v1-1-0
      labels:
        version: v1.1.0
```

---

## 自动注入

### 10. OpenTelemetry Operator

```yaml
# k8s/otel-operator/instrumentation.yaml

apiVersion: opentelemetry.io/v1alpha1
kind: Instrumentation
metadata:
  name: go-instrumentation
  namespace: production
spec:
  exporter:
    endpoint: http://otel-collector.observability:4318
  propagators:
    - tracecontext
    - baggage
  sampler:
    type: parentbased_traceidratio
    argument: "0.1"
  go:
    image: ghcr.io/open-telemetry/opentelemetry-go-instrumentation/autoinstrumentation-go:latest
    env:
      - name: OTEL_GO_AUTO_TARGET_EXE
        value: "/app/app"
      - name: OTEL_SERVICE_NAME
        value: "go-otlp-app"
```

---

## 资源限制

### 11. ResourceQuota 和 LimitRange

```yaml
# k8s/resource-limits.yaml

apiVersion: v1
kind: ResourceQuota
metadata:
  name: production-quota
  namespace: production
spec:
  hard:
    requests.cpu: "50"
    requests.memory: "100Gi"
    limits.cpu: "100"
    limits.memory: "200Gi"
    persistentvolumeclaims: "10"
    services: "20"

---
apiVersion: v1
kind: LimitRange
metadata:
  name: production-limitrange
  namespace: production
spec:
  limits:
    - max:
        cpu: "4"
        memory: "8Gi"
      min:
        cpu: "100m"
        memory: "128Mi"
      default:
        cpu: "1"
        memory: "1Gi"
      defaultRequest:
        cpu: "500m"
        memory: "512Mi"
      type: Container
```

---

## 日志收集

### 12. Fluent Bit 配置

```yaml
# k8s/logging/fluent-bit-config.yaml

apiVersion: v1
kind: ConfigMap
metadata:
  name: fluent-bit-config
  namespace: logging
data:
  fluent-bit.conf: |
    [SERVICE]
        Flush         5
        Log_Level     info
        Daemon        off
        
    [INPUT]
        Name              tail
        Path              /var/log/containers/go-otlp-app*.log
        Parser            docker
        Tag               kube.*
        Refresh_Interval  5
        Mem_Buf_Limit     5MB
        Skip_Long_Lines   On
        
    [FILTER]
        Name                kubernetes
        Match               kube.*
        Kube_URL            https://kubernetes.default.svc:443
        Kube_CA_File        /var/run/secrets/kubernetes.io/serviceaccount/ca.crt
        Kube_Token_File     /var/run/secrets/kubernetes.io/serviceaccount/token
        Merge_Log           On
        K8S-Logging.Parser  On
        K8S-Logging.Exclude On
        
    [OUTPUT]
        Name   forward
        Match  *
        Host   fluentd.logging
        Port   24224
```

---

## 总结

本文档提供了 Go + OpenTelemetry 应用的完整容器化和 Kubernetes 部署方案，包括：

1. ✅ **Docker** - 多阶段构建、优化镜像
2. ✅ **Kubernetes** - Deployment、Service、HPA
3. ✅ **服务网格** - Istio集成、流量管理
4. ✅ **自动注入** - OpenTelemetry Operator
5. ✅ **资源管理** - Quota、LimitRange
6. ✅ **日志收集** - Fluent Bit配置

### 相关文档

- [生产级部署最佳实践](./07_Go生产级部署与运维最佳实践.md)
- [监控告警](./09_Go监控告警最佳实践.md)

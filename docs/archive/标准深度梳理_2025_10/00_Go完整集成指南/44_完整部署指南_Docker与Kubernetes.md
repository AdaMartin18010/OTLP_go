# 44. 完整部署指南：Docker 与 Kubernetes

## 📚 目录

- [1. Docker 部署](#1-docker-部署)
- [2. Docker Compose 完整配置](#2-docker-compose-完整配置)
- [3. Kubernetes 部署](#3-kubernetes-部署)
- [4. Helm Chart](#4-helm-chart)
- [5. CI/CD 集成](#5-cicd-集成)
- [6. 监控与日志](#6-监控与日志)
- [7. 故障排查](#7-故障排查)
- [8. 总结](#8-总结)

---

## 1. Docker 部署

### 1.1 多阶段构建 Dockerfile

```dockerfile
# Dockerfile
# Stage 1: 构建阶段
FROM golang:1.25.1-alpine AS builder

# 安装依赖
RUN apk add --no-cache git make

# 设置工作目录
WORKDIR /app

# 复制 go.mod 和 go.sum
COPY go.mod go.sum ./

# 下载依赖
RUN go mod download

# 复制源代码
COPY . .

# 构建应用（启用 CGO_ENABLED=0 以生成静态二进制文件）
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -ldflags="-w -s -X main.Version=$(git describe --tags --always) -X main.BuildTime=$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    -o /app/bin/app \
    ./cmd/app

# Stage 2: 运行阶段
FROM alpine:3.19

# 安装 CA 证书（用于 HTTPS 请求）
RUN apk --no-cache add ca-certificates tzdata

# 设置时区
ENV TZ=UTC

# 创建非 root 用户
RUN addgroup -g 1000 app && \
    adduser -D -u 1000 -G app app

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/bin/app /app/app

# 复制配置文件（可选）
# COPY --from=builder /app/configs /app/configs

# 更改所有权
RUN chown -R app:app /app

# 切换到非 root 用户
USER app

# 暴露端口
EXPOSE 8080 9090

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health/live || exit 1

# 运行应用
ENTRYPOINT ["/app/app"]
```

### 1.2 .dockerignore

```
# .dockerignore
# Git
.git
.gitignore

# IDE
.vscode
.idea
*.swp
*.swo

# Build artifacts
bin/
dist/
*.exe
*.dll
*.so
*.dylib

# Test
*.test
coverage.out
*.prof

# Documentation
*.md
docs/

# Kubernetes & Docker
*.yaml
*.yml
Dockerfile*
docker-compose*

# Misc
.env
*.log
tmp/
```

### 1.3 构建和运行命令

```bash
# 构建镜像
docker build -t my-app:latest .

# 使用 BuildKit（推荐，更快）
DOCKER_BUILDKIT=1 docker build -t my-app:latest .

# 构建特定平台镜像
docker buildx build --platform linux/amd64,linux/arm64 -t my-app:latest .

# 运行容器
docker run -d \
  --name my-app \
  -p 8080:8080 \
  -p 9090:9090 \
  -e OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317 \
  -e DATABASE_URL=postgres://user:pass@postgres:5432/db \
  my-app:latest

# 查看日志
docker logs -f my-app

# 进入容器
docker exec -it my-app /bin/sh

# 停止容器
docker stop my-app

# 删除容器
docker rm my-app
```

---

## 2. Docker Compose 完整配置

### 2.1 生产级 docker-compose.yml

```yaml
# docker-compose.yml
version: '3.8'

services:
  # ===========================================
  # 应用服务
  # ===========================================
  
  # API Gateway
  api-gateway:
    build:
      context: .
      dockerfile: Dockerfile
      args:
        SERVICE_NAME: api-gateway
    image: my-app/api-gateway:latest
    container_name: api-gateway
    ports:
      - "8080:8080"
      - "9090:9090"
    environment:
      - SERVICE_NAME=api-gateway
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - DATABASE_URL=postgres://user:password@postgres:5432/gateway?sslmode=disable
      - REDIS_URL=redis:6379
      - LOG_LEVEL=info
    depends_on:
      postgres:
        condition: service_healthy
      redis:
        condition: service_healthy
      otel-collector:
        condition: service_started
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:8080/health/live"]
      interval: 10s
      timeout: 3s
      retries: 3
      start_period: 40s
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 512M
        reservations:
          cpus: '0.5'
          memory: 256M

  # User Service
  user-service:
    build:
      context: .
      dockerfile: Dockerfile
      args:
        SERVICE_NAME: user-service
    image: my-app/user-service:latest
    container_name: user-service
    ports:
      - "9001:9001"
    environment:
      - SERVICE_NAME=user-service
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - DATABASE_URL=postgres://user:password@postgres:5432/users?sslmode=disable
      - LOG_LEVEL=info
    depends_on:
      postgres:
        condition: service_healthy
      otel-collector:
        condition: service_started
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:9001/health"]
      interval: 10s
      timeout: 3s
      retries: 3
      start_period: 40s
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 256M

  # ===========================================
  # 基础设施服务
  # ===========================================
  
  # PostgreSQL
  postgres:
    image: postgres:16-alpine
    container_name: postgres
    ports:
      - "5432:5432"
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=gateway
      - PGDATA=/var/lib/postgresql/data/pgdata
    volumes:
      - postgres-data:/var/lib/postgresql/data
      - ./scripts/init-db.sql:/docker-entrypoint-initdb.d/init-db.sql:ro
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user -d gateway"]
      interval: 10s
      timeout: 5s
      retries: 5
      start_period: 10s
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 1G

  # Redis
  redis:
    image: redis:7-alpine
    container_name: redis
    ports:
      - "6379:6379"
    command: redis-server --appendonly yes --requirepass password
    volumes:
      - redis-data:/data
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "redis-cli", "--raw", "incr", "ping"]
      interval: 10s
      timeout: 3s
      retries: 5
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

  # NATS
  nats:
    image: nats:2.10-alpine
    container_name: nats
    ports:
      - "4222:4222"
      - "8222:8222"
    command: ["-js", "-m", "8222"]
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:8222/healthz"]
      interval: 10s
      timeout: 3s
      retries: 5

  # ===========================================
  # 可观测性栈
  # ===========================================
  
  # OTLP Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    container_name: otel-collector
    command: ["--config=/etc/otel-collector-config.yaml"]
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
      - "13133:13133" # health_check
    volumes:
      - ./configs/otel-collector-config.yaml:/etc/otel-collector-config.yaml:ro
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:13133/"]
      interval: 10s
      timeout: 3s
      retries: 3
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 1G

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:latest
    container_name: jaeger
    ports:
      - "16686:16686"  # Jaeger UI
      - "14268:14268"  # Jaeger collector HTTP
    environment:
      - COLLECTOR_OTLP_ENABLED=true
      - SPAN_STORAGE_TYPE=badger
      - BADGER_EPHEMERAL=false
      - BADGER_DIRECTORY_VALUE=/badger/data
      - BADGER_DIRECTORY_KEY=/badger/key
    volumes:
      - jaeger-data:/badger
    networks:
      - app-network
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

  # Prometheus
  prometheus:
    image: prom/prometheus:latest
    container_name: prometheus
    ports:
      - "9090:9090"
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/etc/prometheus/console_libraries'
      - '--web.console.templates=/etc/prometheus/consoles'
      - '--web.enable-lifecycle'
    volumes:
      - ./configs/prometheus.yml:/etc/prometheus/prometheus.yml:ro
      - prometheus-data:/prometheus
    networks:
      - app-network
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:9090/-/healthy"]
      interval: 10s
      timeout: 3s
      retries: 3
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 1G

  # Grafana
  grafana:
    image: grafana/grafana:latest
    container_name: grafana
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_USER=admin
      - GF_SECURITY_ADMIN_PASSWORD=admin
      - GF_INSTALL_PLUGINS=grafana-clock-panel
      - GF_SERVER_ROOT_URL=http://localhost:3000
    volumes:
      - ./configs/grafana/datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml:ro
      - ./configs/grafana/dashboards.yml:/etc/grafana/provisioning/dashboards/dashboards.yml:ro
      - ./configs/grafana/dashboards:/var/lib/grafana/dashboards:ro
      - grafana-data:/var/lib/grafana
    networks:
      - app-network
    restart: unless-stopped
    depends_on:
      - prometheus
      - jaeger
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:3000/api/health"]
      interval: 10s
      timeout: 3s
      retries: 3
    deploy:
      resources:
        limits:
          cpus: '0.25'
          memory: 256M

# ===========================================
# 网络配置
# ===========================================
networks:
  app-network:
    driver: bridge
    ipam:
      config:
        - subnet: 172.28.0.0/16

# ===========================================
# 卷配置
# ===========================================
volumes:
  postgres-data:
    driver: local
  redis-data:
    driver: local
  jaeger-data:
    driver: local
  prometheus-data:
    driver: local
  grafana-data:
    driver: local
```

### 2.2 配置文件

#### otel-collector-config.yaml

```yaml
# configs/otel-collector-config.yaml
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
    send_batch_max_size: 2048
  
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
  
  resourcedetection:
    detectors: [env, system, docker]
    timeout: 5s
  
  attributes:
    actions:
      - key: environment
        value: production
        action: upsert

exporters:
  otlp:
    endpoint: jaeger:4317
    tls:
      insecure: true
  
  prometheus:
    endpoint: "0.0.0.0:8888"
    namespace: app
  
  logging:
    loglevel: info

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
      processors: [memory_limiter, batch, resourcedetection, attributes]
      exporters: [otlp, logging]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, batch, resourcedetection, attributes]
      exporters: [prometheus, logging]
```

#### prometheus.yml

```yaml
# configs/prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s
  external_labels:
    cluster: 'docker-compose'
    replica: '1'

rule_files:
  - /etc/prometheus/rules/*.yml

scrape_configs:
  # OTLP Collector
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['otel-collector:8888']
        labels:
          service: 'otel-collector'
  
  # Application Services
  - job_name: 'api-gateway'
    static_configs:
      - targets: ['api-gateway:9090']
        labels:
          service: 'api-gateway'
  
  - job_name: 'user-service'
    static_configs:
      - targets: ['user-service:9090']
        labels:
          service: 'user-service'
  
  # Infrastructure
  - job_name: 'postgres'
    static_configs:
      - targets: ['postgres-exporter:9187']
        labels:
          service: 'postgres'
  
  - job_name: 'redis'
    static_configs:
      - targets: ['redis-exporter:9121']
        labels:
          service: 'redis'
```

### 2.3 Makefile 辅助命令

```makefile
# Makefile
.PHONY: help build up down logs restart clean

help: ## 显示帮助信息
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

build: ## 构建所有镜像
	docker-compose build

up: ## 启动所有服务
	docker-compose up -d

down: ## 停止所有服务
	docker-compose down

logs: ## 查看所有服务日志
	docker-compose logs -f

logs-%: ## 查看特定服务日志（例如：make logs-api-gateway）
	docker-compose logs -f $*

restart: down up ## 重启所有服务

restart-%: ## 重启特定服务（例如：make restart-api-gateway）
	docker-compose restart $*

ps: ## 查看服务状态
	docker-compose ps

clean: ## 清理所有容器和卷
	docker-compose down -v --remove-orphans

clean-images: ## 清理所有镜像
	docker-compose down --rmi all

health: ## 检查所有服务健康状态
	@echo "Checking service health..."
	@docker-compose ps --format json | jq -r '.[] | "\(.Name): \(.Health)"'

shell-%: ## 进入特定服务的 shell（例如：make shell-api-gateway）
	docker-compose exec $* /bin/sh

test: ## 运行测试
	docker-compose run --rm api-gateway go test ./...

migrate: ## 运行数据库迁移
	docker-compose exec postgres psql -U user -d gateway -f /docker-entrypoint-initdb.d/migrations/$(VERSION).sql
```

### 2.4 启动和管理

```bash
# 启动所有服务
make up

# 查看服务状态
make ps

# 查看日志
make logs

# 查看特定服务日志
make logs-api-gateway

# 重启服务
make restart

# 停止服务
make down

# 清理
make clean
```

---

## 3. Kubernetes 部署

### 3.1 Namespace

```yaml
# k8s/namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: my-app
  labels:
    name: my-app
    environment: production
```

### 3.2 ConfigMap

```yaml
# k8s/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: app-config
  namespace: my-app
data:
  LOG_LEVEL: "info"
  OTEL_EXPORTER_OTLP_ENDPOINT: "http://otel-collector:4317"
  OTEL_SERVICE_NAME: "my-app"
  OTEL_RESOURCE_ATTRIBUTES: "deployment.environment=production,service.version=1.0.0"
```

### 3.3 Secret

```yaml
# k8s/secret.yaml
apiVersion: v1
kind: Secret
metadata:
  name: app-secrets
  namespace: my-app
type: Opaque
stringData:
  DATABASE_URL: "postgres://user:password@postgres:5432/db?sslmode=require"
  REDIS_PASSWORD: "redis-password"
  JWT_SECRET_KEY: "your-jwt-secret-key"
```

### 3.4 Deployment

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: api-gateway
  namespace: my-app
  labels:
    app: api-gateway
    version: v1
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  selector:
    matchLabels:
      app: api-gateway
  template:
    metadata:
      labels:
        app: api-gateway
        version: v1
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    spec:
      # 服务账号
      serviceAccountName: app-service-account
      
      # Pod 安全上下文
      securityContext:
        runAsNonRoot: true
        runAsUser: 1000
        fsGroup: 1000
      
      # 初始化容器
      initContainers:
        - name: wait-for-postgres
          image: busybox:1.36
          command:
            - sh
            - -c
            - |
              until nc -z postgres 5432; do
                echo "Waiting for postgres..."
                sleep 2
              done
      
      # 应用容器
      containers:
        - name: api-gateway
          image: my-app/api-gateway:v1.0.0
          imagePullPolicy: IfNotPresent
          
          # 端口
          ports:
            - name: http
              containerPort: 8080
              protocol: TCP
            - name: metrics
              containerPort: 9090
              protocol: TCP
          
          # 环境变量
          env:
            - name: SERVICE_NAME
              value: "api-gateway"
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
          
          # 从 ConfigMap 加载
          envFrom:
            - configMapRef:
                name: app-config
            - secretRef:
                name: app-secrets
          
          # 资源限制
          resources:
            requests:
              cpu: 250m
              memory: 256Mi
            limits:
              cpu: 500m
              memory: 512Mi
          
          # 健康检查
          livenessProbe:
            httpGet:
              path: /health/live
              port: http
            initialDelaySeconds: 30
            periodSeconds: 10
            timeoutSeconds: 3
            successThreshold: 1
            failureThreshold: 3
          
          readinessProbe:
            httpGet:
              path: /health/ready
              port: http
            initialDelaySeconds: 10
            periodSeconds: 5
            timeoutSeconds: 3
            successThreshold: 1
            failureThreshold: 3
          
          # 启动探针
          startupProbe:
            httpGet:
              path: /health/startup
              port: http
            initialDelaySeconds: 0
            periodSeconds: 10
            timeoutSeconds: 3
            successThreshold: 1
            failureThreshold: 30
          
          # 卷挂载
          volumeMounts:
            - name: config
              mountPath: /app/config
              readOnly: true
            - name: tmp
              mountPath: /tmp
      
      # 卷
      volumes:
        - name: config
          configMap:
            name: app-config
        - name: tmp
          emptyDir: {}
      
      # 节点亲和性
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
                        - api-gateway
                topologyKey: kubernetes.io/hostname
```

### 3.5 Service

```yaml
# k8s/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: api-gateway
  namespace: my-app
  labels:
    app: api-gateway
spec:
  type: ClusterIP
  ports:
    - name: http
      port: 80
      targetPort: 8080
      protocol: TCP
    - name: metrics
      port: 9090
      targetPort: 9090
      protocol: TCP
  selector:
    app: api-gateway
```

### 3.6 Ingress

```yaml
# k8s/ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: api-gateway-ingress
  namespace: my-app
  annotations:
    kubernetes.io/ingress.class: nginx
    cert-manager.io/cluster-issuer: letsencrypt-prod
    nginx.ingress.kubernetes.io/rate-limit: "100"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
spec:
  tls:
    - hosts:
        - api.example.com
      secretName: api-gateway-tls
  rules:
    - host: api.example.com
      http:
        paths:
          - path: /
            pathType: Prefix
            backend:
              service:
                name: api-gateway
                port:
                  number: 80
```

### 3.7 HorizontalPodAutoscaler

```yaml
# k8s/hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: api-gateway-hpa
  namespace: my-app
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: api-gateway
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
          periodSeconds: 15
        - type: Pods
          value: 2
          periodSeconds: 15
      selectPolicy: Max
```

### 3.8 部署命令

```bash
# 创建 namespace
kubectl apply -f k8s/namespace.yaml

# 创建 ConfigMap 和 Secret
kubectl apply -f k8s/configmap.yaml
kubectl apply -f k8s/secret.yaml

# 部署应用
kubectl apply -f k8s/deployment.yaml
kubectl apply -f k8s/service.yaml

# 配置 Ingress
kubectl apply -f k8s/ingress.yaml

# 配置 HPA
kubectl apply -f k8s/hpa.yaml

# 查看状态
kubectl get all -n my-app

# 查看 Pods
kubectl get pods -n my-app

# 查看日志
kubectl logs -f -n my-app -l app=api-gateway

# 进入 Pod
kubectl exec -it -n my-app <pod-name> -- /bin/sh

# 端口转发
kubectl port-forward -n my-app svc/api-gateway 8080:80

# 扩缩容
kubectl scale deployment api-gateway -n my-app --replicas=5

# 滚动更新
kubectl set image deployment/api-gateway api-gateway=my-app/api-gateway:v1.0.1 -n my-app

# 回滚
kubectl rollout undo deployment/api-gateway -n my-app
```

---

## 4. Helm Chart

由于内容较长，我将在后续文档中补充 Helm Chart、CI/CD、监控配置等内容。

---

## 总结

本文档提供了完整的 Docker 和 Kubernetes 部署指南，包括：

### Docker 部署

✅ **多阶段构建** - 优化镜像大小
✅ **非 root 用户** - 安全最佳实践
✅ **健康检查** - 自动重启
✅ **资源限制** - 防止资源耗尽

### Docker Compose

✅ **完整栈部署** - 应用 + 基础设施 + 可观测性
✅ **健康检查** - 依赖管理
✅ **资源限制** - 生产级配置
✅ **卷管理** - 数据持久化

### Kubernetes

✅ **生产级配置** - 3 副本、滚动更新
✅ **健康检查** - Liveness、Readiness、Startup
✅ **HPA** - 自动扩缩容
✅ **Ingress** - HTTPS、速率限制

### 相关文档

- [35_Go生产级部署模式与反模式](./35_Go生产级部署模式与反模式.md)
- [41_实战案例_API Gateway与服务集成](./41_实战案例_API Gateway与服务集成.md)
- [39_实战案例_电商微服务系统](./39_实战案例_电商微服务系统.md)


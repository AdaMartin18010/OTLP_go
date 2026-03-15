# OpenTelemetry GCP 集成指南

> **最后更新**: 2025年10月8日  
> **目标读者**: GCP架构师、DevOps工程师

---

## 目录

- [OpenTelemetry GCP 集成指南](#opentelemetry-gcp-集成指南)
  - [目录](#目录)
  - [1. GCP集成概述](#1-gcp集成概述)
    - [1.1 为什么在GCP上使用OpenTelemetry](#11-为什么在gcp上使用opentelemetry)
    - [1.2 GCP服务与OpenTelemetry](#12-gcp服务与opentelemetry)
  - [2. Cloud Trace集成](#2-cloud-trace集成)
    - [2.1 Cloud Trace Exporter](#21-cloud-trace-exporter)
    - [2.2 完整配置](#22-完整配置)
  - [3. GKE集成](#3-gke集成)
    - [3.1 Autopilot模式](#31-autopilot模式)
    - [3.2 Standard模式](#32-standard模式)
  - [4. Cloud Run集成](#4-cloud-run集成)
    - [4.1 Sidecar模式](#41-sidecar模式)
    - [4.2 完整示例](#42-完整示例)
  - [5. Cloud Functions集成](#5-cloud-functions集成)
  - [6. Compute Engine集成](#6-compute-engine集成)
  - [7. Cloud Monitoring集成](#7-cloud-monitoring集成)
  - [8. GCP服务追踪](#8-gcp服务追踪)
    - [8.1 Firestore追踪](#81-firestore追踪)
    - [8.2 Cloud Storage追踪](#82-cloud-storage追踪)
    - [8.3 Pub/Sub追踪](#83-pubsub追踪)
  - [9. Resource检测](#9-resource检测)
  - [10. 成本优化](#10-成本优化)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 参考资源](#12-参考资源)

---

## 1. GCP集成概述

### 1.1 为什么在GCP上使用OpenTelemetry

**价值**：

```text
1. 供应商中立
   - 不锁定Cloud Trace
   - 可切换到其他后端
   - 多云策略支持

2. 统一标准
   - OpenTelemetry标准
   - 跨云平台一致性
   - 社区生态丰富

3. 灵活路由
   - Cloud Trace + Jaeger
   - Cloud Monitoring + Prometheus
   - 多后端并行

4. 成本控制
   - 采样策略
   - 数据过滤
   - 智能路由

5. 高级功能
   - Tail-based采样
   - 自定义处理
   - 数据转换

架构示例:
应用 → OTel Collector → Cloud Trace + Prometheus + BigQuery
- Traces → Cloud Trace (实时查询)
- Metrics → Cloud Monitoring (告警)
- Raw Data → BigQuery (分析)
```

### 1.2 GCP服务与OpenTelemetry

```text
支持的GCP服务:

计算:
- GKE (Kubernetes)
- Cloud Run
- Cloud Functions
- Compute Engine
- App Engine

后端:
- Cloud Trace (Traces)
- Cloud Monitoring (Metrics)
- Cloud Logging (Logs)

集成:
- Firestore
- Cloud Storage
- Pub/Sub
- Cloud Spanner
- Cloud SQL
- Memorystore
```

---

## 2. Cloud Trace集成

### 2.1 Cloud Trace Exporter

**Collector配置**：

```yaml
# config.yaml
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
    send_batch_size: 256
  
  memory_limiter:
    limit_mib: 512
    spike_limit_mib: 128
  
  # Resource检测
  resourcedetection/gcp:
    detectors: [gcp]
    timeout: 2s

exporters:
  # Cloud Trace exporter
  googlecloud:
    project: "my-gcp-project"
    # 使用应用默认凭证
    use_insecure: false
    
    # Trace配置
    trace:
      endpoint: "cloudtrace.googleapis.com:443"
    
    # Metric配置  
    metric:
      endpoint: "monitoring.googleapis.com:443"
      # 资源映射
      resource_filters:
        - prefix: "k8s."
        - prefix: "cloud."
  
  # 备用后端
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection/gcp, batch]
      exporters: [googlecloud, otlp/jaeger]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection/gcp, batch]
      exporters: [googlecloud]
```

### 2.2 完整配置

**Go SDK配置**：

```go
package main

import (
    "context"
    "log"
    
    texporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/trace"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()
    
    // 创建Cloud Trace exporter
    exporter, err := texporter.New(
        texporter.WithProjectID("my-gcp-project"),
        texporter.WithTraceClientOptions([]option.ClientOption{
            // 可选: 自定义凭证
            // option.WithCredentialsFile("/path/to/key.json"),
        }),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("order-service"),
            semconv.ServiceVersion("1.2.3"),
            semconv.DeploymentEnvironment("production"),
        ),
        // 自动检测GCP资源
        resource.WithDetectors(gcp.NewDetector()),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.1)), // 10%采样
    )
    
    otel.SetTracerProvider(tp)
    
    return tp, nil
}

func main() {
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())
    
    // 使用tracer
    tracer := otel.Tracer("my-app")
    ctx, span := tracer.Start(context.Background(), "main")
    defer span.End()
    
    // 业务逻辑
    // ...
}
```

---

## 3. GKE集成

### 3.1 Autopilot模式

**部署Collector**：

```yaml
# otel-collector.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-collector-config
  namespace: observability
data:
  config.yaml: |
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
        send_batch_size: 256
      
      memory_limiter:
        limit_mib: 512
        spike_limit_mib: 128
      
      # GCP资源检测
      resourcedetection:
        detectors: [gcp, env]
        timeout: 2s
      
      # K8s属性
      k8sattributes:
        auth_type: "serviceAccount"
        passthrough: false
        extract:
          metadata:
            - k8s.namespace.name
            - k8s.deployment.name
            - k8s.pod.name
            - k8s.pod.uid
            - k8s.node.name
          labels:
            - tag_name: app
              key: app
              from: pod
    
    exporters:
      googlecloud:
        project: "my-gcp-project"
        use_insecure: false
      
      logging:
        loglevel: info
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, resourcedetection, k8sattributes, batch]
          exporters: [googlecloud, logging]

---
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: observability
spec:
  replicas: 2
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
        args:
          - --config=/conf/config.yaml
        ports:
        - containerPort: 4317
          name: otlp-grpc
          protocol: TCP
        - containerPort: 4318
          name: otlp-http
          protocol: TCP
        volumeMounts:
        - name: config
          mountPath: /conf
        resources:
          requests:
            cpu: 200m
            memory: 256Mi
          limits:
            cpu: 1000m
            memory: 512Mi
        env:
        - name: GOOGLE_APPLICATION_CREDENTIALS
          value: /var/secrets/google/key.json
      volumes:
      - name: config
        configMap:
          name: otel-collector-config

---
apiVersion: v1
kind: Service
metadata:
  name: otel-collector
  namespace: observability
spec:
  type: ClusterIP
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

---
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability
  annotations:
    iam.gke.io/gcp-service-account: otel-collector@my-gcp-project.iam.gserviceaccount.com
```

**Workload Identity配置**：

```bash
# 1. 创建GCP Service Account
gcloud iam service-accounts create otel-collector \
  --display-name="OpenTelemetry Collector"

# 2. 授予权限
gcloud projects add-iam-policy-binding my-gcp-project \
  --member="serviceAccount:otel-collector@my-gcp-project.iam.gserviceaccount.com" \
  --role="roles/cloudtrace.agent"

gcloud projects add-iam-policy-binding my-gcp-project \
  --member="serviceAccount:otel-collector@my-gcp-project.iam.gserviceaccount.com" \
  --role="roles/monitoring.metricWriter"

# 3. 绑定K8s ServiceAccount
gcloud iam service-accounts add-iam-policy-binding \
  otel-collector@my-gcp-project.iam.gserviceaccount.com \
  --role roles/iam.workloadIdentityUser \
  --member "serviceAccount:my-gcp-project.svc.id.goog[observability/otel-collector]"
```

### 3.2 Standard模式

**DaemonSet部署**：

```yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector-agent
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector-agent
  template:
    metadata:
      labels:
        app: otel-collector-agent
    spec:
      serviceAccountName: otel-collector
      hostNetwork: true
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.90.0
        args:
          - --config=/conf/config.yaml
        ports:
        - containerPort: 4317
          hostPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          hostPort: 4318
          name: otlp-http
        volumeMounts:
        - name: config
          mountPath: /conf
        resources:
          requests:
            cpu: 100m
            memory: 128Mi
          limits:
            cpu: 500m
            memory: 256Mi
      volumes:
      - name: config
        configMap:
          name: otel-collector-config
```

---

## 4. Cloud Run集成

### 4.1 Sidecar模式

**docker-compose.yml (本地测试)**：

```yaml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - OTEL_SERVICE_NAME=order-service
      - OTEL_RESOURCE_ATTRIBUTES=deployment.environment=production
      - GOOGLE_CLOUD_PROJECT=my-gcp-project
    depends_on:
      - otel-collector
  
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.90.0
    command: ["--config=/etc/otel/config.yaml"]
    volumes:
      - ./otel-config.yaml:/etc/otel/config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
```

### 4.2 完整示例

**Dockerfile (Multi-stage)**：

```dockerfile
# Stage 1: Build
FROM golang:1.21 AS builder
WORKDIR /app
COPY . .
RUN CGO_ENABLED=0 go build -o app ./cmd/server

# Stage 2: Runtime with OTel Collector
FROM gcr.io/distroless/base-debian11
COPY --from=builder /app/app /app
COPY --from=otel/opentelemetry-collector-contrib:0.90.0 /otelcol-contrib /otelcol
COPY otel-config.yaml /etc/otel/config.yaml

# 启动脚本
COPY <<'EOF' /start.sh
#!/bin/sh
/otelcol --config=/etc/otel/config.yaml &
exec /app
EOF

RUN chmod +x /start.sh
ENTRYPOINT ["/start.sh"]
```

**Cloud Run部署**：

```bash
# 构建镜像
gcloud builds submit --tag gcr.io/my-gcp-project/order-service:v1.2.3

# 部署到Cloud Run
gcloud run deploy order-service \
  --image gcr.io/my-gcp-project/order-service:v1.2.3 \
  --platform managed \
  --region us-central1 \
  --allow-unauthenticated \
  --set-env-vars="GOOGLE_CLOUD_PROJECT=my-gcp-project" \
  --service-account=otel-collector@my-gcp-project.iam.gserviceaccount.com
```

**Terraform配置**：

```hcl
resource "google_cloud_run_service" "order_service" {
  name     = "order-service"
  location = "us-central1"
  
  template {
    spec {
      service_account_name = google_service_account.otel_collector.email
      
      containers {
        image = "gcr.io/my-gcp-project/order-service:v1.2.3"
        
        env {
          name  = "OTEL_EXPORTER_OTLP_ENDPOINT"
          value = "http://localhost:4317"
        }
        
        env {
          name  = "OTEL_SERVICE_NAME"
          value = "order-service"
        }
        
        env {
          name  = "GOOGLE_CLOUD_PROJECT"
          value = var.project_id
        }
        
        resources {
          limits = {
            cpu    = "2"
            memory = "1Gi"
          }
        }
      }
    }
    
    metadata {
      annotations = {
        "autoscaling.knative.dev/maxScale" = "100"
        "run.googleapis.com/execution-environment" = "gen2"
      }
    }
  }
  
  traffic {
    percent         = 100
    latest_revision = true
  }
}

resource "google_service_account" "otel_collector" {
  account_id   = "otel-collector"
  display_name = "OpenTelemetry Collector"
}

resource "google_project_iam_member" "otel_trace" {
  project = var.project_id
  role    = "roles/cloudtrace.agent"
  member  = "serviceAccount:${google_service_account.otel_collector.email}"
}
```

---

## 5. Cloud Functions集成

**Go Cloud Function**：

```go
package function

import (
    "context"
    "net/http"
    
    "github.com/GoogleCloudPlatform/functions-framework-go/functions"
    texporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/trace"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/sdk/trace"
)

var tracer = otel.Tracer("order-processor")

func init() {
    // 初始化追踪
    ctx := context.Background()
    exporter, _ := texporter.New(texporter.WithProjectID("my-gcp-project"))
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithSampler(trace.TraceIDRatioBased(0.1)),
    )
    
    otel.SetTracerProvider(tp)
    
    // 注册HTTP函数
    functions.HTTP("ProcessOrder", processOrder)
}

func processOrder(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    // 创建Span
    ctx, span := tracer.Start(ctx, "ProcessOrder")
    defer span.End()
    
    // 业务逻辑
    orderID := r.URL.Query().Get("order_id")
    span.SetAttributes(attribute.String("order.id", orderID))
    
    // 处理订单
    result := handleOrder(ctx, orderID)
    
    w.WriteHeader(http.StatusOK)
    w.Write([]byte(result))
}

func handleOrder(ctx context.Context, orderID string) string {
    _, span := tracer.Start(ctx, "HandleOrder")
    defer span.End()
    
    // 处理逻辑
    return "Order processed"
}
```

**部署**：

```bash
gcloud functions deploy process-order \
  --runtime go121 \
  --trigger-http \
  --allow-unauthenticated \
  --entry-point ProcessOrder \
  --set-env-vars GOOGLE_CLOUD_PROJECT=my-gcp-project \
  --service-account otel-collector@my-gcp-project.iam.gserviceaccount.com
```

---

## 6. Compute Engine集成

**启动脚本**：

```bash
#!/bin/bash

# 安装OTel Collector
curl -L https://github.com/open-telemetry/opentelemetry-collector-releases/releases/download/v0.90.0/otelcol-contrib_0.90.0_linux_amd64.tar.gz | tar xz
sudo mv otelcol-contrib /usr/local/bin/

# 配置文件
cat > /etc/otel-collector-config.yaml <<EOF
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

processors:
  batch:
  memory_limiter:
    limit_mib: 512
  resourcedetection:
    detectors: [gcp, env]

exporters:
  googlecloud:
    project: "my-gcp-project"

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resourcedetection, batch]
      exporters: [googlecloud]
EOF

# Systemd服务
cat > /etc/systemd/system/otel-collector.service <<EOF
[Unit]
Description=OpenTelemetry Collector
After=network.target

[Service]
Type=simple
ExecStart=/usr/local/bin/otelcol-contrib --config=/etc/otel-collector-config.yaml
Restart=on-failure

[Install]
WantedBy=multi-user.target
EOF

# 启动服务
sudo systemctl daemon-reload
sudo systemctl enable otel-collector
sudo systemctl start otel-collector
```

---

## 7. Cloud Monitoring集成

**Metrics Exporter配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
      http:

processors:
  batch:
  
  # 资源转换
  resource:
    attributes:
      - key: service.name
        action: insert
        value: my-service

exporters:
  googlecloud:
    project: "my-gcp-project"
    
    metric:
      endpoint: "monitoring.googleapis.com:443"
      
      # 指标前缀
      prefix: "custom.googleapis.com"
      
      # 资源映射
      resource_filters:
        - prefix: "k8s."
        - prefix: "cloud."
      
      # 使用Cloud Monitoring resource types
      use_insecure: false

service:
  pipelines:
    metrics:
      receivers: [otlp]
      processors: [batch, resource]
      exporters: [googlecloud]
```

---

## 8. GCP服务追踪

### 8.1 Firestore追踪

```go
import (
    "cloud.google.com/go/firestore"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
)

func createFirestoreClient(ctx context.Context) (*firestore.Client, error) {
    // 使用OTel instrumentation
    client, err := firestore.NewClient(ctx, "my-gcp-project",
        option.WithGRPCDialOption(
            grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
            grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
        ),
    )
    
    return client, err
}

func saveDocument(ctx context.Context, client *firestore.Client) error {
    // 自动追踪Firestore操作
    _, err := client.Collection("orders").Doc("order-123").Set(ctx, map[string]interface{}{
        "amount": 99.99,
        "status": "pending",
    })
    
    return err
}
```

### 8.2 Cloud Storage追踪

```go
import (
    "cloud.google.com/go/storage"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
)

func uploadFile(ctx context.Context) error {
    client, _ := storage.NewClient(ctx,
        option.WithGRPCDialOption(
            grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        ),
    )
    defer client.Close()
    
    // 自动追踪上传操作
    wc := client.Bucket("my-bucket").Object("file.txt").NewWriter(ctx)
    _, err := wc.Write([]byte("content"))
    wc.Close()
    
    return err
}
```

### 8.3 Pub/Sub追踪

```go
import (
    "cloud.google.com/go/pubsub"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

func publishMessage(ctx context.Context) error {
    client, _ := pubsub.NewClient(ctx, "my-gcp-project")
    defer client.Close()
    
    topic := client.Topic("orders")
    
    // 创建Span
    tracer := otel.Tracer("pubsub-publisher")
    ctx, span := tracer.Start(ctx, "Publish to orders")
    defer span.End()
    
    // 注入TraceContext到消息属性
    carrier := make(map[string]string)
    otel.GetTextMapPropagator().Inject(ctx, propagation.MapCarrier(carrier))
    
    // 发布消息
    result := topic.Publish(ctx, &pubsub.Message{
        Data: []byte("order data"),
        Attributes: carrier,
    })
    
    _, err := result.Get(ctx)
    return err
}

func consumeMessage(ctx context.Context) error {
    client, _ := pubsub.NewClient(ctx, "my-gcp-project")
    defer client.Close()
    
    sub := client.Subscription("orders-sub")
    
    return sub.Receive(ctx, func(ctx context.Context, msg *pubsub.Message) {
        // 提取TraceContext
        ctx = otel.GetTextMapPropagator().Extract(ctx, 
            propagation.MapCarrier(msg.Attributes))
        
        // 创建Consumer Span
        tracer := otel.Tracer("pubsub-consumer")
        ctx, span := tracer.Start(ctx, "Process orders message")
        defer span.End()
        
        // 处理消息
        processMessage(ctx, msg.Data)
        
        msg.Ack()
    })
}
```

---

## 9. Resource检测

**自动检测GCP资源**：

```yaml
processors:
  resourcedetection/gcp:
    detectors: [gcp, env]
    timeout: 2s
    override: false

# 自动检测的属性:
# GKE:
# - cloud.provider: gcp
# - cloud.platform: gcp_kubernetes_engine
# - k8s.cluster.name: my-cluster
# - k8s.namespace.name: production
# - k8s.pod.name: order-service-abc123
# - cloud.availability_zone: us-central1-a
# - cloud.region: us-central1

# Cloud Run:
# - cloud.provider: gcp
# - cloud.platform: gcp_cloud_run
# - service.name: order-service
# - service.instance.id: abc123
# - cloud.region: us-central1

# Compute Engine:
# - cloud.provider: gcp
# - cloud.platform: gcp_compute_engine
# - host.id: 123456789
# - host.name: instance-1
# - host.type: n1-standard-4
# - cloud.availability_zone: us-central1-a
```

---

## 10. 成本优化

```text
1. Cloud Trace定价
   - $0.20 / 百万span ingested
   - 前2.5百万 span/月免费
   
   优化策略:
   # 10%采样
   sampler: parentbased_traceidratio
   sampling_percentage: 10
   
   节省: 90% ($18/百万 vs $180/百万)

2. Cloud Monitoring定价
   - $0.2580 / MB for metrics
   - 前150 MB/月免费
   
   优化策略:
   # 减少指标基数
   processors:
     filter:
       metrics:
         exclude:
           match_type: strict
           metric_names:
             - high_cardinality_metric

3. 数据过滤
   processors:
     filter:
       spans:
         exclude:
           match_type: strict
           attributes:
             - key: http.target
               value: /health

4. 批处理优化
   processors:
     batch:
       send_batch_size: 256
       timeout: 10s

5. 智能路由
   # 高价值trace → Cloud Trace
   # 原始数据 → BigQuery (便宜)
   exporters:
     googlecloud:
       # 仅Error traces
     googlestorage:
       bucket: telemetry-archive
       # 所有traces (长期存储)

估算示例:
100M spans/月
- 100%采样: $20/月
- 10%采样: $2/月 + 免费额度 = $0/月
- 智能采样(20%): $4/月
```

---

## 11. 最佳实践

```text
✅ DO (推荐)
1. 使用Workload Identity (不用Service Account Key)
2. GKE使用DaemonSet + Deployment模式
3. Cloud Run使用Sidecar模式
4. 启用Resource检测器
5. 配置合理采样率 (10-20%)
6. 使用Cloud Trace for查询
7. 使用BigQuery for分析
8. 监控成本
9. 定期更新Collector
10. 使用Terraform管理基础设施

❌ DON'T (避免)
1. 不要100%采样生产环境
2. 不要使用Service Account Key文件
3. 不要忽略IAM权限配置
4. 不要跳过Resource检测
5. 不要硬编码project ID

架构建议:
开发环境: 本地Jaeger
生产环境: Cloud Trace + BigQuery归档

监控指标:
- google.cloud.trace.spans.ingested
- google.cloud.monitoring.timeseries.written
- collector.cpu_usage
- collector.memory_usage

安全建议:
- 使用Workload Identity
- 最小权限原则
- 启用VPC-SC
- 加密传输 (TLS)
- 审计日志
```

---

## 12. 参考资源

- **GCP OpenTelemetry**: <https://cloud.google.com/trace/docs/setup/opentelemetry>
- **Cloud Trace**: <https://cloud.google.com/trace/docs>
- **GCP Exporter**: <https://github.com/GoogleCloudPlatform/opentelemetry-operations-go>
- **GKE最佳实践**: <https://cloud.google.com/kubernetes-engine/docs/how-to/observability>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [AWS集成指南](01_AWS集成指南.md), [Collector架构](../04_核心组件/02_Collector架构.md)

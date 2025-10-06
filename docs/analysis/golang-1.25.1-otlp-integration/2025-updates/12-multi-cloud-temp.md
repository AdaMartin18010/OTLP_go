
## 1. 概述 (扩展)

多云和混合云部署为企业提供了更高的灵活性、可靠性和成本效益。通过在多个云平台部署 OpenTelemetry,可以实现跨云的统一可观测性。

### 1.1 多云部署优势

**高可用性**:
- 跨云容灾,消除单一云厂商依赖
- 多区域部署,提高服务可用性
- 自动故障转移,确保业务连续性
- 分布式架构,降低单点故障风险

**灵活性**:
- 选择最适合的云服务
- 避免厂商锁定
- 支持渐进式迁移
- 灵活的资源调度

**成本优化**:
- 利用不同云的价格优势
- 按需使用,避免资源浪费
- 智能采样,降低数据传输成本
- 分层存储,优化存储成本

**合规性**:
- 数据主权要求
- 地域合规性
- 行业监管要求
- 数据隐私保护

### 1.2 部署场景

**场景 1: 多云容灾**
```text
┌─────────────────┐        ┌─────────────────┐
│   AWS (主)      │◄──────►│  Azure (备)     │
│   ┌─────────┐   │        │   ┌─────────┐   │
│   │ Cluster │   │        │   │ Cluster │   │
│   └─────────┘   │        │   └─────────┘   │
└─────────────────┘        └─────────────────┘
         │                          │
         └──────────┬───────────────┘
                    ▼
         ┌─────────────────┐
         │  统一数据平台    │
         └─────────────────┘
```

**场景 2: 混合云迁移**
```text
┌─────────────────┐        ┌─────────────────┐
│  本地数据中心    │        │   云端 (目标)   │
│   ┌─────────┐   │        │   ┌─────────┐   │
│   │ Legacy  │───┼────────┼──►│  New    │   │
│   └─────────┘   │        │   └─────────┘   │
└─────────────────┘        └─────────────────┘
```

**场景 3: 跨区域部署**
```text
┌──────────┐  ┌──────────┐  ┌──────────┐
│ US-East  │  │ EU-West  │  │ AP-South │
│ Region   │  │ Region   │  │ Region   │
└────┬─────┘  └────┬─────┘  └────┬─────┘
     └─────────────┼──────────────┘
                   ▼
         ┌─────────────────┐
         │  Global Gateway │
         └─────────────────┘
```

---

## 3. AWS 部署 (扩展)

### 3.1 EKS 完整部署

**EKS 集群配置**:

```yaml
apiVersion: eksctl.io/v1alpha5
kind: ClusterConfig

metadata:
  name: otel-cluster
  region: us-east-1
  version: "1.28"

nodeGroups:
  - name: otel-workers
    instanceType: m5.xlarge
    desiredCapacity: 3
    minSize: 2
    maxSize: 10
    volumeSize: 100
    labels:
      role: otel-worker
    tags:
      k8s.io/cluster-autoscaler/enabled: "true"
      k8s.io/cluster-autoscaler/otel-cluster: "owned"
    iam:
      attachPolicyARNs:
        - arn:aws:iam::aws:policy/AmazonEKSWorkerNodePolicy
        - arn:aws:iam::aws:policy/AmazonEKS_CNI_Policy
        - arn:aws:iam::aws:policy/AmazonEC2ContainerRegistryReadOnly
        - arn:aws:iam::aws:policy/CloudWatchAgentServerPolicy
```

**OpenTelemetry Collector on EKS**:

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
      serviceAccountName: otel-collector
      containers:
      - name: otel-agent
        image: otel/opentelemetry-collector-contrib:0.90.0
        env:
        - name: AWS_REGION
          value: us-east-1
        - name: CLUSTER_NAME
          value: otel-cluster
        - name: K8S_NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
        volumeMounts:
        - name: otel-config
          mountPath: /etc/otel
        - name: aws-credentials
          mountPath: /root/.aws
          readOnly: true
        resources:
          requests:
            cpu: 200m
            memory: 256Mi
          limits:
            cpu: 500m
            memory: 512Mi
      volumes:
      - name: otel-config
        configMap:
          name: otel-agent-config
      - name: aws-credentials
        secret:
          secretName: aws-credentials
---
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability
  annotations:
    eks.amazonaws.com/role-arn: arn:aws:iam::123456789012:role/OTelCollectorRole
```

### 3.2 AWS 服务集成

**CloudWatch Logs 导出**:

```yaml
exporters:
  awscloudwatchlogs:
    log_group_name: /aws/otel/traces
    log_stream_name: otel-collector
    region: us-east-1
    
  awscloudwatch:
    namespace: OTLP/Metrics
    region: us-east-1
    metric_declarations:
      - dimensions: [[service.name, operation]]
        metric_name_selectors:
          - "^http\\..*"
          - "^rpc\\..*"
```

**X-Ray 集成**:

```yaml
exporters:
  awsxray:
    region: us-east-1
    index_all_attributes: true
    indexed_attributes:
      - http.method
      - http.status_code
      - error
```

**S3 归档**:

```yaml
exporters:
  awss3:
    region: us-east-1
    s3_bucket: otel-traces-archive
    s3_prefix: traces/
    s3_partition: hour
    compression: gzip
    marshaler: otlp_json
```

### 3.3 ECS/Fargate 部署

**ECS Task Definition**:

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
      "image": "otel/opentelemetry-collector-contrib:0.90.0",
      "portMappings": [
        {
          "containerPort": 4317,
          "protocol": "tcp"
        },
        {
          "containerPort": 4318,
          "protocol": "tcp"
        }
      ],
      "environment": [
        {
          "name": "AWS_REGION",
          "value": "us-east-1"
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
        "command": ["CMD-SHELL", "wget --spider -q http://localhost:13133 || exit 1"],
        "interval": 30,
        "timeout": 5,
        "retries": 3
      }
    }
  ]
}
```

### 3.4 Lambda 集成

**Lambda Layer**:

```go
package main

import (
    "context"
    "os"
    
    "github.com/aws/aws-lambda-go/lambda"
    "go.opentelemetry.io/contrib/instrumentation/github.com/aws/aws-lambda-go/otellambda"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

func main() {
    ctx := context.Background()
    
    // 初始化 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint(os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT")),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        panic(err)
    }
    
    // 创建追踪提供者
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceNameKey.String("lambda-function"),
        )),
    )
    otel.SetTracerProvider(tp)
    
    // 使用 otellambda 包装 Handler
    lambda.Start(otellambda.InstrumentHandler(handleRequest))
}

func handleRequest(ctx context.Context, event map[string]interface{}) (string, error) {
    tracer := otel.Tracer("lambda-handler")
    ctx, span := tracer.Start(ctx, "process-event")
    defer span.End()
    
    // 业务逻辑
    return "Success", nil
}
```

---

## 4. Azure 部署 (扩展)

### 4.1 AKS 完整部署

**AKS 集群创建**:

```bash
# 创建资源组
az group create --name otel-rg --location eastus

# 创建 AKS 集群
az aks create \
  --resource-group otel-rg \
  --name otel-cluster \
  --node-count 3 \
  --node-vm-size Standard_D4s_v3 \
  --enable-managed-identity \
  --enable-addons monitoring \
  --generate-ssh-keys

# 获取凭证
az aks get-credentials --resource-group otel-rg --name otel-cluster
```

**OpenTelemetry on AKS**:

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
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8888"
    spec:
      nodeSelector:
        kubernetes.io/os: linux
      containers:
      - name: otel-gateway
        image: otel/opentelemetry-collector-contrib:0.90.0
        env:
        - name: AZURE_REGION
          value: eastus
        - name: AZURE_SUBSCRIPTION_ID
          valueFrom:
            secretKeyRef:
              name: azure-credentials
              key: subscription-id
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        - containerPort: 8888
          name: metrics
        volumeMounts:
        - name: otel-config
          mountPath: /etc/otel
        resources:
          requests:
            cpu: 1000m
            memory: 2Gi
          limits:
            cpu: 2000m
            memory: 4Gi
      volumes:
      - name: otel-config
        configMap:
          name: otel-gateway-config
```

### 4.2 Azure Monitor 集成

**Application Insights 导出**:

```yaml
exporters:
  azuremonitor:
    instrumentation_key: ${APPLICATIONINSIGHTS_INSTRUMENTATION_KEY}
    endpoint: https://dc.services.visualstudio.com/v2/track
    maxbatchsize: 100
    maxbatchinterval: 10s
```

**Azure Log Analytics**:

```yaml
exporters:
  azureloganalytics:
    workspace_id: ${WORKSPACE_ID}
    workspace_key: ${WORKSPACE_KEY}
    log_type: OTelTraces
```

### 4.3 Container Instances 部署

**ARM Template**:

```json
{
  "$schema": "https://schema.management.azure.com/schemas/2019-04-01/deploymentTemplate.json#",
  "contentVersion": "1.0.0.0",
  "resources": [
    {
      "type": "Microsoft.ContainerInstance/containerGroups",
      "apiVersion": "2021-09-01",
      "name": "otel-collector",
      "location": "eastus",
      "properties": {
        "containers": [
          {
            "name": "otel-collector",
            "properties": {
              "image": "otel/opentelemetry-collector-contrib:0.90.0",
              "ports": [
                {
                  "port": 4317,
                  "protocol": "TCP"
                },
                {
                  "port": 4318,
                  "protocol": "TCP"
                }
              ],
              "environmentVariables": [
                {
                  "name": "AZURE_REGION",
                  "value": "eastus"
                }
              ],
              "resources": {
                "requests": {
                  "cpu": 2,
                  "memoryInGB": 4
                }
              }
            }
          }
        ],
        "osType": "Linux",
        "ipAddress": {
          "type": "Public",
          "ports": [
            {
              "port": 4317,
              "protocol": "TCP"
            },
            {
              "port": 4318,
              "protocol": "TCP"
            }
          ]
        }
      }
    }
  ]
}
```

---

**文档状态**: ✅ 持续填充中  
**最后更新**: 2025-10-06  
**维护者**: OTLP_go Team

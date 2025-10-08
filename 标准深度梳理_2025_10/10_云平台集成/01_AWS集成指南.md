# OpenTelemetry AWS 集成指南

> **最后更新**: 2025年10月8日  
> **目标读者**: AWS架构师、DevOps工程师

---

## 目录

- [OpenTelemetry AWS 集成指南](#opentelemetry-aws-集成指南)
  - [目录](#目录)
  - [1. AWS集成概述](#1-aws集成概述)
    - [1.1 为什么在AWS上使用OpenTelemetry](#11-为什么在aws上使用opentelemetry)
    - [1.2 AWS服务与OpenTelemetry](#12-aws服务与opentelemetry)
  - [2. AWS Distro for OpenTelemetry (ADOT)](#2-aws-distro-for-opentelemetry-adot)
    - [2.1 ADOT概述](#21-adot概述)
    - [2.2 ADOT Collector部署](#22-adot-collector部署)
  - [3. ECS集成](#3-ecs集成)
    - [3.1 ECS Fargate部署](#31-ecs-fargate部署)
    - [3.2 ECS EC2部署](#32-ecs-ec2部署)
  - [4. EKS集成](#4-eks集成)
    - [4.1 ADOT Operator](#41-adot-operator)
    - [4.2 完整部署示例](#42-完整部署示例)
  - [5. Lambda集成](#5-lambda集成)
    - [5.1 Lambda Layer](#51-lambda-layer)
    - [5.2 完整示例](#52-完整示例)
  - [6. AWS X-Ray集成](#6-aws-x-ray集成)
    - [6.1 X-Ray Exporter](#61-x-ray-exporter)
    - [6.2 混合追踪](#62-混合追踪)
  - [7. CloudWatch集成](#7-cloudwatch集成)
  - [8. AWS服务追踪](#8-aws服务追踪)
    - [8.1 DynamoDB追踪](#81-dynamodb追踪)
    - [8.2 S3追踪](#82-s3追踪)
    - [8.3 SQS追踪](#83-sqs追踪)
  - [9. Resource属性](#9-resource属性)
  - [10. 成本优化](#10-成本优化)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 参考资源](#12-参考资源)

---

## 1. AWS集成概述

### 1.1 为什么在AWS上使用OpenTelemetry

**价值**：

```text
1. 供应商中立
   - 不锁定AWS X-Ray
   - 可切换到其他后端
   - 多云策略

2. 统一可观测性
   - 统一SDK
   - 统一数据格式
   - 统一分析

3. 丰富生态
   - 多语言支持
   - 自动instrumentation
   - 社区贡献

4. 灵活路由
   - X-Ray + Jaeger
   - CloudWatch + Prometheus
   - 多后端并行

5. 成本控制
   - 采样控制
   - 数据过滤
   - 智能路由

架构示例:
应用 → ADOT Collector → X-Ray + Prometheus + S3
- Traces → X-Ray (实时查询)
- Metrics → CloudWatch (告警)
- Raw Data → S3 (长期存储)
```

### 1.2 AWS服务与OpenTelemetry

```text
支持的AWS服务:

计算:
- ECS (Fargate/EC2)
- EKS (Kubernetes)
- Lambda
- EC2
- App Runner

后端:
- X-Ray (Traces)
- CloudWatch (Metrics/Logs)
- Managed Prometheus
- Managed Grafana

集成:
- DynamoDB
- S3
- SQS
- SNS
- API Gateway
- Application Load Balancer
```

---

## 2. AWS Distro for OpenTelemetry (ADOT)

### 2.1 ADOT概述

**什么是ADOT**：

```text
ADOT = AWS优化的OpenTelemetry发行版

特点:
1. AWS优化
   - 预配置X-Ray exporter
   - CloudWatch exporter
   - AWS SDK instrumentation

2. 完全兼容
   - 基于上游OpenTelemetry
   - 遵循标准规范
   - 无供应商锁定

3. AWS支持
   - 官方维护
   - 安全补丁
   - 技术支持

4. 性能优化
   - 针对AWS优化
   - 低延迟
   - 高吞吐

组件:
- ADOT Collector
- ADOT SDKs (Java, Python, Go, .NET, JS)
- ADOT Lambda Layers
- ADOT Operator (EKS)
```

### 2.2 ADOT Collector部署

**ECS Fargate Sidecar**：

```json
{
  "family": "my-app-task",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "512",
  "memory": "1024",
  "containerDefinitions": [
    {
      "name": "app",
      "image": "my-app:latest",
      "environment": [
        {
          "name": "OTEL_EXPORTER_OTLP_ENDPOINT",
          "value": "http://localhost:4317"
        },
        {
          "name": "OTEL_SERVICE_NAME",
          "value": "my-app"
        },
        {
          "name": "OTEL_RESOURCE_ATTRIBUTES",
          "value": "deployment.environment=production"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/my-app",
          "awslogs-region": "us-west-2",
          "awslogs-stream-prefix": "ecs"
        }
      }
    },
    {
      "name": "aws-otel-collector",
      "image": "public.ecr.aws/aws-observability/aws-otel-collector:latest",
      "command": [
        "--config=/etc/ecs/ecs-xray.yaml"
      ],
      "environment": [
        {
          "name": "AWS_REGION",
          "value": "us-west-2"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/otel-collector",
          "awslogs-region": "us-west-2",
          "awslogs-stream-prefix": "collector"
        }
      }
    }
  ],
  "taskRoleArn": "arn:aws:iam::123456789012:role/ecsTaskRole",
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole"
}
```

**Collector配置 (X-Ray)**：

```yaml
# ecs-xray.yaml
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
    send_batch_size: 50
  
  memory_limiter:
    limit_mib: 100
    spike_limit_mib: 30

exporters:
  awsxray:
    region: us-west-2
    
  logging:
    loglevel: info

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch]
      exporters: [awsxray, logging]
```

---

## 3. ECS集成

### 3.1 ECS Fargate部署

**完整Task Definition**：

```json
{
  "family": "order-service",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "1024",
  "memory": "2048",
  "containerDefinitions": [
    {
      "name": "order-service",
      "image": "123456789012.dkr.ecr.us-west-2.amazonaws.com/order-service:v1.2.3",
      "cpu": 768,
      "memory": 1536,
      "essential": true,
      "portMappings": [
        {
          "containerPort": 8080,
          "protocol": "tcp"
        }
      ],
      "environment": [
        {
          "name": "OTEL_EXPORTER_OTLP_ENDPOINT",
          "value": "http://localhost:4317"
        },
        {
          "name": "OTEL_SERVICE_NAME",
          "value": "order-service"
        },
        {
          "name": "OTEL_RESOURCE_ATTRIBUTES",
          "value": "service.version=1.2.3,deployment.environment=production,aws.ecs.cluster.name=production-cluster,aws.ecs.task.family=order-service"
        },
        {
          "name": "AWS_REGION",
          "value": "us-west-2"
        }
      ],
      "dependsOn": [
        {
          "containerName": "aws-otel-collector",
          "condition": "START"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-create-group": "true",
          "awslogs-group": "/ecs/order-service",
          "awslogs-region": "us-west-2",
          "awslogs-stream-prefix": "app"
        }
      }
    },
    {
      "name": "aws-otel-collector",
      "image": "public.ecr.aws/aws-observability/aws-otel-collector:v0.35.0",
      "cpu": 256,
      "memory": 512,
      "essential": true,
      "command": [
        "--config=/etc/ecs/otel-config.yaml"
      ],
      "environment": [
        {
          "name": "AWS_REGION",
          "value": "us-west-2"
        }
      ],
      "secrets": [
        {
          "name": "AOT_CONFIG_CONTENT",
          "valueFrom": "arn:aws:ssm:us-west-2:123456789012:parameter/otel-collector-config"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-create-group": "true",
          "awslogs-group": "/ecs/otel-collector",
          "awslogs-region": "us-west-2",
          "awslogs-stream-prefix": "collector"
        }
      }
    }
  ],
  "taskRoleArn": "arn:aws:iam::123456789012:role/ecsTaskRole",
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole"
}
```

**IAM策略**：

```json
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Effect": "Allow",
      "Action": [
        "xray:PutTraceSegments",
        "xray:PutTelemetryRecords"
      ],
      "Resource": "*"
    },
    {
      "Effect": "Allow",
      "Action": [
        "cloudwatch:PutMetricData"
      ],
      "Resource": "*"
    },
    {
      "Effect": "Allow",
      "Action": [
        "logs:CreateLogGroup",
        "logs:CreateLogStream",
        "logs:PutLogEvents"
      ],
      "Resource": "arn:aws:logs:*:*:*"
    }
  ]
}
```

### 3.2 ECS EC2部署

**DaemonSet模式**：

```json
{
  "family": "aws-otel-collector",
  "networkMode": "bridge",
  "containerDefinitions": [
    {
      "name": "aws-otel-collector",
      "image": "public.ecr.aws/aws-observability/aws-otel-collector:latest",
      "cpu": 512,
      "memory": 1024,
      "essential": true,
      "portMappings": [
        {
          "containerPort": 4317,
          "hostPort": 4317,
          "protocol": "tcp"
        },
        {
          "containerPort": 4318,
          "hostPort": 4318,
          "protocol": "tcp"
        }
      ],
      "command": [
        "--config=/etc/ecs/otel-instance-metrics-config.yaml"
      ]
    }
  ]
}
```

---

## 4. EKS集成

### 4.1 ADOT Operator

**安装Operator**：

```bash
# 添加Helm repo
helm repo add aws-observability https://aws-observability.github.io/aws-otel-helm-charts

# 安装ADOT Operator
helm install adot-operator \
  aws-observability/adot-exporter-for-eks-on-ec2 \
  --namespace opentelemetry-operator-system \
  --create-namespace

# 验证安装
kubectl get pods -n opentelemetry-operator-system
```

### 4.2 完整部署示例

**OpenTelemetryCollector CR**：

```yaml
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: adot-collector
  namespace: observability
spec:
  mode: deployment
  replicas: 3
  
  image: public.ecr.aws/aws-observability/aws-otel-collector:v0.35.0
  
  serviceAccount: adot-collector
  
  resources:
    requests:
      cpu: 200m
      memory: 256Mi
    limits:
      cpu: 1000m
      memory: 1Gi
  
  config: |
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
        limit_mib: 768
        spike_limit_mib: 256
      
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
            - tag_name: app.label
              key: app
              from: pod
    
    exporters:
      awsxray:
        region: us-west-2
      
      awsemf:
        region: us-west-2
        namespace: EKS/Observability
        log_group_name: /aws/eks/observability
      
      logging:
        loglevel: info
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, batch]
          exporters: [awsxray, logging]
        
        metrics:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, batch]
          exporters: [awsemf, logging]

---
apiVersion: v1
kind: ServiceAccount
metadata:
  name: adot-collector
  namespace: observability
  annotations:
    eks.amazonaws.com/role-arn: arn:aws:iam::123456789012:role/ADOTCollectorRole

---
apiVersion: v1
kind: Service
metadata:
  name: adot-collector
  namespace: observability
spec:
  selector:
    app.kubernetes.io/name: adot-collector
  ports:
  - name: grpc
    port: 4317
    targetPort: 4317
  - name: http
    port: 4318
    targetPort: 4318
```

**应用部署**：

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
  namespace: production
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-service
  template:
    metadata:
      labels:
        app: order-service
    spec:
      serviceAccountName: order-service
      containers:
      - name: order-service
        image: 123456789012.dkr.ecr.us-west-2.amazonaws.com/order-service:v1.2.3
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://adot-collector.observability.svc.cluster.local:4317"
        - name: OTEL_SERVICE_NAME
          value: "order-service"
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "service.version=1.2.3,deployment.environment=production"
        - name: AWS_REGION
          value: "us-west-2"
        # Kubernetes Downward API
        - name: K8S_POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: K8S_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        - name: K8S_NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
```

---

## 5. Lambda集成

### 5.1 Lambda Layer

**使用ADOT Lambda Layer**：

```python
# lambda_function.py
import json
import os
from aws_lambda_powertools import Tracer
from aws_xray_sdk.core import xray_recorder

tracer = Tracer()

@tracer.capture_lambda_handler
def lambda_handler(event, context):
    # 自动追踪
    order_id = event.get('order_id')
    
    # 自定义Span
    with tracer.provider.tracer.start_as_current_span("process_order") as span:
        span.set_attribute("order.id", order_id)
        
        # 业务逻辑
        result = process_order(order_id)
        
        span.set_attribute("order.status", result['status'])
    
    return {
        'statusCode': 200,
        'body': json.dumps(result)
    }

@tracer.capture_method
def process_order(order_id):
    # 处理订单
    return {'order_id': order_id, 'status': 'processed'}
```

**Terraform配置**：

```hcl
resource "aws_lambda_function" "order_processor" {
  function_name = "order-processor"
  runtime       = "python3.11"
  handler       = "lambda_function.lambda_handler"
  role          = aws_iam_role.lambda_role.arn
  
  filename         = "function.zip"
  source_code_hash = filebase64sha256("function.zip")
  
  # ADOT Lambda Layer
  layers = [
    "arn:aws:lambda:us-west-2:901920570463:layer:aws-otel-python-amd64-ver-1-20-0:2"
  ]
  
  environment {
    variables = {
      AWS_LAMBDA_EXEC_WRAPPER = "/opt/otel-instrument"
      OTEL_SERVICE_NAME       = "order-processor"
      OTEL_PROPAGATORS        = "xray"
      OTEL_PYTHON_DISTRO      = "aws_distro"
      OTEL_PYTHON_CONFIGURATOR = "aws_configurator"
    }
  }
  
  tracing_config {
    mode = "Active"
  }
}

resource "aws_iam_role" "lambda_role" {
  name = "order-processor-role"
  
  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [{
      Action = "sts:AssumeRole"
      Effect = "Allow"
      Principal = {
        Service = "lambda.amazonaws.com"
      }
    }]
  })
}

resource "aws_iam_role_policy_attachment" "lambda_xray" {
  role       = aws_iam_role.lambda_role.name
  policy_arn = "arn:aws:iam::aws:policy/AWSXRayDaemonWriteAccess"
}
```

### 5.2 完整示例

**Go Lambda with ADOT**：

```go
package main

import (
    "context"
    "github.com/aws/aws-lambda-go/lambda"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

type OrderEvent struct {
    OrderID string `json:"order_id"`
    Amount  float64 `json:"amount"`
}

func HandleRequest(ctx context.Context, event OrderEvent) (string, error) {
    tracer := otel.Tracer("order-processor")
    
    ctx, span := tracer.Start(ctx, "process_order")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", event.OrderID),
        attribute.Float64("order.amount", event.Amount),
    )
    
    // 处理订单
    // ...
    
    return "Order processed", nil
}

func main() {
    lambda.Start(HandleRequest)
}
```

---

## 6. AWS X-Ray集成

### 6.1 X-Ray Exporter

**Collector配置**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
      http:

processors:
  batch:

exporters:
  awsxray:
    region: us-west-2
    # 索引所有属性
    index_all_attributes: true
    # 索引的特定属性
    indexed_attributes:
      - http.status_code
      - error
      - aws.operation

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [awsxray]
```

### 6.2 混合追踪

**同时发送到X-Ray和Jaeger**：

```yaml
exporters:
  awsxray:
    region: us-west-2
  
  otlp/jaeger:
    endpoint: jaeger:4317
    tls:
      insecure: true

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [awsxray, otlp/jaeger]  # 多后端
```

---

## 7. CloudWatch集成

**EMF (Embedded Metric Format) Exporter**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:

processors:
  batch:

exporters:
  awsemf:
    region: us-west-2
    namespace: MyApp/Metrics
    log_group_name: /aws/metrics/myapp
    log_stream_name: my-app-stream
    resource_to_telemetry_conversion:
      enabled: true
    dimension_rollup_option: "NoDimensionRollup"
    metric_declarations:
      - dimensions: [[service.name, deployment.environment]]
        metric_name_selectors:
          - "^http\\..*"
          - "^db\\..*"

service:
  pipelines:
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [awsemf]
```

---

## 8. AWS服务追踪

### 8.1 DynamoDB追踪

```go
import (
    "github.com/aws/aws-sdk-go-v2/config"
    "github.com/aws/aws-sdk-go-v2/service/dynamodb"
    "go.opentelemetry.io/contrib/instrumentation/github.com/aws/aws-sdk-go-v2/otelaws"
)

func main() {
    // 加载配置
    cfg, _ := config.LoadDefaultConfig(context.Background())
    
    // 添加OpenTelemetry instrumentation
    otelaws.AppendMiddlewares(&cfg.APIOptions)
    
    // 创建DynamoDB客户端
    client := dynamodb.NewFromConfig(cfg)
    
    // 所有DynamoDB调用自动追踪
    _, err := client.GetItem(ctx, &dynamodb.GetItemInput{
        TableName: aws.String("Orders"),
        Key: map[string]types.AttributeValue{
            "OrderID": &types.AttributeValueMemberS{Value: "order-123"},
        },
    })
}
```

### 8.2 S3追踪

```go
import (
    "github.com/aws/aws-sdk-go-v2/service/s3"
    "go.opentelemetry.io/contrib/instrumentation/github.com/aws/aws-sdk-go-v2/otelaws"
)

func uploadFile(ctx context.Context) error {
    cfg, _ := config.LoadDefaultConfig(ctx)
    otelaws.AppendMiddlewares(&cfg.APIOptions)
    
    client := s3.NewFromConfig(cfg)
    
    // S3 PutObject自动追踪
    _, err := client.PutObject(ctx, &s3.PutObjectInput{
        Bucket: aws.String("my-bucket"),
        Key:    aws.String("file.txt"),
        Body:   bytes.NewReader([]byte("content")),
    })
    
    return err
}
```

### 8.3 SQS追踪

```go
import (
    "github.com/aws/aws-sdk-go-v2/service/sqs"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

func sendMessage(ctx context.Context) error {
    cfg, _ := config.LoadDefaultConfig(ctx)
    otelaws.AppendMiddlewares(&cfg.APIOptions)
    
    client := sqs.NewFromConfig(cfg)
    
    // 注入TraceContext到消息属性
    carrier := make(map[string]string)
    otel.GetTextMapPropagator().Inject(ctx, propagation.MapCarrier(carrier))
    
    messageAttributes := make(map[string]types.MessageAttributeValue)
    for k, v := range carrier {
        messageAttributes[k] = types.MessageAttributeValue{
            DataType:    aws.String("String"),
            StringValue: aws.String(v),
        }
    }
    
    _, err := client.SendMessage(ctx, &sqs.SendMessageInput{
        QueueUrl:          aws.String("https://sqs.us-west-2.amazonaws.com/123456789012/my-queue"),
        MessageBody:       aws.String("message body"),
        MessageAttributes: messageAttributes,
    })
    
    return err
}
```

---

## 9. Resource属性

**AWS特定Resource属性**：

```yaml
# 自动检测
processors:
  resourcedetection:
    detectors: [env, ec2, ecs, eks]
    timeout: 5s

# 生成的属性:
# ECS:
# - cloud.provider: aws
# - cloud.platform: aws_ecs
# - aws.ecs.cluster.arn
# - aws.ecs.task.arn
# - aws.ecs.task.family
# - aws.ecs.task.revision
# - aws.ecs.launchtype: FARGATE/EC2

# EKS:
# - cloud.provider: aws
# - cloud.platform: aws_eks
# - k8s.cluster.name
# - k8s.namespace.name
# - k8s.pod.name

# EC2:
# - cloud.provider: aws
# - cloud.platform: aws_ec2
# - host.id: i-1234567890abcdef0
# - host.type: t3.large
# - cloud.availability_zone: us-west-2a
```

---

## 10. 成本优化

```text
1. 采样策略
   # X-Ray收费: $5/百万traces
   # 使用10%采样
   sampler: parentbased_traceidratio
   sampling_percentage: 10

2. 数据过滤
   # 过滤健康检查
   processors:
     filter:
       spans:
         exclude:
           match_type: strict
           attributes:
             - key: http.target
               value: /health

3. 批处理优化
   processors:
     batch:
       send_batch_size: 8192
       timeout: 10s

4. CloudWatch成本
   # EMF日志: $0.50/GB
   # 减少维度数量
   dimension_rollup_option: "ZeroAndSingleDimensionRollup"

5. 数据保留
   # X-Ray: 30天免费
   # S3长期存储: $0.023/GB/月
   
   exporters:
     awss3:
       region: us-west-2
       s3_bucket: telemetry-archive
       s3_partition: year=%Y/month=%m/day=%d

6. Collector资源
   # Fargate: 按vCPU和内存计费
   # 优化Collector资源
   resources:
     limits:
       cpu: 500m
       memory: 512Mi
```

---

## 11. 最佳实践

```text
✅ DO (推荐)
1. 使用ADOT而非上游OpenTelemetry
2. ECS使用Sidecar模式
3. EKS使用Daemonset或Deployment
4. Lambda使用官方Layer
5. 启用Resource检测器
6. 使用IAM角色而非access key
7. 配置合理的采样率
8. 监控Collector性能
9. 使用CloudWatch告警
10. 定期更新ADOT版本

❌ DON'T (避免)
1. 不要在Lambda中运行Collector
2. 不要100%采样生产环境
3. 不要忽略成本监控
4. 不要硬编码credentials
5. 不要跳过IAM策略配置

架构建议:
开发环境: 简单配置 + 本地Jaeger
生产环境: ADOT Collector + X-Ray + CloudWatch + S3归档

监控指标:
- aws.xray.segments.sent
- aws.xray.segments.rejected
- collector.cpu_usage
- collector.memory_usage
```

---

## 12. 参考资源

- **ADOT文档**: <https://aws-otel.github.io/>
- **ADOT Collector**: <https://github.com/aws-observability/aws-otel-collector>
- **AWS X-Ray**: <https://docs.aws.amazon.com/xray/>
- **EKS最佳实践**: <https://aws.github.io/aws-eks-best-practices/observability/>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [Collector架构](../04_核心组件/02_Collector架构.md), [Resource模型](../03_数据模型/04_Resource/01_Resource模型.md)

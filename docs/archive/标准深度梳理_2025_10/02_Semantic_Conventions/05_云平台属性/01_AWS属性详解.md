# AWS云平台属性详解

> **规范版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [AWS云平台属性详解](#aws云平台属性详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 通用AWS属性](#2-通用aws属性)
  - [3. EC2属性](#3-ec2属性)
  - [4. ECS属性](#4-ecs属性)
  - [5. EKS属性](#5-eks属性)
  - [6. Lambda属性](#6-lambda属性)
  - [7. Elastic Beanstalk属性](#7-elastic-beanstalk属性)
  - [8. 自动检测实现](#8-自动检测实现)
  - [9. 实战示例](#9-实战示例)
  - [10. 最佳实践](#10-最佳实践)
  - [11. 参考资源](#11-参考资源)

---

## 1. 概述

```text
AWS平台属性用途:
1. 识别AWS服务
   - EC2, ECS, EKS, Lambda等
   
2. 资源定位
   - 账户、区域、可用区
   
3. 成本归因
   - 按服务/环境分配

4. 故障定位
   - 快速定位资源

5. 合规审计
   - 追踪资源使用

必需属性:
- cloud.provider = "aws"
- cloud.platform = "aws_ec2" | "aws_ecs" | "aws_eks" | "aws_lambda"
- cloud.account.id
- cloud.region
```

---

## 2. 通用AWS属性

```text
基础属性:
┌────────────────────────┬─────────┬────────────────────┐
│ 属性名                  │ 类型    │ 示例               │
├────────────────────────┼─────────┼────────────────────┤
│ cloud.provider         │ string  │ "aws"              │
│ cloud.platform         │ string  │ "aws_ec2"          │
│ cloud.account.id       │ string  │ "123456789012"     │
│ cloud.region           │ string  │ "us-west-2"        │
│ cloud.availability_zone│ string  │ "us-west-2a"       │
└────────────────────────┴─────────┴────────────────────┘

cloud.platform标准值:
- "aws_ec2" (Elastic Compute Cloud)
- "aws_ecs" (Elastic Container Service)
- "aws_eks" (Elastic Kubernetes Service)
- "aws_lambda" (Lambda Functions)
- "aws_elastic_beanstalk"
- "aws_app_runner"

示例:
{
  "cloud.provider": "aws",
  "cloud.platform": "aws_ec2",
  "cloud.account.id": "123456789012",
  "cloud.region": "us-west-2",
  "cloud.availability_zone": "us-west-2a"
}
```

**从实例元数据获取**:

```go
import (
    "encoding/json"
    "io"
    "net/http"
)

const metadataEndpoint = "http://169.254.169.254/latest/meta-data/"

// 获取实例元数据
func getInstanceMetadata(path string) (string, error) {
    resp, err := http.Get(metadataEndpoint + path)
    if err != nil {
        return "", err
    }
    defer resp.Body.Close()
    
    data, err := io.ReadAll(resp.Body)
    if err != nil {
        return "", err
    }
    
    return string(data), nil
}

// 获取基础AWS属性
func getAWSAttributes() map[string]string {
    attrs := make(map[string]string)
    
    // 账户ID (从IMDSv2)
    token, _ := getIMDSv2Token()
    accountID, _ := getInstanceIdentity(token)
    attrs["cloud.account.id"] = accountID
    
    // 区域
    if region, err := getInstanceMetadata("placement/region"); err == nil {
        attrs["cloud.region"] = region
    }
    
    // 可用区
    if az, err := getInstanceMetadata("placement/availability-zone"); err == nil {
        attrs["cloud.availability_zone"] = az
    }
    
    attrs["cloud.provider"] = "aws"
    
    return attrs
}

// IMDSv2 Token
func getIMDSv2Token() (string, error) {
    client := &http.Client{}
    req, _ := http.NewRequest("PUT", 
        "http://169.254.169.254/latest/api/token", nil)
    req.Header.Set("X-aws-ec2-metadata-token-ttl-seconds", "21600")
    
    resp, err := client.Do(req)
    if err != nil {
        return "", err
    }
    defer resp.Body.Close()
    
    token, err := io.ReadAll(resp.Body)
    return string(token), err
}

// 获取实例身份文档
func getInstanceIdentity(token string) (string, error) {
    client := &http.Client{}
    req, _ := http.NewRequest("GET",
        "http://169.254.169.254/latest/dynamic/instance-identity/document", nil)
    req.Header.Set("X-aws-ec2-metadata-token", token)
    
    resp, err := client.Do(req)
    if err != nil {
        return "", err
    }
    defer resp.Body.Close()
    
    var doc struct {
        AccountID string `json:"accountId"`
    }
    
    if err := json.NewDecoder(resp.Body).Decode(&doc); err != nil {
        return "", err
    }
    
    return doc.AccountID, nil
}
```

---

## 3. EC2属性

```text
EC2特定属性:
┌────────────────────────┬─────────┬────────────────────────┐
│ 属性名                  │ 类型    │ 示例                   │
├────────────────────────┼─────────┼────────────────────────┤
│ host.id                │ string  │ "i-1234567890abcdef0"  │
│ host.type              │ string  │ "t3.large"             │
│ host.image.id          │ string  │ "ami-0c55b159cbfafe1f0"│
│ host.name              │ string  │ "ip-10-0-1-42"         │
└────────────────────────┴─────────┴────────────────────────┘

完整示例:
{
  "cloud.provider": "aws",
  "cloud.platform": "aws_ec2",
  "cloud.account.id": "123456789012",
  "cloud.region": "us-west-2",
  "cloud.availability_zone": "us-west-2a",
  "host.id": "i-1234567890abcdef0",
  "host.type": "t3.large",
  "host.image.id": "ami-0c55b159cbfafe1f0",
  "host.name": "ip-10-0-1-42.ec2.internal"
}

获取实例信息:
func getEC2Attributes() map[string]string {
    attrs := getAWSAttributes()
    attrs["cloud.platform"] = "aws_ec2"
    
    // 实例ID
    if instanceID, err := getInstanceMetadata("instance-id"); err == nil {
        attrs["host.id"] = instanceID
    }
    
    // 实例类型
    if instanceType, err := getInstanceMetadata("instance-type"); err == nil {
        attrs["host.type"] = instanceType
    }
    
    // AMI ID
    if amiID, err := getInstanceMetadata("ami-id"); err == nil {
        attrs["host.image.id"] = amiID
    }
    
    // 主机名
    if hostname, err := getInstanceMetadata("hostname"); err == nil {
        attrs["host.name"] = hostname
    }
    
    return attrs
}
```

---

## 4. ECS属性

```text
ECS特定属性:
┌────────────────────────────┬─────────┬─────────────────────────────┐
│ 属性名                      │ 类型    │ 示例                        │
├────────────────────────────┼─────────┼─────────────────────────────┤
│ aws.ecs.cluster.arn        │ string  │ "arn:aws:ecs:us-west-2:..." │
│ aws.ecs.task.arn           │ string  │ "arn:aws:ecs:us-west-2:..." │
│ aws.ecs.task.family        │ string  │ "my-service"                │
│ aws.ecs.task.revision      │ string  │ "5"                         │
│ aws.ecs.container.arn      │ string  │ "arn:aws:ecs:us-west-2:..." │
│ aws.ecs.launchtype         │ string  │ "FARGATE"                   │
└────────────────────────────┴─────────┴─────────────────────────────┘

aws.ecs.launchtype标准值:
- "EC2"
- "FARGATE"
- "EXTERNAL"

完整示例:
{
  "cloud.provider": "aws",
  "cloud.platform": "aws_ecs",
  "cloud.account.id": "123456789012",
  "cloud.region": "us-west-2",
  "aws.ecs.cluster.arn": "arn:aws:ecs:us-west-2:123456789012:cluster/prod",
  "aws.ecs.task.arn": "arn:aws:ecs:us-west-2:123456789012:task/abc123",
  "aws.ecs.task.family": "my-service",
  "aws.ecs.task.revision": "5",
  "aws.ecs.container.arn": "arn:aws:ecs:us-west-2:123456789012:container/xyz789",
  "aws.ecs.launchtype": "FARGATE",
  "container.id": "1234567890abcdef",
  "container.name": "my-service-container"
}

从环境变量获取:
func getECSAttributes() map[string]string {
    attrs := getAWSAttributes()
    attrs["cloud.platform"] = "aws_ecs"
    
    // ECS元数据
    if taskARN := os.Getenv("ECS_CONTAINER_METADATA_URI_V4"); taskARN != "" {
        metadata := getECSMetadata(taskARN)
        
        attrs["aws.ecs.task.arn"] = metadata.TaskARN
        attrs["aws.ecs.task.family"] = metadata.Family
        attrs["aws.ecs.task.revision"] = metadata.Revision
        attrs["aws.ecs.cluster.arn"] = metadata.ClusterARN
        attrs["aws.ecs.container.arn"] = metadata.ContainerARN
        attrs["aws.ecs.launchtype"] = metadata.LaunchType
        
        attrs["container.id"] = metadata.ContainerID
        attrs["container.name"] = metadata.ContainerName
    }
    
    return attrs
}

type ECSMetadata struct {
    TaskARN      string `json:"TaskARN"`
    Family       string `json:"Family"`
    Revision     string `json:"Revision"`
    ClusterARN   string `json:"Cluster"`
    ContainerARN string `json:"ContainerARN"`
    LaunchType   string `json:"LaunchType"`
    ContainerID  string `json:"DockerId"`
    ContainerName string `json:"ContainerName"`
}

func getECSMetadata(uri string) ECSMetadata {
    resp, _ := http.Get(uri + "/task")
    defer resp.Body.Close()
    
    var metadata ECSMetadata
    json.NewDecoder(resp.Body).Decode(&metadata)
    
    return metadata
}
```

---

## 5. EKS属性

```text
EKS = K8s + AWS

EKS继承所有K8s属性 + AWS属性:

Kubernetes属性:
- k8s.cluster.name
- k8s.namespace.name
- k8s.pod.name
- k8s.pod.uid
- k8s.deployment.name
- k8s.node.name
- k8s.container.name

AWS属性:
- cloud.provider = "aws"
- cloud.platform = "aws_eks"
- cloud.account.id
- cloud.region

完整示例:
{
  "cloud.provider": "aws",
  "cloud.platform": "aws_eks",
  "cloud.account.id": "123456789012",
  "cloud.region": "us-west-2",
  "k8s.cluster.name": "prod-eks-cluster",
  "k8s.namespace.name": "default",
  "k8s.pod.name": "my-service-7d5f9c8b6-xhq2w",
  "k8s.pod.uid": "12345678-1234-1234-1234-123456789abc",
  "k8s.deployment.name": "my-service",
  "k8s.node.name": "ip-10-0-1-42.us-west-2.compute.internal",
  "k8s.container.name": "app"
}

获取EKS属性:
func getEKSAttributes() map[string]string {
    attrs := make(map[string]string)
    
    // AWS属性
    attrs["cloud.provider"] = "aws"
    attrs["cloud.platform"] = "aws_eks"
    attrs["cloud.account.id"] = os.Getenv("AWS_ACCOUNT_ID")
    attrs["cloud.region"] = os.Getenv("AWS_REGION")
    
    // K8s属性 (从环境变量)
    attrs["k8s.cluster.name"] = os.Getenv("CLUSTER_NAME")
    attrs["k8s.namespace.name"] = os.Getenv("POD_NAMESPACE")
    attrs["k8s.pod.name"] = os.Getenv("POD_NAME")
    attrs["k8s.pod.uid"] = os.Getenv("POD_UID")
    attrs["k8s.node.name"] = os.Getenv("NODE_NAME")
    attrs["k8s.container.name"] = os.Getenv("CONTAINER_NAME")
    
    return attrs
}

Kubernetes Deployment配置:
apiVersion: apps/v1
kind: Deployment
spec:
  template:
    spec:
      containers:
      - name: app
        env:
        # AWS
        - name: AWS_REGION
          value: "us-west-2"
        # K8s
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: POD_NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        - name: POD_UID
          valueFrom:
            fieldRef:
              fieldPath: metadata.uid
        - name: NODE_NAME
          valueFrom:
            fieldRef:
              fieldPath: spec.nodeName
```

---

## 6. Lambda属性

```text
Lambda特定属性:
┌────────────────────────┬─────────┬────────────────────────┐
│ 属性名                  │ 类型    │ 示例                   │
├────────────────────────┼─────────┼────────────────────────┤
│ faas.name              │ string  │ "my-function"          │
│ faas.version           │ string  │ "$LATEST"              │
│ faas.instance          │ string  │ "2021/01/01/[$LATEST]" │
│ faas.max_memory        │ int     │ 512                    │
│ faas.trigger           │ string  │ "http"                 │
│ aws.lambda.invoked_arn │ string  │ "arn:aws:lambda:..."   │
└────────────────────────┴─────────┴────────────────────────┘

faas.trigger标准值:
- "http" (API Gateway/ALB)
- "pubsub" (SNS/SQS)
- "timer" (EventBridge)
- "datasource" (DynamoDB/S3)
- "other"

完整示例:
{
  "cloud.provider": "aws",
  "cloud.platform": "aws_lambda",
  "cloud.account.id": "123456789012",
  "cloud.region": "us-west-2",
  "faas.name": "my-function",
  "faas.version": "$LATEST",
  "faas.instance": "2021/01/01/[$LATEST]abc123def456",
  "faas.max_memory": 512,
  "faas.trigger": "http",
  "aws.lambda.invoked_arn": "arn:aws:lambda:us-west-2:123456789012:function:my-function"
}

从环境变量获取:
func getLambdaAttributes() map[string]string {
    attrs := make(map[string]string)
    
    attrs["cloud.provider"] = "aws"
    attrs["cloud.platform"] = "aws_lambda"
    attrs["cloud.region"] = os.Getenv("AWS_REGION")
    
    // Lambda特定
    attrs["faas.name"] = os.Getenv("AWS_LAMBDA_FUNCTION_NAME")
    attrs["faas.version"] = os.Getenv("AWS_LAMBDA_FUNCTION_VERSION")
    attrs["faas.max_memory"] = os.Getenv("AWS_LAMBDA_FUNCTION_MEMORY_SIZE")
    
    // 从Context获取
    if lambdaCtx, ok := lambdacontext.FromContext(ctx); ok {
        attrs["faas.instance"] = lambdaCtx.LogStreamName
        attrs["aws.lambda.invoked_arn"] = lambdaCtx.InvokedFunctionArn
    }
    
    return attrs
}

Lambda Handler示例:
func handler(ctx context.Context, event events.APIGatewayProxyRequest) error {
    // 初始化OpenTelemetry with Lambda attributes
    res, _ := resource.New(ctx,
        resource.WithAttributes(getLambdaResourceAttributes()...),
    )
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithResource(res),
        sdktrace.WithBatcher(exporter),
    )
    otel.SetTracerProvider(tp)
    
    // Handler逻辑
    tracer := otel.Tracer("lambda")
    ctx, span := tracer.Start(ctx, "handler")
    defer span.End()
    
    // 记录触发类型
    span.SetAttributes(
        attribute.String("faas.trigger", "http"),
        attribute.String("http.method", event.HTTPMethod),
        attribute.String("http.route", event.Path),
    )
    
    // 业务逻辑
    return nil
}
```

---

## 7. Elastic Beanstalk属性

```text
Elastic Beanstalk特定属性:
┌────────────────────────────────┬─────────┬─────────────────┐
│ 属性名                          │ 类型    │ 示例            │
├────────────────────────────────┼─────────┼─────────────────┤
│ service.instance.id            │ string  │ "i-123456..."   │
│ aws.elasticbeanstalk.env.name  │ string  │ "prod-env"      │
│ aws.elasticbeanstalk.deployment│ int     │ 5               │
└────────────────────────────────┴─────────┴─────────────────┘

从文件系统获取:
func getElasticBeanstalkAttributes() map[string]string {
    attrs := getEC2Attributes()
    attrs["cloud.platform"] = "aws_elastic_beanstalk"
    
    // 从配置文件读取
    if envName, err := readEBConfig("/opt/elasticbeanstalk/deployment/env"); err == nil {
        attrs["aws.elasticbeanstalk.env.name"] = envName
    }
    
    if deployment, err := readEBConfig("/opt/elasticbeanstalk/deployment/version"); err == nil {
        attrs["aws.elasticbeanstalk.deployment"] = deployment
    }
    
    return attrs
}
```

---

## 8. 自动检测实现

**完整AWS检测器**:

```go
package awsdetector

import (
    "context"
    "os"
    
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

type AWSDetector struct{}

func (d *AWSDetector) Detect(ctx context.Context) (*resource.Resource, error) {
    // 检测AWS环境
    if !isAWS() {
        return resource.Empty(), nil
    }
    
    var attrs []attribute.KeyValue
    
    // 基础AWS属性
    attrs = append(attrs,
        semconv.CloudProviderAWS,
        semconv.CloudAccountIDKey.String(getAccountID()),
        semconv.CloudRegionKey.String(getRegion()),
        semconv.CloudAvailabilityZoneKey.String(getAvailabilityZone()),
    )
    
    // 检测平台
    switch {
    case isLambda():
        attrs = append(attrs, getLambdaAttributes()...)
    case isECS():
        attrs = append(attrs, getECSAttributes()...)
    case isEKS():
        attrs = append(attrs, getEKSAttributes()...)
    case isElasticBeanstalk():
        attrs = append(attrs, getElasticBeanstalkAttributes()...)
    case isEC2():
        attrs = append(attrs, getEC2Attributes()...)
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}

func isAWS() bool {
    // 检查环境变量
    if os.Getenv("AWS_REGION") != "" {
        return true
    }
    
    // 尝试访问实例元数据
    resp, err := http.Get("http://169.254.169.254/latest/meta-data/")
    if err != nil {
        return false
    }
    defer resp.Body.Close()
    
    return resp.StatusCode == 200
}

func isLambda() bool {
    return os.Getenv("AWS_LAMBDA_FUNCTION_NAME") != ""
}

func isECS() bool {
    return os.Getenv("ECS_CONTAINER_METADATA_URI_V4") != ""
}

func isEKS() bool {
    // 检查K8s + AWS
    return os.Getenv("KUBERNETES_SERVICE_HOST") != "" && isAWS()
}

func isElasticBeanstalk() bool {
    _, err := os.Stat("/opt/elasticbeanstalk")
    return err == nil
}

func isEC2() bool {
    // 如果不是其他平台，但在AWS上，就是EC2
    return isAWS()
}

// 使用检测器
func initWithAWSDetection() (*resource.Resource, error) {
    return resource.New(context.Background(),
        resource.WithDetectors(&AWSDetector{}),
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
        ),
    )
}
```

---

## 9. 实战示例

**EC2部署**:

```go
func main() {
    // 创建Resource with AWS检测
    res, _ := resource.New(context.Background(),
        resource.WithDetectors(&AWSDetector{}),
        resource.WithAttributes(
            semconv.ServiceNameKey.String("checkout-service"),
            semconv.ServiceVersionKey.String("1.2.0"),
        ),
    )
    
    // 创建Exporter
    exporter, _ := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("collector.example.com:4317"),
        otlptracegrpc.WithInsecure(),
    )
    
    // 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )
    otel.SetTracerProvider(tp)
    
    // 应用逻辑
    // ...
}
```

**ECS Fargate部署**:

```yaml
# task-definition.json
{
  "family": "my-service",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "256",
  "memory": "512",
  "containerDefinitions": [
    {
      "name": "app",
      "image": "my-service:1.2.0",
      "environment": [
        {
          "name": "OTEL_EXPORTER_OTLP_ENDPOINT",
          "value": "http://collector:4317"
        },
        {
          "name": "OTEL_RESOURCE_ATTRIBUTES",
          "value": "service.name=my-service,service.version=1.2.0"
        }
      ]
    }
  ]
}
```

**Lambda部署**:

```go
// Lambda with OpenTelemetry Layer
package main

import (
    "context"
    "github.com/aws/aws-lambda-go/lambda"
    "go.opentelemetry.io/contrib/instrumentation/github.com/aws/aws-lambda-go/otellambda"
)

func handler(ctx context.Context, event MyEvent) (string, error) {
    // OpenTelemetry自动初始化 (通过Lambda Layer)
    
    tracer := otel.Tracer("lambda")
    ctx, span := tracer.Start(ctx, "handler")
    defer span.End()
    
    // 业务逻辑
    result := processEvent(ctx, event)
    
    return result, nil
}

func main() {
    // 使用OpenTelemetry包装的Lambda Handler
    lambda.Start(otellambda.InstrumentHandler(handler))
}
```

---

## 10. 最佳实践

```text
✅ DO (推荐)
1. 使用自动检测
   - AWSDetector自动识别平台
   - 减少手动配置

2. 环境变量配置
   - OTEL_RESOURCE_ATTRIBUTES
   - 便于CI/CD

3. 完整Resource
   - 云属性 + 服务属性
   - 便于多维度分析

4. 成本标签
   - 添加team, environment标签
   - 用于成本归因

5. 合规标签
   - 添加data_classification
   - 用于安全审计

❌ DON'T (避免)
1. 不要硬编码
   - 使用环境变量或元数据
   
2. 不要遗漏region
   - 多区域部署必需

3. 不要忽略platform
   - 便于区分EC2/ECS/Lambda

4. 不要暴露敏感信息
   - 不要在Resource中放密钥

示例最佳配置:
{
  // AWS识别
  "cloud.provider": "aws",
  "cloud.platform": "aws_ecs",
  "cloud.account.id": "123456789012",
  "cloud.region": "us-west-2",
  
  // 服务识别
  "service.name": "checkout-service",
  "service.version": "1.2.0",
  "service.namespace": "ecommerce",
  
  // 部署环境
  "deployment.environment": "production",
  
  // 成本归因
  "team": "platform",
  "cost_center": "engineering",
  
  // ECS特定
  "aws.ecs.cluster.arn": "...",
  "aws.ecs.task.family": "checkout-service"
}
```

---

## 11. 参考资源

- **AWS语义约定**: <https://opentelemetry.io/docs/specs/semconv/resource/cloud/>
- **AWS Distro for OpenTelemetry**: <https://aws-otel.github.io/>
- **EC2实例元数据**: <https://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ec2-instance-metadata.html>
- **ECS任务元数据**: <https://docs.aws.amazon.com/AmazonECS/latest/developerguide/task-metadata-endpoint.html>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [通用资源属性](01_通用资源属性.md), [AWS集成指南](../../10_云平台集成/01_AWS集成指南.md)

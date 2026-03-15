# OpenTelemetry Resource 模型详解

> **规范版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry Resource 模型详解](#opentelemetry-resource-模型详解)
  - [目录](#目录)
  - [1. Resource概述](#1-resource概述)
    - [1.1 什么是Resource](#11-什么是resource)
    - [1.2 为什么需要Resource](#12-为什么需要resource)
  - [2. 核心数据结构](#2-核心数据结构)
    - [2.1 Resource定义](#21-resource定义)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. Resource语义约定](#3-resource语义约定)
    - [3.1 Service属性](#31-service属性)
    - [3.2 部署属性](#32-部署属性)
    - [3.3 环境属性](#33-环境属性)
    - [3.4 主机属性](#34-主机属性)
    - [3.5 容器属性](#35-容器属性)
    - [3.6 Kubernetes属性](#36-kubernetes属性)
    - [3.7 云平台属性](#37-云平台属性)
  - [4. Resource检测](#4-resource检测)
    - [4.1 自动检测](#41-自动检测)
    - [4.2 手动配置](#42-手动配置)
    - [4.3 环境变量配置](#43-环境变量配置)
  - [5. Resource实现](#5-resource实现)
    - [5.1 Go实现](#51-go实现)
    - [5.2 Python实现](#52-python实现)
    - [5.3 Java实现](#53-java实现)
  - [6. Resource合并](#6-resource合并)
  - [7. 最佳实践](#7-最佳实践)
  - [8. 实战案例](#8-实战案例)
  - [9. 参考资源](#9-参考资源)

---

## 1. Resource概述

### 1.1 什么是Resource

**定义**：

```text
Resource (资源):
描述遥测数据来源实体的不可变属性集合

实体类型:
- 服务 (Service)
- 进程 (Process)
- 主机 (Host)
- 容器 (Container)
- Pod (Kubernetes)
- 云实例 (Cloud Instance)

特点:
1. 不可变 (Immutable)
   - 在应用生命周期内不变
   - 如: service.name, host.name

2. 全局共享
   - 所有Span/Metric/Log共享同一Resource
   - 避免重复存储

3. 标准化
   - 遵循语义约定
   - 保证一致性

示例Resource:
{
  "service.name": "order-service",
  "service.version": "1.2.3",
  "deployment.environment": "production",
  "host.name": "server-01",
  "host.arch": "amd64",
  "os.type": "linux"
}
```

**架构位置**：

```text
┌────────────────────────────────────────────────────┐
│                 Application                        │
│                                                    │
│  ┌──────────────────────────────────────────┐      │
│  │          OpenTelemetry SDK               │      │
│  │                                          │      │
│  │  ┌────────────────────────────────┐      │      │
│  │  │         Resource               │      │      │
│  │  │  service.name: order-service   │◄────┼────┼─ 全局共享
│  │  │  service.version: 1.2.3        │      │      │
│  │  │  host.name: server-01          │      │      │
│  │  └────────────────┬───────────────┘      │      │
│  │                   │                      │      │
│  │  ┌────────────────▼───────────────┐      │      │
│  │  │   Traces / Metrics / Logs      │      │      │
│  │  └────────────────────────────────┘      │      │
│  └──────────────────────────────────────────┘      │
└────────────────────────────────────────────────────┘

每个Span/Metric/Log都关联到同一个Resource
```

### 1.2 为什么需要Resource

**价值**：

```text
1. 上下文识别
   问题: 这个Span来自哪个服务？哪台机器？
   解决: Resource提供完整上下文

2. 过滤和聚合
   查询: service.name = "order-service" AND 
         deployment.environment = "production"
   聚合: GROUP BY host.name

3. 多租户
   隔离: 不同服务/团队的数据
   计费: 按service.name计费

4. 故障定位
   场景: 某台机器CPU高
   定位: host.name + Metrics

5. 容量规划
   分析: 每个服务的资源使用
   决策: 扩容/缩容

示例场景:
查询: 生产环境order-service在主机server-01上的错误Trace
WHERE service.name = "order-service"
  AND deployment.environment = "production"
  AND host.name = "server-01"
  AND status = ERROR
```

---

## 2. 核心数据结构

### 2.1 Resource定义

**Protobuf定义**：

```protobuf
message Resource {
  // 属性列表
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 1;
  
  // 已删除属性数量
  uint32 dropped_attributes_count = 2;
}

// KeyValue定义
message KeyValue {
  string key = 1;
  AnyValue value = 2;
}
```

**Go SDK定义**：

```go
type Resource struct {
    attrs  attribute.Set  // 属性集合
    schemaURL string       // Schema URL
}

// 创建Resource
func NewResource(attrs ...attribute.KeyValue) (*Resource, error)

// 合并Resource
func (r *Resource) Merge(other *Resource) (*Resource, error)
```

### 2.2 形式化定义

```text
Resource定义:
R = (A, S)

其中:
A: Attributes (属性集合)
  A = {(k₁,v₁), (k₂,v₂), ..., (kₙ,vₙ)}
  kᵢ: string (键, 必须唯一)
  vᵢ: AnyValue (值)

S: SchemaURL (模式URL)
  S: string
  指向属性定义的版本

约束:
1. 键唯一性: ∀i,j: i≠j → kᵢ≠kⱼ
2. 不可变性: Resource创建后不可修改
3. 必需属性: service.name必须存在

Resource关系:
R₁ ∪ R₂ = R₃ (合并操作)
- 冲突时: R₂覆盖R₁
- 空Resource是单位元

示例:
R₁ = {service.name: "api", version: "1.0"}
R₂ = {service.name: "api", env: "prod"}
R₁ ∪ R₂ = {service.name: "api", version: "1.0", env: "prod"}
```

---

## 3. Resource语义约定

### 3.1 Service属性

**核心Service属性**：

```text
必需属性:
- service.name: 服务名称
  类型: string
  示例: "order-service"
  唯一标识: 必须在同一namespace内唯一

推荐属性:
- service.version: 服务版本
  类型: string
  示例: "1.2.3", "v2.0.0-rc1"
  格式: SemVer推荐

- service.namespace: 服务命名空间
  类型: string
  示例: "ecommerce", "payments"
  用途: 逻辑分组

- service.instance.id: 服务实例ID
  类型: string
  示例: "pod-abc123", "instance-001"
  唯一性: 全局唯一

完整标识:
service_identity = (namespace, name, instance.id)
```

**示例**：

```yaml
service.name: "order-service"
service.version: "1.2.3"
service.namespace: "ecommerce"
service.instance.id: "pod-abc123"
```

### 3.2 部署属性

```text
deployment.environment: 部署环境
  值: "production", "staging", "development"
  示例: "production"

deployment.environment.name: 环境名称
  值: 自定义
  示例: "prod-us-west-1"
```

### 3.3 环境属性

```text
1. 操作系统
   - os.type: linux, windows, darwin
   - os.description: "Ubuntu 22.04 LTS"
   - os.version: "5.15.0"

2. 进程
   - process.pid: 进程ID
   - process.executable.name: "java"
   - process.executable.path: "/usr/bin/java"
   - process.command: 完整命令
   - process.command_line: 命令行
   - process.command_args: ["arg1", "arg2"]
   - process.owner: "appuser"
   - process.runtime.name: "OpenJDK Runtime"
   - process.runtime.version: "17.0.1"
   - process.runtime.description: "OpenJDK 64-Bit Server VM"

3. 编程语言
   - telemetry.sdk.language: "go", "python", "java"
   - telemetry.sdk.name: "opentelemetry"
   - telemetry.sdk.version: "1.24.0"
```

### 3.4 主机属性

```text
host.id: 主机唯一ID
  示例: "host-12345"

host.name: 主机名
  示例: "server-01.example.com"

host.type: 主机类型
  示例: "m5.xlarge" (AWS), "n1-standard-4" (GCP)

host.arch: CPU架构
  值: "amd64", "arm64", "x86"

host.ip: IP地址
  示例: ["10.0.1.5", "192.168.1.100"]

host.mac: MAC地址
  示例: ["00:1A:2B:3C:4D:5E"]

host.image.name: 镜像名
  示例: "ubuntu-22.04-minimal"

host.image.id: 镜像ID
  示例: "ami-0c55b159cbfafe1f0"

host.image.version: 镜像版本
  示例: "22.04"
```

### 3.5 容器属性

```text
container.id: 容器ID
  示例: "abc123def456"

container.name: 容器名
  示例: "order-service-container"

container.image.name: 镜像名
  示例: "myregistry/order-service"

container.image.tag: 镜像标签
  示例: "1.2.3", "latest"

container.image.id: 镜像ID (SHA256)
  示例: "sha256:abc123..."

container.runtime: 容器运行时
  值: "docker", "containerd", "cri-o"
```

### 3.6 Kubernetes属性

```text
k8s.namespace.name: Kubernetes命名空间
  示例: "production"

k8s.pod.name: Pod名称
  示例: "order-service-7d9f8b6c5-abc12"

k8s.pod.uid: Pod UID
  示例: "abc123-def456-..."

k8s.deployment.name: Deployment名称
  示例: "order-service"

k8s.deployment.uid: Deployment UID

k8s.replicaset.name: ReplicaSet名称
  示例: "order-service-7d9f8b6c5"

k8s.replicaset.uid: ReplicaSet UID

k8s.statefulset.name: StatefulSet名称

k8s.daemonset.name: DaemonSet名称

k8s.job.name: Job名称

k8s.cronjob.name: CronJob名称

k8s.container.name: 容器名称
  示例: "order-service"

k8s.node.name: 节点名称
  示例: "node-01"

k8s.node.uid: 节点UID

k8s.cluster.name: 集群名称
  示例: "production-cluster"
```

### 3.7 云平台属性

**通用云属性**：

```text
cloud.provider: 云提供商
  值: "aws", "azure", "gcp", "alibaba_cloud"

cloud.account.id: 云账号ID
  示例: "123456789012" (AWS)

cloud.region: 云区域
  示例: "us-west-2" (AWS), "westus2" (Azure)

cloud.availability_zone: 可用区
  示例: "us-west-2a"

cloud.platform: 云平台
  值: "aws_ec2", "azure_vm", "gcp_compute_engine"
```

**AWS属性**：

```text
cloud.provider: "aws"

cloud.platform: 
  - "aws_ec2": EC2实例
  - "aws_ecs": ECS容器
  - "aws_eks": EKS Kubernetes
  - "aws_lambda": Lambda函数

aws.ecs.task.arn: ECS任务ARN
aws.ecs.task.family: 任务定义家族
aws.ecs.task.revision: 任务定义版本
aws.ecs.cluster.arn: 集群ARN
aws.ecs.container.arn: 容器ARN

aws.eks.cluster.arn: EKS集群ARN

aws.lambda.function.name: Lambda函数名
aws.lambda.function.version: 函数版本
```

**GCP属性**：

```text
cloud.provider: "gcp"

cloud.platform:
  - "gcp_compute_engine": Compute Engine
  - "gcp_kubernetes_engine": GKE
  - "gcp_cloud_run": Cloud Run
  - "gcp_cloud_functions": Cloud Functions

gcp.gce.instance.name: 实例名
gcp.gce.instance.hostname: 主机名

gcp.cloud_run.job.execution: Cloud Run执行ID
gcp.cloud_run.job.task_index: 任务索引
```

**Azure属性**：

```text
cloud.provider: "azure"

cloud.platform:
  - "azure_vm": 虚拟机
  - "azure_container_instances": 容器实例
  - "azure_aks": AKS
  - "azure_functions": Azure Functions

azure.vm.name: VM名称
azure.vm.size: VM大小
azure.vm.scaleset.name: 扩展集名称
```

---

## 4. Resource检测

### 4.1 自动检测

**ResourceDetectors**：

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/contrib/detectors/aws/ec2"
    "go.opentelemetry.io/contrib/detectors/gcp"
)

// 自动检测Resource
res, err := resource.New(ctx,
    resource.WithDetectors(
        // 环境变量检测器
        resource.WithFromEnv(),
        
        // 主机检测器
        resource.WithHost(),
        
        // 操作系统检测器
        resource.WithOS(),
        
        // 进程检测器
        resource.WithProcess(),
        
        // 容器检测器
        resource.WithContainer(),
        
        // AWS EC2检测器
        ec2.NewResourceDetector(),
        
        // GCP检测器
        gcp.NewDetector(),
    ),
)
```

**检测器优先级**：

```text
1. 显式配置 (最高优先级)
2. 环境变量 (OTEL_RESOURCE_ATTRIBUTES)
3. SDK自动检测
4. 默认值 (最低优先级)

合并规则: 高优先级覆盖低优先级
```

### 4.2 手动配置

**Go示例**：

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// 手动创建Resource
res, err := resource.Merge(
    resource.Default(),
    resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceName("order-service"),
        semconv.ServiceVersion("1.2.3"),
        semconv.ServiceNamespace("ecommerce"),
        semconv.DeploymentEnvironment("production"),
        attribute.String("custom.attribute", "value"),
    ),
)
```

### 4.3 环境变量配置

```bash
# OTEL_RESOURCE_ATTRIBUTES
export OTEL_RESOURCE_ATTRIBUTES="service.name=order-service,service.version=1.2.3,deployment.environment=production"

# OTEL_SERVICE_NAME (简化)
export OTEL_SERVICE_NAME="order-service"

# 应用会自动读取这些环境变量
```

---

## 5. Resource实现

### 5.1 Go实现

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/sdk/trace"
)

func initResource() (*resource.Resource, error) {
    return resource.Merge(
        // 默认Resource
        resource.Default(),
        
        // 自定义Resource
        resource.NewWithAttributes(
            semconv.SchemaURL,
            
            // Service属性
            semconv.ServiceName("order-service"),
            semconv.ServiceVersion("1.2.3"),
            semconv.ServiceNamespace("ecommerce"),
            semconv.ServiceInstanceID("instance-001"),
            
            // Deployment属性
            semconv.DeploymentEnvironment("production"),
            
            // Host属性
            semconv.HostName("server-01"),
            semconv.HostArch("amd64"),
            
            // 自定义属性
            attribute.String("team", "platform"),
            attribute.String("region", "us-west-1"),
        ),
    )
}

func main() {
    ctx := context.Background()
    
    // 创建Resource
    res, err := initResource()
    if err != nil {
        panic(err)
    }
    
    // 创建TracerProvider with Resource
    tp := trace.NewTracerProvider(
        trace.WithResource(res),
    )
    otel.SetTracerProvider(tp)
    
    // 所有Span都会继承这个Resource
    tracer := otel.Tracer("my-tracer")
    _, span := tracer.Start(ctx, "operation")
    defer span.End()
}
```

### 5.2 Python实现

```python
from opentelemetry import trace
from opentelemetry.sdk.resources import Resource, SERVICE_NAME, SERVICE_VERSION
from opentelemetry.sdk.trace import TracerProvider

# 创建Resource
resource = Resource.create({
    SERVICE_NAME: "order-service",
    SERVICE_VERSION: "1.2.3",
    "service.namespace": "ecommerce",
    "deployment.environment": "production",
    "host.name": "server-01",
    "team": "platform"
})

# 创建TracerProvider with Resource
provider = TracerProvider(resource=resource)
trace.set_tracer_provider(provider)

# 所有Span都会继承这个Resource
tracer = trace.get_tracer(__name__)
with tracer.start_as_current_span("operation"):
    pass
```

### 5.3 Java实现

```java
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.semconv.ResourceAttributes;

// 创建Resource
Resource resource = Resource.create(
    Attributes.builder()
        .put(ResourceAttributes.SERVICE_NAME, "order-service")
        .put(ResourceAttributes.SERVICE_VERSION, "1.2.3")
        .put(ResourceAttributes.SERVICE_NAMESPACE, "ecommerce")
        .put(ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production")
        .put(ResourceAttributes.HOST_NAME, "server-01")
        .put("team", "platform")
        .build()
);

// 创建TracerProvider with Resource
SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
    .setResource(resource)
    .build();
```

---

## 6. Resource合并

**合并规则**：

```text
合并操作: R₁ ∪ R₂

规则:
1. 键不冲突: 直接合并
   R₁ = {a: 1, b: 2}
   R₂ = {c: 3}
   Result = {a: 1, b: 2, c: 3}

2. 键冲突: 后者覆盖前者
   R₁ = {a: 1, b: 2}
   R₂ = {b: 3, c: 4}
   Result = {a: 1, b: 3, c: 4}

3. SchemaURL冲突: 报错
   不同SchemaURL不能合并

4. 空Resource是单位元
   R ∪ ∅ = ∅ ∪ R = R
```

**代码示例**：

```go
// 合并Resource
res1 := resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceName("api"),
    semconv.ServiceVersion("1.0"),
)

res2 := resource.NewWithAttributes(
    semconv.SchemaURL,
    semconv.ServiceVersion("2.0"),  // 覆盖
    semconv.DeploymentEnvironment("prod"),  // 新增
)

merged, err := resource.Merge(res1, res2)
// Result: service.name=api, service.version=2.0, deployment.environment=prod
```

---

## 7. 最佳实践

```text
1. 必需属性
   ✅ 始终设置service.name
   ✅ 设置service.version
   ✅ 设置deployment.environment

2. 使用语义约定
   ✅ 使用标准属性名
   ❌ 避免自定义命名 (除非必要)

3. 自动检测
   ✅ 使用ResourceDetectors
   ✅ 环境变量配置
   ❌ 避免硬编码

4. 避免高基数
   ❌ 不要在Resource中使用UUID
   ❌ 不要使用时间戳
   ❌ 不要使用请求ID

5. 适度自定义
   ✅ 添加team, region等自定义属性
   ❌ 不要添加过多属性 (< 20)

6. 一致性
   ✅ 同一服务使用相同Resource
   ✅ 多实例使用相同service.name
   ✅ 通过service.instance.id区分实例

7. Kubernetes
   ✅ 使用Downward API注入Pod信息
   ✅ 使用k8s.* 属性

8. 安全性
   ❌ 不要在Resource中存储敏感信息
   ❌ 不要存储密码/Token
```

---

## 8. 实战案例

**Kubernetes部署**：

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-service
spec:
  template:
    spec:
      containers:
      - name: order-service
        image: myregistry/order-service:1.2.3
        env:
          # Service属性
          - name: OTEL_SERVICE_NAME
            value: "order-service"
          - name: OTEL_SERVICE_VERSION
            value: "1.2.3"
          
          # Deployment属性
          - name: OTEL_RESOURCE_ATTRIBUTES
            value: "service.namespace=ecommerce,deployment.environment=production"
          
          # Kubernetes属性 (Downward API)
          - name: K8S_POD_NAME
            valueFrom:
              fieldRef:
                fieldPath: metadata.name
          - name: K8S_POD_NAMESPACE
            valueFrom:
              fieldRef:
                fieldPath: metadata.namespace
          - name: K8S_NODE_NAME
            valueFrom:
              fieldRef:
                fieldPath: spec.nodeName
```

**应用代码**：

```go
import (
    "os"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// 从环境变量创建Resource
res, _ := resource.New(ctx,
    resource.WithFromEnv(),  // 读取OTEL_RESOURCE_ATTRIBUTES
    resource.WithHost(),
    resource.WithOS(),
    resource.WithProcess(),
    resource.WithContainer(),
    resource.WithAttributes(
        // Kubernetes属性
        semconv.K8SPodName(os.Getenv("K8S_POD_NAME")),
        semconv.K8SNamespaceName(os.Getenv("K8S_POD_NAMESPACE")),
        semconv.K8SNodeName(os.Getenv("K8S_NODE_NAME")),
    ),
)

// Result Resource:
// service.name: "order-service"
// service.version: "1.2.3"
// service.namespace: "ecommerce"
// deployment.environment: "production"
// k8s.pod.name: "order-service-7d9f8b6c5-abc12"
// k8s.namespace.name: "production"
// k8s.node.name: "node-01"
// host.name: "node-01"
// ...
```

---

## 9. 参考资源

- **Resource规范**: <https://opentelemetry.io/docs/specs/otel/resource/sdk/>
- **语义约定**: <https://opentelemetry.io/docs/specs/semconv/resource/>
- **Go SDK**: <https://pkg.go.dev/go.opentelemetry.io/otel/sdk/resource>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [Span结构](../01_Traces数据模型/01_Span结构.md), [SDK概述](../../04_核心组件/01_SDK概述.md)

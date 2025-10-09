# Resource 定义

## 📋 目录

- [Resource 定义](#resource-定义)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Resource](#什么是-resource)
    - [为什么需要 Resource](#为什么需要-resource)
  - [Resource 数据结构](#resource-数据结构)
    - [1. 完整定义](#1-完整定义)
    - [2. Protocol Buffers 定义](#2-protocol-buffers-定义)
    - [3. Go 结构体定义](#3-go-结构体定义)
  - [核心属性](#核心属性)
    - [1. service.\* 属性](#1-service-属性)
    - [2. host.\* 属性](#2-host-属性)
    - [3. process.\* 属性](#3-process-属性)
    - [4. cloud.\* 属性](#4-cloud-属性)
    - [5. k8s.\* 属性](#5-k8s-属性)
  - [Resource 标识](#resource-标识)
    - [1. 唯一性标识](#1-唯一性标识)
    - [2. 标识符组合](#2-标识符组合)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本实现](#1-基本实现)
    - [2. Resource 构建器](#2-resource-构建器)
    - [3. 预定义 Resource](#3-预定义-resource)
  - [Resource 生命周期](#resource-生命周期)
    - [1. 创建阶段](#1-创建阶段)
    - [2. 检测阶段](#2-检测阶段)
    - [3. 合并阶段](#3-合并阶段)
    - [4. 使用阶段](#4-使用阶段)
  - [最佳实践](#最佳实践)
    - [1. 属性选择](#1-属性选择)
    - [2. 属性数量](#2-属性数量)
    - [3. 值规范](#3-值规范)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 Resource

**Resource** 是 OpenTelemetry 中用于描述遥测数据来源的实体。它是一组不可变的属性，用于标识产生遥测数据的服务、主机、进程等。

```text
Resource = {
  service.name: "api-gateway",
  service.version: "1.0.0",
  host.name: "server-01",
  deployment.environment: "production"
}
```

### 为什么需要 Resource

```text
问题：
❌ 无法区分不同服务的遥测数据
❌ 难以定位问题来源
❌ 缺少上下文信息

Resource 解决方案：
✅ 统一标识遥测数据来源
✅ 提供丰富的上下文信息
✅ 支持多维度分析和过滤
✅ 自动检测和配置
```

---

## Resource 数据结构

### 1. 完整定义

Resource 由一组键值对属性组成：

```text
Resource {
  Attributes: map[string]Value
}

常见属性类别：
- Service Attributes: 服务标识
- Host Attributes: 主机信息
- Process Attributes: 进程信息
- Cloud Attributes: 云环境
- Kubernetes Attributes: K8s 资源
- Deployment Attributes: 部署信息
```

### 2. Protocol Buffers 定义

```protobuf
message Resource {
  // 资源属性
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 1;
  
  // 被丢弃的属性数量
  uint32 dropped_attributes_count = 2;
}

message KeyValue {
  string key = 1;
  AnyValue value = 2;
}
```

### 3. Go 结构体定义

```go
package resource

import (
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
)

// Resource 表示遥测数据的来源
type Resource struct {
    attrs *attribute.Set
}

// New 创建新的 Resource
func New(attrs ...attribute.KeyValue) *Resource {
    return &Resource{
        attrs: attribute.NewSet(attrs...),
    }
}

// Attributes 返回所有属性
func (r *Resource) Attributes() []attribute.KeyValue {
    return r.attrs.ToSlice()
}

// Equal 比较两个 Resource 是否相等
func (r *Resource) Equal(other *Resource) bool {
    return r.attrs.Equals(other.attrs)
}
```

---

## 核心属性

### 1. service.* 属性

**服务标识属性** - 最重要的 Resource 属性

```go
// 必需属性
const (
    ServiceName      = "service.name"         // 服务名称 (必需)
    ServiceNamespace = "service.namespace"    // 服务命名空间
    ServiceVersion   = "service.version"      // 服务版本
    ServiceInstanceID = "service.instance.id" // 实例 ID
)

// 示例
r := resource.New(
    attribute.String(ServiceName, "api-gateway"),
    attribute.String(ServiceNamespace, "prod"),
    attribute.String(ServiceVersion, "1.0.0"),
    attribute.String(ServiceInstanceID, "instance-123"),
)
```

### 2. host.* 属性

**主机信息属性**:

```go
const (
    HostName = "host.name"           // 主机名
    HostID   = "host.id"             // 主机 ID
    HostType = "host.type"           // 主机类型
    HostArch = "host.arch"           // CPU 架构
    HostImageName = "host.image.name" // 镜像名称
    HostImageID   = "host.image.id"   // 镜像 ID
)

// 示例
r := resource.New(
    attribute.String(HostName, "server-01"),
    attribute.String(HostID, "i-1234567890abcdef0"),
    attribute.String(HostType, "m5.large"),
    attribute.String(HostArch, "amd64"),
)
```

### 3. process.* 属性

**进程信息属性**:

```go
const (
    ProcessPID          = "process.pid"             // 进程 ID
    ProcessExecutableName = "process.executable.name" // 可执行文件名
    ProcessExecutablePath = "process.executable.path" // 可执行文件路径
    ProcessCommandLine    = "process.command_line"    // 命令行
    ProcessRuntimeName    = "process.runtime.name"    // 运行时名称
    ProcessRuntimeVersion = "process.runtime.version" // 运行时版本
)

// 示例
import "os"
import "runtime"

r := resource.New(
    attribute.Int64(ProcessPID, int64(os.Getpid())),
    attribute.String(ProcessExecutableName, "api-gateway"),
    attribute.String(ProcessRuntimeName, "go"),
    attribute.String(ProcessRuntimeVersion, runtime.Version()),
)
```

### 4. cloud.* 属性

**云环境属性**:

```go
const (
    CloudProvider         = "cloud.provider"           // 云提供商
    CloudAccountID        = "cloud.account.id"         // 账户 ID
    CloudRegion           = "cloud.region"             // 区域
    CloudAvailabilityZone = "cloud.availability_zone"  // 可用区
    CloudPlatform         = "cloud.platform"           // 平台
)

// 示例 - AWS
r := resource.New(
    attribute.String(CloudProvider, "aws"),
    attribute.String(CloudAccountID, "123456789012"),
    attribute.String(CloudRegion, "us-west-2"),
    attribute.String(CloudAvailabilityZone, "us-west-2a"),
    attribute.String(CloudPlatform, "aws_ec2"),
)

// 示例 - GCP
r := resource.New(
    attribute.String(CloudProvider, "gcp"),
    attribute.String(CloudAccountID, "my-project"),
    attribute.String(CloudRegion, "us-central1"),
    attribute.String(CloudAvailabilityZone, "us-central1-a"),
    attribute.String(CloudPlatform, "gcp_compute_engine"),
)

// 示例 - Azure
r := resource.New(
    attribute.String(CloudProvider, "azure"),
    attribute.String(CloudRegion, "eastus"),
    attribute.String(CloudPlatform, "azure_vm"),
)
```

### 5. k8s.* 属性

**Kubernetes 资源属性**:

```go
const (
    K8SClusterName     = "k8s.cluster.name"      // 集群名称
    K8SNamespaceName   = "k8s.namespace.name"    // 命名空间
    K8SPodName         = "k8s.pod.name"          // Pod 名称
    K8SPodUID          = "k8s.pod.uid"           // Pod UID
    K8SContainerName   = "k8s.container.name"    // 容器名称
    K8SDeploymentName  = "k8s.deployment.name"   // Deployment 名称
    K8SReplicaSetName  = "k8s.replicaset.name"   // ReplicaSet 名称
    K8SNodeName        = "k8s.node.name"         // 节点名称
)

// 示例
r := resource.New(
    attribute.String(K8SClusterName, "prod-cluster"),
    attribute.String(K8SNamespaceName, "default"),
    attribute.String(K8SPodName, "api-gateway-7d9f8b5c4-x8z9k"),
    attribute.String(K8SPodUID, "12345678-1234-1234-1234-123456789012"),
    attribute.String(K8SContainerName, "api-gateway"),
    attribute.String(K8SDeploymentName, "api-gateway"),
    attribute.String(K8SNodeName, "node-01"),
)
```

---

## Resource 标识

### 1. 唯一性标识

Resource 通过组合多个属性来唯一标识遥测数据的来源：

```text
最小标识集合:
✅ service.name (必需)
✅ service.instance.id (推荐)

完整标识集合:
✅ service.name + service.namespace + service.version
✅ + host.name / host.id
✅ + process.pid
✅ + container.id / k8s.pod.uid
```

**Go 实现**:

```go
// UniqueID 生成 Resource 的唯一标识
func (r *Resource) UniqueID() string {
    var parts []string
    
    // Service 标识
    if v, ok := r.attrs.Value(ServiceName); ok {
        parts = append(parts, v.AsString())
    }
    if v, ok := r.attrs.Value(ServiceInstanceID); ok {
        parts = append(parts, v.AsString())
    }
    
    // Host 标识
    if v, ok := r.attrs.Value(HostName); ok {
        parts = append(parts, v.AsString())
    }
    
    // Process 标识
    if v, ok := r.attrs.Value(ProcessPID); ok {
        parts = append(parts, fmt.Sprintf("pid-%d", v.AsInt64()))
    }
    
    return strings.Join(parts, ":")
}
```

### 2. 标识符组合

不同环境下的标识符组合：

```go
// 1. 裸机服务
// service.name + host.name + process.pid
"api-gateway:server-01:pid-12345"

// 2. 容器化服务
// service.name + container.id
"api-gateway:container-abc123"

// 3. Kubernetes 服务
// service.name + k8s.namespace.name + k8s.pod.name
"api-gateway:prod:api-gateway-7d9f8b5c4-x8z9k"

// 4. AWS Lambda
// service.name + faas.instance
"api-function:instance-xyz789"
```

---

## Go 1.25.1 实现

### 1. 基本实现

```go
package resource

import (
    "context"
    
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// NewResource 创建新的 Resource
func NewResource(ctx context.Context, attrs ...attribute.KeyValue) (*resource.Resource, error) {
    return resource.New(ctx, attrs...)
}

// NewResourceWithDefaults 创建带默认值的 Resource
func NewResourceWithDefaults(ctx context.Context, serviceName string) (*resource.Resource, error) {
    return resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(serviceName),
            semconv.ServiceVersion("1.0.0"),
        ),
        resource.WithProcessPID(),
        resource.WithProcessExecutableName(),
        resource.WithProcessRuntimeName(),
        resource.WithProcessRuntimeVersion(),
        resource.WithHost(),
        resource.WithOS(),
    )
}

// 使用示例
func main() {
    ctx := context.Background()
    
    // 方式 1: 手动指定属性
    res, err := NewResource(ctx,
        semconv.ServiceName("api-gateway"),
        semconv.ServiceVersion("1.0.0"),
        semconv.DeploymentEnvironment("production"),
    )
    if err != nil {
        log.Fatal(err)
    }
    
    // 方式 2: 使用默认值
    res, err = NewResourceWithDefaults(ctx, "api-gateway")
    if err != nil {
        log.Fatal(err)
    }
}
```

### 2. Resource 构建器

```go
// ResourceBuilder Resource 构建器
type ResourceBuilder struct {
    attrs []attribute.KeyValue
}

// NewResourceBuilder 创建构建器
func NewResourceBuilder() *ResourceBuilder {
    return &ResourceBuilder{
        attrs: make([]attribute.KeyValue, 0),
    }
}

// WithService 设置服务信息
func (b *ResourceBuilder) WithService(name, version, namespace string) *ResourceBuilder {
    b.attrs = append(b.attrs,
        semconv.ServiceName(name),
        semconv.ServiceVersion(version),
        semconv.ServiceNamespace(namespace),
    )
    return b
}

// WithDeployment 设置部署信息
func (b *ResourceBuilder) WithDeployment(env string) *ResourceBuilder {
    b.attrs = append(b.attrs,
        semconv.DeploymentEnvironment(env),
    )
    return b
}

// WithHost 设置主机信息
func (b *ResourceBuilder) WithHost(name, id string) *ResourceBuilder {
    b.attrs = append(b.attrs,
        semconv.HostName(name),
        semconv.HostID(id),
    )
    return b
}

// WithK8s 设置 Kubernetes 信息
func (b *ResourceBuilder) WithK8s(cluster, namespace, pod string) *ResourceBuilder {
    b.attrs = append(b.attrs,
        semconv.K8SClusterName(cluster),
        semconv.K8SNamespaceName(namespace),
        semconv.K8SPodName(pod),
    )
    return b
}

// Build 构建 Resource
func (b *ResourceBuilder) Build(ctx context.Context) (*resource.Resource, error) {
    return resource.New(ctx,
        resource.WithAttributes(b.attrs...),
    )
}

// 使用示例
res, err := NewResourceBuilder().
    WithService("api-gateway", "1.0.0", "prod").
    WithDeployment("production").
    WithHost("server-01", "i-1234567890abcdef0").
    Build(context.Background())
```

### 3. 预定义 Resource

```go
// 常用 Resource 预定义
var (
    // ProductionResource 生产环境 Resource
    ProductionResource = func(serviceName string) (*resource.Resource, error) {
        return resource.New(context.Background(),
            resource.WithAttributes(
                semconv.ServiceName(serviceName),
                semconv.DeploymentEnvironment("production"),
            ),
            resource.WithHost(),
            resource.WithProcess(),
        )
    }
    
    // DevelopmentResource 开发环境 Resource
    DevelopmentResource = func(serviceName string) (*resource.Resource, error) {
        return resource.New(context.Background(),
            resource.WithAttributes(
                semconv.ServiceName(serviceName),
                semconv.DeploymentEnvironment("development"),
            ),
        )
    }
)

// 使用
res, _ := ProductionResource("api-gateway")
```

---

## Resource 生命周期

### 1. 创建阶段

```go
// 创建 Resource
ctx := context.Background()
res, err := resource.New(ctx,
    resource.WithAttributes(
        semconv.ServiceName("api-gateway"),
    ),
)
```

### 2. 检测阶段

```go
// 自动检测环境信息
res, err := resource.New(ctx,
    resource.WithAttributes(semconv.ServiceName("api-gateway")),
    resource.WithHost(),          // 自动检测主机信息
    resource.WithOS(),            // 自动检测操作系统
    resource.WithProcess(),       // 自动检测进程信息
    resource.WithContainer(),     // 自动检测容器信息
    resource.WithFromEnv(),       // 从环境变量读取
)
```

### 3. 合并阶段

```go
// 合并多个 Resource
res1, _ := resource.New(ctx, 
    resource.WithAttributes(semconv.ServiceName("api-gateway")))
    
res2, _ := resource.New(ctx,
    resource.WithHost())

// 合并 (res2 覆盖 res1 的重复属性)
merged, err := resource.Merge(res1, res2)
```

### 4. 使用阶段

```go
// 在 TracerProvider 中使用
tp := trace.NewTracerProvider(
    trace.WithResource(res),
)

// 在 MeterProvider 中使用
mp := metric.NewMeterProvider(
    metric.WithResource(res),
)

// 在 LoggerProvider 中使用
lp := log.NewLoggerProvider(
    log.WithResource(res),
)
```

---

## 最佳实践

### 1. 属性选择

```go
// ✅ 正确：包含必需属性
res := resource.New(ctx,
    semconv.ServiceName("api-gateway"),        // 必需
    semconv.ServiceVersion("1.0.0"),           // 推荐
    semconv.DeploymentEnvironment("production"), // 推荐
)

// ❌ 错误：缺少 service.name
res := resource.New(ctx,
    semconv.ServiceVersion("1.0.0"),
)
```

### 2. 属性数量

```go
// ✅ 正确：适量的属性 (< 20)
res := resource.New(ctx,
    semconv.ServiceName("api-gateway"),
    semconv.ServiceVersion("1.0.0"),
    semconv.DeploymentEnvironment("production"),
    semconv.HostName("server-01"),
)

// ❌ 错误：过多的属性
res := resource.New(ctx,
    attribute.String("custom.attr1", "value1"),
    attribute.String("custom.attr2", "value2"),
    // ... 50+ 个自定义属性
)
```

### 3. 值规范

```go
// ✅ 正确：使用标准值
res := resource.New(ctx,
    semconv.ServiceName("api-gateway"),           // 小写，连字符
    semconv.DeploymentEnvironment("production"),  // 标准值
)

// ❌ 错误：非标准值
res := resource.New(ctx,
    attribute.String("service.name", "ApiGateway"),  // 大写
    attribute.String("deployment.environment", "prod"), // 缩写
)
```

---

## 常见问题

**Q1: service.name 和 service.namespace 的区别？**

```text
service.name: 服务的逻辑名称
  示例: "api-gateway", "user-service"

service.namespace: 服务的命名空间/分组
  示例: "prod", "staging", "team-a"

完整标识: service.namespace + service.name
  示例: "prod:api-gateway"
```

**Q2: 何时使用 service.instance.id？**

```text
使用场景:
✅ 同一服务有多个实例
✅ 需要区分特定实例
✅ 负载均衡环境

生成方式:
- 容器: 使用 container ID
- K8s: 使用 pod UID
- 裸机: 使用 hostname + PID
- AWS: 使用 instance ID
```

**Q3: Resource 是否可变？**

```text
❌ Resource 是不可变的 (immutable)

原因:
1. 保证数据一致性
2. 支持并发安全
3. 简化缓存和比较

如果需要修改，创建新的 Resource:
res1 := resource.New(...)
res2, _ := resource.Merge(res1, newAttrs)
```

---

## 参考资源

- [OpenTelemetry Resource Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/resource/)
- [Go SDK Resource Package](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/resource)
- [02_资源检测.md](./02_资源检测.md)
- [03_资源合并.md](./03_资源合并.md)

---

**🎉 恭喜！你已经掌握了 Resource 的完整定义！**

现在你可以：

- ✅ 理解 Resource 的作用和结构
- ✅ 使用核心属性标识资源
- ✅ 实现 Resource 创建和配置
- ✅ 遵循最佳实践

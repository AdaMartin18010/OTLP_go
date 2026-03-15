# Azure云平台属性详解

> **Microsoft Azure**: Resource与Span完整语义约定规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [Azure云平台属性详解](#azure云平台属性详解)
  - [目录](#目录)
  - [1. Azure概述](#1-azure概述)
    - [1.1 Azure特点](#11-azure特点)
    - [1.2 核心服务](#12-核心服务)
  - [2. Azure通用Resource属性](#2-azure通用resource属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Azure VM属性](#3-azure-vm属性)
    - [3.1 虚拟机属性](#31-虚拟机属性)
    - [3.2 自动检测实现](#32-自动检测实现)
  - [4. Azure AKS属性](#4-azure-aks属性)
    - [4.1 Kubernetes属性](#41-kubernetes属性)
    - [4.2 AKS特有属性](#42-aks特有属性)
  - [5. Azure Functions属性](#5-azure-functions属性)
    - [5.1 Serverless属性](#51-serverless属性)
    - [5.2 触发器属性](#52-触发器属性)
  - [6. Azure App Service属性](#6-azure-app-service属性)
    - [6.1 Web应用属性](#61-web应用属性)
    - [6.2 部署槽属性](#62-部署槽属性)
  - [7. Azure Container Instances属性](#7-azure-container-instances属性)
    - [7.1 容器属性](#71-容器属性)
    - [7.2 容器组属性](#72-容器组属性)
  - [8. Go实现示例](#8-go实现示例)
    - [8.1 Azure VM检测](#81-azure-vm检测)
    - [8.2 Azure AKS检测](#82-azure-aks检测)
    - [8.3 Azure Functions检测](#83-azure-functions检测)
  - [9. Python实现示例](#9-python实现示例)
    - [9.1 通用Azure检测](#91-通用azure检测)
    - [9.2 App Service检测](#92-app-service检测)
  - [10. 后端集成](#10-后端集成)
    - [10.1 Azure Monitor集成](#101-azure-monitor集成)
    - [10.2 Application Insights集成](#102-application-insights集成)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 属性命名规范](#111-属性命名规范)
    - [11.2 性能优化](#112-性能优化)
    - [11.3 成本优化](#113-成本优化)

---

## 1. Azure概述

### 1.1 Azure特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Microsoft Azure云平台:

核心优势:
✅ 企业级可靠性 (99.95% SLA)
✅ 全球覆盖 (60+区域)
✅ 混合云能力 (Azure Arc)
✅ Windows生态整合
✅ Active Directory集成
✅ 完善的PaaS服务
✅ 强大的AI/ML服务

vs AWS对比:
✅ 更好的Windows支持
✅ 更强的混合云能力
✅ 企业级Active Directory
✅ Office 365深度集成

vs GCP对比:
✅ 更全面的服务
✅ 更多全球区域
✅ 更成熟的企业方案

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心服务

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure核心服务:

计算服务:
✅ Azure VM (虚拟机)
✅ Azure AKS (Kubernetes)
✅ Azure Functions (Serverless)
✅ Azure App Service (PaaS)
✅ Azure Container Instances (ACI)
✅ Azure Batch

存储服务:
✅ Azure Blob Storage
✅ Azure Files
✅ Azure Disk Storage
✅ Azure Data Lake

数据库:
✅ Azure SQL Database
✅ Azure Cosmos DB
✅ Azure Database for PostgreSQL/MySQL

网络:
✅ Azure Virtual Network
✅ Azure Load Balancer
✅ Azure Application Gateway
✅ Azure Front Door

可观测性:
✅ Azure Monitor
✅ Application Insights
✅ Log Analytics

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Azure通用Resource属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"azure"` |
| `cloud.platform` | string | 平台类型 | `"azure_vm"`, `"azure_aks"`, `"azure_functions"` |
| `cloud.region` | string | Azure区域 | `"eastus"`, `"westeurope"` |
| `cloud.account.id` | string | 订阅ID | `"12345678-1234-1234-1234-123456789012"` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.resource.id` | string | 资源ID (Azure Resource Manager) | `"/subscriptions/.../resourceGroups/my-rg/..."` |
| `azure.resource_group` | string | 资源组名称 | `"my-resource-group"` |
| `azure.subscription.id` | string | 订阅ID | `"12345678-..."` |
| `azure.tenant.id` | string | 租户ID | `"87654321-..."` |
| `azure.location` | string | 位置 | `"East US"` |
| `azure.environment` | string | Azure环境 | `"AzurePublicCloud"`, `"AzureChina"` |

---

## 3. Azure VM属性

### 3.1 虚拟机属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure VM Resource属性:

必需:
✅ cloud.provider = "azure"
✅ cloud.platform = "azure_vm"
✅ cloud.region
✅ cloud.account.id

推荐:
📋 host.id (VM ID)
📋 host.name (VM名称)
📋 host.type (VM大小)
📋 azure.vm.id
📋 azure.vm.name
📋 azure.vm.size
📋 azure.vm.scale_set.name (VMSS)
📋 azure.resource_group

示例:
    ```yaml
    resource:
    attributes:
        cloud.provider: azure
        cloud.platform: azure_vm
        cloud.region: eastus
        cloud.account.id: 12345678-1234-1234-1234-123456789012
        host.id: /subscriptions/.../virtualMachines/my-vm
        host.name: my-vm
        host.type: Standard_D4s_v3
        azure.vm.id: abcd-1234-efgh-5678
        azure.vm.size: Standard_D4s_v3
        azure.resource_group: my-rg
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `azure.vm.id` | string | VM唯一ID | `"abcd1234-..."` |
| `azure.vm.name` | string | VM名称 | `"my-vm-001"` |
| `azure.vm.size` | string | VM大小 (SKU) | `"Standard_D4s_v3"` |
| `azure.vm.scale_set.name` | string | VMSS名称 | `"my-vmss"` |
| `azure.vm.zone` | string | 可用区 | `"1"`, `"2"`, `"3"` |
| `azure.vm.image.publisher` | string | 镜像发布者 | `"Canonical"` |
| `azure.vm.image.offer` | string | 镜像产品 | `"UbuntuServer"` |
| `azure.vm.image.sku` | string | 镜像SKU | `"18.04-LTS"` |

### 3.2 自动检测实现

```go
// Azure Instance Metadata Service (IMDS)
// Endpoint: http://169.254.169.254/metadata/instance?api-version=2021-02-01

type AzureVMMetadata struct {
    Compute struct {
        AzEnvironment       string `json:"azEnvironment"`
        Location            string `json:"location"`
        Name                string `json:"name"`
        ResourceGroupName   string `json:"resourceGroupName"`
        SubscriptionID      string `json:"subscriptionId"`
        VMID                string `json:"vmId"`
        VMSize              string `json:"vmSize"`
        Zone                string `json:"zone"`
        VMScaleSetName      string `json:"vmScaleSetName"`
    } `json:"compute"`
}

func DetectAzureVM(ctx context.Context) (resource.Resource, error) {
    // 创建HTTP请求
    req, err := http.NewRequestWithContext(ctx,
        "GET",
        "http://169.254.169.254/metadata/instance?api-version=2021-02-01",
        nil)
    if err != nil {
        return nil, err
    }
    
    // 必需Header
    req.Header.Set("Metadata", "true")
    
    // 发送请求
    resp, err := http.DefaultClient.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()
    
    // 解析响应
    var metadata AzureVMMetadata
    if err := json.NewDecoder(resp.Body).Decode(&metadata); err != nil {
        return nil, err
    }
    
    // 构建Resource
    attrs := []attribute.KeyValue{
        semconv.CloudProviderAzure,
        semconv.CloudPlatformAzureVM,
        semconv.CloudRegionKey.String(metadata.Compute.Location),
        semconv.CloudAccountIDKey.String(metadata.Compute.SubscriptionID),
        attribute.String("host.id", metadata.Compute.VMID),
        attribute.String("host.name", metadata.Compute.Name),
        attribute.String("host.type", metadata.Compute.VMSize),
        attribute.String("azure.vm.id", metadata.Compute.VMID),
        attribute.String("azure.vm.name", metadata.Compute.Name),
        attribute.String("azure.vm.size", metadata.Compute.VMSize),
        attribute.String("azure.resource_group", 
            metadata.Compute.ResourceGroupName),
    }
    
    if metadata.Compute.Zone != "" {
        attrs = append(attrs, 
            attribute.String("azure.vm.zone", metadata.Compute.Zone))
    }
    
    if metadata.Compute.VMScaleSetName != "" {
        attrs = append(attrs, 
            attribute.String("azure.vm.scale_set.name", 
                metadata.Compute.VMScaleSetName))
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}
```

---

## 4. Azure AKS属性

### 4.1 Kubernetes属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure AKS Resource属性:

必需:
✅ cloud.provider = "azure"
✅ cloud.platform = "azure_aks"
✅ cloud.region
✅ k8s.cluster.name
✅ k8s.namespace.name
✅ k8s.pod.name

推荐:
📋 k8s.deployment.name
📋 k8s.node.name
📋 azure.aks.cluster.resource_id
📋 azure.aks.cluster.version
📋 azure.resource_group

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `azure.aks.cluster.name` | string | AKS集群名称 | `"my-aks-cluster"` |
| `azure.aks.cluster.resource_id` | string | 集群资源ID | `"/subscriptions/.../managedClusters/my-aks"` |
| `azure.aks.cluster.version` | string | Kubernetes版本 | `"1.27.3"` |
| `azure.aks.node_pool.name` | string | 节点池名称 | `"nodepool1"` |
| `azure.aks.node_pool.mode` | string | 节点池模式 | `"System"`, `"User"` |

### 4.2 AKS特有属性

```go
func DetectAzureAKS(ctx context.Context) (resource.Resource, error) {
    // 检测Kubernetes环境
    k8sResource, err := resource.New(ctx,
        resource.WithFromEnv(),
        resource.WithContainer(),
    )
    if err != nil {
        return nil, err
    }
    
    // 从环境变量获取AKS信息
    attrs := []attribute.KeyValue{
        semconv.CloudProviderAzure,
        semconv.CloudPlatformAzureAKS,
    }
    
    // AKS集群名称 (从标签或环境变量)
    if clusterName := os.Getenv("AKS_CLUSTER_NAME"); clusterName != "" {
        attrs = append(attrs,
            attribute.String("azure.aks.cluster.name", clusterName))
    }
    
    // 从Azure IMDS获取底层VM信息
    vmMetadata, err := getAzureVMMetadata(ctx)
    if err == nil {
        attrs = append(attrs,
            semconv.CloudRegionKey.String(vmMetadata.Compute.Location),
            semconv.CloudAccountIDKey.String(
                vmMetadata.Compute.SubscriptionID),
            attribute.String("azure.resource_group", 
                vmMetadata.Compute.ResourceGroupName),
        )
    }
    
    // 合并Kubernetes属性
    aksResource := resource.NewWithAttributes(
        semconv.SchemaURL, attrs...)
    
    return resource.Merge(k8sResource, aksResource)
}
```

---

## 5. Azure Functions属性

### 5.1 Serverless属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure Functions Resource属性:

必需:
✅ cloud.provider = "azure"
✅ cloud.platform = "azure_functions"
✅ cloud.region
✅ faas.name (函数名称)

推荐:
📋 faas.id (函数ID)
📋 faas.version
📋 faas.instance
📋 azure.functions.app.name
📋 azure.functions.runtime.version
📋 azure.resource_group

示例:
    ```yaml
    resource:
    attributes:
        cloud.provider: azure
        cloud.platform: azure_functions
        cloud.region: eastus
        faas.name: MyHttpFunction
        faas.version: "1.0"
        azure.functions.app.name: my-function-app
        azure.functions.runtime.version: "~4"
        azure.resource_group: my-rg
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `azure.functions.app.name` | string | Function App名称 | `"my-function-app"` |
| `azure.functions.runtime.version` | string | Runtime版本 | `"~4"` |
| `azure.functions.runtime.name` | string | Runtime名称 | `"dotnet"`, `"node"`, `"python"` |
| `azure.functions.plan.type` | string | 托管计划 | `"Consumption"`, `"Premium"`, `"App Service"` |
| `azure.functions.slot.name` | string | 部署槽 | `"production"`, `"staging"` |

### 5.2 触发器属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure Functions触发器属性:

HTTP触发器:
✅ faas.trigger = "http"
✅ http.method
✅ http.route

Timer触发器:
✅ faas.trigger = "timer"
✅ azure.functions.timer.schedule

Queue触发器:
✅ faas.trigger = "pubsub"
✅ messaging.system = "azure_queue"
✅ messaging.destination.name

Blob触发器:
✅ faas.trigger = "datasource"
✅ azure.functions.blob.path

Event Hub触发器:
✅ faas.trigger = "pubsub"
✅ messaging.system = "azure_eventhub"
✅ messaging.destination.name

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 6. Azure App Service属性

### 6.1 Web应用属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure App Service Resource属性:

必需:
✅ cloud.provider = "azure"
✅ cloud.platform = "azure_app_service"
✅ cloud.region
✅ service.name (应用名称)

推荐:
📋 service.instance.id
📋 azure.app_service.name
📋 azure.app_service.resource_group
📋 azure.app_service.plan.name
📋 azure.app_service.slot.name

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `azure.app_service.name` | string | App Service名称 | `"my-web-app"` |
| `azure.app_service.plan.name` | string | App Service Plan | `"my-plan"` |
| `azure.app_service.plan.tier` | string | 定价层 | `"Standard"`, `"Premium"` |
| `azure.app_service.slot.name` | string | 部署槽 | `"production"`, `"staging"` |
| `azure.app_service.runtime.name` | string | Runtime | `"dotnetcore"`, `"node"`, `"python"` |
| `azure.app_service.runtime.version` | string | Runtime版本 | `"8.0"`, `"18"`, `"3.11"` |

### 6.2 部署槽属性

```go
func DetectAzureAppService(ctx context.Context) (resource.Resource, error) {
    // Azure App Service环境变量
    websiteName := os.Getenv("WEBSITE_SITE_NAME")
    if websiteName == "" {
        return nil, errors.New("not running in Azure App Service")
    }
    
    attrs := []attribute.KeyValue{
        semconv.CloudProviderAzure,
        semconv.CloudPlatformKey.String("azure_app_service"),
        attribute.String("azure.app_service.name", websiteName),
    }
    
    // Region
    if region := os.Getenv("REGION_NAME"); region != "" {
        attrs = append(attrs, semconv.CloudRegionKey.String(region))
    }
    
    // Resource Group
    if rg := os.Getenv("WEBSITE_RESOURCE_GROUP"); rg != "" {
        attrs = append(attrs, 
            attribute.String("azure.resource_group", rg))
    }
    
    // Deployment Slot
    if slot := os.Getenv("WEBSITE_SLOT_NAME"); slot != "" {
        attrs = append(attrs,
            attribute.String("azure.app_service.slot.name", slot))
    } else {
        attrs = append(attrs,
            attribute.String("azure.app_service.slot.name", "production"))
    }
    
    // Instance ID
    if instanceID := os.Getenv("WEBSITE_INSTANCE_ID"); instanceID != "" {
        attrs = append(attrs,
            semconv.ServiceInstanceIDKey.String(instanceID))
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}
```

---

## 7. Azure Container Instances属性

### 7.1 容器属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.platform` | string | 平台 | `"azure_container_instances"` |
| `azure.container_instance.name` | string | 容器实例名称 | `"my-container"` |
| `azure.container_group.name` | string | 容器组名称 | `"my-container-group"` |
| `container.id` | string | 容器ID | `"abc123..."` |
| `container.name` | string | 容器名称 | `"app"` |
| `container.image.name` | string | 镜像名称 | `"myapp"` |
| `container.image.tag` | string | 镜像标签 | `"v1.0"` |

### 7.2 容器组属性

```yaml
resource:
  attributes:
    cloud.provider: azure
    cloud.platform: azure_container_instances
    cloud.region: eastus
    azure.container_group.name: my-container-group
    azure.container_instance.name: my-container
    azure.resource_group: my-rg
    container.id: abc123def456
    container.name: app
    container.image.name: myregistry.azurecr.io/myapp
    container.image.tag: v1.0
```

---

## 8. Go实现示例

### 8.1 Azure VM检测

```go
package main

import (
    "context"
    "encoding/json"
    "net/http"
    "time"
    
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

const (
    azureIMDSEndpoint = "http://169.254.169.254/metadata/instance"
    azureIMDSVersion  = "2021-02-01"
)

type AzureIMDSMetadata struct {
    Compute struct {
        AzEnvironment     string `json:"azEnvironment"`
        Location          string `json:"location"`
        Name              string `json:"name"`
        ResourceGroupName string `json:"resourceGroupName"`
        SubscriptionID    string `json:"subscriptionId"`
        VMID              string `json:"vmId"`
        VMSize            string `json:"vmSize"`
        Zone              string `json:"zone"`
        VMScaleSetName    string `json:"vmScaleSetName"`
    } `json:"compute"`
}

func DetectAzure(ctx context.Context) (*resource.Resource, error) {
    // 创建HTTP客户端 (短超时)
    client := &http.Client{
        Timeout: 2 * time.Second,
    }
    
    // 创建请求
    req, err := http.NewRequestWithContext(ctx,
        "GET",
        azureIMDSEndpoint+"?api-version="+azureIMDSVersion,
        nil)
    if err != nil {
        return nil, err
    }
    
    // Azure IMDS必需Header
    req.Header.Set("Metadata", "true")
    
    // 发送请求
    resp, err := client.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()
    
    if resp.StatusCode != http.StatusOK {
        return nil, fmt.Errorf("IMDS returned %d", resp.StatusCode)
    }
    
    // 解析元数据
    var metadata AzureIMDSMetadata
    if err := json.NewDecoder(resp.Body).Decode(&metadata); err != nil {
        return nil, err
    }
    
    // 构建Resource属性
    attrs := []attribute.KeyValue{
        semconv.CloudProviderAzure,
        semconv.CloudPlatformAzureVM,
        semconv.CloudRegionKey.String(metadata.Compute.Location),
        semconv.CloudAccountIDKey.String(metadata.Compute.SubscriptionID),
        semconv.HostIDKey.String(metadata.Compute.VMID),
        semconv.HostNameKey.String(metadata.Compute.Name),
        semconv.HostTypeKey.String(metadata.Compute.VMSize),
        attribute.String("azure.vm.id", metadata.Compute.VMID),
        attribute.String("azure.vm.name", metadata.Compute.Name),
        attribute.String("azure.vm.size", metadata.Compute.VMSize),
        attribute.String("azure.resource_group", 
            metadata.Compute.ResourceGroupName),
        attribute.String("azure.environment", 
            metadata.Compute.AzEnvironment),
    }
    
    // 可选属性
    if metadata.Compute.Zone != "" {
        attrs = append(attrs,
            attribute.String("azure.vm.zone", metadata.Compute.Zone))
    }
    
    if metadata.Compute.VMScaleSetName != "" {
        attrs = append(attrs,
            attribute.String("azure.vm.scale_set.name", 
                metadata.Compute.VMScaleSetName))
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}
```

### 8.2 Azure AKS检测

```go
func DetectAzureAKS(ctx context.Context) (*resource.Resource, error) {
    // 先检测Kubernetes环境
    k8sDetector := resource.StringDetector(
        semconv.SchemaURL,
        semconv.CloudPlatformAzureAKS,
        func() (string, error) {
            // 检查是否在Kubernetes中
            if _, err := os.Stat("/var/run/secrets/kubernetes.io"); err != nil {
                return "", err
            }
            return string(semconv.CloudPlatformAzureAKS), nil
        },
    )
    
    k8sResource, err := resource.New(ctx,
        resource.WithDetectors(k8sDetector),
        resource.WithContainer(),
        resource.WithFromEnv(),
    )
    if err != nil {
        return nil, err
    }
    
    // 获取Azure VM元数据 (AKS节点)
    azureResource, err := DetectAzure(ctx)
    if err != nil {
        // 如果无法获取Azure元数据，返回K8s资源
        return k8sResource, nil
    }
    
    // 合并资源
    return resource.Merge(k8sResource, azureResource)
}
```

### 8.3 Azure Functions检测

```go
func DetectAzureFunctions(ctx context.Context) (*resource.Resource, error) {
    // 检查环境变量
    websiteName := os.Getenv("WEBSITE_SITE_NAME")
    functionsWorkerRuntime := os.Getenv("FUNCTIONS_WORKER_RUNTIME")
    
    if websiteName == "" || functionsWorkerRuntime == "" {
        return nil, errors.New("not running in Azure Functions")
    }
    
    attrs := []attribute.KeyValue{
        semconv.CloudProviderAzure,
        semconv.CloudPlatformAzureFunctions,
        attribute.String("azure.functions.app.name", websiteName),
        attribute.String("azure.functions.runtime.name", 
            functionsWorkerRuntime),
    }
    
    // Region
    if region := os.Getenv("REGION_NAME"); region != "" {
        attrs = append(attrs, semconv.CloudRegionKey.String(region))
    }
    
    // Runtime版本
    if runtimeVersion := os.Getenv("FUNCTIONS_EXTENSION_VERSION"); 
        runtimeVersion != "" {
        attrs = append(attrs,
            attribute.String("azure.functions.runtime.version", 
                runtimeVersion))
    }
    
    // Resource Group
    if rg := os.Getenv("WEBSITE_RESOURCE_GROUP"); rg != "" {
        attrs = append(attrs, 
            attribute.String("azure.resource_group", rg))
    }
    
    // Instance ID
    if instanceID := os.Getenv("WEBSITE_INSTANCE_ID"); instanceID != "" {
        attrs = append(attrs,
            semconv.ServiceInstanceIDKey.String(instanceID))
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}
```

---

## 9. Python实现示例

### 9.1 通用Azure检测

```python
import os
import requests
from opentelemetry.sdk.resources import Resource
from opentelemetry.semconv.resource import (
    CloudProviderValues,
    CloudPlatformValues,
    ResourceAttributes
)

AZURE_IMDS_ENDPOINT = "http://169.254.169.254/metadata/instance"
AZURE_IMDS_VERSION = "2021-02-01"

def detect_azure_vm() -> Resource:
    """检测Azure VM环境"""
    try:
        # 请求Azure IMDS
        response = requests.get(
            f"{AZURE_IMDS_ENDPOINT}?api-version={AZURE_IMDS_VERSION}",
            headers={"Metadata": "true"},
            timeout=2
        )
        response.raise_for_status()
        
        metadata = response.json()
        compute = metadata.get("compute", {})
        
        # 构建Resource属性
        attributes = {
            ResourceAttributes.CLOUD_PROVIDER: CloudProviderValues.AZURE.value,
            ResourceAttributes.CLOUD_PLATFORM: CloudPlatformValues.AZURE_VM.value,
            ResourceAttributes.CLOUD_REGION: compute.get("location"),
            ResourceAttributes.CLOUD_ACCOUNT_ID: compute.get("subscriptionId"),
            ResourceAttributes.HOST_ID: compute.get("vmId"),
            ResourceAttributes.HOST_NAME: compute.get("name"),
            ResourceAttributes.HOST_TYPE: compute.get("vmSize"),
            "azure.vm.id": compute.get("vmId"),
            "azure.vm.name": compute.get("name"),
            "azure.vm.size": compute.get("vmSize"),
            "azure.resource_group": compute.get("resourceGroupName"),
        }
        
        # 可选属性
        if zone := compute.get("zone"):
            attributes["azure.vm.zone"] = zone
        
        if vmss_name := compute.get("vmScaleSetName"):
            attributes["azure.vm.scale_set.name"] = vmss_name
        
        return Resource.create(attributes)
        
    except Exception as e:
        # 非Azure环境或检测失败
        return Resource.empty()

def detect_azure_functions() -> Resource:
    """检测Azure Functions环境"""
    website_name = os.getenv("WEBSITE_SITE_NAME")
    functions_runtime = os.getenv("FUNCTIONS_WORKER_RUNTIME")
    
    if not website_name or not functions_runtime:
        return Resource.empty()
    
    attributes = {
        ResourceAttributes.CLOUD_PROVIDER: CloudProviderValues.AZURE.value,
        ResourceAttributes.CLOUD_PLATFORM: CloudPlatformValues.AZURE_FUNCTIONS.value,
        "azure.functions.app.name": website_name,
        "azure.functions.runtime.name": functions_runtime,
    }
    
    # 可选属性
    if region := os.getenv("REGION_NAME"):
        attributes[ResourceAttributes.CLOUD_REGION] = region
    
    if runtime_version := os.getenv("FUNCTIONS_EXTENSION_VERSION"):
        attributes["azure.functions.runtime.version"] = runtime_version
    
    if resource_group := os.getenv("WEBSITE_RESOURCE_GROUP"):
        attributes["azure.resource_group"] = resource_group
    
    if instance_id := os.getenv("WEBSITE_INSTANCE_ID"):
        attributes[ResourceAttributes.SERVICE_INSTANCE_ID] = instance_id
    
    return Resource.create(attributes)
```

### 9.2 App Service检测

```python
def detect_azure_app_service() -> Resource:
    """检测Azure App Service环境"""
    website_name = os.getenv("WEBSITE_SITE_NAME")
    
    # 区分Functions和App Service
    if os.getenv("FUNCTIONS_WORKER_RUNTIME"):
        return Resource.empty()  # 这是Functions，不是App Service
    
    if not website_name:
        return Resource.empty()
    
    attributes = {
        ResourceAttributes.CLOUD_PROVIDER: CloudProviderValues.AZURE.value,
        ResourceAttributes.CLOUD_PLATFORM: "azure_app_service",
        "azure.app_service.name": website_name,
    }
    
    # Region
    if region := os.getenv("REGION_NAME"):
        attributes[ResourceAttributes.CLOUD_REGION] = region
    
    # Resource Group
    if resource_group := os.getenv("WEBSITE_RESOURCE_GROUP"):
        attributes["azure.resource_group"] = resource_group
    
    # Deployment Slot
    slot_name = os.getenv("WEBSITE_SLOT_NAME", "production")
    attributes["azure.app_service.slot.name"] = slot_name
    
    # Instance ID
    if instance_id := os.getenv("WEBSITE_INSTANCE_ID"):
        attributes[ResourceAttributes.SERVICE_INSTANCE_ID] = instance_id
    
    return Resource.create(attributes)

# 统一检测函数
def detect_azure() -> Resource:
    """自动检测Azure环境类型"""
    # 优先级: Functions > App Service > VM
    
    # 1. Azure Functions
    functions_resource = detect_azure_functions()
    if functions_resource.attributes:
        return functions_resource
    
    # 2. Azure App Service
    app_service_resource = detect_azure_app_service()
    if app_service_resource.attributes:
        return app_service_resource
    
    # 3. Azure VM (including AKS)
    vm_resource = detect_azure_vm()
    return vm_resource
```

---

## 10. 后端集成

### 10.1 Azure Monitor集成

```yaml
# OpenTelemetry Collector配置
exporters:
  azuremonitor:
    instrumentation_key: "${APPLICATIONINSIGHTS_CONNECTION_STRING}"
    # 或使用Connection String
    connection_string: "InstrumentationKey=...;IngestionEndpoint=..."
    
    # 采样配置
    sampling_percentage: 100
    
    # 最大批处理
    max_batch_size: 100
    max_batch_interval: 10s

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, resource]
      exporters: [azuremonitor]
    
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [azuremonitor]
```

### 10.2 Application Insights集成

```go
// Azure Monitor Exporter
import (
    "go.opentelemetry.io/otel/exporters/azuremonitor"
    "go.opentelemetry.io/otel/sdk/trace"
)

func InitAzureMonitor(ctx context.Context) (*trace.TracerProvider, error) {
    // 获取Connection String
    connectionString := os.Getenv("APPLICATIONINSIGHTS_CONNECTION_STRING")
    
    // 创建Azure Monitor Exporter
    exporter, err := azuremonitor.NewExporter(
        azuremonitor.WithConnectionString(connectionString),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithResource(detectAzureResource(ctx)),
    )
    
    return tp, nil
}

func detectAzureResource(ctx context.Context) *resource.Resource {
    // 自动检测Azure环境
    azureResource, _ := DetectAzure(ctx)
    
    // 默认资源
    defaultResource := resource.Default()
    
    // 合并
    return resource.Merge(defaultResource, azureResource)
}
```

---

## 11. 最佳实践

### 11.1 属性命名规范

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure属性命名规范:

1. 使用azure前缀 ⭐⭐⭐⭐⭐
   azure.vm.id
   azure.aks.cluster.name
   azure.functions.app.name

2. 遵循OpenTelemetry语义约定 ⭐⭐⭐⭐⭐
   cloud.provider = "azure"
   cloud.platform = "azure_vm"
   cloud.region

3. 资源层次结构 ⭐⭐⭐⭐
   azure.resource_group
   azure.subscription.id
   azure.tenant.id

4. 避免PII ⭐⭐⭐⭐⭐
   ❌ 不要包含敏感信息
   ❌ 不要包含个人数据

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 11.2 性能优化

```go
// IMDS请求优化
var (
    azureMetadataOnce  sync.Once
    azureMetadataCache *AzureIMDSMetadata
    azureMetadataErr   error
)

func GetAzureMetadata(ctx context.Context) (*AzureIMDSMetadata, error) {
    azureMetadataOnce.Do(func() {
        // 创建超时Context
        ctx, cancel := context.WithTimeout(ctx, 2*time.Second)
        defer cancel()
        
        // 请求IMDS
        azureMetadataCache, azureMetadataErr = fetchAzureIMDS(ctx)
    })
    
    return azureMetadataCache, azureMetadataErr
}

// Resource缓存
var globalResource *resource.Resource

func GetOrCreateResource(ctx context.Context) *resource.Resource {
    if globalResource == nil {
        globalResource, _ = DetectAzure(ctx)
    }
    return globalResource
}
```

### 11.3 成本优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure Monitor成本优化:

1. 采样策略 ⭐⭐⭐⭐⭐
   - 生产: 10-20%
   - 测试: 50%
   - 开发: 100%

2. 数据保留 ⭐⭐⭐⭐
   - 默认90天
   - 按需调整 (30-730天)

3. 数据摄取限制 ⭐⭐⭐⭐
   - 设置每日上限
   - 监控摄取量

4. 属性优化 ⭐⭐⭐
   - 只发送必需属性
   - 避免高基数属性

Application Insights定价:
- 前5GB/月: 免费
- 超出: $2.88/GB

成本监控:
- Azure Cost Management
- 设置预算告警

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**Azure SDK版本**: Latest  
**适用场景**: Azure云原生应用、混合云架构、企业级系统

**关键特性**:

- ✅ Azure VM/AKS/Functions/App Service完整支持
- ✅ Azure IMDS自动检测
- ✅ Azure Monitor深度集成
- ✅ Application Insights原生支持
- ✅ Go/Python完整示例
- ✅ 成本优化策略
- ✅ 企业级最佳实践

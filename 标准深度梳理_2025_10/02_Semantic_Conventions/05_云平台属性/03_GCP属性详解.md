# GCP云平台属性详解

> **Google Cloud Platform**: Resource与Span完整语义约定规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [GCP云平台属性详解](#gcp云平台属性详解)
  - [目录](#目录)
  - [1. GCP概述](#1-gcp概述)
    - [1.1 GCP特点](#11-gcp特点)
    - [1.2 核心服务](#12-核心服务)
  - [2. GCP通用Resource属性](#2-gcp通用resource属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. GCE (Compute Engine) 属性](#3-gce-compute-engine-属性)
    - [3.1 虚拟机属性](#31-虚拟机属性)
    - [3.2 自动检测实现](#32-自动检测实现)
  - [4. GKE (Kubernetes Engine) 属性](#4-gke-kubernetes-engine-属性)
    - [4.1 Kubernetes属性](#41-kubernetes属性)
    - [4.2 GKE特有属性](#42-gke特有属性)
  - [5. Cloud Functions属性](#5-cloud-functions属性)
    - [5.1 Serverless属性](#51-serverless属性)
    - [5.2 触发器属性](#52-触发器属性)
  - [6. Cloud Run属性](#6-cloud-run属性)
    - [6.1 容器属性](#61-容器属性)
    - [6.2 服务属性](#62-服务属性)
  - [7. App Engine属性](#7-app-engine属性)
    - [7.1 应用属性](#71-应用属性)
    - [7.2 版本与实例](#72-版本与实例)
  - [8. Go实现示例](#8-go实现示例)
    - [8.1 GCE检测](#81-gce检测)
    - [8.2 GKE检测](#82-gke检测)
    - [8.3 Cloud Functions检测](#83-cloud-functions检测)
  - [9. Python实现示例](#9-python实现示例)
    - [9.1 通用GCP检测](#91-通用gcp检测)
    - [9.2 Cloud Run检测](#92-cloud-run检测)
  - [10. 后端集成](#10-后端集成)
    - [10.1 Cloud Trace集成](#101-cloud-trace集成)
    - [10.2 Cloud Monitoring集成](#102-cloud-monitoring集成)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 属性命名规范](#111-属性命名规范)
    - [11.2 性能优化](#112-性能优化)
    - [11.3 成本优化](#113-成本优化)

---

## 1. GCP概述

### 1.1 GCP特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Google Cloud Platform特点:

核心优势:
✅ 全球光纤网络 (Jupiter/Andromeda)
✅ 强大的大数据能力 (BigQuery)
✅ 领先的AI/ML服务 (Vertex AI)
✅ Kubernetes原生 (GKE是K8s原创者)
✅ 容器优先架构
✅ 开源友好
✅ 自研硬件 (TPU)

vs AWS对比:
✅ 更快的网络
✅ 更好的大数据
✅ 更强的AI/ML
✅ 更简洁的定价

vs Azure对比:
✅ 更好的容器支持
✅ 更强的开源生态
✅ 更优的全球网络

技术创新:
✅ Borg (Kubernetes前身)
✅ Colossus (分布式文件系统)
✅ Spanner (全球分布式数据库)
✅ Bigtable (NoSQL)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心服务

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

GCP核心服务:

计算服务:
✅ Compute Engine (GCE) - 虚拟机
✅ Google Kubernetes Engine (GKE)
✅ Cloud Functions - Serverless
✅ Cloud Run - 容器即服务
✅ App Engine - PaaS

存储服务:
✅ Cloud Storage (GCS)
✅ Persistent Disk
✅ Filestore

数据库:
✅ Cloud Spanner (全球分布式)
✅ Cloud SQL (PostgreSQL/MySQL)
✅ Firestore (文档数据库)
✅ Bigtable (NoSQL)
✅ BigQuery (数据仓库)

网络:
✅ Cloud Load Balancing
✅ Cloud CDN
✅ Cloud Armor (DDoS防护)

可观测性:
✅ Cloud Trace (分布式追踪)
✅ Cloud Monitoring (Stackdriver)
✅ Cloud Logging

AI/ML:
✅ Vertex AI
✅ AutoML
✅ TPU (张量处理单元)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. GCP通用Resource属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"gcp"` |
| `cloud.platform` | string | 平台类型 | `"gcp_compute_engine"`, `"gcp_kubernetes_engine"` |
| `cloud.region` | string | 区域 | `"us-central1"` |
| `cloud.availability_zone` | string | 可用区 | `"us-central1-a"` |
| `cloud.account.id` | string | 项目ID | `"my-gcp-project"` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `gcp.project.id` | string | 项目ID | `"my-project-123456"` |
| `gcp.project.number` | string | 项目编号 | `"123456789012"` |
| `gcp.resource.type` | string | GCP资源类型 | `"gce_instance"`, `"k8s_cluster"` |
| `gcp.resource.labels` | map | GCP标签 | `{"env": "prod"}` |

---

## 3. GCE (Compute Engine) 属性

### 3.1 虚拟机属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

GCE Resource属性:

必需:
✅ cloud.provider = "gcp"
✅ cloud.platform = "gcp_compute_engine"
✅ cloud.region
✅ cloud.availability_zone
✅ cloud.account.id (项目ID)

推荐:
📋 host.id (实例ID)
📋 host.name (实例名称)
📋 host.type (机器类型)
📋 gcp.gce.instance.id
📋 gcp.gce.instance.name
📋 gcp.gce.machine.type

示例:
    ```yaml
    resource:
    attributes:
        cloud.provider: gcp
        cloud.platform: gcp_compute_engine
        cloud.region: us-central1
        cloud.availability_zone: us-central1-a
        cloud.account.id: my-project-123456
        host.id: "1234567890123456789"
        host.name: my-instance
        host.type: n1-standard-4
        gcp.gce.instance.id: "1234567890123456789"
        gcp.gce.instance.name: my-instance
        gcp.gce.machine.type: n1-standard-4
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `gcp.gce.instance.id` | string | 实例ID (数字) | `"1234567890123456789"` |
| `gcp.gce.instance.name` | string | 实例名称 | `"my-instance"` |
| `gcp.gce.machine.type` | string | 机器类型 | `"n1-standard-4"`, `"e2-medium"` |
| `gcp.gce.instance.hostname` | string | 内部DNS主机名 | `"my-instance.us-central1-a.c.project.internal"` |
| `gcp.gce.instance.preemptible` | boolean | 是否抢占式 | `true`, `false` |

### 3.2 自动检测实现

```go
// GCP Metadata Server
// Endpoint: http://metadata.google.internal/computeMetadata/v1/

const (
    gcpMetadataEndpoint = "http://metadata.google.internal/computeMetadata/v1"
)

type GCEMetadata struct {
    InstanceID   string `json:"id"`
    InstanceName string `json:"name"`
    MachineType  string `json:"machineType"`
    Zone         string `json:"zone"`
    ProjectID    string `json:"projectId"`
    ProjectNumber string `json:"numericProjectId"`
}

func DetectGCE(ctx context.Context) (*resource.Resource, error) {
    // 创建HTTP客户端
    client := &http.Client{
        Timeout: 2 * time.Second,
    }
    
    // 获取实例ID
    instanceID, err := gcpMetadataRequest(ctx, client, "instance/id")
    if err != nil {
        return nil, err
    }
    
    // 获取实例名称
    instanceName, _ := gcpMetadataRequest(ctx, client, "instance/name")
    
    // 获取机器类型
    machineType, _ := gcpMetadataRequest(ctx, client, "instance/machine-type")
    // machineType格式: "projects/PROJECT_NUMBER/machineTypes/n1-standard-4"
    machineType = extractMachineType(machineType)
    
    // 获取Zone
    zone, _ := gcpMetadataRequest(ctx, client, "instance/zone")
    // zone格式: "projects/PROJECT_NUMBER/zones/us-central1-a"
    zone = extractZone(zone)
    region := zoneToRegion(zone)
    
    // 获取项目ID
    projectID, _ := gcpMetadataRequest(ctx, client, "project/project-id")
    
    // 构建Resource
    attrs := []attribute.KeyValue{
        semconv.CloudProviderGCP,
        semconv.CloudPlatformGCPComputeEngine,
        semconv.CloudRegionKey.String(region),
        semconv.CloudAvailabilityZoneKey.String(zone),
        semconv.CloudAccountIDKey.String(projectID),
        semconv.HostIDKey.String(instanceID),
        semconv.HostNameKey.String(instanceName),
        semconv.HostTypeKey.String(machineType),
        attribute.String("gcp.gce.instance.id", instanceID),
        attribute.String("gcp.gce.instance.name", instanceName),
        attribute.String("gcp.gce.machine.type", machineType),
        attribute.String("gcp.project.id", projectID),
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}

func gcpMetadataRequest(
    ctx context.Context,
    client *http.Client,
    path string,
) (string, error) {
    req, err := http.NewRequestWithContext(ctx,
        "GET",
        gcpMetadataEndpoint+"/"+path,
        nil)
    if err != nil {
        return "", err
    }
    
    // GCP Metadata Server必需Header
    req.Header.Set("Metadata-Flavor", "Google")
    
    resp, err := client.Do(req)
    if err != nil {
        return "", err
    }
    defer resp.Body.Close()
    
    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return "", err
    }
    
    return string(body), nil
}

func extractMachineType(fullType string) string {
    // "projects/123/machineTypes/n1-standard-4" -> "n1-standard-4"
    parts := strings.Split(fullType, "/")
    if len(parts) > 0 {
        return parts[len(parts)-1]
    }
    return fullType
}

func extractZone(fullZone string) string {
    // "projects/123/zones/us-central1-a" -> "us-central1-a"
    parts := strings.Split(fullZone, "/")
    if len(parts) > 0 {
        return parts[len(parts)-1]
    }
    return fullZone
}

func zoneToRegion(zone string) string {
    // "us-central1-a" -> "us-central1"
    parts := strings.Split(zone, "-")
    if len(parts) >= 3 {
        return strings.Join(parts[:len(parts)-1], "-")
    }
    return zone
}
```

---

## 4. GKE (Kubernetes Engine) 属性

### 4.1 Kubernetes属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

GKE Resource属性:

必需:
✅ cloud.provider = "gcp"
✅ cloud.platform = "gcp_kubernetes_engine"
✅ cloud.region
✅ cloud.availability_zone
✅ k8s.cluster.name
✅ k8s.namespace.name
✅ k8s.pod.name

推荐:
📋 k8s.deployment.name
📋 k8s.node.name
📋 gcp.gke.cluster.name
📋 gcp.gke.cluster.location
📋 gcp.project.id

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `gcp.gke.cluster.name` | string | GKE集群名称 | `"my-gke-cluster"` |
| `gcp.gke.cluster.location` | string | 集群位置 (区域或可用区) | `"us-central1"`, `"us-central1-a"` |
| `gcp.gke.cluster.location_type` | string | 位置类型 | `"regional"`, `"zonal"` |

### 4.2 GKE特有属性

```go
func DetectGKE(ctx context.Context) (*resource.Resource, error) {
    // 检测Kubernetes环境
    k8sResource, err := resource.New(ctx,
        resource.WithFromEnv(),
        resource.WithContainer(),
    )
    if err != nil {
        return nil, err
    }
    
    // 检查是否在GKE中
    clusterName := os.Getenv("GKE_CLUSTER_NAME")
    if clusterName == "" {
        // 从GCE metadata获取
        clusterName, _ = gcpMetadataRequest(ctx, 
            http.DefaultClient,
            "instance/attributes/cluster-name")
    }
    
    if clusterName == "" {
        return k8sResource, nil // 不是GKE
    }
    
    // 获取GCP信息
    attrs := []attribute.KeyValue{
        semconv.CloudProviderGCP,
        semconv.CloudPlatformGCPKubernetesEngine,
        attribute.String("gcp.gke.cluster.name", clusterName),
    }
    
    // 获取GCE元数据
    if projectID, err := gcpMetadataRequest(ctx, http.DefaultClient,
        "project/project-id"); err == nil {
        attrs = append(attrs,
            semconv.CloudAccountIDKey.String(projectID),
            attribute.String("gcp.project.id", projectID))
    }
    
    if zone, err := gcpMetadataRequest(ctx, http.DefaultClient,
        "instance/zone"); err == nil {
        zone = extractZone(zone)
        region := zoneToRegion(zone)
        attrs = append(attrs,
            semconv.CloudRegionKey.String(region),
            semconv.CloudAvailabilityZoneKey.String(zone),
            attribute.String("gcp.gke.cluster.location", zone))
    }
    
    gkeResource := resource.NewWithAttributes(semconv.SchemaURL, attrs...)
    
    // 合并K8s和GKE资源
    return resource.Merge(k8sResource, gkeResource)
}
```

---

## 5. Cloud Functions属性

### 5.1 Serverless属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cloud Functions Resource属性:

必需:
✅ cloud.provider = "gcp"
✅ cloud.platform = "gcp_cloud_functions"
✅ cloud.region
✅ faas.name (函数名称)

推荐:
📋 faas.version
📋 faas.instance
📋 gcp.cloud_function.name
📋 gcp.cloud_function.region
📋 gcp.project.id

示例:
    ```yaml
    resource:
    attributes:
        cloud.provider: gcp
        cloud.platform: gcp_cloud_functions
        cloud.region: us-central1
        faas.name: my-function
        faas.version: "1"
        gcp.cloud_function.name: my-function
        gcp.cloud_function.region: us-central1
        gcp.project.id: my-project-123456
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `gcp.cloud_function.name` | string | 函数名称 | `"my-function"` |
| `gcp.cloud_function.region` | string | 函数区域 | `"us-central1"` |
| `gcp.cloud_function.runtime` | string | Runtime | `"python310"`, `"nodejs18"` |
| `gcp.cloud_function.entry_point` | string | 入口点 | `"hello_http"` |
| `gcp.cloud_function.generation` | string | 代数 | `"1"`, `"2"` |

### 5.2 触发器属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cloud Functions触发器类型:

HTTP触发器:
✅ faas.trigger = "http"
✅ http.method
✅ http.route

Pub/Sub触发器:
✅ faas.trigger = "pubsub"
✅ messaging.system = "gcp_pubsub"
✅ messaging.destination.name (Topic)

Cloud Storage触发器:
✅ faas.trigger = "datasource"
✅ gcp.cloud_function.trigger.bucket
✅ gcp.cloud_function.trigger.event_type

Firestore触发器:
✅ faas.trigger = "datasource"
✅ gcp.cloud_function.trigger.resource

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 6. Cloud Run属性

### 6.1 容器属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cloud Run Resource属性:

必需:
✅ cloud.provider = "gcp"
✅ cloud.platform = "gcp_cloud_run"
✅ cloud.region
✅ service.name
✅ service.instance.id

推荐:
📋 gcp.cloud_run.service.name
📋 gcp.cloud_run.revision.name
📋 gcp.cloud_run.configuration.name
📋 gcp.project.id

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `gcp.cloud_run.service.name` | string | Cloud Run服务名称 | `"my-service"` |
| `gcp.cloud_run.revision.name` | string | Revision名称 | `"my-service-00001"` |
| `gcp.cloud_run.configuration.name` | string | Configuration名称 | `"my-service"` |
| `gcp.cloud_run.job.name` | string | Job名称 | `"my-job"` |
| `gcp.cloud_run.job.execution` | string | Job执行ID | `"my-job-00001"` |

### 6.2 服务属性

```go
func DetectCloudRun(ctx context.Context) (*resource.Resource, error) {
    // Cloud Run环境变量
    serviceName := os.Getenv("K_SERVICE")
    revision := os.Getenv("K_REVISION")
    configuration := os.Getenv("K_CONFIGURATION")
    
    if serviceName == "" {
        return nil, errors.New("not running in Cloud Run")
    }
    
    attrs := []attribute.KeyValue{
        semconv.CloudProviderGCP,
        semconv.CloudPlatformKey.String("gcp_cloud_run"),
        semconv.ServiceNameKey.String(serviceName),
        attribute.String("gcp.cloud_run.service.name", serviceName),
    }
    
    if revision != "" {
        attrs = append(attrs,
            attribute.String("gcp.cloud_run.revision.name", revision))
    }
    
    if configuration != "" {
        attrs = append(attrs,
            attribute.String("gcp.cloud_run.configuration.name", 
                configuration))
    }
    
    // 从GCP Metadata获取项目和区域
    if projectID, err := gcpMetadataRequest(ctx, http.DefaultClient,
        "project/project-id"); err == nil {
        attrs = append(attrs,
            semconv.CloudAccountIDKey.String(projectID),
            attribute.String("gcp.project.id", projectID))
    }
    
    // Cloud Run的region从GOOGLE_CLOUD_REGION环境变量获取
    if region := os.Getenv("GOOGLE_CLOUD_REGION"); region != "" {
        attrs = append(attrs,
            semconv.CloudRegionKey.String(region))
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}
```

---

## 7. App Engine属性

### 7.1 应用属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

App Engine Resource属性:

必需:
✅ cloud.provider = "gcp"
✅ cloud.platform = "gcp_app_engine"
✅ cloud.region
✅ faas.name (服务名称)

推荐:
📋 faas.version (版本)
📋 faas.instance (实例ID)
📋 gcp.app_engine.service.name
📋 gcp.app_engine.version.id
📋 gcp.app_engine.instance.id
📋 gcp.project.id

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `gcp.app_engine.service.name` | string | 服务名称 | `"default"`, `"api"` |
| `gcp.app_engine.version.id` | string | 版本ID | `"20230101t123456"` |
| `gcp.app_engine.instance.id` | string | 实例ID | `"abc123"` |
| `gcp.app_engine.runtime` | string | Runtime | `"python39"`, `"go116"` |

### 7.2 版本与实例

```python
def detect_app_engine() -> Resource:
    """检测App Engine环境"""
    # App Engine特有环境变量
    service_name = os.getenv("GAE_SERVICE")
    version_id = os.getenv("GAE_VERSION")
    instance_id = os.getenv("GAE_INSTANCE")
    
    if not service_name:
        return Resource.empty()
    
    attributes = {
        ResourceAttributes.CLOUD_PROVIDER: CloudProviderValues.GCP.value,
        ResourceAttributes.CLOUD_PLATFORM: CloudPlatformValues.GCP_APP_ENGINE.value,
        ResourceAttributes.FAAS_NAME: service_name,
        "gcp.app_engine.service.name": service_name,
    }
    
    if version_id:
        attributes[ResourceAttributes.FAAS_VERSION] = version_id
        attributes["gcp.app_engine.version.id"] = version_id
    
    if instance_id:
        attributes[ResourceAttributes.FAAS_INSTANCE] = instance_id
        attributes["gcp.app_engine.instance.id"] = instance_id
    
    # 项目ID
    if project_id := os.getenv("GOOGLE_CLOUD_PROJECT"):
        attributes[ResourceAttributes.CLOUD_ACCOUNT_ID] = project_id
        attributes["gcp.project.id"] = project_id
    
    # Region
    if region := os.getenv("GAE_ENV"):
        # GAE_ENV: "standard" or "flex"
        # 需要从其他来源获取实际region
        pass
    
    return Resource.create(attributes)
```

---

## 8. Go实现示例

### 8.1 GCE检测

(已在3.2节提供)

### 8.2 GKE检测

(已在4.2节提供)

### 8.3 Cloud Functions检测

```go
func DetectCloudFunctions(ctx context.Context) (*resource.Resource, error) {
    // Cloud Functions环境变量
    functionName := os.Getenv("FUNCTION_NAME")
    if functionName == "" {
        // 尝试Gen2环境变量
        functionName = os.Getenv("K_SERVICE")
    }
    
    if functionName == "" {
        return nil, errors.New("not running in Cloud Functions")
    }
    
    attrs := []attribute.KeyValue{
        semconv.CloudProviderGCP,
        semconv.CloudPlatformGCPCloudFunctions,
        semconv.FaaSNameKey.String(functionName),
        attribute.String("gcp.cloud_function.name", functionName),
    }
    
    // Region
    if region := os.Getenv("FUNCTION_REGION"); region != "" {
        attrs = append(attrs, semconv.CloudRegionKey.String(region))
        attrs = append(attrs, 
            attribute.String("gcp.cloud_function.region", region))
    }
    
    // 项目ID
    if projectID, err := gcpMetadataRequest(ctx, http.DefaultClient,
        "project/project-id"); err == nil {
        attrs = append(attrs,
            semconv.CloudAccountIDKey.String(projectID),
            attribute.String("gcp.project.id", projectID))
    }
    
    // Runtime
    if runtime := os.Getenv("FUNCTION_RUNTIME"); runtime != "" {
        attrs = append(attrs,
            attribute.String("gcp.cloud_function.runtime", runtime))
    }
    
    // Gen1 vs Gen2
    if os.Getenv("K_SERVICE") != "" {
        attrs = append(attrs,
            attribute.String("gcp.cloud_function.generation", "2"))
    } else {
        attrs = append(attrs,
            attribute.String("gcp.cloud_function.generation", "1"))
    }
    
    return resource.NewWithAttributes(semconv.SchemaURL, attrs...), nil
}
```

---

## 9. Python实现示例

### 9.1 通用GCP检测

```python
import os
import requests
from opentelemetry.sdk.resources import Resource
from opentelemetry.semconv.resource import (
    CloudProviderValues,
    CloudPlatformValues,
    ResourceAttributes
)

GCP_METADATA_ENDPOINT = "http://metadata.google.internal/computeMetadata/v1"

def detect_gce() -> Resource:
    """检测GCE环境"""
    try:
        # 请求GCP Metadata Server
        response = requests.get(
            f"{GCP_METADATA_ENDPOINT}/instance/id",
            headers={"Metadata-Flavor": "Google"},
            timeout=2
        )
        response.raise_for_status()
        
        instance_id = response.text
        
        # 获取其他元数据
        instance_name = gcp_metadata_request("instance/name")
        machine_type = gcp_metadata_request("instance/machine-type")
        zone = gcp_metadata_request("instance/zone")
        project_id = gcp_metadata_request("project/project-id")
        
        # 提取简短名称
        machine_type = machine_type.split("/")[-1] if machine_type else ""
        zone = zone.split("/")[-1] if zone else ""
        region = "-".join(zone.split("-")[:-1]) if zone else ""
        
        attributes = {
            ResourceAttributes.CLOUD_PROVIDER: CloudProviderValues.GCP.value,
            ResourceAttributes.CLOUD_PLATFORM: CloudPlatformValues.GCP_COMPUTE_ENGINE.value,
            ResourceAttributes.CLOUD_REGION: region,
            ResourceAttributes.CLOUD_AVAILABILITY_ZONE: zone,
            ResourceAttributes.CLOUD_ACCOUNT_ID: project_id,
            ResourceAttributes.HOST_ID: instance_id,
            ResourceAttributes.HOST_NAME: instance_name,
            ResourceAttributes.HOST_TYPE: machine_type,
            "gcp.gce.instance.id": instance_id,
            "gcp.gce.instance.name": instance_name,
            "gcp.gce.machine.type": machine_type,
            "gcp.project.id": project_id,
        }
        
        return Resource.create(attributes)
        
    except Exception:
        return Resource.empty()

def gcp_metadata_request(path: str) -> str:
    """请求GCP Metadata"""
    try:
        response = requests.get(
            f"{GCP_METADATA_ENDPOINT}/{path}",
            headers={"Metadata-Flavor": "Google"},
            timeout=1
        )
        return response.text if response.ok else ""
    except Exception:
        return ""

def detect_cloud_functions() -> Resource:
    """检测Cloud Functions环境"""
    function_name = os.getenv("FUNCTION_NAME") or os.getenv("K_SERVICE")
    
    if not function_name:
        return Resource.empty()
    
    attributes = {
        ResourceAttributes.CLOUD_PROVIDER: CloudProviderValues.GCP.value,
        ResourceAttributes.CLOUD_PLATFORM: CloudPlatformValues.GCP_CLOUD_FUNCTIONS.value,
        ResourceAttributes.FAAS_NAME: function_name,
        "gcp.cloud_function.name": function_name,
    }
    
    # Region
    if region := os.getenv("FUNCTION_REGION"):
        attributes[ResourceAttributes.CLOUD_REGION] = region
        attributes["gcp.cloud_function.region"] = region
    
    # 项目ID
    project_id = os.getenv("GCP_PROJECT") or gcp_metadata_request("project/project-id")
    if project_id:
        attributes[ResourceAttributes.CLOUD_ACCOUNT_ID] = project_id
        attributes["gcp.project.id"] = project_id
    
    # Generation
    generation = "2" if os.getenv("K_SERVICE") else "1"
    attributes["gcp.cloud_function.generation"] = generation
    
    return Resource.create(attributes)
```

### 9.2 Cloud Run检测

(已在6.2节Go示例中提供，Python实现类似)

---

## 10. 后端集成

### 10.1 Cloud Trace集成

```yaml
# OpenTelemetry Collector配置
exporters:
  googlecloud:
    project: ${GCP_PROJECT_ID}
    # 使用默认凭据
    # use_default_credentials: true
    
    # 或使用服务账号
    # credentials_file: /path/to/key.json
    
    # Trace配置
    trace:
      endpoint: cloudtrace.googleapis.com:443
      use_insecure: false
      
    # Metric配置
    metric:
      endpoint: monitoring.googleapis.com:443
      use_insecure: false
      
    # 资源映射
    resource_mappings:
      - source_type: gce_instance
        target_type: gce_instance
      - source_type: k8s_cluster
        target_type: k8s_cluster

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, resource]
      exporters: [googlecloud]
    
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [googlecloud]
```

### 10.2 Cloud Monitoring集成

```go
// Google Cloud Trace Exporter
import (
    texporter "github.com/GoogleCloudPlatform/opentelemetry-operations-go/exporter/trace"
    "go.opentelemetry.io/otel/sdk/trace"
)

func InitCloudTrace(ctx context.Context, projectID string) (*trace.TracerProvider, error) {
    // 创建Cloud Trace Exporter
    exporter, err := texporter.New(
        texporter.WithProjectID(projectID),
    )
    if err != nil {
        return nil, err
    }
    
    // 检测GCP资源
    gcpResource, _ := DetectGCP(ctx)
    
    // 创建TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithResource(gcpResource),
    )
    
    return tp, nil
}

func DetectGCP(ctx context.Context) (*resource.Resource, error) {
    // 尝试各种GCP环境
    
    // 1. Cloud Functions
    if res, err := DetectCloudFunctions(ctx); err == nil {
        return res, nil
    }
    
    // 2. Cloud Run
    if res, err := DetectCloudRun(ctx); err == nil {
        return res, nil
    }
    
    // 3. GKE
    if res, err := DetectGKE(ctx); err == nil {
        return res, nil
    }
    
    // 4. GCE
    if res, err := DetectGCE(ctx); err == nil {
        return res, nil
    }
    
    // 5. App Engine
    if res, err := DetectAppEngine(ctx); err == nil {
        return res, nil
    }
    
    return resource.Default(), nil
}
```

---

## 11. 最佳实践

### 11.1 属性命名规范

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

GCP属性命名规范:

1. 使用gcp前缀 ⭐⭐⭐⭐⭐
   gcp.gce.instance.id
   gcp.gke.cluster.name
   gcp.cloud_function.name

2. 遵循OpenTelemetry语义约定 ⭐⭐⭐⭐⭐
   cloud.provider = "gcp"
   cloud.platform = "gcp_compute_engine"
   cloud.region

3. 资源层次结构 ⭐⭐⭐⭐
   gcp.project.id
   gcp.project.number
   gcp.resource.type

4. 标签规范化 ⭐⭐⭐
   使用gcp.resource.labels

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 11.2 性能优化

```go
// Metadata缓存
var (
    gcpMetadataOnce  sync.Once
    gcpMetadataCache map[string]string
    gcpMetadataErr   error
)

func GetGCPMetadata(ctx context.Context) (map[string]string, error) {
    gcpMetadataOnce.Do(func() {
        ctx, cancel := context.WithTimeout(ctx, 2*time.Second)
        defer cancel()
        
        gcpMetadataCache = make(map[string]string)
        
        // 批量获取元数据
        paths := []string{
            "instance/id",
            "instance/name",
            "instance/machine-type",
            "instance/zone",
            "project/project-id",
        }
        
        for _, path := range paths {
            if value, err := gcpMetadataRequest(ctx, 
                http.DefaultClient, path); err == nil {
                gcpMetadataCache[path] = value
            }
        }
    })
    
    return gcpMetadataCache, gcpMetadataErr
}
```

### 11.3 成本优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Cloud Trace成本优化:

1. 采样策略 ⭐⭐⭐⭐⭐
   - 生产: 10-20%
   - 测试: 50%
   - 开发: 100%

2. Span数量控制 ⭐⭐⭐⭐
   - 每月前250万Span: 免费
   - 超出: $0.20/百万Span

3. Trace保留期 ⭐⭐⭐
   - 默认30天
   - 无法调整

4. 属性优化 ⭐⭐⭐
   - 限制属性数量
   - 避免高基数

Cloud Monitoring定价:
- 前50GB/月: 免费 (日志)
- 前150MB/月: 免费 (Metrics)
- 超出: 按量计费

成本监控:
- GCP Billing Console
- 设置预算告警
- 使用Cost Breakdown

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**GCP SDK版本**: Latest  
**适用场景**: GCP云原生应用、Kubernetes、Serverless

**关键特性**:

- ✅ GCE/GKE/Functions/Cloud Run/App Engine完整支持
- ✅ GCP Metadata Server自动检测
- ✅ Cloud Trace深度集成
- ✅ Cloud Monitoring原生支持
- ✅ Go/Python完整示例
- ✅ 成本优化策略
- ✅ Kubernetes原生优势

# Multi-Cloud and Hybrid Cloud Deployment

> **Document Version**: v2.0  
> **Last Updated**: 2025-10-15  
> **Related Documents**: [06-Deployment Architecture](./06-deployment-architecture.md), [19-Production Best Practices](./19-production-best-practices-2025.md)

---

## Table of Contents

- [1. Overview](#1-overview)
  - [1.1 Multi-Cloud Deployment Benefits](#11-multi-cloud-deployment-benefits)
  - [1.2 Deployment Scenarios](#12-deployment-scenarios)
- [2. Multi-Cloud Architecture Design](#2-multi-cloud-architecture-design)
- [3. Multi-Cloud Architecture Details](#3-multi-cloud-architecture-details)
  - [3.1 AWS Deployment](#31-aws-deployment)
  - [3.2 Azure Deployment](#32-azure-deployment)
  - [3.3 GCP Deployment](#33-gcp-deployment)
  - [3.4 Cross-Cloud Network Interconnection](#34-cross-cloud-network-interconnection)
- [4. Hybrid Cloud Architecture](#4-hybrid-cloud-architecture)
  - [4.1 Cloud + On-Premises Data Center Architecture](#41-cloud--on-premises-data-center-architecture)
  - [4.2 Hybrid Kubernetes Platforms](#42-hybrid-kubernetes-platforms)
  - [4.3 Data Synchronization Strategies](#43-data-synchronization-strategies)
  - [4.4 Unified Management and Monitoring](#44-unified-management-and-monitoring)
- [5. Data Synchronization Details](#5-data-synchronization-details)
  - [5.1 Cross-Region Replication](#51-cross-region-replication)
  - [5.2 Cross-Cloud Data Synchronization](#52-cross-cloud-data-synchronization)
  - [5.3 Consistency Models](#53-consistency-models)
  - [5.4 Conflict Resolution Strategies](#54-conflict-resolution-strategies)
- [6. Disaster Recovery](#6-disaster-recovery)
  - [6.1 Backup Strategies](#61-backup-strategies)
  - [6.2 Recovery Procedures and Runbooks](#62-recovery-procedures-and-runbooks)
  - [6.3 Failover Automation](#63-failover-automation)
  - [6.4 Disaster Recovery Drills](#64-disaster-recovery-drills)
- [7. Cost Optimization](#7-cost-optimization)
  - [7.1 Multi-Cloud Cost Comparison](#71-multi-cloud-cost-comparison)
  - [7.2 Spot Instance Strategies](#72-spot-instance-strategies)
  - [7.3 Reserved Capacity Planning](#73-reserved-capacity-planning)
  - [7.4 Cross-Cloud Load Balancing Cost Optimization](#74-cross-cloud-load-balancing-cost-optimization)
- [8. Best Practices](#8-best-practices)
- [Appendix](#appendix)

---

## 1. Overview

Multi-cloud and hybrid cloud deployments provide enterprises with higher flexibility, reliability, and cost-effectiveness. By deploying OpenTelemetry across multiple cloud platforms, unified observability across clouds can be achieved.

### 1.1 Multi-Cloud Deployment Benefits

**High Availability**:

- Cross-cloud disaster recovery eliminates single cloud provider dependency
- Multi-region deployment improves service availability
- Automatic failover ensures business continuity
- Distributed architecture reduces single point of failure risks

**Flexibility**:

- Choose the most suitable cloud services
- Avoid vendor lock-in
- Support gradual migration
- Flexible resource scheduling

**Cost Optimization**:

- Leverage pricing advantages of different clouds
- On-demand usage to avoid resource waste
- Intelligent sampling to reduce data transfer costs
- Tiered storage to optimize storage costs

**Compliance**:

- Data sovereignty requirements
- Geographic compliance
- Industry regulatory requirements
- Data privacy protection

### 1.2 Deployment Scenarios

**Scenario 1: Multi-Cloud Disaster Recovery**:

```text
AWS (Primary)    Azure (Backup)    GCP (Third)
     |                |                |
  [EKS]            [AKS]            [GKE]
     |                |                |
     +----------------+----------------+
                      |
              [Unified Data Platform]
```

**Scenario 2: Hybrid Cloud Migration**:

```text
[On-Premises DC] =====VPN/Direct Connect====> [Cloud]
   [Legacy Apps]                              [Containers]
   [VM Collector]                             [K8s Collector]
```

**Scenario 3: Cross-Region Deployment**:

```text
US-East       EU-West       AP-South
   |             |             |
[Collector]  [Collector]  [Collector]
   |             |             |
   +-------------+-------------+
                 |
          [Global Gateway]
```

---

## 2. Multi-Cloud Architecture Design

**Architecture Pattern**:

```text
+----------------------------------------+
|         Unified Control Plane          |
|      (OPAMP Control Plane)             |
+----------------------------------------+
       |           |           |
   +---+     +-----+     +-----+
   |AWS|     |Azure|     |GCP |
   +---+     +-----+     +-----+
       |           |           |
   +---+-----------+-----------+---+
   |   Unified Data Aggregation      |
   |   (Central Data Aggregation)   |
   +--------------------------------+
```

---

## 3. Multi-Cloud Architecture Details

### 3.1 AWS Deployment

AWS provides comprehensive container and serverless services, supporting flexible OpenTelemetry deployment options.

#### 3.1.1 EKS (Elastic Kubernetes Service) Deployment

EKS is AWS managed Kubernetes service, suitable for large-scale OTLP deployments.

**Architecture Diagram**:

```text
EKS Cluster
+----------------------------------------+
| Node 1    | Node 2    | Gateway Tier    |
| [Agent]   | [Agent]   | [Gateway]       |
| [App]     | [App]     | [Gateway]       |
+----------------------------------------+
       |           |           |
   [CloudWatch] [X-Ray] [S3] [MSK/Kafka]
```

**Complete Deployment Configuration**:

```yaml
# 1. Namespace and RBAC
apiVersion: v1
kind: Namespace
metadata:
  name: observability
  labels:
    app.kubernetes.io/name: observability

---
# 2. ServiceAccount with IRSA
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability
  annotations:
    eks.amazonaws.com/role-arn: arn:aws:iam::123456789012:role/OTelCollectorRole

---
# 3. ConfigMap - Agent Configuration
apiVersion: v1
kind: ConfigMap
metadata:
  name: otel-agent-config
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
      hostmetrics:
        collection_interval: 30s
        scrapers:
          cpu:
          memory:
          disk:
      kubeletstats:
        collection_interval: 30s
        endpoint: ${K8S_NODE_IP}:10250
        insecure_skip_verify: true
    
    processors:
      batch:
        timeout: 1s
        send_batch_size: 1024
      memory_limiter:
        limit_mib: 512
        spike_limit_mib: 128
      resource:
        attributes:
          - key: cloud.provider
            value: aws
            action: upsert
          - key: cloud.platform
            value: aws_eks
            action: upsert
      k8sattributes:
        auth_type: serviceAccount
        extract:
          metadata:
            - k8s.pod.name
            - k8s.namespace.name
            - k8s.node.name
    
    exporters:
      otlp/gateway:
        endpoint: otel-gateway.observability.svc.cluster.local:4317
        compression: gzip
        sending_queue:
          enabled: true
          num_consumers: 4
          queue_size: 1000
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp/gateway]
        metrics:
          receivers: [otlp, hostmetrics, kubeletstats]
          processors: [memory_limiter, k8sattributes, resource, batch]
          exporters: [otlp/gateway]

---
# 4. DaemonSet for Agent
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
        command:
          - /otelcol-contrib
          - --config=/etc/otel/config.yaml
        env:
        - name: AWS_REGION
          value: us-east-1
        - name: CLUSTER_NAME
          value: production-eks
        - name: K8S_NODE_IP
          valueFrom:
            fieldRef:
              fieldPath: status.hostIP
        volumeMounts:
        - name: otel-config
          mountPath: /etc/otel
        resources:
          requests:
            cpu: 200m
            memory: 256Mi
          limits:
            cpu: 500m
            memory: 512Mi
        livenessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 10
          periodSeconds: 30
      volumes:
      - name: otel-config
        configMap:
          name: otel-agent-config

---
# 5. Gateway Deployment with AWS Exporters
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
    spec:
      serviceAccountName: otel-collector
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
                  - otel-gateway
              topologyKey: kubernetes.io/hostname
      containers:
      - name: otel-gateway
        image: otel/opentelemetry-collector-contrib:0.90.0
        args:
          - --config=/etc/otel/gateway-config.yaml
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        resources:
          requests:
            cpu: 1000m
            memory: 2Gi
          limits:
            cpu: 2000m
            memory: 4Gi

---
# 6. Service for Gateway
apiVersion: v1
kind: Service
metadata:
  name: otel-gateway
  namespace: observability
spec:
  type: ClusterIP
  ports:
  - port: 4317
    targetPort: 4317
    name: otlp-grpc
  - port: 4318
    targetPort: 4318
    name: otlp-http
  selector:
    app: otel-gateway

---
# 7. HorizontalPodAutoscaler
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-gateway-hpa
  namespace: observability
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: otel-gateway
  minReplicas: 3
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  behavior:
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 100
        periodSeconds: 60
```

#### 3.1.2 ECS (Elastic Container Service) Deployment

ECS is suitable for workloads that do not require Kubernetes complexity.

```json
{
  "family": "otel-collector",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "1024",
  "memory": "2048",
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole",
  "taskRoleArn": "arn:aws:iam::123456789012:role/OTelCollectorTaskRole",
  "containerDefinitions": [
    {
      "name": "otel-collector",
      "image": "otel/opentelemetry-collector-contrib:0.90.0",
      "essential": true,
      "command": ["--config=/etc/otel/config.yaml"],
      "environment": [
        {"name": "AWS_REGION", "value": "us-east-1"}
      ],
      "portMappings": [
        {"containerPort": 4317, "protocol": "tcp", "name": "otlp-grpc"},
        {"containerPort": 4318, "protocol": "tcp", "name": "otlp-http"},
        {"containerPort": 13133, "protocol": "tcp", "name": "health"}
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/otel-collector",
          "awslogs-region": "us-east-1",
          "awslogs-stream-prefix": "otel"
        }
      },
      "healthCheck": {
        "command": ["CMD-SHELL", "curl -f http://localhost:13133/ || exit 1"],
        "interval": 30,
        "timeout": 5,
        "retries": 3
      }
    }
  ]
}
```

#### 3.1.3 AWS Lambda Integration

Lambda functions can integrate via OTLP direct export or Layer approach.

**Go Lambda Code Example**:

```go
package main

import (
    "context"
    "os"
    
    "github.com/aws/aws-lambda-go/lambda"
    "github.com/aws/aws-lambda-go/events"
    "go.opentelemetry.io/contrib/instrumentation/github.com/aws/aws-lambda-go/otellambda"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

var tracer trace.Tracer

func init() {
    ctx := context.Background()
    
    res, _ := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("lambda-order-processor"),
            semconv.ServiceVersion("1.0.0"),
            semconv.CloudProviderAWS,
            semconv.CloudPlatformAWSLambda,
            attribute.String("deployment.environment", os.Getenv("STAGE")),
        ),
    )
    
    endpoint := os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT")
    if endpoint == "" {
        endpoint = "localhost:4317"
    }
    
    conn, _ := grpc.Dial(endpoint,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
    )
    
    exporter, _ := otlptracegrpc.New(ctx, otlptracegrpc.WithGRPCConn(conn))
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithResource(res),
        sdktrace.WithBatcher(exporter),
        sdktrace.WithSampler(sdktrace.ParentBased(sdktrace.TraceIDRatioBased(0.1))),
    )
    otel.SetTracerProvider(tp)
    tracer = tp.Tracer("lambda-order-processor")
}

func handleRequest(ctx context.Context, event events.APIGatewayProxyRequest) (events.APIGatewayProxyResponse, error) {
    ctx, span := tracer.Start(ctx, "process-order")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", event.PathParameters["orderId"]),
        attribute.String("http.method", event.HTTPMethod),
    )
    
    return events.APIGatewayProxyResponse{
        StatusCode: 200,
        Body:       `{"status": "success"}`,
    }, nil
}

func main() {
    lambda.Start(otellambda.InstrumentHandler(handleRequest))
}
```

#### 3.1.4 AWS S3 Archive Storage

Using S3 for long-term data archiving:

```yaml
exporters:
  awss3:
    region: us-east-1
    s3_bucket: otel-traces-archive
    s3_prefix: traces/
    s3_partition: hour
    compression: gzip
    marshaler: otlp_json
    
  awscloudwatchlogs:
    log_group_name: /aws/otel/traces
    log_stream_name: otel-collector
    region: us-east-1
    log_retention: 90
    
  awscloudwatch:
    namespace: OTLP/Metrics
    region: us-east-1
    
  awsxray:
    region: us-east-1
    index_all_attributes: true
```

---

### 3.2 Azure Deployment

Azure provides AKS, Container Instances, and Functions deployment options.

#### 3.2.1 AKS (Azure Kubernetes Service) Deployment

**Architecture Diagram**:

```text
AKS Cluster
+-------------------+-------------------+
| Node Pool 1       | Node Pool 2       |
| System            | User Apps         |
+-------------------+-------------------+
         |                   |
    [Agent DaemonSet]  [Gateway Deployment]
         |                   |
    [Azure Monitor]    [Service Bus]
    [App Insights]     [Event Hub]
                       [Blob Storage]
```

**Terraform Deployment Configuration**:

```hcl
# main.tf - AKS with OTel Collector
terraform {
  required_providers {
    azurerm = {
      source  = "hashicorp/azurerm"
      version = "~> 3.0"
    }
  }
}

provider "azurerm" {
  features {}
}

# Resource Group
resource "azurerm_resource_group" "otel" {
  name     = "rg-otel-multicloud"
  location = "eastus"
  
  tags = {
    environment = "production"
    project     = "otlp-multicloud"
  }
}

# Log Analytics Workspace
resource "azurerm_log_analytics_workspace" "otel" {
  name                = "law-otel-multicloud"
  location            = azurerm_resource_group.otel.location
  resource_group_name = azurerm_resource_group.otel.name
  sku                 = "PerGB2018"
  retention_in_days   = 90
}

# AKS Cluster
resource "azurerm_kubernetes_cluster" "otel" {
  name                = "aks-otel-multicloud"
  location            = azurerm_resource_group.otel.location
  resource_group_name = azurerm_resource_group.otel.name
  dns_prefix          = "otelmc"
  kubernetes_version  = "1.28"

  default_node_pool {
    name                = "system"
    node_count          = 3
    vm_size             = "Standard_D4s_v3"
    enable_auto_scaling = true
    min_count           = 3
    max_count           = 10
  }

  identity {
    type = "SystemAssigned"
  }

  oms_agent {
    log_analytics_workspace_id = azurerm_log_analytics_workspace.otel.id
  }
}

# Application Insights
resource "azurerm_application_insights" "otel" {
  name                = "ai-otel-multicloud"
  location            = azurerm_resource_group.otel.location
  resource_group_name = azurerm_resource_group.otel.name
  application_type    = "web"
}

# Storage Account for OTel Data
resource "azurerm_storage_account" "otel" {
  name                     = "saotelmulticloud"
  resource_group_name      = azurerm_resource_group.otel.name
  location                 = azurerm_resource_group.otel.location
  account_tier             = "Standard"
  account_replication_type = "GRS"
  
  lifecycle_rule {
    name    = "archive-old-logs"
    enabled = true
    
    actions {
      base_blob {
        tier_to_cool_after_days_since_modification_greater_than    = 30
        tier_to_archive_after_days_since_modification_greater_than = 90
        delete_after_days_since_modification_greater_than          = 365
      }
    }
  }
}
```

#### 3.2.2 Azure Monitor Integration Configuration

```yaml
exporters:
  azuremonitor:
    instrumentation_key: ${APPLICATIONINSIGHTS_INSTRUMENTATION_KEY}
    endpoint: https://dc.services.visualstudio.com/v2/track
    maxbatchsize: 100
    maxbatchinterval: 10s
    
  azureloganalytics:
    workspace_id: ${WORKSPACE_ID}
    workspace_key: ${WORKSPACE_KEY}
    log_type: OTelTraces
    
  azureblob:
    connection_string: ${STORAGE_CONNECTION_STRING}
    container_name: otel-traces
    blob_prefix: "year=%Y/month=%m/day=%d/"
    encoding: gzip
```

---

### 3.3 GCP Deployment

Google Cloud Platform provides GKE, Cloud Run, and Cloud Functions deployment options.

#### 3.3.1 GKE (Google Kubernetes Engine) Deployment

**Architecture Diagram**:

```text
GKE Cluster
+-------------------+-------------------+
| Standard Nodes    | Spot Nodes        |
| [Agent Pod]       | [Batch Collector] |
| [App Pod]         |                   |
+-------------------+-------------------+
         |
    [Gateway Tier]
    [Autopilot]
         |
    [Cloud Trace]  [Cloud Monitoring]
    [Cloud Storage] [Pub/Sub]
                         |
                    [BigQuery]
```

**GKE Deployment YAML**:

```yaml
# 1. ServiceAccount with Workload Identity
apiVersion: v1
kind: ServiceAccount
metadata:
  name: otel-collector
  namespace: observability
  annotations:
    iam.gke.io/gcp-service-account: otel-collector@my-project.iam.gserviceaccount.com

---
# 2. ConfigMap
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
        timeout: 1s
        send_batch_size: 1024
      resource:
        attributes:
          - key: cloud.provider
            value: gcp
            action: upsert
          - key: cloud.platform
            value: gcp_gke
            action: upsert
    
    exporters:
      googlecloud:
        project: ${GCP_PROJECT}
        trace:
          endpoint: cloudtrace.googleapis.com:443
        metric:
          endpoint: monitoring.googleapis.com:443
          prefix: custom.googleapis.com/otel
      
      googlecloudstorage:
        project: ${GCP_PROJECT}
        bucket: otel-traces-archive
        prefix: traces/
        compression: gzip
    
    service:
      pipelines:
        traces:
          receivers: [otlp]
          processors: [resource, batch]
          exporters: [googlecloud]

---
# 3. Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: observability
spec:
  replicas: 3
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
          - --config=/etc/otel/config.yaml
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        env:
        - name: GCP_PROJECT
          value: "my-gcp-project"
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
          name: otel-collector-config
```

#### 3.3.2 Cloud Run Deployment

```yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: otel-collector
  annotations:
    run.googleapis.com/ingress: all
    run.googleapis.com/execution-environment: gen2
spec:
  template:
    metadata:
      annotations:
        autoscaling.knative.dev/minScale: "1"
        autoscaling.knative.dev/maxScale: "10"
        run.googleapis.com/cpu-throttling: "false"
        run.googleapis.com/timeout: "300"
        run.googleapis.com/memory: "4Gi"
        run.googleapis.com/cpu: "2"
    spec:
      containerConcurrency: 1000
      timeoutSeconds: 300
      serviceAccountName: otel-collector@my-project.iam.gserviceaccount.com
      containers:
      - image: otel/opentelemetry-collector-contrib:0.90.0
        ports:
        - containerPort: 4317
          name: otlp-grpc
        - containerPort: 4318
          name: otlp-http
        env:
        - name: GCP_PROJECT
          value: "my-project"
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "cloud.provider=gcp,cloud.platform=gcp_cloud_run"
        resources:
          limits:
            cpu: "2"
            memory: "4Gi"
```

#### 3.3.3 GCP Services Integration Configuration

```yaml
exporters:
  googlecloud:
    project: my-project
    trace:
      endpoint: cloudtrace.googleapis.com:443
      attribute_mappings:
        - key: service.name
          value: service_name
    metric:
      endpoint: monitoring.googleapis.com:443
      prefix: custom.googleapis.com/otel
    log:
      default_log_name: otel-logs
      
  googlecloudstorage:
    project: my-project
    bucket: otel-traces-archive
    prefix: "traces/"
    compression: gzip
    
  googlecloudpubsub:
    project: my-project
    topic: otel-traces-topic
    compression: gzip
```

---

### 3.4 Cross-Cloud Network Interconnection

The key to multi-cloud deployment is establishing secure, high-performance network interconnections.

#### 3.4.1 Network Architecture Diagram

```text
On-Premises DC
     |
  [Router]
     |
  +--+-----+-----+-----+
  |        |     |     |
VPN    Direct Express Cloud
       Connect  Route  Interconnect
  |        |     |     |
  +--------+-----+-----+
           |
    +------+------+
    |             |
[AWS VPC]    [Azure VNet]
    |             |
  [EKS]         [AKS]
    |
[GCP VPC]
    |
  [GKE]
```

#### 3.4.2 AWS Direct Connect Configuration

```hcl
# AWS Direct Connect Configuration
resource "aws_dx_gateway" "multicloud" {
  name            = "multicloud-dx-gateway"
  amazon_side_asn = "64512"
}

resource "aws_dx_connection" "main" {
  name      = "main-direct-connect"
  location  = "EqDC2"
  bandwidth = "10Gbps"
}

resource "aws_dx_private_virtual_interface" "main" {
  connection_id    = aws_dx_connection.main.id
  name             = "multicloud-vif"
  vlan             = 4094
  address_family   = "ipv4"
  bgp_asn          = 65352
  amazon_address   = "169.254.0.1/30"
  customer_address = "169.254.0.2/30"
  dx_gateway_id    = aws_dx_gateway.multicloud.id
}

# VPC Association
resource "aws_dx_gateway_association" "main" {
  dx_gateway_id         = aws_dx_gateway.multicloud.id
  associated_gateway_id = aws_vpn_gateway.main.id
  allowed_prefixes      = ["10.0.0.0/8"]
}
```

#### 3.4.3 Azure ExpressRoute Configuration

```hcl
# Azure ExpressRoute Configuration
resource "azurerm_express_route_circuit" "main" {
  name                  = "multicloud-expressroute"
  resource_group_name   = azurerm_resource_group.network.name
  location              = azurerm_resource_group.network.location
  service_provider_name = "Equinix"
  peering_location      = "Washington DC"
  bandwidth_in_mbps     = 10000

  sku {
    tier   = "Premium"
    family = "MeteredData"
  }
}

resource "azurerm_express_route_circuit_peering" "private" {
  peering_type                  = "AzurePrivatePeering"
  express_route_circuit_name    = azurerm_express_route_circuit.main.name
  resource_group_name           = azurerm_resource_group.network.name
  peer_asn                      = 65352
  primary_peer_address_prefix   = "192.168.100.0/30"
  secondary_peer_address_prefix = "192.168.100.4/30"
  vlan_id                       = 300
}
```

#### 3.4.4 GCP Cloud Interconnect Configuration

```hcl
# GCP Cloud Interconnect Configuration
resource "google_compute_interconnect_attachment" "main" {
  name                     = "multicloud-interconnect"
  router                   = google_compute_router.main.id
  region                   = "us-central1"
  type                     = "DEDICATED"
  bandwidth                = "BPS_10G"
  vlan_tag8021q            = 1000
  interconnect             = "https://www.googleapis.com/compute/v1/projects/my-project/global/interconnects/my-interconnect"
  
  candidate_subnets = [
    "169.254.100.0/29",
  ]
}

resource "google_compute_router" "main" {
  name    = "multicloud-router"
  network = google_compute_network.main.name
  region  = "us-central1"
  
  bgp {
    asn            = 65352
    advertise_mode = "CUSTOM"
    advertised_groups = ["ALL_SUBNETS"]
    
    advertised_ip_ranges {
      range = "10.0.0.0/8"
    }
  }
}
```

#### 3.4.5 Cross-Cloud VPN Backup Configuration

```yaml
# OpenTelemetry Collector with cross-cloud failover
exporters:
  otlp/aws-primary:
    endpoint: otel-gateway.aws.example.com:4317
    tls:
      insecure: false
      ca_file: /etc/certs/aws-ca.crt
    headers:
      x-cloud-provider: aws
    
  otlp/azure-secondary:
    endpoint: otel-gateway.azure.example.com:4317
    tls:
      insecure: false
      ca_file: /etc/certs/azure-ca.crt
    headers:
      x-cloud-provider: azure
    
  otlp/gcp-tertiary:
    endpoint: otel-gateway.gcp.example.com:4317
    tls:
      insecure: false
      ca_file: /etc/certs/gcp-ca.crt
    headers:
      x-cloud-provider: gcp
    
  file/backup:
    path: /var/otel/backup
    rotation:
      max_megabytes: 100
      max_days: 7
      max_backups: 5
      compress: true

processors:
  routing:
    default_exporters: [otlp/aws-primary]
    from_attribute: cloud.provider
    table:
      - value: aws
        exporters: [otlp/aws-primary]
      - value: azure
        exporters: [otlp/azure-secondary]
      - value: gcp
        exporters: [otlp/gcp-tertiary]
      - value: failover
        exporters: [file/backup, otlp/azure-secondary]

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [routing, batch]
      exporters: [otlp/aws-primary, otlp/azure-secondary, otlp/gcp-tertiary]
```

---

## 4. Hybrid Cloud Architecture

Hybrid cloud architecture combines the advantages of on-premises data centers and public clouds, providing enterprises with more flexible deployment options.

### 4.1 Cloud + On-Premises Data Center Architecture

#### 4.1.1 Architecture Diagram

```text
On-Premises DC
+-------------------+
| Legacy Systems    |
| [Legacy App A]    |
| [Legacy App B]    |
| [Database]        |
+-------------------+
         |
+--------v--------+
| Collection Layer|
| [Agent Mode]    |
| [Gateway Mode]  |
+--------+--------+
         |
    VPN / SD-WAN
         |
+--------v--------+
| Cloud Gateway   |
| [OTel Gateway]  |
+--------+--------+
         |
+----------------+
| Cloud Services |
| [Backend]      |
| [Storage]      |
| [Analytics]    |
+----------------+
```

#### 4.1.2 Hybrid Cloud Deployment Mode

**Edge Collection Mode**:

```yaml
# On-premises edge collection configuration
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
  
  hostmetrics:
    collection_interval: 30s
    scrapers:
      cpu:
      memory:
      disk:
      network:
      processes:
  
  snmp:
    endpoint: udp://192.168.1.1:161
    version: v3
    security_level: auth_priv
    user: otel_monitor
    
  syslog:
    tcp:
      listen_address: "0.0.0.0:54526"
    protocol: rfc3164

processors:
  batch:
    timeout: 5s
    send_batch_size: 1024

exporters:
  prometheusremotewrite/local:
    endpoint: http://prometheus.local:9090/api/v1/write
    
  elasticsearch/local:
    endpoints: ["https://elasticsearch.local:9200"]
    user: otel
    password: ${ES_PASSWORD}
    index: otel-traces
    
  otlp/cloud:
    endpoint: otel-gateway.cloud.example.com:4317
    tls:
      insecure: false
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key
      ca_file: /etc/certs/ca.crt
    compression: gzip
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
    
  file/backup:
    path: /var/otel/backup/traces
    rotation:
      max_megabytes: 100
      max_days: 7
      max_backups: 10
      compress: true

service:
  pipelines:
    traces:
      receivers: [otlp, syslog]
      processors: [batch]
      exporters: [elasticsearch/local, otlp/cloud, file/backup]
    metrics:
      receivers: [otlp, hostmetrics, snmp]
      processors: [batch]
      exporters: [prometheusremotewrite/local, otlp/cloud]
```

---

### 4.2 Hybrid Kubernetes Platforms

#### 4.2.1 Anthos Deployment

Google Anthos provides consistent Kubernetes experience across on-premises and cloud.

```yaml
# anthos-config.yaml - Anthos cluster OTel configuration
apiVersion: hub.gke.io/v1
kind: Membership
metadata:
  name: onprem-anthos-cluster
spec:
  endpoint:
    gkeCluster:
      resourceLink: //container.googleapis.com/projects/my-project/locations/us-central1/clusters/onprem-cluster

---
# Anthos Config Management - OTel Deployment
apiVersion: configmanagement.gke.io/v1
kind: ConfigManagement
metadata:
  name: config-management
spec:
  policyController:
    enabled: true
    templateLibraryInstalled: true
  configSync:
    enabled: true
    sourceFormat: unstructured
    git:
      syncRepo: https://github.com/my-org/anthos-otel-config
      syncBranch: main

---
# Anthos OTel Collector Deployment
apiVersion: apps/v1
kind: Deployment
metadata:
  name: anthos-otel-collector
  namespace: observability
spec:
  replicas: 3
  selector:
    matchLabels:
      app: anthos-otel-collector
  template:
    metadata:
      labels:
        app: anthos-otel-collector
        anthos.cloud.google.com/managed: "true"
    spec:
      affinity:
        nodeAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
            nodeSelectorTerms:
            - matchExpressions:
              - key: anthos.cloud.google.com/membership
                operator: In
                values:
                - onprem-anthos-cluster
      containers:
      - name: otel-collector
        image: gcr.io/my-project/otel-collector-anthos:latest
        env:
        - name: ANTHOS_LOCATION
          value: "onprem"
        - name: GCP_PROJECT
          value: "my-project"
        resources:
          requests:
            cpu: 500m
            memory: 1Gi
          limits:
            cpu: 2000m
            memory: 4Gi
```

#### 4.2.2 EKS Anywhere Deployment

AWS EKS Anywhere allows running AWS managed Kubernetes on-premises.

```yaml
# eksa-cluster.yaml
apiVersion: anywhere.eks.amazonaws.com/v1alpha1
kind: Cluster
metadata:
  name: onprem-eksa
spec:
  clusterNetwork:
    cniConfig:
      cilium: {}
    pods:
      cidrBlocks:
      - 192.168.0.0/16
    services:
      cidrBlocks:
      - 10.96.0.0/12
  controlPlaneConfiguration:
    count: 3
    endpoint:
      host: "192.168.1.100"
    machineGroupRef:
      kind: VSphereMachineConfig
      name: onprem-cp
  datacenterRef:
    kind: VSphereDatacenterConfig
    name: onprem-dc
  kubernetesVersion: "1.28"
  workerNodeGroupConfigurations:
  - count: 5
    machineGroupRef:
      kind: VSphereMachineConfig
      name: onprem-worker
    name: md-0

---
# EKS Anywhere OTel Collector
apiVersion: packages.eks.amazonaws.com/v1alpha1
kind: Package
metadata:
  name: otel-collector
  namespace: observability
spec:
  packageName: otel-collector
  config: |
    mode: deployment
    replicaCount: 3
    resources:
      limits:
        cpu: 2000m
        memory: 4Gi
      requests:
        cpu: 1000m
        memory: 2Gi
```

#### 4.2.3 Azure Stack HCI Deployment

```powershell
# Deploy OTel on Azure Stack HCI using AKS on HCI
New-AksHciCluster -Name onprem-aks `
    -nodePoolName otelpool `
    -nodeCount 3 `
    -osType Linux `
    -nodeVmSize Standard_K8S3_v1

Get-AksHciClusterKubeconfig -Name onprem-aks -OutputPath ~/.kube/config

kubectl apply -f otel-deployment.yaml
```

---

### 4.3 Data Synchronization Strategies

#### 4.3.1 Bidirectional Synchronization Architecture

```text
On-Premises                    Cloud
+-----------+             +-----------+
| [Local    |             | [Cloud    |
|  Database]|             |  Database]|
+-----+-----+             +-----+-----+
      |                         |
      |         Sync Layer      |
      +-----> [Kafka/Event Hub] <-----+
                 |                    |
                 +--------------------+
```

#### 4.3.2 Kafka-based Data Synchronization

```yaml
# Kafka Connect configuration for OTel data sync
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  transform/sync:
    log_statements:
      - context: resource
        statements:
          - set(attributes["sync.timestamp"], timestamp())
          - set(attributes["sync.source"], "onprem")
  
  batch:
    timeout: 1s
    send_batch_size: 1000

exporters:
  kafka:
    brokers:
      - kafka-onprem.local:9092
      - kafka-cloud.example.com:9092
    topic: otel-traces
    encoding: otlp_proto
    producer:
      max_message_bytes: 10000000
      required_acks: 1
    partition_traces_by_id: true
    partition_metrics_by_resource_attributes:
      - service.name
      - host.name

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [transform/sync, batch]
      exporters: [kafka]
```

---

### 4.4 Unified Management and Monitoring

#### 4.4.1 Unified Control Plane

```text
+----------------------------------+
|     Unified Control Plane        |
|  [OPAMP Server] [Config Mgmt]    |
+----------------------------------+
    |         |         |        |
 On-Prem      AWS      Azure     GCP
 [Collector] [Collector] [Collector] [Collector]
```

#### 4.4.2 OPAMP Unified Configuration

```go
package main

import (
	"context"
	"crypto/sha256"
	"fmt"
	"os"
	"time"

	"github.com/open-telemetry/opamp-go/client"
	"github.com/open-telemetry/opamp-go/client/types"
	"github.com/open-telemetry/opamp-go/protobufs"
)

type UnifiedOpAMPClient struct {
	client        client.OpAMPClient
	configHash    string
	instanceID    string
	location      string
	cloudProvider string
}

func NewUnifiedOpAMPClient(instanceID, location, cloudProvider string) *UnifiedOpAMPClient {
	return &UnifiedOpAMPClient{
		instanceID:    instanceID,
		location:      location,
		cloudProvider: cloudProvider,
	}
}

func (u *UnifiedOpAMPClient) Start(ctx context.Context, serverURL string) error {
	settings := types.StartSettings{
		OpAMPServerURL: serverURL,
		InstanceUID:    u.instanceID,
		Headers: map[string]string{
			"X-Location":       u.location,
			"X-Cloud-Provider": u.cloudProvider,
		},
		AgentDescription: &protobufs.AgentDescription{
			AgentType:    "opentelemetry-collector",
			AgentVersion: "0.90.0",
			AgentAttributes: []*protobufs.KeyValue{
				{
					Key: "location",
					Value: &protobufs.AnyValue{
						Value: &protobufs.AnyValue_StringValue{StringValue: u.location},
					},
				},
				{
					Key: "cloud.provider",
					Value: &protobufs.AnyValue{
						Value: &protobufs.AnyValue_StringValue{StringValue: u.cloudProvider},
					},
				},
			},
		},
		Callbacks: types.CallbacksStruct{
			OnConnectFunc: func(ctx context.Context) {
				fmt.Printf("Connected to OPAMP server from %s\\n", u.location)
			},
			OnMessageFunc: u.onMessage,
		},
	}

	u.client = client.NewWebSocket(nil)
	return u.client.Start(ctx, settings)
}

func (u *UnifiedOpAMPClient) onMessage(ctx context.Context, msg *protobufs.ServerToAgent) {
	if msg.RemoteConfig != nil {
		newHash := fmt.Sprintf("%x", sha256.Sum256(msg.RemoteConfig.Config.ConfigMap["config.yaml"].Body))
		if newHash != u.configHash {
			u.applyConfig(ctx, msg.RemoteConfig.Config)
			u.configHash = newHash
		}
	}
}

func (u *UnifiedOpAMPClient) applyConfig(ctx context.Context, config *protobufs.AgentConfigMap) {
	for name, content := range config.ConfigMap {
		if name == "config.yaml" {
			configPath := "/etc/otel/config.yaml"
			os.WriteFile(configPath, content.Body, 0644)
		}
	}
}

func main() {
	onpremClient := NewUnifiedOpAMPClient(
		"onprem-collector-001",
		"datacenter-beijing",
		"onprem",
	)
	
	awsClient := NewUnifiedOpAMPClient(
		"aws-collector-001",
		"aws-us-east-1",
		"aws",
	)
	
	ctx := context.Background()
	go onpremClient.Start(ctx, "wss://opamp.example.com/v1/opamp")
	go awsClient.Start(ctx, "wss://opamp.example.com/v1/opamp")
	
	select {}
}
```

---

## 5. Data Synchronization Details

### 5.1 Cross-Region Replication

#### 5.1.1 Cross-Region Architecture Diagram

```text
Region A (Primary)      Region B (Secondary)    Region C (DR)
+-----------+          +-----------+          +-----------+
| [App]     |          | [App]     |          | [App]     |
| [Collector|          | [Collector|          | [Collector|
| [Storage] |          | [Storage] |          | [Storage] |
+-----+-----+          +-----+-----+          +-----+-----+
      |                      |                      |
      +----------+-----------+----------------------+
                 |
          [Replication Layer]
          (Async / Sync)
```

#### 5.1.2 Cross-Region Replication Configuration

```yaml
# Cross-region replication configuration
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  routing/region:
    default_exporters: [otlp/primary]
    from_attribute: telemetry.destination.region
    table:
      - value: us-east-1
        exporters: [otlp/us-east-1, otlp/eu-west-1, otlp/ap-southeast-1]
      - value: eu-west-1
        exporters: [otlp/eu-west-1, otlp/us-east-1]
      - value: ap-southeast-1
        exporters: [otlp/ap-southeast-1, otlp/us-east-1]
  
  transform/replication:
    trace_statements:
      - context: span
        statements:
          - set(attributes["replication.source_region"], "us-east-1")
          - set(attributes["replication.timestamp"], Now())

exporters:
  otlp/us-east-1:
    endpoint: otel-gateway.us-east-1.example.com:4317
    headers:
      x-region: us-east-1
      x-replication-role: primary
    
  otlp/eu-west-1:
    endpoint: otel-gateway.eu-west-1.example.com:4317
    headers:
      x-region: eu-west-1
      x-replication-role: secondary
    sending_queue:
      enabled: true
      num_consumers: 4
      queue_size: 5000
    
  otlp/ap-southeast-1:
    endpoint: otel-gateway.ap-southeast-1.example.com:4317
    headers:
      x-region: ap-southeast-1
      x-replication-role: dr

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [routing/region, transform/replication, batch]
      exporters: [otlp/us-east-1, otlp/eu-west-1, otlp/ap-southeast-1]
```

---

### 5.2 Cross-Cloud Data Synchronization

#### 5.2.1 Cross-Cloud Sync Architecture

```text
    [AWS Collector]         [Azure Collector]       [GCP Collector]
           |                       |                       |
           v                       v                       v
    [AWS Kinesis]           [Azure Event Hub]       [GCP Pub/Sub]
           |                       |                       |
           +-----------------------+-----------------------+
                               |
                     [Apache Kafka]
                   (Central Message Bus)
                               |
                       [Central Storage]
```

#### 5.2.2 Kafka Cross-Cloud Sync Configuration

```yaml
# Kafka Connect configuration
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  batch:
    timeout: 1s
    send_batch_size: 1000

exporters:
  kafka:
    brokers:
      - broker1.kafka.aws.example.com:9092
      - broker2.kafka.azure.example.com:9092
      - broker3.kafka.gcp.example.com:9092
    topic: otel-traces
    encoding: otlp_proto
    partition_traces_by_id: true
    producer:
      max_message_bytes: 10485760
      required_acks: 1
      compression: snappy
    
  aws_kinesis:
    region: us-east-1
    stream_name: otel-traces
    partition_key: trace_id
    
  azureeventhub:
    connection_string: ${EVENTHUB_CONNECTION_STRING}
    hub_name: otel-traces
    
  googlecloudpubsub:
    project: my-project
    topic: otel-traces

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [kafka, aws_kinesis, azureeventhub, googlecloudpubsub]
```

---

### 5.3 Consistency Models

#### 5.3.1 Consistency Strategy Comparison

| Consistency Model | Description | Use Case | Latency | Availability |
|-------------------|-------------|----------|---------|--------------|
| **Strong Consistency** | All nodes see the same data simultaneously | Financial transactions | High | Medium |
| **Eventual Consistency** | Data will eventually be consistent across all nodes | Log analysis | Low | High |
| **Causal Consistency** | Preserves causal event ordering | User behavior tracking | Medium | High |
| **Session Consistency** | Read your own writes within same session | User sessions | Medium | High |

#### 5.3.2 Eventual Consistency Configuration

```yaml
processors:
  routing/eventual:
    default_exporters: [otlp/local]
    from_attribute: sync.priority
    table:
      - value: high
        exporters: [otlp/local, otlp/cloud-sync]
      - value: normal
        exporters: [otlp/local, otlp/cloud-async]
      - value: low
        exporters: [otlp/cloud-async]

exporters:
  otlp/local:
    endpoint: localhost:4317
    
  otlp/cloud-sync:
    endpoint: cloud-primary.example.com:4317
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 1000
      
  otlp/cloud-async:
    endpoint: cloud-secondary.example.com:4317
    sending_queue:
      enabled: true
      num_consumers: 2
      queue_size: 10000
    retry_on_failure:
      enabled: true
      initial_interval: 10s
      max_interval: 60s
      max_elapsed_time: 1h
```

---

### 5.4 Conflict Resolution Strategies

#### 5.4.1 Conflict Types and Resolution Strategies

```yaml
# Conflict resolution configuration
processors:
  transform/conflict-resolution:
    trace_statements:
      # Timestamp conflict: use earliest timestamp
      - context: span
        statements:
          - set(attributes["span.start_time"], Min(attributes["span.start_time_local"], attributes["span.start_time_remote"]))
      
      # Priority conflict: keep high priority span
      - context: span
        statements:
          - delete_key(attributes, "span.duplicate") where attributes["span.priority"] == "low"
      
      # Data merge: merge local and remote attributes
      - context: span
        statements:
          - set(attributes["span.source"], Concat(attributes["span.source_local"], ",", attributes["span.source_remote"]))

  groupbytrace:
    wait_duration: 30s
    num_traces: 100000
    num_workers: 10
    discard_orphans:
      enabled: true
      wait: 2m
```

---

## 6. Disaster Recovery

### 6.1 Backup Strategies

#### 6.1.1 Backup Architecture Diagram

```text
Primary Site
+-------------+     +-------------+     +-------------+
| Collector   |     | Config      |     | State Data  |
| Data        |     | Files       |     |             |
+------+------+     +------+------+     +------+------+
       |                   |                   |
       +-------------------+-------------------+
                           |
                   Backup Layer
              [Velero] [Cloud-Native] [Snapshot]
                           |
              +------------+------------+------------+
              |            |            |            |
         Hot Storage   Warm Storage  Cold Storage  Archive
         (7 days)      (30 days)     (90 days)     (7 years)
              |            |            |
              +------------+------------+
                           |
                    Restore to DR Site
```

#### 6.1.2 Velero Backup Configuration

```yaml
# Velero Backup Schedule for OTel
apiVersion: velero.io/v1
kind: Schedule
metadata:
  name: otel-daily-backup
  namespace: velero
spec:
  schedule: "0 2 * * *"  # Daily at 2 AM
  template:
    includedNamespaces:
      - observability
    excludedResources:
      - events
      - pods
    labelSelector:
      matchLabels:
        app.kubernetes.io/part-of: otel
    ttl: 720h0m0s  # 30 days retention
    storageLocation: default
    snapshotVolumes: true

---
# Velero Restore
apiVersion: velero.io/v1
kind: Restore
metadata:
  name: otel-disaster-recovery
  namespace: velero
spec:
  backupName: otel-daily-backup-20251015
  includedNamespaces:
    - observability
  restorePVs: true
```

#### 6.1.3 Cloud-Native Backup

```yaml
# AWS Backup Configuration
apiVersion: backup.aws.upbound.io/v1beta1
kind: Plan
metadata:
  name: otel-backup-plan
spec:
  forProvider:
    name: otel-multicloud-backup
    rule:
      - ruleName: daily-backup
        targetVaultName: otel-backup-vault
        schedule: cron(0 2 * * ? *)
        lifecycle:
          deleteAfter: 30
          moveToColdStorageAfter: 7
        copyAction:
          - destinationVaultArn: arn:aws:backup:eu-west-1:123456789012:backup-vault:otel-dr-vault

---
# Azure Backup Configuration
apiVersion: recoveryservices.azure.upbound.io/v1beta1
kind: ProtectionPolicyVM
metadata:
  name: otel-backup-policy
spec:
  forProvider:
    name: otel-multicloud-policy
    resourceGroupName: rg-otel-backup
    recoveryVaultName: rv-otel-backup
    backup:
      - frequency: Daily
        time: "02:00"
    retentionDaily:
      - count: 30
    retentionWeekly:
      - count: 12
        weekdays: ["Sunday"]
```

#### 6.1.4 Collector State Backup

```yaml
exporters:
  file/backup:
    path: /var/otel/backup/state
    rotation:
      max_megabytes: 100
      max_days: 7
      max_backups: 5
      compress: true
  
  otlp/primary:
    endpoint: primary-backend:4317
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
      storage: file_storage

extensions:
  file_storage:
    directory: /var/otel/storage
    timeout: 10s
    compaction:
      on_start: true
      on_rebound: true

service:
  extensions: [file_storage]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/primary, file/backup]
```

---

### 6.2 Recovery Procedures and Runbooks

#### 6.2.1 Recovery Flowchart

```text
Disaster Occurs
       |
  Impact Assessment
       |
   +---+---+
   |       |
Minor   Severe
   |       |
Local   Initiate DR
Recovery  Process
            |
      +-----+-----+
      |           |
  Notify      Assess Backup
  Team        Status
                  |
            Backup Available?
            +----+----+
            |         |
           Yes       No
            |         |
      Select     Switch to
      Recovery     Cold Backup
      Point        |
            +------+
            |
      Prepare DR
      Environment
            |
      Restore Config
            |
      Restore Data
            |
      Validate Recovery
            |
      Validation Pass?
      +------+------+
      |             |
     Yes            No
      |             |
  Switch     Troubleshoot
  Traffic       |
      |         +-> Prepare DR
  Monitor     |
  Validation  |
      |       |
      +-------+
            |
    Notify Business
    Recovery Complete
```

#### 6.2.2 Recovery Runbook

```markdown
# OTel Disaster Recovery Runbook

## RTO/RPO Targets
- **RTO (Recovery Time Objective)**: 30 minutes
- **RPO (Recovery Point Objective)**: 5 minutes

## Scenario 1: Single Region Failure

### Detection
```bash
# Check collector health status
kubectl get pods -n observability -l app=otel-collector

# Check exporter connection
curl http://otel-gateway:13133/debug/exporters
```

### Response
1. **Switch Traffic to Backup Region**
```bash
aws route53 change-resource-record-sets \
  --hosted-zone-id Z123456789 \
  --change-batch file://switch-to-dr.json
```

2. **Verify Backup Region Services**
```bash
kubectl --context=dr-cluster get pods -n observability
```

## Scenario 2: Primary Storage Failure

### Detection
```bash
curl -f http://jaeger-query:16686/health || echo "Storage unavailable"
```

### Response
1. **Switch to Backup Storage**
```yaml
exporters:
  jaeger:
    endpoint: jaeger-dr:14250  # Switch to DR Jaeger
```

2. **Replay Backlogged Data**
```bash
otelcol --config=/etc/otel/recovery-config.yaml
```

## Recovery Validation Checklist

- [ ] Collector pods running normally
- [ ] Configuration loaded correctly
- [ ] Exporter connections normal
- [ ] Data receiving normally
- [ ] Query function normal
- [ ] Alerting system normal
- [ ] Documentation updated

## Contact Information

- **On-call Engineer**: on-call@example.com
- **DR Lead**: dr-lead@example.com
- **Platform Team**: platform@example.com
```

---

### 6.3 Failover Automation

#### 6.3.1 Automatic Failover Architecture

```text
Health Check Layer
+-----------------+-----------------+-----------------+
| HTTP Probe      | TCP Probe       | Custom Probe    |
+--------+--------+--------+--------+--------+--------+
         |                 |                 |
         +-----------------+-----------------+
                           |
                    Decision Engine
              +------------+------------+
              |            |            |
         Rule Engine  Threshold   Manual
                        Judge      Confirm
              |            |            |
              +------------+------------+
                           |
                    Execute Actions
              +------------+------------+------------+
              |            |            |            |
         DNS Switch   LB Adjust   Config Update   Monitor
              |            |            |            |
              +------------+------------+------------+
                           |
                    Monitoring Feedback
```

#### 6.3.2 Automatic Failover Configuration

```yaml
# OpenTelemetry Collector Failover Configuration
exporters:
  otlp/primary:
    endpoint: primary-gateway:4317
    tls:
      insecure: false
      ca_file: /etc/certs/primary-ca.crt
    retry_on_failure:
      enabled: true
      max_elapsed_time: 60s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
      storage: file_storage
    
  otlp/secondary:
    endpoint: secondary-gateway:4317
    tls:
      insecure: false
      ca_file: /etc/certs/secondary-ca.crt
    retry_on_failure:
      enabled: true
      max_elapsed_time: 300s
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 10000
      storage: file_storage
  
  otlp/tertiary:
    endpoint: tertiary-gateway:4317
    tls:
      insecure: false
      ca_file: /etc/certs/tertiary-ca.crt

processors:
  failover:
    priority_levels:
      - name: primary
        exporters: [otlp/primary]
        failback_seconds: 300
      - name: secondary
        exporters: [otlp/secondary]
        failback_seconds: 600
      - name: tertiary
        exporters: [otlp/tertiary]
    
    health_check:
      interval: 10s
      timeout: 5s
      threshold: 3
      path: /health
      port: 13133

extensions:
  health_check:
    endpoint: 0.0.0.0:13133
    path: /health
  
  file_storage:
    directory: /var/otel/storage
    timeout: 10s

service:
  extensions: [health_check, file_storage]
  pipelines:
    traces:
      receivers: [otlp]
      processors: [failover, batch]
      exporters: [otlp/primary, otlp/secondary, otlp/tertiary]
```

---

### 6.4 Disaster Recovery Drills

#### 6.4.1 Drill Plan Template

```yaml
# dr-drill.yaml
apiVersion: drill.otlp.io/v1
kind: DisasterRecoveryDrill
metadata:
  name: quarterly-dr-drill
  namespace: observability
spec:
  schedule: "0 2 * * 0#1"  # First Sunday of every quarter
  duration: 4h
  scope:
    components:
      - collector
      - storage
      - network
    regions:
      - us-east-1
      - eu-west-1
  scenarios:
    - name: single-region-failure
      type: region-failure
      target: us-east-1
      expectedRTO: 30m
      expectedRPO: 5m
      validation:
        - metric: collector.availability
          expected: ">= 0.99"
        - metric: data.loss.percentage
          expected: "<= 0.01"
          
    - name: storage-failure
      type: storage-failure
      target: jaeger-primary
      expectedRTO: 15m
      validation:
        - metric: query.latency.p99
          expected: "<= 500ms"
          
    - name: complete-site-failure
      type: site-failure
      target: us-east-1
      expectedRTO: 1h
      expectedRPO: 10m
      
  rollback:
    automatic: true
    delay: 30m
    validationRequired: true
  
  notifications:
    before:
      - type: slack
        channel: "#dr-drills"
      - type: email
        to: ["dr-team@example.com"]
    after:
      - type: slack
        channel: "#dr-drills"
      - type: email
        to: ["dr-team@example.com", "management@example.com"]
```

#### 6.4.2 Drill Execution Script

```bash
#!/bin/bash
# dr-drill.sh - Disaster Recovery Drill Script

set -e

DRILL_ID=$(date +%Y%m%d-%H%M%S)
SCENARIO=${1:-single-region-failure}
REGION=${2:-us-east-1}
LOG_FILE="/var/log/dr-drill-${DRILL_ID}.log"

echo "Starting DR Drill: ${DRILL_ID}" | tee -a $LOG_FILE
echo "Scenario: ${SCENARIO}" | tee -a $LOG_FILE
echo "Target Region: ${REGION}" | tee -a $LOG_FILE

# Pre-check
echo "[$(date)] Pre-check started" | tee -a $LOG_FILE
kubectl get pods -n observability > /tmp/pre-check-pods.txt
curl -s http://otel-gateway:13133/health > /tmp/pre-check-health.txt

case $SCENARIO in
  single-region-failure)
    echo "[$(date)] Simulating region failure: ${REGION}" | tee -a $LOG_FILE
    
    # Simulate network partition
    kubectl apply -f network-partition.yaml
    
    # Wait for failover
    sleep 300
    
    # Verify failover
    ./validate-failover.sh
    
    # Restore network
    kubectl delete networkchaos region-partition -n observability
    ;;
    
  storage-failure)
    echo "[$(date)] Simulating storage failure" | tee -a $LOG_FILE
    
    # Simulate storage failure
    kubectl patch statefulset jaeger --type=json \
      -p='[{"op": "replace", "path": "/spec/replicas", "value": 0}]'
    
    sleep 180
    
    # Verify storage failover
    ./validate-storage-failover.sh
    
    # Restore storage
    kubectl patch statefulset jaeger --type=json \
      -p='[{"op": "replace", "path": "/spec/replicas", "value": 3}]'
    ;;
    
  complete-site-failure)
    echo "[$(date)] Simulating complete site failure" | tee -a $LOG_FILE
    
    # Start DR recovery process
    velero restore create dr-drill-${DRILL_ID} \
      --from-backup otel-daily-backup \
      --include-namespaces observability
    
    # Wait for restore completion
    kubectl wait --for=condition=Complete restore dr-drill-${DRILL_ID} -n velero --timeout=30m
    
    # Validate restore
    ./validate-restore.sh
    ;;
esac

# Post-check
echo "[$(date)] Post-check started" | tee -a $LOG_FILE
kubectl get pods -n observability > /tmp/post-check-pods.txt
curl -s http://otel-gateway:13133/health > /tmp/post-check-health.txt

echo "DR Drill completed. Report: /tmp/dr-drill-report-${DRILL_ID}.md"
```

---

## 7. Cost Optimization

### 7.1 Multi-Cloud Cost Comparison

#### 7.1.1 Cloud Service Pricing Comparison

| Service Type | AWS | Azure | GCP | Recommended Scenario |
|--------------|-----|-------|-----|---------------------|
| **Compute (vCPU/hour)** | $0.042 (t3.medium) | $0.041 (B2s) | $0.033 (e2-medium) | Long-term: GCP; Short-term: AWS/Azure |
| **Storage (GB/month)** | $0.023 (S3 Standard) | $0.018 (Blob Hot) | $0.020 (Standard) | Azure lowest cost |
| **Network Egress (GB)** | $0.09 | $0.087 | $0.12 | High traffic: Azure; Low traffic: Any |
| **Kubernetes Cluster** | $0.10/hour (EKS) | $0.10/hour (AKS) | $0.10/hour (GKE) | Similar pricing, choose familiar platform |
| **Serverless (per million requests)** | $0.20 (Lambda) | $0.20 (Functions) | $0.40 (Cloud Functions) | High frequency: AWS/Azure; Low frequency: Any |

#### 7.1.2 Cost Analysis Tools

```yaml
# OTel Collector cost analysis configuration
processors:
  metricstransform/cost:
    transforms:
      - include: otelcol_exporter_sent_bytes
        match_type: regexp
        action: update
        operations:
          - action: add_label
            new_label: cost_category
            new_value: data_transfer
          - action: aggregate_labels
            label_set: [exporter, cost_category]
            aggregation_type: sum

exporters:
  prometheus/cost:
    endpoint: cost-metrics:9090
    namespace: otel_cost
```

---

### 7.2 Spot Instance Strategies

#### 7.2.1 Spot Instance Architecture

```text
On-Demand Instances (Critical)
+-----------+
| Gateway   |
| 3 replicas|
+-----+-----+
      |
      v
Spot Instances (Batch)
+-----------+     +-----------+
| Agent     |     | Batch     |
| DaemonSet |     | Processor |
+-----+-----+     +-----+-----+
      |                 |
      +--------+--------+
               |
          Interruption
               |
      +--------v--------+
      |  On-Demand      |
      |  Fallback Pool  |
      +--------+--------+
               |
               v
         Cost Savings
         (60-90% discount)
```

#### 7.2.2 Spot Instance Configuration

```yaml
# AWS EKS with Spot Instances
apiVersion: karpenter.sh/v1alpha5
kind: Provisioner
metadata:
  name: otel-spot
spec:
  requirements:
    - key: karpenter.sh/capacity-type
      operator: In
      values: ["spot"]
    - key: node.kubernetes.io/instance-type
      operator: In
      values: ["m5.large", "m5.xlarge", "m5.2xlarge", "c5.large", "c5.xlarge"]
    - key: kubernetes.io/arch
      operator: In
      values: ["amd64"]
  
  ttlSecondsAfterEmpty: 30
  ttlSecondsUntilExpired: 86400
  
  limits:
    resources:
      cpu: 1000
      memory: 4000Gi
  
  taints:
    - key: spot
      value: "true"
      effect: NoSchedule
  
  labels:
    workload-type: spot-tolerant

---
# Spot-tolerant Collector Deployment
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-agent-spot
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-agent-spot
  template:
    metadata:
      labels:
        app: otel-agent-spot
    spec:
      tolerations:
        - key: spot
          operator: Equal
          value: "true"
          effect: NoSchedule
      nodeSelector:
        workload-type: spot-tolerant
      containers:
      - name: otel-agent
        image: otel/opentelemetry-collector-contrib:0.90.0
        resources:
          requests:
            cpu: 200m
            memory: 256Mi
          limits:
            cpu: 1000m
            memory: 1Gi
        lifecycle:
          preStop:
            exec:
              command: ["/bin/sh", "-c", "sleep 30"]
```

---

### 7.3 Reserved Capacity Planning

#### 7.3.1 Reserved Instance Comparison

| Reserved Type | AWS | Azure | GCP | Discount |
|--------------|-----|-------|-----|----------|
| **1-Year All Upfront** | 40% | 36% | 37% | Highest discount |
| **1-Year Partial Upfront** | 35% | 32% | 33% | Balanced cash flow |
| **1-Year No Upfront** | 30% | 28% | 29% | Lowest barrier |
| **3-Year All Upfront** | 60% | 54% | 55% | Long-term commitment |
| **Savings Plans** | 30-72% | Contract | Committed Use Discounts | Most flexible |

#### 7.3.2 Capacity Planning Configuration

```hcl
# Terraform - Reserved Capacity Planning

# AWS Savings Plans
resource "aws_savingsplans_plan" "otel_compute" {
  savings_plan_type = "Compute"
  term              = 3
  payment_option    = "All Upfront"
  commitment        = "100.0"
}

# Azure Reserved VM Instances
resource "azurerm_reservation" "otel_vms" {
  name = "otel-collector-reservation"
  sku {
    name = "Standard_D4s_v3"
    tier = "Standard"
  }
  scope {
    type = "Single"
    id   = azurerm_subscription.current.id
  }
  term      = "P3Y"
  quantity  = 10
}

# GCP Committed Use Discounts
resource "google_compute_region_commitment" "otel_resources" {
  name = "otel-collector-commitment"
  plan = "ANNUAL"
  
  resources {
    type   = "VCPU"
    amount = "100"
  }
  
  resources {
    type   = "MEMORY"
    amount = "409600"
  }
  
  region = "us-central1"
}
```

---

### 7.4 Cross-Cloud Load Balancing Cost Optimization

#### 7.4.1 Cross-Cloud Load Balancing Architecture

```text
Traffic Entry
+-------------+
| Global DNS  |
| Route53/CF  |
+------+------+
       |
Load Balancing Layer
+------v------+
| Global LB   |
+------+------+
       |
   +---+---+
   |       |
US Region EU Region
(Spot)   (Spot)
   |       |
  AWS    Azure
   |       |
   +---+---+
       |
   APAC Region
     (Spot)
       |
      GCP
```

#### 7.4.2 Cost-Aware Routing Configuration

```yaml
processors:
  routing/cost-aware:
    default_exporters: [otlp/primary]
    from_attribute: cost.region
    table:
      - value: aws-spot
        exporters: [otlp/aws-spot]
      - value: azure-spot
        exporters: [otlp/azure-spot]
      - value: gcp-spot
        exporters: [otlp/gcp-spot]
      - value: aws-on-demand
        exporters: [otlp/aws-on-demand]
      - value: azure-on-demand
        exporters: [otlp/azure-on-demand]

exporters:
  otlp/aws-spot:
    endpoint: aws-spot-gateway:4317
    headers:
      x-cost-tier: spot
      x-cloud-provider: aws
    
  otlp/azure-spot:
    endpoint: azure-spot-gateway:4317
    headers:
      x-cost-tier: spot
      x-cloud-provider: azure
    
  otlp/gcp-spot:
    endpoint: gcp-spot-gateway:4317
    headers:
      x-cost-tier: spot
      x-cloud-provider: gcp

  otlp/aws-on-demand:
    endpoint: aws-od-gateway:4317
    headers:
      x-cost-tier: on-demand
      x-cloud-provider: aws
```

---

## 8. Best Practices

### 8.1 Unified Configuration Management

```yaml
# Use OPAMP for remote configuration management
extensions:
  opamp:
    server:
      ws:
        endpoint: wss://opamp.example.com/v1/opamp
        headers:
          X-API-Key: ${OPAMP_API_KEY}
    agent:
      description:
        agent_type: "opentelemetry-collector"
        agent_version: "0.90.0"
```

### 8.2 Security Best Practices

```yaml
# mTLS configuration
exporters:
  otlp/secure:
    endpoint: secure-gateway:4317
    tls:
      insecure: false
      cert_file: /etc/certs/client.crt
      key_file: /etc/certs/client.key
      ca_file: /etc/certs/ca.crt
      min_version: "1.3"
```

### 8.3 Monitoring and Alerting

```yaml
# Self-monitoring configuration
processors:
  metricstransform/self-monitoring:
    transforms:
      - include: otelcol_exporter_queue_size
        action: update
        new_name: collector_queue_saturation
        operations:
          - action: add_label
            new_label: priority
            new_value: high

exporters:
  prometheusremotewrite/self:
    endpoint: http://prometheus:9090/api/v1/write
    resource_to_telemetry_conversion:
      enabled: true
```

---

## Appendix

### A. Glossary

| Term | Definition |
|------|------------|
| **OTLP** | OpenTelemetry Protocol |
| **EKS** | Amazon Elastic Kubernetes Service |
| **AKS** | Azure Kubernetes Service |
| **GKE** | Google Kubernetes Engine |
| **OPAMP** | Open Agent Management Protocol |
| **RTO** | Recovery Time Objective |
| **RPO** | Recovery Point Objective |
| **Velero** | Kubernetes backup and migration tool |

### B. Reference Links

- [OpenTelemetry Documentation](https://opentelemetry.io/docs/)
- [AWS EKS Best Practices](https://aws.github.io/aws-eks-best-practices/)
- [Azure AKS Documentation](https://docs.microsoft.com/en-us/azure/aks/)
- [GCP GKE Documentation](https://cloud.google.com/kubernetes-engine/docs)
- [Velero Documentation](https://velero.io/docs/)

---

**Document Status**: Complete  
**Last Updated**: 2025-10-15  
**Lines**: 1400+  
**Code Examples**: 50+  
**Maintainer**: OTLP_go Team

# 🇨🇳 腾讯云OpenTelemetry集成指南

> **腾讯云服务**: CLS, APM, TDMQ, TMP  
> **OTLP版本**: v1.3.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [🇨🇳 腾讯云OpenTelemetry集成指南](#-腾讯云opentelemetry集成指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [腾讯云可观测性服务](#腾讯云可观测性服务)
    - [集成架构](#集成架构)
    - [为什么选择腾讯云 + OTLP?](#为什么选择腾讯云--otlp)
  - [📊 CLS日志服务集成](#-cls日志服务集成)
    - [概述](#概述)
    - [前置准备](#前置准备)
    - [Collector配置](#collector配置)
      - [方式1: 通过Kafka协议](#方式1-通过kafka协议)
      - [方式2: 通过HTTP API](#方式2-通过http-api)
    - [SDK集成](#sdk集成)
      - [Go SDK](#go-sdk)
      - [Java SDK (Spring Boot集成)](#java-sdk-spring-boot集成)
      - [Python SDK](#python-sdk)
    - [CLS检索和分析](#cls检索和分析)
      - [检索语法](#检索语法)
      - [分析示例](#分析示例)
  - [🚀 APM应用性能监控集成](#-apm应用性能监控集成)
    - [概述1](#概述1)
    - [前置准备1](#前置准备1)
    - [Collector配置1](#collector配置1)
    - [SDK直接集成](#sdk直接集成)
    - [APM功能](#apm功能)
      - [1. 链路追踪](#1-链路追踪)
      - [2. 服务拓扑](#2-服务拓扑)
      - [3. 性能分析](#3-性能分析)
  - [📈 TMP云原生监控集成](#-tmp云原生监控集成)
    - [概述2](#概述2)
    - [Collector配置2](#collector配置2)
    - [Grafana集成](#grafana集成)
      - [配置数据源](#配置数据源)
      - [常用Dashboard](#常用dashboard)
        - [1. 应用性能监控](#1-应用性能监控)
        - [2. 系统资源监控](#2-系统资源监控)
  - [🏗️ 架构最佳实践](#️-架构最佳实践)
    - [1. 混合云架构](#1-混合云架构)
    - [2. TKE (腾讯云K8s) DaemonSet](#2-tke-腾讯云k8s-daemonset)
    - [3. 分层部署](#3-分层部署)
  - [💰 成本优化](#-成本优化)
    - [CLS成本分析](#cls成本分析)
      - [计费项](#计费项)
      - [优化策略](#优化策略)
        - [1. 启用压缩 (节省60-70%)](#1-启用压缩-节省60-70)
        - [2. 智能采样 (节省90%+)](#2-智能采样-节省90)
        - [3. 生命周期管理](#3-生命周期管理)
        - [4. 索引优化](#4-索引优化)
      - [成本计算示例](#成本计算示例)
    - [APM成本优化](#apm成本优化)
  - [🔍 故障排查](#-故障排查)
    - [常见问题](#常见问题)
      - [1. CLS Kafka连接失败](#1-cls-kafka连接失败)
      - [2. APM Token认证失败](#2-apm-token认证失败)
      - [3. TMP远程写入失败](#3-tmp远程写入失败)
      - [4. 数据延迟高](#4-数据延迟高)
  - [📚 参考资源](#-参考资源)
  - [🎯 最佳实践总结](#-最佳实践总结)

---

## 🎯 概述

### 腾讯云可观测性服务

| 服务 | 用途 | OTLP支持 | 推荐场景 |
|-----|------|----------|---------|
| **CLS (日志服务)** | 日志收集、检索、分析 | ✅ Native | 日志中心化 |
| **APM (应用性能监控)** | 链路追踪、调用分析 | ✅ Native | 微服务追踪 |
| **TMP (Prometheus监控)** | 时序指标监控 | ✅ Native | 云原生监控 |
| **TDMQ (消息队列)** | 消息中间件 | ⚠️ 间接 | 数据缓冲 |

### 集成架构

```text
┌───────────────────────────────────────────────────────┐
│                    应用层                              │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐           │
│  │   Go     │  │  Java    │  │  Python  │  ...      │
│  │   App    │  │   App    │  │   App    │           │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘           │
│       │             │              │                  │
│       └─────────────┼──────────────┘                 │
│                     │ OTLP (gRPC/HTTP)               │
└─────────────────────┼────────────────────────────────┘
                      │
┌─────────────────────▼────────────────────────────────┐
│              OpenTelemetry Collector                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │
│  │ Receivers   │→ │ Processors  │→ │ Exporters   │ │
│  │ (OTLP)      │  │ (Batch,     │  │ (CLS, APM,  │ │
│  │             │  │  Filter)    │  │  TMP)       │ │
│  └─────────────┘  └─────────────┘  └──────┬──────┘ │
└────────────────────────────────────────────┼────────┘
                                              │
┌─────────────────────────────────────────────▼────────┐
│                    腾讯云服务                         │
│  ┌──────────────┐  ┌──────────────┐  ┌────────────┐│
│  │     CLS      │  │     APM      │  │    TMP     ││
│  │  (日志服务)   │  │  (应用监控)   │  │(Prometheus)││
│  └──────────────┘  └──────────────┘  └────────────┘│
└───────────────────────────────────────────────────────┘
```

### 为什么选择腾讯云 + OTLP?

| 优势 | 说明 |
|-----|------|
| **深度集成** | 与微信、QQ等生态深度集成 |
| **国内优化** | 针对国内网络环境优化 |
| **游戏行业** | 特别适合游戏/社交应用 |
| **成本优势** | 竞争力的价格 |
| **合规性** | 满足国内数据合规要求 |

---

## 📊 CLS日志服务集成

### 概述

腾讯云日志服务 (CLS - Cloud Log Service) 支持通过Kafka协议接收OTLP数据。

### 前置准备

1. **创建日志集和日志主题**

   ```text
   控制台路径: 日志服务 CLS → 日志主题
   - 日志集: my-observability
   - 日志主题: otlp-logs
   - 地域: ap-guangzhou
   ```

2. **获取访问凭证**
   - SecretId
   - SecretKey
   - 日志主题ID

### Collector配置

#### 方式1: 通过Kafka协议

```yaml
# otel-collector-config.yaml
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
    check_interval: 1s
    limit_mib: 512
  
  resource:
    attributes:
      - key: cloud.provider
        value: tencent_cloud
        action: upsert
      - key: cloud.region
        value: ap-guangzhou
        action: upsert

exporters:
  # CLS通过Kafka协议
  kafka/cls:
    brokers:
      - ${CLS_KAFKA_ENDPOINT}  # 例如: 10.1.2.3:9096
    topic: ${CLS_TOPIC_ID}
    encoding: otlp_proto
    compression: gzip
    auth:
      sasl:
        username: ${TENCENT_SECRET_ID}
        password: ${TENCENT_SECRET_KEY}
        mechanism: PLAIN
      tls:
        insecure: false

service:
  pipelines:
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [kafka/cls]
    
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [kafka/cls]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [kafka/cls]
```

#### 方式2: 通过HTTP API

```yaml
exporters:
  tencentcloud_cls:
    endpoint: "ap-guangzhou.cls.tencentyun.com"
    topic_id: "${CLS_TOPIC_ID}"
    secret_id: "${TENCENT_SECRET_ID}"
    secret_key: "${TENCENT_SECRET_KEY}"
    # 可选: 指定字段
    log_type: "minimalist_log"  # 或 "json_log"

service:
  pipelines:
    logs:
      receivers: [otlp]
      processors: [batch]
      exporters: [tencentcloud_cls]
```

### SDK集成

#### Go SDK

```go
package main

import (
    "context"
    "log"
    "os"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploggrpc"
    "go.opentelemetry.io/otel/sdk/log"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func initLogger() (*log.LoggerProvider, error) {
    ctx := context.Background()

    // 创建OTLP exporter
    exporter, err := otlploggrpc.New(
        ctx,
        otlploggrpc.WithEndpoint("collector.example.com:4317"),
        otlploggrpc.WithInsecure(), // 生产环境使用TLS
    )
    if err != nil {
        return nil, err
    }

    // 创建Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("my-tencent-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
            semconv.CloudProvider("tencent_cloud"),
            semconv.CloudRegion("ap-guangzhou"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 创建LoggerProvider
    lp := log.NewLoggerProvider(
        log.WithProcessor(log.NewBatchProcessor(exporter,
            log.WithBatchTimeout(5*time.Second),
        )),
        log.WithResource(res),
    )

    return lp, nil
}

func main() {
    lp, err := initLogger()
    if err != nil {
        log.Fatal(err)
    }
    defer lp.Shutdown(context.Background())

    // 使用Logger
    logger := lp.Logger("my-service")
    
    // 记录日志
    logger.Info("Application started",
        log.String("version", "1.0.0"),
        log.Int("port", 8080),
    )

    // 业务逻辑
    time.Sleep(2 * time.Second)
}
```

#### Java SDK (Spring Boot集成)

```java
import io.opentelemetry.api.GlobalOpenTelemetry;
import io.opentelemetry.exporter.otlp.logs.OtlpGrpcLogRecordExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.logs.SdkLoggerProvider;
import io.opentelemetry.sdk.logs.export.BatchLogRecordProcessor;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.semconv.resource.attributes.ResourceAttributes;

@Configuration
public class TencentCloudOTLPConfig {
    
    @Bean
    public OpenTelemetrySdk openTelemetrySdk() {
        // 创建Resource
        Resource resource = Resource.getDefault()
            .merge(Resource.create(Attributes.of(
                ResourceAttributes.SERVICE_NAME, "my-spring-service",
                ResourceAttributes.SERVICE_VERSION, "1.0.0",
                ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production",
                ResourceAttributes.CLOUD_PROVIDER, "tencent_cloud",
                ResourceAttributes.CLOUD_REGION, "ap-guangzhou"
            )));

        // 创建OTLP log exporter
        OtlpGrpcLogRecordExporter logExporter = OtlpGrpcLogRecordExporter.builder()
            .setEndpoint("http://collector.example.com:4317")
            .setTimeout(Duration.ofSeconds(30))
            .build();

        // 创建LoggerProvider
        SdkLoggerProvider loggerProvider = SdkLoggerProvider.builder()
            .addLogRecordProcessor(
                BatchLogRecordProcessor.builder(logExporter)
                    .setScheduleDelay(Duration.ofSeconds(5))
                    .build()
            )
            .setResource(resource)
            .build();

        // 创建OpenTelemetry SDK
        return OpenTelemetrySdk.builder()
            .setLoggerProvider(loggerProvider)
            .buildAndRegisterGlobal();
    }
}
```

#### Python SDK

```python
import time
from opentelemetry import logs
from opentelemetry.exporter.otlp.proto.grpc._log_exporter import OTLPLogExporter
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk._logs import LoggerProvider
from opentelemetry.sdk._logs.export import BatchLogRecordProcessor
from opentelemetry.semconv.resource import ResourceAttributes

def init_logger():
    # 创建Resource
    resource = Resource.create({
        ResourceAttributes.SERVICE_NAME: "my-python-service",
        ResourceAttributes.SERVICE_VERSION: "1.0.0",
        ResourceAttributes.DEPLOYMENT_ENVIRONMENT: "production",
        ResourceAttributes.CLOUD_PROVIDER: "tencent_cloud",
        ResourceAttributes.CLOUD_REGION: "ap-guangzhou",
    })

    # 创建OTLP exporter
    otlp_exporter = OTLPLogExporter(
        endpoint="collector.example.com:4317",
        insecure=True,  # 生产环境使用TLS
    )

    # 创建LoggerProvider
    provider = LoggerProvider(resource=resource)
    processor = BatchLogRecordProcessor(otlp_exporter)
    provider.add_log_record_processor(processor)
    logs.set_logger_provider(provider)

    return logs.get_logger("my-service")

def main():
    logger = init_logger()

    # 记录日志
    logger.info("Application started", {"version": "1.0.0", "port": 8080})
    time.sleep(2)

if __name__ == "__main__":
    main()
```

### CLS检索和分析

#### 检索语法

```text
# 全文检索
"error" AND "timeout"

# 字段检索
service.name: "my-service" AND status.code: "ERROR"

# 范围检索
duration: [500 TO 1000]

# 正则检索
http.url: /api/users/\d+/

# 模糊检索
message: *timeout*
```

#### 分析示例

```sql
-- 统计各服务的错误率
* | SELECT service.name, 
           COUNT(CASE WHEN status.code = 'ERROR' THEN 1 END) * 100.0 / COUNT(*) as error_rate
    GROUP BY service.name
    ORDER BY error_rate DESC

-- 统计P99延迟
* | SELECT approx_percentile(duration, 0.99) as p99_latency

-- 统计QPS
* | SELECT date_trunc('minute', __TIMESTAMP__) as time, 
           COUNT(*) / 60.0 as qps
    GROUP BY time
    ORDER BY time
```

---

## 🚀 APM应用性能监控集成

### 概述1

腾讯云APM (Application Performance Management) 提供分布式链路追踪能力,支持OTLP协议。

### 前置准备1

1. **开通APM服务**
2. **创建业务系统**
3. **获取接入点信息**
   - Region: `ap-guangzhou`
   - Token: 从控制台获取

### Collector配置1

```yaml
exporters:
  otlp/apm:
    endpoint: "apm.tencentcs.com:4317"
    headers:
      # APM Token认证
      Authorization: "Bearer ${TENCENT_APM_TOKEN}"
    compression: gzip
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch, tail_sampling]
      exporters: [otlp/apm]
```

### SDK直接集成

```go
// Go SDK直接导出到腾讯云APM
exporter, err := otlptracegrpc.New(
    ctx,
    otlptracegrpc.WithEndpoint("apm.tencentcs.com:4317"),
    otlptracegrpc.WithHeaders(map[string]string{
        "Authorization": "Bearer " + os.Getenv("TENCENT_APM_TOKEN"),
    }),
    otlptracegrpc.WithCompressor("gzip"),
)
```

### APM功能

#### 1. 链路追踪

- **调用链路图**: 可视化服务间调用关系
- **Span详情**: 查看每个Span的详细信息
- **慢调用分析**: 自动识别慢请求
- **错误追踪**: 聚合和分析错误

#### 2. 服务拓扑

```text
┌─────────────┐
│  Frontend   │
└──────┬──────┘
       │
       ▼
┌─────────────┐     ┌─────────────┐
│   API GW    │────>│   Auth      │
└──────┬──────┘     └─────────────┘
       │
       ├──────────────┬──────────────┐
       ▼              ▼              ▼
┌─────────────┐ ┌──────────┐ ┌──────────┐
│  Order API  │ │ User API │ │ Pay API  │
└──────┬──────┘ └────┬─────┘ └────┬─────┘
       │             │             │
       ▼             ▼             ▼
┌─────────────┐ ┌──────────┐ ┌──────────┐
│   MySQL     │ │  Redis   │ │  Kafka   │
└─────────────┘ └──────────┘ └──────────┘
```

#### 3. 性能分析

```text
TOP慢接口:
1. POST /api/orders/create     - 1.2s (P99)
2. GET /api/users/{id}/profile - 850ms (P99)
3. POST /api/payment/process   - 650ms (P99)

错误率TOP:
1. GET /api/third-party/data - 5.2% (网络超时)
2. POST /api/sms/send        - 3.1% (限流)
3. GET /api/cache/get        - 1.5% (Redis连接)
```

---

## 📈 TMP云原生监控集成

### 概述2

腾讯云Prometheus监控服务 (TMP - Tencent Managed Service for Prometheus) 提供托管的Prometheus。

### Collector配置2

```yaml
exporters:
  prometheusremotewrite:
    endpoint: "http://tmp-xxx.tencentcs.com/api/v1/write"
    headers:
      # TMP认证
      X-Prometheus-Remote-Write-Version: "0.1.0"
      Authorization: "Bearer ${TMP_TOKEN}"
    resource_to_telemetry_conversion:
      enabled: true
    compression: snappy
    retry_on_failure:
      enabled: true
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000

service:
  pipelines:
    metrics:
      receivers: [otlp, prometheus]
      processors: [batch, filter]
      exporters: [prometheusremotewrite]
```

### Grafana集成

#### 配置数据源

```yaml
apiVersion: 1

datasources:
  - name: TMP
    type: prometheus
    access: proxy
    url: http://tmp-xxx.tencentcs.com
    jsonData:
      httpHeaderName1: 'Authorization'
    secureJsonData:
      httpHeaderValue1: 'Bearer ${TMP_TOKEN}'
```

#### 常用Dashboard

##### 1. 应用性能监控

```promql
# QPS
rate(http_server_request_duration_count[1m])

# P99延迟
histogram_quantile(0.99, 
  rate(http_server_request_duration_bucket[5m])
)

# 错误率
sum(rate(http_server_request_duration_count{http_status_code=~"5.."}[1m])) 
/ sum(rate(http_server_request_duration_count[1m]))

# 请求量TOP 10
topk(10, sum by(http_route) (
  rate(http_server_request_duration_count[5m])
))
```

##### 2. 系统资源监控

```promql
# CPU使用率
100 - (avg by(instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)

# 内存使用率
(1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)) * 100

# 磁盘IO
rate(node_disk_read_bytes_total[5m]) + rate(node_disk_written_bytes_total[5m])

# 网络流量
rate(node_network_receive_bytes_total[5m]) + rate(node_network_transmit_bytes_total[5m])
```

---

## 🏗️ 架构最佳实践

### 1. 混合云架构

```text
┌──────────────────────────────────────────────────────┐
│                  自建IDC / 其他云                     │
│  ┌───────┐  ┌───────┐  ┌───────┐                    │
│  │  App  │  │  App  │  │  App  │                    │
│  └───┬───┘  └───┬───┘  └───┬───┘                    │
│      │          │          │                         │
│      └──────────┼──────────┘                         │
│                 │                                     │
│         ┌───────▼──────┐                             │
│         │   Collector  │                             │
│         │   (Agent)    │                             │
│         └──────┬───────┘                             │
│                │ 专线/VPN                             │
└────────────────┼──────────────────────────────────────┘
                 │
┌────────────────▼──────────────────────────────────────┐
│                    腾讯云VPC                           │
│          ┌────────────────┐                           │
│          │   Collector    │                           │
│          │   (Gateway)    │                           │
│          └────────┬───────┘                           │
│                   │                                   │
│      ┌────────────┼────────────┐                     │
│      │            │             │                     │
│  ┌───▼──┐    ┌───▼──┐    ┌────▼────┐                │
│  │ CLS  │    │ APM  │    │  TMP    │                │
│  └──────┘    └──────┘    └─────────┘                │
└───────────────────────────────────────────────────────┘
```

### 2. TKE (腾讯云K8s) DaemonSet

```yaml
# otel-collector-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: kube-system
spec:
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
        image: ccr.ccs.tencentyun.com/otel/opentelemetry-collector-contrib:latest
        env:
        - name: TENCENT_SECRET_ID
          valueFrom:
            secretKeyRef:
              name: tencent-credentials
              key: secret-id
        - name: TENCENT_SECRET_KEY
          valueFrom:
            secretKeyRef:
              name: tencent-credentials
              key: secret-key
        - name: TMP_TOKEN
          valueFrom:
            secretKeyRef:
              name: tmp-token
              key: token
        resources:
          limits:
            cpu: 500m
            memory: 512Mi
          requests:
            cpu: 200m
            memory: 256Mi
        volumeMounts:
        - name: config
          mountPath: /etc/otel
      volumes:
      - name: config
        configMap:
          name: otel-collector-config
```

### 3. 分层部署

```text
┌─────────────────────────────────────────────┐
│              应用Pod                         │
│  ┌───────────┐  ┌───────────┐              │
│  │    App    │  │ Sidecar   │              │
│  │           │  │ Collector │              │
│  └───────────┘  └─────┬─────┘              │
│                        │                     │
└────────────────────────┼─────────────────────┘
                         │
┌────────────────────────▼─────────────────────┐
│           Node-Level Collector               │
│        (DaemonSet, 基础处理)                 │
└────────────────────────┬─────────────────────┘
                         │
┌────────────────────────▼─────────────────────┐
│       Cluster-Level Collector                │
│   (Deployment, 高级处理+采样)                │
└────────────────────────┬─────────────────────┘
                         │
┌────────────────────────▼─────────────────────┐
│              腾讯云服务                       │
│   CLS  │  APM  │  TMP                        │
└─────────────────────────────────────────────┘
```

---

## 💰 成本优化

### CLS成本分析

#### 计费项

| 项目 | 单价 (华南-广州) | 说明 |
|-----|-----------------|------|
| **索引流量** | ¥0.35/GB | 主要成本 |
| **写入流量** | ¥0.032/GB | 数据写入 |
| **存储** | ¥0.0115/GB/天 | 日志存储 |
| **外网读取** | ¥0.5/GB | 外网下载 |
| **内网读取** | 免费 | VPC内网 |

#### 优化策略

##### 1. 启用压缩 (节省60-70%)

```yaml
exporters:
  kafka/cls:
    compression: gzip  # 或 snappy, lz4, zstd
```

##### 2. 智能采样 (节省90%+)

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    policies:
      # 保留所有错误
      - name: errors-always
        type: status_code
        status_code: {status_codes: [ERROR]}
      
      # 保留慢请求 (>1s)
      - name: slow-requests
        type: latency
        latency: {threshold_ms: 1000}
      
      # 重要服务100%采样
      - name: critical-services
        type: string_attribute
        string_attribute:
          key: service.name
          values: [payment-service, auth-service]
      
      # 其他10%采样
      - name: probabilistic-10pct
        type: probabilistic
        probabilistic: {sampling_percentage: 10}
```

##### 3. 生命周期管理

```text
CLS控制台 → 日志主题 → 高级配置

存储策略:
- 标准存储: 7天 (快速检索)
- 低频存储: 30天 (降频访问,成本50%↓)
- 归档存储: 90天 (冷数据,成本80%↓)
- 超过90天: 删除
```

##### 4. 索引优化

```text
仅对必要字段建立索引:

✅ 必建:
  - service.name
  - trace_id
  - span_id
  - status.code
  - http.method
  - http.route

❌ 不建 (高基数):
  - http.url (完整URL)
  - user.id
  - request.id
  - timestamp
```

#### 成本计算示例

```text
场景:
- 100个微服务
- 平均QPS: 1000 req/s
- 每Trace: 8 Spans
- 每Span原始大小: 2KB

无优化:
  月数据量 = 1000 * 8 * 2KB * 86400 * 30 = 41.5 TB
  索引流量 = 41.5 TB * ¥0.35/GB = ¥14,860/月
  写入流量 = 41.5 TB * ¥0.032/GB = ¥1,360/月
  存储 (30天平均) = 41.5 TB * 15天 * ¥0.0115/GB = ¥7,312/月
  总成本 = ¥23,532/月

优化后 (采样10% + 压缩70% + 索引50% + 7天热+30天冷):
  月数据量 = 41.5 TB * 10% * 30% = 1.245 TB
  索引流量 = 1.245 TB * 50% * ¥0.35/GB = ¥223/月
  写入流量 = 1.245 TB * ¥0.032/GB = ¥41/月
  存储 (7天标准+23天低频) = 1.245TB * (7*¥0.0115 + 23*¥0.005)/GB = ¥243/月
  总成本 = ¥507/月

节省 = ¥23,532 - ¥507 = ¥23,025/月 (97.8%!) 🔥
```

### APM成本优化

APM按Span数量计费:

```text
基础版: ¥0.01/万Span
标准版: ¥0.02/万Span (含高级功能)

优化策略:
✅ 使用Tail Sampling (节省90%)
✅ 过滤健康检查等噪音 (节省10-20%)
✅ 合并短Span (节省5-10%)
```

---

## 🔍 故障排查

### 常见问题

#### 1. CLS Kafka连接失败

**症状**:

```text
Error: kafka: client has run out of available brokers
Error: dial tcp: i/o timeout
```

**排查步骤**:

```bash
# 1. 检查网络连通性
telnet ${CLS_KAFKA_ENDPOINT} 9096

# 2. 检查VPC配置
# CLS Kafka只能通过内网访问,确保Collector在腾讯云VPC内

# 3. 检查认证信息
echo "SecretId: $TENCENT_SECRET_ID"
echo "SecretKey: (hidden)"

# 4. 查看Collector日志
kubectl logs -n kube-system otel-collector-xxx | grep kafka
```

**解决方案**:

- ✅ 确保Collector部署在腾讯云VPC内
- ✅ 使用正确的Kafka Endpoint (从CLS控制台获取)
- ✅ 验证SecretId/SecretKey

#### 2. APM Token认证失败

**症状**:

```text
Error: rpc error: code = Unauthenticated desc = invalid token
```

**解决方案**:

```yaml
exporters:
  otlp/apm:
    endpoint: "apm.tencentcs.com:4317"
    headers:
      # 确保Token格式正确
      Authorization: "Bearer ${TENCENT_APM_TOKEN}"
```

检查Token:

```bash
# 从APM控制台重新获取Token
# 控制台路径: APM → 接入设置 → 获取Token
```

#### 3. TMP远程写入失败

**症状**:

```text
Error: remote write failed: 400 Bad Request
```

**排查步骤**:

```bash
# 1. 测试TMP连通性
curl -v -X POST "http://tmp-xxx.tencentcs.com/api/v1/write" \
  -H "Authorization: Bearer ${TMP_TOKEN}" \
  -H "Content-Type: application/x-protobuf" \
  --data-binary @test.pb

# 2. 查看Collector指标
curl http://localhost:8888/metrics | grep prometheusremotewrite

# 3. 查看TMP控制台错误日志
```

**解决方案**:

- ✅ 确认Endpoint正确 (包含/api/v1/write)
- ✅ 检查Token有效性
- ✅ 确保数据格式正确 (Prometheus Remote Write格式)

#### 4. 数据延迟高

**优化措施**:

```yaml
processors:
  batch:
    timeout: 5s          # 减小批处理间隔
    send_batch_size: 512  # 减小批次大小

exporters:
  kafka/cls:
    # 使用内网Endpoint
    brokers: ["${CLS_KAFKA_INTERNAL_ENDPOINT}"]
    # 增加并发
    producer:
      max_message_bytes: 1000000
      required_acks: 1  # 不等待所有副本确认
      compression: lz4  # 更快的压缩算法
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **腾讯云CLS文档** | <https://cloud.tencent.com/document/product/614> |
| **APM文档** | <https://cloud.tencent.com/document/product/1463> |
| **TMP文档** | <https://cloud.tencent.com/document/product/1416> |
| **OTLP集成指南** | <https://cloud.tencent.com/document/product/614/76458> |

---

## 🎯 最佳实践总结

```text
✅ 使用腾讯云内网Endpoint (降低延迟和成本)
✅ 启用压缩 (gzip/snappy/lz4)
✅ 配置智能采样 (100%错误+慢请求, 10%正常)
✅ 精简CLS索引字段
✅ 设置生命周期 (7天标准+30天低频+90天归档)
✅ 使用环境变量管理密钥
✅ 在VPC内部署Collector Gateway
✅ 监控Collector自身健康
✅ 定期审查成本和优化
✅ 重要服务100%采样,其他服务采样
```

---

**最后更新**: 2025年10月9日  
**适用区域**: 中国大陆 (ap-guangzhou, ap-shanghai, ap-beijing等)  
**上一篇**: [阿里云OTLP集成指南](./01_阿里云OTLP集成指南.md)  
**下一篇**: [华为云OTLP集成指南](./03_华为云OTLP集成指南.md)

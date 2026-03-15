# 🇨🇳 华为云OpenTelemetry集成指南

> **华为云服务**: LTS, APM, AOM  
> **OTLP版本**: v1.3.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [🇨🇳 华为云OpenTelemetry集成指南](#-华为云opentelemetry集成指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [华为云可观测性服务](#华为云可观测性服务)
    - [集成架构](#集成架构)
    - [为什么选择华为云 + OTLP?](#为什么选择华为云--otlp)
  - [📊 LTS日志服务集成](#-lts日志服务集成)
    - [概述](#概述)
    - [前置准备](#前置准备)
    - [Collector配置](#collector配置)
    - [SDK集成](#sdk集成)
      - [Go SDK](#go-sdk)
      - [Java SDK (Spring Boot)](#java-sdk-spring-boot)
      - [Python SDK](#python-sdk)
    - [LTS检索语法](#lts检索语法)
      - [基础检索](#基础检索)
      - [SQL分析](#sql分析)
  - [🚀 APM应用性能管理集成](#-apm应用性能管理集成)
    - [概述1](#概述1)
    - [前置准备1](#前置准备1)
    - [Collector配置1](#collector配置1)
    - [SDK直接集成](#sdk直接集成)
    - [APM功能](#apm功能)
      - [1. 链路追踪](#1-链路追踪)
      - [2. 应用性能](#2-应用性能)
  - [📈 AOM应用运维管理集成](#-aom应用运维管理集成)
    - [概述2](#概述2)
    - [Collector配置2](#collector配置2)
    - [Grafana集成](#grafana集成)
      - [配置AOM数据源](#配置aom数据源)
      - [常用PromQL](#常用promql)
  - [🏗️ 架构最佳实践](#️-架构最佳实践)
    - [1. 华为云CCE (K8s) DaemonSet](#1-华为云cce-k8s-daemonset)
    - [2. 混合云部署](#2-混合云部署)
    - [3. 多Region部署](#3-多region部署)
  - [💰 成本优化](#-成本优化)
    - [LTS成本分析](#lts成本分析)
      - [计费项](#计费项)
      - [优化策略](#优化策略)
        - [1. 启用压缩 (节省65%+)](#1-启用压缩-节省65)
        - [2. 采样策略 (节省90%+)](#2-采样策略-节省90)
        - [3. 生命周期管理](#3-生命周期管理)
      - [成本示例](#成本示例)
  - [🔍 故障排查](#-故障排查)
    - [常见问题](#常见问题)
      - [1. LTS认证失败](#1-lts认证失败)
      - [2. APM连接超时](#2-apm连接超时)
      - [3. 数据延迟高](#3-数据延迟高)
  - [📚 参考资源](#-参考资源)
  - [🎯 最佳实践总结](#-最佳实践总结)

---

## 🎯 概述

### 华为云可观测性服务

| 服务 | 用途 | OTLP支持 | 推荐场景 |
|-----|------|----------|---------|
| **LTS (日志服务)** | 日志收集、检索、分析 | ✅ Native | 日志统一管理 |
| **APM (应用性能管理)** | 链路追踪、调用分析 | ✅ Native | 微服务监控 |
| **AOM (应用运维管理)** | 指标监控、告警 | ✅ Native | 云原生监控 |
| **CCE (容器引擎)** | K8s容器编排 | ⚠️ 间接 | 容器环境 |

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
│  │ (OTLP)      │  │ (Batch,     │  │ (LTS, APM,  │ │
│  │             │  │  Filter)    │  │  AOM)       │ │
│  └─────────────┘  └─────────────┘  └──────┬──────┘ │
└────────────────────────────────────────────┼────────┘
                                              │
┌─────────────────────────────────────────────▼────────┐
│                    华为云服务                         │
│  ┌──────────────┐  ┌──────────────┐  ┌────────────┐│
│  │     LTS      │  │     APM      │  │    AOM     ││
│  │  (日志服务)   │  │  (应用性能)   │  │  (运维)    ││
│  └──────────────┘  └──────────────┘  └────────────┘│
└───────────────────────────────────────────────────────┘
```

### 为什么选择华为云 + OTLP?

| 优势 | 说明 |
|-----|------|
| **政企首选** | 国产替代,适合政府和大型企业 |
| **安全合规** | 满足等保要求和数据本地化 |
| **5G边缘** | 优秀的5G和边缘计算能力 |
| **全栈云** | 完整的IaaS/PaaS/SaaS解决方案 |
| **欧拉系统** | 适配国产openEuler操作系统 |

---

## 📊 LTS日志服务集成

### 概述

华为云日志服务 (LTS - Log Tank Service) 支持通过HTTP API接收OTLP数据。

### 前置准备

1. **创建日志组和日志流**

   ```text
   控制台路径: 日志服务 LTS → 日志管理
   - 日志组: my-observability-group
   - 日志流: otlp-logs
   - 区域: cn-north-4 (北京四)
   ```

2. **获取访问凭证**
   - AK (Access Key)
   - SK (Secret Key)
   - Project ID

### Collector配置

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
        value: huawei_cloud
        action: upsert
      - key: cloud.region
        value: cn-north-4
        action: upsert

exporters:
  # LTS HTTP API导出器
  huaweicloud_lts:
    endpoint: "https://lts.cn-north-4.myhuaweicloud.com"
    project_id: "${HUAWEI_PROJECT_ID}"
    log_group_id: "${LTS_LOG_GROUP_ID}"
    log_stream_id: "${LTS_LOG_STREAM_ID}"
    access_key: "${HUAWEI_ACCESS_KEY}"
    secret_key: "${HUAWEI_SECRET_KEY}"
    # 可选: 指定Region
    region: "cn-north-4"

service:
  pipelines:
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [huaweicloud_lts]
    
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [huaweicloud_lts]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [huaweicloud_lts]
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
    sdklog "go.opentelemetry.io/otel/sdk/log"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func initLogger() (*sdklog.LoggerProvider, error) {
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
            semconv.ServiceName("my-huawei-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
            semconv.CloudProvider("huawei_cloud"),
            semconv.CloudRegion("cn-north-4"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 创建LoggerProvider
    lp := sdklog.NewLoggerProvider(
        sdklog.WithProcessor(sdklog.NewBatchProcessor(exporter,
            sdklog.WithBatchTimeout(5*time.Second),
        )),
        sdklog.WithResource(res),
    )

    return lp, nil
}

func main() {
    lp, err := initLogger()
    if err != nil {
        log.Fatal(err)
    }
    defer lp.Shutdown(context.Background())

    // 使用Logger记录日志
    logger := lp.Logger("my-service")
    
    logger.Info("Application started on Huawei Cloud",
        sdklog.String("region", "cn-north-4"),
        sdklog.String("availability_zone", "cn-north-4a"),
    )

    time.Sleep(2 * time.Second)
}
```

#### Java SDK (Spring Boot)

```java
import io.opentelemetry.api.GlobalOpenTelemetry;
import io.opentelemetry.exporter.otlp.logs.OtlpGrpcLogRecordExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.logs.SdkLoggerProvider;
import io.opentelemetry.sdk.logs.export.BatchLogRecordProcessor;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.semconv.resource.attributes.ResourceAttributes;

@Configuration
public class HuaweiCloudOTLPConfig {
    
    @Bean
    public OpenTelemetrySdk openTelemetrySdk() {
        // 创建Resource
        Resource resource = Resource.getDefault()
            .merge(Resource.create(Attributes.of(
                ResourceAttributes.SERVICE_NAME, "my-spring-service",
                ResourceAttributes.SERVICE_VERSION, "1.0.0",
                ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production",
                ResourceAttributes.CLOUD_PROVIDER, "huawei_cloud",
                ResourceAttributes.CLOUD_REGION, "cn-north-4"
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
                    .setMaxExportBatchSize(1024)
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
        ResourceAttributes.CLOUD_PROVIDER: "huawei_cloud",
        ResourceAttributes.CLOUD_REGION: "cn-north-4",
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
    logger.info("Application running on Huawei Cloud", 
                {"region": "cn-north-4", "zone": "cn-north-4a"})
    time.sleep(2)

if __name__ == "__main__":
    main()
```

### LTS检索语法

#### 基础检索

```text
# 全文检索
"error" AND "timeout"

# 字段检索
service.name:"my-service" AND status.code:"ERROR"

# 范围检索
duration:[500 TO 1000]

# 通配符
http.url:*/api/users/*

# 正则表达式
message:/error|exception|failure/i
```

#### SQL分析

```sql
-- 错误率统计
SELECT service_name, 
       COUNT(CASE WHEN status_code = 'ERROR' THEN 1 END) * 100.0 / COUNT(*) as error_rate
FROM otlp_logs
GROUP BY service_name
ORDER BY error_rate DESC
LIMIT 10;

-- P99延迟
SELECT approx_percentile(duration, 0.99) as p99_latency
FROM otlp_logs
WHERE __time__ >= NOW() - INTERVAL '1' HOUR;

-- 热门接口
SELECT http_route, COUNT(*) as request_count
FROM otlp_logs
GROUP BY http_route
ORDER BY request_count DESC
LIMIT 20;
```

---

## 🚀 APM应用性能管理集成

### 概述1

华为云APM提供分布式链路追踪、性能分析等APM能力。

### 前置准备1

1. **开通APM服务**
2. **创建应用**
3. **获取接入点**
   - Region: `cn-north-4`
   - Token: 从控制台获取

### Collector配置1

```yaml
exporters:
  otlp/apm:
    endpoint: "apm-access.cn-north-4.myhuaweicloud.com:4317"
    headers:
      # 华为云APM Token
      X-HW-APM-Token: "${HUAWEI_APM_TOKEN}"
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
// Go SDK直接导出到华为云APM
exporter, err := otlptracegrpc.New(
    ctx,
    otlptracegrpc.WithEndpoint("apm-access.cn-north-4.myhuaweicloud.com:4317"),
    otlptracegrpc.WithHeaders(map[string]string{
        "X-HW-APM-Token": os.Getenv("HUAWEI_APM_TOKEN"),
    }),
    otlptracegrpc.WithCompressor("gzip"),
)
```

### APM功能

#### 1. 链路追踪

- **全链路追踪**: 可视化完整调用链
- **拓扑图**: 自动生成服务拓扑
- **慢调用分析**: 识别性能瓶颈
- **异常追踪**: 快速定位错误

#### 2. 应用性能

```text
应用概览:
┌──────────────────────────────┐
│ 平均响应时间: 145ms          │
│ 错误率: 0.32%                │
│ 吞吐量: 1,250 req/s          │
│ 活跃实例: 12个               │
└──────────────────────────────┘

慢事务TOP 5:
1. POST /api/orders/create   - 1.8s
2. GET /api/report/generate  - 1.2s
3. POST /api/batch/import    - 950ms
4. GET /api/search           - 680ms
5. PUT /api/data/sync        - 520ms
```

---

## 📈 AOM应用运维管理集成

### 概述2

华为云AOM (Application Operations Management) 提供指标监控、日志分析、告警等运维能力。

### Collector配置2

```yaml
exporters:
  # AOM Prometheus远程写入
  prometheusremotewrite/aom:
    endpoint: "https://aom-access.cn-north-4.myhuaweicloud.com/prometheus/write"
    headers:
      X-AK: "${HUAWEI_ACCESS_KEY}"
      X-SK: "${HUAWEI_SECRET_KEY}"
      X-Project-Id: "${HUAWEI_PROJECT_ID}"
    resource_to_telemetry_conversion:
      enabled: true
    compression: snappy

service:
  pipelines:
    metrics:
      receivers: [otlp, prometheus]
      processors: [batch, filter]
      exporters: [prometheusremotewrite/aom]
```

### Grafana集成

#### 配置AOM数据源

```yaml
apiVersion: 1

datasources:
  - name: HuaweiCloud AOM
    type: prometheus
    access: proxy
    url: https://aom-access.cn-north-4.myhuaweicloud.com/prometheus
    jsonData:
      httpHeaderName1: 'X-Project-Id'
    secureJsonData:
      httpHeaderValue1: '${HUAWEI_PROJECT_ID}'
```

#### 常用PromQL

```promql
# 应用QPS
sum(rate(http_server_request_duration_count{service_name="my-service"}[1m]))

# P99延迟
histogram_quantile(0.99, 
  sum by(le) (rate(http_server_request_duration_bucket[5m]))
)

# CPU使用率
100 - (avg by(instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)

# 内存使用率
(1 - (node_memory_MemAvailable_bytes / node_memory_MemTotal_bytes)) * 100

# 错误率趋势
sum(rate(http_server_request_duration_count{http_status_code=~"5.."}[1m])) 
/ sum(rate(http_server_request_duration_count[1m])) * 100
```

---

## 🏗️ 架构最佳实践

### 1. 华为云CCE (K8s) DaemonSet

```yaml
# otel-collector-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: otel-system
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
        image: swr.cn-north-4.myhuaweicloud.com/otel/opentelemetry-collector-contrib:latest
        env:
        - name: HUAWEI_ACCESS_KEY
          valueFrom:
            secretKeyRef:
              name: huawei-credentials
              key: access-key
        - name: HUAWEI_SECRET_KEY
          valueFrom:
            secretKeyRef:
              name: huawei-credentials
              key: secret-key
        - name: HUAWEI_PROJECT_ID
          value: "xxxxxxxxxxxxx"
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

### 2. 混合云部署

```text
┌──────────────────────────────────────────────────────┐
│                   本地IDC / 其他云                    │
│  ┌───────┐  ┌───────┐  ┌───────┐                    │
│  │  App  │  │  App  │  │  App  │                    │
│  └───┬───┘  └───┬───┘  └───┬───┘                    │
│      │          │          │                         │
│      └──────────┼──────────┘                         │
│                 │                                     │
│         ┌───────▼──────┐                             │
│         │  Collector   │                             │
│         │  (Agent)     │                             │
│         └──────┬───────┘                             │
│                │ 云专线/VPN                           │
└────────────────┼──────────────────────────────────────┘
                 │
┌────────────────▼──────────────────────────────────────┐
│                  华为云VPC                             │
│          ┌────────────────┐                           │
│          │   Collector    │                           │
│          │   (Gateway)    │                           │
│          └────────┬───────┘                           │
│                   │                                   │
│      ┌────────────┼────────────┐                     │
│      │            │             │                     │
│  ┌───▼──┐    ┌───▼──┐    ┌────▼────┐                │
│  │ LTS  │    │ APM  │    │  AOM    │                │
│  └──────┘    └──────┘    └─────────┘                │
└───────────────────────────────────────────────────────┘
```

### 3. 多Region部署

```yaml
# 华为云多Region配置
exporters:
  # 北京四
  huaweicloud_lts/beijing:
    endpoint: "https://lts.cn-north-4.myhuaweicloud.com"
    region: "cn-north-4"
    # ...其他配置
  
  # 上海二
  huaweicloud_lts/shanghai:
    endpoint: "https://lts.cn-east-2.myhuaweicloud.com"
    region: "cn-east-2"
    # ...其他配置

service:
  pipelines:
    logs/beijing:
      receivers: [otlp]
      processors: [batch, filter/beijing]
      exporters: [huaweicloud_lts/beijing]
    
    logs/shanghai:
      receivers: [otlp]
      processors: [batch, filter/shanghai]
      exporters: [huaweicloud_lts/shanghai]
```

---

## 💰 成本优化

### LTS成本分析

#### 计费项

| 项目 | 单价 (华北-北京四) | 说明 |
|-----|------------------|------|
| **索引流量** | ¥0.35/GB | 建立索引的数据 |
| **写入流量** | ¥0.03/GB | 原始数据写入 |
| **存储** | ¥0.012/GB/天 | 日志存储 |
| **公网流量** | ¥0.8/GB | 公网下载 |

#### 优化策略

##### 1. 启用压缩 (节省65%+)

```yaml
exporters:
  huaweicloud_lts:
    compression: gzip  # 或 zstd
```

##### 2. 采样策略 (节省90%+)

```yaml
processors:
  tail_sampling:
    decision_wait: 10s
    policies:
      # 保留所有错误
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      
      # 保留慢请求
      - name: slow
        type: latency
        latency: {threshold_ms: 500}
      
      # 其他10%采样
      - name: normal
        type: probabilistic
        probabilistic: {sampling_percentage: 10}
```

##### 3. 生命周期管理

```text
LTS控制台配置:
- 标准存储: 7天
- 低频存储: 30天 (成本降低50%)
- 删除: 超过30天
```

#### 成本示例

```text
场景:
- 微服务: 50个
- QPS: 500 req/s
- 每Trace: 10 Spans
- 每Span: 2KB

无优化:
  月数据量 = 500 * 10 * 2KB * 86400 * 30 = 25.92 TB
  索引流量 = 25.92 TB * ¥0.35/GB = ¥9,292/月
  写入流量 = 25.92 TB * ¥0.03/GB = ¥796/月
  存储 (30天) = 25.92 TB * 15天 * ¥0.012/GB = ¥4,771/月
  总成本 = ¥14,859/月

优化后 (采样10% + 压缩70% + 7天存储):
  月数据量 = 25.92 TB * 10% * 30% = 0.78 TB
  索引流量 = 0.78 TB * ¥0.35/GB = ¥279/月
  写入流量 = 0.78 TB * ¥0.03/GB = ¥24/月
  存储 (7天) = 0.78 TB * 3.5天 * ¥0.012/GB = ¥33/月
  总成本 = ¥336/月

节省 = ¥14,859 - ¥336 = ¥14,523/月 (97.7%!) 🔥
```

---

## 🔍 故障排查

### 常见问题

#### 1. LTS认证失败

**症状**:

```text
Error: 401 Unauthorized
Error: Invalid AK/SK
```

**解决方案**:

```bash
# 1. 验证AK/SK
echo "AK: $HUAWEI_ACCESS_KEY"
echo "Project ID: $HUAWEI_PROJECT_ID"

# 2. 检查IAM权限
# 确保AK/SK拥有LTS写入权限

# 3. 测试LTS API
curl -X POST "https://lts.cn-north-4.myhuaweicloud.com/v2/${HUAWEI_PROJECT_ID}/groups/${LOG_GROUP_ID}/streams/${LOG_STREAM_ID}/logs" \
  -H "X-Auth-Token: ${TOKEN}" \
  -H "Content-Type: application/json" \
  -d '{"logs":[{"content":"test"}]}'
```

#### 2. APM连接超时

**症状**:

```text
Error: context deadline exceeded
Error: dial tcp: i/o timeout
```

**排查步骤**:

```bash
# 1. 检查网络连通性
telnet apm-access.cn-north-4.myhuaweicloud.com 4317

# 2. 检查VPC配置
# 确保Collector在华为云VPC内,或配置了公网NAT

# 3. 查看Collector日志
kubectl logs -n otel-system otel-collector-xxx | grep -i error

# 4. 测试gRPC连接
grpcurl -plaintext \
  -H "X-HW-APM-Token: ${HUAWEI_APM_TOKEN}" \
  apm-access.cn-north-4.myhuaweicloud.com:4317 list
```

#### 3. 数据延迟高

**优化措施**:

```yaml
# 1. 使用内网Endpoint (延迟降低70%+)
exporters:
  huaweicloud_lts:
    endpoint: "https://lts-internal.cn-north-4.myhuaweicloud.com"

# 2. 增加批处理频率
processors:
  batch:
    timeout: 5s        # 从10s降至5s
    send_batch_size: 512  # 从1024降至512

# 3. 减少Processor数量
service:
  pipelines:
    logs:
      processors: [batch]  # 精简Pipeline
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **华为云LTS文档** | <https://support.huaweicloud.com/lts/index.html> |
| **APM文档** | <https://support.huaweicloud.com/apm/index.html> |
| **AOM文档** | <https://support.huaweicloud.com/aom/index.html> |
| **CCE文档** | <https://support.huaweicloud.com/cce/index.html> |

---

## 🎯 最佳实践总结

```text
✅ 使用华为云内网Endpoint (降低延迟+成本)
✅ 启用压缩 (gzip/zstd)
✅ 配置智能采样 (100%错误, 10%正常)
✅ 精简LTS索引字段
✅ 设置生命周期 (7天标准+30天低频)
✅ 使用IAM进行权限管理
✅ 在VPC内部署Collector Gateway
✅ 监控Collector健康
✅ 定期审查成本
✅ 适配国产化环境 (openEuler)
```

---

**最后更新**: 2025年10月9日  
**适用区域**: 中国大陆 (cn-north-4, cn-east-2, cn-south-1等)  
**上一篇**: [腾讯云OTLP集成指南](./02_腾讯云OTLP集成指南.md)  
**系列完成**: 国内三大云平台集成指南全部完成! 🎉

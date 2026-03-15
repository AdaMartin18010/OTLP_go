# 🇨🇳 阿里云OpenTelemetry集成指南

> **阿里云服务**: SLS, ARMS, Prometheus  
> **OTLP版本**: v1.3.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [🇨🇳 阿里云OpenTelemetry集成指南](#-阿里云opentelemetry集成指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [阿里云可观测性服务](#阿里云可观测性服务)
    - [集成架构](#集成架构)
    - [为什么使用OTLP?](#为什么使用otlp)
  - [📊 SLS日志服务集成](#-sls日志服务集成)
    - [概述](#概述)
    - [前置准备](#前置准备)
    - [Collector配置](#collector配置)
      - [完整配置示例](#完整配置示例)
    - [SDK集成](#sdk集成)
      - [Go SDK](#go-sdk)
      - [Java SDK](#java-sdk)
      - [Python SDK](#python-sdk)
    - [SLS查询和分析](#sls查询和分析)
      - [查询Traces](#查询traces)
      - [查询Metrics](#查询metrics)
  - [🚀 ARMS应用监控集成](#-arms应用监控集成)
    - [概述1](#概述1)
    - [前置准备1](#前置准备1)
    - [Collector配置1](#collector配置1)
    - [直接从SDK导出到ARMS](#直接从sdk导出到arms)
    - [ARMS链路追踪](#arms链路追踪)
      - [查看链路拓扑](#查看链路拓扑)
      - [查询Traces1](#查询traces1)
  - [📈 Prometheus监控集成](#-prometheus监控集成)
    - [阿里云Prometheus监控](#阿里云prometheus监控)
    - [Collector配置2](#collector配置2)
    - [Grafana可视化](#grafana可视化)
      - [配置数据源](#配置数据源)
      - [常用PromQL查询](#常用promql查询)
  - [🏗️ 架构最佳实践](#️-架构最佳实践)
    - [1. 混合云部署架构](#1-混合云部署架构)
    - [2. K8s DaemonSet模式](#2-k8s-daemonset模式)
    - [3. 多后端导出](#3-多后端导出)
  - [💰 成本优化](#-成本优化)
    - [SLS成本分析](#sls成本分析)
      - [计费项目](#计费项目)
      - [成本优化策略](#成本优化策略)
        - [1. 启用压缩 (节省60-70%)](#1-启用压缩-节省60-70)
        - [2. 采样 (节省90%+)](#2-采样-节省90)
        - [3. 精简索引 (节省50-80%)](#3-精简索引-节省50-80)
        - [4. 设置数据生命周期](#4-设置数据生命周期)
      - [成本计算示例](#成本计算示例)
  - [🔍 故障排查](#-故障排查)
    - [常见问题](#常见问题)
      - [1. 数据未到达SLS](#1-数据未到达sls)
      - [2. ARMS Token认证失败](#2-arms-token认证失败)
      - [3. 高延迟问题](#3-高延迟问题)
  - [📚 参考资源](#-参考资源)
  - [🎯 最佳实践总结](#-最佳实践总结)

---

## 🎯 概述

### 阿里云可观测性服务

| 服务 | 用途 | OTLP支持 | 推荐场景 |
|-----|------|----------|---------|
| **SLS (日志服务)** | 日志收集、分析、告警 | ✅ Native | 日志中心化 |
| **ARMS (应用监控)** | APM、链路追踪、实时监控 | ✅ Native | 应用性能监控 |
| **Prometheus监控** | 时序数据、指标监控 | ✅ Native | 云原生监控 |
| **Cloud Monitor** | 基础设施监控 | ⚠️ 通过Exporter | 云资源监控 |

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
│  │ (OTLP)      │  │ (Batch,     │  │ (SLS, ARMS, │ │
│  │             │  │  Filter)    │  │  Prometheus)│ │
│  └─────────────┘  └─────────────┘  └──────┬──────┘ │
└────────────────────────────────────────────┼────────┘
                                              │
┌─────────────────────────────────────────────▼────────┐
│                    阿里云服务                         │
│  ┌──────────────┐  ┌──────────────┐  ┌────────────┐│
│  │     SLS      │  │     ARMS     │  │ Prometheus ││
│  │  (日志服务)   │  │  (应用监控)   │  │  (监控)    ││
│  └──────────────┘  └──────────────┘  └────────────┘│
└───────────────────────────────────────────────────────┘
```

### 为什么使用OTLP?

| 优势 | 说明 |
|-----|------|
| **统一标准** | 一套代码,多个后端 |
| **厂商中立** | 避免厂商锁定 |
| **高性能** | gRPC + Protobuf,低延迟 |
| **灵活切换** | 轻松切换或多后端导出 |
| **云原生** | K8s、微服务友好 |

---

## 📊 SLS日志服务集成

### 概述

阿里云日志服务 (SLS) 原生支持OTLP协议,可直接接收Traces、Metrics和Logs数据。

### 前置准备

1. **创建SLS Project和Logstore**

   ```bash
   # 通过阿里云控制台创建
   Project: my-observability-project
   Logstore: otlp-logs
   ```

2. **获取访问凭证**
   - AccessKey ID
   - AccessKey Secret
   - Project所在Region

### Collector配置

#### 完整配置示例

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
        value: alibaba_cloud
        action: upsert
      - key: cloud.region
        value: cn-hangzhou
        action: upsert

exporters:
  # SLS Logs导出器
  alibabacloud_logservice/logs:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    project: "my-observability-project"
    logstore: "otlp-logs"
    access_key_id: "${ALIYUN_ACCESS_KEY_ID}"
    access_key_secret: "${ALIYUN_ACCESS_KEY_SECRET}"
  
  # SLS Traces导出器
  alibabacloud_logservice/traces:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    project: "my-observability-project"
    logstore: "otlp-traces"
    access_key_id: "${ALIYUN_ACCESS_KEY_ID}"
    access_key_secret: "${ALIYUN_ACCESS_KEY_SECRET}"
  
  # SLS Metrics导出器
  alibabacloud_logservice/metrics:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    project: "my-observability-project"
    logstore: "otlp-metrics"
    access_key_id: "${ALIYUN_ACCESS_KEY_ID}"
    access_key_secret: "${ALIYUN_ACCESS_KEY_SECRET}"

service:
  pipelines:
    logs:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [alibabacloud_logservice/logs]
    
    traces:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [alibabacloud_logservice/traces]
    
    metrics:
      receivers: [otlp]
      processors: [memory_limiter, resource, batch]
      exporters: [alibabacloud_logservice/metrics]
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
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func initTracer() (*trace.TracerProvider, error) {
    ctx := context.Background()

    // 创建OTLP exporter
    exporter, err := otlptracegrpc.New(
        ctx,
        otlptracegrpc.WithEndpoint("collector.example.com:4317"),
        otlptracegrpc.WithInsecure(), // 生产环境使用TLS
    )
    if err != nil {
        return nil, err
    }

    // 创建Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("my-golang-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
            semconv.CloudProvider("alibaba_cloud"),
            semconv.CloudRegion("cn-hangzhou"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 创建TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter,
            trace.WithMaxExportBatchSize(1024),
            trace.WithBatchTimeout(5*time.Second),
        ),
        trace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

func main() {
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 使用Tracer
    tracer := otel.Tracer("my-service")
    ctx := context.Background()

    _, span := tracer.Start(ctx, "main-operation")
    defer span.End()

    // 业务逻辑
    log.Println("Application is running...")
    time.Sleep(2 * time.Second)
}
```

#### Java SDK

```java
import io.opentelemetry.api.GlobalOpenTelemetry;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.exporter.otlp.trace.OtlpGrpcSpanExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.semconv.resource.attributes.ResourceAttributes;

public class AliyunOTLPExample {
    
    public static OpenTelemetrySdk initOpenTelemetry() {
        // 创建Resource
        Resource resource = Resource.getDefault()
            .merge(Resource.create(Attributes.of(
                ResourceAttributes.SERVICE_NAME, "my-java-service",
                ResourceAttributes.SERVICE_VERSION, "1.0.0",
                ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production",
                ResourceAttributes.CLOUD_PROVIDER, "alibaba_cloud",
                ResourceAttributes.CLOUD_REGION, "cn-hangzhou"
            )));

        // 创建OTLP exporter
        OtlpGrpcSpanExporter spanExporter = OtlpGrpcSpanExporter.builder()
            .setEndpoint("http://collector.example.com:4317")
            .setTimeout(Duration.ofSeconds(30))
            .build();

        // 创建TracerProvider
        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
            .addSpanProcessor(BatchSpanProcessor.builder(spanExporter)
                .setMaxExportBatchSize(1024)
                .setScheduleDelay(Duration.ofSeconds(5))
                .build())
            .setResource(resource)
            .build();

        // 创建OpenTelemetry SDK
        OpenTelemetrySdk openTelemetry = OpenTelemetrySdk.builder()
            .setTracerProvider(tracerProvider)
            .buildAndRegisterGlobal();

        return openTelemetry;
    }

    public static void main(String[] args) throws InterruptedException {
        OpenTelemetrySdk openTelemetry = initOpenTelemetry();
        Tracer tracer = openTelemetry.getTracer("my-service");

        // 创建Span
        Span span = tracer.spanBuilder("main-operation").startSpan();
        try (Scope scope = span.makeCurrent()) {
            // 业务逻辑
            System.out.println("Application is running...");
            Thread.sleep(2000);
        } finally {
            span.end();
        }

        // 关闭
        openTelemetry.getSdkTracerProvider().shutdown();
    }
}
```

#### Python SDK

```python
import time
from opentelemetry import trace
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.semconv.resource import ResourceAttributes

def init_tracer():
    # 创建Resource
    resource = Resource.create({
        ResourceAttributes.SERVICE_NAME: "my-python-service",
        ResourceAttributes.SERVICE_VERSION: "1.0.0",
        ResourceAttributes.DEPLOYMENT_ENVIRONMENT: "production",
        ResourceAttributes.CLOUD_PROVIDER: "alibaba_cloud",
        ResourceAttributes.CLOUD_REGION: "cn-hangzhou",
    })

    # 创建OTLP exporter
    otlp_exporter = OTLPSpanExporter(
        endpoint="collector.example.com:4317",
        insecure=True,  # 生产环境使用TLS
    )

    # 创建TracerProvider
    provider = TracerProvider(resource=resource)
    processor = BatchSpanProcessor(
        otlp_exporter,
        max_export_batch_size=1024,
        schedule_delay_millis=5000,
    )
    provider.add_span_processor(processor)
    trace.set_tracer_provider(provider)

    return trace.get_tracer("my-service")

def main():
    tracer = init_tracer()

    with tracer.start_as_current_span("main-operation"):
        # 业务逻辑
        print("Application is running...")
        time.sleep(2)

if __name__ == "__main__":
    main()
```

### SLS查询和分析

#### 查询Traces

```sql
-- 查询最近1小时的所有Trace
* | WHERE __topic__ = "otlp-traces" AND __time__ > now() - 3600

-- 查询错误的Trace
* | WHERE status.code = "ERROR"

-- 查询慢请求 (>500ms)
* | WHERE duration > 500000000  -- 纳秒

-- 统计请求量TOP 10的服务
* | SELECT service.name, COUNT(*) as count 
    GROUP BY service.name 
    ORDER BY count DESC 
    LIMIT 10
```

#### 查询Metrics

```sql
-- 查询HTTP请求QPS
* | WHERE __topic__ = "otlp-metrics" AND metric.name = "http.server.request.duration"
  | SELECT from_unixtime(__time__) as time, 
           COUNT(*) / 60.0 as qps 
    GROUP BY time

-- 查询P99延迟
* | WHERE metric.name = "http.server.request.duration"
  | SELECT approx_percentile(value, 0.99) as p99_latency
```

---

## 🚀 ARMS应用监控集成

### 概述1

阿里云ARMS (Application Real-Time Monitoring Service) 提供APM能力,支持OTLP协议接入。

### 前置准备1

1. **开通ARMS服务**
2. **创建应用监控任务**
3. **获取接入点信息**
   - Region: `cn-hangzhou`
   - Endpoint: `http://tracing-analysis-dc-hz.aliyuncs.com/adapt_xxx`

### Collector配置1

```yaml
exporters:
  otlp/arms:
    endpoint: "tracing-analysis-dc-hz.aliyuncs.com:8090"
    headers:
      # ARMS认证Token
      Authentication: "${ARMS_TOKEN}"
    compression: gzip

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [otlp/arms]
```

### 直接从SDK导出到ARMS

```go
// Go SDK直接导出到ARMS
exporter, err := otlptracegrpc.New(
    ctx,
    otlptracegrpc.WithEndpoint("tracing-analysis-dc-hz.aliyuncs.com:8090"),
    otlptracegrpc.WithHeaders(map[string]string{
        "Authentication": os.Getenv("ARMS_TOKEN"),
    }),
    otlptracegrpc.WithCompressor("gzip"),
)
```

### ARMS链路追踪

#### 查看链路拓扑

1. 登录ARMS控制台
2. 选择"应用监控" → "链路追踪"
3. 查看服务调用关系图

#### 查询Traces1

- **按TraceID查询**
- **按服务名查询**
- **按状态码过滤** (成功/失败)
- **按延迟范围过滤**

---

## 📈 Prometheus监控集成

### 阿里云Prometheus监控

阿里云提供托管的Prometheus服务,支持远程写入。

### Collector配置2

```yaml
exporters:
  prometheusremotewrite:
    endpoint: "https://cn-hangzhou-intranet.arms.aliyuncs.com/prometheus/xxx/api/v1/write"
    headers:
      Authorization: "Bearer ${PROMETHEUS_TOKEN}"
    resource_to_telemetry_conversion:
      enabled: true
    compression: snappy

service:
  pipelines:
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [prometheusremotewrite]
```

### Grafana可视化

#### 配置数据源

1. 登录Grafana (ARMS控制台提供的Grafana)
2. 添加Prometheus数据源
   - URL: `https://cn-hangzhou-intranet.arms.aliyuncs.com/prometheus/xxx`
   - Auth: 使用阿里云AccessKey

#### 常用PromQL查询

```promql
# HTTP请求QPS
rate(http_server_request_duration_count[1m])

# P99延迟
histogram_quantile(0.99, 
  rate(http_server_request_duration_bucket[5m])
)

# 错误率
rate(http_server_request_duration_count{http_status_code=~"5.."}[1m])
/ rate(http_server_request_duration_count[1m])

# CPU使用率
system_cpu_utilization

# 内存使用
process_runtime_jvm_memory_usage
```

---

## 🏗️ 架构最佳实践

### 1. 混合云部署架构

```text
┌──────────────────────────────────────────────────────┐
│                    自建IDC / 其他云                   │
│  ┌───────┐  ┌───────┐                                │
│  │  App  │  │  App  │                                │
│  └───┬───┘  └───┬───┘                                │
│      │          │                                     │
│      └──────────┼──────┐                             │
│                 │      │                             │
│         ┌───────▼──────▼────┐                        │
│         │ Collector (Agent) │                        │
│         └──────────┬─────────┘                        │
│                    │ VPN/专线                         │
└────────────────────┼──────────────────────────────────┘
                     │
┌────────────────────▼──────────────────────────────────┐
│                  阿里云VPC                             │
│         ┌────────────────────┐                        │
│         │ Collector (Gateway)│                        │
│         └──────────┬───────────┘                      │
│                    │                                  │
│      ┌─────────────┼─────────────┐                   │
│      │             │              │                   │
│  ┌───▼───┐    ┌───▼───┐    ┌────▼────┐              │
│  │  SLS  │    │ ARMS  │    │Prometheus│              │
│  └───────┘    └───────┘    └─────────┘              │
└───────────────────────────────────────────────────────┘
```

**优势**:

- ✅ 统一可观测性平台
- ✅ 混合云数据汇聚
- ✅ 降低数据传输成本 (内网)

### 2. K8s DaemonSet模式

```yaml
# otel-collector-daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: otel-collector
  namespace: observability
spec:
  selector:
    matchLabels:
      app: otel-collector
  template:
    metadata:
      labels:
        app: otel-collector
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:latest
        env:
        - name: ALIYUN_ACCESS_KEY_ID
          valueFrom:
            secretKeyRef:
              name: aliyun-credentials
              key: access-key-id
        - name: ALIYUN_ACCESS_KEY_SECRET
          valueFrom:
            secretKeyRef:
              name: aliyun-credentials
              key: access-key-secret
        volumeMounts:
        - name: config
          mountPath: /etc/otel
      volumes:
      - name: config
        configMap:
          name: otel-collector-config
```

### 3. 多后端导出

```yaml
# 同时导出到多个后端
exporters:
  # SLS (主要)
  alibabacloud_logservice/sls:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    project: "my-project"
    logstore: "otlp-traces"
    access_key_id: "${ALIYUN_ACCESS_KEY_ID}"
    access_key_secret: "${ALIYUN_ACCESS_KEY_SECRET}"
  
  # ARMS (链路追踪)
  otlp/arms:
    endpoint: "tracing-analysis-dc-hz.aliyuncs.com:8090"
    headers:
      Authentication: "${ARMS_TOKEN}"
  
  # Prometheus (指标)
  prometheusremotewrite:
    endpoint: "https://cn-hangzhou-intranet.arms.aliyuncs.com/prometheus/xxx/api/v1/write"

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [alibabacloud_logservice/sls, otlp/arms]  # 多后端
    
    metrics:
      receivers: [otlp]
      processors: [batch]
      exporters: [prometheusremotewrite]
```

---

## 💰 成本优化

### SLS成本分析

#### 计费项目

| 项目 | 单价 | 说明 |
|-----|------|------|
| **索引流量** | ¥0.35/GB | 最主要成本 |
| **写入流量** | ¥0.045/GB | 数据写入 |
| **存储** | ¥0.002/GB/天 | 数据存储 |
| **读取流量** | ¥0.15/GB | 数据读取 |

#### 成本优化策略

##### 1. 启用压缩 (节省60-70%)

```yaml
exporters:
  alibabacloud_logservice/sls:
    endpoint: "cn-hangzhou.log.aliyuncs.com"
    # 启用压缩
    compression: gzip  # 或 zstd
```

**节省**: 写入流量减少60-70%

##### 2. 采样 (节省90%+)

```yaml
processors:
  # Head sampling (SDK层)
  probabilistic_sampler:
    sampling_percentage: 10  # 采样10%

  # Tail sampling (Collector层)
  tail_sampling:
    policies:
      - name: errors
        type: status_code
        status_code: {status_codes: [ERROR]}
      - name: sample-10pct
        type: probabilistic
        probabilistic: {sampling_percentage: 10}
```

**节省**: 数据量减少90%

##### 3. 精简索引 (节省50-80%)

```text
SLS控制台 → Logstore → 索引配置

仅对必要字段建立索引:
✅ service.name
✅ trace.id
✅ span.name
✅ status.code
❌ http.url (高基数,不建索引)
❌ user.id (高基数,不建索引)
```

**节省**: 索引流量减少50-80%

##### 4. 设置数据生命周期

```text
SLS控制台 → Logstore → 数据保留

- 热数据 (可查询): 7天
- 冷数据 (归档): 30天
- 超过30天: 自动删除
```

**节省**: 存储成本减少80%+

#### 成本计算示例

```text
假设:
- 流量: 1000 req/s
- 每Trace: 10 Spans
- 每Span: 2 KB (原始)

无优化成本 (每月):
  数据量 = 1000 * 10 * 2KB * 86400 * 30 = 51.84 TB/月
  索引流量 = 51.84 TB * ¥0.35/GB = ¥18,500/月
  写入流量 = 51.84 TB * ¥0.045/GB = ¥2,387/月
  总成本 = ¥20,887/月

优化后成本 (采样10% + 压缩70% + 精简索引50%):
  数据量 = 51.84 TB * 10% * 30% = 1.56 TB/月
  索引流量 = 1.56 TB * 50% * ¥0.35/GB = ¥280/月
  写入流量 = 1.56 TB * ¥0.045/GB = ¥72/月
  总成本 = ¥352/月

节省 = ¥20,887 - ¥352 = ¥20,535/月 (98.3%!) 🔥
```

---

## 🔍 故障排查

### 常见问题

#### 1. 数据未到达SLS

**排查步骤**:

```bash
# 1. 检查Collector日志
kubectl logs -n observability otel-collector-xxx

# 2. 查看导出器指标
curl http://collector:8888/metrics | grep alibabacloud_logservice

# 3. 测试SLS连通性
curl -v https://cn-hangzhou.log.aliyuncs.com
```

**常见原因**:

- ❌ AccessKey错误
- ❌ Project/Logstore不存在
- ❌ 网络不通 (VPC配置)
- ❌ Region配置错误

#### 2. ARMS Token认证失败

**解决方案**:

```yaml
exporters:
  otlp/arms:
    endpoint: "tracing-analysis-dc-hz.aliyuncs.com:8090"
    headers:
      # 确保Token正确
      Authentication: "${ARMS_TOKEN}"
```

检查Token有效性:

```bash
# 使用Token测试连接
grpcurl -H "Authentication: ${ARMS_TOKEN}" \
  tracing-analysis-dc-hz.aliyuncs.com:8090 \
  list
```

#### 3. 高延迟问题

**优化建议**:

- ✅ 使用阿里云内网Endpoint (降低延迟50%+)
- ✅ 启用批处理 (batch_size=1024-2048)
- ✅ 使用ECS/K8s部署Collector (同VPC)

```yaml
exporters:
  alibabacloud_logservice/sls:
    # 使用内网Endpoint
    endpoint: "cn-hangzhou-intranet.log.aliyuncs.com"
```

---

## 📚 参考资源

| 资源 | 链接 |
|------|------|
| **阿里云SLS文档** | <https://help.aliyun.com/product/28958.html> |
| **ARMS文档** | <https://help.aliyun.com/product/34364.html> |
| **Prometheus监控** | <https://help.aliyun.com/document_detail/205392.html> |
| **OTLP集成** | <https://help.aliyun.com/document_detail/180761.html> |

---

## 🎯 最佳实践总结

```text
✅ 使用内网Endpoint降低延迟和成本
✅ 启用压缩 (gzip/zstd)
✅ 配置采样 (10%正常,100%错误)
✅ 精简SLS索引字段
✅ 设置合理的数据生命周期 (7天热+30天冷)
✅ 使用环境变量管理AccessKey
✅ 部署Collector Gateway在阿里云VPC内
✅ 监控Collector自身指标
✅ 定期审查成本和优化配置
✅ 保留所有错误和慢请求
```

---

**最后更新**: 2025年10月9日  
**适用区域**: 中国大陆 (cn-hangzhou, cn-beijing, cn-shanghai等)  
**下一篇**: [腾讯云OTLP集成指南](./02_腾讯云OTLP集成指南.md)

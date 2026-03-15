# 📘 OTLP协议速查手册

> **版本**: v1.3.0  
> **最后更新**: 2025年10月9日  
> **用途**: 快速参考OTLP核心协议要点

---

## 🎯 速查目录

- [📘 OTLP协议速查手册](#-otlp协议速查手册)
  - [🎯 速查目录](#-速查目录)
  - [📋 协议版本](#-协议版本)
  - [🌐 传输协议](#-传输协议)
    - [快速对比](#快速对比)
    - [选择建议](#选择建议)
  - [📊 信号类型](#-信号类型)
  - [🔧 编码格式](#-编码格式)
    - [Protobuf vs JSON](#protobuf-vs-json)
    - [Content-Type](#content-type)
  - [🛣️ 端点路径](#️-端点路径)
    - [完整URL格式](#完整url格式)
    - [标准端点](#标准端点)
  - [📨 HTTP Headers](#-http-headers)
    - [必需Headers](#必需headers)
    - [推荐Headers](#推荐headers)
    - [CORS Headers (浏览器端)](#cors-headers-浏览器端)
  - [✅ 响应码](#-响应码)
    - [成功](#成功)
    - [客户端错误 (4xx)](#客户端错误-4xx)
    - [服务端错误 (5xx)](#服务端错误-5xx)
  - [📦 批处理](#-批处理)
    - [配置参数](#配置参数)
    - [动态批处理 (v1.2.0+)](#动态批处理-v120)
    - [批处理策略](#批处理策略)
  - [🗜️ 压缩](#️-压缩)
    - [支持的算法](#支持的算法)
    - [配置示例](#配置示例)
    - [性能对比](#性能对比)
  - [🔄 重试策略](#-重试策略)
    - [推荐配置](#推荐配置)
    - [指数退避算法](#指数退避算法)
    - [应重试的响应码](#应重试的响应码)
  - [⚙️ 常用配置](#️-常用配置)
    - [Go SDK](#go-sdk)
    - [Python SDK](#python-sdk)
    - [JavaScript SDK (Node.js)](#javascript-sdk-nodejs)
    - [Java SDK](#java-sdk)
  - [🔍 快速诊断](#-快速诊断)
    - [常见问题速查](#常见问题速查)
    - [调试工具](#调试工具)
    - [启用调试日志](#启用调试日志)
  - [📚 快速参考链接](#-快速参考链接)
  - [🎯 最佳实践清单](#-最佳实践清单)

---

## 📋 协议版本

| 版本 | 发布时间 | 主要特性 | 状态 |
|------|---------|---------|------|
| **v1.3.0** | 2024-09 | Profiles稳定、性能优化、zstd压缩 | ✅ 当前 |
| v1.2.0 | 2024-06 | 动态批处理、HTTP/JSON增强 | ✅ 稳定 |
| v1.1.0 | 2024-03 | JSON编码、Exemplars、Logs GA | ✅ 稳定 |
| v1.0.0 | 2023-11 | 初始稳定版 | ✅ 稳定 |

---

## 🌐 传输协议

### 快速对比

| 协议 | 端口 | 优势 | 适用场景 |
|-----|------|------|---------|
| **gRPC** | 4317 | 高性能、流式传输、双向通信 | 生产环境、高吞吐量 |
| **HTTP/Protobuf** | 4318 | 防火墙友好、简单易用 | 受限网络、Web应用 |
| **HTTP/JSON** | 4318 | 人类可读、调试友好 | 开发调试、浏览器端 |

### 选择建议

```text
使用 gRPC 当:
  ✅ 追求极致性能
  ✅ 需要流式传输
  ✅ 微服务间通信
  ✅ 数据量大 (>10MB/s)

使用 HTTP/Protobuf 当:
  ✅ 防火墙限制
  ✅ 负载均衡需求
  ✅ 云环境集成
  ✅ 需要HTTP中间件

使用 HTTP/JSON 当:
  ✅ 浏览器端应用
  ✅ 开发调试阶段
  ✅ 人工审查数据
  ✅ JSON生态集成
```

---

## 📊 信号类型

| 信号 | 用途 | 状态 | 端点后缀 | 典型数据大小 |
|------|-----|------|---------|-------------|
| **Traces** | 分布式追踪 | ✅ GA | `/v1/traces` | 1-10 KB/span |
| **Metrics** | 性能指标 | ✅ GA | `/v1/metrics` | 100-500 B/point |
| **Logs** | 日志记录 | ✅ GA (v1.1.0) | `/v1/logs` | 500 B-2 KB/log |
| **Profiles** | 性能剖析 | ✅ Stable (v1.3.0) | `/v1/profiles` | 10-100 KB/profile |

---

## 🔧 编码格式

### Protobuf vs JSON

| 特性 | Protobuf | JSON |
|-----|----------|------|
| **大小** | 小 (基准) | 大 (+60%~150%) |
| **速度** | 快 (基准) | 慢 (+30%~80%) |
| **可读性** | ❌ 二进制 | ✅ 人类可读 |
| **浏览器支持** | ⚠️ 需库 | ✅ 原生 |
| **调试难度** | 高 | 低 |
| **生产推荐** | ✅ 首选 | ⚠️ 特定场景 |

### Content-Type

```text
Protobuf: application/x-protobuf
JSON:     application/json
```

---

## 🛣️ 端点路径

### 完整URL格式

```text
{scheme}://{host}:{port}/v1/{signal}

示例:
- gRPC:     grpc://collector:4317
- HTTP:     https://collector:4318/v1/traces
- 本地开发: http://localhost:4318/v1/metrics
```

### 标准端点

| 信号 | gRPC | HTTP |
|------|------|------|
| Traces | `grpc://host:4317` | `https://host:4318/v1/traces` |
| Metrics | `grpc://host:4317` | `https://host:4318/v1/metrics` |
| Logs | `grpc://host:4317` | `https://host:4318/v1/logs` |
| Profiles | `grpc://host:4317` | `https://host:4318/v1/profiles` |

---

## 📨 HTTP Headers

### 必需Headers

```http
POST /v1/traces HTTP/1.1
Host: collector.example.com:4318
Content-Type: application/x-protobuf
Content-Length: 1234
```

### 推荐Headers

| Header | 值 | 用途 |
|--------|---|------|
| `Content-Type` | `application/x-protobuf` / `application/json` | 编码格式 |
| `Content-Encoding` | `gzip` / `zstd` | 压缩算法 |
| `X-Requested-With` | `XMLHttpRequest` | CORS预检 |
| `Authorization` | `Bearer <token>` | 认证 |
| `User-Agent` | `MyApp/1.0` | 客户端标识 |

### CORS Headers (浏览器端)

```http
Access-Control-Allow-Origin: *
Access-Control-Allow-Methods: POST, OPTIONS
Access-Control-Allow-Headers: Content-Type, Content-Encoding
Access-Control-Max-Age: 3600
```

---

## ✅ 响应码

### 成功

| 码 | 含义 | 处理 |
|----|------|------|
| **200** | OK | 数据已接收并处理 ✅ |
| **202** | Accepted | 数据已接收,异步处理 ✅ |

### 客户端错误 (4xx)

| 码 | 含义 | 常见原因 | 修复建议 |
|----|------|---------|---------|
| **400** | Bad Request | Protobuf解析失败 | 检查编码格式、字段值 |
| **401** | Unauthorized | 认证失败 | 检查API Key/Token |
| **404** | Not Found | 错误的端点路径 | 确认`/v1/{signal}` |
| **413** | Payload Too Large | 批量过大 | 减小批次大小 |
| **415** | Unsupported Media | Content-Type错误 | 设置正确的Content-Type |
| **429** | Too Many Requests | 速率限制 | 启用重试退避 |

### 服务端错误 (5xx)

| 码 | 含义 | 处理策略 |
|----|------|---------|
| **500** | Internal Server Error | 重试 (指数退避) |
| **502** | Bad Gateway | 重试 (检查网络) |
| **503** | Service Unavailable | 重试 (等待服务恢复) |
| **504** | Gateway Timeout | 重试 (增加超时) |

---

## 📦 批处理

### 配置参数

| 参数 | 默认值 | 推荐值 | 说明 |
|-----|--------|--------|------|
| `max_export_batch_size` | 512 | 1024-2048 | 单批最大条目数 |
| `max_queue_size` | 2048 | 4096-8192 | 队列最大大小 |
| `schedule_delay` | 5s | 5-10s | 批处理间隔 |
| `export_timeout` | 30s | 30-60s | 导出超时 |

### 动态批处理 (v1.2.0+)

```yaml
# OpenTelemetry Collector配置
exporters:
  otlp:
    endpoint: collector:4317
    sending_queue:
      enabled: true
      num_consumers: 10
      queue_size: 5000
    retry_on_failure:
      enabled: true
      initial_interval: 1s
      max_interval: 30s
      max_elapsed_time: 300s
    # 动态批处理
    batch:
      enabled: true
      timeout: 10s
      send_batch_size: 1024
      send_batch_max_size: 2048
```

### 批处理策略

```text
低延迟场景 (< 100ms):
  batch_size: 256-512
  schedule_delay: 1-2s

均衡场景 (100-500ms):
  batch_size: 1024-2048
  schedule_delay: 5-10s

高吞吐场景 (> 500ms可接受):
  batch_size: 4096-8192
  schedule_delay: 15-30s
```

---

## 🗜️ 压缩

### 支持的算法

| 算法 | 版本 | 压缩率 | CPU开销 | 推荐场景 |
|------|------|--------|---------|---------|
| **gzip** | v1.0.0+ | 60-70% | 中 | 通用场景 ✅ |
| **zstd** | v1.1.0+ | 70-80% | 低-中 | 高吞吐量 🔥 |
| **none** | - | 0% | 无 | 本地开发 |

### 配置示例

```yaml
# gRPC
exporters:
  otlp:
    endpoint: collector:4317
    compression: gzip  # 或 zstd

# HTTP
exporters:
  otlphttp:
    endpoint: https://collector:4318
    compression: gzip
    headers:
      Content-Encoding: gzip
```

### 性能对比

```text
原始大小: 1 MB

gzip:  压缩后 ~300-400 KB  (CPU: 中)  ✅ 默认推荐
zstd:  压缩后 ~200-300 KB  (CPU: 低)  🔥 高性能推荐
none:  无压缩  1 MB         (CPU: 无)  ⚠️ 仅开发环境
```

---

## 🔄 重试策略

### 推荐配置

```yaml
retry_on_failure:
  enabled: true
  initial_interval: 1s      # 首次重试间隔
  max_interval: 30s         # 最大重试间隔
  max_elapsed_time: 300s    # 总重试时长
  multiplier: 1.5           # 退避倍数
  randomization_factor: 0.5 # 随机抖动
```

### 指数退避算法

```text
重试间隔 = min(initial_interval * multiplier^attempt, max_interval)

示例 (initial=1s, multiplier=2):
- 第1次: 1s
- 第2次: 2s
- 第3次: 4s
- 第4次: 8s
- 第5次: 16s
- 第6次: 30s (达到max_interval)
```

### 应重试的响应码

```text
✅ 应重试:
  429 Too Many Requests
  500 Internal Server Error
  502 Bad Gateway
  503 Service Unavailable
  504 Gateway Timeout

❌ 不应重试:
  400 Bad Request
  401 Unauthorized
  403 Forbidden
  404 Not Found
  413 Payload Too Large
  415 Unsupported Media Type
```

---

## ⚙️ 常用配置

### Go SDK

```go
import (
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/trace"
)

func initTracer() (*trace.TracerProvider, error) {
    exporter, err := otlptracegrpc.New(
        context.Background(),
        otlptracegrpc.WithEndpoint("collector:4317"),
        otlptracegrpc.WithInsecure(), // 仅开发环境
        otlptracegrpc.WithCompressor("gzip"),
        otlptracegrpc.WithTimeout(30*time.Second),
        otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
            Enabled:         true,
            InitialInterval: 1 * time.Second,
            MaxInterval:     30 * time.Second,
            MaxElapsedTime:  300 * time.Second,
        }),
    )
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter,
            trace.WithMaxExportBatchSize(1024),
            trace.WithBatchTimeout(5*time.Second),
        ),
    )
    return tp, nil
}
```

### Python SDK

```python
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor

exporter = OTLPSpanExporter(
    endpoint="collector:4317",
    insecure=True,  # 仅开发环境
    compression="gzip",
    timeout=30,
)

provider = TracerProvider()
provider.add_span_processor(
    BatchSpanProcessor(
        exporter,
        max_export_batch_size=1024,
        schedule_delay_millis=5000,
        export_timeout_millis=30000,
    )
)
```

### JavaScript SDK (Node.js)

```javascript
const { OTLPTraceExporter } = require('@opentelemetry/exporter-trace-otlp-grpc');
const { BatchSpanProcessor } = require('@opentelemetry/sdk-trace-base');
const { NodeTracerProvider } = require('@opentelemetry/sdk-trace-node');

const exporter = new OTLPTraceExporter({
  url: 'grpc://collector:4317',
  compression: 'gzip',
  timeoutMillis: 30000,
});

const provider = new NodeTracerProvider();
provider.addSpanProcessor(new BatchSpanProcessor(exporter, {
  maxExportBatchSize: 1024,
  scheduledDelayMillis: 5000,
  exportTimeoutMillis: 30000,
}));
```

### Java SDK

```java
import io.opentelemetry.exporter.otlp.trace.OtlpGrpcSpanExporter;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;

OtlpGrpcSpanExporter exporter = OtlpGrpcSpanExporter.builder()
    .setEndpoint("http://collector:4317")
    .setCompression("gzip")
    .setTimeout(Duration.ofSeconds(30))
    .build();

SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
    .addSpanProcessor(
        BatchSpanProcessor.builder(exporter)
            .setMaxExportBatchSize(1024)
            .setScheduleDelay(Duration.ofSeconds(5))
            .setExporterTimeout(Duration.ofSeconds(30))
            .build()
    )
    .build();
```

---

## 🔍 快速诊断

### 常见问题速查

| 症状 | 可能原因 | 快速检查命令 |
|-----|---------|------------|
| 连接失败 | 端口/地址错误 | `telnet collector 4317` |
| 数据未到达 | 防火墙/网络 | `curl -v http://collector:4318/v1/traces` |
| 401错误 | 认证问题 | 检查`Authorization` header |
| 415错误 | Content-Type | 确认`application/x-protobuf` |
| 大量429 | 速率限制 | 检查Collector限流配置 |
| 高延迟 | 批处理过大 | 减小`batch_size` |
| 内存溢出 | 队列积压 | 减小`max_queue_size` |

### 调试工具

```bash
# 1. 测试gRPC连接
grpcurl -plaintext collector:4317 list

# 2. 测试HTTP端点
curl -X POST http://collector:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{"resourceSpans":[]}'

# 3. 查看Collector日志
docker logs -f opentelemetry-collector

# 4. 检查端口监听
netstat -tuln | grep -E '4317|4318'

# 5. 抓包分析
tcpdump -i any -A 'port 4317 or port 4318'
```

### 启用调试日志

```yaml
# OpenTelemetry Collector
service:
  telemetry:
    logs:
      level: debug
      encoding: json
      output_paths:
        - stdout
        - /var/log/otel-collector.log
```

```go
// Go SDK
import "go.opentelemetry.io/otel"
otel.SetLogger(logr.New(logSink)) // 设置自定义logger
```

```python
# Python SDK
import logging
logging.basicConfig(level=logging.DEBUG)
```

---

## 📚 快速参考链接

| 资源 | 链接 |
|------|------|
| **OTLP规范** | <https://opentelemetry.io/docs/specs/otlp/> |
| **协议定义 (Protobuf)** | <https://github.com/open-telemetry/opentelemetry-proto> |
| **Collector配置** | <https://opentelemetry.io/docs/collector/configuration/> |
| **SDK文档** | <https://opentelemetry.io/docs/instrumentation/> |
| **示例项目** | <https://github.com/open-telemetry/opentelemetry-demo> |

---

## 🎯 最佳实践清单

```text
✅ 生产环境使用gRPC + Protobuf + gzip/zstd
✅ 启用批处理 (batch_size: 1024-2048)
✅ 配置重试策略 (指数退避)
✅ 设置合理的超时 (30-60s)
✅ 使用TLS加密传输 (生产环境)
✅ 实施认证授权 (API Key/mTLS)
✅ 监控导出器指标 (成功率/延迟)
✅ 限制队列大小防止OOM
✅ 开发环境使用HTTP/JSON便于调试
✅ 定期更新SDK到最新稳定版
```

---

**最后更新**: 2025年10月9日  
**下一篇**: [Semantic Conventions速查手册](./02_Semantic_Conventions速查手册.md)

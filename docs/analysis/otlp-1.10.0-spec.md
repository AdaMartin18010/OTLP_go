# OTLP 1.10.0 规范更新详解

> **规范版本**: OTLP 1.10.0  
> **发布日期**: 2025-10-17  
> **文档日期**: 2026-03-17  
> **适用**: OpenTelemetry Go SDK 开发

---

## 📋 目录

1. [规范概述](#1-规范概述)
2. [信号类型状态](#2-信号类型状态)
3. [重大变更](#3-重大变更)
4. [Protocol 细节](#4-protocol-细节)
5. [Go SDK 实现指南](#5-go-sdk-实现指南)

---

## 1. 规范概述

OTLP (OpenTelemetry Protocol) 1.10.0 是 OpenTelemetry 项目的重要里程碑版本，标志着所有主要信号类型（Traces、Metrics、Logs）进入稳定状态。

### 1.1 版本亮点

- ✅ **Traces**: 全面稳定 (Stable)
- ✅ **Metrics**: API/Protocol 稳定，SDK 混合状态
- ✅ **Logs**: 全面稳定 (Stable)
- 🔄 **Profiles**: Protocol 开发中
- ⚠️ **Zipkin Exporter**: 正式弃用

---

## 2. 信号类型状态

### 2.1 Traces（追踪）

| 组件 | 状态 | 说明 |
|------|------|------|
| API | Stable | 长期支持，仅向后兼容扩展 |
| SDK | Stable | 生产就绪 |
| Protocol | Stable | gRPC/HTTP 传输稳定 |
| Semantic Conventions | Stable | 语义约定稳定 |

**Go SDK 实现要点**:
```go
// 稳定的 Trace API
tracer := otel.Tracer("my-service")
ctx, span := tracer.Start(ctx, "operation")
defer span.End()
```

### 2.2 Metrics（指标）

| 组件 | 状态 | 说明 |
|------|------|------|
| API | Stable | 长期支持 |
| SDK | Mixed | 部分功能仍在开发 |
| Protocol | Stable | 数据传输稳定 |
| Exemplars | Stable | 示例值支持 |
| Views | Experimental | 视图配置实验性 |

**注意**: Metrics SDK 的某些高级功能（如复杂的视图配置）仍处于实验性状态。

### 2.3 Logs（日志）

| 组件 | 状态 | 说明 |
|------|------|------|
| Bridge API | Stable | 桥接 API 稳定 |
| SDK | Stable | 日志 SDK 稳定 |
| Protocol | Stable | 日志传输稳定 |
| Log Appenders | Development | 各语言 appender 开发中 |

**Go SDK 实现要点**:
```go
// 使用 LoggerProvider
loggerProvider := otellog.NewLoggerProvider(
    otellog.WithProcessor(otellog.NewBatchProcessor(exporter)),
)
logger := loggerProvider.Logger("my-service")
```

### 2.4 Profiles（性能分析）

| 组件 | 状态 | 说明 |
|------|------|------|
| Protocol | Development | pprof 格式集成开发中 |
| Data Model | Development | 数据模型定义中 |

**预期**: Go 1.27 或 OTLP 1.11.0 可能进入稳定状态。

---

## 3. 重大变更

### 3.1 Zipkin Exporter 弃用 ⛔

**变更时间**: 2025-12-22

**原因**:
- Zipkin 原生支持 OTLP 接收
- 自定义 exporter 维护成本高
- 各语言 SDK 使用率低下

**影响**:
- 现有稳定 Zipkin exporter 维护至 2026-12
- 新语言 SDK 无需实现 Zipkin exporter

**迁移方案**:

```yaml
# 方案 1: 直接发送到 Zipkin (推荐)
# Zipkin 启用 OTLP 接收器

# 应用配置
export OTEL_EXPORTER_OTLP_ENDPOINT=http://zipkin:9411/api/v2/otlp

# 方案 2: 通过 Collector 转发
# Collector 配置
exporters:
  zipkin:
    endpoint: http://zipkin:9411/api/v2/spans
```

### 3.2 Jaeger Exporter 弃用 ⛔

Jaeger exporter 已在先前版本中弃用，OTLP 1.10.0 正式确认。

**迁移方案**:
```yaml
# 直接发送到 Jaeger OTLP 接收器
export OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:4317
```

### 3.3 Partial Success 响应语义澄清

**规范更新**:
- 服务器在部分成功时必须设置 `partial_success` 字段
- 客户端不应重试部分成功的请求
- `rejected_<signal>` 为 0 时可用于传递警告信息

**Go SDK 实现**:
```go
// 处理 Partial Success
resp, err := client.Export(ctx, req)
if err != nil {
    return err
}

if ps := resp.PartialSuccess; ps != nil {
    if ps.RejectedSpans > 0 {
        log.Printf("Server rejected %d spans: %s", 
            ps.RejectedSpans, ps.ErrorMessage)
        // 不自动重试，记录日志即可
    }
}
```

---

## 4. Protocol 细节

### 4.1 传输协议支持

| 传输方式 | 状态 | 端点 | 内容类型 |
|----------|------|------|----------|
| OTLP/gRPC | Stable | `:4317` | application/grpc |
| OTLP/HTTP | Stable | `:4318` | application/x-protobuf |
| OTLP/HTTP JSON | Stable | `:4318` | application/json |

### 4.2 压缩支持

所有服务端组件必须支持:
- `none` - 无压缩
- `gzip` - Gzip 压缩
- `zstd` - Zstandard 压缩（推荐，性能更好）

**Go SDK 配置**:
```go
// 使用 zstd 压缩（更高性能）
import "github.com/klauspost/compress/zstd"

exporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithCompressor("zstd"),
)
```

### 4.3 并发请求

**推荐实践**:
- 低延迟网络（本地 Collector）: 顺序发送
- 高延迟网络: 支持并发 Unary 调用
- 并发数应可配置

**最大吞吐量公式**:
```
max_throughput = max_concurrent_requests × max_request_size / (network_latency + server_response_time)
```

**Go SDK 配置**:
```go
// 启用并发导出
exporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
        MaxConcurrentRequests: 10,
    }),
)
```

---

## 5. Go SDK 实现指南

### 5.1 依赖版本建议

```go
// go.mod
require (
    go.opentelemetry.io/otel v1.30.0
    go.opentelemetry.io/otel/sdk v1.30.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace v1.30.0
    go.opentelemetry.io/otel/exporters/otlp/otlpmetric v1.30.0
    go.opentelemetry.io/otel/exporters/otlp/otlplog v0.6.0  // 日志仍在 0.x
)
```

### 5.2 信号类型组合导出

OTLP 1.10.0 支持通过统一端点导出所有信号类型:

```go
// 使用 OTLP Collector 的复合导出器
endpoint := "http://collector:4317"

// Trace Exporter
traceExporter, _ := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint(endpoint),
)

// Metric Exporter
metricExporter, _ := otlpmetricgrpc.New(ctx,
    otlpmetricgrpc.WithEndpoint(endpoint),
)

// Log Exporter
logExporter, _ := otlploggrpc.New(ctx,
    otlploggrpc.WithEndpoint(endpoint),
)
```

### 5.3 错误处理最佳实践

```go
// 实现永久/可重试错误分类
type PermanentError struct {
    Err error
}

func (e PermanentError) Error() string {
    return e.Err.Error()
}

// 导出时错误处理
func (e *Exporter) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    err := e.client.ExportSpans(ctx, spans)
    if err == nil {
        return nil
    }
    
    // 检查状态码
    if status.Code(err) == codes.Unimplemented {
        return PermanentError{Err: err}  // 不重试
    }
    
    if status.Code(err) == codes.Unavailable {
        return err  // 可重试
    }
    
    return err
}
```

### 5.4 Resource 属性对齐

OTLP 1.10.0 推荐使用最新的 Semantic Conventions:

```go
// 使用稳定的 Resource 属性
res, _ := resource.New(ctx,
    resource.WithAttributes(
        // 服务属性
        semconv.ServiceNameKey.String("my-service"),
        semconv.ServiceVersionKey.String("1.0.0"),
        semconv.DeploymentEnvironmentKey.String("production"),
        
        // 主机属性
        semconv.HostNameKey.String(hostname),
        semconv.HostArchKey.String(runtime.GOARCH),
        
        // Go 运行时属性
        semconv.ProcessRuntimeNameKey.String("go"),
        semconv.ProcessRuntimeVersionKey.String(runtime.Version()),
    ),
)
```

---

## 📊 规范符合性检查清单

### Traces 实现

- [x] Trace API 实现
- [x] W3C Trace Context 传播
- [x] Baggage 传播
- [x] OTLP/gRPC 导出
- [x] OTLP/HTTP 导出
- [x] B3 传播（可选）
- [x] Jaeger 传播（可选）

### Metrics 实现

- [x] Counter
- [x] UpDownCounter
- [x] Histogram
- [x] ObservableCounter
- [x] ObservableUpDownCounter
- [x] ObservableGauge
- [ ] Exponential Histogram（实验性）
- [ ] Views（实验性）

### Logs 实现

- [x] Log Bridge API
- [x] OTLP 日志导出
- [x] 结构化日志支持
- [x] Severity 级别映射

---

## 📚 参考

- [OTLP Specification 1.10.0](https://opentelemetry.io/docs/specs/otlp/)
- [OpenTelemetry Specification Status](https://opentelemetry.io/docs/specs/status/)
- [Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/)

---

**文档版本**: v1.0  
**最后更新**: 2026-03-17

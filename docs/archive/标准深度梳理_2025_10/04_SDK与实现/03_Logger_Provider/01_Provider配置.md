# LoggerProvider 配置

## 📋 目录

- [LoggerProvider 配置](#loggerprovider-配置)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 LoggerProvider](#什么是-loggerprovider)
    - [架构图](#架构图)
  - [基本配置](#基本配置)
    - [1. 最小配置](#1-最小配置)
    - [2. 完整配置](#2-完整配置)
    - [3. 全局配置](#3-全局配置)
  - [Processor 配置](#processor-配置)
    - [1. SimpleLogRecordProcessor](#1-simplelogrecordprocessor)
    - [2. BatchLogRecordProcessor](#2-batchlogrecordprocessor)
  - [Resource 配置](#resource-配置)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 配置结构](#1-配置结构)
    - [2. 配置构建器](#2-配置构建器)
    - [3. slog 集成](#3-slog-集成)
  - [生产环境配置](#生产环境配置)
    - [1. 标准配置](#1-标准配置)
    - [2. 高可用配置](#2-高可用配置)
    - [3. 云原生配置](#3-云原生配置)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 LoggerProvider

**LoggerProvider** 是 OpenTelemetry Logs 的入口点，负责：

```text
职责:
- 创建 Logger 实例
- 管理 LogRecordProcessor（处理日志记录）
- 配置 LogRecordExporter（导出日志）
- 关联 Resource（服务标识）
```

### 架构图

```text
Application
    ↓
LoggerProvider
    ├── Resource (服务标识)
    ├── Processor (处理策略)
    │   ├── SimpleLogRecordProcessor (同步处理)
    │   └── BatchLogRecordProcessor (批处理)
    ├── Exporter (导出目标)
    └── Logger (per InstrumentationScope)
        └── LogRecord (日志记录)
```

---

## 基本配置

### 1. 最小配置

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/sdk/log"
    "go.opentelemetry.io/otel/exporters/stdout/stdoutlog"
)

func main() {
    // 创建导出器
    exporter, _ := stdoutlog.New()
    
    // 创建 LoggerProvider (最小配置)
    lp := log.NewLoggerProvider(
        log.WithProcessor(
            log.NewSimpleProcessor(exporter),
        ),
    )
    
    // 设置为全局
    otel.SetLoggerProvider(lp)
    
    // 关闭时清理
    defer lp.Shutdown(context.Background())
}
```

### 2. 完整配置

```go
import (
    "time"
    "go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploggrpc"
    "go.opentelemetry.io/otel/sdk/log"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

func main() {
    // 1. 创建 Resource
    res, _ := resource.New(
        context.Background(),
        resource.WithAttributes(
            semconv.ServiceName("myapp"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    
    // 2. 创建 OTLP 导出器
    exporter, _ := otlploggrpc.New(
        context.Background(),
        otlploggrpc.WithEndpoint("localhost:4317"),
        otlploggrpc.WithInsecure(),
    )
    
    // 3. 创建 BatchProcessor
    processor := log.NewBatchProcessor(
        exporter,
        log.WithBatchTimeout(5*time.Second),
        log.WithMaxQueueSize(2048),
        log.WithExportMaxBatchSize(512),
    )
    
    // 4. 创建 LoggerProvider
    lp := log.NewLoggerProvider(
        log.WithResource(res),
        log.WithProcessor(processor),
    )
    
    // 5. 设置为全局
    otel.SetLoggerProvider(lp)
    
    // 6. 关闭时清理
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        if err := lp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down LoggerProvider: %v", err)
        }
    }()
}
```

### 3. 全局配置

```go
package telemetry

import (
    "sync"
)

var (
    globalLP   *log.LoggerProvider
    globalOnce sync.Once
)

// InitLoggerProvider 初始化全局 LoggerProvider
func InitLoggerProvider() error {
    var err error
    globalOnce.Do(func() {
        // 创建 Resource
        res, _ := resource.New(...)
        
        // 创建 Exporter
        exporter, _ := otlploggrpc.New(...)
        
        // 创建 Processor
        processor := log.NewBatchProcessor(exporter)
        
        // 创建 LoggerProvider
        globalLP = log.NewLoggerProvider(
            log.WithResource(res),
            log.WithProcessor(processor),
        )
        
        // 设置为全局
        otel.SetLoggerProvider(globalLP)
    })
    return err
}

// ShutdownLoggerProvider 关闭全局 LoggerProvider
func ShutdownLoggerProvider(ctx context.Context) error {
    if globalLP != nil {
        return globalLP.Shutdown(ctx)
    }
    return nil
}
```

---

## Processor 配置

### 1. SimpleLogRecordProcessor

同步处理（适合开发环境）：

```go
// 创建 SimpleProcessor
processor := log.NewSimpleProcessor(exporter)

lp := log.NewLoggerProvider(
    log.WithProcessor(processor),
)
```

**特点**:

```text
✅ 适用:
  - 开发环境
  - 调试
  - 低流量 (< 10 logs/s)

❌ 不适用:
  - 生产环境
  - 高流量
  - 性能敏感

优点:
✅ 立即可见
✅ 无延迟

缺点:
❌ 同步阻塞
❌ 性能开销大
```

### 2. BatchLogRecordProcessor

批量异步处理（推荐生产环境）：

```go
// 创建 BatchProcessor
processor := log.NewBatchProcessor(
    exporter,
    // 批处理超时
    log.WithBatchTimeout(5*time.Second),
    
    // 最大队列大小
    log.WithMaxQueueSize(2048),
    
    // 最大批次大小
    log.WithExportMaxBatchSize(512),
    
    // 导出超时
    log.WithExportTimeout(30*time.Second),
)

lp := log.NewLoggerProvider(
    log.WithProcessor(processor),
)
```

**配置说明**:

```text
BatchTimeout (批处理超时):
- 默认: 5秒
- 推荐: 1-10秒
- 过短: 增加网络开销
- 过长: 延迟可见性

MaxQueueSize (队列大小):
- 默认: 2048
- 推荐: 1024-4096
- 计算: 预期 log/s × BatchTimeout × 2

ExportMaxBatchSize (批次大小):
- 默认: 512
- 推荐: 256-1024
- 过小: 频繁导出
- 过大: 内存占用高

ExportTimeout (导出超时):
- 默认: 30秒
- 推荐: 10-30秒
- 应 < BatchTimeout
```

---

## Resource 配置

```go
import (
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
)

// 基本 Resource
res, _ := resource.New(
    context.Background(),
    resource.WithAttributes(
        semconv.ServiceName("myapp"),
        semconv.ServiceVersion("1.0.0"),
    ),
)

// 完整 Resource
res, _ := resource.New(
    context.Background(),
    // 服务信息
    resource.WithAttributes(
        semconv.ServiceName("myapp"),
        semconv.ServiceVersion("1.0.0"),
        semconv.ServiceInstanceID("instance-1"),
    ),
    // 部署环境
    resource.WithAttributes(
        semconv.DeploymentEnvironment("production"),
    ),
    // 主机信息
    resource.WithHost(),
    
    // 容器信息
    resource.WithContainer(),
    
    // 进程信息
    resource.WithProcess(),
    
    // OS 信息
    resource.WithOS(),
)

lp := log.NewLoggerProvider(
    log.WithResource(res),
    log.WithProcessor(processor),
)
```

---

## Go 1.25.1 实现

### 1. 配置结构

```go
package telemetry

import (
    "time"
)

// LoggerProviderConfig LoggerProvider 配置
type LoggerProviderConfig struct {
    // 服务信息
    ServiceName    string
    ServiceVersion string
    Environment    string
    
    // 导出配置
    ExporterType   string // "otlp", "stdout"
    Endpoint       string
    Insecure       bool
    
    // Processor 配置
    ProcessorType  string // "simple", "batch"
    BatchTimeout   time.Duration
    MaxQueueSize   int
    MaxBatchSize   int
    
    // Resource 配置
    AdditionalAttributes map[string]string
}

// DefaultConfig 默认配置
func DefaultConfig() *LoggerProviderConfig {
    return &LoggerProviderConfig{
        ServiceName:    "unknown-service",
        ServiceVersion: "0.0.0",
        Environment:    "development",
        ExporterType:   "stdout",
        ProcessorType:  "simple",
        BatchTimeout:   5 * time.Second,
        MaxQueueSize:   2048,
        MaxBatchSize:   512,
        AdditionalAttributes: make(map[string]string),
    }
}
```

### 2. 配置构建器

```go
package telemetry

// NewLoggerProvider 创建 LoggerProvider
func NewLoggerProvider(cfg *LoggerProviderConfig) (*log.LoggerProvider, error) {
    // 1. 创建 Resource
    res, err := createResource(cfg)
    if err != nil {
        return nil, err
    }
    
    // 2. 创建 Exporter
    exporter, err := createLogExporter(cfg)
    if err != nil {
        return nil, err
    }
    
    // 3. 创建 Processor
    var processor log.Processor
    switch cfg.ProcessorType {
    case "simple":
        processor = log.NewSimpleProcessor(exporter)
    case "batch":
        processor = log.NewBatchProcessor(
            exporter,
            log.WithBatchTimeout(cfg.BatchTimeout),
            log.WithMaxQueueSize(cfg.MaxQueueSize),
            log.WithExportMaxBatchSize(cfg.MaxBatchSize),
        )
    default:
        processor = log.NewBatchProcessor(exporter)
    }
    
    // 4. 创建 LoggerProvider
    lp := log.NewLoggerProvider(
        log.WithResource(res),
        log.WithProcessor(processor),
    )
    
    return lp, nil
}

func createLogExporter(cfg *LoggerProviderConfig) (log.Exporter, error) {
    switch cfg.ExporterType {
    case "otlp":
        return createOTLPLogExporter(cfg)
    case "stdout":
        return stdoutlog.New()
    default:
        return nil, fmt.Errorf("unknown exporter type: %s", cfg.ExporterType)
    }
}

func createOTLPLogExporter(cfg *LoggerProviderConfig) (log.Exporter, error) {
    opts := []otlploggrpc.Option{
        otlploggrpc.WithEndpoint(cfg.Endpoint),
    }
    
    if cfg.Insecure {
        opts = append(opts, otlploggrpc.WithInsecure())
    }
    
    return otlploggrpc.New(context.Background(), opts...)
}

// 使用示例
func main() {
    cfg := &LoggerProviderConfig{
        ServiceName:    "myapp",
        ServiceVersion: "1.0.0",
        Environment:    "production",
        ExporterType:   "otlp",
        Endpoint:       "localhost:4317",
        Insecure:       true,
        ProcessorType:  "batch",
        BatchTimeout:   5 * time.Second,
    }
    
    lp, err := NewLoggerProvider(cfg)
    if err != nil {
        log.Fatal(err)
    }
    defer lp.Shutdown(context.Background())
    
    otel.SetLoggerProvider(lp)
}
```

### 3. slog 集成

```go
package telemetry

import (
    "log/slog"
    "go.opentelemetry.io/contrib/bridges/otelslog"
)

// SetupSlog 设置 slog 与 OpenTelemetry 集成
func SetupSlog(lp *log.LoggerProvider) {
    // 创建 OpenTelemetry Logger
    logger := lp.Logger("myapp")
    
    // 创建 slog Handler
    handler := otelslog.NewHandler("myapp", otelslog.WithLoggerProvider(lp))
    
    // 设置为默认 slog logger
    slog.SetDefault(slog.New(handler))
}

// 使用示例
func main() {
    // 创建 LoggerProvider
    lp, _ := NewLoggerProvider(cfg)
    defer lp.Shutdown(context.Background())
    
    // 设置 slog
    SetupSlog(lp)
    
    // 使用 slog
    slog.Info("Application started",
        "version", "1.0.0",
        "port", 8080,
    )
    
    slog.Error("Failed to connect to database",
        "error", err,
        "host", "localhost",
    )
}
```

---

## 生产环境配置

### 1. 标准配置

```go
func NewProductionLoggerProvider() (*log.LoggerProvider, error) {
    // Resource
    res, _ := resource.New(
        context.Background(),
        resource.WithAttributes(
            semconv.ServiceName(os.Getenv("SERVICE_NAME")),
            semconv.ServiceVersion(os.Getenv("SERVICE_VERSION")),
            semconv.DeploymentEnvironment("production"),
        ),
        resource.WithHost(),
        resource.WithContainer(),
    )
    
    // OTLP Exporter
    exporter, _ := otlploggrpc.New(
        context.Background(),
        otlploggrpc.WithEndpoint(os.Getenv("OTEL_COLLECTOR_ENDPOINT")),
        otlploggrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")),
    )
    
    // BatchProcessor (5秒批处理)
    processor := log.NewBatchProcessor(
        exporter,
        log.WithBatchTimeout(5*time.Second),
        log.WithMaxQueueSize(2048),
        log.WithExportMaxBatchSize(512),
    )
    
    // LoggerProvider
    lp := log.NewLoggerProvider(
        log.WithResource(res),
        log.WithProcessor(processor),
    )
    
    return lp, nil
}
```

### 2. 高可用配置

```go
// 多后端导出
func NewHALoggerProvider() (*log.LoggerProvider, error) {
    res, _ := resource.New(...)
    
    // Primary OTLP Collector
    primary, _ := otlploggrpc.New(
        context.Background(),
        otlploggrpc.WithEndpoint("primary-collector:4317"),
    )
    
    // Backup OTLP Collector
    backup, _ := otlploggrpc.New(
        context.Background(),
        otlploggrpc.WithEndpoint("backup-collector:4317"),
    )
    
    // 创建多个 Processor
    lp := log.NewLoggerProvider(
        log.WithResource(res),
        log.WithProcessor(log.NewBatchProcessor(primary)),
        log.WithProcessor(log.NewBatchProcessor(backup)),
    )
    
    return lp, nil
}
```

### 3. 云原生配置

```go
// Kubernetes 环境配置
func NewK8sLoggerProvider() (*log.LoggerProvider, error) {
    res, _ := resource.New(
        context.Background(),
        // 服务信息
        resource.WithAttributes(
            semconv.ServiceName(os.Getenv("SERVICE_NAME")),
            semconv.ServiceVersion(os.Getenv("SERVICE_VERSION")),
        ),
        // K8s 信息
        resource.WithAttributes(
            semconv.K8SNamespaceName(os.Getenv("K8S_NAMESPACE")),
            semconv.K8SPodName(os.Getenv("K8S_POD_NAME")),
            semconv.K8SNodeName(os.Getenv("K8S_NODE_NAME")),
        ),
        resource.WithHost(),
        resource.WithContainer(),
    )
    
    // OTLP Exporter (K8s Service)
    exporter, _ := otlploggrpc.New(
        context.Background(),
        otlploggrpc.WithEndpoint("otel-collector.observability.svc.cluster.local:4317"),
        otlploggrpc.WithInsecure(),
    )
    
    processor := log.NewBatchProcessor(exporter)
    
    lp := log.NewLoggerProvider(
        log.WithResource(res),
        log.WithProcessor(processor),
    )
    
    return lp, nil
}
```

---

## 最佳实践

```go
// ✅ 正确: 在应用启动时初始化
func main() {
    lp, err := NewProductionLoggerProvider()
    if err != nil {
        log.Fatal(err)
    }
    defer lp.Shutdown(context.Background())
    
    otel.SetLoggerProvider(lp)
    SetupSlog(lp)
    
    // 应用逻辑
}

// ✅ 正确: 正确关闭
defer func() {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    if err := lp.Shutdown(ctx); err != nil {
        log.Printf("Error shutting down: %v", err)
    }
}()

// ✅ 正确: 生产环境使用批处理
processor := log.NewBatchProcessor(
    exporter,
    log.WithBatchTimeout(5*time.Second),
)

// ❌ 错误: 生产环境使用同步处理
processor := log.NewSimpleProcessor(exporter) // 性能差！

// ✅ 正确: 包含完整的 Resource
res, _ := resource.New(
    context.Background(),
    resource.WithAttributes(
        semconv.ServiceName("myapp"),
        semconv.ServiceVersion("1.0.0"),
        semconv.DeploymentEnvironment("production"),
    ),
    resource.WithHost(),
    resource.WithContainer(),
)

// ❌ 错误: Resource 不完整
res, _ := resource.New(
    context.Background(),
    resource.WithAttributes(
        semconv.ServiceName("myapp"),
    ),
)
```

---

## 常见问题

**Q1: SimpleProcessor vs BatchProcessor？**

```text
SimpleProcessor:
✅ 适用:
  - 开发环境
  - 调试
  - 低流量
  - 需要立即可见

❌ 不适用:
  - 生产环境
  - 高流量

BatchProcessor (推荐):
✅ 适用:
  - 生产环境
  - 高流量
  - 性能敏感

配置推荐:
- 开发: SimpleProcessor
- 生产: BatchProcessor (5s 批处理)
```

**Q2: 如何与 slog 集成？**

```go
// 1. 创建 LoggerProvider
lp, _ := NewLoggerProvider(cfg)

// 2. 使用 otelslog bridge
handler := otelslog.NewHandler("myapp",
    otelslog.WithLoggerProvider(lp),
)

// 3. 设置为默认
slog.SetDefault(slog.New(handler))

// 4. 使用 slog
slog.Info("message", "key", "value")
```

**Q3: 批处理参数如何选择？**

```text
考虑因素:
1. 日志频率
   - < 10 logs/s: 简单处理
   - 10-100 logs/s: 批处理 (5s)
   - > 100 logs/s: 批处理 (1-2s)

2. 可见性要求
   - 实时: 1-2秒
   - 一般: 5秒
   - 低优先级: 10秒+

推荐配置:
BatchTimeout: 5秒
MaxQueueSize: 2048
MaxBatchSize: 512
```

---

## 参考资源

- [OpenTelemetry Logs SDK](https://opentelemetry.io/docs/specs/otel/logs/sdk/)
- [Go SDK LoggerProvider](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/log#LoggerProvider)
- [slog Bridge](https://pkg.go.dev/go.opentelemetry.io/contrib/bridges/otelslog)
- [02_Logger创建.md](./02_Logger创建.md)

---

**🎉 恭喜！你已经掌握了 LoggerProvider 的配置！**

现在你可以：

- ✅ 配置 LoggerProvider
- ✅ 使用 SimpleProcessor 和 BatchProcessor
- ✅ 配置 Resource
- ✅ 集成 Go slog
- ✅ 为生产环境创建配置

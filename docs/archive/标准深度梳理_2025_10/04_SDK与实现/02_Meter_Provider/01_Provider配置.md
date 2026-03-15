# MeterProvider 配置

## 📋 目录

- [MeterProvider 配置](#meterprovider-配置)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 MeterProvider](#什么是-meterprovider)
    - [架构图](#架构图)
  - [基本配置](#基本配置)
    - [1. 最小配置](#1-最小配置)
    - [2. 完整配置](#2-完整配置)
    - [3. 全局配置](#3-全局配置)
  - [Reader 配置](#reader-配置)
    - [1. PeriodicReader](#1-periodicreader)
    - [2. ManualReader](#2-manualreader)
    - [3. 多 Reader](#3-多-reader)
  - [Resource 配置](#resource-配置)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 配置结构](#1-配置结构)
    - [2. 配置构建器](#2-配置构建器)
    - [3. 环境变量配置](#3-环境变量配置)
  - [生产环境配置](#生产环境配置)
    - [1. 标准配置](#1-标准配置)
    - [2. 高可用配置](#2-高可用配置)
    - [3. 云原生配置](#3-云原生配置)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 MeterProvider

**MeterProvider** 是 OpenTelemetry Metrics 的入口点，负责：

```text
职责:
- 创建 Meter 实例
- 管理 Reader（周期性导出、手动导出）
- 配置 View（指标过滤和转换）
- 关联 Resource（服务标识）
```

### 架构图

```text
Application
    ↓
MeterProvider
    ├── Resource (服务标识)
    ├── Reader (导出策略)
    │   ├── PeriodicReader (周期性导出)
    │   └── ManualReader (手动导出)
    ├── View (指标转换)
    └── Meter (per InstrumentationScope)
        └── Instrument (Counter, Gauge, Histogram, etc.)
```

---

## 基本配置

### 1. 最小配置

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/stdout/stdoutmetric"
    "go.opentelemetry.io/otel/sdk/metric"
)

func main() {
    // 创建导出器
    exporter, _ := stdoutmetric.New()
    
    // 创建 MeterProvider (最小配置)
    mp := metric.NewMeterProvider(
        metric.WithReader(
            metric.NewPeriodicReader(exporter),
        ),
    )
    
    // 设置为全局
    otel.SetMeterProvider(mp)
    
    // 关闭时清理
    defer mp.Shutdown(context.Background())
}
```

### 2. 完整配置

```go
import (
    "time"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/sdk/metric"
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
    exporter, _ := otlpmetricgrpc.New(
        context.Background(),
        otlpmetricgrpc.WithEndpoint("localhost:4317"),
        otlpmetricgrpc.WithInsecure(),
    )
    
    // 3. 创建 Reader
    reader := metric.NewPeriodicReader(
        exporter,
        metric.WithInterval(30*time.Second),
    )
    
    // 4. 创建 MeterProvider
    mp := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(reader),
    )
    
    // 5. 设置为全局
    otel.SetMeterProvider(mp)
    
    // 6. 关闭时清理
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        if err := mp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down MeterProvider: %v", err)
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
    globalMP   *metric.MeterProvider
    globalOnce sync.Once
)

// InitMeterProvider 初始化全局 MeterProvider
func InitMeterProvider() error {
    var err error
    globalOnce.Do(func() {
        // 创建 Resource
        res, _ := resource.New(...)
        
        // 创建 Exporter
        exporter, _ := otlpmetricgrpc.New(...)
        
        // 创建 Reader
        reader := metric.NewPeriodicReader(exporter)
        
        // 创建 MeterProvider
        globalMP = metric.NewMeterProvider(
            metric.WithResource(res),
            metric.WithReader(reader),
        )
        
        // 设置为全局
        otel.SetMeterProvider(globalMP)
    })
    return err
}

// ShutdownMeterProvider 关闭全局 MeterProvider
func ShutdownMeterProvider(ctx context.Context) error {
    if globalMP != nil {
        return globalMP.Shutdown(ctx)
    }
    return nil
}
```

---

## Reader 配置

### 1. PeriodicReader

周期性导出指标（推荐生产环境）：

```go
// 默认配置（60秒间隔）
reader := metric.NewPeriodicReader(exporter)

// 自定义间隔
reader := metric.NewPeriodicReader(
    exporter,
    metric.WithInterval(30*time.Second),      // 导出间隔
    metric.WithTimeout(10*time.Second),       // 导出超时
)

// 使用示例
mp := metric.NewMeterProvider(
    metric.WithReader(reader),
)
```

**配置说明**:

```text
Interval (导出间隔):
- 默认: 60秒
- 推荐: 15-60秒
- 过短: 增加网络开销
- 过长: 延迟可见性

Timeout (导出超时):
- 默认: 30秒
- 推荐: 5-30秒
- 应 < Interval
```

### 2. ManualReader

手动触发导出（适合测试）：

```go
// 创建 ManualReader
reader := metric.NewManualReader()

mp := metric.NewMeterProvider(
    metric.WithReader(reader),
)

// 手动收集指标
ctx := context.Background()
var rm metricdata.ResourceMetrics
if err := reader.Collect(ctx, &rm); err != nil {
    log.Fatal(err)
}

// 处理指标数据
for _, sm := range rm.ScopeMetrics {
    for _, m := range sm.Metrics {
        fmt.Printf("Metric: %s\n", m.Name)
    }
}
```

**使用场景**:

```text
✅ 适用:
  - 单元测试
  - 集成测试
  - 按需导出

❌ 不适用:
  - 生产环境
```

### 3. 多 Reader

同时配置多个 Reader：

```go
// Reader 1: 周期性导出到 OTLP
otlpExporter, _ := otlpmetricgrpc.New(...)
otlpReader := metric.NewPeriodicReader(
    otlpExporter,
    metric.WithInterval(30*time.Second),
)

// Reader 2: 周期性导出到 Prometheus
promExporter, _ := prometheus.New()
promReader := metric.NewPeriodicReader(
    promExporter,
    metric.WithInterval(60*time.Second),
)

// 配置多个 Reader
mp := metric.NewMeterProvider(
    metric.WithReader(otlpReader),
    metric.WithReader(promReader),
)
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

// 完整 Resource (包含环境、主机等)
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
    
    // 容器信息 (自动检测)
    resource.WithContainer(),
    
    // 进程信息
    resource.WithProcess(),
    
    // OS 信息
    resource.WithOS(),
)

mp := metric.NewMeterProvider(
    metric.WithResource(res),
    metric.WithReader(reader),
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

// MeterProviderConfig MeterProvider 配置
type MeterProviderConfig struct {
    // 服务信息
    ServiceName    string
    ServiceVersion string
    Environment    string
    
    // 导出配置
    ExporterType   string // "otlp", "prometheus", "stdout"
    Endpoint       string
    Insecure       bool
    
    // Reader 配置
    ExportInterval time.Duration
    ExportTimeout  time.Duration
    
    // Resource 配置
    AdditionalAttributes map[string]string
}

// DefaultConfig 默认配置
func DefaultConfig() *MeterProviderConfig {
    return &MeterProviderConfig{
        ServiceName:    "unknown-service",
        ServiceVersion: "0.0.0",
        Environment:    "development",
        ExporterType:   "stdout",
        ExportInterval: 60 * time.Second,
        ExportTimeout:  30 * time.Second,
        AdditionalAttributes: make(map[string]string),
    }
}
```

### 2. 配置构建器

```go
package telemetry

// NewMeterProvider 创建 MeterProvider
func NewMeterProvider(cfg *MeterProviderConfig) (*metric.MeterProvider, error) {
    // 1. 创建 Resource
    res, err := createResource(cfg)
    if err != nil {
        return nil, err
    }
    
    // 2. 创建 Exporter
    exporter, err := createExporter(cfg)
    if err != nil {
        return nil, err
    }
    
    // 3. 创建 Reader
    reader := metric.NewPeriodicReader(
        exporter,
        metric.WithInterval(cfg.ExportInterval),
        metric.WithTimeout(cfg.ExportTimeout),
    )
    
    // 4. 创建 MeterProvider
    mp := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(reader),
    )
    
    return mp, nil
}

func createResource(cfg *MeterProviderConfig) (*resource.Resource, error) {
    attrs := []attribute.KeyValue{
        semconv.ServiceName(cfg.ServiceName),
        semconv.ServiceVersion(cfg.ServiceVersion),
        semconv.DeploymentEnvironment(cfg.Environment),
    }
    
    // 添加自定义属性
    for k, v := range cfg.AdditionalAttributes {
        attrs = append(attrs, attribute.String(k, v))
    }
    
    return resource.New(
        context.Background(),
        resource.WithAttributes(attrs...),
        resource.WithHost(),
        resource.WithProcess(),
    )
}

func createExporter(cfg *MeterProviderConfig) (metric.Exporter, error) {
    switch cfg.ExporterType {
    case "otlp":
        return createOTLPExporter(cfg)
    case "prometheus":
        return prometheus.New()
    case "stdout":
        return stdoutmetric.New()
    default:
        return nil, fmt.Errorf("unknown exporter type: %s", cfg.ExporterType)
    }
}

func createOTLPExporter(cfg *MeterProviderConfig) (metric.Exporter, error) {
    opts := []otlpmetricgrpc.Option{
        otlpmetricgrpc.WithEndpoint(cfg.Endpoint),
    }
    
    if cfg.Insecure {
        opts = append(opts, otlpmetricgrpc.WithInsecure())
    }
    
    return otlpmetricgrpc.New(context.Background(), opts...)
}

// 使用示例
func main() {
    cfg := &MeterProviderConfig{
        ServiceName:    "myapp",
        ServiceVersion: "1.0.0",
        Environment:    "production",
        ExporterType:   "otlp",
        Endpoint:       "localhost:4317",
        Insecure:       true,
        ExportInterval: 30 * time.Second,
    }
    
    mp, err := NewMeterProvider(cfg)
    if err != nil {
        log.Fatal(err)
    }
    defer mp.Shutdown(context.Background())
    
    otel.SetMeterProvider(mp)
}
```

### 3. 环境变量配置

```go
package telemetry

import (
    "os"
    "strconv"
    "time"
)

// LoadConfigFromEnv 从环境变量加载配置
func LoadConfigFromEnv() *MeterProviderConfig {
    cfg := DefaultConfig()
    
    // 服务信息
    if v := os.Getenv("SERVICE_NAME"); v != "" {
        cfg.ServiceName = v
    }
    if v := os.Getenv("SERVICE_VERSION"); v != "" {
        cfg.ServiceVersion = v
    }
    if v := os.Getenv("DEPLOYMENT_ENVIRONMENT"); v != "" {
        cfg.Environment = v
    }
    
    // 导出配置
    if v := os.Getenv("OTEL_EXPORTER_TYPE"); v != "" {
        cfg.ExporterType = v
    }
    if v := os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT"); v != "" {
        cfg.Endpoint = v
    }
    if v := os.Getenv("OTEL_EXPORTER_OTLP_INSECURE"); v != "" {
        cfg.Insecure = v == "true"
    }
    
    // 导出间隔
    if v := os.Getenv("OTEL_METRIC_EXPORT_INTERVAL"); v != "" {
        if d, err := time.ParseDuration(v); err == nil {
            cfg.ExportInterval = d
        }
    }
    
    return cfg
}

// 使用示例
func main() {
    cfg := LoadConfigFromEnv()
    mp, err := NewMeterProvider(cfg)
    if err != nil {
        log.Fatal(err)
    }
    defer mp.Shutdown(context.Background())
    
    otel.SetMeterProvider(mp)
}
```

---

## 生产环境配置

### 1. 标准配置

```go
func NewProductionMeterProvider() (*metric.MeterProvider, error) {
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
    exporter, _ := otlpmetricgrpc.New(
        context.Background(),
        otlpmetricgrpc.WithEndpoint(os.Getenv("OTEL_COLLECTOR_ENDPOINT")),
        otlpmetricgrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")),
    )
    
    // Periodic Reader (30秒间隔)
    reader := metric.NewPeriodicReader(
        exporter,
        metric.WithInterval(30*time.Second),
        metric.WithTimeout(10*time.Second),
    )
    
    // MeterProvider
    mp := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(reader),
    )
    
    return mp, nil
}
```

### 2. 高可用配置

```go
// 多后端导出
func NewHAMeterProvider() (*metric.MeterProvider, error) {
    res, _ := resource.New(...)
    
    // Primary OTLP Collector
    primary, _ := otlpmetricgrpc.New(
        context.Background(),
        otlpmetricgrpc.WithEndpoint("primary-collector:4317"),
    )
    
    // Backup OTLP Collector
    backup, _ := otlpmetricgrpc.New(
        context.Background(),
        otlpmetricgrpc.WithEndpoint("backup-collector:4317"),
    )
    
    // 创建多个 Reader
    mp := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(metric.NewPeriodicReader(primary)),
        metric.WithReader(metric.NewPeriodicReader(backup)),
    )
    
    return mp, nil
}
```

### 3. 云原生配置

```go
// Kubernetes 环境配置
func NewK8sMeterProvider() (*metric.MeterProvider, error) {
    res, _ := resource.New(
        context.Background(),
        // 服务信息
        resource.WithAttributes(
            semconv.ServiceName(os.Getenv("SERVICE_NAME")),
            semconv.ServiceVersion(os.Getenv("SERVICE_VERSION")),
        ),
        // K8s 信息 (从 Downward API)
        resource.WithAttributes(
            semconv.K8SNamespaceName(os.Getenv("K8S_NAMESPACE")),
            semconv.K8SPodName(os.Getenv("K8S_POD_NAME")),
            semconv.K8SNodeName(os.Getenv("K8S_NODE_NAME")),
        ),
        resource.WithHost(),
        resource.WithContainer(),
    )
    
    // OTLP Exporter (使用 K8s Service)
    exporter, _ := otlpmetricgrpc.New(
        context.Background(),
        otlpmetricgrpc.WithEndpoint("otel-collector.observability.svc.cluster.local:4317"),
        otlpmetricgrpc.WithInsecure(),
    )
    
    reader := metric.NewPeriodicReader(exporter)
    
    mp := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(reader),
    )
    
    return mp, nil
}
```

---

## 最佳实践

```go
// ✅ 正确: 在应用启动时初始化
func main() {
    mp, err := NewProductionMeterProvider()
    if err != nil {
        log.Fatal(err)
    }
    defer mp.Shutdown(context.Background())
    
    otel.SetMeterProvider(mp)
    
    // 应用逻辑
}

// ✅ 正确: 正确关闭
defer func() {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    if err := mp.Shutdown(ctx); err != nil {
        log.Printf("Error shutting down: %v", err)
    }
}()

// ✅ 正确: 使用合理的导出间隔
reader := metric.NewPeriodicReader(
    exporter,
    metric.WithInterval(30*time.Second), // 生产环境: 15-60秒
)

// ❌ 错误: 过短的导出间隔
reader := metric.NewPeriodicReader(
    exporter,
    metric.WithInterval(1*time.Second), // 太频繁！
)

// ✅ 正确: 包含完整的 Resource 信息
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

// ❌ 错误: Resource 信息不完整
res, _ := resource.New(
    context.Background(),
    resource.WithAttributes(
        semconv.ServiceName("myapp"),
    ),
)
```

---

## 常见问题

**Q1: PeriodicReader 和 ManualReader 如何选择？**

```text
PeriodicReader (推荐):
✅ 适用场景:
  - 生产环境
  - 持续监控
  - 自动导出

配置:
- Interval: 15-60秒 (根据需求)
- Timeout: 5-30秒

ManualReader:
✅ 适用场景:
  - 单元测试
  - 集成测试
  - 按需导出

推荐:
- 生产环境: PeriodicReader
- 测试环境: ManualReader
```

**Q2: 导出间隔如何选择？**

```text
考虑因素:
1. 可见性需求
   - 实时监控: 15-30秒
   - 一般监控: 60秒

2. 网络开销
   - 间隔越短 → 开销越大

3. 后端能力
   - 考虑后端处理能力

推荐:
- 开发: 10-15秒 (快速反馈)
- 生产: 30-60秒 (平衡)
- 低流量: 60秒+ (节省资源)
```

**Q3: 如何配置多个后端？**

```go
// 方案 1: 多 Reader
mp := metric.NewMeterProvider(
    metric.WithReader(metric.NewPeriodicReader(otlpExporter)),
    metric.WithReader(metric.NewPeriodicReader(promExporter)),
)

// 方案 2: 使用 OpenTelemetry Collector (推荐)
// 应用 → OTLP Collector → 多个后端
exporter, _ := otlpmetricgrpc.New(...)
mp := metric.NewMeterProvider(
    metric.WithReader(metric.NewPeriodicReader(exporter)),
)
```

---

## 参考资源

- [OpenTelemetry Metrics SDK](https://opentelemetry.io/docs/specs/otel/metrics/sdk/)
- [Go SDK MeterProvider](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/metric#MeterProvider)
- [02_Meter创建.md](./02_Meter创建.md)

---

**🎉 恭喜！你已经掌握了 MeterProvider 的配置！**

现在你可以：

- ✅ 配置 MeterProvider
- ✅ 使用 PeriodicReader 和 ManualReader
- ✅ 配置 Resource
- ✅ 为生产环境创建配置
- ✅ 处理多后端导出

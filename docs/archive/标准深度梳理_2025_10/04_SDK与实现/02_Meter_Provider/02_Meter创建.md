# Meter 创建

## 📋 目录

- [Meter 创建](#meter-创建)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Meter](#什么是-meter)
    - [创建流程](#创建流程)
  - [基本创建](#基本创建)
    - [1. 从全局 MeterProvider 创建](#1-从全局-meterprovider-创建)
    - [2. 从自定义 MeterProvider 创建](#2-从自定义-meterprovider-创建)
    - [3. 带选项创建](#3-带选项创建)
  - [InstrumentationScope 配置](#instrumentationscope-配置)
    - [1. Name 配置](#1-name-配置)
    - [2. Version 配置](#2-version-配置)
    - [3. SchemaURL 配置](#3-schemaurl-配置)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本实现](#1-基本实现)
    - [2. Meter 缓存](#2-meter-缓存)
    - [3. Meter 注册表](#3-meter-注册表)
  - [Meter 管理](#meter-管理)
    - [1. 单例模式](#1-单例模式)
    - [2. 模块级 Meter](#2-模块级-meter)
    - [3. 包级 Meter](#3-包级-meter)
  - [Meter 使用](#meter-使用)
    - [1. 创建 Counter](#1-创建-counter)
    - [2. 创建 Histogram](#2-创建-histogram)
    - [3. 创建 Gauge](#3-创建-gauge)
  - [性能优化](#性能优化)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 Meter

**Meter** 是 OpenTelemetry Metrics 中用于创建 Instrument（Counter、Histogram、Gauge等）的工具。每个 Meter 关联一个 InstrumentationScope，标识指标的来源。

```text
MeterProvider (全局)
    ↓
Meter (per InstrumentationScope)
    ↓
Instrument (Counter, Histogram, Gauge, etc.)
    ↓
Measurement (记录数值)
```

### 创建流程

```text
1. 应用启动时设置 MeterProvider
2. 模块/包初始化时创建 Meter
3. 使用 Meter 创建 Instrument
4. 使用 Instrument 记录 Measurement
5. 应用关闭时清理 MeterProvider
```

---

## 基本创建

### 1. 从全局 MeterProvider 创建

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

func main() {
    // 从全局 MeterProvider 获取 Meter
    meter := otel.Meter("myapp")
    
    // 使用 Meter 创建 Counter
    counter, _ := meter.Int64Counter("requests")
    counter.Add(context.Background(), 1)
}
```

### 2. 从自定义 MeterProvider 创建

```go
package main

import (
    "go.opentelemetry.io/otel/sdk/metric"
)

func main() {
    // 创建自定义 MeterProvider
    mp := metric.NewMeterProvider()
    
    // 从自定义 MeterProvider 获取 Meter
    meter := mp.Meter("myapp")
    
    // 使用 Meter
    counter, _ := meter.Int64Counter("requests")
    counter.Add(context.Background(), 1)
}
```

### 3. 带选项创建

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

func main() {
    // 带选项创建 Meter
    meter := otel.Meter(
        "myapp",
        metric.WithInstrumentationVersion("1.0.0"),
        metric.WithSchemaURL("https://opentelemetry.io/schemas/1.21.0"),
    )
    
    counter, _ := meter.Int64Counter("requests")
    counter.Add(context.Background(), 1)
}
```

---

## InstrumentationScope 配置

### 1. Name 配置

Name 应该唯一标识仪表化库或模块：

```go
// ✅ 推荐：使用包的导入路径
meter := otel.Meter("github.com/myorg/myapp/api")

// ✅ 推荐：使用模块路径
meter := otel.Meter("myapp/database")

// ❌ 不推荐：使用笼统名称
meter := otel.Meter("app")

// ❌ 不推荐：使用大写
meter := otel.Meter("MyApp")
```

**命名约定**:

```text
✅ 使用小写
✅ 使用斜杠 / 或点号 . 分隔
✅ 反映代码组织结构
✅ 全局唯一

示例:
- "github.com/myorg/myapp"
- "myapp/api"
- "myapp/database/postgresql"
```

### 2. Version 配置

Version 标识仪表化库的版本：

```go
// 库级别：使用库的版本
meter := otel.Meter(
    "github.com/myorg/mylib",
    metric.WithInstrumentationVersion("1.2.3"),
)

// 应用级别：使用应用的版本
var Version = "1.0.0" // 从构建时注入

meter := otel.Meter(
    "myapp",
    metric.WithInstrumentationVersion(Version),
)

// 开发环境：可以使用 "dev"
meter := otel.Meter(
    "myapp",
    metric.WithInstrumentationVersion("dev"),
)
```

### 3. SchemaURL 配置

SchemaURL 标识语义约定的版本：

```go
import semconv "go.opentelemetry.io/otel/semconv/v1.21.0"

meter := otel.Meter(
    "myapp",
    metric.WithInstrumentationVersion("1.0.0"),
    metric.WithSchemaURL(semconv.SchemaURL),
)
```

---

## Go 1.25.1 实现

### 1. 基本实现

```go
package metrics

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

// MeterConfig Meter 配置
type MeterConfig struct {
    Name    string
    Version string
    Schema  string
}

// NewMeter 创建新的 Meter
func NewMeter(cfg MeterConfig) metric.Meter {
    opts := []metric.MeterOption{}
    
    if cfg.Version != "" {
        opts = append(opts, metric.WithInstrumentationVersion(cfg.Version))
    }
    
    if cfg.Schema != "" {
        opts = append(opts, metric.WithSchemaURL(cfg.Schema))
    }
    
    return otel.Meter(cfg.Name, opts...)
}

// 使用示例
func main() {
    meter := NewMeter(MeterConfig{
        Name:    "myapp",
        Version: "1.0.0",
        Schema:  "https://opentelemetry.io/schemas/1.21.0",
    })
    
    counter, _ := meter.Int64Counter("requests")
    counter.Add(context.Background(), 1)
}
```

### 2. Meter 缓存

```go
package metrics

import (
    "sync"
    "go.opentelemetry.io/otel/metric"
)

// MeterCache Meter 缓存
type MeterCache struct {
    mu     sync.RWMutex
    meters map[string]metric.Meter
}

// NewMeterCache 创建缓存
func NewMeterCache() *MeterCache {
    return &MeterCache{
        meters: make(map[string]metric.Meter),
    }
}

// GetOrCreate 获取或创建 Meter
func (c *MeterCache) GetOrCreate(cfg MeterConfig) metric.Meter {
    key := cfg.Name + "@" + cfg.Version
    
    // 快速路径：读锁
    c.mu.RLock()
    if meter, ok := c.meters[key]; ok {
        c.mu.RUnlock()
        return meter
    }
    c.mu.RUnlock()
    
    // 慢速路径：写锁
    c.mu.Lock()
    defer c.mu.Unlock()
    
    // 双重检查
    if meter, ok := c.meters[key]; ok {
        return meter
    }
    
    // 创建新 Meter
    meter := NewMeter(cfg)
    c.meters[key] = meter
    return meter
}

// 全局缓存
var globalCache = NewMeterCache()

// GetMeter 从全局缓存获取 Meter
func GetMeter(name, version string) metric.Meter {
    return globalCache.GetOrCreate(MeterConfig{
        Name:    name,
        Version: version,
    })
}
```

### 3. Meter 注册表

```go
package metrics

import (
    "fmt"
    "sync"
)

// MeterRegistry Meter 注册表
type MeterRegistry struct {
    mu     sync.RWMutex
    meters map[string]metric.Meter
}

// NewMeterRegistry 创建注册表
func NewMeterRegistry() *MeterRegistry {
    return &MeterRegistry{
        meters: make(map[string]metric.Meter),
    }
}

// Register 注册 Meter
func (r *MeterRegistry) Register(name string, meter metric.Meter) error {
    r.mu.Lock()
    defer r.mu.Unlock()
    
    if _, exists := r.meters[name]; exists {
        return fmt.Errorf("meter %s already registered", name)
    }
    
    r.meters[name] = meter
    return nil
}

// Get 获取 Meter
func (r *MeterRegistry) Get(name string) (metric.Meter, bool) {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    meter, ok := r.meters[name]
    return meter, ok
}

// List 列出所有 Meter
func (r *MeterRegistry) List() []string {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    names := make([]string, 0, len(r.meters))
    for name := range r.meters {
        names = append(names, name)
    }
    return names
}

// 使用示例
var registry = NewMeterRegistry()

func init() {
    apiMeter := otel.Meter("myapp/api")
    registry.Register("api", apiMeter)
    
    dbMeter := otel.Meter("myapp/database")
    registry.Register("database", dbMeter)
}
```

---

## Meter 管理

### 1. 单例模式

```go
package metrics

import (
    "sync"
    "go.opentelemetry.io/otel"
)

var (
    meter     metric.Meter
    meterOnce sync.Once
)

// GetMeter 获取单例 Meter
func GetMeter() metric.Meter {
    meterOnce.Do(func() {
        meter = otel.Meter(
            "myapp",
            metric.WithInstrumentationVersion("1.0.0"),
        )
    })
    return meter
}

// 使用示例
func RecordRequest(ctx context.Context) {
    meter := GetMeter()
    counter, _ := meter.Int64Counter("requests")
    counter.Add(ctx, 1)
}
```

### 2. 模块级 Meter

```go
package api

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

// 模块级 Meter
var meter = otel.Meter("myapp/api")

// 模块级 Instrument
var (
    requestCounter  metric.Int64Counter
    requestDuration metric.Float64Histogram
)

func init() {
    var err error
    
    requestCounter, err = meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Number of HTTP requests"),
    )
    if err != nil {
        panic(err)
    }
    
    requestDuration, err = meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        panic(err)
    }
}

func HandleRequest(ctx context.Context) {
    start := time.Now()
    
    // 记录请求
    requestCounter.Add(ctx, 1)
    
    // 业务逻辑
    // ...
    
    // 记录持续时间
    duration := time.Since(start).Milliseconds()
    requestDuration.Record(ctx, float64(duration))
}
```

### 3. 包级 Meter

```go
package database

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/attribute"
)

var meter = otel.Meter("myapp/database/postgresql")

var (
    queryCounter  metric.Int64Counter
    queryDuration metric.Float64Histogram
)

func init() {
    queryCounter, _ = meter.Int64Counter("db.queries")
    queryDuration, _ = meter.Float64Histogram("db.query.duration")
}

func Query(ctx context.Context, query string) error {
    start := time.Now()
    
    // 记录查询
    queryCounter.Add(ctx, 1, metric.WithAttributes(
        attribute.String("db.operation", "select"),
    ))
    
    // 执行查询
    // ...
    
    // 记录持续时间
    duration := time.Since(start).Milliseconds()
    queryDuration.Record(ctx, float64(duration))
    
    return nil
}
```

---

## Meter 使用

### 1. 创建 Counter

```go
package main

func main() {
    meter := otel.Meter("myapp")
    
    // Int64 Counter
    counter, _ := meter.Int64Counter(
        "requests.count",
        metric.WithDescription("Total number of requests"),
        metric.WithUnit("{request}"),
    )
    
    // 记录
    counter.Add(context.Background(), 1, metric.WithAttributes(
        attribute.String("method", "GET"),
        attribute.String("path", "/api/users"),
    ))
    
    // Float64 Counter
    dataCounter, _ := meter.Float64Counter(
        "data.processed",
        metric.WithDescription("Amount of data processed"),
        metric.WithUnit("By"),
    )
    
    dataCounter.Add(context.Background(), 1024.5)
}
```

### 2. 创建 Histogram

```go
package main

func main() {
    meter := otel.Meter("myapp")
    
    // Float64 Histogram
    histogram, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    
    // 记录持续时间
    start := time.Now()
    // ... 业务逻辑
    duration := time.Since(start).Milliseconds()
    
    histogram.Record(context.Background(), float64(duration), metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.String("http.route", "/api/users"),
        attribute.Int("http.status_code", 200),
    ))
    
    // Int64 Histogram
    sizeHistogram, _ := meter.Int64Histogram(
        "response.size",
        metric.WithDescription("Response size in bytes"),
        metric.WithUnit("By"),
    )
    
    sizeHistogram.Record(context.Background(), 1024)
}
```

### 3. 创建 Gauge

```go
package main

func main() {
    meter := otel.Meter("myapp")
    
    // Int64 Gauge (通过 ObservableGauge)
    _, _ = meter.Int64ObservableGauge(
        "memory.used",
        metric.WithDescription("Current memory usage"),
        metric.WithUnit("By"),
        metric.WithInt64Callback(func(ctx context.Context, o metric.Int64Observer) error {
            // 获取当前内存使用
            var m runtime.MemStats
            runtime.ReadMemStats(&m)
            o.Observe(int64(m.Alloc))
            return nil
        }),
    )
    
    // Float64 Gauge
    _, _ = meter.Float64ObservableGauge(
        "cpu.utilization",
        metric.WithDescription("CPU utilization"),
        metric.WithUnit("1"),
        metric.WithFloat64Callback(func(ctx context.Context, o metric.Float64Observer) error {
            // 获取 CPU 使用率
            utilization := getCPUUtilization()
            o.Observe(utilization)
            return nil
        }),
    )
}
```

---

## 性能优化

```go
// 1. 缓存 Meter（避免重复创建）
var meter = otel.Meter("myapp")

func recordMetric(ctx context.Context) {
    // 复用 meter
    counter, _ := meter.Int64Counter("requests")
    counter.Add(ctx, 1)
}

// 2. 缓存 Instrument（更重要！）
var (
    meter   = otel.Meter("myapp")
    counter metric.Int64Counter
)

func init() {
    counter, _ = meter.Int64Counter("requests")
}

func recordMetric(ctx context.Context) {
    // 复用 instrument
    counter.Add(ctx, 1)
}

// 3. 使用 sync.OnceFunc (Go 1.25.1)
var getMeter = sync.OnceFunc(func() metric.Meter {
    return otel.Meter(
        "myapp",
        metric.WithInstrumentationVersion("1.0.0"),
    )
})

// 4. 预分配 Instrument（应用启动时）
var (
    meter           = otel.Meter("myapp")
    requestCounter  metric.Int64Counter
    requestDuration metric.Float64Histogram
    activeRequests  metric.Int64UpDownCounter
)

func init() {
    requestCounter, _ = meter.Int64Counter("requests")
    requestDuration, _ = meter.Float64Histogram("duration")
    activeRequests, _ = meter.Int64UpDownCounter("active")
}

// 5. 避免不必要的 Meter 创建
// ❌ 错误
func recordMetric(ctx context.Context) {
    meter := otel.Meter("myapp") // 每次调用都创建
    counter, _ := meter.Int64Counter("requests")
    counter.Add(ctx, 1)
}

// ✅ 正确
var meter = otel.Meter("myapp")
var counter, _ = meter.Int64Counter("requests")

func recordMetric(ctx context.Context) {
    counter.Add(ctx, 1)
}
```

---

## 最佳实践

```go
// ✅ 正确: 在包级别定义 Meter 和 Instrument
package api

var meter = otel.Meter("myapp/api", metric.WithInstrumentationVersion("1.0.0"))

var (
    requestCounter  metric.Int64Counter
    requestDuration metric.Float64Histogram
)

func init() {
    requestCounter, _ = meter.Int64Counter("http.server.requests")
    requestDuration, _ = meter.Float64Histogram("http.server.duration")
}

// ✅ 正确: 使用有意义的 Meter 名称
meter := otel.Meter("github.com/myorg/myapp/api")

// ❌ 错误: 使用笼统名称
meter := otel.Meter("app")

// ✅ 正确: 为不同模块使用不同 Meter
var (
    apiMeter = otel.Meter("myapp/api")
    dbMeter  = otel.Meter("myapp/database")
)

// ❌ 错误: 所有模块共用一个 Meter
var meter = otel.Meter("myapp")

// ✅ 正确: 缓存 Instrument
var counter, _ = meter.Int64Counter("requests")

func handler(ctx context.Context) {
    counter.Add(ctx, 1) // 快速
}

// ❌ 错误: 每次都创建 Instrument
func handler(ctx context.Context) {
    counter, _ := meter.Int64Counter("requests") // 慢！
    counter.Add(ctx, 1)
}

// ✅ 正确: 处理错误
counter, err := meter.Int64Counter("requests")
if err != nil {
    log.Printf("Failed to create counter: %v", err)
    return
}

// ❌ 错误: 忽略错误
counter, _ := meter.Int64Counter("requests")
```

---

## 常见问题

**Q1: 何时应该创建新的 Meter？**

```text
应该创建新 Meter:
✅ 为每个独立的库/模块创建
✅ 为可重用组件创建
✅ 为不同版本的库创建

不应该创建新 Meter:
❌ 为每个函数创建
❌ 为每个请求创建
❌ 动态创建（运行时频繁创建）

推荐粒度:
- 包级别: myapp/api, myapp/database
- 模块级别: myapp/api/v1, myapp/api/v2
```

**Q2: Meter 和 Instrument 的区别？**

```text
Meter:
- 工厂：用于创建 Instrument
- 生命周期：与应用同生命周期
- 复用：应该被缓存和复用
- 标识：InstrumentationScope (name, version)

Instrument:
- 实例：表示单个指标（Counter, Histogram, etc.）
- 生命周期：与应用同生命周期
- 唯一：同名 Instrument 在同一 Meter 中唯一
- 记录：调用 Add/Record 记录测量值
```

**Q3: 如何为第三方库创建 Meter？**

```go
// 为第三方库创建 Meter
import (
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
)

// 使用第三方库的包路径作为 Meter 名称
var ginMeter = otel.Meter(
    "github.com/gin-gonic/gin",
    metric.WithInstrumentationVersion(gin.Version),
)

// 或者使用自己的仪表化包路径
var ginMeter = otel.Meter(
    "myapp/instrumentation/gin",
    metric.WithInstrumentationVersion("1.0.0"),
)
```

**Q4: Instrument 创建失败怎么办？**

```go
// 方案 1: 检查错误
counter, err := meter.Int64Counter("requests")
if err != nil {
    log.Printf("Failed to create counter: %v", err)
    // 使用 noop counter
    counter = noopCounter{}
}

// 方案 2: Panic（在 init 中）
func init() {
    var err error
    counter, err = meter.Int64Counter("requests")
    if err != nil {
        panic(fmt.Sprintf("Failed to create counter: %v", err))
    }
}

// 方案 3: 使用 Must (自定义)
func MustCounter(meter metric.Meter, name string, opts ...metric.Int64CounterOption) metric.Int64Counter {
    counter, err := meter.Int64Counter(name, opts...)
    if err != nil {
        panic(err)
    }
    return counter
}

var counter = MustCounter(meter, "requests")
```

---

## 参考资源

- [OpenTelemetry Meter API](https://opentelemetry.io/docs/specs/otel/metrics/api/#meter)
- [Go SDK Meter](https://pkg.go.dev/go.opentelemetry.io/otel/metric#Meter)
- [01_Provider配置.md](./01_Provider配置.md)
- [03_视图配置.md](./03_视图配置.md)

---

**🎉 恭喜！你已经掌握了 Meter 的创建和管理！**

现在你可以：

- ✅ 创建和配置 Meter
- ✅ 使用 InstrumentationScope 标识
- ✅ 实现 Meter 缓存和注册表
- ✅ 管理模块级和包级 Meter
- ✅ 使用 Meter 创建各种 Instrument

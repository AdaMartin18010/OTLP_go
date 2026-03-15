# Tracer 创建

## 📋 目录

- [Tracer 创建](#tracer-创建)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Tracer](#什么是-tracer)
    - [创建流程](#创建流程)
  - [基本创建](#基本创建)
    - [1. 从全局 TracerProvider 创建](#1-从全局-tracerprovider-创建)
    - [2. 从自定义 TracerProvider 创建](#2-从自定义-tracerprovider-创建)
    - [3. 带选项创建](#3-带选项创建)
  - [InstrumentationScope 配置](#instrumentationscope-配置)
    - [1. Name 配置](#1-name-配置)
    - [2. Version 配置](#2-version-配置)
    - [3. SchemaURL 配置](#3-schemaurl-配置)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本实现](#1-基本实现)
    - [2. Tracer 缓存](#2-tracer-缓存)
    - [3. Tracer 注册表](#3-tracer-注册表)
  - [Tracer 管理](#tracer-管理)
    - [1. 单例模式](#1-单例模式)
    - [2. 模块级 Tracer](#2-模块级-tracer)
    - [3. 包级 Tracer](#3-包级-tracer)
  - [Tracer 使用](#tracer-使用)
    - [1. 创建 Span](#1-创建-span)
    - [2. 嵌套 Span](#2-嵌套-span)
    - [3. Context 传播](#3-context-传播)
  - [性能优化](#性能优化)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 Tracer

**Tracer** 是 OpenTelemetry 中用于创建 Span 的工具。每个 Tracer 关联一个 InstrumentationScope，标识遥测数据的来源。

```text
TracerProvider (全局)
    ↓
Tracer (per InstrumentationScope)
    ↓
Span (per operation)
```

### 创建流程

```text
1. 应用启动时设置 TracerProvider
2. 模块/包初始化时创建 Tracer
3. 使用 Tracer 创建 Span
4. 应用关闭时清理 TracerProvider
```

---

## 基本创建

### 1. 从全局 TracerProvider 创建

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 从全局 TracerProvider 获取 Tracer
    tracer := otel.Tracer("myapp")
    
    // 使用 Tracer 创建 Span
    ctx, span := tracer.Start(context.Background(), "operation")
    defer span.End()
    
    // ... 业务逻辑
}
```

### 2. 从自定义 TracerProvider 创建

```go
package main

import (
    "go.opentelemetry.io/otel/sdk/trace"
)

func main() {
    // 创建自定义 TracerProvider
    tp := trace.NewTracerProvider()
    
    // 从自定义 TracerProvider 获取 Tracer
    tracer := tp.Tracer("myapp")
    
    // 使用 Tracer
    ctx, span := tracer.Start(context.Background(), "operation")
    defer span.End()
}
```

### 3. 带选项创建

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 带选项创建 Tracer
    tracer := otel.Tracer(
        "myapp",
        trace.WithInstrumentationVersion("1.0.0"),
        trace.WithSchemaURL("https://opentelemetry.io/schemas/1.21.0"),
    )
    
    ctx, span := tracer.Start(context.Background(), "operation")
    defer span.End()
}
```

---

## InstrumentationScope 配置

### 1. Name 配置

Name 应该唯一标识仪表化库或模块：

```go
// ✅ 推荐：使用包的导入路径
tracer := otel.Tracer("github.com/myorg/myapp/api")

// ✅ 推荐：使用模块路径
tracer := otel.Tracer("myapp/database")

// ❌ 不推荐：使用笼统名称
tracer := otel.Tracer("app")

// ❌ 不推荐：使用大写
tracer := otel.Tracer("MyApp")
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
tracer := otel.Tracer(
    "github.com/myorg/mylib",
    trace.WithInstrumentationVersion("1.2.3"),
)

// 应用级别：使用应用的版本
var Version = "1.0.0" // 从构建时注入

tracer := otel.Tracer(
    "myapp",
    trace.WithInstrumentationVersion(Version),
)

// 开发环境：可以使用 "dev"
tracer := otel.Tracer(
    "myapp",
    trace.WithInstrumentationVersion("dev"),
)
```

### 3. SchemaURL 配置

SchemaURL 标识语义约定的版本：

```go
import semconv "go.opentelemetry.io/otel/semconv/v1.21.0"

tracer := otel.Tracer(
    "myapp",
    trace.WithInstrumentationVersion("1.0.0"),
    trace.WithSchemaURL(semconv.SchemaURL),
)
```

---

## Go 1.25.1 实现

### 1. 基本实现

```go
package tracing

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// TracerConfig Tracer 配置
type TracerConfig struct {
    Name    string
    Version string
    Schema  string
}

// NewTracer 创建新的 Tracer
func NewTracer(cfg TracerConfig) trace.Tracer {
    opts := []trace.TracerOption{}
    
    if cfg.Version != "" {
        opts = append(opts, trace.WithInstrumentationVersion(cfg.Version))
    }
    
    if cfg.Schema != "" {
        opts = append(opts, trace.WithSchemaURL(cfg.Schema))
    }
    
    return otel.Tracer(cfg.Name, opts...)
}

// 使用示例
func main() {
    tracer := NewTracer(TracerConfig{
        Name:    "myapp",
        Version: "1.0.0",
        Schema:  "https://opentelemetry.io/schemas/1.21.0",
    })
    
    ctx, span := tracer.Start(context.Background(), "operation")
    defer span.End()
}
```

### 2. Tracer 缓存

```go
package tracing

import (
    "sync"
    "go.opentelemetry.io/otel/trace"
)

// TracerCache Tracer 缓存
type TracerCache struct {
    mu      sync.RWMutex
    tracers map[string]trace.Tracer
}

// NewTracerCache 创建缓存
func NewTracerCache() *TracerCache {
    return &TracerCache{
        tracers: make(map[string]trace.Tracer),
    }
}

// GetOrCreate 获取或创建 Tracer
func (c *TracerCache) GetOrCreate(cfg TracerConfig) trace.Tracer {
    key := cfg.Name + "@" + cfg.Version
    
    // 快速路径：读锁
    c.mu.RLock()
    if tracer, ok := c.tracers[key]; ok {
        c.mu.RUnlock()
        return tracer
    }
    c.mu.RUnlock()
    
    // 慢速路径：写锁
    c.mu.Lock()
    defer c.mu.Unlock()
    
    // 双重检查
    if tracer, ok := c.tracers[key]; ok {
        return tracer
    }
    
    // 创建新 Tracer
    tracer := NewTracer(cfg)
    c.tracers[key] = tracer
    return tracer
}

// 全局缓存
var globalCache = NewTracerCache()

// GetTracer 从全局缓存获取 Tracer
func GetTracer(name, version string) trace.Tracer {
    return globalCache.GetOrCreate(TracerConfig{
        Name:    name,
        Version: version,
    })
}
```

### 3. Tracer 注册表

```go
package tracing

import (
    "fmt"
    "sync"
)

// TracerRegistry Tracer 注册表
type TracerRegistry struct {
    mu      sync.RWMutex
    tracers map[string]trace.Tracer
}

// NewTracerRegistry 创建注册表
func NewTracerRegistry() *TracerRegistry {
    return &TracerRegistry{
        tracers: make(map[string]trace.Tracer),
    }
}

// Register 注册 Tracer
func (r *TracerRegistry) Register(name string, tracer trace.Tracer) error {
    r.mu.Lock()
    defer r.mu.Unlock()
    
    if _, exists := r.tracers[name]; exists {
        return fmt.Errorf("tracer %s already registered", name)
    }
    
    r.tracers[name] = tracer
    return nil
}

// Get 获取 Tracer
func (r *TracerRegistry) Get(name string) (trace.Tracer, bool) {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    tracer, ok := r.tracers[name]
    return tracer, ok
}

// List 列出所有 Tracer
func (r *TracerRegistry) List() []string {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    names := make([]string, 0, len(r.tracers))
    for name := range r.tracers {
        names = append(names, name)
    }
    return names
}

// 使用示例
var registry = NewTracerRegistry()

func init() {
    apiTracer := otel.Tracer("myapp/api")
    registry.Register("api", apiTracer)
    
    dbTracer := otel.Tracer("myapp/database")
    registry.Register("database", dbTracer)
}
```

---

## Tracer 管理

### 1. 单例模式

```go
package tracing

import (
    "sync"
    "go.opentelemetry.io/otel"
)

var (
    tracer     trace.Tracer
    tracerOnce sync.Once
)

// GetTracer 获取单例 Tracer
func GetTracer() trace.Tracer {
    tracerOnce.Do(func() {
        tracer = otel.Tracer(
            "myapp",
            trace.WithInstrumentationVersion("1.0.0"),
        )
    })
    return tracer
}

// 使用示例
func HandleRequest(ctx context.Context) {
    tracer := GetTracer()
    ctx, span := tracer.Start(ctx, "HandleRequest")
    defer span.End()
}
```

### 2. 模块级 Tracer

```go
package api

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// 模块级 Tracer
var tracer = otel.Tracer("myapp/api")

func HandleRequest(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "HandleRequest")
    defer span.End()
    
    // ... 业务逻辑
}

func ProcessData(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "ProcessData")
    defer span.End()
    
    // ... 业务逻辑
}
```

### 3. 包级 Tracer

```go
package database

import (
    "go.opentelemetry.io/otel"
)

var tracer = otel.Tracer("myapp/database/postgresql")

func Query(ctx context.Context, query string) error {
    ctx, span := tracer.Start(ctx, "Query")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("db.statement", query),
    )
    
    // ... 查询逻辑
    return nil
}
```

---

## Tracer 使用

### 1. 创建 Span

```go
package main

func Operation(ctx context.Context) {
    tracer := otel.Tracer("myapp")
    
    // 创建 Span
    ctx, span := tracer.Start(ctx, "Operation")
    defer span.End()
    
    // 添加属性
    span.SetAttributes(
        attribute.String("user.id", "12345"),
        attribute.String("operation.type", "read"),
    )
    
    // 添加事件
    span.AddEvent("Processing started")
    
    // 业务逻辑
    result, err := doWork(ctx)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return
    }
    
    span.AddEvent("Processing completed")
    span.SetStatus(codes.Ok, "")
}
```

### 2. 嵌套 Span

```go
func ParentOperation(ctx context.Context) {
    tracer := otel.Tracer("myapp")
    
    // 父 Span
    ctx, parentSpan := tracer.Start(ctx, "ParentOperation")
    defer parentSpan.End()
    
    // 子 Span 1
    childOperation1(ctx)
    
    // 子 Span 2
    childOperation2(ctx)
}

func childOperation1(ctx context.Context) {
    tracer := otel.Tracer("myapp")
    
    // 自动成为 ParentOperation 的子 Span
    ctx, span := tracer.Start(ctx, "ChildOperation1")
    defer span.End()
    
    // ... 业务逻辑
}

func childOperation2(ctx context.Context) {
    tracer := otel.Tracer("myapp")
    
    ctx, span := tracer.Start(ctx, "ChildOperation2")
    defer span.End()
    
    // ... 业务逻辑
}
```

### 3. Context 传播

```go
package main

// HTTP Handler
func HTTPHandler(w http.ResponseWriter, r *http.Request) {
    tracer := otel.Tracer("myapp/api")
    
    // 从 HTTP 请求提取 Context
    ctx := otel.GetTextMapPropagator().Extract(
        r.Context(),
        propagation.HeaderCarrier(r.Header),
    )
    
    // 创建 Span
    ctx, span := tracer.Start(ctx, "HTTPHandler")
    defer span.End()
    
    // 调用业务逻辑，传递 Context
    result := businessLogic(ctx)
    
    // 返回响应
    json.NewEncoder(w).Encode(result)
}

// 业务逻辑
func businessLogic(ctx context.Context) interface{} {
    tracer := otel.Tracer("myapp/service")
    
    // Context 中包含父 Span 信息
    ctx, span := tracer.Start(ctx, "BusinessLogic")
    defer span.End()
    
    // 调用数据库
    data := queryDatabase(ctx)
    
    return data
}

// 数据库查询
func queryDatabase(ctx context.Context) interface{} {
    tracer := otel.Tracer("myapp/database")
    
    // 继续传播 Context
    ctx, span := tracer.Start(ctx, "QueryDatabase")
    defer span.End()
    
    // ... 数据库操作
    return nil
}
```

---

## 性能优化

```go
// 1. 缓存 Tracer（避免重复创建）
var tracer = otel.Tracer("myapp")

func operation(ctx context.Context) {
    // 复用 tracer
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
}

// 2. 使用 sync.OnceFunc (Go 1.25.1)
var getTracer = sync.OnceFunc(func() trace.Tracer {
    return otel.Tracer(
        "myapp",
        trace.WithInstrumentationVersion("1.0.0"),
    )
})

func operation(ctx context.Context) {
    tracer := getTracer()
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
}

// 3. 预分配 Tracer（应用启动时）
var (
    apiTracer = otel.Tracer("myapp/api")
    dbTracer  = otel.Tracer("myapp/database")
    cacheTracer = otel.Tracer("myapp/cache")
)

// 4. 避免不必要的 Tracer 创建
// ❌ 错误
func operation(ctx context.Context) {
    tracer := otel.Tracer("myapp") // 每次调用都创建
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
}

// ✅ 正确
var tracer = otel.Tracer("myapp")

func operation(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
}
```

---

## 最佳实践

```go
// ✅ 正确：在包级别定义 Tracer
package api

var tracer = otel.Tracer("myapp/api", trace.WithInstrumentationVersion("1.0.0"))

func Handler(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "Handler")
    defer span.End()
}

// ✅ 正确：使用有意义的 Tracer 名称
tracer := otel.Tracer("github.com/myorg/myapp/api")

// ❌ 错误：使用笼统名称
tracer := otel.Tracer("app")

// ✅ 正确：为不同模块使用不同 Tracer
var (
    apiTracer = otel.Tracer("myapp/api")
    dbTracer  = otel.Tracer("myapp/database")
)

// ❌ 错误：所有模块共用一个 Tracer
var tracer = otel.Tracer("myapp")

// ✅ 正确：在函数调用链中传递 Context
func Parent(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "Parent")
    defer span.End()
    
    Child(ctx) // 传递 Context
}

func Child(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "Child")
    defer span.End()
}

// ❌ 错误：不传递 Context
func Parent(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "Parent")
    defer span.End()
    
    Child(context.Background()) // 错误：丢失父 Span 信息
}
```

---

## 常见问题

**Q1: 何时应该创建新的 Tracer？**

```text
应该创建新 Tracer:
✅ 为每个独立的库/模块创建
✅ 为可重用组件创建
✅ 为不同版本的库创建

不应该创建新 Tracer:
❌ 为每个函数创建
❌ 为每个请求创建
❌ 动态创建（运行时频繁创建）

推荐粒度:
- 包级别: myapp/api, myapp/database
- 模块级别: myapp/api/v1, myapp/api/v2
```

**Q2: Tracer 和 Span 的区别？**

```text
Tracer:
- 工厂：用于创建 Span
- 生命周期：与应用同生命周期
- 复用：应该被缓存和复用
- 标识：InstrumentationScope (name, version)

Span:
- 实例：表示单个操作
- 生命周期：短暂（操作开始到结束）
- 唯一：每次操作创建新 Span
- 标识：SpanID, TraceID
```

**Q3: 如何为第三方库创建 Tracer？**

```go
// 为第三方库创建 Tracer
import (
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
)

// 使用第三方库的包路径作为 Tracer 名称
var ginTracer = otel.Tracer(
    "github.com/gin-gonic/gin",
    trace.WithInstrumentationVersion(gin.Version),
)

// 或者使用自己的仪表化包路径
var ginTracer = otel.Tracer(
    "myapp/instrumentation/gin",
    trace.WithInstrumentationVersion("1.0.0"),
)
```

---

## 参考资源

- [OpenTelemetry Tracer API](https://opentelemetry.io/docs/specs/otel/trace/api/#tracer)
- [Go SDK Tracer](https://pkg.go.dev/go.opentelemetry.io/otel/trace#Tracer)
- [01_Provider配置.md](./01_Provider配置.md)
- [03_采样器.md](./03_采样器.md)

---

**🎉 恭喜！你已经掌握了 Tracer 的创建和管理！**

现在你可以：

- ✅ 创建和配置 Tracer
- ✅ 使用 InstrumentationScope 标识
- ✅ 实现 Tracer 缓存和注册表
- ✅ 管理模块级和包级 Tracer
- ✅ 使用 Tracer 创建 Span 和传播 Context

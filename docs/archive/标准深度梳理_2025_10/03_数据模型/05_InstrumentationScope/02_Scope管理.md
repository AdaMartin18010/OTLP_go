# Scope 管理

## 📋 目录

- [Scope 管理](#scope-管理)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Scope 创建](#scope-创建)
    - [1. 基本创建](#1-基本创建)
    - [2. 使用构建器](#2-使用构建器)
    - [3. 从配置创建](#3-从配置创建)
  - [Scope 获取](#scope-获取)
    - [1. Tracer Scope](#1-tracer-scope)
    - [2. Meter Scope](#2-meter-scope)
    - [3. Logger Scope](#3-logger-scope)
  - [Scope 生命周期](#scope-生命周期)
    - [1. 初始化阶段](#1-初始化阶段)
    - [2. 使用阶段](#2-使用阶段)
    - [3. 清理阶段](#3-清理阶段)
  - [Scope 注册表](#scope-注册表)
    - [1. 全局注册表](#1-全局注册表)
    - [2. 作用域注册表](#2-作用域注册表)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. Scope Manager](#1-scope-manager)
    - [2. Scope Registry](#2-scope-registry)
    - [3. Scope Provider](#3-scope-provider)
  - [多 Scope 管理](#多-scope-管理)
    - [1. Scope 层次结构](#1-scope-层次结构)
    - [2. Scope 过滤](#2-scope-过滤)
    - [3. Scope 聚合](#3-scope-聚合)
  - [最佳实践](#最佳实践)
  - [参考资源](#参考资源)

---

## 概述

**Scope 管理** 涉及 InstrumentationScope 的创建、获取、存储和生命周期管理。

```text
Scope 管理的核心任务:
✅ 创建和配置 Scope
✅ 获取和复用 Scope
✅ 管理 Scope 的生命周期
✅ 维护 Scope 注册表
```

---

## Scope 创建

### 1. 基本创建

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 创建 Tracer 时指定 Scope
func CreateTracer() trace.Tracer {
    return otel.GetTracerProvider().Tracer(
        "myapp/api",                              // name
        trace.WithInstrumentationVersion("1.0.0"), // version
        trace.WithAttributes(
            attribute.String("module", "api"),
        ),
    )
}

// 创建 Meter 时指定 Scope
func CreateMeter() metric.Meter {
    return otel.GetMeterProvider().Meter(
        "myapp/metrics",
        metric.WithInstrumentationVersion("1.0.0"),
    )
}

// 创建 Logger 时指定 Scope
func CreateLogger() log.Logger {
    return otel.GetLoggerProvider().Logger(
        "myapp/logger",
        log.WithInstrumentationVersion("1.0.0"),
    )
}
```

### 2. 使用构建器

```go
package instrumentation

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ScopeBuilder Scope 构建器
type ScopeBuilder struct {
    name       string
    version    string
    attributes []attribute.KeyValue
}

// NewScopeBuilder 创建构建器
func NewScopeBuilder(name string) *ScopeBuilder {
    return &ScopeBuilder{
        name:       name,
        attributes: make([]attribute.KeyValue, 0),
    }
}

// WithVersion 设置版本
func (b *ScopeBuilder) WithVersion(version string) *ScopeBuilder {
    b.version = version
    return b
}

// WithAttribute 添加属性
func (b *ScopeBuilder) WithAttribute(kv attribute.KeyValue) *ScopeBuilder {
    b.attributes = append(b.attributes, kv)
    return b
}

// WithAttributes 添加多个属性
func (b *ScopeBuilder) WithAttributes(kvs ...attribute.KeyValue) *ScopeBuilder {
    b.attributes = append(b.attributes, kvs...)
    return b
}

// BuildTracer 构建 Tracer
func (b *ScopeBuilder) BuildTracer() trace.Tracer {
    opts := []trace.TracerOption{
        trace.WithInstrumentationVersion(b.version),
    }
    if len(b.attributes) > 0 {
        opts = append(opts, trace.WithAttributes(b.attributes...))
    }
    return otel.GetTracerProvider().Tracer(b.name, opts...)
}

// BuildMeter 构建 Meter
func (b *ScopeBuilder) BuildMeter() metric.Meter {
    opts := []metric.MeterOption{
        metric.WithInstrumentationVersion(b.version),
    }
    return otel.GetMeterProvider().Meter(b.name, opts...)
}

// 使用示例
func main() {
    tracer := NewScopeBuilder("myapp/api").
        WithVersion("1.0.0").
        WithAttribute(attribute.String("team", "platform")).
        BuildTracer()
    
    meter := NewScopeBuilder("myapp/metrics").
        WithVersion("1.0.0").
        BuildMeter()
}
```

### 3. 从配置创建

```go
package config

import (
    "encoding/json"
    "os"
)

// ScopeConfig Scope 配置
type ScopeConfig struct {
    Name       string            `json:"name"`
    Version    string            `json:"version"`
    Attributes map[string]string `json:"attributes"`
}

// LoadFromFile 从文件加载配置
func LoadFromFile(path string) (*ScopeConfig, error) {
    data, err := os.ReadFile(path)
    if err != nil {
        return nil, err
    }
    
    var config ScopeConfig
    if err := json.Unmarshal(data, &config); err != nil {
        return nil, err
    }
    
    return &config, nil
}

// CreateTracer 从配置创建 Tracer
func (c *ScopeConfig) CreateTracer() trace.Tracer {
    opts := []trace.TracerOption{
        trace.WithInstrumentationVersion(c.Version),
    }
    
    if len(c.Attributes) > 0 {
        attrs := make([]attribute.KeyValue, 0, len(c.Attributes))
        for k, v := range c.Attributes {
            attrs = append(attrs, attribute.String(k, v))
        }
        opts = append(opts, trace.WithAttributes(attrs...))
    }
    
    return otel.GetTracerProvider().Tracer(c.Name, opts...)
}

// 配置文件示例 (scope.json)
/*
{
  "name": "myapp/api",
  "version": "1.0.0",
  "attributes": {
    "team": "platform",
    "environment": "production"
  }
}
*/

// 使用示例
func main() {
    config, _ := LoadFromFile("scope.json")
    tracer := config.CreateTracer()
}
```

---

## Scope 获取

### 1. Tracer Scope

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

var tracer trace.Tracer

func init() {
    // 应用启动时创建并缓存 Tracer
    tracer = otel.GetTracerProvider().Tracer(
        "myapp/api",
        trace.WithInstrumentationVersion("1.0.0"),
    )
}

// 在整个应用中复用同一个 Tracer
func HandleRequest(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "HandleRequest")
    defer span.End()
    
    // ... 业务逻辑
}

func ProcessData(ctx context.Context) {
    // 同一个 Tracer，同一个 Scope
    ctx, span := tracer.Start(ctx, "ProcessData")
    defer span.End()
    
    // ... 业务逻辑
}
```

### 2. Meter Scope

```go
package metrics

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

var (
    meter          metric.Meter
    requestCounter metric.Int64Counter
    latencyHisto   metric.Float64Histogram
)

func init() {
    // 创建 Meter
    meter = otel.GetMeterProvider().Meter(
        "myapp/metrics",
        metric.WithInstrumentationVersion("1.0.0"),
    )
    
    // 创建指标
    requestCounter, _ = meter.Int64Counter("requests")
    latencyHisto, _ = meter.Float64Histogram("latency")
}

// 使用指标
func RecordRequest(ctx context.Context, duration float64) {
    requestCounter.Add(ctx, 1)
    latencyHisto.Record(ctx, duration)
}
```

### 3. Logger Scope

```go
package logger

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/log"
)

var logger log.Logger

func init() {
    logger = otel.GetLoggerProvider().Logger(
        "myapp/logger",
        log.WithInstrumentationVersion("1.0.0"),
    )
}

func Info(ctx context.Context, msg string, attrs ...any) {
    logger.Info(ctx, msg, attrs...)
}

func Error(ctx context.Context, msg string, attrs ...any) {
    logger.Error(ctx, msg, attrs...)
}
```

---

## Scope 生命周期

### 1. 初始化阶段

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// 应用启动时初始化
func InitializeInstrumentation() {
    // 1. 设置 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithResource(resource.Default()),
    )
    otel.SetTracerProvider(tp)
    
    // 2. 创建应用级 Tracer
    appTracer = otel.GetTracerProvider().Tracer(
        "myapp",
        trace.WithInstrumentationVersion("1.0.0"),
    )
    
    // 3. 创建模块级 Tracer
    apiTracer = otel.GetTracerProvider().Tracer(
        "myapp/api",
        trace.WithInstrumentationVersion("1.0.0"),
    )
    
    dbTracer = otel.GetTracerProvider().Tracer(
        "myapp/database",
        trace.WithInstrumentationVersion("1.0.0"),
    )
}

func main() {
    InitializeInstrumentation()
    // ... 应用逻辑
}
```

### 2. 使用阶段

```go
// 在整个应用生命周期中复用 Tracer
func HandleAPIRequest(ctx context.Context) {
    // API 模块使用 apiTracer
    ctx, span := apiTracer.Start(ctx, "HandleAPIRequest")
    defer span.End()
    
    // 调用数据库模块
    queryDatabase(ctx)
}

func queryDatabase(ctx context.Context) {
    // 数据库模块使用 dbTracer
    ctx, span := dbTracer.Start(ctx, "QueryDatabase")
    defer span.End()
    
    // ... 查询逻辑
}
```

### 3. 清理阶段

```go
// 应用关闭时清理
func Shutdown(ctx context.Context) error {
    // 刷新并关闭 TracerProvider
    if tp, ok := otel.GetTracerProvider().(*sdktrace.TracerProvider); ok {
        return tp.Shutdown(ctx)
    }
    return nil
}

func main() {
    InitializeInstrumentation()
    defer Shutdown(context.Background())
    
    // ... 应用逻辑
}
```

---

## Scope 注册表

### 1. 全局注册表

```go
package instrumentation

import (
    "sync"
    "go.opentelemetry.io/otel/trace"
)

// ScopeRegistry 全局 Scope 注册表
type ScopeRegistry struct {
    mu      sync.RWMutex
    tracers map[string]trace.Tracer
    meters  map[string]metric.Meter
}

var globalRegistry = &ScopeRegistry{
    tracers: make(map[string]trace.Tracer),
    meters:  make(map[string]metric.Meter),
}

// RegisterTracer 注册 Tracer
func RegisterTracer(name string, tracer trace.Tracer) {
    globalRegistry.mu.Lock()
    defer globalRegistry.mu.Unlock()
    globalRegistry.tracers[name] = tracer
}

// GetTracer 获取 Tracer
func GetTracer(name string) (trace.Tracer, bool) {
    globalRegistry.mu.RLock()
    defer globalRegistry.mu.RUnlock()
    tracer, ok := globalRegistry.tracers[name]
    return tracer, ok
}

// ListTracers 列出所有 Tracer
func ListTracers() []string {
    globalRegistry.mu.RLock()
    defer globalRegistry.mu.RUnlock()
    
    names := make([]string, 0, len(globalRegistry.tracers))
    for name := range globalRegistry.tracers {
        names = append(names, name)
    }
    return names
}

// 使用示例
func main() {
    // 注册 Tracer
    apiTracer := otel.GetTracerProvider().Tracer("myapp/api", ...)
    RegisterTracer("api", apiTracer)
    
    // 获取 Tracer
    if tracer, ok := GetTracer("api"); ok {
        ctx, span := tracer.Start(context.Background(), "operation")
        defer span.End()
    }
}
```

### 2. 作用域注册表

```go
package instrumentation

// ScopedRegistry 作用域注册表
type ScopedRegistry struct {
    parent *ScopedRegistry
    scopes map[string]trace.Tracer
    mu     sync.RWMutex
}

// NewScopedRegistry 创建作用域注册表
func NewScopedRegistry(parent *ScopedRegistry) *ScopedRegistry {
    return &ScopedRegistry{
        parent: parent,
        scopes: make(map[string]trace.Tracer),
    }
}

// Register 注册 Scope
func (r *ScopedRegistry) Register(name string, tracer trace.Tracer) {
    r.mu.Lock()
    defer r.mu.Unlock()
    r.scopes[name] = tracer
}

// Get 获取 Scope (支持继承)
func (r *ScopedRegistry) Get(name string) (trace.Tracer, bool) {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    // 先查找当前作用域
    if tracer, ok := r.scopes[name]; ok {
        return tracer, true
    }
    
    // 查找父作用域
    if r.parent != nil {
        return r.parent.Get(name)
    }
    
    return nil, false
}

// 使用示例
func main() {
    // 全局注册表
    globalReg := NewScopedRegistry(nil)
    globalReg.Register("app", appTracer)
    
    // 模块注册表 (继承全局)
    moduleReg := NewScopedRegistry(globalReg)
    moduleReg.Register("api", apiTracer)
    
    // 可以获取 "api" (当前作用域)
    apiTracer, _ := moduleReg.Get("api")
    
    // 也可以获取 "app" (父作用域)
    appTracer, _ := moduleReg.Get("app")
}
```

---

## Go 1.25.1 实现

### 1. Scope Manager

```go
package instrumentation

import (
    "sync"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// ScopeManager 管理多个 Scope
type ScopeManager struct {
    tracers map[string]trace.Tracer
    meters  map[string]metric.Meter
    mu      sync.RWMutex
}

// NewScopeManager 创建管理器
func NewScopeManager() *ScopeManager {
    return &ScopeManager{
        tracers: make(map[string]trace.Tracer),
        meters:  make(map[string]metric.Meter),
    }
}

// GetOrCreateTracer 获取或创建 Tracer
func (m *ScopeManager) GetOrCreateTracer(name, version string) trace.Tracer {
    key := name + "@" + version
    
    m.mu.RLock()
    if tracer, ok := m.tracers[key]; ok {
        m.mu.RUnlock()
        return tracer
    }
    m.mu.RUnlock()
    
    m.mu.Lock()
    defer m.mu.Unlock()
    
    // 双重检查
    if tracer, ok := m.tracers[key]; ok {
        return tracer
    }
    
    // 创建新 Tracer
    tracer := otel.GetTracerProvider().Tracer(
        name,
        trace.WithInstrumentationVersion(version),
    )
    m.tracers[key] = tracer
    return tracer
}

// GetOrCreateMeter 获取或创建 Meter
func (m *ScopeManager) GetOrCreateMeter(name, version string) metric.Meter {
    key := name + "@" + version
    
    m.mu.RLock()
    if meter, ok := m.meters[key]; ok {
        m.mu.RUnlock()
        return meter
    }
    m.mu.RUnlock()
    
    m.mu.Lock()
    defer m.mu.Unlock()
    
    if meter, ok := m.meters[key]; ok {
        return meter
    }
    
    meter := otel.GetMeterProvider().Meter(
        name,
        metric.WithInstrumentationVersion(version),
    )
    m.meters[key] = meter
    return meter
}

// 使用示例
var manager = NewScopeManager()

func GetAPITracer() trace.Tracer {
    return manager.GetOrCreateTracer("myapp/api", "1.0.0")
}
```

### 2. Scope Registry

```go
package instrumentation

// Registry 完整的注册表实现
type Registry struct {
    mu    sync.RWMutex
    items map[string]interface{}
}

func NewRegistry() *Registry {
    return &Registry{
        items: make(map[string]interface{}),
    }
}

func (r *Registry) Set(key string, value interface{}) {
    r.mu.Lock()
    defer r.mu.Unlock()
    r.items[key] = value
}

func (r *Registry) Get(key string) (interface{}, bool) {
    r.mu.RLock()
    defer r.mu.RUnlock()
    val, ok := r.items[key]
    return val, ok
}

func (r *Registry) Delete(key string) {
    r.mu.Lock()
    defer r.mu.Unlock()
    delete(r.items, key)
}

func (r *Registry) Keys() []string {
    r.mu.RLock()
    defer r.mu.RUnlock()
    
    keys := make([]string, 0, len(r.items))
    for k := range r.items {
        keys = append(keys, k)
    }
    return keys
}
```

### 3. Scope Provider

```go
package instrumentation

// Provider 提供统一的 Scope 访问接口
type Provider struct {
    manager *ScopeManager
}

func NewProvider() *Provider {
    return &Provider{
        manager: NewScopeManager(),
    }
}

func (p *Provider) Tracer(name string, opts ...trace.TracerOption) trace.Tracer {
    version := ""
    for _, opt := range opts {
        if vo, ok := opt.(interface{ Version() string }); ok {
            version = vo.Version()
        }
    }
    return p.manager.GetOrCreateTracer(name, version)
}

func (p *Provider) Meter(name string, opts ...metric.MeterOption) metric.Meter {
    version := ""
    for _, opt := range opts {
        if vo, ok := opt.(interface{ Version() string }); ok {
            version = vo.Version()
        }
    }
    return p.manager.GetOrCreateMeter(name, version)
}
```

---

## 多 Scope 管理

### 1. Scope 层次结构

```go
// 应用层次结构
app/
├── api/          (Scope: myapp/api)
│   ├── handlers/ (使用 myapp/api Scope)
│   └── middleware/ (使用 myapp/api Scope)
├── database/     (Scope: myapp/database)
│   ├── postgresql/ (使用 myapp/database Scope)
│   └── redis/     (使用 myapp/database Scope)
└── metrics/      (Scope: myapp/metrics)

// 实现
var (
    apiTracer = otel.GetTracerProvider().Tracer("myapp/api", ...)
    dbTracer  = otel.GetTracerProvider().Tracer("myapp/database", ...)
)
```

### 2. Scope 过滤

```go
package instrumentation

// FilterScopes 过滤 Scope
func FilterScopes(scopes []string, predicate func(string) bool) []string {
    filtered := make([]string, 0)
    for _, scope := range scopes {
        if predicate(scope) {
            filtered = append(filtered, scope)
        }
    }
    return filtered
}

// 使用示例
func main() {
    allScopes := ListTracers()
    
    // 只保留 API 相关的 Scope
    apiScopes := FilterScopes(allScopes, func(name string) bool {
        return strings.HasPrefix(name, "myapp/api")
    })
    
    log.Printf("API Scopes: %v", apiScopes)
}
```

### 3. Scope 聚合

```go
// 按模块聚合 Span
func AggregateByScope(spans []trace.Span) map[string][]trace.Span {
    result := make(map[string][]trace.Span)
    
    for _, span := range spans {
        scopeName := span.InstrumentationScope().Name
        result[scopeName] = append(result[scopeName], span)
    }
    
    return result
}
```

---

## 最佳实践

```go
// ✅ 正确：在应用启动时创建并缓存 Scope
var tracer trace.Tracer

func init() {
    tracer = otel.GetTracerProvider().Tracer("myapp", ...)
}

// ✅ 正确：使用 ScopeManager 管理多个 Scope
var manager = NewScopeManager()

func GetTracer(name string) trace.Tracer {
    return manager.GetOrCreateTracer(name, "1.0.0")
}

// ❌ 错误：每次使用时创建新 Scope
func BadExample(ctx context.Context) {
    tracer := otel.GetTracerProvider().Tracer("myapp", ...) // 不要这样做
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
}

// ✅ 正确：为不同模块使用不同 Scope
var (
    apiTracer = otel.GetTracerProvider().Tracer("myapp/api", ...)
    dbTracer  = otel.GetTracerProvider().Tracer("myapp/database", ...)
)

// ❌ 错误：所有模块共用一个 Scope
var sharedTracer = otel.GetTracerProvider().Tracer("myapp", ...) // 粒度太粗
```

---

## 参考资源

- [OpenTelemetry Instrumentation Spec](https://opentelemetry.io/docs/specs/otel/overview/)
- [Go SDK Tracer API](https://pkg.go.dev/go.opentelemetry.io/otel/trace)
- [01_Scope定义.md](./01_Scope定义.md)
- [03_形式化定义.md](./03_形式化定义.md)

---

**🎉 恭喜！你已经掌握了 Scope 的完整管理！**

现在你可以：
- ✅ 创建和配置 Scope
- ✅ 获取和复用 Scope
- ✅ 管理 Scope 的生命周期
- ✅ 实现 Scope 注册表


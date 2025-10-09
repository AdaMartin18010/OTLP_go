# InstrumentationScope 定义

## 📋 目录

- [InstrumentationScope 定义](#instrumentationscope-定义)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 InstrumentationScope](#什么是-instrumentationscope)
    - [为什么需要 InstrumentationScope](#为什么需要-instrumentationscope)
  - [InstrumentationScope 数据结构](#instrumentationscope-数据结构)
    - [1. 完整定义](#1-完整定义)
    - [2. Protocol Buffers 定义](#2-protocol-buffers-定义)
    - [3. Go 结构体定义](#3-go-结构体定义)
  - [核心字段](#核心字段)
    - [1. Name (必需)](#1-name-必需)
    - [2. Version (可选)](#2-version-可选)
    - [3. Attributes (可选)](#3-attributes-可选)
    - [4. DroppedAttributesCount](#4-droppedattributescount)
  - [Scope 标识](#scope-标识)
    - [1. 唯一性标识](#1-唯一性标识)
    - [2. 标识符组合](#2-标识符组合)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本实现](#1-基本实现)
    - [2. Scope 比较](#2-scope-比较)
    - [3. 预定义 Scope](#3-预定义-scope)
  - [Scope 使用场景](#scope-使用场景)
    - [1. 库级别追踪](#1-库级别追踪)
    - [2. 模块级别度量](#2-模块级别度量)
    - [3. 组件级别日志](#3-组件级别日志)
  - [最佳实践](#最佳实践)
    - [1. 命名约定](#1-命名约定)
    - [2. 版本管理](#2-版本管理)
    - [3. 属性使用](#3-属性使用)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 InstrumentationScope

**InstrumentationScope** 是 OpenTelemetry 中用于标识遥测数据产生者的逻辑单元。它表示一个库、模块或组件的仪表化范围。

```text
InstrumentationScope = {
  name: "github.com/myapp/database",
  version: "1.2.3",
  attributes: {
    "db.system": "postgresql"
  }
}
```

### 为什么需要 InstrumentationScope

```text
问题：
❌ 无法区分不同库/模块的遥测数据
❌ 难以定位问题源头
❌ 版本升级影响无法追踪

InstrumentationScope 解决方案：
✅ 标识遥测数据的具体来源（库/模块）
✅ 支持版本级别的数据分析
✅ 便于过滤和聚合特定组件的数据
✅ 支持细粒度的采样和配置
```

---

## InstrumentationScope 数据结构

### 1. 完整定义

InstrumentationScope 由三个核心字段组成：

```text
InstrumentationScope {
  Name:    string          (必需)
  Version: string          (可选)
  Attributes: map[string]Value (可选)
  DroppedAttributesCount: uint32
}

典型示例:
name: "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
version: "0.46.0"
attributes: {
  "http.flavor": "1.1"
}
```

### 2. Protocol Buffers 定义

```protobuf
message InstrumentationScope {
  // 仪表化库的名称（必需）
  string name = 1;
  
  // 仪表化库的版本（可选）
  string version = 2;
  
  // 附加属性（可选）
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 3;
  
  // 被丢弃的属性数量
  uint32 dropped_attributes_count = 4;
}
```

### 3. Go 结构体定义

```go
package instrumentation

import (
    "go.opentelemetry.io/otel/attribute"
)

// Scope represents an instrumentation scope
type Scope struct {
    Name                   string
    Version                string
    Attributes             []attribute.KeyValue
    DroppedAttributesCount uint32
}

// NewScope creates a new instrumentation scope
func NewScope(name, version string, attrs ...attribute.KeyValue) Scope {
    return Scope{
        Name:       name,
        Version:    version,
        Attributes: attrs,
    }
}

// Equal checks if two scopes are equal
func (s Scope) Equal(other Scope) bool {
    return s.Name == other.Name && s.Version == other.Version
}
```

---

## 核心字段

### 1. Name (必需)

**名称字段** - 唯一标识仪表化库或模块

```go
// 推荐格式: 使用 Go import path
name := "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

// 其他语言:
// Java:   "io.opentelemetry.instrumentation.spring.webmvc"
// Python: "opentelemetry.instrumentation.requests"
// .NET:   "OpenTelemetry.Instrumentation.AspNetCore"
```

**命名约定**:

- 使用包的完整导入路径
- 反映代码组织结构
- 全局唯一
- 小写，使用点号分隔

### 2. Version (可选)

**版本字段** - 标识仪表化库的版本

```go
// 推荐: 语义化版本
version := "1.2.3"       // MAJOR.MINOR.PATCH
version := "0.46.0"      // 0.x.y for pre-release
version := "2.1.0-beta"  // 带预发布标识

// 不推荐:
version := "v1.2.3"      // ❌ 不要前缀 "v"
version := "1.2"         // ❌ 不完整
version := "latest"      // ❌ 非具体版本
```

### 3. Attributes (可选)

**属性字段** - 提供关于 Scope 的额外元数据

```go
// 库特定的元数据
attrs := []attribute.KeyValue{
    attribute.String("instrumentation.library.owner", "platform-team"),
    attribute.String("instrumentation.library.language", "go"),
    attribute.Bool("instrumentation.library.experimental", false),
}

scope := NewScope("myapp/database", "1.0.0", attrs...)
```

**常用属性**:

```text
instrumentation.library.owner      - 库的维护团队
instrumentation.library.language   - 编程语言
instrumentation.library.framework  - 框架名称
instrumentation.library.experimental - 是否实验性
```

### 4. DroppedAttributesCount

**丢弃计数** - 记录被丢弃的属性数量

```go
// 当属性超过限制时，记录丢弃的数量
if len(attrs) > MaxAttributes {
    scope.Attributes = attrs[:MaxAttributes]
    scope.DroppedAttributesCount = uint32(len(attrs) - MaxAttributes)
}
```

---

## Scope 标识

### 1. 唯一性标识

InstrumentationScope 通过 Name 和 Version 的组合唯一标识：

```text
最小标识:
✅ name (必需)

完整标识:
✅ name + version

示例:
"go.opentelemetry.io/otel/sdk/trace" + "1.19.0"
```

**Go 实现**:

```go
// UniqueID 生成 Scope 的唯一标识
func (s Scope) UniqueID() string {
    if s.Version == "" {
        return s.Name
    }
    return s.Name + "@" + s.Version
}

// 示例:
// "myapp/database"
// "myapp/database@1.0.0"
```

### 2. 标识符组合

不同场景下的标识符：

```go
// 1. 库级别
scope := NewScope("go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp", "0.46.0")
// ID: "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp@0.46.0"

// 2. 应用模块
scope := NewScope("myapp/api", "1.0.0")
// ID: "myapp/api@1.0.0"

// 3. 框架组件
scope := NewScope("github.com/gin-gonic/gin", "1.9.1")
// ID: "github.com/gin-gonic/gin@1.9.1"

// 4. 内部组件（无版本）
scope := NewScope("myapp/internal/cache", "")
// ID: "myapp/internal/cache"
```

---

## Go 1.25.1 实现

### 1. 基本实现

```go
package instrumentation

import (
    "go.opentelemetry.io/otel/attribute"
)

// Scope represents an instrumentation scope
type Scope struct {
    Name                   string
    Version                string
    Attributes             []attribute.KeyValue
    DroppedAttributesCount uint32
}

// NewScope creates a new instrumentation scope
func NewScope(name, version string, attrs ...attribute.KeyValue) Scope {
    return Scope{
        Name:       name,
        Version:    version,
        Attributes: attrs,
    }
}

// String returns string representation
func (s Scope) String() string {
    if s.Version == "" {
        return s.Name
    }
    return s.Name + "@" + s.Version
}

// IsValid checks if the scope is valid
func (s Scope) IsValid() bool {
    return s.Name != ""
}

// 使用示例
func main() {
    // 创建 Scope
    scope := NewScope(
        "myapp/database",
        "1.0.0",
        attribute.String("db.system", "postgresql"),
    )
    
    log.Printf("Scope: %s", scope)
    log.Printf("Valid: %v", scope.IsValid())
}
```

### 2. Scope 比较

```go
// Equal checks if two scopes are equal
func (s Scope) Equal(other Scope) bool {
    // 名称和版本必须相同
    if s.Name != other.Name || s.Version != other.Version {
        return false
    }
    
    // 属性比较（可选）
    if len(s.Attributes) != len(other.Attributes) {
        return false
    }
    
    // 简化的属性比较
    for i, attr := range s.Attributes {
        if attr != other.Attributes[i] {
            return false
        }
    }
    
    return true
}

// Matches checks if scope matches the given name
func (s Scope) Matches(name string) bool {
    return s.Name == name
}

// MatchesPrefix checks if scope name starts with prefix
func (s Scope) MatchesPrefix(prefix string) bool {
    return strings.HasPrefix(s.Name, prefix)
}

// 使用示例
func main() {
    scope1 := NewScope("myapp/api", "1.0.0")
    scope2 := NewScope("myapp/api", "1.0.0")
    scope3 := NewScope("myapp/api", "2.0.0")
    
    log.Printf("scope1 == scope2: %v", scope1.Equal(scope2)) // true
    log.Printf("scope1 == scope3: %v", scope1.Equal(scope3)) // false
    
    log.Printf("Matches 'myapp/api': %v", scope1.Matches("myapp/api")) // true
    log.Printf("Matches prefix 'myapp/': %v", scope1.MatchesPrefix("myapp/")) // true
}
```

### 3. 预定义 Scope

```go
package instrumentation

import (
    "runtime"
)

// 预定义的常用 Scope
var (
    // SDKScope 是 OpenTelemetry SDK 的 Scope
    SDKScope = NewScope(
        "go.opentelemetry.io/otel/sdk",
        "1.19.0",
    )
    
    // HTTPScope 是 HTTP 仪表化的 Scope
    HTTPScope = NewScope(
        "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp",
        "0.46.0",
    )
    
    // GRPCScope 是 gRPC 仪表化的 Scope
    GRPCScope = NewScope(
        "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc",
        "0.46.0",
    )
    
    // DatabaseScope 是数据库仪表化的 Scope
    DatabaseScope = NewScope(
        "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql",
        "0.46.0",
    )
)

// NewAppScope 创建应用级别的 Scope
func NewAppScope(moduleName, version string) Scope {
    return NewScope(
        moduleName,
        version,
        attribute.String("language", "go"),
        attribute.String("runtime.version", runtime.Version()),
    )
}

// 使用示例
func main() {
    // 使用预定义 Scope
    httpTracer := tracer.WithInstrumentationScope(HTTPScope)
    
    // 创建自定义应用 Scope
    appScope := NewAppScope("myapp/api", "1.0.0")
    appTracer := tracer.WithInstrumentationScope(appScope)
}
```

---

## Scope 使用场景

### 1. 库级别追踪

```go
package mylib

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

var (
    // 库的 Scope
    libraryScope = instrumentation.NewScope(
        "github.com/myorg/mylib",
        "1.0.0",
    )
    
    // 使用 Scope 创建 Tracer
    tracer = otel.GetTracerProvider().Tracer(
        libraryScope.Name,
        trace.WithInstrumentationVersion(libraryScope.Version),
    )
)

func DoSomething(ctx context.Context) error {
    // 创建的 Span 会关联到 libraryScope
    ctx, span := tracer.Start(ctx, "DoSomething")
    defer span.End()
    
    // ... 业务逻辑
    return nil
}
```

### 2. 模块级别度量

```go
package metrics

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

var (
    // API 模块的 Scope
    apiScope = instrumentation.NewScope(
        "myapp/api",
        "1.0.0",
        attribute.String("module", "api"),
    )
    
    // 使用 Scope 创建 Meter
    meter = otel.GetMeterProvider().Meter(
        apiScope.Name,
        metric.WithInstrumentationVersion(apiScope.Version),
    )
    
    // 创建指标
    requestCounter, _ = meter.Int64Counter("api.requests")
)

func RecordRequest() {
    // 记录的指标会关联到 apiScope
    requestCounter.Add(context.Background(), 1)
}
```

### 3. 组件级别日志

```go
package logger

import (
    "log/slog"
    "go.opentelemetry.io/otel/log"
)

var (
    // 数据库组件的 Scope
    dbScope = instrumentation.NewScope(
        "myapp/database",
        "1.0.0",
        attribute.String("component", "postgresql"),
    )
    
    // 使用 Scope 创建 Logger
    logger = otel.GetLoggerProvider().Logger(
        dbScope.Name,
        log.WithInstrumentationVersion(dbScope.Version),
    )
)

func LogQuery(query string) {
    // 记录的日志会关联到 dbScope
    logger.Info("Executing query", "query", query)
}
```

---

## 最佳实践

### 1. 命名约定

```go
// ✅ 正确：使用完整的导入路径
scope := NewScope("go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp", "0.46.0")
scope := NewScope("github.com/myorg/myapp/api", "1.0.0")
scope := NewScope("myapp/database/postgresql", "1.0.0")

// ❌ 错误：不规范的命名
scope := NewScope("HTTP", "1.0.0")                    // 太笼统
scope := NewScope("my-app", "1.0.0")                  // 使用连字符
scope := NewScope("MyApp", "1.0.0")                   // 大写开头
scope := NewScope("app/api/v1", "1.0.0")              // 路径包含版本
```

### 2. 版本管理

```go
// ✅ 正确：使用语义化版本
scope := NewScope("myapp/api", "1.2.3")               // 稳定版本
scope := NewScope("myapp/api", "0.1.0")               // 预发布版本
scope := NewScope("myapp/api", "2.0.0-beta.1")        // 带标识

// ❌ 错误：不规范的版本
scope := NewScope("myapp/api", "v1.2.3")              // 不要 "v" 前缀
scope := NewScope("myapp/api", "1.2")                 // 不完整
scope := NewScope("myapp/api", "latest")              // 非具体版本
scope := NewScope("myapp/api", "master")              // 分支名
```

### 3. 属性使用

```go
// ✅ 正确：有意义的属性
scope := NewScope("myapp/api", "1.0.0",
    attribute.String("team", "platform"),
    attribute.String("environment", "production"),
)

// ✅ 正确：库特定元数据
scope := NewScope("github.com/gin-gonic/gin", "1.9.1",
    attribute.String("framework", "gin"),
    attribute.String("language", "go"),
)

// ❌ 错误：冗余属性
scope := NewScope("myapp/api", "1.0.0",
    attribute.String("name", "myapp/api"),          // 冗余，已在 Name 字段
    attribute.String("version", "1.0.0"),           // 冗余，已在 Version 字段
)

// ❌ 错误：过多属性
scope := NewScope("myapp/api", "1.0.0",
    // ... 50+ 个属性                               // 过多
)
```

---

## 常见问题

**Q1: InstrumentationScope 和 Resource 的区别？**

```text
Resource:
- 描述遥测数据的"来源" (服务、主机、进程)
- 全局属性，适用于所有遥测数据
- 示例: service.name, host.name, cloud.provider

InstrumentationScope:
- 描述遥测数据的"产生者" (库、模块、组件)
- 局部属性，仅适用于特定库/模块的数据
- 示例: 库名称、库版本

关系:
Resource (全局) → InstrumentationScope (局部) → 遥测数据
```

**Q2: 何时应该创建新的 Scope？**

```text
应该创建新 Scope:
✅ 为每个独立的库创建 Scope
✅ 为应用的不同模块创建 Scope
✅ 为可重用组件创建 Scope

不应该创建新 Scope:
❌ 为每个函数创建 Scope
❌ 为每个类创建 Scope
❌ 动态创建 Scope (运行时)

粒度建议:
- 库级别: github.com/myorg/mylib
- 模块级别: myapp/api, myapp/database
- 组件级别: myapp/cache/redis
```

**Q3: Scope 的 Version 字段是否必需？**

```text
Version 字段是可选的，但强烈推荐：

必需场景:
✅ 可重用库 (需要追踪版本变化)
✅ 共享组件 (需要版本兼容性)
✅ 第三方集成 (需要版本信息)

可选场景:
⚠️  应用内部模块 (版本与应用同步)
⚠️  简单工具类 (很少变更)

不使用的影响:
- 无法区分不同版本的行为差异
- 升级后问题难以追踪
- 不利于版本级别的数据分析
```

---

## 参考资源

- [OpenTelemetry InstrumentationScope Spec](https://opentelemetry.io/docs/specs/otel/glossary/#instrumentation-scope)
- [Go SDK Instrumentation Package](https://pkg.go.dev/go.opentelemetry.io/otel/sdk/instrumentation)
- [02_Scope管理.md](./02_Scope管理.md)
- [03_形式化定义.md](./03_形式化定义.md)

---

**🎉 恭喜！你已经掌握了 InstrumentationScope 的完整定义！**

现在你可以：

- ✅ 理解 InstrumentationScope 的作用和结构
- ✅ 使用核心字段标识仪表化库/模块
- ✅ 实现 Scope 创建和比较
- ✅ 遵循命名和版本管理最佳实践

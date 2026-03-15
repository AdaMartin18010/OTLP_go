# 79. Beego 框架与 OTLP 完整集成（2025版）

> **Beego 版本**: v2.3.3  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [79. Beego 框架与 OTLP 完整集成（2025版）](#79-beego-框架与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Beego 框架概述](#1-beego-框架概述)
    - [1.1 为什么选择 Beego](#11-为什么选择-beego)
    - [1.2 核心特性](#12-核心特性)
    - [1.3 与其他框架对比](#13-与其他框架对比)
  - [2. 快速开始](#2-快速开始)
    - [2.1 环境准备](#21-环境准备)
    - [2.2 项目初始化](#22-项目初始化)
    - [2.3 基础集成](#23-基础集成)
  - [3. OTLP 完整集成](#3-otlp-完整集成)
    - [3.1 TracerProvider 配置](#31-tracerprovider-配置)
    - [3.2 Beego Filter 中间件](#32-beego-filter-中间件)
    - [3.3 Controller 追踪](#33-controller-追踪)
  - [4. ORM 集成与数据库追踪](#4-orm-集成与数据库追踪)
    - [4.1 Beego ORM 配置](#41-beego-orm-配置)
    - [4.2 自动数据库追踪](#42-自动数据库追踪)
    - [4.3 查询性能分析](#43-查询性能分析)
  - [5. 缓存追踪](#5-缓存追踪)
    - [5.1 Cache 模块集成](#51-cache-模块集成)
    - [5.2 Redis 缓存追踪](#52-redis-缓存追踪)
    - [5.3 Memcache 追踪](#53-memcache-追踪)
  - [6. Task 任务调度追踪](#6-task-任务调度追踪)
    - [6.1 Cron 任务追踪](#61-cron-任务追踪)
    - [6.2 异步任务追踪](#62-异步任务追踪)
  - [7. Session 追踪](#7-session-追踪)
    - [7.1 Session 中间件](#71-session-中间件)
    - [7.2 Session 存储追踪](#72-session-存储追踪)
  - [8. 完整微服务示例](#8-完整微服务示例)
    - [8.1 用户服务](#81-用户服务)
    - [8.2 API 文档集成](#82-api-文档集成)
    - [8.3 配置管理](#83-配置管理)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 项目结构](#91-项目结构)
    - [9.2 错误处理](#92-错误处理)
    - [9.3 性能优化](#93-性能优化)
  - [10. 生产部署](#10-生产部署)
    - [10.1 Docker 容器化](#101-docker-容器化)
    - [10.2 监控告警](#102-监控告警)
    - [10.3 日志集成](#103-日志集成)
  - [11. 总结](#11-总结)
    - [11.1 核心优势](#111-核心优势)
    - [11.2 适用场景](#112-适用场景)
    - [11.3 相关资源](#113-相关资源)

---

## 1. Beego 框架概述

### 1.1 为什么选择 Beego

**Beego** 是中国开发者 astaxie 创建的成熟 Go Web 框架，在国内拥有庞大用户基础。

```text
✅ MVC 架构         - 完整的 Model-View-Controller 设计
✅ 功能完整         - ORM、Cache、Session、Task 等内置
✅ 企业级           - 已被多家大型企业采用
✅ 自动化工具       - bee 工具一键生成项目
✅ 中文文档         - 完善的中文文档和社区
✅ RESTful API     - 原生支持 RESTful 设计
✅ 热更新           - 开发模式下自动热更新
```

### 1.2 核心特性

```go
// Beego 核心组件
type BeegoFramework struct {
    // Web 框架
    App        *beego.App         // 应用实例
    Router     *beego.ControllerRegister  // 路由器
    
    // 数据层
    ORM        orm.Ormer          // ORM 实例
    Cache      cache.Cache        // 缓存
    Session    session.Provider   // Session
    
    // 任务调度
    Task       *toolbox.Task      // 定时任务
    
    // 配置
    Config     config.Configer    // 配置管理
    
    // 可观测性
    Tracing    trace.TracerProvider
    Metrics    metric.MeterProvider
    Logger     logs.BeeLogger
}
```

**特性列表**：

| 特性 | 描述 | 支持度 |
|------|------|--------|
| **MVC 架构** | Model-View-Controller 完整实现 | ⭐⭐⭐⭐⭐ |
| **ORM** | 支持 MySQL、PostgreSQL、SQLite 等 | ⭐⭐⭐⭐⭐ |
| **Cache** | 内存、文件、Redis、Memcache | ⭐⭐⭐⭐⭐ |
| **Session** | 多种存储后端支持 | ⭐⭐⭐⭐⭐ |
| **表单验证** | 强大的表单验证器 | ⭐⭐⭐⭐ |
| **国际化** | i18n 支持 | ⭐⭐⭐⭐ |
| **Swagger** | 自动生成 API 文档 | ⭐⭐⭐⭐⭐ |
| **任务调度** | Cron 定时任务 | ⭐⭐⭐⭐ |

### 1.3 与其他框架对比

```text
┌─────────────────────────────────────────────────────────┐
│              Beego vs Gin vs Echo vs Fiber              │
├───────────┬────────┬────────┬────────┬──────────────────┤
│   指标    │ Beego  │  Gin   │  Echo  │  对比结果        │
├───────────┼────────┼────────┼────────┼──────────────────┤
│  功能完整 │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐   │ ⭐⭐⭐⭐ │ Beego 最全       │
│  性能     │ ⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐⭐│ Beego 中等       │
│  学习曲线 │ ⭐⭐⭐   │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐⭐│ Beego 稍陡       │
│  社区活跃 │ ⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐ │ Gin 最活跃       │
│  企业应用 │ ⭐⭐⭐⭐⭐│ ⭐⭐⭐⭐ │ ⭐⭐⭐⭐ │ Beego 企业友好   │
└───────────┴────────┴────────┴────────┴──────────────────┘
```

**适用场景**：

- ✅ 企业级 Web 应用（管理后台、CMS）
- ✅ RESTful API 服务
- ✅ 需要完整功能的快速开发
- ❌ 超高性能场景（不如 Gin/Fiber）
- ❌ 极简主义项目（功能过于丰富）

---

## 2. 快速开始

### 2.1 环境准备

```bash
# 安装 Go 1.25.1
go version  # go version go1.25.1 linux/amd64

# 安装 Beego v2 和 bee 工具
go install github.com/beego/beego/v2@v2.3.3
go install github.com/beego/bee/v2@latest

# 安装 OpenTelemetry 依赖
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/trace@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.32.0
go get go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp@v0.58.0
```

### 2.2 项目初始化

```bash
# 使用 bee 工具创建项目
bee new myapp
cd myapp

# 项目结构
.
├── conf/
│   └── app.conf          # 配置文件
├── controllers/
│   └── default.go        # 控制器
├── models/               # 模型层
├── routers/
│   └── router.go         # 路由配置
├── static/               # 静态文件
├── views/                # 视图模板
├── tests/                # 测试
├── go.mod
└── main.go               # 入口文件
```

### 2.3 基础集成

**`go.mod`**:

```go
module myapp

go 1.25.1

require (
    github.com/beego/beego/v2 v2.3.3
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.32.0
    go.opentelemetry.io/otel/sdk v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp v0.58.0
)
```

---

## 3. OTLP 完整集成

### 3.1 TracerProvider 配置

**`pkg/telemetry/tracer.go`**:

```go
package telemetry

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.28.0"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

type TelemetryConfig struct {
    ServiceName      string
    ServiceVersion   string
    OTLPEndpoint     string
    SamplingRate     float64
    EnableCompression bool
}

// InitTracer 初始化全局 TracerProvider
func InitTracer(cfg TelemetryConfig) (*sdktrace.TracerProvider, error) {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()

    // 1. 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String(cfg.ServiceName),
            semconv.ServiceVersionKey.String(cfg.ServiceVersion),
            semconv.DeploymentEnvironmentKey.String("production"),
        ),
        resource.WithHost(),
        resource.WithProcess(),
        resource.WithOS(),
        resource.WithContainer(),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create resource: %w", err)
    }

    // 2. 创建 OTLP gRPC 导出器
    opts := []otlptracegrpc.Option{
        otlptracegrpc.WithEndpoint(cfg.OTLPEndpoint),
        otlptracegrpc.WithDialOption(grpc.WithTransportCredentials(insecure.NewCredentials())),
        otlptracegrpc.WithTimeout(10 * time.Second),
    }

    if cfg.EnableCompression {
        opts = append(opts, otlptracegrpc.WithCompressor("gzip"))
    }

    exporter, err := otlptracegrpc.New(ctx, opts...)
    if err != nil {
        return nil, fmt.Errorf("failed to create OTLP exporter: %w", err)
    }

    // 3. 创建采样器
    var sampler sdktrace.Sampler
    if cfg.SamplingRate >= 1.0 {
        sampler = sdktrace.AlwaysSample()
    } else {
        sampler = sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(cfg.SamplingRate),
        )
    }

    // 4. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSampler(sampler),
        sdktrace.WithResource(res),
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
            sdktrace.WithMaxQueueSize(2048),
        ),
    )

    // 5. 设置全局 TracerProvider 和 Propagator
    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )

    return tp, nil
}

// GetTracer 获取 Tracer 实例
func GetTracer(name string) trace.Tracer {
    return otel.Tracer(name,
        trace.WithInstrumentationVersion("1.0.0"),
        trace.WithSchemaURL(semconv.SchemaURL),
    )
}
```

### 3.2 Beego Filter 中间件

**`pkg/middleware/tracing.go`**:

```go
package middleware

import (
    "fmt"
    "time"

    "github.com/beego/beego/v2/server/web"
    "github.com/beego/beego/v2/server/web/context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    semconv "go.opentelemetry.io/otel/semconv/v1.28.0"
    "go.opentelemetry.io/otel/trace"
)

const (
    tracerName = "beego-tracer"
)

// TracingFilter Beego 追踪 Filter
func TracingFilter(ctx *context.Context) {
    tracer := otel.Tracer(tracerName)
    
    // 1. 从请求头提取 Trace Context
    propagator := otel.GetTextMapPropagator()
    spanCtx := propagator.Extract(ctx.Request.Context(), propagation.HeaderCarrier(ctx.Request.Header))
    
    // 2. 创建 Span
    spanName := fmt.Sprintf("%s %s", ctx.Request.Method, ctx.Request.URL.Path)
    spanCtx, span := tracer.Start(spanCtx, spanName,
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            semconv.HTTPMethodKey.String(ctx.Request.Method),
            semconv.HTTPURLKey.String(ctx.Request.URL.String()),
            semconv.HTTPTargetKey.String(ctx.Request.URL.Path),
            semconv.HTTPSchemeKey.String(ctx.Request.URL.Scheme),
            semconv.HTTPHostKey.String(ctx.Request.Host),
            semconv.HTTPUserAgentKey.String(ctx.Request.UserAgent()),
            semconv.HTTPClientIPKey.String(ctx.Request.RemoteAddr),
        ),
    )
    defer span.End()
    
    // 3. 将新的 Context 注入到请求中
    ctx.Request = ctx.Request.WithContext(spanCtx)
    
    // 4. 记录开始时间
    startTime := time.Now()
    
    // 5. 继续执行后续 Filter
    // Beego 的 Filter 不需要显式调用 next
    
    // 6. 记录响应信息
    duration := time.Since(startTime)
    statusCode := ctx.ResponseWriter.Status
    
    span.SetAttributes(
        semconv.HTTPStatusCodeKey.Int(statusCode),
        attribute.Int64("http.response.size", int64(ctx.ResponseWriter.Size)),
        attribute.Float64("http.duration_ms", float64(duration.Milliseconds())),
    )
    
    // 7. 记录错误状态
    if statusCode >= 400 {
        span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", statusCode))
        if statusCode >= 500 {
            span.RecordError(fmt.Errorf("server error: %d", statusCode))
        }
    } else {
        span.SetStatus(codes.Ok, "")
    }
}

// 注册 Filter
func RegisterFilters() {
    // 全局 Filter
    web.InsertFilter("*", web.BeforeRouter, TracingFilter)
}
```

### 3.3 Controller 追踪

**`controllers/user.go`**:

```go
package controllers

import (
    "context"
    "fmt"

    "github.com/beego/beego/v2/server/web"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// UserController 用户控制器
type UserController struct {
    web.Controller
}

// GetUser 获取用户信息
// @router /user/:id [get]
func (c *UserController) GetUser() {
    // 1. 获取上下文中的 Span
    ctx := c.Ctx.Request.Context()
    tracer := otel.Tracer("user-controller")
    
    // 2. 创建子 Span
    ctx, span := tracer.Start(ctx, "UserController.GetUser",
        trace.WithAttributes(
            attribute.String("controller", "UserController"),
            attribute.String("action", "GetUser"),
        ),
    )
    defer span.End()
    
    // 3. 获取路径参数
    userID := c.Ctx.Input.Param(":id")
    span.SetAttributes(attribute.String("user.id", userID))
    
    // 4. 调用 Service 层（传递 Context）
    user, err := c.getUserFromDB(ctx, userID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to get user")
        c.Ctx.Output.SetStatus(500)
        c.Data["json"] = map[string]string{"error": err.Error()}
        c.ServeJSON()
        return
    }
    
    span.SetStatus(codes.Ok, "")
    c.Data["json"] = user
    c.ServeJSON()
}

// getUserFromDB 从数据库获取用户（示例）
func (c *UserController) getUserFromDB(ctx context.Context, userID string) (map[string]interface{}, error) {
    tracer := otel.Tracer("user-service")
    ctx, span := tracer.Start(ctx, "getUserFromDB",
        trace.WithAttributes(
            attribute.String("db.operation", "SELECT"),
            attribute.String("db.table", "users"),
        ),
    )
    defer span.End()
    
    // 模拟数据库查询
    user := map[string]interface{}{
        "id":    userID,
        "name":  "Alice",
        "email": "alice@example.com",
    }
    
    span.SetStatus(codes.Ok, "")
    return user, nil
}

// CreateUser 创建用户
// @router /user [post]
func (c *UserController) CreateUser() {
    ctx := c.Ctx.Request.Context()
    tracer := otel.Tracer("user-controller")
    
    ctx, span := tracer.Start(ctx, "UserController.CreateUser",
        trace.WithAttributes(
            attribute.String("controller", "UserController"),
            attribute.String("action", "CreateUser"),
        ),
    )
    defer span.End()
    
    // 解析请求体
    var user struct {
        Name  string `json:"name"`
        Email string `json:"email"`
    }
    
    if err := c.Ctx.BindJSON(&user); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "invalid request body")
        c.Ctx.Output.SetStatus(400)
        c.Data["json"] = map[string]string{"error": "invalid request"}
        c.ServeJSON()
        return
    }
    
    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )
    
    // 调用创建逻辑
    // ...
    
    span.SetStatus(codes.Ok, "")
    c.Data["json"] = map[string]string{"status": "created"}
    c.ServeJSON()
}
```

---

## 4. ORM 集成与数据库追踪

### 4.1 Beego ORM 配置

**`models/init.go`**:

```go
package models

import (
    "fmt"

    "github.com/beego/beego/v2/client/orm"
    _ "github.com/go-sql-driver/mysql"
)

func init() {
    // 注册数据库驱动
    orm.RegisterDriver("mysql", orm.DRMySQL)
    
    // 注册数据源
    err := orm.RegisterDataBase("default", "mysql",
        "root:password@tcp(127.0.0.1:3306)/myapp?charset=utf8mb4&parseTime=True&loc=Local")
    if err != nil {
        panic(err)
    }
    
    // 注册模型
    orm.RegisterModel(new(User))
    
    // 开发模式：打印 SQL 语句
    orm.Debug = true
}

// User 用户模型
type User struct {
    ID        int64  `orm:"auto;pk"`
    Name      string `orm:"size(100)"`
    Email     string `orm:"unique;size(255)"`
    CreatedAt int64  `orm:"auto_now_add;type(bigint)"`
    UpdatedAt int64  `orm:"auto_now;type(bigint)"`
}

func (u *User) TableName() string {
    return "users"
}
```

### 4.2 自动数据库追踪

**`pkg/db/traced_orm.go`**:

```go
package db

import (
    "context"
    "database/sql"
    "fmt"
    "time"

    "github.com/beego/beego/v2/client/orm"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.28.0"
    "go.opentelemetry.io/otel/trace"
)

// TracedOrmer 带追踪的 ORM 包装器
type TracedOrmer struct {
    orm.Ormer
    tracer trace.Tracer
}

// NewTracedOrm 创建带追踪的 ORM
func NewTracedOrm() orm.Ormer {
    return &TracedOrmer{
        Ormer:  orm.NewOrm(),
        tracer: otel.Tracer("beego-orm"),
    }
}

// Read 带追踪的读取
func (t *TracedOrmer) ReadWithContext(ctx context.Context, md interface{}, cols ...string) error {
    ctx, span := t.tracer.Start(ctx, "orm.Read",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemKey.String("mysql"),
            semconv.DBOperationKey.String("SELECT"),
            attribute.String("db.method", "Read"),
        ),
    )
    defer span.End()
    
    startTime := time.Now()
    err := t.Ormer.ReadWithCtx(ctx, md, cols...)
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Float64("db.duration_ms", float64(duration.Milliseconds())),
    )
    
    if err != nil && err != orm.ErrNoRows {
        span.RecordError(err)
        span.SetStatus(codes.Error, "read failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return err
}

// Insert 带追踪的插入
func (t *TracedOrmer) InsertWithContext(ctx context.Context, md interface{}) (int64, error) {
    ctx, span := t.tracer.Start(ctx, "orm.Insert",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemKey.String("mysql"),
            semconv.DBOperationKey.String("INSERT"),
            attribute.String("db.method", "Insert"),
        ),
    )
    defer span.End()
    
    startTime := time.Now()
    id, err := t.Ormer.InsertWithCtx(ctx, md)
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Int64("db.inserted_id", id),
        attribute.Float64("db.duration_ms", float64(duration.Milliseconds())),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "insert failed")
        return 0, err
    }
    
    span.SetStatus(codes.Ok, "")
    return id, nil
}

// Update 带追踪的更新
func (t *TracedOrmer) UpdateWithContext(ctx context.Context, md interface{}, cols ...string) (int64, error) {
    ctx, span := t.tracer.Start(ctx, "orm.Update",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemKey.String("mysql"),
            semconv.DBOperationKey.String("UPDATE"),
            attribute.String("db.method", "Update"),
        ),
    )
    defer span.End()
    
    startTime := time.Now()
    num, err := t.Ormer.UpdateWithCtx(ctx, md, cols...)
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Int64("db.affected_rows", num),
        attribute.Float64("db.duration_ms", float64(duration.Milliseconds())),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "update failed")
        return 0, err
    }
    
    span.SetStatus(codes.Ok, "")
    return num, nil
}

// QueryTable 带追踪的查询构建器
func (t *TracedOrmer) QueryTableWithContext(ctx context.Context, ptrStructOrTableName interface{}) orm.QuerySeter {
    // 返回带追踪的 QuerySeter
    return &TracedQuerySeter{
        QuerySeter: t.Ormer.QueryTable(ptrStructOrTableName),
        tracer:     t.tracer,
        ctx:        ctx,
    }
}

// TracedQuerySeter 带追踪的查询构建器
type TracedQuerySeter struct {
    orm.QuerySeter
    tracer trace.Tracer
    ctx    context.Context
}

// All 带追踪的查询所有
func (t *TracedQuerySeter) All(container interface{}, cols ...string) (int64, error) {
    ctx, span := t.tracer.Start(t.ctx, "querySeter.All",
        trace.WithAttributes(
            semconv.DBSystemKey.String("mysql"),
            semconv.DBOperationKey.String("SELECT"),
            attribute.String("db.method", "All"),
        ),
    )
    defer span.End()
    
    startTime := time.Now()
    num, err := t.QuerySeter.AllWithCtx(ctx, container, cols...)
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Int64("db.row_count", num),
        attribute.Float64("db.duration_ms", float64(duration.Milliseconds())),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "query failed")
        return 0, err
    }
    
    span.SetStatus(codes.Ok, "")
    return num, nil
}
```

### 4.3 查询性能分析

**`services/user_service.go`**:

```go
package services

import (
    "context"
    "myapp/models"
    "myapp/pkg/db"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

type UserService struct {
    orm    *db.TracedOrmer
    tracer trace.Tracer
}

func NewUserService() *UserService {
    return &UserService{
        orm:    db.NewTracedOrm().(*db.TracedOrmer),
        tracer: otel.Tracer("user-service"),
    }
}

// GetUserByID 根据 ID 获取用户
func (s *UserService) GetUserByID(ctx context.Context, userID int64) (*models.User, error) {
    ctx, span := s.tracer.Start(ctx, "UserService.GetUserByID",
        trace.WithAttributes(
            attribute.Int64("user.id", userID),
        ),
    )
    defer span.End()
    
    user := &models.User{ID: userID}
    err := s.orm.ReadWithContext(ctx, user)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )
    
    return user, nil
}

// ListUsers 获取用户列表
func (s *UserService) ListUsers(ctx context.Context, page, pageSize int) ([]*models.User, int64, error) {
    ctx, span := s.tracer.Start(ctx, "UserService.ListUsers",
        trace.WithAttributes(
            attribute.Int("pagination.page", page),
            attribute.Int("pagination.page_size", pageSize),
        ),
    )
    defer span.End()
    
    var users []*models.User
    qs := s.orm.QueryTableWithContext(ctx, new(models.User))
    
    // 计算总数
    total, err := qs.Count()
    if err != nil {
        span.RecordError(err)
        return nil, 0, err
    }
    
    // 分页查询
    _, err = qs.Limit(pageSize, (page-1)*pageSize).All(&users)
    if err != nil {
        span.RecordError(err)
        return nil, 0, err
    }
    
    span.SetAttributes(
        attribute.Int64("result.total", total),
        attribute.Int("result.count", len(users)),
    )
    
    return users, total, nil
}

// CreateUser 创建用户
func (s *UserService) CreateUser(ctx context.Context, name, email string) (*models.User, error) {
    ctx, span := s.tracer.Start(ctx, "UserService.CreateUser",
        trace.WithAttributes(
            attribute.String("user.name", name),
            attribute.String("user.email", email),
        ),
    )
    defer span.End()
    
    user := &models.User{
        Name:  name,
        Email: email,
    }
    
    id, err := s.orm.InsertWithContext(ctx, user)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    user.ID = id
    span.SetAttributes(attribute.Int64("user.id", id))
    
    return user, nil
}
```

---

## 5. 缓存追踪

### 5.1 Cache 模块集成

**`pkg/cache/traced_cache.go`**:

```go
package cache

import (
    "context"
    "time"

    "github.com/beego/beego/v2/client/cache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TracedCache 带追踪的缓存包装器
type TracedCache struct {
    cache.Cache
    tracer trace.Tracer
    name   string
}

// NewTracedCache 创建带追踪的缓存
func NewTracedCache(c cache.Cache, name string) cache.Cache {
    return &TracedCache{
        Cache:  c,
        tracer: otel.Tracer("beego-cache"),
        name:   name,
    }
}

// Get 带追踪的获取
func (t *TracedCache) Get(ctx context.Context, key string) (interface{}, error) {
    ctx, span := t.tracer.Start(ctx, "cache.Get",
        trace.WithAttributes(
            attribute.String("cache.name", t.name),
            attribute.String("cache.operation", "GET"),
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()
    
    startTime := time.Now()
    value, err := t.Cache.Get(ctx, key)
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Float64("cache.duration_ms", float64(duration.Microseconds())/1000),
    )
    
    if err != nil {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        if err != cache.ErrKeyNotFound {
            span.RecordError(err)
            span.SetStatus(codes.Error, "get failed")
        }
        return nil, err
    }
    
    span.SetAttributes(attribute.Bool("cache.hit", true))
    span.SetStatus(codes.Ok, "")
    return value, nil
}

// Put 带追踪的设置
func (t *TracedCache) Put(ctx context.Context, key string, val interface{}, timeout time.Duration) error {
    ctx, span := t.tracer.Start(ctx, "cache.Put",
        trace.WithAttributes(
            attribute.String("cache.name", t.name),
            attribute.String("cache.operation", "PUT"),
            attribute.String("cache.key", key),
            attribute.Float64("cache.ttl_seconds", timeout.Seconds()),
        ),
    )
    defer span.End()
    
    err := t.Cache.Put(ctx, key, val, timeout)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "put failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// Delete 带追踪的删除
func (t *TracedCache) Delete(ctx context.Context, key string) error {
    ctx, span := t.tracer.Start(ctx, "cache.Delete",
        trace.WithAttributes(
            attribute.String("cache.name", t.name),
            attribute.String("cache.operation", "DELETE"),
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()
    
    err := t.Cache.Delete(ctx, key)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "delete failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}
```

### 5.2 Redis 缓存追踪

**`pkg/cache/redis_cache.go`**:

```go
package cache

import (
    "github.com/beego/beego/v2/client/cache"
    _ "github.com/beego/beego/v2/client/cache/redis"
)

// InitRedisCache 初始化 Redis 缓存（带追踪）
func InitRedisCache() (cache.Cache, error) {
    config := `{"conn":"127.0.0.1:6379","dbNum":"0","password":""}`
    
    // 创建 Redis 缓存
    c, err := cache.NewCache("redis", config)
    if err != nil {
        return nil, err
    }
    
    // 包装为带追踪的缓存
    return NewTracedCache(c, "redis"), nil
}
```

### 5.3 Memcache 追踪

**`pkg/cache/memcache_cache.go`**:

```go
package cache

import (
    "github.com/beego/beego/v2/client/cache"
    _ "github.com/beego/beego/v2/client/cache/memcache"
)

// InitMemcacheCache 初始化 Memcache 缓存（带追踪）
func InitMemcacheCache() (cache.Cache, error) {
    config := `{"conn":"127.0.0.1:11211"}`
    
    // 创建 Memcache 缓存
    c, err := cache.NewCache("memcache", config)
    if err != nil {
        return nil, err
    }
    
    // 包装为带追踪的缓存
    return NewTracedCache(c, "memcache"), nil
}
```

---

## 6. Task 任务调度追踪

### 6.1 Cron 任务追踪

**`tasks/cron_tasks.go`**:

```go
package tasks

import (
    "context"
    "time"

    "github.com/beego/beego/v2/task"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// CleanupTask 清理任务
type CleanupTask struct {
    tracer trace.Tracer
}

func NewCleanupTask() *CleanupTask {
    return &CleanupTask{
        tracer: otel.Tracer("cron-task"),
    }
}

// Run 执行任务
func (t *CleanupTask) Run() error {
    ctx := context.Background()
    ctx, span := t.tracer.Start(ctx, "CleanupTask.Run",
        trace.WithAttributes(
            attribute.String("task.name", "cleanup"),
            attribute.String("task.type", "cron"),
        ),
    )
    defer span.End()
    
    // 模拟清理逻辑
    startTime := time.Now()
    
    // 执行清理
    // ...
    
    duration := time.Since(startTime)
    span.SetAttributes(
        attribute.Float64("task.duration_ms", float64(duration.Milliseconds())),
    )
    
    return nil
}

// RegisterTasks 注册所有定时任务
func RegisterTasks() {
    // 每天凌晨 2 点执行清理任务
    cleanupTask := task.NewTask("cleanup", "0 0 2 * * *", NewCleanupTask().Run)
    task.AddTask("cleanup", cleanupTask)
    
    // 启动任务调度器
    task.StartTask()
}
```

### 6.2 异步任务追踪

**`tasks/async_tasks.go`**:

```go
package tasks

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// SendEmailTask 发送邮件异步任务
func SendEmailTask(ctx context.Context, to, subject, body string) {
    tracer := otel.Tracer("async-task")
    
    ctx, span := tracer.Start(ctx, "SendEmailTask",
        trace.WithAttributes(
            attribute.String("task.type", "async"),
            attribute.String("email.to", to),
            attribute.String("email.subject", subject),
        ),
    )
    defer span.End()
    
    // 模拟发送邮件
    time.Sleep(100 * time.Millisecond)
    
    // 记录结果
    span.SetAttributes(
        attribute.Bool("email.sent", true),
    )
    span.SetStatus(codes.Ok, "email sent successfully")
}

// ProcessImageTask 处理图片异步任务
func ProcessImageTask(ctx context.Context, imageURL string) error {
    tracer := otel.Tracer("async-task")
    
    ctx, span := tracer.Start(ctx, "ProcessImageTask",
        trace.WithAttributes(
            attribute.String("task.type", "async"),
            attribute.String("image.url", imageURL),
        ),
    )
    defer span.End()
    
    // 模拟图片处理
    time.Sleep(500 * time.Millisecond)
    
    if imageURL == "" {
        err := fmt.Errorf("invalid image URL")
        span.RecordError(err)
        span.SetStatus(codes.Error, "processing failed")
        return err
    }
    
    span.SetAttributes(
        attribute.Bool("image.processed", true),
    )
    span.SetStatus(codes.Ok, "image processed successfully")
    return nil
}
```

---

## 7. Session 追踪

### 7.1 Session 中间件

**`pkg/middleware/session.go`**:

```go
package middleware

import (
    "github.com/beego/beego/v2/server/web"
    "github.com/beego/beego/v2/server/web/context"
    "github.com/beego/beego/v2/server/web/session"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

var globalSessions *session.Manager

// InitSession 初始化 Session 管理器
func InitSession() error {
    config := &session.ManagerConfig{
        CookieName:      "beego_session",
        EnableSetCookie: true,
        Gclifetime:      3600,
        Secure:          false,
        CookieLifeTime:  3600,
        ProviderConfig:  "", // 使用内存存储
    }
    
    var err error
    globalSessions, err = session.NewManager("memory", config)
    if err != nil {
        return err
    }
    
    go globalSessions.GC()
    return nil
}

// SessionTracingFilter Session 追踪 Filter
func SessionTracingFilter(ctx *context.Context) {
    tracer := otel.Tracer("session-middleware")
    
    spanCtx := ctx.Request.Context()
    spanCtx, span := tracer.Start(spanCtx, "Session.Get",
        trace.WithAttributes(
            attribute.String("component", "session"),
        ),
    )
    defer span.End()
    
    // 获取 Session
    sess, err := globalSessions.SessionStart(ctx.ResponseWriter, ctx.Request)
    if err != nil {
        span.RecordError(err)
        return
    }
    
    sessionID := sess.SessionID()
    span.SetAttributes(
        attribute.String("session.id", sessionID),
    )
    
    // 将 Session 存储到上下文
    ctx.Input.SetData("session", sess)
}
```

### 7.2 Session 存储追踪

**`pkg/session/redis_session.go`**:

```go
package session

import (
    "context"

    "github.com/beego/beego/v2/server/web/session"
    _ "github.com/beego/beego/v2/server/web/session/redis"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TracedSession 带追踪的 Session
type TracedSession struct {
    session.Store
    tracer trace.Tracer
}

// Get 带追踪的获取
func (s *TracedSession) Get(ctx context.Context, key interface{}) interface{} {
    ctx, span := s.tracer.Start(ctx, "session.Get",
        trace.WithAttributes(
            attribute.String("session.operation", "GET"),
            attribute.String("session.key", key.(string)),
        ),
    )
    defer span.End()
    
    value := s.Store.Get(ctx, key)
    span.SetAttributes(
        attribute.Bool("session.found", value != nil),
    )
    
    return value
}

// Set 带追踪的设置
func (s *TracedSession) Set(ctx context.Context, key, value interface{}) error {
    ctx, span := s.tracer.Start(ctx, "session.Set",
        trace.WithAttributes(
            attribute.String("session.operation", "SET"),
            attribute.String("session.key", key.(string)),
        ),
    )
    defer span.End()
    
    err := s.Store.Set(ctx, key, value)
    if err != nil {
        span.RecordError(err)
    }
    
    return err
}

// InitRedisSession 初始化 Redis Session（带追踪）
func InitRedisSession() (*session.Manager, error) {
    config := &session.ManagerConfig{
        CookieName:      "beego_session",
        EnableSetCookie: true,
        Gclifetime:      3600,
        Secure:          false,
        CookieLifeTime:  3600,
        ProviderConfig:  "127.0.0.1:6379",
    }
    
    return session.NewManager("redis", config)
}
```

---

## 8. 完整微服务示例

### 8.1 用户服务

**`main.go`**:

```go
package main

import (
    "context"
    "log"
    "time"

    "myapp/controllers"
    "myapp/pkg/middleware"
    "myapp/pkg/telemetry"
    "myapp/tasks"

    "github.com/beego/beego/v2/server/web"
)

func main() {
    // 1. 初始化 OpenTelemetry
    tp, err := telemetry.InitTracer(telemetry.TelemetryConfig{
        ServiceName:       "user-service",
        ServiceVersion:    "1.0.0",
        OTLPEndpoint:      "localhost:4317",
        SamplingRate:      1.0,
        EnableCompression: true,
    })
    if err != nil {
        log.Fatalf("Failed to initialize tracer: %v", err)
    }
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer: %v", err)
        }
    }()
    
    // 2. 注册 Filter
    middleware.RegisterFilters()
    
    // 3. 初始化 Session
    if err := middleware.InitSession(); err != nil {
        log.Fatalf("Failed to initialize session: %v", err)
    }
    
    // 4. 注册路由
    web.Router("/user/:id", &controllers.UserController{}, "get:GetUser")
    web.Router("/user", &controllers.UserController{}, "post:CreateUser")
    
    // 5. 注册定时任务
    tasks.RegisterTasks()
    
    // 6. 配置服务器
    web.BConfig.AppName = "user-service"
    web.BConfig.RunMode = "prod"
    web.BConfig.Listen.HTTPPort = 8080
    web.BConfig.CopyRequestBody = true
    web.BConfig.EnableErrorsShow = false
    web.BConfig.EnableErrorsRender = false
    
    // 7. 启动服务
    web.Run()
}
```

### 8.2 API 文档集成

**`routers/router.go`**:

```go
package routers

import (
    "myapp/controllers"

    "github.com/beego/beego/v2/server/web"
)

func init() {
    // API Namespace
    ns := web.NewNamespace("/api/v1",
        // User routes
        web.NSNamespace("/users",
            web.NSInclude(
                &controllers.UserController{},
            ),
        ),
    )
    
    web.AddNamespace(ns)
    
    // Swagger 文档（生产环境关闭）
    if web.BConfig.RunMode == "dev" {
        web.BConfig.WebConfig.DirectoryIndex = true
        web.BConfig.WebConfig.StaticDir["/swagger"] = "swagger"
    }
}

// 生成 Swagger 文档
// $ bee run -gendoc=true -downdoc=true
```

### 8.3 配置管理

**`conf/app.conf`**:

```ini
appname = user-service
httpport = 8080
runmode = prod

# 数据库配置
db.host = 127.0.0.1
db.port = 3306
db.user = root
db.password = password
db.database = myapp

# Redis 配置
redis.host = 127.0.0.1
redis.port = 6379
redis.password = 
redis.db = 0

# OTLP 配置
otlp.endpoint = localhost:4317
otlp.service_name = user-service
otlp.sampling_rate = 1.0

# 日志配置
log.level = info
log.filename = logs/app.log
log.maxlines = 100000
log.maxsize = 10000000
log.daily = true
log.maxdays = 7
```

**读取配置**:

```go
package config

import (
    "github.com/beego/beego/v2/server/web"
)

// GetConfig 读取配置
func GetConfig() *Config {
    return &Config{
        DB: DBConfig{
            Host:     web.AppConfig.String("db.host"),
            Port:     web.AppConfig.DefaultInt("db.port", 3306),
            User:     web.AppConfig.String("db.user"),
            Password: web.AppConfig.String("db.password"),
            Database: web.AppConfig.String("db.database"),
        },
        OTLP: OTLPConfig{
            Endpoint:     web.AppConfig.String("otlp.endpoint"),
            ServiceName:  web.AppConfig.String("otlp.service_name"),
            SamplingRate: web.AppConfig.DefaultFloat("otlp.sampling_rate", 1.0),
        },
    }
}

type Config struct {
    DB   DBConfig
    OTLP OTLPConfig
}

type DBConfig struct {
    Host     string
    Port     int
    User     string
    Password string
    Database string
}

type OTLPConfig struct {
    Endpoint     string
    ServiceName  string
    SamplingRate float64
}
```

---

## 9. 最佳实践

### 9.1 项目结构

```text
myapp/
├── conf/
│   ├── app.conf              # 主配置文件
│   ├── app.dev.conf          # 开发环境配置
│   └── app.prod.conf         # 生产环境配置
├── controllers/              # 控制器层
│   ├── base.go               # 基础控制器
│   ├── user.go               # 用户控制器
│   └── admin.go              # 管理员控制器
├── models/                   # 模型层
│   ├── init.go               # ORM 初始化
│   ├── user.go               # 用户模型
│   └── order.go              # 订单模型
├── services/                 # 服务层（业务逻辑）
│   ├── user_service.go       # 用户服务
│   └── order_service.go      # 订单服务
├── pkg/                      # 公共包
│   ├── telemetry/            # 可观测性
│   │   ├── tracer.go         # 追踪初始化
│   │   └── metrics.go        # 指标初始化
│   ├── middleware/           # 中间件
│   │   ├── tracing.go        # 追踪中间件
│   │   ├── auth.go           # 认证中间件
│   │   └── ratelimit.go      # 限流中间件
│   ├── db/                   # 数据库
│   │   └── traced_orm.go     # 带追踪的 ORM
│   └── cache/                # 缓存
│       └── traced_cache.go   # 带追踪的缓存
├── tasks/                    # 定时任务
│   ├── cron_tasks.go         # Cron 任务
│   └── async_tasks.go        # 异步任务
├── routers/                  # 路由配置
│   └── router.go             # 路由定义
├── tests/                    # 测试
│   ├── controller_test.go    # 控制器测试
│   └── service_test.go       # 服务测试
├── static/                   # 静态文件
│   ├── css/
│   ├── js/
│   └── img/
├── views/                    # 视图模板
│   ├── layout/
│   └── user/
├── swagger/                  # Swagger 文档
├── logs/                     # 日志文件
├── go.mod
├── go.sum
└── main.go                   # 入口文件
```

### 9.2 错误处理

**`pkg/errors/errors.go`**:

```go
package errors

import (
    "fmt"

    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// AppError 应用错误
type AppError struct {
    Code    int
    Message string
    Details interface{}
    Err     error
}

func (e *AppError) Error() string {
    if e.Err != nil {
        return fmt.Sprintf("%s: %v", e.Message, e.Err)
    }
    return e.Message
}

// 预定义错误
var (
    ErrNotFound = &AppError{
        Code:    404,
        Message: "Resource not found",
    }
    ErrUnauthorized = &AppError{
        Code:    401,
        Message: "Unauthorized",
    }
    ErrBadRequest = &AppError{
        Code:    400,
        Message: "Bad request",
    }
    ErrInternalServer = &AppError{
        Code:    500,
        Message: "Internal server error",
    }
)

// HandleError 处理错误并记录到 Span
func HandleError(span trace.Span, err error) {
    if err == nil {
        return
    }
    
    span.RecordError(err)
    
    if appErr, ok := err.(*AppError); ok {
        span.SetStatus(codes.Error, appErr.Message)
    } else {
        span.SetStatus(codes.Error, err.Error())
    }
}
```

### 9.3 性能优化

**最佳实践**：

```go
// 1. 使用对象池减少内存分配
var bufferPool = sync.Pool{
    New: func() interface{} {
        return new(bytes.Buffer)
    },
}

// 2. 批量处理数据库操作
func (s *UserService) BatchCreateUsers(ctx context.Context, users []*models.User) error {
    ctx, span := s.tracer.Start(ctx, "UserService.BatchCreateUsers")
    defer span.End()
    
    // 使用 InsertMulti
    num, err := s.orm.InsertMulti(100, users)
    span.SetAttributes(attribute.Int64("batch.size", num))
    
    return err
}

// 3. 采样策略优化
// 生产环境使用 10% 采样
cfg := telemetry.TelemetryConfig{
    SamplingRate: 0.1,  // 10% 采样
}

// 4. 异步导出 Span
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        sdktrace.WithBatchTimeout(5*time.Second),
        sdktrace.WithMaxExportBatchSize(512),
    ),
)
```

---

## 10. 生产部署

### 10.1 Docker 容器化

**`Dockerfile`**:

```dockerfile
# 构建阶段
FROM golang:1.25.1-alpine AS builder

WORKDIR /build

# 安装依赖
RUN apk add --no-cache git

# 复制 go.mod 和 go.sum
COPY go.mod go.sum ./
RUN go mod download

# 复制源代码
COPY . .

# 编译
RUN CGO_ENABLED=0 GOOS=linux go build -a -installsuffix cgo \
    -ldflags='-w -s -extldflags "-static"' -o myapp .

# 运行阶段
FROM alpine:latest

RUN apk --no-cache add ca-certificates tzdata

WORKDIR /app

# 复制二进制文件
COPY --from=builder /build/myapp .
COPY --from=builder /build/conf ./conf
COPY --from=builder /build/static ./static
COPY --from=builder /build/views ./views

# 创建日志目录
RUN mkdir -p logs

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8080/health || exit 1

# 运行
CMD ["./myapp"]
```

**`docker-compose.yml`**:

```yaml
version: '3.8'

services:
  user-service:
    build: .
    ports:
      - "8080:8080"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
      - OTEL_SERVICE_NAME=user-service
      - DB_HOST=mysql
      - REDIS_HOST=redis
    depends_on:
      - mysql
      - redis
      - otel-collector
    networks:
      - myapp-network

  mysql:
    image: mysql:8.0
    environment:
      MYSQL_ROOT_PASSWORD: password
      MYSQL_DATABASE: myapp
    volumes:
      - mysql-data:/var/lib/mysql
    networks:
      - myapp-network

  redis:
    image: redis:7-alpine
    networks:
      - myapp-network

  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"  # OTLP gRPC
      - "4318:4318"  # OTLP HTTP
    networks:
      - myapp-network

  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"  # Jaeger UI
      - "14250:14250"  # gRPC
    networks:
      - myapp-network

networks:
  myapp-network:
    driver: bridge

volumes:
  mysql-data:
```

### 10.2 监控告警

**Prometheus 指标导出**:

```go
package telemetry

import (
    "github.com/prometheus/client_golang/prometheus"
    "github.com/prometheus/client_golang/prometheus/promhttp"
    "github.com/beego/beego/v2/server/web"
)

// InitMetrics 初始化 Prometheus 指标
func InitMetrics() {
    // 注册默认指标
    prometheus.MustRegister(prometheus.NewGoCollector())
    prometheus.MustRegister(prometheus.NewProcessCollector(prometheus.ProcessCollectorOpts{}))
    
    // 暴露 /metrics 端点
    web.Handler("/metrics", promhttp.Handler())
}
```

### 10.3 日志集成

**结构化日志**:

```go
package logging

import (
    "context"

    "github.com/beego/beego/v2/core/logs"
    "go.opentelemetry.io/otel/trace"
)

// LogWithTrace 带追踪信息的日志
func LogWithTrace(ctx context.Context, level, message string, fields map[string]interface{}) {
    span := trace.SpanFromContext(ctx)
    if span.SpanContext().IsValid() {
        fields["trace_id"] = span.SpanContext().TraceID().String()
        fields["span_id"] = span.SpanContext().SpanID().String()
    }
    
    logs.Info("%s: %v", message, fields)
}
```

---

## 11. 总结

### 11.1 核心优势

```text
✅ 功能完整      - MVC、ORM、Cache、Session、Task 一应俱全
✅ 企业级        - 成熟稳定，被多家大型企业采用
✅ 中文生态      - 完善的中文文档和活跃社区
✅ 自动化工具    - bee 工具快速生成项目和代码
✅ 完整追踪      - 全栈 OTLP 集成（HTTP、ORM、Cache、Task）
✅ 易于集成      - Filter 机制方便集成中间件
✅ 高可扩展性    - 模块化设计，易于扩展
```

### 11.2 适用场景

| 场景 | 适用度 | 说明 |
|------|--------|------|
| **企业管理系统** | ⭐⭐⭐⭐⭐ | MVC 架构完美契合 |
| **CMS 系统** | ⭐⭐⭐⭐⭐ | 内置 ORM、Session、模板引擎 |
| **RESTful API** | ⭐⭐⭐⭐⭐ | 完整的 REST 支持 + Swagger |
| **微服务** | ⭐⭐⭐⭐ | 需手动集成服务发现 |
| **高性能场景** | ⭐⭐⭐ | 性能不如 Gin/Fiber |

### 11.3 相关资源

**官方资源**:

- [Beego 官网](https://beego.wiki/)
- [Beego GitHub](https://github.com/beego/beego)
- [Beego 中文文档](https://beego.wiki/zh-CN/)
- [bee 工具](https://github.com/beego/bee)

**OpenTelemetry**:

- [OpenTelemetry Go SDK](https://github.com/open-telemetry/opentelemetry-go)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)

**示例代码**:

- [完整示例](https://github.com/your-org/beego-otlp-example)

---

**最后更新**: 2025-10-11  
**文档版本**: v1.0.0  
**维护者**: OTLP Go Integration Team

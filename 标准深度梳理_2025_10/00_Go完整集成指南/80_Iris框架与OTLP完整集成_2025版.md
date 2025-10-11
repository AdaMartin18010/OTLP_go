# 80. Iris 框架与 OTLP 完整集成（2025版）

> **Iris 版本**: v12.2.11  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [80. Iris 框架与 OTLP 完整集成（2025版）](#80-iris-框架与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Iris 框架概述](#1-iris-框架概述)
    - [1.1 为什么选择 Iris](#11-为什么选择-iris)
    - [1.2 核心特性](#12-核心特性)
    - [1.3 性能对比](#13-性能对比)
  - [2. 快速开始](#2-快速开始)
  - [3. OTLP 完整集成](#3-otlp-完整集成)
    - [3.1 TracerProvider 初始化](#31-tracerprovider-初始化)
    - [3.2 Iris 中间件](#32-iris-中间件)
    - [3.3 路由追踪](#33-路由追踪)
  - [4. MVC 架构集成](#4-mvc-架构集成)
    - [4.1 MVC 应用](#41-mvc-应用)
    - [4.2 注册 MVC](#42-注册-mvc)
  - [5. 会话管理与追踪](#5-会话管理与追踪)
    - [5.1 Session 中间件](#51-session-中间件)
  - [6. WebSocket 追踪](#6-websocket-追踪)
    - [6.1 WebSocket 服务器](#61-websocket-服务器)
  - [7. 依赖注入追踪](#7-依赖注入追踪)
    - [7.1 Hero 依赖注入](#71-hero-依赖注入)
  - [8. 完整示例](#8-完整示例)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 性能优化](#91-性能优化)
    - [9.2 错误处理](#92-错误处理)
  - [10. 总结](#10-总结)
    - [10.1 核心优势](#101-核心优势)
    - [10.2 适用场景](#102-适用场景)
    - [10.3 相关资源](#103-相关资源)

---

## 1. Iris 框架概述

### 1.1 为什么选择 Iris

**Iris** 是由希腊开发者 Gerasimos Maropoulos 创建的高性能 Go Web 框架。

```text
✅ 极高性能        - TechEmpower 基准测试中名列前茅
✅ 功能完整        - MVC、依赖注入、WebSocket 等
✅ 优雅 API        - 简洁直观的 API 设计
✅ 完善文档        - 多语言文档（含中文）
✅ 社区活跃        - GitHub 25k+ stars
✅ 企业级特性      - 会话管理、视图引擎、国际化
✅ HTTP/2 Push    - 原生支持服务端推送
```

### 1.2 核心特性

```go
// Iris 核心组件
type IrisFramework struct {
    // 核心
    App        *iris.Application
    Router     iris.Party
    
    // MVC
    MVC        *mvc.Application
    DI         *hero.Container  // 依赖注入
    
    // 会话
    Sessions   *sessions.Sessions
    
    // WebSocket
    WebSockets iris.WebsocketServer
    
    // 可观测性
    Tracer     trace.TracerProvider
    Meter      metric.MeterProvider
}
```

### 1.3 性能对比

**TechEmpower Round 21 基准测试**:

```text
┌────────────────────────────────────────────────┐
│      性能对比 (请求/秒)                         │
├──────────┬─────────┬─────────┬────────────────┤
│  框架    │ Plaintext│  JSON   │  对比         │
├──────────┼─────────┼─────────┼────────────────┤
│  Iris    │ 950k    │ 750k    │ 最高性能       │
│  Fiber   │ 900k    │ 700k    │ 接近 Iris      │
│  Gin     │ 600k    │ 500k    │ 中等性能       │
│  Echo    │ 550k    │ 480k    │ 中等性能       │
│  Beego   │ 300k    │ 250k    │ 较低性能       │
└──────────┴─────────┴─────────┴────────────────┘
```

---

## 2. 快速开始

**安装依赖**:

```bash
# 安装 Iris
go get github.com/kataras/iris/v12@v12.2.11

# 安装 OpenTelemetry
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/trace@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.32.0
go get go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp@v0.58.0
```

**基础示例**:

```go
package main

import (
    "github.com/kataras/iris/v12"
    "go.opentelemetry.io/otel"
)

func main() {
    app := iris.New()
    
    // 注册追踪中间件
    app.Use(TracingMiddleware())
    
    app.Get("/", func(ctx iris.Context) {
        ctx.WriteString("Hello, Iris + OTLP!")
    })
    
    app.Listen(":8080")
}
```

---

## 3. OTLP 完整集成

### 3.1 TracerProvider 初始化

**`pkg/telemetry/tracer.go`**:

```go
package telemetry

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.28.0"
)

func InitTracer(serviceName, otlpEndpoint string) (*sdktrace.TracerProvider, error) {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    
    // 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint(otlpEndpoint),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String(serviceName),
            semconv.ServiceVersionKey.String("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
        sdktrace.WithResource(res),
        sdktrace.WithBatcher(exporter),
    )
    
    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.TraceContext{})
    
    return tp, nil
}
```

### 3.2 Iris 中间件

**`middleware/tracing.go`**:

```go
package middleware

import (
    "fmt"
    "time"

    "github.com/kataras/iris/v12"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    semconv "go.opentelemetry.io/otel/semconv/v1.28.0"
    "go.opentelemetry.io/otel/trace"
)

// TracingMiddleware Iris 追踪中间件
func TracingMiddleware() iris.Handler {
    tracer := otel.Tracer("iris-server")
    propagator := otel.GetTextMapPropagator()
    
    return func(ctx iris.Context) {
        // 1. 提取 Trace Context
        spanCtx := propagator.Extract(ctx.Request().Context(), 
            propagation.HeaderCarrier(ctx.Request().Header))
        
        // 2. 创建 Span
        spanName := fmt.Sprintf("%s %s", ctx.Method(), ctx.Path())
        spanCtx, span := tracer.Start(spanCtx, spanName,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.HTTPMethodKey.String(ctx.Method()),
                semconv.HTTPURLKey.String(ctx.Request().URL.String()),
                semconv.HTTPTargetKey.String(ctx.Path()),
                semconv.HTTPUserAgentKey.String(ctx.Request().UserAgent()),
                semconv.HTTPClientIPKey.String(ctx.RemoteAddr()),
                attribute.String("http.route", ctx.GetCurrentRoute().Name()),
            ),
        )
        defer span.End()
        
        // 3. 注入新的 Context
        ctx.ResetRequest(ctx.Request().WithContext(spanCtx))
        
        // 4. 记录开始时间
        startTime := time.Now()
        
        // 5. 执行后续中间件和处理器
        ctx.Next()
        
        // 6. 记录响应信息
        duration := time.Since(startTime)
        statusCode := ctx.GetStatusCode()
        
        span.SetAttributes(
            semconv.HTTPStatusCodeKey.Int(statusCode),
            attribute.Int64("http.response.size", int64(ctx.ResponseWriter().Written())),
            attribute.Float64("http.duration_ms", float64(duration.Milliseconds())),
        )
        
        // 7. 记录错误
        if statusCode >= 400 {
            span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", statusCode))
            if statusCode >= 500 {
                span.RecordError(fmt.Errorf("server error: %d", statusCode))
            }
        } else {
            span.SetStatus(codes.Ok, "")
        }
    }
}
```

### 3.3 路由追踪

**`main.go`**:

```go
package main

import (
    "context"
    "log"
    "time"

    "github.com/kataras/iris/v12"
    "myapp/middleware"
    "myapp/pkg/telemetry"
)

func main() {
    // 1. 初始化 TracerProvider
    tp, err := telemetry.InitTracer("iris-service", "localhost:4317")
    if err != nil {
        log.Fatal(err)
    }
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        tp.Shutdown(ctx)
    }()
    
    // 2. 创建 Iris 应用
    app := iris.New()
    
    // 3. 全局中间件
    app.Use(middleware.TracingMiddleware())
    app.Use(iris.Compression) // 启用压缩
    
    // 4. 路由组
    api := app.Party("/api/v1")
    {
        // 用户路由
        users := api.Party("/users")
        users.Get("/", ListUsers)
        users.Get("/{id:uint64}", GetUser)
        users.Post("/", CreateUser)
        users.Put("/{id:uint64}", UpdateUser)
        users.Delete("/{id:uint64}", DeleteUser)
    }
    
    // 5. 监听
    app.Listen(":8080",
        iris.WithOptimizations,  // 启用优化
        iris.WithoutServerError(iris.ErrServerClosed),
    )
}

// 处理器示例
func GetUser(ctx iris.Context) {
    // 从 Context 获取追踪信息
    spanCtx := ctx.Request().Context()
    tracer := otel.Tracer("user-handler")
    
    spanCtx, span := tracer.Start(spanCtx, "GetUser")
    defer span.End()
    
    // 获取路径参数
    userID := ctx.Params().GetUint64Default("id", 0)
    span.SetAttributes(attribute.Int64("user.id", int64(userID)))
    
    // 业务逻辑
    user := map[string]interface{}{
        "id":   userID,
        "name": "Alice",
    }
    
    ctx.JSON(user)
}
```

---

## 4. MVC 架构集成

### 4.1 MVC 应用

**`mvc/user_controller.go`**:

```go
package mvc

import (
    "context"

    "github.com/kataras/iris/v12"
    "github.com/kataras/iris/v12/mvc"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// UserController 用户控制器
type UserController struct {
    Ctx     iris.Context
    Service *UserService  // 依赖注入
    tracer  trace.Tracer
}

// BeforeActivation 路由配置
func (c *UserController) BeforeActivation(b mvc.BeforeActivation) {
    b.Handle("GET", "/", "Get")
    b.Handle("GET", "/{id:uint64}", "GetBy")
    b.Handle("POST", "/", "Post")
}

// Get 获取用户列表
func (c *UserController) Get() mvc.Result {
    ctx := c.Ctx.Request().Context()
    c.tracer = otel.Tracer("user-controller")
    
    ctx, span := c.tracer.Start(ctx, "UserController.Get")
    defer span.End()
    
    users, err := c.Service.ListUsers(ctx)
    if err != nil {
        span.RecordError(err)
        return mvc.Response{
            Code: 500,
            Object: map[string]string{"error": err.Error()},
        }
    }
    
    return mvc.Response{
        Code:   200,
        Object: users,
    }
}

// GetBy 根据 ID 获取用户
func (c *UserController) GetBy(id uint64) mvc.Result {
    ctx := c.Ctx.Request().Context()
    c.tracer = otel.Tracer("user-controller")
    
    ctx, span := c.tracer.Start(ctx, "UserController.GetBy",
        trace.WithAttributes(
            attribute.Int64("user.id", int64(id)),
        ),
    )
    defer span.End()
    
    user, err := c.Service.GetUserByID(ctx, id)
    if err != nil {
        span.RecordError(err)
        return mvc.Response{
            Code: 404,
            Object: map[string]string{"error": "user not found"},
        }
    }
    
    return mvc.Response{
        Code:   200,
        Object: user,
    }
}

// Post 创建用户
func (c *UserController) Post() mvc.Result {
    ctx := c.Ctx.Request().Context()
    c.tracer = otel.Tracer("user-controller")
    
    ctx, span := c.tracer.Start(ctx, "UserController.Post")
    defer span.End()
    
    var req struct {
        Name  string `json:"name"`
        Email string `json:"email"`
    }
    
    if err := c.Ctx.ReadJSON(&req); err != nil {
        span.RecordError(err)
        return mvc.Response{
            Code: 400,
            Object: map[string]string{"error": "invalid request"},
        }
    }
    
    span.SetAttributes(
        attribute.String("user.name", req.Name),
        attribute.String("user.email", req.Email),
    )
    
    user, err := c.Service.CreateUser(ctx, req.Name, req.Email)
    if err != nil {
        span.RecordError(err)
        return mvc.Response{
            Code: 500,
            Object: map[string]string{"error": err.Error()},
        }
    }
    
    return mvc.Response{
        Code:   201,
        Object: user,
    }
}
```

### 4.2 注册 MVC

**`main.go`**:

```go
func setupMVC(app *iris.Application) {
    // 创建 MVC 应用
    mvcApp := mvc.New(app.Party("/users"))
    
    // 注册依赖（单例）
    mvcApp.Register(
        NewUserService(),      // Service
        NewUserRepository(),   // Repository
    )
    
    // 注册控制器
    mvcApp.Handle(new(mvc.UserController))
}
```

---

## 5. 会话管理与追踪

### 5.1 Session 中间件

**`middleware/session.go`**:

```go
package middleware

import (
    "github.com/kataras/iris/v12"
    "github.com/kataras/iris/v12/sessions"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
    "time"
)

var sess *sessions.Sessions

// InitSessions 初始化 Session 管理器
func InitSessions() {
    sess = sessions.New(sessions.Config{
        Cookie:  "iris_session",
        Expires: 24 * time.Hour,
    })
}

// SessionTracingMiddleware Session 追踪中间件
func SessionTracingMiddleware() iris.Handler {
    tracer := otel.Tracer("session-middleware")
    
    return func(ctx iris.Context) {
        spanCtx := ctx.Request().Context()
        spanCtx, span := tracer.Start(spanCtx, "Session.Get",
            trace.WithAttributes(
                attribute.String("component", "session"),
            ),
        )
        defer span.End()
        
        // 获取 Session
        session := sess.Start(ctx)
        sessionID := session.ID()
        
        span.SetAttributes(
            attribute.String("session.id", sessionID),
        )
        
        // 将 Session 存储到上下文
        ctx.Values().Set("session", session)
        
        ctx.Next()
    }
}

// GetSession 从 Context 获取 Session
func GetSession(ctx iris.Context) *sessions.Session {
    if v := ctx.Values().Get("session"); v != nil {
        return v.(*sessions.Session)
    }
    return sess.Start(ctx)
}
```

---

## 6. WebSocket 追踪

### 6.1 WebSocket 服务器

**`websocket/server.go`**:

```go
package websocket

import (
    "context"

    "github.com/kataras/iris/v12"
    "github.com/kataras/iris/v12/websocket"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// SetupWebSocket 设置 WebSocket 服务器
func SetupWebSocket(app *iris.Application) {
    ws := websocket.New(websocket.DefaultGorillaUpgrader, websocket.Events{
        websocket.OnNativeMessage: func(nsConn *websocket.NSConn, msg websocket.Message) error {
            return handleMessage(nsConn, msg)
        },
    })
    
    app.Get("/ws", websocket.Handler(ws))
}

func handleMessage(nsConn *websocket.NSConn, msg websocket.Message) error {
    tracer := otel.Tracer("websocket-server")
    ctx := context.Background()
    
    ctx, span := tracer.Start(ctx, "WebSocket.HandleMessage",
        trace.WithAttributes(
            attribute.String("ws.event", msg.Event),
            attribute.String("ws.namespace", nsConn.Namespace()),
            attribute.String("ws.room", nsConn.Conn.ID()),
        ),
    )
    defer span.End()
    
    // 处理消息
    span.SetAttributes(
        attribute.Int("ws.message.size", len(msg.Body)),
    )
    
    // 广播给所有客户端
    nsConn.Conn.Server().Broadcast(nsConn, msg)
    
    return nil
}
```

---

## 7. 依赖注入追踪

### 7.1 Hero 依赖注入

**`services/user_service.go`**:

```go
package services

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// UserService 用户服务
type UserService struct {
    repo   *UserRepository
    tracer trace.Tracer
}

// NewUserService 创建用户服务（供依赖注入使用）
func NewUserService(repo *UserRepository) *UserService {
    return &UserService{
        repo:   repo,
        tracer: otel.Tracer("user-service"),
    }
}

// GetUserByID 根据 ID 获取用户
func (s *UserService) GetUserByID(ctx context.Context, id uint64) (*User, error) {
    ctx, span := s.tracer.Start(ctx, "UserService.GetUserByID",
        trace.WithAttributes(
            attribute.Int64("user.id", int64(id)),
        ),
    )
    defer span.End()
    
    user, err := s.repo.FindByID(ctx, id)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    return user, nil
}

// ListUsers 获取用户列表
func (s *UserService) ListUsers(ctx context.Context) ([]*User, error) {
    ctx, span := s.tracer.Start(ctx, "UserService.ListUsers")
    defer span.End()
    
    users, err := s.repo.FindAll(ctx)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.Int("result.count", len(users)),
    )
    
    return users, nil
}

// CreateUser 创建用户
func (s *UserService) CreateUser(ctx context.Context, name, email string) (*User, error) {
    ctx, span := s.tracer.Start(ctx, "UserService.CreateUser",
        trace.WithAttributes(
            attribute.String("user.name", name),
            attribute.String("user.email", email),
        ),
    )
    defer span.End()
    
    user := &User{
        Name:  name,
        Email: email,
    }
    
    if err := s.repo.Create(ctx, user); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.Int64("user.id", int64(user.ID)),
    )
    
    return user, nil
}

// User 用户模型
type User struct {
    ID    uint64 `json:"id"`
    Name  string `json:"name"`
    Email string `json:"email"`
}
```

---

## 8. 完整示例

**`main.go`**:

```go
package main

import (
    "context"
    "log"
    "time"

    "github.com/kataras/iris/v12"
    "github.com/kataras/iris/v12/mvc"
    "myapp/middleware"
    "myapp/pkg/telemetry"
    "myapp/services"
    "myapp/websocket"
)

func main() {
    // 1. 初始化 TracerProvider
    tp, err := telemetry.InitTracer("iris-service", "localhost:4317")
    if err != nil {
        log.Fatal(err)
    }
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        tp.Shutdown(ctx)
    }()
    
    // 2. 创建 Iris 应用
    app := iris.New()
    
    // 3. 全局配置
    app.Configure(iris.WithOptimizations, iris.WithConfiguration(iris.Configuration{
        DisableStartupLog: false,
        EnableOptimizations: true,
    }))
    
    // 4. 全局中间件
    app.Use(middleware.TracingMiddleware())
    app.Use(iris.Compression)
    
    // 5. 初始化 Session
    middleware.InitSessions()
    app.Use(middleware.SessionTracingMiddleware())
    
    // 6. API 路由
    api := app.Party("/api/v1")
    api.Get("/health", func(ctx iris.Context) {
        ctx.JSON(iris.Map{"status": "ok"})
    })
    
    // 7. MVC 应用
    setupUserMVC(app)
    
    // 8. WebSocket
    websocket.SetupWebSocket(app)
    
    // 9. 静态文件
    app.HandleDir("/static", iris.Dir("./static"))
    
    // 10. 监听
    app.Listen(":8080",
        iris.WithOptimizations,
        iris.WithoutServerError(iris.ErrServerClosed),
    )
}

func setupUserMVC(app *iris.Application) {
    // 创建 MVC 应用
    userApp := mvc.New(app.Party("/users"))
    
    // 注册依赖
    userRepo := services.NewUserRepository()
    userService := services.NewUserService(userRepo)
    
    userApp.Register(userService)
    
    // 注册控制器
    userApp.Handle(new(mvc.UserController))
}
```

---

## 9. 最佳实践

### 9.1 性能优化

```go
// 1. 启用压缩
app.Use(iris.Compression)

// 2. 启用优化模式
app.Configure(iris.WithOptimizations)

// 3. 设置超时
app.ConfigureHost(func(su *host.Supervisor) {
    su.Server.ReadTimeout = 30 * time.Second
    su.Server.WriteTimeout = 30 * time.Second
})

// 4. 使用对象池
var bufferPool = sync.Pool{
    New: func() interface{} {
        return new(bytes.Buffer)
    },
}
```

### 9.2 错误处理

```go
// 全局错误处理
app.OnErrorCode(iris.StatusNotFound, func(ctx iris.Context) {
    span := trace.SpanFromContext(ctx.Request().Context())
    span.RecordError(fmt.Errorf("404 not found: %s", ctx.Path()))
    
    ctx.JSON(iris.Map{
        "error": "Not Found",
        "path":  ctx.Path(),
    })
})

app.OnErrorCode(iris.StatusInternalServerError, func(ctx iris.Context) {
    span := trace.SpanFromContext(ctx.Request().Context())
    span.RecordError(fmt.Errorf("500 internal error"))
    
    ctx.JSON(iris.Map{
        "error": "Internal Server Error",
    })
})
```

---

## 10. 总结

### 10.1 核心优势

```text
✅ 极高性能        - TechEmpower 基准测试名列前茅
✅ 功能完整        - MVC、DI、WebSocket、Session 等
✅ 优雅 API        - 简洁直观的 API 设计
✅ 完善文档        - 多语言文档（含中文）
✅ HTTP/2 推送     - 原生支持服务端推送
✅ 生产就绪        - 多家企业使用
```

### 10.2 适用场景

| 场景 | 适用度 | 说明 |
|------|--------|------|
| **高性能 API** | ⭐⭐⭐⭐⭐ | 性能最佳 |
| **实时应用** | ⭐⭐⭐⭐⭐ | WebSocket 支持好 |
| **企业应用** | ⭐⭐⭐⭐ | MVC + DI 架构完善 |
| **微服务** | ⭐⭐⭐⭐ | 轻量高性能 |

### 10.3 相关资源

- [Iris 官网](https://www.iris-go.com/)
- [Iris GitHub](https://github.com/kataras/iris)
- [中文文档](https://www.iris-go.com/docs)

---

**最后更新**: 2025-10-11  
**文档版本**: v1.0.0  
**维护者**: OTLP Go Integration Team

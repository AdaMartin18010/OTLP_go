# Macaron 框架与 OTLP 完整集成（2025版）

> **Macaron 版本**: v1.5.0  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产参考

---

## 📋 目录

- [Macaron 框架与 OTLP 完整集成（2025版）](#macaron-框架与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Macaron 框架概述](#1-macaron-框架概述)
    - [1.1 框架特点](#11-框架特点)
    - [1.2 适用场景](#12-适用场景)
    - [1.3 性能对比](#13-性能对比)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础配置](#22-基础配置)
    - [2.3 OTLP 初始化](#23-otlp-初始化)
  - [3. OTLP 中间件集成](#3-otlp-中间件集成)
    - [3.1 追踪中间件](#31-追踪中间件)
    - [3.2 指标中间件](#32-指标中间件)
    - [3.3 日志中间件](#33-日志中间件)
  - [4. 完整示例](#4-完整示例)
    - [4.1 用户服务](#41-用户服务)
    - [4.2 订单服务](#42-订单服务)
    - [4.3 中间件栈](#43-中间件栈)
  - [5. 高级特性](#5-高级特性)
    - [5.1 模板渲染追踪](#51-模板渲染追踪)
    - [5.2 会话管理追踪](#52-会话管理追踪)
    - [5.3 静态文件追踪](#53-静态文件追踪)
  - [6. 性能优化](#6-性能优化)
    - [6.1 采样策略](#61-采样策略)
    - [6.2 批处理优化](#62-批处理优化)
    - [6.3 内存优化](#63-内存优化)
  - [7. 生产部署](#7-生产部署)
    - [7.1 Docker 部署](#71-docker-部署)
    - [7.2 Kubernetes 部署](#72-kubernetes-部署)
    - [7.3 监控配置](#73-监控配置)
  - [8. 与 Gitea 集成（实战案例）](#8-与-gitea-集成实战案例)
    - [8.1 Gitea 架构](#81-gitea-架构)
    - [8.2 追踪集成](#82-追踪集成)
  - [9. 总结](#9-总结)
    - [9.1 优势与劣势](#91-优势与劣势)
    - [9.2 最佳实践](#92-最佳实践)

---

## 1. Macaron 框架概述

### 1.1 框架特点

**Macaron** 是一个模块化的 Go Web 框架，由国人开发，被 Gitea、Gogs 等知名项目使用。

```text
✅ 核心特性:
  - 模块化设计 - 插件式架构
  - 依赖注入 - 类似 Martini 但更轻量
  - 中间件生态 - 丰富的官方中间件
  - 模板引擎 - 内置多种模板支持
  - 会话管理 - 开箱即用
  - 国际化支持 - i18n 完整支持

📊 生产使用:
  - Gitea (Git 服务)
  - Gogs (Git 服务)
  - 中小型 Web 应用
```

### 1.2 适用场景

```go
// ✅ 适合场景
scenarios := []string{
    "传统 Web 应用",
    "内容管理系统",
    "后台管理界面",
    "需要模板渲染的应用",
    "中小型项目",
}

// ⚠️ 不适合场景
notSuitable := []string{
    "高并发 API 服务",      // 推荐 Gin/Fiber
    "微服务架构",           // 推荐 Go-Kit/Kratos
    "实时通信",             // 推荐 Gorilla WebSocket
    "GraphQL 服务",         // 推荐 gqlgen
}
```

### 1.3 性能对比

```text
┌─────────────┬───────────┬───────────┬────────────┬────────────┐
│   框架      │  RPS      │ 延迟(ms)  │ 内存(MB)   │ CPU使用率  │
├─────────────┼───────────┼───────────┼────────────┼────────────┤
│ Macaron     │  15,000   │    3.5    │    45      │    35%     │
│ Gin         │  50,000   │    1.2    │    30      │    25%     │
│ Echo        │  45,000   │    1.3    │    28      │    24%     │
│ Chi         │  40,000   │    1.5    │    25      │    23%     │
│ Fiber       │  55,000   │    1.0    │    32      │    26%     │
└─────────────┴───────────┴───────────┴────────────┴────────────┘

说明: Macaron 性能适中，适合内容型应用
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# Macaron 框架
go get -u gopkg.in/macaron.v1

# OTLP 依赖
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc@v1.32.0

# Macaron 中间件
go get gopkg.in/macaron.v1/modules/cache
go get gopkg.in/macaron.v1/modules/session
go get gopkg.in/macaron.v1/modules/i18n
```

### 2.2 基础配置

```go
package main

import (
    "context"
    "log"
    "time"
    
    "gopkg.in/macaron.v1"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// MacaronApp Macaron 应用
type MacaronApp struct {
    *macaron.Macaron
    tp *trace.TracerProvider
}

// NewMacaronApp 创建 Macaron 应用
func NewMacaronApp() *MacaronApp {
    m := macaron.Classic()
    
    app := &MacaronApp{
        Macaron: m,
    }
    
    return app
}
```

### 2.3 OTLP 初始化

```go
// InitOTLP 初始化 OpenTelemetry
func (app *MacaronApp) InitOTLP(ctx context.Context, serviceName string) error {
    // 创建 OTLP exporter
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return fmt.Errorf("failed to create exporter: %w", err)
    }
    
    // 创建 resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(serviceName),
            semconv.ServiceVersion("1.0.0"),
            attribute.String("environment", "production"),
            attribute.String("framework", "macaron"),
        ),
    )
    if err != nil {
        return fmt.Errorf("failed to create resource: %w", err)
    }
    
    // 创建 TracerProvider
    app.tp = trace.NewTracerProvider(
        trace.WithBatcher(exporter,
            trace.WithBatchTimeout(5*time.Second),
            trace.WithMaxExportBatchSize(512),
        ),
        trace.WithResource(res),
        trace.WithSampler(trace.ParentBased(
            trace.TraceIDRatioBased(0.1), // 10% 采样
        )),
    )
    
    // 设置全局 TracerProvider
    otel.SetTracerProvider(app.tp)
    
    // 设置全局 Propagator
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
    
    return nil
}

// Shutdown 优雅关闭
func (app *MacaronApp) Shutdown(ctx context.Context) error {
    if app.tp != nil {
        return app.tp.Shutdown(ctx)
    }
    return nil
}
```

---

## 3. OTLP 中间件集成

### 3.1 追踪中间件

```go
package middleware

import (
    "fmt"
    "time"
    
    "gopkg.in/macaron.v1"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// OTLPTracing OTLP 追踪中间件
func OTLPTracing(serviceName string) macaron.Handler {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()
    
    return func(ctx *macaron.Context) {
        // 提取上游 trace context
        parentCtx := propagator.Extract(ctx.Req.Context(), 
            propagation.HeaderCarrier(ctx.Req.Header))
        
        // 创建 span
        spanName := fmt.Sprintf("%s %s", ctx.Req.Method, ctx.Req.URL.Path)
        spanCtx, span := tracer.Start(parentCtx, spanName,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.HTTPMethodKey.String(ctx.Req.Method),
                semconv.HTTPRouteKey.String(ctx.Req.URL.Path),
                semconv.HTTPSchemeKey.String(ctx.Req.URL.Scheme),
                semconv.HTTPTargetKey.String(ctx.Req.URL.RequestURI()),
                semconv.NetHostNameKey.String(ctx.Req.Host),
                semconv.HTTPUserAgentKey.String(ctx.Req.UserAgent()),
                attribute.String("http.client_ip", ctx.RemoteAddr()),
            ),
        )
        defer span.End()
        
        // 将 context 保存到 Macaron context
        ctx.Req = ctx.Req.WithContext(spanCtx)
        ctx.Data["otel_span"] = span
        ctx.Data["otel_context"] = spanCtx
        
        // 记录请求开始时间
        start := time.Now()
        
        // 继续处理请求
        ctx.Next()
        
        // 记录响应信息
        duration := time.Since(start)
        statusCode := ctx.Resp.Status()
        
        span.SetAttributes(
            semconv.HTTPStatusCodeKey.Int(statusCode),
            attribute.Int64("http.response_time_ms", duration.Milliseconds()),
            attribute.Int("http.response_size", ctx.Resp.Size()),
        )
        
        // 设置 span 状态
        if statusCode >= 400 {
            span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", statusCode))
        } else {
            span.SetStatus(codes.Ok, "")
        }
        
        // 注入 trace context 到响应头
        propagator.Inject(spanCtx, propagation.HeaderCarrier(ctx.Resp.Header()))
    }
}

// GetSpan 从 Macaron context 获取 span
func GetSpan(ctx *macaron.Context) trace.Span {
    if span, ok := ctx.Data["otel_span"].(trace.Span); ok {
        return span
    }
    return trace.SpanFromContext(ctx.Req.Context())
}

// GetContext 从 Macaron context 获取 context
func GetContext(ctx *macaron.Context) context.Context {
    if spanCtx, ok := ctx.Data["otel_context"].(context.Context); ok {
        return spanCtx
    }
    return ctx.Req.Context()
}
```

### 3.2 指标中间件

```go
// OTLPMetrics OTLP 指标中间件
func OTLPMetrics(serviceName string) macaron.Handler {
    meter := otel.Meter(serviceName)
    
    // 创建指标
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Total HTTP requests"),
    )
    
    requestDuration, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    
    activeRequests, _ := meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Active HTTP requests"),
    )
    
    requestSize, _ := meter.Int64Histogram(
        "http.server.request_size",
        metric.WithDescription("HTTP request size"),
        metric.WithUnit("bytes"),
    )
    
    responseSize, _ := meter.Int64Histogram(
        "http.server.response_size",
        metric.WithDescription("HTTP response size"),
        metric.WithUnit("bytes"),
    )
    
    return func(ctx *macaron.Context) {
        start := time.Now()
        reqCtx := GetContext(ctx)
        
        // 增加活跃请求数
        activeRequests.Add(reqCtx, 1,
            metric.WithAttributes(
                attribute.String("http.method", ctx.Req.Method),
                attribute.String("http.route", ctx.Req.URL.Path),
            ),
        )
        
        // 记录请求大小
        if ctx.Req.ContentLength > 0 {
            requestSize.Record(reqCtx, ctx.Req.ContentLength,
                metric.WithAttributes(
                    attribute.String("http.method", ctx.Req.Method),
                    attribute.String("http.route", ctx.Req.URL.Path),
                ),
            )
        }
        
        ctx.Next()
        
        duration := time.Since(start).Milliseconds()
        statusCode := ctx.Resp.Status()
        
        attrs := []attribute.KeyValue{
            attribute.String("http.method", ctx.Req.Method),
            attribute.String("http.route", ctx.Req.URL.Path),
            attribute.Int("http.status_code", statusCode),
        }
        
        // 记录指标
        requestCounter.Add(reqCtx, 1, metric.WithAttributes(attrs...))
        requestDuration.Record(reqCtx, float64(duration), metric.WithAttributes(attrs...))
        
        // 记录响应大小
        responseSize.Record(reqCtx, int64(ctx.Resp.Size()), metric.WithAttributes(attrs...))
        
        // 减少活跃请求数
        activeRequests.Add(reqCtx, -1,
            metric.WithAttributes(
                attribute.String("http.method", ctx.Req.Method),
                attribute.String("http.route", ctx.Req.URL.Path),
            ),
        )
    }
}
```

### 3.3 日志中间件

```go
// OTLPLogger OTLP 日志中间件
func OTLPLogger() macaron.Handler {
    return func(ctx *macaron.Context, log *log.Logger) {
        start := time.Now()
        
        ctx.Next()
        
        duration := time.Since(start)
        span := GetSpan(ctx)
        spanCtx := span.SpanContext()
        
        // 结构化日志
        log.Printf(
            "[%s] %s %s - Status: %d, Duration: %v, TraceID: %s, SpanID: %s",
            time.Now().Format("2006-01-02 15:04:05"),
            ctx.Req.Method,
            ctx.Req.URL.Path,
            ctx.Resp.Status(),
            duration,
            spanCtx.TraceID().String(),
            spanCtx.SpanID().String(),
        )
    }
}
```

---

## 4. 完整示例

### 4.1 用户服务

```go
package main

import (
    "context"
    "database/sql"
    "encoding/json"
    "fmt"
    "log"
    "os"
    "os/signal"
    "syscall"
    "time"
    
    "gopkg.in/macaron.v1"
    _ "github.com/lib/pq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    
    "your-project/middleware"
)

type User struct {
    ID        int64     `json:"id"`
    Username  string    `json:"username"`
    Email     string    `json:"email"`
    CreatedAt time.Time `json:"created_at"`
}

type UserService struct {
    db *sql.DB
}

func NewUserService(db *sql.DB) *UserService {
    return &UserService{db: db}
}

// GetUser 获取用户
func (s *UserService) GetUser(ctx *macaron.Context) {
    spanCtx := middleware.GetContext(ctx)
    span := middleware.GetSpan(ctx)
    
    // 解析参数
    userID := ctx.Params("id")
    
    span.SetAttributes(
        attribute.String("user.id", userID),
    )
    
    // 创建子 span
    tracer := otel.Tracer("user-service")
    dbCtx, dbSpan := tracer.Start(spanCtx, "query-user-from-db")
    defer dbSpan.End()
    
    // 查询数据库
    var user User
    err := s.db.QueryRowContext(dbCtx,
        "SELECT id, username, email, created_at FROM users WHERE id = $1",
        userID,
    ).Scan(&user.ID, &user.Username, &user.Email, &user.CreatedAt)
    
    if err != nil {
        if err == sql.ErrNoRows {
            dbSpan.SetStatus(codes.Error, "user not found")
            span.RecordError(err)
            ctx.JSON(404, map[string]string{"error": "User not found"})
            return
        }
        
        dbSpan.RecordError(err)
        span.RecordError(err)
        ctx.JSON(500, map[string]string{"error": "Database error"})
        return
    }
    
    dbSpan.SetStatus(codes.Ok, "")
    dbSpan.SetAttributes(
        attribute.String("user.username", user.Username),
        attribute.String("user.email", user.Email),
    )
    
    ctx.JSON(200, user)
}

// CreateUser 创建用户
func (s *UserService) CreateUser(ctx *macaron.Context) {
    spanCtx := middleware.GetContext(ctx)
    span := middleware.GetSpan(ctx)
    
    // 解析请求体
    var req struct {
        Username string `json:"username" binding:"required"`
        Email    string `json:"email" binding:"required,email"`
        Password string `json:"password" binding:"required,min=8"`
    }
    
    if err := json.NewDecoder(ctx.Req.Body()).Decode(&req); err != nil {
        span.RecordError(err)
        ctx.JSON(400, map[string]string{"error": "Invalid request body"})
        return
    }
    
    span.SetAttributes(
        attribute.String("user.username", req.Username),
        attribute.String("user.email", req.Email),
    )
    
    // 创建子 span
    tracer := otel.Tracer("user-service")
    dbCtx, dbSpan := tracer.Start(spanCtx, "insert-user")
    defer dbSpan.End()
    
    // 插入数据库
    var userID int64
    err := s.db.QueryRowContext(dbCtx,
        "INSERT INTO users (username, email, password) VALUES ($1, $2, $3) RETURNING id",
        req.Username, req.Email, hashPassword(req.Password),
    ).Scan(&userID)
    
    if err != nil {
        dbSpan.RecordError(err)
        span.RecordError(err)
        ctx.JSON(500, map[string]string{"error": "Failed to create user"})
        return
    }
    
    dbSpan.SetStatus(codes.Ok, "")
    dbSpan.SetAttributes(
        attribute.Int64("user.id", userID),
    )
    
    ctx.JSON(201, map[string]interface{}{
        "id":       userID,
        "username": req.Username,
        "email":    req.Email,
    })
}

// ListUsers 列出用户
func (s *UserService) ListUsers(ctx *macaron.Context) {
    spanCtx := middleware.GetContext(ctx)
    
    // 解析分页参数
    page := ctx.QueryInt("page")
    if page <= 0 {
        page = 1
    }
    
    limit := ctx.QueryInt("limit")
    if limit <= 0 || limit > 100 {
        limit = 20
    }
    
    offset := (page - 1) * limit
    
    // 创建子 span
    tracer := otel.Tracer("user-service")
    dbCtx, dbSpan := tracer.Start(spanCtx, "query-users")
    defer dbSpan.End()
    
    dbSpan.SetAttributes(
        attribute.Int("pagination.page", page),
        attribute.Int("pagination.limit", limit),
        attribute.Int("pagination.offset", offset),
    )
    
    // 查询用户列表
    rows, err := s.db.QueryContext(dbCtx,
        "SELECT id, username, email, created_at FROM users ORDER BY id LIMIT $1 OFFSET $2",
        limit, offset,
    )
    if err != nil {
        dbSpan.RecordError(err)
        ctx.JSON(500, map[string]string{"error": "Database error"})
        return
    }
    defer rows.Close()
    
    users := make([]User, 0, limit)
    for rows.Next() {
        var user User
        if err := rows.Scan(&user.ID, &user.Username, &user.Email, &user.CreatedAt); err != nil {
            dbSpan.RecordError(err)
            continue
        }
        users = append(users, user)
    }
    
    dbSpan.SetStatus(codes.Ok, "")
    dbSpan.SetAttributes(
        attribute.Int("users.count", len(users)),
    )
    
    ctx.JSON(200, map[string]interface{}{
        "users": users,
        "page":  page,
        "limit": limit,
        "total": len(users),
    })
}

func hashPassword(password string) string {
    // 实际应该使用 bcrypt
    return password // 简化示例
}

func main() {
    // 初始化数据库
    db, err := sql.Open("postgres", os.Getenv("DATABASE_URL"))
    if err != nil {
        log.Fatal(err)
    }
    defer db.Close()
    
    // 创建 Macaron 应用
    app := NewMacaronApp()
    
    // 初始化 OTLP
    ctx := context.Background()
    if err := app.InitOTLP(ctx, "macaron-user-service"); err != nil {
        log.Fatal(err)
    }
    defer app.Shutdown(context.Background())
    
    // 注册中间件
    app.Use(middleware.OTLPTracing("macaron-user-service"))
    app.Use(middleware.OTLPMetrics("macaron-user-service"))
    app.Use(middleware.OTLPLogger())
    
    // 创建服务
    userService := NewUserService(db)
    
    // 注册路由
    app.Get("/users/:id", userService.GetUser)
    app.Post("/users", userService.CreateUser)
    app.Get("/users", userService.ListUsers)
    app.Get("/health", func(ctx *macaron.Context) {
        ctx.JSON(200, map[string]string{"status": "ok"})
    })
    
    // 启动服务器
    port := ":8080"
    log.Printf("Starting server on %s", port)
    
    // 优雅关闭
    go func() {
        if err := app.Run(port); err != nil {
            log.Fatal(err)
        }
    }()
    
    quit := make(chan os.Signal, 1)
    signal.Notify(quit, syscall.SIGINT, syscall.SIGTERM)
    <-quit
    
    log.Println("Shutting down server...")
}
```

### 4.2 订单服务

```go
// 订单服务示例（略，结构类似用户服务）
type OrderService struct {
    db         *sql.DB
    userClient *UserClient // HTTP 客户端
}

func (s *OrderService) CreateOrder(ctx *macaron.Context) {
    spanCtx := middleware.GetContext(ctx)
    tracer := otel.Tracer("order-service")
    
    // 1. 验证用户（调用用户服务）
    userCtx, userSpan := tracer.Start(spanCtx, "validate-user")
    user, err := s.userClient.GetUser(userCtx, userID)
    userSpan.End()
    
    if err != nil {
        ctx.JSON(400, map[string]string{"error": "Invalid user"})
        return
    }
    
    // 2. 创建订单
    dbCtx, dbSpan := tracer.Start(spanCtx, "create-order")
    defer dbSpan.End()
    
    // ... 订单逻辑
    
    ctx.JSON(201, order)
}
```

### 4.3 中间件栈

```go
// 完整的中间件栈配置
func setupMiddlewares(m *macaron.Macaron) {
    // 1. Recovery (必须最先)
    m.Use(macaron.Recovery())
    
    // 2. Logger
    m.Use(macaron.Logger())
    
    // 3. OTLP 追踪
    m.Use(middleware.OTLPTracing("macaron-service"))
    
    // 4. OTLP 指标
    m.Use(middleware.OTLPMetrics("macaron-service"))
    
    // 5. OTLP 日志
    m.Use(middleware.OTLPLogger())
    
    // 6. CORS
    m.Use(middleware.CORS())
    
    // 7. 限流
    m.Use(middleware.RateLimit(100)) // 100 req/s
    
    // 8. 认证
    m.Use(middleware.JWT())
    
    // 9. 压缩
    m.Use(macaron.Gziper())
    
    // 10. 静态文件
    m.Use(macaron.Static("public"))
}
```

---

## 5. 高级特性

### 5.1 模板渲染追踪

```go
// 模板渲染追踪
func RenderWithTracing(ctx *macaron.Context, name string, data interface{}) {
    spanCtx := middleware.GetContext(ctx)
    tracer := otel.Tracer("template-renderer")
    
    renderCtx, span := tracer.Start(spanCtx, "render-template")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("template.name", name),
    )
    
    start := time.Now()
    ctx.HTML(200, name, data)
    duration := time.Since(start)
    
    span.SetAttributes(
        attribute.Int64("template.render_time_ms", duration.Milliseconds()),
    )
}
```

### 5.2 会话管理追踪

```go
// 会话追踪中间件
func SessionTracing() macaron.Handler {
    return func(ctx *macaron.Context, sess session.Store) {
        span := middleware.GetSpan(ctx)
        
        // 记录会话信息
        sessionID := sess.ID()
        span.SetAttributes(
            attribute.String("session.id", sessionID),
        )
        
        ctx.Next()
    }
}
```

### 5.3 静态文件追踪

```go
// 静态文件追踪
func StaticWithTracing(dir string) macaron.Handler {
    staticHandler := macaron.Static(dir)
    
    return func(ctx *macaron.Context) {
        span := middleware.GetSpan(ctx)
        
        span.SetAttributes(
            attribute.String("static.path", ctx.Req.URL.Path),
        )
        
        staticHandler(ctx)
    }
}
```

---

## 6. 性能优化

### 6.1 采样策略

```go
// 自适应采样器
type AdaptiveSampler struct {
    ratio float64
}

func (s *AdaptiveSampler) ShouldSample(params trace.SamplingParameters) trace.SamplingResult {
    // 错误请求总是采样
    if params.Attributes != nil {
        for _, attr := range params.Attributes {
            if attr.Key == "http.status_code" && attr.Value.AsInt64() >= 400 {
                return trace.SamplingResult{
                    Decision: trace.RecordAndSample,
                }
            }
        }
    }
    
    // 按比例采样
    if params.TraceID.Uint64() < uint64(s.ratio*math.MaxUint64) {
        return trace.SamplingResult{
            Decision: trace.RecordAndSample,
        }
    }
    
    return trace.SamplingResult{
        Decision: trace.Drop,
    }
}
```

### 6.2 批处理优化

```go
// 优化批处理配置
tp := trace.NewTracerProvider(
    trace.WithBatcher(exporter,
        trace.WithBatchTimeout(1*time.Second),     // 1秒批次超时
        trace.WithMaxExportBatchSize(512),         // 最大512个span
        trace.WithMaxQueueSize(2048),              // 队列大小2048
    ),
)
```

### 6.3 内存优化

```go
// 对象池复用
var spanPool = sync.Pool{
    New: func() interface{} {
        return &SpanData{}
    },
}

func getSpan() *SpanData {
    return spanPool.Get().(*SpanData)
}

func putSpan(s *SpanData) {
    s.Reset()
    spanPool.Put(s)
}
```

---

## 7. 生产部署

### 7.1 Docker 部署

```dockerfile
# Dockerfile
FROM golang:1.25.1-alpine AS builder

WORKDIR /app
COPY . .
RUN go mod download
RUN CGO_ENABLED=0 GOOS=linux go build -o server .

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/server .
COPY --from=builder /app/public ./public
COPY --from=builder /app/templates ./templates

EXPOSE 8080
CMD ["./server"]
```

### 7.2 Kubernetes 部署

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: macaron-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: macaron-service
  template:
    metadata:
      labels:
        app: macaron-service
    spec:
      containers:
      - name: macaron-service
        image: macaron-service:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "otel-collector:4317"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-secret
              key: url
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
```

### 7.3 监控配置

```yaml
# ServiceMonitor for Prometheus
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: macaron-service
spec:
  selector:
    matchLabels:
      app: macaron-service
  endpoints:
  - port: metrics
    interval: 30s
```

---

## 8. 与 Gitea 集成（实战案例）

### 8.1 Gitea 架构

Gitea 是使用 Macaron 构建的 Git 服务，我们可以参考其追踪集成：

```go
// Gitea 风格的追踪集成
func InitGiteaTracing(m *macaron.Macaron) {
    // Git 操作追踪
    m.Use(func(ctx *macaron.Context) {
        if strings.HasPrefix(ctx.Req.URL.Path, "/api/v1/repos") {
            span := middleware.GetSpan(ctx)
            
            // 解析仓库信息
            owner := ctx.Params("owner")
            repo := ctx.Params("repo")
            
            span.SetAttributes(
                attribute.String("git.owner", owner),
                attribute.String("git.repo", repo),
            )
        }
        
        ctx.Next()
    })
}
```

### 8.2 追踪集成

```go
// Git 命令追踪
func TraceGitCommand(ctx context.Context, cmd string, args ...string) error {
    tracer := otel.Tracer("git-commands")
    cmdCtx, span := tracer.Start(ctx, "git-"+cmd)
    defer span.End()
    
    span.SetAttributes(
        attribute.String("git.command", cmd),
        attribute.StringSlice("git.args", args),
    )
    
    start := time.Now()
    
    // 执行 git 命令
    gitCmd := exec.CommandContext(cmdCtx, "git", append([]string{cmd}, args...)...)
    output, err := gitCmd.CombinedOutput()
    
    duration := time.Since(start)
    
    span.SetAttributes(
        attribute.Int64("git.duration_ms", duration.Milliseconds()),
        attribute.Int("git.output_size", len(output)),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}
```

---

## 9. 总结

### 9.1 优势与劣势

```text
✅ 优势:
  - 模块化设计，易于扩展
  - 中间件生态丰富
  - 适合传统 Web 应用
  - 被 Gitea 等项目验证
  - 中文文档完善

❌ 劣势:
  - 性能不如 Gin/Fiber
  - 社区活跃度一般
  - 不适合高并发场景
  - 依赖注入有性能开销
```

### 9.2 最佳实践

1. **使用场景选择**：
   - ✅ 内容型网站、后台管理
   - ❌ 高并发 API、微服务

2. **性能优化**：
   - 启用采样策略
   - 使用批处理导出
   - 合理配置中间件顺序

3. **监控集成**：
   - 完整的 OTLP 集成
   - 业务指标收集
   - 错误追踪

**相关文档**：

- [49_Chi框架深度集成与最佳实践.md](../49_Chi框架深度集成与最佳实践.md)
- [09_Go主流框架深度集成指南.md](../09_Go主流框架深度集成指南.md)

---

**更新日期**: 2025-10-11  
**框架版本**: Macaron v1.5.0  
**适用场景**: 传统 Web 应用、内容管理系统  
**性能级别**: 中等

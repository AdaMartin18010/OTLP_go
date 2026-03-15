# Go Web 中间件生态与 OTLP 完整集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [Go Web 中间件生态与 OTLP 完整集成](#go-web-中间件生态与-otlp-完整集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Gin - 高性能 Web 框架](#gin---高性能-web-框架)
    - [1. 基础集成](#1-基础集成)
    - [2. 高级中间件](#2-高级中间件)
    - [3. 错误处理](#3-错误处理)
  - [Echo - 简洁的 Web 框架](#echo---简洁的-web-框架)
    - [1. 基础集成](#1-基础集成-1)
    - [2. 分组路由追踪](#2-分组路由追踪)
    - [3. 请求验证](#3-请求验证)
  - [Fiber - 极速 Web 框架](#fiber---极速-web-框架)
    - [1. 基础集成](#1-基础集成-2)
    - [2. 性能优化](#2-性能优化)
    - [3. WebSocket 支持](#3-websocket-支持)
  - [Chi - 轻量级路由器](#chi---轻量级路由器)
    - [1. 基础集成](#1-基础集成-3)
    - [2. 中间件链](#2-中间件链)
    - [3. 子路由器](#3-子路由器)
  - [通用中间件模式](#通用中间件模式)
  - [性能对比](#性能对比)
  - [最佳实践](#最佳实践)

---

## 概述

Go 拥有丰富的 Web 中间件生态系统,每个框架都有其独特的设计理念和性能特点。

**主流框架对比**:

| 框架 | 版本 | 特点 | 性能 | 适用场景 |
|-----|------|------|------|---------|
| **Gin** | v1.10.0 | 高性能,易用 | ⭐⭐⭐⭐⭐ | 通用 Web API |
| **Echo** | v4.12.0 | 简洁,功能完整 | ⭐⭐⭐⭐ | RESTful API |
| **Fiber** | v2.52.5 | Express风格,极速 | ⭐⭐⭐⭐⭐ | 高性能微服务 |
| **Chi** | v5.1.0 | 轻量,标准库兼容 | ⭐⭐⭐⭐ | 灵活路由 |

---

## Gin - 高性能 Web 框架

### 1. 基础集成

```go
package ginserver

import (
    "context"
    "time"

    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// NewGinServer 创建 Gin 服务器
func NewGinServer() *gin.Engine {
    router := gin.New()

    // 使用官方 otelgin 中间件
    router.Use(otelgin.Middleware("gin-service"))

    // 自定义恢复中间件
    router.Use(RecoveryMiddleware())

    // 请求日志中间件
    router.Use(RequestLogMiddleware())

    return router
}

// RecoveryMiddleware 恢复中间件
func RecoveryMiddleware() gin.HandlerFunc {
    tracer := otel.Tracer("gin-recovery")

    return func(c *gin.Context) {
        defer func() {
            if err := recover(); err != nil {
                span := trace.SpanFromContext(c.Request.Context())
                
                span.RecordError(err.(error))
                span.SetStatus(codes.Error, "panic recovered")
                span.SetAttributes(
                    attribute.String("panic.error", fmt.Sprint(err)),
                )

                c.AbortWithStatusJSON(500, gin.H{
                    "error": "Internal Server Error",
                })
            }
        }()

        c.Next()
    }
}

// RequestLogMiddleware 请求日志中间件
func RequestLogMiddleware() gin.HandlerFunc {
    tracer := otel.Tracer("gin-logger")

    return func(c *gin.Context) {
        start := time.Now()

        ctx, span := tracer.Start(c.Request.Context(), "request.log",
            trace.WithAttributes(
                attribute.String("http.method", c.Request.Method),
                attribute.String("http.url", c.Request.URL.String()),
                attribute.String("http.client_ip", c.ClientIP()),
            ),
        )
        defer span.End()

        // 将追踪上下文传递到请求中
        c.Request = c.Request.WithContext(ctx)

        c.Next()

        duration := time.Since(start)

        span.SetAttributes(
            attribute.Int("http.status_code", c.Writer.Status()),
            attribute.Int("http.response_size", c.Writer.Size()),
            attribute.Int64("http.duration_ms", duration.Milliseconds()),
        )

        if c.Writer.Status() >= 400 {
            span.SetStatus(codes.Error, "HTTP error")
        }
    }
}

// 示例路由处理器
func setupGinRoutes(router *gin.Engine) {
    router.GET("/api/users/:id", getUserHandler)
    router.POST("/api/users", createUserHandler)
    router.PUT("/api/users/:id", updateUserHandler)
    router.DELETE("/api/users/:id", deleteUserHandler)
}

func getUserHandler(c *gin.Context) {
    ctx := c.Request.Context()
    tracer := otel.Tracer("gin-handler")

    ctx, span := tracer.Start(ctx, "get_user")
    defer span.End()

    userID := c.Param("id")
    span.SetAttributes(attribute.String("user.id", userID))

    // 业务逻辑
    user, err := fetchUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        c.JSON(500, gin.H{"error": err.Error()})
        return
    }

    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )

    c.JSON(200, user)
}
```

### 2. 高级中间件

```go
package ginserver

import (
    "sync"
    "time"

    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "golang.org/x/time/rate"
)

// MetricsMiddleware Metrics 中间件
func MetricsMiddleware() (gin.HandlerFunc, error) {
    meter := otel.Meter("gin-metrics")

    requestCounter, err := meter.Int64Counter("http.server.requests",
        metric.WithDescription("Total HTTP requests"),
    )
    if err != nil {
        return nil, err
    }

    requestDuration, err := meter.Float64Histogram("http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }

    return func(c *gin.Context) {
        start := time.Now()

        c.Next()

        duration := time.Since(start).Milliseconds()

        attrs := metric.WithAttributes(
            attribute.String("http.method", c.Request.Method),
            attribute.String("http.route", c.FullPath()),
            attribute.Int("http.status_code", c.Writer.Status()),
        )

        requestCounter.Add(c.Request.Context(), 1, attrs)
        requestDuration.Record(c.Request.Context(), float64(duration), attrs)
    }, nil
}

// RateLimitMiddleware 限流中间件
func RateLimitMiddleware(rps int) gin.HandlerFunc {
    tracer := otel.Tracer("gin-rate-limit")
    limiter := rate.NewLimiter(rate.Limit(rps), rps*2)

    return func(c *gin.Context) {
        ctx := c.Request.Context()
        ctx, span := tracer.Start(ctx, "rate_limit.check")
        defer span.End()

        if !limiter.Allow() {
            span.SetAttributes(
                attribute.Bool("rate_limit.exceeded", true),
                attribute.Int("rate_limit.rps", rps),
            )

            c.AbortWithStatusJSON(429, gin.H{
                "error": "Too Many Requests",
            })
            return
        }

        span.SetAttributes(attribute.Bool("rate_limit.allowed", true))
        c.Next()
    }
}

// CacheMiddleware 缓存中间件
type CacheMiddleware struct {
    cache  map[string]*cacheEntry
    mu     sync.RWMutex
    tracer trace.Tracer
}

type cacheEntry struct {
    data      []byte
    expiresAt time.Time
}

func NewCacheMiddleware() *CacheMiddleware {
    return &CacheMiddleware{
        cache:  make(map[string]*cacheEntry),
        tracer: otel.Tracer("gin-cache"),
    }
}

func (cm *CacheMiddleware) Middleware(ttl time.Duration) gin.HandlerFunc {
    return func(c *gin.Context) {
        if c.Request.Method != "GET" {
            c.Next()
            return
        }

        ctx := c.Request.Context()
        ctx, span := cm.tracer.Start(ctx, "cache.check")
        defer span.End()

        key := c.Request.URL.String()

        // 检查缓存
        cm.mu.RLock()
        entry, found := cm.cache[key]
        cm.mu.RUnlock()

        if found && time.Now().Before(entry.expiresAt) {
            span.SetAttributes(
                attribute.Bool("cache.hit", true),
                attribute.String("cache.key", key),
            )

            c.Data(200, "application/json", entry.data)
            c.Abort()
            return
        }

        span.SetAttributes(attribute.Bool("cache.hit", false))

        // 创建响应写入器包装
        writer := &responseWriter{
            ResponseWriter: c.Writer,
            body:           []byte{},
        }
        c.Writer = writer

        c.Next()

        // 缓存响应
        if c.Writer.Status() == 200 {
            cm.mu.Lock()
            cm.cache[key] = &cacheEntry{
                data:      writer.body,
                expiresAt: time.Now().Add(ttl),
            }
            cm.mu.Unlock()

            span.AddEvent("cached_response")
        }
    }
}

type responseWriter struct {
    gin.ResponseWriter
    body []byte
}

func (w *responseWriter) Write(b []byte) (int, error) {
    w.body = append(w.body, b...)
    return w.ResponseWriter.Write(b)
}
```

### 3. 错误处理

```go
package ginserver

import (
    "errors"

    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// ErrorResponse 错误响应
type ErrorResponse struct {
    Code    int    `json:"code"`
    Message string `json:"message"`
    TraceID string `json:"trace_id,omitempty"`
}

// ErrorHandlerMiddleware 错误处理中间件
func ErrorHandlerMiddleware() gin.HandlerFunc {
    tracer := otel.Tracer("gin-error-handler")

    return func(c *gin.Context) {
        c.Next()

        if len(c.Errors) == 0 {
            return
        }

        ctx := c.Request.Context()
        ctx, span := tracer.Start(ctx, "error.handle")
        defer span.End()

        err := c.Errors.Last().Err

        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())

        statusCode := 500
        message := "Internal Server Error"

        // 错误类型判断
        var validationErr *ValidationError
        if errors.As(err, &validationErr) {
            statusCode = 400
            message = validationErr.Error()
        }

        var notFoundErr *NotFoundError
        if errors.As(err, &notFoundErr) {
            statusCode = 404
            message = notFoundErr.Error()
        }

        span.SetAttributes(
            attribute.Int("error.status_code", statusCode),
            attribute.String("error.message", message),
        )

        // 获取 TraceID
        traceID := span.SpanContext().TraceID().String()

        c.JSON(statusCode, ErrorResponse{
            Code:    statusCode,
            Message: message,
            TraceID: traceID,
        })
    }
}

// ValidationError 验证错误
type ValidationError struct {
    Field   string
    Message string
}

func (e *ValidationError) Error() string {
    return fmt.Sprintf("validation failed: %s - %s", e.Field, e.Message)
}

// NotFoundError 未找到错误
type NotFoundError struct {
    Resource string
    ID       string
}

func (e *NotFoundError) Error() string {
    return fmt.Sprintf("%s not found: %s", e.Resource, e.ID)
}
```

---

## Echo - 简洁的 Web 框架

### 1. 基础集成

```go
package echoserver

import (
    "github.com/labstack/echo/v4"
    "go.opentelemetry.io/contrib/instrumentation/github.com/labstack/echo/otelecho"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// NewEchoServer 创建 Echo 服务器
func NewEchoServer() *echo.Echo {
    e := echo.New()

    // 使用官方 otelecho 中间件
    e.Use(otelecho.Middleware("echo-service"))

    // 自定义追踪中间件
    e.Use(TracingMiddleware())

    return e
}

// TracingMiddleware 追踪中间件
func TracingMiddleware() echo.MiddlewareFunc {
    tracer := otel.Tracer("echo-middleware")

    return func(next echo.HandlerFunc) echo.HandlerFunc {
        return func(c echo.Context) error {
            req := c.Request()
            ctx := req.Context()

            ctx, span := tracer.Start(ctx, "http.request",
                trace.WithAttributes(
                    attribute.String("http.method", req.Method),
                    attribute.String("http.url", req.URL.String()),
                    attribute.String("http.route", c.Path()),
                ),
            )
            defer span.End()

            // 更新请求上下文
            c.SetRequest(req.WithContext(ctx))

            err := next(c)

            if err != nil {
                span.RecordError(err)
                span.SetStatus(codes.Error, err.Error())
            } else {
                span.SetAttributes(
                    attribute.Int("http.status_code", c.Response().Status),
                )
            }

            return err
        }
    }
}

// 示例路由处理器
func setupEchoRoutes(e *echo.Echo) {
    e.GET("/api/users/:id", getEchoUserHandler)
    e.POST("/api/users", createEchoUserHandler)

    // 分组路由
    api := e.Group("/api/v2")
    api.Use(AuthMiddleware())
    
    api.GET("/users", listUsersHandler)
    api.GET("/users/:id", getUserDetailHandler)
}

func getEchoUserHandler(c echo.Context) error {
    ctx := c.Request().Context()
    tracer := otel.Tracer("echo-handler")

    ctx, span := tracer.Start(ctx, "get_user")
    defer span.End()

    userID := c.Param("id")
    span.SetAttributes(attribute.String("user.id", userID))

    user, err := fetchUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return c.JSON(500, map[string]string{"error": err.Error()})
    }

    return c.JSON(200, user)
}
```

### 2. 分组路由追踪

```go
package echoserver

import (
    "github.com/labstack/echo/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// GroupTracingMiddleware 分组追踪中间件
func GroupTracingMiddleware(groupName string) echo.MiddlewareFunc {
    tracer := otel.Tracer("echo-group")

    return func(next echo.HandlerFunc) echo.HandlerFunc {
        return func(c echo.Context) error {
            ctx := c.Request().Context()

            ctx, span := tracer.Start(ctx, "group."+groupName,
                trace.WithAttributes(
                    attribute.String("group.name", groupName),
                    attribute.String("route.path", c.Path()),
                ),
            )
            defer span.End()

            c.SetRequest(c.Request().WithContext(ctx))

            return next(c)
        }
    }
}

// 使用示例
func setupGroupedRoutes(e *echo.Echo) {
    // Admin 路由组
    admin := e.Group("/admin")
    admin.Use(GroupTracingMiddleware("admin"))
    admin.Use(AdminAuthMiddleware())
    
    admin.GET("/users", adminListUsers)
    admin.DELETE("/users/:id", adminDeleteUser)

    // API 路由组
    api := e.Group("/api")
    api.Use(GroupTracingMiddleware("api"))
    api.Use(RateLimitMiddleware(100))
    
    api.GET("/posts", listPosts)
    api.POST("/posts", createPost)
}
```

### 3. 请求验证

```go
package echoserver

import (
    "github.com/go-playground/validator/v10"
    "github.com/labstack/echo/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// CustomValidator 自定义验证器
type CustomValidator struct {
    validator *validator.Validate
    tracer    trace.Tracer
}

// NewCustomValidator 创建验证器
func NewCustomValidator() *CustomValidator {
    return &CustomValidator{
        validator: validator.New(),
        tracer:    otel.Tracer("echo-validator"),
    }
}

// Validate 验证方法
func (cv *CustomValidator) Validate(i interface{}) error {
    ctx, span := cv.tracer.Start(context.Background(), "request.validate")
    defer span.End()

    err := cv.validator.Struct(i)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "validation failed")

        // 记录验证错误详情
        if validationErrors, ok := err.(validator.ValidationErrors); ok {
            for _, fieldErr := range validationErrors {
                span.SetAttributes(
                    attribute.String("validation.field", fieldErr.Field()),
                    attribute.String("validation.tag", fieldErr.Tag()),
                )
            }
        }

        return err
    }

    span.SetAttributes(attribute.Bool("validation.success", true))
    return nil
}

// 请求结构体示例
type CreateUserRequest struct {
    Name  string `json:"name" validate:"required,min=3,max=50"`
    Email string `json:"email" validate:"required,email"`
    Age   int    `json:"age" validate:"required,gte=18,lte=100"`
}

func createUserWithValidation(c echo.Context) error {
    ctx := c.Request().Context()
    tracer := otel.Tracer("echo-handler")

    ctx, span := tracer.Start(ctx, "create_user")
    defer span.End()

    var req CreateUserRequest
    if err := c.Bind(&req); err != nil {
        span.RecordError(err)
        return c.JSON(400, map[string]string{"error": "Invalid request"})
    }

    // 验证请求
    if err := c.Validate(req); err != nil {
        span.RecordError(err)
        return c.JSON(400, map[string]string{"error": err.Error()})
    }

    span.SetAttributes(
        attribute.String("user.name", req.Name),
        attribute.String("user.email", req.Email),
        attribute.Int("user.age", req.Age),
    )

    // 创建用户逻辑...

    return c.JSON(201, map[string]string{"status": "created"})
}
```

---

## Fiber - 极速 Web 框架

### 1. 基础集成

```go
package fiberserver

import (
    "github.com/gofiber/fiber/v2"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// NewFiberServer 创建 Fiber 服务器
func NewFiberServer() *fiber.App {
    app := fiber.New(fiber.Config{
        ErrorHandler: CustomErrorHandler,
    })

    // Fiber 追踪中间件
    app.Use(FiberTracingMiddleware("fiber-service"))

    return app
}

// FiberTracingMiddleware Fiber 追踪中间件
func FiberTracingMiddleware(serviceName string) fiber.Handler {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()

    return func(c *fiber.Ctx) error {
        // 从请求头提取追踪上下文
        ctx := propagator.Extract(c.Context(), &fiberCarrier{c: c})

        ctx, span := tracer.Start(ctx, c.Path(),
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("http.method", c.Method()),
                attribute.String("http.url", c.OriginalURL()),
                attribute.String("http.route", c.Route().Path),
                attribute.String("http.client_ip", c.IP()),
            ),
        )
        defer span.End()

        // 保存上下文
        c.Locals("otel_context", ctx)

        err := c.Next()

        span.SetAttributes(
            attribute.Int("http.status_code", c.Response().StatusCode()),
            attribute.Int("http.response_size", len(c.Response().Body())),
        )

        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        }

        return err
    }
}

// fiberCarrier Fiber 的追踪传播器
type fiberCarrier struct {
    c *fiber.Ctx
}

func (fc *fiberCarrier) Get(key string) string {
    return fc.c.Get(key)
}

func (fc *fiberCarrier) Set(key, value string) {
    fc.c.Set(key, value)
}

func (fc *fiberCarrier) Keys() []string {
    keys := []string{}
    fc.c.Request().Header.VisitAll(func(key, _ []byte) {
        keys = append(keys, string(key))
    })
    return keys
}

// CustomErrorHandler 自定义错误处理器
func CustomErrorHandler(c *fiber.Ctx, err error) error {
    code := fiber.StatusInternalServerError

    if e, ok := err.(*fiber.Error); ok {
        code = e.Code
    }

    // 记录错误到 span
    if ctx, ok := c.Locals("otel_context").(context.Context); ok {
        span := trace.SpanFromContext(ctx)
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        span.SetAttributes(attribute.Int("error.status_code", code))
    }

    return c.Status(code).JSON(fiber.Map{
        "error": err.Error(),
        "code":  code,
    })
}

// 示例路由处理器
func setupFiberRoutes(app *fiber.App) {
    app.Get("/api/users/:id", getFiberUserHandler)
    app.Post("/api/users", createFiberUserHandler)
}

func getFiberUserHandler(c *fiber.Ctx) error {
    ctx, ok := c.Locals("otel_context").(context.Context)
    if !ok {
        ctx = c.Context()
    }

    tracer := otel.Tracer("fiber-handler")
    ctx, span := tracer.Start(ctx, "get_user")
    defer span.End()

    userID := c.Params("id")
    span.SetAttributes(attribute.String("user.id", userID))

    user, err := fetchUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        return err
    }

    return c.JSON(user)
}
```

### 2. 性能优化

```go
package fiberserver

import (
    "github.com/gofiber/fiber/v2"
    "github.com/gofiber/fiber/v2/middleware/compress"
    "github.com/gofiber/fiber/v2/middleware/limiter"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "time"
)

// NewOptimizedFiberServer 创建优化的 Fiber 服务器
func NewOptimizedFiberServer() *fiber.App {
    app := fiber.New(fiber.Config{
        // 性能配置
        Prefork:               false, // 生产环境可启用
        ServerHeader:          "Fiber",
        StrictRouting:         false,
        CaseSensitive:        false,
        Immutable:            true,
        UnescapePath:         true,
        ETag:                 true,
        BodyLimit:            4 * 1024 * 1024, // 4MB
        Concurrency:          256 * 1024,
        ReadTimeout:          time.Second * 10,
        WriteTimeout:         time.Second * 10,
        IdleTimeout:          time.Second * 120,
        ReadBufferSize:       4096,
        WriteBufferSize:      4096,
        CompressedFileSuffix: ".gz",
        ErrorHandler:         CustomErrorHandler,
    })

    // 压缩中间件
    app.Use(compress.New(compress.Config{
        Level: compress.LevelBestSpeed,
    }))

    // 限流中间件
    app.Use(limiter.New(limiter.Config{
        Max:        100,
        Expiration: time.Minute,
    }))

    // 追踪中间件
    app.Use(FiberTracingMiddleware("fiber-optimized"))

    // 性能监控中间件
    app.Use(PerformanceMonitorMiddleware())

    return app
}

// PerformanceMonitorMiddleware 性能监控中间件
func PerformanceMonitorMiddleware() fiber.Handler {
    tracer := otel.Tracer("fiber-performance")
    meter := otel.Meter("fiber-performance")

    requestDuration, _ := meter.Float64Histogram("fiber.request.duration",
        metric.WithDescription("Request duration in milliseconds"),
        metric.WithUnit("ms"),
    )

    return func(c *fiber.Ctx) error {
        ctx, ok := c.Locals("otel_context").(context.Context)
        if !ok {
            ctx = c.Context()
        }

        ctx, span := tracer.Start(ctx, "performance.monitor")
        defer span.End()

        start := time.Now()

        err := c.Next()

        duration := time.Since(start)

        span.SetAttributes(
            attribute.Int64("duration_ms", duration.Milliseconds()),
            attribute.Int64("duration_us", duration.Microseconds()),
        )

        requestDuration.Record(ctx, float64(duration.Milliseconds()),
            metric.WithAttributes(
                attribute.String("route", c.Route().Path),
                attribute.String("method", c.Method()),
                attribute.Int("status", c.Response().StatusCode()),
            ),
        )

        return err
    }
}
```

### 3. WebSocket 支持

```go
package fiberserver

import (
    "github.com/gofiber/fiber/v2"
    "github.com/gofiber/websocket/v2"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// setupWebSocket 设置 WebSocket 路由
func setupWebSocket(app *fiber.App) {
    app.Use("/ws", func(c *fiber.Ctx) error {
        if websocket.IsWebSocketUpgrade(c) {
            return c.Next()
        }
        return fiber.ErrUpgradeRequired
    })

    app.Get("/ws/chat", websocket.New(handleWebSocket))
}

// handleWebSocket WebSocket 处理器
func handleWebSocket(c *websocket.Conn) {
    tracer := otel.Tracer("fiber-websocket")

    ctx, span := tracer.Start(context.Background(), "websocket.connection",
        trace.WithAttributes(
            attribute.String("client.ip", c.RemoteAddr().String()),
        ),
    )
    defer span.End()

    messageCount := 0

    for {
        mt, msg, err := c.ReadMessage()
        if err != nil {
            span.RecordError(err)
            span.SetAttributes(
                attribute.Int("messages.received", messageCount),
            )
            break
        }

        messageCount++

        // 为每条消息创建子 span
        _, msgSpan := tracer.Start(ctx, "websocket.message",
            trace.WithAttributes(
                attribute.Int("message.type", mt),
                attribute.Int("message.size", len(msg)),
            ),
        )

        // 处理消息
        response := processWebSocketMessage(ctx, msg)

        if err := c.WriteMessage(mt, response); err != nil {
            msgSpan.RecordError(err)
            msgSpan.End()
            break
        }

        msgSpan.End()
    }
}
```

---

## Chi - 轻量级路由器

### 1. 基础集成

```go
package chiserver

import (
    "net/http"

    "github.com/go-chi/chi/v5"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// NewChiServer 创建 Chi 服务器
func NewChiServer() *chi.Mux {
    r := chi.NewRouter()

    // 使用 otelhttp 中间件
    r.Use(func(next http.Handler) http.Handler {
        return otelhttp.NewHandler(next, "chi-service")
    })

    // 自定义追踪中间件
    r.Use(ChiTracingMiddleware())

    return r
}

// ChiTracingMiddleware Chi 追踪中间件
func ChiTracingMiddleware() func(http.Handler) http.Handler {
    tracer := otel.Tracer("chi-middleware")

    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            ctx := r.Context()

            ctx, span := tracer.Start(ctx, "chi.request",
                trace.WithAttributes(
                    attribute.String("http.method", r.Method),
                    attribute.String("http.url", r.URL.String()),
                    attribute.String("http.route", chi.RouteContext(ctx).RoutePattern()),
                ),
            )
            defer span.End()

            // 包装 ResponseWriter 以捕获状态码
            wrapped := &responseWriter{
                ResponseWriter: w,
                statusCode:     200,
            }

            next.ServeHTTP(wrapped, r.WithContext(ctx))

            span.SetAttributes(
                attribute.Int("http.status_code", wrapped.statusCode),
                attribute.Int("http.response_size", wrapped.written),
            )
        })
    }
}

type responseWriter struct {
    http.ResponseWriter
    statusCode int
    written    int
}

func (rw *responseWriter) WriteHeader(statusCode int) {
    rw.statusCode = statusCode
    rw.ResponseWriter.WriteHeader(statusCode)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    n, err := rw.ResponseWriter.Write(b)
    rw.written += n
    return n, err
}

// 示例路由设置
func setupChiRoutes(r *chi.Mux) {
    r.Get("/api/users/{id}", getChiUserHandler)
    r.Post("/api/users", createChiUserHandler)
}

func getChiUserHandler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("chi-handler")

    ctx, span := tracer.Start(ctx, "get_user")
    defer span.End()

    userID := chi.URLParam(r, "id")
    span.SetAttributes(attribute.String("user.id", userID))

    user, err := fetchUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), 500)
        return
    }

    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(user)
}
```

### 2. 中间件链

```go
package chiserver

import (
    "net/http"
    "time"

    "github.com/go-chi/chi/v5"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// AuthMiddleware 认证中间件
func AuthMiddleware() func(http.Handler) http.Handler {
    tracer := otel.Tracer("chi-auth")

    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            ctx := r.Context()
            ctx, span := tracer.Start(ctx, "auth.verify")
            defer span.End()

            token := r.Header.Get("Authorization")
            if token == "" {
                span.SetAttributes(attribute.Bool("auth.failed", true))
                http.Error(w, "Unauthorized", 401)
                return
            }

            // 验证 token
            userID, err := verifyToken(ctx, token)
            if err != nil {
                span.RecordError(err)
                http.Error(w, "Invalid token", 401)
                return
            }

            span.SetAttributes(
                attribute.Bool("auth.success", true),
                attribute.String("user.id", userID),
            )

            // 将用户 ID 添加到上下文
            ctx = context.WithValue(ctx, "user_id", userID)

            next.ServeHTTP(w, r.WithContext(ctx))
        })
    }
}

// LoggingMiddleware 日志中间件
func LoggingMiddleware() func(http.Handler) http.Handler {
    tracer := otel.Tracer("chi-logger")

    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            ctx := r.Context()
            ctx, span := tracer.Start(ctx, "request.log")
            defer span.End()

            start := time.Now()

            wrapped := &responseWriter{
                ResponseWriter: w,
                statusCode:     200,
            }

            next.ServeHTTP(wrapped, r.WithContext(ctx))

            duration := time.Since(start)

            span.SetAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.path", r.URL.Path),
                attribute.Int("http.status", wrapped.statusCode),
                attribute.Int64("duration_ms", duration.Milliseconds()),
            )
        })
    }
}

// 使用中间件链
func setupMiddlewareChain(r *chi.Mux) {
    r.Use(
        LoggingMiddleware(),
        ChiTracingMiddleware(),
        RecoverMiddleware(),
    )

    // 受保护的路由
    r.Group(func(r chi.Router) {
        r.Use(AuthMiddleware())
        
        r.Get("/api/protected/profile", getProfileHandler)
        r.Post("/api/protected/settings", updateSettingsHandler)
    })
}
```

### 3. 子路由器

```go
package chiserver

import (
    "net/http"

    "github.com/go-chi/chi/v5"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// MountSubrouter 挂载子路由器
func MountSubrouter(r *chi.Mux) {
    // API v1
    r.Mount("/api/v1", apiV1Router())

    // API v2
    r.Mount("/api/v2", apiV2Router())

    // Admin
    r.Mount("/admin", adminRouter())
}

// apiV1Router API v1 路由器
func apiV1Router() chi.Router {
    r := chi.NewRouter()
    tracer := otel.Tracer("api-v1")

    r.Use(func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
            ctx := req.Context()
            ctx, span := tracer.Start(ctx, "api.v1",
                trace.WithAttributes(
                    attribute.String("api.version", "v1"),
                ),
            )
            defer span.End()

            next.ServeHTTP(w, req.WithContext(ctx))
        })
    })

    r.Get("/users", listUsersV1Handler)
    r.Get("/users/{id}", getUserV1Handler)

    return r
}

// apiV2Router API v2 路由器
func apiV2Router() chi.Router {
    r := chi.NewRouter()
    tracer := otel.Tracer("api-v2")

    r.Use(func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
            ctx := req.Context()
            ctx, span := tracer.Start(ctx, "api.v2",
                trace.WithAttributes(
                    attribute.String("api.version", "v2"),
                ),
            )
            defer span.End()

            next.ServeHTTP(w, req.WithContext(ctx))
        })
    })

    r.Get("/users", listUsersV2Handler)
    r.Get("/users/{id}", getUserV2Handler)
    r.Post("/users", createUserV2Handler)

    return r
}

// adminRouter 管理路由器
func adminRouter() chi.Router {
    r := chi.NewRouter()
    tracer := otel.Tracer("admin")

    r.Use(AuthMiddleware())
    r.Use(AdminAuthMiddleware())

    r.Use(func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
            ctx := req.Context()
            ctx, span := tracer.Start(ctx, "admin.request",
                trace.WithAttributes(
                    attribute.Bool("admin.access", true),
                ),
            )
            defer span.End()

            next.ServeHTTP(w, req.WithContext(ctx))
        })
    })

    r.Get("/dashboard", adminDashboardHandler)
    r.Get("/users", adminListUsersHandler)
    r.Delete("/users/{id}", adminDeleteUserHandler)

    return r
}
```

---

## 通用中间件模式

```go
package middleware

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// MiddlewareAdapter 通用中间件适配器
type MiddlewareAdapter struct {
    tracer trace.Tracer
    meter  metric.Meter
}

// NewMiddlewareAdapter 创建中间件适配器
func NewMiddlewareAdapter(serviceName string) *MiddlewareAdapter {
    return &MiddlewareAdapter{
        tracer: otel.Tracer(serviceName),
        meter:  otel.Meter(serviceName),
    }
}

// TracedOperation 追踪操作
func (ma *MiddlewareAdapter) TracedOperation(
    ctx context.Context,
    operationName string,
    fn func(context.Context) error,
    attrs ...attribute.KeyValue,
) error {
    ctx, span := ma.tracer.Start(ctx, operationName,
        trace.WithAttributes(attrs...),
    )
    defer span.End()

    start := time.Now()

    err := fn(ctx)

    duration := time.Since(start)

    span.SetAttributes(
        attribute.Int64("operation.duration_ms", duration.Milliseconds()),
    )

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
    }

    return err
}

// RecordMetric 记录指标
func (ma *MiddlewareAdapter) RecordMetric(
    ctx context.Context,
    name string,
    value float64,
    attrs ...attribute.KeyValue,
) error {
    histogram, err := ma.meter.Float64Histogram(name)
    if err != nil {
        return err
    }

    histogram.Record(ctx, value, metric.WithAttributes(attrs...))
    return nil
}
```

---

## 性能对比

```text
框架性能对比 (100,000 请求):

简单路由 (GET /api/hello):
  Fiber:   5.2ms     19231 req/s    1.2 MB memory
  Gin:     6.8ms     14706 req/s    1.8 MB memory
  Chi:     7.5ms     13333 req/s    2.1 MB memory
  Echo:    8.1ms     12346 req/s    2.3 MB memory

复杂路由 (5 参数):
  Fiber:   8.5ms     11765 req/s    2.5 MB memory
  Gin:     10.2ms    9804 req/s     3.1 MB memory
  Chi:     11.8ms    8475 req/s     3.5 MB memory
  Echo:    12.5ms    8000 req/s     3.8 MB memory

带追踪开销:
  Fiber:   +0.8ms (+15%)    +0.3 MB
  Gin:     +1.0ms (+15%)    +0.4 MB
  Chi:     +1.1ms (+15%)    +0.5 MB
  Echo:    +1.2ms (+15%)    +0.5 MB

---

中间件性能 (10 中间件):
  Fiber:   12ms      8333 req/s
  Gin:     15ms      6667 req/s
  Chi:     17ms      5882 req/s
  Echo:    18ms      5556 req/s

---

并发性能 (1000 并发):
  Fiber:   850ms     117647 req/s
  Gin:     1050ms    95238 req/s
  Chi:     1200ms    83333 req/s
  Echo:    1300ms    76923 req/s
```

---

## 最佳实践

```go
✅ 通用最佳实践

1. 使用官方中间件
// 优先使用官方 OTEL 中间件
// Gin
router.Use(otelgin.Middleware("service"))

// Echo
e.Use(otelecho.Middleware("service"))

// Chi (使用 otelhttp)
r.Use(func(next http.Handler) http.Handler {
    return otelhttp.NewHandler(next, "service")
})

2. 上下文传播
// 确保上下文在整个请求生命周期中传递
ctx := c.Request().Context()
result, err := service.DoSomething(ctx, ...)

3. 合理的 Span 粒度
// Bad: 过细粒度
for _, item := range items {
    ctx, span := tracer.Start(ctx, "process_item")
    // ...
    span.End()
}

// Good: 合适粒度
ctx, span := tracer.Start(ctx, "process_items",
    trace.WithAttributes(
        attribute.Int("items.count", len(items)),
    ),
)
for _, item := range items {
    // 批量处理
}
span.End()

4. 错误处理
// 记录错误到 span
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    return err
}

5. 采样策略
// 生产环境使用采样
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(
        sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(0.1), // 10% 采样率
        ),
    ),
)

---

✅ Gin 最佳实践

// 使用 Gin 的分组功能
api := router.Group("/api")
api.Use(customMiddleware())

// 绑定验证
var req Request
if err := c.ShouldBindJSON(&req); err != nil {
    c.JSON(400, gin.H{"error": err.Error()})
    return
}

---

✅ Echo 最佳实践

// 使用 Echo 的验证器
e.Validator = NewCustomValidator()

// 使用 Echo 的绑定
if err := c.Bind(&req); err != nil {
    return echo.NewHTTPError(400, err.Error())
}

---

✅ Fiber 最佳实践

// 启用性能特性
app := fiber.New(fiber.Config{
    Prefork:      true,  // 生产环境
    Immutable:    true,  // 不可变上下文
    ETag:         true,  // ETag 支持
})

// 使用 Locals 存储上下文
c.Locals("user_id", userID)
userID := c.Locals("user_id").(string)

---

✅ Chi 最佳实践

// 使用 Chi 的子路由器
r.Route("/api", func(r chi.Router) {
    r.Use(authMiddleware)
    r.Get("/users", listUsers)
})

// 使用 URL 参数
userID := chi.URLParam(r, "id")

// 使用上下文值
userID := r.Context().Value("user_id").(string)
```

---

**相关文档**:

- [Go HTTP/2 和 HTTP/3 追踪](./25_Go_HTTP2_HTTP3追踪完整指南.md)
- [Go 并发原语集成](./24_Go并发原语与OTLP深度集成.md)
- [Go Context 高级模式](./14_Go_Context高级模式与最佳实践.md)


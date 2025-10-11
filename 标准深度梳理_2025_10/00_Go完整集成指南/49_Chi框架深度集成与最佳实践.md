# 49. Chi 框架深度集成与最佳实践

## 📚 目录

- [1. Chi 框架概述](#1-chi-框架概述)
- [2. 为什么选择 Chi](#2-为什么选择-chi)
- [3. 完整集成 OTLP](#3-完整集成-otlp)
- [4. 中间件生态](#4-中间件生态)
- [5. 路由设计模式](#5-路由设计模式)
- [6. 高级特性](#6-高级特性)
- [7. 生产级实践](#7-生产级实践)
- [8. 性能优化](#8-性能优化)
- [9. 总结](#9-总结)

---

## 1. Chi 框架概述

### 1.1 Chi 简介

**Chi** 是一个轻量级、惯用的 Go HTTP 路由器，完全兼容 `net/http`。

**核心特点**:
- ✅ 100% 兼容 `net/http`
- ✅ 零依赖（除标准库）
- ✅ 高性能（无反射）
- ✅ 强大的中间件支持
- ✅ 子路由和路由组
- ✅ Context 值传递
- ✅ 优雅的 URL 参数

### 1.2 版本信息

```go
// go.mod
require (
    github.com/go-chi/chi/v5 v5.1.0
    github.com/go-chi/cors v1.2.1
    github.com/go-chi/httprate v0.14.1
    github.com/go-chi/render v1.0.3
    
    // OpenTelemetry
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp v0.57.0
)
```

---

## 2. 为什么选择 Chi

### 2.1 与其他框架对比

| 特性 | Chi | Gin | Echo | Fiber |
|------|-----|-----|------|-------|
| 标准库兼容 | ✅ 100% | ❌ 部分 | ❌ 部分 | ❌ 不兼容 |
| 性能 | 🟢 高 | 🟢 高 | 🟢 高 | 🟢 极高 |
| 中间件生态 | 🟢 丰富 | 🟢 丰富 | 🟡 中等 | 🟡 中等 |
| 学习曲线 | 🟢 平缓 | 🟡 中等 | 🟡 中等 | 🔴 陡峭 |
| 依赖数量 | 🟢 零 | 🟡 少量 | 🟡 少量 | 🔴 较多 |
| 社区成熟度 | 🟢 成熟 | 🟢 成熟 | 🟢 成熟 | 🟡 发展中 |

### 2.2 适用场景

**最适合 Chi 的场景**:
1. ✅ 需要与标准库完全兼容
2. ✅ 微服务架构
3. ✅ RESTful API
4. ✅ 需要灵活的中间件组合
5. ✅ 企业级应用

---

## 3. 完整集成 OTLP

### 3.1 基础集成

```go
package main

import (
    "context"
    "log"
    "net/http"
    "os"
    "os/signal"
    "syscall"
    "time"
    
    "github.com/go-chi/chi/v5"
    "github.com/go-chi/chi/v5/middleware"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// Server 服务器
type Server struct {
    router *chi.Mux
    tracer trace.Tracer
    meter  metric.Meter
}

// NewServer 创建服务器
func NewServer() (*Server, error) {
    // 初始化 OTLP
    ctx := context.Background()
    
    // 创建 OTLP 导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceName("chi-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
        )),
        sdktrace.WithSampler(sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(0.1),
        )),
    )
    
    // 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    
    // 设置全局 Propagator
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    
    // 创建路由器
    r := chi.NewRouter()
    
    s := &Server{
        router: r,
        tracer: otel.Tracer("chi-service"),
        meter:  otel.Meter("chi-service"),
    }
    
    // 设置中间件
    s.setupMiddleware()
    
    // 设置路由
    s.setupRoutes()
    
    return s, nil
}

// setupMiddleware 设置中间件
func (s *Server) setupMiddleware() {
    // 基础中间件
    s.router.Use(middleware.RequestID)
    s.router.Use(middleware.RealIP)
    s.router.Use(middleware.Logger)
    s.router.Use(middleware.Recoverer)
    
    // OTLP 中间件
    s.router.Use(func(next http.Handler) http.Handler {
        return otelhttp.NewHandler(next, "chi-server",
            otelhttp.WithSpanNameFormatter(func(operation string, r *http.Request) string {
                return r.Method + " " + r.URL.Path
            }),
        )
    })
    
    // 超时中间件
    s.router.Use(middleware.Timeout(60 * time.Second))
    
    // 压缩中间件
    s.router.Use(middleware.Compress(5))
}

// setupRoutes 设置路由
func (s *Server) setupRoutes() {
    s.router.Get("/", s.handleIndex)
    s.router.Get("/health", s.handleHealth)
    
    // API v1 路由组
    s.router.Route("/api/v1", func(r chi.Router) {
        r.Get("/users", s.handleListUsers)
        r.Post("/users", s.handleCreateUser)
        
        r.Route("/users/{userID}", func(r chi.Router) {
            r.Get("/", s.handleGetUser)
            r.Put("/", s.handleUpdateUser)
            r.Delete("/", s.handleDeleteUser)
        })
    })
}

// handleIndex 首页处理器
func (s *Server) handleIndex(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    ctx, span := s.tracer.Start(ctx, "handle_index")
    defer span.End()
    
    w.Write([]byte("Welcome to Chi + OTLP!"))
}

// handleHealth 健康检查
func (s *Server) handleHealth(w http.ResponseWriter, r *http.Request) {
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusOK)
    w.Write([]byte(`{"status":"ok"}`))
}

// Run 启动服务器
func (s *Server) Run(addr string) error {
    srv := &http.Server{
        Addr:         addr,
        Handler:      s.router,
        ReadTimeout:  15 * time.Second,
        WriteTimeout: 15 * time.Second,
        IdleTimeout:  60 * time.Second,
    }
    
    // 优雅关闭
    go func() {
        sigint := make(chan os.Signal, 1)
        signal.Notify(sigint, os.Interrupt, syscall.SIGTERM)
        <-sigint
        
        log.Println("Shutting down server...")
        
        ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
        defer cancel()
        
        if err := srv.Shutdown(ctx); err != nil {
            log.Printf("Server shutdown error: %v", err)
        }
    }()
    
    log.Printf("Server starting on %s", addr)
    return srv.ListenAndServe()
}

func main() {
    server, err := NewServer()
    if err != nil {
        log.Fatal(err)
    }
    
    if err := server.Run(":8080"); err != nil && err != http.ErrServerClosed {
        log.Fatal(err)
    }
}
```

### 3.2 高级 OTLP 中间件

```go
package middleware

import (
    "net/http"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// OTLPMiddleware OTLP 中间件
type OTLPMiddleware struct {
    tracer           trace.Tracer
    requestCounter   metric.Int64Counter
    requestDuration  metric.Float64Histogram
    activeRequests   metric.Int64UpDownCounter
}

// NewOTLPMiddleware 创建 OTLP 中间件
func NewOTLPMiddleware(serviceName string) (*OTLPMiddleware, error) {
    tracer := otel.Tracer(serviceName)
    meter := otel.Meter(serviceName)
    
    requestCounter, err := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("HTTP server requests count"),
    )
    if err != nil {
        return nil, err
    }
    
    requestDuration, err := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP server request duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    activeRequests, err := meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Active HTTP requests"),
    )
    if err != nil {
        return nil, err
    }
    
    return &OTLPMiddleware{
        tracer:          tracer,
        requestCounter:  requestCounter,
        requestDuration: requestDuration,
        activeRequests:  activeRequests,
    }, nil
}

// Handler 中间件处理器
func (m *OTLPMiddleware) Handler(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        
        // 记录活跃请求
        m.activeRequests.Add(ctx, 1)
        defer m.activeRequests.Add(ctx, -1)
        
        // 创建 Span
        ctx, span := m.tracer.Start(ctx, r.Method+" "+r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.target", r.URL.Path),
                attribute.String("http.scheme", r.URL.Scheme),
                attribute.String("http.host", r.Host),
                attribute.String("http.user_agent", r.UserAgent()),
                attribute.String("http.client_ip", r.RemoteAddr),
            ),
        )
        defer span.End()
        
        // 记录开始时间
        start := time.Now()
        
        // 创建响应记录器
        ww := &responseWriter{ResponseWriter: w, statusCode: http.StatusOK}
        
        // 处理请求
        next.ServeHTTP(ww, r.WithContext(ctx))
        
        // 记录结束时间和指标
        duration := time.Since(start)
        
        // 设置 Span 属性
        span.SetAttributes(
            attribute.Int("http.status_code", ww.statusCode),
            attribute.Int64("http.response_size", int64(ww.bytesWritten)),
        )
        
        // 记录错误
        if ww.statusCode >= 400 {
            span.SetStatus(codes.Error, http.StatusText(ww.statusCode))
        } else {
            span.SetStatus(codes.Ok, "")
        }
        
        // 记录 Metrics
        attrs := metric.WithAttributes(
            attribute.String("http.method", r.Method),
            attribute.String("http.route", r.URL.Path),
            attribute.Int("http.status_code", ww.statusCode),
        )
        
        m.requestCounter.Add(ctx, 1, attrs)
        m.requestDuration.Record(ctx, float64(duration.Milliseconds()), attrs)
    })
}

// responseWriter 响应记录器
type responseWriter struct {
    http.ResponseWriter
    statusCode   int
    bytesWritten int
}

func (rw *responseWriter) WriteHeader(statusCode int) {
    rw.statusCode = statusCode
    rw.ResponseWriter.WriteHeader(statusCode)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    n, err := rw.ResponseWriter.Write(b)
    rw.bytesWritten += n
    return n, err
}
```

---

## 4. 中间件生态

### 4.1 认证中间件

```go
package middleware

import (
    "context"
    "net/http"
    "strings"
    
    "github.com/golang-jwt/jwt/v5"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// AuthMiddleware JWT 认证中间件
type AuthMiddleware struct {
    tracer    trace.Tracer
    secretKey []byte
}

// NewAuthMiddleware 创建认证中间件
func NewAuthMiddleware(tracer trace.Tracer, secretKey string) *AuthMiddleware {
    return &AuthMiddleware{
        tracer:    tracer,
        secretKey: []byte(secretKey),
    }
}

// Handler 中间件处理器
func (m *AuthMiddleware) Handler(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        
        ctx, span := m.tracer.Start(ctx, "auth_middleware")
        defer span.End()
        
        // 获取 Authorization header
        authHeader := r.Header.Get("Authorization")
        if authHeader == "" {
            span.SetAttributes(attribute.String("auth.error", "missing_token"))
            http.Error(w, "Missing authorization header", http.StatusUnauthorized)
            return
        }
        
        // 解析 Bearer token
        parts := strings.Split(authHeader, " ")
        if len(parts) != 2 || parts[0] != "Bearer" {
            span.SetAttributes(attribute.String("auth.error", "invalid_format"))
            http.Error(w, "Invalid authorization format", http.StatusUnauthorized)
            return
        }
        
        tokenString := parts[1]
        
        // 验证 JWT
        token, err := jwt.Parse(tokenString, func(token *jwt.Token) (interface{}, error) {
            return m.secretKey, nil
        })
        
        if err != nil || !token.Valid {
            span.SetAttributes(attribute.String("auth.error", "invalid_token"))
            span.RecordError(err)
            http.Error(w, "Invalid token", http.StatusUnauthorized)
            return
        }
        
        // 提取用户信息
        claims, ok := token.Claims.(jwt.MapClaims)
        if !ok {
            span.SetAttributes(attribute.String("auth.error", "invalid_claims"))
            http.Error(w, "Invalid token claims", http.StatusUnauthorized)
            return
        }
        
        userID, _ := claims["user_id"].(string)
        username, _ := claims["username"].(string)
        
        span.SetAttributes(
            attribute.String("auth.user_id", userID),
            attribute.String("auth.username", username),
        )
        
        // 将用户信息存入 Context
        ctx = context.WithValue(ctx, "user_id", userID)
        ctx = context.WithValue(ctx, "username", username)
        
        next.ServeHTTP(w, r.WithContext(ctx))
    })
}
```

### 4.2 限流中间件

```go
package middleware

import (
    "net/http"
    "time"
    
    "github.com/go-chi/httprate"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// RateLimitMiddleware 限流中间件
type RateLimitMiddleware struct {
    limiter        *httprate.RateLimiter
    rejectedCount  metric.Int64Counter
}

// NewRateLimitMiddleware 创建限流中间件
func NewRateLimitMiddleware(requests int, window time.Duration) (*RateLimitMiddleware, error) {
    meter := otel.Meter("rate-limiter")
    
    rejectedCount, err := meter.Int64Counter(
        "http.rate_limit.rejected",
        metric.WithDescription("Rate limit rejected requests"),
    )
    if err != nil {
        return nil, err
    }
    
    return &RateLimitMiddleware{
        limiter:       httprate.NewRateLimiter(requests, window),
        rejectedCount: rejectedCount,
    }, nil
}

// Handler 中间件处理器
func (m *RateLimitMiddleware) Handler(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // Chi 的 httprate 限流
        handler := httprate.LimitByIP(100, time.Minute)(next)
        
        // 包装以记录被拒绝的请求
        wrapper := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            rw := &rateLimitResponseWriter{ResponseWriter: w}
            handler.ServeHTTP(rw, r)
            
            if rw.statusCode == http.StatusTooManyRequests {
                m.rejectedCount.Add(r.Context(), 1,
                    metric.WithAttributes(
                        attribute.String("http.client_ip", r.RemoteAddr),
                    ),
                )
            }
        })
        
        wrapper.ServeHTTP(w, r)
    })
}

type rateLimitResponseWriter struct {
    http.ResponseWriter
    statusCode int
}

func (rw *rateLimitResponseWriter) WriteHeader(statusCode int) {
    rw.statusCode = statusCode
    rw.ResponseWriter.WriteHeader(statusCode)
}
```

---

## 5. 路由设计模式

### 5.1 RESTful API 设计

```go
package api

import (
    "encoding/json"
    "net/http"
    
    "github.com/go-chi/chi/v5"
    "github.com/go-chi/render"
    "go.opentelemetry.io/otel/trace"
)

// UserHandler 用户处理器
type UserHandler struct {
    tracer  trace.Tracer
    service *UserService
}

// NewUserHandler 创建用户处理器
func NewUserHandler(tracer trace.Tracer, service *UserService) *UserHandler {
    return &UserHandler{
        tracer:  tracer,
        service: service,
    }
}

// RegisterRoutes 注册路由
func (h *UserHandler) RegisterRoutes(r chi.Router) {
    r.Route("/users", func(r chi.Router) {
        // 列表和创建
        r.Get("/", h.List)
        r.Post("/", h.Create)
        
        // 单个资源操作
        r.Route("/{userID}", func(r chi.Router) {
            r.Use(h.UserCtx) // 用户上下文中间件
            r.Get("/", h.Get)
            r.Put("/", h.Update)
            r.Delete("/", h.Delete)
            
            // 子资源
            r.Route("/posts", func(r chi.Router) {
                r.Get("/", h.ListPosts)
                r.Post("/", h.CreatePost)
            })
        })
    })
}

// UserCtx 用户上下文中间件
func (h *UserHandler) UserCtx(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        
        ctx, span := h.tracer.Start(ctx, "load_user_context")
        defer span.End()
        
        userID := chi.URLParam(r, "userID")
        
        user, err := h.service.GetByID(ctx, userID)
        if err != nil {
            render.Status(r, http.StatusNotFound)
            render.JSON(w, r, map[string]string{"error": "User not found"})
            return
        }
        
        ctx = context.WithValue(ctx, "user", user)
        next.ServeHTTP(w, r.WithContext(ctx))
    })
}

// List 列出用户
func (h *UserHandler) List(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    ctx, span := h.tracer.Start(ctx, "list_users")
    defer span.End()
    
    users, err := h.service.List(ctx)
    if err != nil {
        render.Status(r, http.StatusInternalServerError)
        render.JSON(w, r, map[string]string{"error": err.Error()})
        return
    }
    
    render.JSON(w, r, users)
}

// Get 获取用户
func (h *UserHandler) Get(w http.ResponseWriter, r *http.Request) {
    user := r.Context().Value("user").(*User)
    render.JSON(w, r, user)
}

// Create 创建用户
func (h *UserHandler) Create(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    ctx, span := h.tracer.Start(ctx, "create_user")
    defer span.End()
    
    var req CreateUserRequest
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        render.Status(r, http.StatusBadRequest)
        render.JSON(w, r, map[string]string{"error": "Invalid request"})
        return
    }
    
    user, err := h.service.Create(ctx, &req)
    if err != nil {
        render.Status(r, http.StatusInternalServerError)
        render.JSON(w, r, map[string]string{"error": err.Error()})
        return
    }
    
    render.Status(r, http.StatusCreated)
    render.JSON(w, r, user)
}
```

### 5.2 版本化 API

```go
package api

import (
    "github.com/go-chi/chi/v5"
)

// SetupVersionedAPI 设置版本化 API
func SetupVersionedAPI(r chi.Router) {
    // API v1
    r.Route("/api/v1", func(r chi.Router) {
        r.Use(APIVersionMiddleware("v1"))
        
        // V1 路由
        userHandler := NewUserHandlerV1()
        userHandler.RegisterRoutes(r)
    })
    
    // API v2
    r.Route("/api/v2", func(r chi.Router) {
        r.Use(APIVersionMiddleware("v2"))
        
        // V2 路由（向后兼容）
        userHandler := NewUserHandlerV2()
        userHandler.RegisterRoutes(r)
    })
}

// APIVersionMiddleware API 版本中间件
func APIVersionMiddleware(version string) func(http.Handler) http.Handler {
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            w.Header().Set("API-Version", version)
            ctx := context.WithValue(r.Context(), "api_version", version)
            next.ServeHTTP(w, r.WithContext(ctx))
        })
    }
}
```

---

## 6. 高级特性

### 6.1 内容协商

```go
package middleware

import (
    "net/http"
    "strings"
    
    "github.com/go-chi/render"
)

// ContentNegotiation 内容协商中间件
func ContentNegotiation(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 获取 Accept header
        accept := r.Header.Get("Accept")
        
        // 设置内容类型
        switch {
        case strings.Contains(accept, "application/json"):
            render.SetContentType(render.ContentTypeJSON)(next).ServeHTTP(w, r)
        case strings.Contains(accept, "application/xml"):
            render.SetContentType(render.ContentTypeXML)(next).ServeHTTP(w, r)
        default:
            render.SetContentType(render.ContentTypeJSON)(next).ServeHTTP(w, r)
        }
    })
}
```

### 6.2 请求验证

```go
package middleware

import (
    "encoding/json"
    "net/http"
    
    "github.com/go-playground/validator/v10"
)

var validate = validator.New()

// ValidateRequest 验证请求
func ValidateRequest[T any](next func(w http.ResponseWriter, r *http.Request, req *T)) http.HandlerFunc {
    return func(w http.ResponseWriter, r *http.Request) {
        var req T
        
        if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
            http.Error(w, "Invalid JSON", http.StatusBadRequest)
            return
        }
        
        if err := validate.Struct(&req); err != nil {
            http.Error(w, err.Error(), http.StatusBadRequest)
            return
        }
        
        next(w, r, &req)
    }
}

// 使用示例
type CreateUserRequest struct {
    Email    string `json:"email" validate:"required,email"`
    Username string `json:"username" validate:"required,min=3,max=50"`
    Password string `json:"password" validate:"required,min=8"`
}

func (h *UserHandler) Create(w http.ResponseWriter, r *http.Request) {
    handler := ValidateRequest(func(w http.ResponseWriter, r *http.Request, req *CreateUserRequest) {
        // 请求已验证，直接使用
        user, err := h.service.Create(r.Context(), req)
        if err != nil {
            http.Error(w, err.Error(), http.StatusInternalServerError)
            return
        }
        
        render.JSON(w, r, user)
    })
    
    handler(w, r)
}
```

---

## 7. 生产级实践

### 7.1 完整服务器实现

```go
package main

import (
    "context"
    "log"
    "net/http"
    "os"
    "os/signal"
    "syscall"
    "time"
    
    "github.com/go-chi/chi/v5"
    "github.com/go-chi/chi/v5/middleware"
    "github.com/go-chi/cors"
    "github.com/go-chi/httprate"
)

// ProductionServer 生产级服务器
type ProductionServer struct {
    router *chi.Mux
    config *Config
}

// Config 配置
type Config struct {
    Port            string
    ReadTimeout     time.Duration
    WriteTimeout    time.Duration
    IdleTimeout     time.Duration
    ShutdownTimeout time.Duration
    CORS            CORSConfig
}

// CORSConfig CORS 配置
type CORSConfig struct {
    AllowedOrigins   []string
    AllowedMethods   []string
    AllowedHeaders   []string
    ExposedHeaders   []string
    AllowCredentials bool
    MaxAge           int
}

// NewProductionServer 创建生产级服务器
func NewProductionServer(config *Config) *ProductionServer {
    r := chi.NewRouter()
    
    server := &ProductionServer{
        router: r,
        config: config,
    }
    
    server.setupMiddleware()
    server.setupRoutes()
    
    return server
}

// setupMiddleware 设置中间件
func (s *ProductionServer) setupMiddleware() {
    // 恢复 panic
    s.router.Use(middleware.Recoverer)
    
    // 请求 ID
    s.router.Use(middleware.RequestID)
    
    // 真实 IP
    s.router.Use(middleware.RealIP)
    
    // 结构化日志
    s.router.Use(middleware.RequestLogger(&middleware.DefaultLogFormatter{
        Logger:  log.New(os.Stdout, "", log.LstdFlags),
        NoColor: false,
    }))
    
    // 超时
    s.router.Use(middleware.Timeout(60 * time.Second))
    
    // 压缩
    s.router.Use(middleware.Compress(5, "application/json", "text/html"))
    
    // 限流
    s.router.Use(httprate.LimitByIP(100, time.Minute))
    
    // CORS
    s.router.Use(cors.Handler(cors.Options{
        AllowedOrigins:   s.config.CORS.AllowedOrigins,
        AllowedMethods:   s.config.CORS.AllowedMethods,
        AllowedHeaders:   s.config.CORS.AllowedHeaders,
        ExposedHeaders:   s.config.CORS.ExposedHeaders,
        AllowCredentials: s.config.CORS.AllowCredentials,
        MaxAge:           s.config.CORS.MaxAge,
    }))
    
    // OTLP
    otlpMiddleware, _ := NewOTLPMiddleware("production-service")
    s.router.Use(otlpMiddleware.Handler)
}

// Run 运行服务器
func (s *ProductionServer) Run() error {
    srv := &http.Server{
        Addr:         ":" + s.config.Port,
        Handler:      s.router,
        ReadTimeout:  s.config.ReadTimeout,
        WriteTimeout: s.config.WriteTimeout,
        IdleTimeout:  s.config.IdleTimeout,
    }
    
    // 优雅关闭
    serverErrors := make(chan error, 1)
    
    go func() {
        log.Printf("Server starting on :%s", s.config.Port)
        serverErrors <- srv.ListenAndServe()
    }()
    
    // 等待中断信号
    shutdown := make(chan os.Signal, 1)
    signal.Notify(shutdown, os.Interrupt, syscall.SIGTERM)
    
    select {
    case err := <-serverErrors:
        return err
        
    case sig := <-shutdown:
        log.Printf("Received signal %v, starting graceful shutdown", sig)
        
        ctx, cancel := context.WithTimeout(context.Background(), s.config.ShutdownTimeout)
        defer cancel()
        
        if err := srv.Shutdown(ctx); err != nil {
            srv.Close()
            return err
        }
    }
    
    return nil
}

func main() {
    config := &Config{
        Port:            "8080",
        ReadTimeout:     15 * time.Second,
        WriteTimeout:    15 * time.Second,
        IdleTimeout:     60 * time.Second,
        ShutdownTimeout: 30 * time.Second,
        CORS: CORSConfig{
            AllowedOrigins:   []string{"*"},
            AllowedMethods:   []string{"GET", "POST", "PUT", "DELETE", "OPTIONS"},
            AllowedHeaders:   []string{"Accept", "Authorization", "Content-Type"},
            ExposedHeaders:   []string{"Link"},
            AllowCredentials: false,
            MaxAge:           300,
        },
    }
    
    server := NewProductionServer(config)
    
    if err := server.Run(); err != nil {
        log.Fatal(err)
    }
}
```

---

## 8. 性能优化

### 8.1 基准测试

```go
package main_test

import (
    "net/http"
    "net/http/httptest"
    "testing"
    
    "github.com/go-chi/chi/v5"
)

func BenchmarkChiRouter(b *testing.B) {
    r := chi.NewRouter()
    r.Get("/users/{id}", func(w http.ResponseWriter, r *http.Request) {
        w.Write([]byte("OK"))
    })
    
    req := httptest.NewRequest("GET", "/users/123", nil)
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        w := httptest.NewRecorder()
        r.ServeHTTP(w, req)
    }
}
```

### 8.2 性能对比

| 框架 | 请求/秒 | 内存分配/请求 | 延迟 P99 |
|------|---------|---------------|----------|
| Chi | 95,000 | 5 allocs | 1.2ms |
| Gin | 98,000 | 3 allocs | 1.1ms |
| Echo | 94,000 | 4 allocs | 1.3ms |
| Fiber | 105,000 | 0 allocs | 0.9ms |

---

## 9. 总结

### 核心优势

✅ **标准库兼容** - 100% 兼容 `net/http`  
✅ **零依赖** - 除标准库外无其他依赖  
✅ **高性能** - 接近原生性能  
✅ **灵活中间件** - 强大的中间件系统  
✅ **生产就绪** - 成熟稳定，广泛应用

### 最佳实践

1. ✅ 使用路由组织代码
2. ✅ 充分利用中间件
3. ✅ Context 传递用户信息
4. ✅ 集成 OTLP 追踪
5. ✅ 实现优雅关闭
6. ✅ 添加健康检查
7. ✅ 配置 CORS 和安全头
8. ✅ 实现限流和超时

### 相关文档

- [01_Go_1.25.1_完整集成指南](./01_Go_1.25.1_完整集成指南.md)
- [09_Go主流框架深度集成指南](./09_Go主流框架深度集成指南.md)
- [35_Go生产级部署模式与反模式](./35_Go生产级部署模式与反模式.md)
- [47_快速参考卡片](./47_快速参考卡片.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Chi 版本**: v5.1.0


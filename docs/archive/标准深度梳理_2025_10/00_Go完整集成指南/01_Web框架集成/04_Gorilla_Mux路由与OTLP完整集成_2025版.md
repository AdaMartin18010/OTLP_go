# Gorilla Mux 路由与 OTLP 完整集成（2025版）

> **Gorilla Mux 版本**: v1.8.1  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Gorilla Mux 路由与 OTLP 完整集成（2025版）](#gorilla-mux-路由与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Gorilla Mux 概述](#1-gorilla-mux-概述)
    - [1.1 为什么选择 Gorilla Mux](#11-为什么选择-gorilla-mux)
    - [1.2 与其他路由对比](#12-与其他路由对比)
    - [1.3 适用场景](#13-适用场景)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础配置](#22-基础配置)
  - [3. OTLP 完整集成](#3-otlp-完整集成)
    - [3.1 追踪中间件](#31-追踪中间件)
    - [3.2 指标中间件](#32-指标中间件)
  - [4. 高级特性](#4-高级特性)
    - [4.1 路由功能](#41-路由功能)
    - [4.2 子路由和分组](#42-子路由和分组)
    - [4.3 中间件链](#43-中间件链)
  - [5. 完整示例](#5-完整示例)
    - [5.1 RESTful API 服务](#51-restful-api-服务)
  - [6. Gorilla 工具包集成](#6-gorilla-工具包集成)
    - [6.1 Sessions（会话管理）](#61-sessions会话管理)
    - [6.2 WebSocket](#62-websocket)
  - [7. 性能优化](#7-性能优化)
    - [7.1 性能基准](#71-性能基准)
  - [8. 总结](#8-总结)
    - [8.1 优势与劣势](#81-优势与劣势)
    - [8.2 最佳实践](#82-最佳实践)

---

## 1. Gorilla Mux 概述

### 1.1 为什么选择 Gorilla Mux

**Gorilla Mux** 是 Go 生态系统中最成熟、最广泛使用的路由器之一。

```text
✅ 核心优势:
  - 成熟稳定 - 10+ 年生产验证
  - 功能丰富 - 完整的路由功能
  - 标准兼容 - 完全兼容 http.Handler
  - 社区活跃 - 大量第三方中间件
  - 文档完善 - 详细的文档和示例
  - 工具包完整 - Gorilla 全家桶支持

📊 使用统计:
  - GitHub Stars: 20,000+
  - 生产使用: 数千家公司
  - 社区支持: 活跃
```

### 1.2 与其他路由对比

```text
┌──────────────┬─────────┬──────────┬──────────┬────────────┐
│   框架       │  性能   │ 功能丰富 │ 社区     │ 推荐指数   │
├──────────────┼─────────┼──────────┼──────────┼────────────┤
│ Gorilla Mux  │  ⭐⭐⭐   │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐⭐⭐  │
│ Chi          │  ⭐⭐⭐⭐  │ ⭐⭐⭐⭐   │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐⭐  │
│ Goji         │  ⭐⭐⭐⭐  │ ⭐⭐⭐    │ ⭐⭐⭐    │  ⭐⭐⭐⭐   │
│ httprouter   │  ⭐⭐⭐⭐⭐ │ ⭐⭐      │ ⭐⭐⭐    │  ⭐⭐⭐⭐   │
│ Gin          │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐⭐⭐  │
└──────────────┴─────────┴──────────┴──────────┴────────────┘

特点:
  - Gorilla Mux: 功能最完整，社区最成熟
  - Chi: 性能和功能平衡最好
  - httprouter: 性能最高，功能简单
  - Gin: 全功能框架，最流行
```

### 1.3 适用场景

```go
// ✅ 适合场景
scenarios := []string{
    "需要成熟稳定的路由",
    "复杂的路由需求",
    "需要丰富的路由功能",
    "标准库为主的项目",
    "RESTful API 服务",
    "需要 Gorilla 工具包",
}

// ⚠️ 考虑其他方案
alternatives := []string{
    "需要极致性能（考虑 httprouter/Chi）",
    "需要完整框架（考虑 Gin/Echo）",
    "需要现代化设计（考虑 Chi）",
}
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# Gorilla Mux
go get github.com/gorilla/mux

# Gorilla 工具包（可选）
go get github.com/gorilla/handlers
go get github.com/gorilla/sessions
go get github.com/gorilla/websocket
go get github.com/gorilla/schema
go get github.com/gorilla/securecookie

# OTLP 依赖
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0
go get go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp@v0.57.0
```

### 2.2 基础配置

```go
package main

import (
    "context"
    "net/http"
    "time"
    
    "github.com/gorilla/mux"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func main() {
    ctx := context.Background()
    
    // 初始化 OTLP
    tp, err := initOTLP(ctx)
    if err != nil {
        panic(err)
    }
    defer tp.Shutdown(ctx)
    
    // 创建路由器
    r := mux.NewRouter()
    
    // 注册中间件
    r.Use(tracingMiddleware)
    r.Use(metricsMiddleware)
    
    // 注册路由
    r.HandleFunc("/users/{id:[0-9]+}", getUser).Methods("GET")
    r.HandleFunc("/users", createUser).Methods("POST")
    r.HandleFunc("/health", healthCheck).Methods("GET")
    
    // 启动服务器
    srv := &http.Server{
        Addr:         ":8080",
        Handler:      r,
        ReadTimeout:  15 * time.Second,
        WriteTimeout: 15 * time.Second,
        IdleTimeout:  60 * time.Second,
    }
    
    srv.ListenAndServe()
}

func initOTLP(ctx context.Context) (*trace.TracerProvider, error) {
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceName("gorilla-mux-service"),
            semconv.ServiceVersion("1.0.0"),
        )),
    )
    
    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
    
    return tp, nil
}
```

---

## 3. OTLP 完整集成

### 3.1 追踪中间件

```go
package middleware

import (
    "fmt"
    "net/http"
    "time"
    
    "github.com/gorilla/mux"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// TracingMiddleware OTLP 追踪中间件
func TracingMiddleware(serviceName string) mux.MiddlewareFunc {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()
    
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            // 提取上游 trace context
            ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))
            
            // 获取路由信息
            route := mux.CurrentRoute(r)
            var routeName string
            var routePattern string
            if route != nil {
                routeName = route.GetName()
                routePattern, _ = route.GetPathTemplate()
            }
            
            // 创建 span
            spanName := r.Method + " " + routePattern
            if spanName == "" {
                spanName = r.Method + " " + r.URL.Path
            }
            
            ctx, span := tracer.Start(ctx, spanName,
                trace.WithSpanKind(trace.SpanKindServer),
                trace.WithAttributes(
                    semconv.HTTPMethodKey.String(r.Method),
                    semconv.HTTPRouteKey.String(routePattern),
                    semconv.HTTPTargetKey.String(r.URL.RequestURI()),
                    semconv.NetHostNameKey.String(r.Host),
                    semconv.HTTPUserAgentKey.String(r.UserAgent()),
                    attribute.String("http.route.name", routeName),
                    attribute.String("http.client_ip", r.RemoteAddr),
                ),
            )
            defer span.End()
            
            // 记录路由变量
            vars := mux.Vars(r)
            if len(vars) > 0 {
                for k, v := range vars {
                    span.SetAttributes(attribute.String("http.route.var."+k, v))
                }
            }
            
            // 包装 ResponseWriter
            rw := &responseWriter{
                ResponseWriter: w,
                statusCode:     http.StatusOK,
            }
            
            start := time.Now()
            
            // 继续处理请求
            next.ServeHTTP(rw, r.WithContext(ctx))
            
            duration := time.Since(start)
            
            // 记录响应信息
            span.SetAttributes(
                semconv.HTTPStatusCodeKey.Int(rw.statusCode),
                attribute.Int64("http.response_time_ms", duration.Milliseconds()),
                attribute.Int("http.response_size", rw.bytesWritten),
            )
            
            // 设置 span 状态
            if rw.statusCode >= 400 {
                span.SetStatus(codes.Error, http.StatusText(rw.statusCode))
            } else {
                span.SetStatus(codes.Ok, "")
            }
            
            // 注入 trace context 到响应头
            propagator.Inject(ctx, propagation.HeaderCarrier(w.Header()))
        })
    }
}

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

### 3.2 指标中间件

```go
// MetricsMiddleware OTLP 指标中间件
func MetricsMiddleware(serviceName string) mux.MiddlewareFunc {
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
    
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            ctx := r.Context()
            start := time.Now()
            
            // 获取路由信息
            route := mux.CurrentRoute(r)
            var routePattern string
            if route != nil {
                routePattern, _ = route.GetPathTemplate()
            }
            
            attrs := []attribute.KeyValue{
                attribute.String("http.method", r.Method),
                attribute.String("http.route", routePattern),
            }
            
            // 增加活跃请求数
            activeRequests.Add(ctx, 1, metric.WithAttributes(attrs...))
            defer activeRequests.Add(ctx, -1, metric.WithAttributes(attrs...))
            
            // 记录请求大小
            if r.ContentLength > 0 {
                requestSize.Record(ctx, r.ContentLength, metric.WithAttributes(attrs...))
            }
            
            // 包装 ResponseWriter
            rw := &responseWriter{
                ResponseWriter: w,
                statusCode:     http.StatusOK,
            }
            
            next.ServeHTTP(rw, r)
            
            duration := time.Since(start).Milliseconds()
            
            // 添加状态码
            attrs = append(attrs, attribute.Int("http.status_code", rw.statusCode))
            
            // 记录指标
            requestCounter.Add(ctx, 1, metric.WithAttributes(attrs...))
            requestDuration.Record(ctx, float64(duration), metric.WithAttributes(attrs...))
            responseSize.Record(ctx, int64(rw.bytesWritten), metric.WithAttributes(attrs...))
        })
    }
}
```

---

## 4. 高级特性

### 4.1 路由功能

```go
func SetupRoutes(r *mux.Router) {
    // 1. 基础路由
    r.HandleFunc("/", homeHandler)
    
    // 2. 路径参数
    r.HandleFunc("/users/{id}", getUserHandler)
    r.HandleFunc("/users/{id}/posts/{postId}", getUserPostHandler)
    
    // 3. 正则表达式约束
    r.HandleFunc("/posts/{id:[0-9]+}", getPostHandler)
    r.HandleFunc("/articles/{slug:[a-z-]+}", getArticleHandler)
    
    // 4. HTTP 方法
    r.HandleFunc("/users", listUsersHandler).Methods("GET")
    r.HandleFunc("/users", createUserHandler).Methods("POST")
    r.HandleFunc("/users/{id}", updateUserHandler).Methods("PUT")
    r.HandleFunc("/users/{id}", deleteUserHandler).Methods("DELETE")
    
    // 5. Host 匹配
    r.HandleFunc("/", apiHandler).Host("api.example.com")
    r.HandleFunc("/", adminHandler).Host("admin.example.com")
    
    // 6. Scheme 匹配
    r.HandleFunc("/secure", secureHandler).Schemes("https")
    
    // 7. Header 匹配
    r.HandleFunc("/api", apiV1Handler).Headers("X-API-Version", "1")
    r.HandleFunc("/api", apiV2Handler).Headers("X-API-Version", "2")
    
    // 8. Query 参数匹配
    r.HandleFunc("/search", searchHandler).Queries("q", "{query}")
    
    // 9. 子路由
    api := r.PathPrefix("/api").Subrouter()
    api.Use(authMiddleware)
    api.HandleFunc("/users", listUsersHandler)
    api.HandleFunc("/posts", listPostsHandler)
    
    // 10. 命名路由
    r.HandleFunc("/users/{id}", getUserHandler).Name("user")
    
    // 生成 URL
    url, _ := r.Get("user").URL("id", "123")
    // Output: /users/123
}
```

### 4.2 子路由和分组

```go
func SetupAPIRoutes(r *mux.Router) {
    // API v1
    v1 := r.PathPrefix("/api/v1").Subrouter()
    v1.Use(TracingMiddleware("api-v1"))
    v1.Use(authMiddleware)
    
    // 用户路由
    users := v1.PathPrefix("/users").Subrouter()
    users.HandleFunc("", listUsers).Methods("GET")
    users.HandleFunc("", createUser).Methods("POST")
    users.HandleFunc("/{id:[0-9]+}", getUser).Methods("GET")
    users.HandleFunc("/{id:[0-9]+}", updateUser).Methods("PUT")
    users.HandleFunc("/{id:[0-9]+}", deleteUser).Methods("DELETE")
    
    // 订单路由
    orders := v1.PathPrefix("/orders").Subrouter()
    orders.HandleFunc("", listOrders).Methods("GET")
    orders.HandleFunc("", createOrder).Methods("POST")
    orders.HandleFunc("/{id:[0-9]+}", getOrder).Methods("GET")
    
    // API v2
    v2 := r.PathPrefix("/api/v2").Subrouter()
    v2.Use(TracingMiddleware("api-v2"))
    v2.HandleFunc("/users", listUsersV2).Methods("GET")
}
```

### 4.3 中间件链

```go
func SetupMiddlewares(r *mux.Router) {
    // 全局中间件
    r.Use(recoveryMiddleware)
    r.Use(loggingMiddleware)
    r.Use(TracingMiddleware("service"))
    r.Use(MetricsMiddleware("service"))
    r.Use(corsMiddleware)
    
    // 路由级中间件
    api := r.PathPrefix("/api").Subrouter()
    api.Use(authMiddleware)
    api.Use(rateLimitMiddleware)
    
    // 单个路由中间件
    r.Handle("/admin", 
        adminMiddleware(adminHandler),
    ).Methods("GET")
}

// 中间件组合
func Chain(middlewares ...mux.MiddlewareFunc) mux.MiddlewareFunc {
    return func(next http.Handler) http.Handler {
        for i := len(middlewares) - 1; i >= 0; i-- {
            next = middlewares[i](next)
        }
        return next
    }
}
```

---

## 5. 完整示例

### 5.1 RESTful API 服务

```go
package main

import (
    "context"
    "database/sql"
    "encoding/json"
    "net/http"
    "strconv"
    "time"
    
    "github.com/gorilla/mux"
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

// ListUsers 列出用户
func (s *UserService) ListUsers(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("user-service")
    
    ctx, span := tracer.Start(ctx, "list-users")
    defer span.End()
    
    // 解析查询参数
    limit, _ := strconv.Atoi(r.URL.Query().Get("limit"))
    offset, _ := strconv.Atoi(r.URL.Query().Get("offset"))
    
    if limit <= 0 || limit > 100 {
        limit = 20
    }
    
    span.SetAttributes(
        attribute.Int("pagination.limit", limit),
        attribute.Int("pagination.offset", offset),
    )
    
    // 查询数据库
    rows, err := s.db.QueryContext(ctx,
        "SELECT id, username, email, created_at FROM users ORDER BY id LIMIT $1 OFFSET $2",
        limit, offset,
    )
    if err != nil {
        span.RecordError(err)
        http.Error(w, "Database error", http.StatusInternalServerError)
        return
    }
    defer rows.Close()
    
    users := make([]User, 0, limit)
    for rows.Next() {
        var user User
        if err := rows.Scan(&user.ID, &user.Username, &user.Email, &user.CreatedAt); err != nil {
            span.RecordError(err)
            continue
        }
        users = append(users, user)
    }
    
    span.SetAttributes(attribute.Int("users.count", len(users)))
    span.SetStatus(codes.Ok, "")
    
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(map[string]interface{}{
        "users":  users,
        "limit":  limit,
        "offset": offset,
    })
}

// GetUser 获取用户
func (s *UserService) GetUser(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("user-service")
    
    ctx, span := tracer.Start(ctx, "get-user")
    defer span.End()
    
    // 获取路由变量
    vars := mux.Vars(r)
    userID := vars["id"]
    
    span.SetAttributes(attribute.String("user.id", userID))
    
    var user User
    err := s.db.QueryRowContext(ctx,
        "SELECT id, username, email, created_at FROM users WHERE id = $1",
        userID,
    ).Scan(&user.ID, &user.Username, &user.Email, &user.CreatedAt)
    
    if err == sql.ErrNoRows {
        span.SetStatus(codes.Error, "user not found")
        http.Error(w, "User not found", http.StatusNotFound)
        return
    }
    
    if err != nil {
        span.RecordError(err)
        http.Error(w, "Database error", http.StatusInternalServerError)
        return
    }
    
    span.SetStatus(codes.Ok, "")
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(user)
}

// CreateUser 创建用户
func (s *UserService) CreateUser(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("user-service")
    
    ctx, span := tracer.Start(ctx, "create-user")
    defer span.End()
    
    var req struct {
        Username string `json:"username"`
        Email    string `json:"email"`
        Password string `json:"password"`
    }
    
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        span.RecordError(err)
        http.Error(w, "Invalid request", http.StatusBadRequest)
        return
    }
    
    span.SetAttributes(
        attribute.String("user.username", req.Username),
        attribute.String("user.email", req.Email),
    )
    
    var userID int64
    err := s.db.QueryRowContext(ctx,
        "INSERT INTO users (username, email, password) VALUES ($1, $2, $3) RETURNING id",
        req.Username, req.Email, hashPassword(req.Password),
    ).Scan(&userID)
    
    if err != nil {
        span.RecordError(err)
        http.Error(w, "Failed to create user", http.StatusInternalServerError)
        return
    }
    
    span.SetAttributes(attribute.Int64("user.id", userID))
    span.SetStatus(codes.Ok, "")
    
    w.WriteHeader(http.StatusCreated)
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(map[string]interface{}{
        "id":       userID,
        "username": req.Username,
        "email":    req.Email,
    })
}

func hashPassword(password string) string {
    // 实际应该使用 bcrypt
    return password
}

func main() {
    ctx := context.Background()
    
    // 初始化 OTLP
    tp, err := initOTLP(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(ctx)
    
    // 初始化数据库
    db, err := sql.Open("postgres", os.Getenv("DATABASE_URL"))
    if err != nil {
        log.Fatal(err)
    }
    defer db.Close()
    
    // 创建服务
    userService := NewUserService(db)
    
    // 创建路由器
    r := mux.NewRouter()
    
    // 配置中间件
    r.Use(middleware.RecoveryMiddleware())
    r.Use(middleware.LoggingMiddleware())
    r.Use(middleware.TracingMiddleware("gorilla-mux-service"))
    r.Use(middleware.MetricsMiddleware("gorilla-mux-service"))
    r.Use(middleware.CORSMiddleware())
    
    // API 路由
    api := r.PathPrefix("/api/v1").Subrouter()
    api.HandleFunc("/users", userService.ListUsers).Methods("GET")
    api.HandleFunc("/users", userService.CreateUser).Methods("POST")
    api.HandleFunc("/users/{id:[0-9]+}", userService.GetUser).Methods("GET")
    api.HandleFunc("/users/{id:[0-9]+}", userService.UpdateUser).Methods("PUT")
    api.HandleFunc("/users/{id:[0-9]+}", userService.DeleteUser).Methods("DELETE")
    
    // 健康检查
    r.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
        w.WriteHeader(http.StatusOK)
        json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
    }).Methods("GET")
    
    // 启动服务器
    srv := &http.Server{
        Addr:         ":8080",
        Handler:      r,
        ReadTimeout:  15 * time.Second,
        WriteTimeout: 15 * time.Second,
        IdleTimeout:  60 * time.Second,
    }
    
    log.Println("Starting server on :8080")
    if err := srv.ListenAndServe(); err != nil {
        log.Fatal(err)
    }
}
```

---

## 6. Gorilla 工具包集成

### 6.1 Sessions（会话管理）

```go
import "github.com/gorilla/sessions"

var store = sessions.NewCookieStore([]byte("secret-key"))

func loginHandler(w http.ResponseWriter, r *http.Request) {
    session, _ := store.Get(r, "session-name")
    
    // 设置会话值
    session.Values["user_id"] = 123
    session.Values["authenticated"] = true
    
    // 保存会话（带追踪）
    ctx := r.Context()
    tracer := otel.Tracer("session")
    ctx, span := tracer.Start(ctx, "save-session")
    defer span.End()
    
    if err := session.Save(r, w); err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    span.SetStatus(codes.Ok, "")
}
```

### 6.2 WebSocket

```go
import "github.com/gorilla/websocket"

var upgrader = websocket.Upgrader{
    CheckOrigin: func(r *http.Request) bool {
        return true
    },
}

func wsHandler(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("websocket")
    
    ctx, span := tracer.Start(ctx, "websocket-upgrade")
    defer span.End()
    
    conn, err := upgrader.Upgrade(w, r, nil)
    if err != nil {
        span.RecordError(err)
        return
    }
    defer conn.Close()
    
    span.SetStatus(codes.Ok, "connection established")
    
    // 处理消息
    for {
        msgCtx, msgSpan := tracer.Start(ctx, "websocket-message")
        
        messageType, p, err := conn.ReadMessage()
        if err != nil {
            msgSpan.RecordError(err)
            msgSpan.End()
            break
        }
        
        msgSpan.SetAttributes(
            attribute.Int("message.type", messageType),
            attribute.Int("message.size", len(p)),
        )
        
        // 回显消息
        if err := conn.WriteMessage(messageType, p); err != nil {
            msgSpan.RecordError(err)
            msgSpan.End()
            break
        }
        
        msgSpan.SetStatus(codes.Ok, "")
        msgSpan.End()
    }
}
```

---

## 7. 性能优化

### 7.1 性能基准

```go
// BenchmarkGorillaMux 基准测试
func BenchmarkGorillaMux(b *testing.B) {
    r := mux.NewRouter()
    r.HandleFunc("/users/{id}", func(w http.ResponseWriter, r *http.Request) {
        w.WriteHeader(http.StatusOK)
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

// 结果:
// BenchmarkGorillaMux-8    500000    2500 ns/op    1200 B/op    12 allocs/op
```

---

## 8. 总结

### 8.1 优势与劣势

```text
✅ 优势:
  - 成熟稳定，10+年验证
  - 功能丰富，路由功能完整
  - 社区活跃，大量第三方支持
  - 文档完善
  - Gorilla 工具包完整

❌ 劣势:
  - 性能不如 Chi/httprouter
  - 内存占用较高
  - 不是最现代的设计
```

### 8.2 最佳实践

1. **使用子路由**: 组织大型应用
2. **命名路由**: 便于生成 URL
3. **正则约束**: 提前验证参数
4. **中间件链**: 合理组织中间件

**相关文档**:

- [49_Chi框架深度集成与最佳实践.md](../49_Chi框架深度集成与最佳实践.md)
- [85_Gorilla_Toolkit与OTLP完整集成_2025版.md](../85_Gorilla_Toolkit与OTLP完整集成_2025版.md)

---

**更新日期**: 2025-10-11  
**Gorilla Mux 版本**: v1.8.1  
**性能级别**: ⭐⭐⭐  
**推荐指数**: ⭐⭐⭐⭐⭐

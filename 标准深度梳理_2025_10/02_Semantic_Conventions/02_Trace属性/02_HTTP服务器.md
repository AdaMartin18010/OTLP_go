# HTTP 服务器追踪属性完整指南

> **文档版本**: v2.0.0  
> **最后更新**: 2025-10-09  
> **OpenTelemetry 版本**: v1.32.0  
> **Go 版本**: 1.25.1

## 目录

- [HTTP 服务器追踪属性完整指南](#http-服务器追踪属性完整指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 HTTP 服务器语义约定](#11-http-服务器语义约定)
    - [1.2 与客户端的区别](#12-与客户端的区别)
  - [2. 核心属性](#2-核心属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
    - [2.3 网络属性](#23-网络属性)
  - [3. Go 标准库集成](#3-go-标准库集成)
    - [3.1 基础中间件](#31-基础中间件)
    - [3.2 使用示例](#32-使用示例)
  - [4. 框架集成](#4-框架集成)
    - [4.1 Gin 框架](#41-gin-框架)
    - [4.2 Echo 框架](#42-echo-框架)
    - [4.3 Fiber 框架](#43-fiber-框架)
    - [4.4 Chi 框架](#44-chi-框架)
  - [5. 路由追踪](#5-路由追踪)
    - [5.1 动态路由模板](#51-动态路由模板)
    - [5.2 路由参数提取](#52-路由参数提取)
    - [5.3 高级路由中间件](#53-高级路由中间件)
  - [6. 中间件模式](#6-中间件模式)
    - [6.1 中间件链](#61-中间件链)
    - [6.2 条件中间件](#62-条件中间件)
    - [6.3 采样中间件](#63-采样中间件)
  - [7. 错误处理](#7-错误处理)
    - [7.1 panic 恢复](#71-panic-恢复)
    - [7.2 错误响应追踪](#72-错误响应追踪)
  - [8. 完整实现](#8-完整实现)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 Span 命名](#91-span-命名)
    - [9.2 敏感数据过滤](#92-敏感数据过滤)
    - [9.3 性能监控](#93-性能监控)
  - [10. 性能优化](#10-性能优化)
    - [10.1 批量导出](#101-批量导出)
    - [10.2 采样策略](#102-采样策略)
    - [10.3 资源池](#103-资源池)
  - [总结](#总结)

---

## 1. 概述

### 1.1 HTTP 服务器语义约定

HTTP 服务器追踪记录从**服务器视角**处理的 HTTP 请求。

**关键特征**:

- **Span Kind**: `SPAN_KIND_SERVER`
- **命名规范**: `{http.request.method} {http.route}`
- **父 Span**: 来自客户端的远程 Span (通过 Trace Context 传播)
- **子 Span**: 业务逻辑、数据库查询等

### 1.2 与客户端的区别

| 维度 | 服务器端 | 客户端 |
|------|----------|--------|
| **Span Kind** | `SERVER` | `CLIENT` |
| **命名** | `GET /api/users/:id` | `GET` |
| **网络属性** | `client.address`, `client.port` | `server.address`, `server.port` |
| **关注点** | 路由、业务逻辑、响应生成 | 请求发起、重试、超时 |

---

## 2. 核心属性

### 2.1 必需属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `http.request.method` | string | `GET`, `POST` | HTTP 方法 |
| `http.route` | string | `/api/users/:id` | 匹配的路由模板 |
| `url.scheme` | string | `https` | URL 协议 |
| `url.path` | string | `/api/users/123` | 实际请求路径 |

### 2.2 推荐属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `server.address` | string | `api.example.com` | 服务器地址 (Host 头) |
| `server.port` | int | `8080` | 服务器端口 |
| `client.address` | string | `192.168.1.10` | 客户端 IP |
| `client.port` | int | `54321` | 客户端端口 |
| `http.request.header.<key>` | string[] | `["application/json"]` | 请求头 |
| `http.response.status_code` | int | `200` | HTTP 状态码 |
| `http.response.header.<key>` | string[] | `["gzip"]` | 响应头 |
| `user_agent.original` | string | `Mozilla/5.0...` | User-Agent |

### 2.3 网络属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `network.protocol.name` | string | `http` | 协议名称 |
| `network.protocol.version` | string | `1.1`, `2` | 协议版本 |
| `network.peer.address` | string | `192.168.1.10` | 对端 IP |
| `network.peer.port` | int | `54321` | 对端端口 |

---

## 3. Go 标准库集成

### 3.1 基础中间件

```go
package httpserver

import (
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

// TracingMiddleware 为 http.Handler 添加追踪
func TracingMiddleware(next http.Handler) http.Handler {
    tracer := otel.Tracer("http-server")
    propagator := otel.GetTextMapPropagator()

    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 从 HTTP 头提取追踪上下文
        ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

        // 创建服务器 Span
        spanName := r.Method + " " + r.URL.Path
        ctx, span := tracer.Start(ctx, spanName,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.HTTPRequestMethodKey.String(r.Method),
                semconv.URLPath(r.URL.Path),
                semconv.URLScheme(r.URL.Scheme),
                semconv.ServerAddress(r.Host),
                semconv.UserAgentOriginal(r.UserAgent()),
            ),
        )
        defer span.End()

        // 添加客户端地址
        if clientIP := extractClientIP(r); clientIP != "" {
            span.SetAttributes(semconv.ClientAddress(clientIP))
        }

        // 添加查询参数 (可选)
        if r.URL.RawQuery != "" {
            span.SetAttributes(semconv.URLQuery(r.URL.RawQuery))
        }

        // 包装 ResponseWriter 以捕获状态码
        recorder := &statusRecorder{ResponseWriter: w, statusCode: 200}

        // 调用下一个处理器
        next.ServeHTTP(recorder, r.WithContext(ctx))

        // 记录响应状态码
        span.SetAttributes(semconv.HTTPResponseStatusCode(recorder.statusCode))

        // 设置 Span 状态
        if recorder.statusCode >= 400 {
            span.SetStatus(codes.Error, http.StatusText(recorder.statusCode))
        } else {
            span.SetStatus(codes.Ok, "")
        }
    })
}

// statusRecorder 包装 ResponseWriter 以记录状态码
type statusRecorder struct {
    http.ResponseWriter
    statusCode int
}

func (r *statusRecorder) WriteHeader(statusCode int) {
    r.statusCode = statusCode
    r.ResponseWriter.WriteHeader(statusCode)
}

func (r *statusRecorder) Write(b []byte) (int, error) {
    return r.ResponseWriter.Write(b)
}

// extractClientIP 提取真实客户端 IP
func extractClientIP(r *http.Request) string {
    // 优先从 X-Forwarded-For 获取
    if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
        ips := strings.Split(xff, ",")
        return strings.TrimSpace(ips[0])
    }

    // X-Real-IP
    if xri := r.Header.Get("X-Real-IP"); xri != "" {
        return xri
    }

    // 直接连接的客户端
    host, _, _ := net.SplitHostPort(r.RemoteAddr)
    return host
}
```

### 3.2 使用示例

```go
func main() {
    // 初始化 OpenTelemetry
    tp := initTracer()
    defer tp.Shutdown(context.Background())

    // 创建路由
    mux := http.NewServeMux()
    mux.HandleFunc("/api/users", handleUsers)
    mux.HandleFunc("/api/users/", handleUserByID)

    // 应用追踪中间件
    handler := TracingMiddleware(mux)

    // 启动服务器
    log.Println("Server starting on :8080")
    log.Fatal(http.ListenAndServe(":8080", handler))
}

func handleUsers(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    span := trace.SpanFromContext(ctx)
    
    // 设置路由模板
    span.SetAttributes(semconv.HTTPRoute("/api/users"))

    // 业务逻辑
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusOK)
    json.NewEncoder(w).Encode(map[string]string{
        "message": "Users list",
    })
}
```

---

## 4. 框架集成

### 4.1 Gin 框架

```go
import (
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin"
)

func setupGinServer() *gin.Engine {
    r := gin.New()
    
    // 使用 OpenTelemetry 中间件
    r.Use(otelgin.Middleware("my-service"))

    r.GET("/api/users/:id", func(c *gin.Context) {
        span := trace.SpanFromContext(c.Request.Context())
        
        // 路由参数自动设置
        // http.route = "/api/users/:id"
        
        userID := c.Param("id")
        span.SetAttributes(attribute.String("user.id", userID))

        c.JSON(200, gin.H{"user_id": userID})
    })

    return r
}
```

### 4.2 Echo 框架

```go
import (
    "github.com/labstack/echo/v4"
    "go.opentelemetry.io/contrib/instrumentation/github.com/labstack/echo/otelecho"
)

func setupEchoServer() *echo.Echo {
    e := echo.New()
    
    // 使用 OpenTelemetry 中间件
    e.Use(otelecho.Middleware("my-service"))

    e.GET("/api/users/:id", func(c echo.Context) error {
        span := trace.SpanFromContext(c.Request().Context())
        
        userID := c.Param("id")
        span.SetAttributes(attribute.String("user.id", userID))

        return c.JSON(200, map[string]string{"user_id": userID})
    })

    return e
}
```

### 4.3 Fiber 框架

```go
import (
    "github.com/gofiber/fiber/v2"
    "go.opentelemetry.io/contrib/instrumentation/github.com/gofiber/fiber/otelfiber"
)

func setupFiberServer() *fiber.App {
    app := fiber.New()
    
    // 使用 OpenTelemetry 中间件
    app.Use(otelfiber.Middleware("my-service"))

    app.Get("/api/users/:id", func(c *fiber.Ctx) error {
        span := trace.SpanFromContext(c.Context())
        
        userID := c.Params("id")
        span.SetAttributes(attribute.String("user.id", userID))

        return c.JSON(fiber.Map{"user_id": userID})
    })

    return app
}
```

### 4.4 Chi 框架

```go
import (
    "github.com/go-chi/chi/v5"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
)

func setupChiServer() *chi.Mux {
    r := chi.NewRouter()
    
    // 使用 OpenTelemetry 中间件
    r.Use(func(next http.Handler) http.Handler {
        return otelhttp.NewHandler(next, "my-service")
    })

    r.Get("/api/users/{id}", func(w http.ResponseWriter, r *http.Request) {
        span := trace.SpanFromContext(r.Context())
        
        userID := chi.URLParam(r, "id")
        span.SetAttributes(attribute.String("user.id", userID))

        json.NewEncoder(w).Encode(map[string]string{"user_id": userID})
    })

    return r
}
```

---

## 5. 路由追踪

### 5.1 动态路由模板

正确设置 `http.route` 属性:

```go
// ✅ 正确: 使用路由模板
span.SetAttributes(semconv.HTTPRoute("/api/users/:id"))

// ❌ 错误: 使用实际路径
span.SetAttributes(semconv.HTTPRoute("/api/users/123"))
```

### 5.2 路由参数提取

```go
type RouteExtractor interface {
    ExtractRoute(r *http.Request) string
}

// PatternBasedExtractor 基于模式匹配的路由提取器
type PatternBasedExtractor struct {
    routes map[string]*regexp.Regexp
}

func NewPatternBasedExtractor(patterns []string) *PatternBasedExtractor {
    e := &PatternBasedExtractor{
        routes: make(map[string]*regexp.Regexp),
    }
    
    for _, pattern := range patterns {
        // 转换路由模板为正则表达式
        // /api/users/:id -> ^/api/users/([^/]+)$
        regex := convertPatternToRegex(pattern)
        e.routes[pattern] = regexp.MustCompile(regex)
    }
    
    return e
}

func (e *PatternBasedExtractor) ExtractRoute(r *http.Request) string {
    path := r.URL.Path
    
    for pattern, regex := range e.routes {
        if regex.MatchString(path) {
            return pattern
        }
    }
    
    return path // 无匹配时返回原路径
}

func convertPatternToRegex(pattern string) string {
    // /api/users/:id -> ^/api/users/([^/]+)$
    regex := "^" + strings.ReplaceAll(pattern, ":id", "([^/]+)") + "$"
    return regex
}
```

### 5.3 高级路由中间件

```go
// AdvancedTracingMiddleware 带路由提取的中间件
func AdvancedTracingMiddleware(extractor RouteExtractor) func(http.Handler) http.Handler {
    tracer := otel.Tracer("http-server")
    propagator := otel.GetTextMapPropagator()

    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

            // 提取路由模板
            route := extractor.ExtractRoute(r)
            spanName := r.Method + " " + route

            ctx, span := tracer.Start(ctx, spanName,
                trace.WithSpanKind(trace.SpanKindServer),
                trace.WithAttributes(
                    semconv.HTTPRequestMethodKey.String(r.Method),
                    semconv.HTTPRoute(route),
                    semconv.URLPath(r.URL.Path),
                ),
            )
            defer span.End()

            recorder := &statusRecorder{ResponseWriter: w, statusCode: 200}
            next.ServeHTTP(recorder, r.WithContext(ctx))

            span.SetAttributes(semconv.HTTPResponseStatusCode(recorder.statusCode))
        })
    }
}
```

---

## 6. 中间件模式

### 6.1 中间件链

```go
// Middleware 中间件类型
type Middleware func(http.Handler) http.Handler

// Chain 链接多个中间件
func Chain(middlewares ...Middleware) Middleware {
    return func(final http.Handler) http.Handler {
        for i := len(middlewares) - 1; i >= 0; i-- {
            final = middlewares[i](final)
        }
        return final
    }
}

// 使用示例
handler := Chain(
    TracingMiddleware,
    LoggingMiddleware,
    AuthMiddleware,
)(mux)
```

### 6.2 条件中间件

```go
// ConditionalMiddleware 基于条件应用中间件
func ConditionalMiddleware(condition func(*http.Request) bool, middleware Middleware) Middleware {
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            if condition(r) {
                middleware(next).ServeHTTP(w, r)
            } else {
                next.ServeHTTP(w, r)
            }
        })
    }
}

// 仅对 API 路径追踪
apiOnlyTracing := ConditionalMiddleware(
    func(r *http.Request) bool {
        return strings.HasPrefix(r.URL.Path, "/api/")
    },
    TracingMiddleware,
)
```

### 6.3 采样中间件

```go
// SamplingMiddleware 基于采样率的追踪中间件
func SamplingMiddleware(rate float64) Middleware {
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            if rand.Float64() < rate {
                TracingMiddleware(next).ServeHTTP(w, r)
            } else {
                next.ServeHTTP(w, r)
            }
        })
    }
}
```

---

## 7. 错误处理

### 7.1 panic 恢复

```go
// RecoveryMiddleware 恢复 panic 并记录到 Span
func RecoveryMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        defer func() {
            if err := recover(); err != nil {
                span := trace.SpanFromContext(r.Context())
                
                // 记录 panic
                span.RecordError(fmt.Errorf("panic: %v", err))
                span.SetStatus(codes.Error, "Internal Server Error")
                
                // 记录堆栈
                stack := debug.Stack()
                span.AddEvent("panic.recovered", trace.WithAttributes(
                    attribute.String("panic.value", fmt.Sprintf("%v", err)),
                    attribute.String("panic.stack", string(stack)),
                ))

                // 返回 500 错误
                http.Error(w, "Internal Server Error", http.StatusInternalServerError)
            }
        }()

        next.ServeHTTP(w, r)
    })
}
```

### 7.2 错误响应追踪

```go
// ErrorResponse 结构化错误响应
type ErrorResponse struct {
    Code    string `json:"code"`
    Message string `json:"message"`
    Details any    `json:"details,omitempty"`
}

// WriteError 写入错误响应并记录到 Span
func WriteError(ctx context.Context, w http.ResponseWriter, statusCode int, err error) {
    span := trace.SpanFromContext(ctx)
    
    // 记录错误
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    span.SetAttributes(
        semconv.HTTPResponseStatusCode(statusCode),
        attribute.String("error.type", fmt.Sprintf("%T", err)),
    )

    // 写入响应
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(statusCode)
    json.NewEncoder(w).Encode(ErrorResponse{
        Code:    "ERROR",
        Message: err.Error(),
    })
}
```

---

## 8. 完整实现

生产级服务器实现:

```go
package main

import (
    "context"
    "encoding/json"
    "log"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func main() {
    // 初始化追踪
    tp := initTracer()
    defer tp.Shutdown(context.Background())

    // 创建服务器
    server := &http.Server{
        Addr:         ":8080",
        Handler:      setupRoutes(),
        ReadTimeout:  10 * time.Second,
        WriteTimeout: 10 * time.Second,
    }

    log.Println("Server starting on :8080")
    log.Fatal(server.ListenAndServe())
}

func initTracer() *sdktrace.TracerProvider {
    exporter, _ := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )

    resource := resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceName("api-server"),
        semconv.ServiceVersion("1.0.0"),
    )

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(resource),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )

    otel.SetTracerProvider(tp)
    return tp
}

func setupRoutes() http.Handler {
    mux := http.NewServeMux()

    // 注册路由
    mux.HandleFunc("/api/users", handleUsers)
    mux.HandleFunc("/api/users/", handleUserByID)
    mux.HandleFunc("/health", handleHealth)

    // 应用中间件链
    handler := Chain(
        RecoveryMiddleware,
        TracingMiddleware,
        LoggingMiddleware,
    )(mux)

    return handler
}

func handleUsers(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    span := trace.SpanFromContext(ctx)
    span.SetAttributes(semconv.HTTPRoute("/api/users"))

    if r.Method != http.MethodGet {
        WriteError(ctx, w, http.StatusMethodNotAllowed, 
            fmt.Errorf("method not allowed"))
        return
    }

    users := []map[string]string{
        {"id": "1", "name": "Alice"},
        {"id": "2", "name": "Bob"},
    }

    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(users)
}

func handleUserByID(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    span := trace.SpanFromContext(ctx)
    span.SetAttributes(semconv.HTTPRoute("/api/users/:id"))

    // 提取 ID
    parts := strings.Split(r.URL.Path, "/")
    if len(parts) < 4 {
        WriteError(ctx, w, http.StatusBadRequest, 
            fmt.Errorf("invalid user ID"))
        return
    }

    userID := parts[3]
    span.SetAttributes(attribute.String("user.id", userID))

    user := map[string]string{
        "id":   userID,
        "name": "User " + userID,
    }

    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(user)
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
    w.WriteHeader(http.StatusOK)
    w.Write([]byte("OK"))
}

func LoggingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        log.Printf("Started %s %s", r.Method, r.URL.Path)
        
        next.ServeHTTP(w, r)
        
        log.Printf("Completed in %v", time.Since(start))
    })
}
```

---

## 9. 最佳实践

### 9.1 Span 命名

```go
// ✅ 使用路由模板
"GET /api/users/:id"

// ❌ 使用实际路径 (高基数)
"GET /api/users/12345"
```

### 9.2 敏感数据过滤

```go
func sanitizeHeaders(headers http.Header) http.Header {
    sanitized := headers.Clone()
    sensitive := []string{"Authorization", "Cookie", "X-API-Key"}
    
    for _, key := range sensitive {
        if sanitized.Get(key) != "" {
            sanitized.Set(key, "[REDACTED]")
        }
    }
    
    return sanitized
}
```

### 9.3 性能监控

```go
// PerformanceMiddleware 监控请求性能
func PerformanceMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        span := trace.SpanFromContext(r.Context())

        next.ServeHTTP(w, r)

        duration := time.Since(start)
        span.SetAttributes(
            attribute.Int64("http.duration_ms", duration.Milliseconds()),
        )

        // 慢请求告警
        if duration > 1*time.Second {
            span.AddEvent("slow_request", trace.WithAttributes(
                attribute.String("duration", duration.String()),
            ))
        }
    })
}
```

---

## 10. 性能优化

### 10.1 批量导出

```go
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        sdktrace.WithMaxExportBatchSize(512),
        sdktrace.WithBatchTimeout(5*time.Second),
        sdktrace.WithMaxQueueSize(2048),
    ),
)
```

### 10.2 采样策略

```go
// 父级采样 + 错误采样
sampler := sdktrace.ParentBased(
    sdktrace.TraceIDRatioBased(0.1), // 10% 基础采样
)

tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(sampler),
)
```

### 10.3 资源池

```go
var spanRecorderPool = sync.Pool{
    New: func() interface{} {
        return &statusRecorder{}
    },
}

func getRecorder(w http.ResponseWriter) *statusRecorder {
    recorder := spanRecorderPool.Get().(*statusRecorder)
    recorder.ResponseWriter = w
    recorder.statusCode = 200
    return recorder
}

func putRecorder(recorder *statusRecorder) {
    recorder.ResponseWriter = nil
    spanRecorderPool.Put(recorder)
}
```

---

## 总结

✅ **核心属性**: `http.route`, `http.request.method`, `http.response.status_code`  
✅ **框架支持**: Gin, Echo, Fiber, Chi  
✅ **中间件模式**: 链式、条件、采样  
✅ **错误处理**: panic 恢复、错误追踪  
✅ **性能优化**: 批量导出、采样、资源池

**下一步**: 参见 `03_RPC与gRPC.md` 了解 RPC 追踪。

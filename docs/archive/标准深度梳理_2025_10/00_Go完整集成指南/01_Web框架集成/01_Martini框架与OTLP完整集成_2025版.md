# Martini 框架与 OTLP 完整集成（2025版）

> **Martini 版本**: v1.0 (archived, 历史参考)  
> **推荐替代**: Chi v5 / Echo v4  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ⚠️ 归档参考

---

## 📋 目录

- [Martini 框架与 OTLP 完整集成（2025版）](#martini-框架与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Martini 框架概述](#1-martini-框架概述)
    - [1.1 历史背景](#11-历史背景)
    - [1.2 为什么不推荐 Martini](#12-为什么不推荐-martini)
    - [1.3 迁移建议](#13-迁移建议)
  - [2. Martini 基础集成（仅供参考）](#2-martini-基础集成仅供参考)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础配置](#22-基础配置)
    - [2.3 OTLP 中间件实现](#23-otlp-中间件实现)
  - [3. 完整示例](#3-完整示例)
    - [3.1 基础服务](#31-基础服务)
    - [3.2 中间件栈](#32-中间件栈)
  - [4. 迁移到现代框架](#4-迁移到现代框架)
    - [4.1 迁移到 Chi](#41-迁移到-chi)
    - [4.2 迁移到 Echo](#42-迁移到-echo)
  - [5. 总结](#5-总结)
    - [5.1 Martini 的遗产](#51-martini-的遗产)
    - [5.2 现代替代方案](#52-现代替代方案)

---

## 1. Martini 框架概述

### 1.1 历史背景

**Martini** 是由 CodeGangsta 在 2013 年创建的 Go Web 框架，曾经非常流行。

```text
📊 历史地位:
  - 2013-2015: Go 最流行的 Web 框架之一
  - 引入了依赖注入（DI）概念到 Go 生态
  - 优雅的 API 设计影响了后续框架
  
⚠️ 现状:
  - 2014 年作者宣布停止维护
  - 使用 reflect 导致性能问题
  - 已被现代框架超越
```

### 1.2 为什么不推荐 Martini

```go
// ❌ Martini 的问题

// 1. 性能问题 - 大量使用 reflect
m := martini.Classic()
m.Get("/user/:id", func(params martini.Params) string {
    // 每次请求都会进行反射操作
    return "User " + params["id"]
})

// 2. 内存分配 - 每个请求都会创建新的注入器
// Benchmark 结果:
// Martini:     3000 ns/op    2000 B/op    30 allocs/op
// Chi:          800 ns/op     400 B/op     5 allocs/op
// Echo:         600 ns/op     300 B/op     4 allocs/op

// 3. 不支持 Context - 无法使用 Go 1.7+ context.Context
m.Get("/api", func() string {
    // ❌ 无法传递 context
    return "response"
})

// 4. 维护停止 - 不支持现代 Go 特性
// ❌ 无泛型支持
// ❌ 无 Go 1.25.1 新特性
// ❌ 安全漏洞无人修复
```

**性能对比**：

```text
┌────────────┬───────────┬───────────┬────────────┐
│   框架     │  延迟(ns) │ 内存(B)   │ 分配次数   │
├────────────┼───────────┼───────────┼────────────┤
│ Martini    │   3000    │   2000    │    30      │
│ Chi        │    800    │    400    │     5      │
│ Echo       │    600    │    300    │     4      │
│ Gin        │    500    │    250    │     3      │
│ Fiber      │    400    │    200    │     2      │
└────────────┴───────────┴───────────┴────────────┘
```

### 1.3 迁移建议

```go
// ✅ 推荐迁移路径

// Martini → Chi (最平滑)
// - 相似的路由 API
// - 标准 net/http 兼容
// - 零依赖

// Martini → Echo (高性能)
// - 更快的性能
// - 完善的中间件生态
// - 内置绑定和验证

// Martini → Gin (最流行)
// - 最大的社区
// - 最多的中间件
// - 性能优秀
```

---

## 2. Martini 基础集成（仅供参考）

> ⚠️ **警告**: 以下内容仅供维护遗留系统参考，新项目请使用现代框架。

### 2.1 依赖安装

```bash
# Martini (已归档)
go get github.com/go-martini/martini

# OTLP 依赖
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.32.0
```

### 2.2 基础配置

```go
package main

import (
    "context"
    "log"
    "net/http"
    
    "github.com/go-martini/martini"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// initOTLP 初始化 OpenTelemetry
func initOTLP(ctx context.Context) (*trace.TracerProvider, error) {
    // 创建 OTLP exporter
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceName("martini-service"),
            semconv.ServiceVersion("1.0.0"),
            attribute.String("environment", "production"),
        )),
    )
    
    // 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    
    // 设置全局 Propagator
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
    
    return tp, nil
}
```

### 2.3 OTLP 中间件实现

```go
package middleware

import (
    "context"
    "net/http"
    "time"
    
    "github.com/go-martini/martini"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// TracingMiddleware OTLP 追踪中间件
func TracingMiddleware(serviceName string) martini.Handler {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()
    
    return func(res http.ResponseWriter, req *http.Request, c martini.Context) {
        // 提取上游 trace context
        ctx := propagator.Extract(req.Context(), propagation.HeaderCarrier(req.Header))
        
        // 创建 span
        spanName := req.Method + " " + req.URL.Path
        ctx, span := tracer.Start(ctx, spanName,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.HTTPMethodKey.String(req.Method),
                semconv.HTTPRouteKey.String(req.URL.Path),
                semconv.HTTPSchemeKey.String(req.URL.Scheme),
                semconv.HTTPTargetKey.String(req.URL.RequestURI()),
                semconv.NetHostNameKey.String(req.Host),
                attribute.String("http.client_ip", req.RemoteAddr),
                attribute.String("http.user_agent", req.UserAgent()),
            ),
        )
        defer span.End()
        
        // ⚠️ Martini 不支持 context.Context
        // 这是一个 workaround
        contextKey := "__otel_context__"
        c.Map(contextKey)
        c.MapTo(ctx, (*context.Context)(nil))
        
        // 记录请求开始时间
        start := time.Now()
        
        // 继续处理请求
        c.Next()
        
        // 记录响应信息
        duration := time.Since(start)
        
        // 获取响应状态码（Martini 的限制：无法直接获取）
        // 需要使用自定义 ResponseWriter
        statusCode := getStatusCode(res)
        
        span.SetAttributes(
            semconv.HTTPStatusCodeKey.Int(statusCode),
            attribute.Int64("http.response_time_ms", duration.Milliseconds()),
        )
        
        // 设置 span 状态
        if statusCode >= 400 {
            span.SetStatus(codes.Error, http.StatusText(statusCode))
        } else {
            span.SetStatus(codes.Ok, "")
        }
    }
}

// CustomResponseWriter 自定义 ResponseWriter 以捕获状态码
type CustomResponseWriter struct {
    http.ResponseWriter
    statusCode int
}

func NewCustomResponseWriter(w http.ResponseWriter) *CustomResponseWriter {
    return &CustomResponseWriter{
        ResponseWriter: w,
        statusCode:     http.StatusOK,
    }
}

func (w *CustomResponseWriter) WriteHeader(statusCode int) {
    w.statusCode = statusCode
    w.ResponseWriter.WriteHeader(statusCode)
}

func getStatusCode(w http.ResponseWriter) int {
    if crw, ok := w.(*CustomResponseWriter); ok {
        return crw.statusCode
    }
    return http.StatusOK
}

// MetricsMiddleware 指标收集中间件
func MetricsMiddleware() martini.Handler {
    meter := otel.Meter("martini-metrics")
    
    // 创建指标
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("HTTP server requests"),
    )
    
    requestDuration, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP server request duration"),
        metric.WithUnit("ms"),
    )
    
    return func(req *http.Request, c martini.Context) {
        start := time.Now()
        
        c.Next()
        
        duration := time.Since(start).Milliseconds()
        
        // 获取 context (workaround)
        ctx := req.Context()
        if ctxVal := c.Get("__otel_context__"); ctxVal.IsValid() {
            if contextVal, ok := ctxVal.Interface().(context.Context); ok {
                ctx = contextVal
            }
        }
        
        attrs := []attribute.KeyValue{
            attribute.String("http.method", req.Method),
            attribute.String("http.route", req.URL.Path),
        }
        
        requestCounter.Add(ctx, 1, metric.WithAttributes(attrs...))
        requestDuration.Record(ctx, float64(duration), metric.WithAttributes(attrs...))
    }
}
```

---

## 3. 完整示例

### 3.1 基础服务

```go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "os"
    "os/signal"
    "syscall"
    "time"
    
    "github.com/go-martini/martini"
    "your-project/middleware"
)

func main() {
    // 初始化 OTLP
    ctx := context.Background()
    tp, err := initOTLP(ctx)
    if err != nil {
        log.Fatalf("Failed to initialize OTLP: %v", err)
    }
    defer func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }()
    
    // 创建 Martini 实例
    m := martini.Classic()
    
    // 注册中间件
    m.Use(middleware.TracingMiddleware("martini-service"))
    m.Use(middleware.MetricsMiddleware())
    
    // 注册路由
    setupRoutes(m)
    
    // 启动服务器
    port := ":8080"
    log.Printf("Starting server on %s", port)
    
    // 优雅关闭
    go func() {
        if err := http.ListenAndServe(port, m); err != nil {
            log.Fatalf("Server failed: %v", err)
        }
    }()
    
    // 等待中断信号
    quit := make(chan os.Signal, 1)
    signal.Notify(quit, syscall.SIGINT, syscall.SIGTERM)
    <-quit
    
    log.Println("Shutting down server...")
}

func setupRoutes(m *martini.ClassicMartini) {
    // 健康检查
    m.Get("/health", func() string {
        return "OK"
    })
    
    // 用户 API
    m.Get("/users/:id", getUser)
    m.Post("/users", createUser)
    m.Put("/users/:id", updateUser)
    m.Delete("/users/:id", deleteUser)
    
    // 带追踪的复杂操作
    m.Get("/orders/:id", getOrder)
}

// ⚠️ Martini handler 的限制
func getUser(params martini.Params) string {
    // ❌ 无法获取 context.Context
    // ❌ 无法创建子 span
    
    userID := params["id"]
    
    // 模拟数据库查询
    time.Sleep(10 * time.Millisecond)
    
    return fmt.Sprintf(`{"id": "%s", "name": "User %s"}`, userID, userID)
}

func createUser() string {
    return `{"id": "123", "name": "New User"}`
}

func updateUser(params martini.Params) string {
    return fmt.Sprintf(`{"id": "%s", "updated": true}`, params["id"])
}

func deleteUser(params martini.Params) string {
    return fmt.Sprintf(`{"id": "%s", "deleted": true}`, params["id"])
}

func getOrder(params martini.Params) string {
    orderID := params["id"]
    return fmt.Sprintf(`{"order_id": "%s", "status": "shipped"}`, orderID)
}
```

### 3.2 中间件栈

```go
// ❌ Martini 的中间件限制

// 1. 无法传递 context
m.Use(func(c martini.Context) {
    // ❌ 无法创建带 timeout 的 context
    // ❌ 无法取消操作
    c.Next()
})

// 2. 错误处理困难
m.Use(func(res http.ResponseWriter, req *http.Request) {
    // ❌ 无法捕获 panic
    // ❌ 无法统一错误格式
})

// 3. 性能问题
m.Use(func(c martini.Context, req *http.Request) {
    // ❌ 每次请求都会通过反射注入依赖
    // 性能损失 3-5x
})
```

---

## 4. 迁移到现代框架

### 4.1 迁移到 Chi

```go
// ✅ Chi - 最平滑的迁移路径

package main

import (
    "net/http"
    
    "github.com/go-chi/chi/v5"
    "github.com/go-chi/chi/v5/middleware"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
)

func main() {
    r := chi.NewRouter()
    
    // 标准中间件
    r.Use(middleware.Logger)
    r.Use(middleware.Recoverer)
    
    // OTLP 中间件 - 原生支持 context
    r.Use(func(next http.Handler) http.Handler {
        return otelhttp.NewHandler(next, "chi-service")
    })
    
    // 路由 - API 几乎相同
    r.Get("/users/{id}", getUserChi)
    r.Post("/users", createUserChi)
    
    http.ListenAndServe(":8080", r)
}

// ✅ 完整的 context 支持
func getUserChi(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context() // ✅ 获取 context
    userID := chi.URLParam(r, "id")
    
    // ✅ 可以创建子 span
    tracer := otel.Tracer("chi-service")
    ctx, span := tracer.Start(ctx, "get-user-from-db")
    defer span.End()
    
    // 使用 context 进行数据库查询
    user, err := fetchUserFromDB(ctx, userID)
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    json.NewEncoder(w).Encode(user)
}
```

### 4.2 迁移到 Echo

```go
// ✅ Echo - 高性能选择

package main

import (
    "github.com/labstack/echo/v4"
    "github.com/labstack/echo/v4/middleware"
    "go.opentelemetry.io/contrib/instrumentation/github.com/labstack/echo/otelecho"
)

func main() {
    e := echo.New()
    
    // 中间件
    e.Use(middleware.Logger())
    e.Use(middleware.Recover())
    e.Use(otelecho.Middleware("echo-service"))
    
    // 路由
    e.GET("/users/:id", getUserEcho)
    e.POST("/users", createUserEcho)
    
    e.Start(":8080")
}

// ✅ Echo 的优势
func getUserEcho(c echo.Context) error {
    ctx := c.Request().Context() // ✅ 原生 context
    userID := c.Param("id")
    
    // ✅ 创建子 span
    tracer := otel.Tracer("echo-service")
    ctx, span := tracer.Start(ctx, "get-user")
    defer span.End()
    
    // ✅ 内置绑定和验证
    var req struct {
        ID string `param:"id" validate:"required,uuid"`
    }
    if err := c.Bind(&req); err != nil {
        return c.JSON(400, map[string]string{"error": err.Error()})
    }
    
    user, err := fetchUserFromDB(ctx, userID)
    if err != nil {
        span.RecordError(err)
        return c.JSON(500, map[string]string{"error": err.Error()})
    }
    
    return c.JSON(200, user)
}
```

---

## 5. 总结

### 5.1 Martini 的遗产

```text
✅ 积极影响:
  - 引入了依赖注入概念
  - 优雅的中间件 API 设计
  - 影响了后续框架的设计

❌ 技术债务:
  - 过度使用反射导致性能问题
  - 不支持 context.Context
  - 维护停止，安全漏洞无人修复
  - 不支持现代 Go 特性（泛型、PGO等）
```

### 5.2 现代替代方案

```text
┌─────────────┬──────────┬──────────┬────────────┬────────────┐
│   框架      │  性能    │ 生态     │ 学习曲线   │ 推荐指数   │
├─────────────┼──────────┼──────────┼────────────┼────────────┤
│ Chi         │  ⭐⭐⭐⭐  │  ⭐⭐⭐   │    低      │   ⭐⭐⭐⭐⭐  │
│ Echo        │  ⭐⭐⭐⭐⭐ │  ⭐⭐⭐⭐  │    中      │   ⭐⭐⭐⭐⭐  │
│ Gin         │  ⭐⭐⭐⭐⭐ │  ⭐⭐⭐⭐⭐ │    低      │   ⭐⭐⭐⭐⭐  │
│ Fiber       │  ⭐⭐⭐⭐⭐ │  ⭐⭐⭐⭐  │    中      │   ⭐⭐⭐⭐   │
│ Martini     │  ⭐⭐     │  ⭐      │    低      │   ❌       │
└─────────────┴──────────┴──────────┴────────────┴────────────┘
```

**迁移建议**：

1. **新项目**: 使用 Chi、Echo 或 Gin
2. **遗留系统**: 逐步迁移到现代框架
3. **性能敏感**: 选择 Fiber 或 Echo
4. **生态完整**: 选择 Gin 或 Echo

**相关文档**：

- [49_Chi框架深度集成与最佳实践.md](../49_Chi框架深度集成与最佳实践.md)
- [09_Go主流框架深度集成指南.md](../09_Go主流框架深度集成指南.md)
- [50_现代Go架构模式_Clean_Architecture.md](../50_现代Go架构模式_Clean_Architecture.md)

---

**更新日期**: 2025-10-11  
**文档状态**: ⚠️ 归档参考  
**推荐替代**: Chi v5, Echo v4, Gin v1.10  
**维护状态**: Martini 已停止维护

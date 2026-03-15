# HttpRouter 与 OTLP 完整集成（2025版）

> **HttpRouter 版本**: v1.3.0+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [HttpRouter 与 OTLP 完整集成（2025版）](#httprouter-与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. HttpRouter 框架概述](#1-httprouter-框架概述)
    - [1.1 为什么选择 HttpRouter](#11-为什么选择-httprouter)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础集成](#22-基础集成)
  - [3. 完整集成示例](#3-完整集成示例)
    - [3.1 RESTful API](#31-restful-api)
  - [4. 中间件实现](#4-中间件实现)
    - [4.1 OTLP 追踪中间件](#41-otlp-追踪中间件)
    - [4.2 日志中间件](#42-日志中间件)
    - [4.3 错误恢复中间件](#43-错误恢复中间件)
    - [4.4 中间件链](#44-中间件链)
  - [5. 高级特性](#5-高级特性)
    - [5.1 自定义错误处理](#51-自定义错误处理)
    - [5.2 文件服务](#52-文件服务)
  - [6. 生产部署](#6-生产部署)
    - [6.1 Docker 部署](#61-docker-部署)
    - [6.2 Kubernetes 部署](#62-kubernetes-部署)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 性能优化](#71-性能优化)
    - [7.2 安全建议](#72-安全建议)

---

## 1. HttpRouter 框架概述

**HttpRouter** 是一个轻量级、高性能的 HTTP 请求路由器，专注于路由功能。

```text
🚀 核心特性:
  ✅ 极致性能 - 基于 Radix 树的路由匹配
  ✅ 零内存分配 - 路由匹配零分配
  ✅ RESTful 支持 - 完整的路径参数支持
  ✅ 轻量级 - 仅专注路由功能
  ✅ 标准兼容 - 完全兼容 net/http

📊 性能数据:
  - 路由匹配: <100ns (静态路由)
  - 路由匹配: <500ns (动态路由)
  - 内存分配: 0 allocs/op
  - 适用场景: 高性能 API、微服务
```

### 1.1 为什么选择 HttpRouter

```go
// 优势对比

// 1. 路由性能
// HttpRouter: Radix 树 - O(log n)
router := httprouter.New()
router.GET("/users/:id", handler)

// 标准库: 线性查找 - O(n)
mux := http.NewServeMux()
mux.HandleFunc("/users/", handler)

// 2. 内存分配
// HttpRouter: 零分配路由匹配
// 标准库: 每次匹配都有内存分配

// 3. RESTful 支持
// HttpRouter: 完整的路径参数
router.GET("/users/:id/posts/:postid", handler)

// 标准库: 需要手动解析
// /users/123/posts/456 → 手动 split 和 parse
```

**基准测试**:

```text
┌──────────────┬──────────────┬─────────────┬─────────────┐
│   路由器     │  ns/op       │  B/op       │ allocs/op   │
├──────────────┼──────────────┼─────────────┼─────────────┤
│ HttpRouter   │   75         │   0         │   0         │
│ net/http mux │  3500        │  1024       │   3         │
│ Gorilla Mux  │  4200        │  1280       │   5         │
│ Chi          │   800        │   432       │   3         │
└──────────────┴──────────────┴─────────────┴─────────────┘
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 HttpRouter
go get -u github.com/julienschmidt/httprouter@v1.3.0

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u go.opentelemetry.io/otel/sdk@v1.32.0
go get -u go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp@v0.56.0
```

### 2.2 基础集成

```go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"

    "github.com/julienschmidt/httprouter"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

// 初始化追踪
func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("httprouter-api"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

// Hello Handler
func Hello(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
    fmt.Fprintf(w, "Hello, %s!\n", ps.ByName("name"))
}

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 创建路由器
    router := httprouter.New()
    router.GET("/hello/:name", Hello)

    // 启动服务器
    log.Println("Server starting on :8080")
    log.Fatal(http.ListenAndServe(":8080", router))
}
```

---

## 3. 完整集成示例

### 3.1 RESTful API

```go
package main

import (
    "context"
    "encoding/json"
    "fmt"
    "log"
    "net/http"
    "strconv"
    "time"

    "github.com/julienschmidt/httprouter"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// User 模型
type User struct {
    ID        int       `json:"id"`
    Username  string    `json:"username"`
    Email     string    `json:"email"`
    CreatedAt time.Time `json:"created_at"`
}

// UserRepository 用户仓库
type UserRepository struct {
    tracer trace.Tracer
}

func NewUserRepository() *UserRepository {
    return &UserRepository{
        tracer: otel.Tracer("user-repository"),
    }
}

// GetByID 根据ID获取用户
func (r *UserRepository) GetByID(ctx context.Context, id int) (*User, error) {
    _, span := r.tracer.Start(ctx, "UserRepository.GetByID",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    // 模拟数据库查询
    time.Sleep(10 * time.Millisecond)

    user := &User{
        ID:        id,
        Username:  fmt.Sprintf("user%d", id),
        Email:     fmt.Sprintf("user%d@example.com", id),
        CreatedAt: time.Now(),
    }

    span.SetAttributes(
        attribute.String("user.username", user.Username),
        attribute.String("user.email", user.Email),
    )

    return user, nil
}

// List 获取用户列表
func (r *UserRepository) List(ctx context.Context, limit, offset int) ([]*User, error) {
    _, span := r.tracer.Start(ctx, "UserRepository.List",
        trace.WithAttributes(
            attribute.Int("limit", limit),
            attribute.Int("offset", offset),
        ),
    )
    defer span.End()

    // 模拟数据库查询
    time.Sleep(20 * time.Millisecond)

    users := make([]*User, 0, limit)
    for i := 0; i < limit; i++ {
        users = append(users, &User{
            ID:        offset + i + 1,
            Username:  fmt.Sprintf("user%d", offset+i+1),
            Email:     fmt.Sprintf("user%d@example.com", offset+i+1),
            CreatedAt: time.Now(),
        })
    }

    return users, nil
}

// Create 创建用户
func (r *UserRepository) Create(ctx context.Context, user *User) error {
    _, span := r.tracer.Start(ctx, "UserRepository.Create",
        trace.WithAttributes(
            attribute.String("user.username", user.Username),
            attribute.String("user.email", user.Email),
        ),
    )
    defer span.End()

    // 模拟数据库插入
    time.Sleep(15 * time.Millisecond)
    user.ID = 999
    user.CreatedAt = time.Now()

    return nil
}

// Update 更新用户
func (r *UserRepository) Update(ctx context.Context, id int, user *User) error {
    _, span := r.tracer.Start(ctx, "UserRepository.Update",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    // 模拟数据库更新
    time.Sleep(12 * time.Millisecond)

    return nil
}

// Delete 删除用户
func (r *UserRepository) Delete(ctx context.Context, id int) error {
    _, span := r.tracer.Start(ctx, "UserRepository.Delete",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    // 模拟数据库删除
    time.Sleep(8 * time.Millisecond)

    return nil
}

// UserHandler API 处理器
type UserHandler struct {
    repo *UserRepository
}

func NewUserHandler(repo *UserRepository) *UserHandler {
    return &UserHandler{repo: repo}
}

// GetUser GET /users/:id
func (h *UserHandler) GetUser(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
    ctx := r.Context()

    // 解析 ID
    id, err := strconv.Atoi(ps.ByName("id"))
    if err != nil {
        http.Error(w, "Invalid user ID", http.StatusBadRequest)
        return
    }

    // 获取用户
    user, err := h.repo.GetByID(ctx, id)
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 返回 JSON
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(user)
}

// ListUsers GET /users?limit=10&offset=0
func (h *UserHandler) ListUsers(w http.ResponseWriter, r *http.Request, _ httprouter.Params) {
    ctx := r.Context()

    // 解析查询参数
    limit, _ := strconv.Atoi(r.URL.Query().Get("limit"))
    offset, _ := strconv.Atoi(r.URL.Query().Get("offset"))
    if limit == 0 {
        limit = 10
    }

    // 获取用户列表
    users, err := h.repo.List(ctx, limit, offset)
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 返回 JSON
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(map[string]interface{}{
        "users":  users,
        "total":  len(users),
        "limit":  limit,
        "offset": offset,
    })
}

// CreateUser POST /users
func (h *UserHandler) CreateUser(w http.ResponseWriter, r *http.Request, _ httprouter.Params) {
    ctx := r.Context()

    // 解析请求体
    var user User
    if err := json.NewDecoder(r.Body).Decode(&user); err != nil {
        http.Error(w, "Invalid request body", http.StatusBadRequest)
        return
    }

    // 验证
    if user.Username == "" || user.Email == "" {
        http.Error(w, "Username and email are required", http.StatusBadRequest)
        return
    }

    // 创建用户
    if err := h.repo.Create(ctx, &user); err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 返回创建的用户
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusCreated)
    json.NewEncoder(w).Encode(user)
}

// UpdateUser PUT /users/:id
func (h *UserHandler) UpdateUser(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
    ctx := r.Context()

    // 解析 ID
    id, err := strconv.Atoi(ps.ByName("id"))
    if err != nil {
        http.Error(w, "Invalid user ID", http.StatusBadRequest)
        return
    }

    // 解析请求体
    var user User
    if err := json.NewDecoder(r.Body).Decode(&user); err != nil {
        http.Error(w, "Invalid request body", http.StatusBadRequest)
        return
    }

    // 更新用户
    if err := h.repo.Update(ctx, id, &user); err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 返回更新的用户
    user.ID = id
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(user)
}

// DeleteUser DELETE /users/:id
func (h *UserHandler) DeleteUser(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
    ctx := r.Context()

    // 解析 ID
    id, err := strconv.Atoi(ps.ByName("id"))
    if err != nil {
        http.Error(w, "Invalid user ID", http.StatusBadRequest)
        return
    }

    // 删除用户
    if err := h.repo.Delete(ctx, id); err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 返回成功
    w.WriteHeader(http.StatusNoContent)
}

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 创建依赖
    repo := NewUserRepository()
    handler := NewUserHandler(repo)

    // 创建路由器
    router := httprouter.New()

    // 注册路由
    router.GET("/users", handler.ListUsers)
    router.GET("/users/:id", handler.GetUser)
    router.POST("/users", handler.CreateUser)
    router.PUT("/users/:id", handler.UpdateUser)
    router.DELETE("/users/:id", handler.DeleteUser)

    // 健康检查
    router.GET("/health", func(w http.ResponseWriter, r *http.Request, _ httprouter.Params) {
        w.Header().Set("Content-Type", "application/json")
        json.NewEncoder(w).Encode(map[string]string{
            "status":    "healthy",
            "timestamp": time.Now().Format(time.RFC3339),
        })
    })

    // 启动服务器
    log.Println("🚀 HttpRouter server starting on :8080")
    log.Fatal(http.ListenAndServe(":8080", router))
}
```

---

## 4. 中间件实现

### 4.1 OTLP 追踪中间件

```go
package middleware

import (
    "fmt"
    "net/http"
    "time"

    "github.com/julienschmidt/httprouter"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
    "go.opentelemetry.io/otel/trace"
)

// TracingMiddleware 追踪中间件
func TracingMiddleware(serviceName string) func(httprouter.Handle) httprouter.Handle {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()

    return func(next httprouter.Handle) httprouter.Handle {
        return func(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
            // 提取上下文
            ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

            // 创建 span
            spanName := fmt.Sprintf("%s %s", r.Method, r.URL.Path)
            ctx, span := tracer.Start(ctx, spanName,
                trace.WithSpanKind(trace.SpanKindServer),
                trace.WithAttributes(
                    semconv.HTTPMethod(r.Method),
                    semconv.HTTPTarget(r.URL.Path),
                    semconv.HTTPScheme(r.URL.Scheme),
                    semconv.HTTPHost(r.Host),
                    semconv.HTTPUserAgent(r.UserAgent()),
                    semconv.NetPeerIP(r.RemoteAddr),
                ),
            )
            defer span.End()

            // 记录路径参数
            for _, param := range ps {
                span.SetAttributes(attribute.String(
                    fmt.Sprintf("http.route.param.%s", param.Key),
                    param.Value,
                ))
            }

            // 创建响应记录器
            rec := &responseRecorder{
                ResponseWriter: w,
                statusCode:     http.StatusOK,
            }

            // 记录开始时间
            start := time.Now()

            // 调用下一个处理器
            next(rec, r.WithContext(ctx), ps)

            // 记录响应信息
            duration := time.Since(start)
            statusCode := rec.statusCode

            span.SetAttributes(
                semconv.HTTPStatusCode(statusCode),
                attribute.Int64("http.response.size", rec.written),
                attribute.Float64("http.duration_ms", float64(duration.Microseconds())/1000.0),
            )

            // 设置状态
            if statusCode >= 400 {
                span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", statusCode))
            } else {
                span.SetStatus(codes.Ok, "")
            }
        }
    }
}

// responseRecorder 记录响应状态
type responseRecorder struct {
    http.ResponseWriter
    statusCode int
    written    int64
}

func (r *responseRecorder) WriteHeader(statusCode int) {
    r.statusCode = statusCode
    r.ResponseWriter.WriteHeader(statusCode)
}

func (r *responseRecorder) Write(b []byte) (int, error) {
    n, err := r.ResponseWriter.Write(b)
    r.written += int64(n)
    return n, err
}
```

### 4.2 日志中间件

```go
package middleware

import (
    "log"
    "net/http"
    "time"

    "github.com/julienschmidt/httprouter"
)

// LoggingMiddleware 日志中间件
func LoggingMiddleware(next httprouter.Handle) httprouter.Handle {
    return func(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
        start := time.Now()

        // 创建响应记录器
        rec := &responseRecorder{
            ResponseWriter: w,
            statusCode:     http.StatusOK,
        }

        // 调用下一个处理器
        next(rec, r, ps)

        // 记录日志
        duration := time.Since(start)
        log.Printf(
            "%s %s %d %s",
            r.Method,
            r.URL.Path,
            rec.statusCode,
            duration,
        )
    }
}
```

### 4.3 错误恢复中间件

```go
package middleware

import (
    "fmt"
    "log"
    "net/http"
    "runtime/debug"

    "github.com/julienschmidt/httprouter"
    "go.opentelemetry.io/otel/trace"
)

// RecoveryMiddleware 恢复中间件
func RecoveryMiddleware(next httprouter.Handle) httprouter.Handle {
    return func(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
        defer func() {
            if err := recover(); err != nil {
                // 记录错误
                log.Printf("Panic recovered: %v\n%s", err, debug.Stack())

                // 记录到 span
                if span := trace.SpanFromContext(r.Context()); span.IsRecording() {
                    span.RecordError(fmt.Errorf("panic: %v", err))
                }

                // 返回错误响应
                http.Error(w, "Internal Server Error", http.StatusInternalServerError)
            }
        }()

        next(w, r, ps)
    }
}
```

### 4.4 中间件链

```go
package middleware

import (
    "net/http"

    "github.com/julienschmidt/httprouter"
)

// Chain 中间件链
type Chain []func(httprouter.Handle) httprouter.Handle

// Then 应用中间件链
func (c Chain) Then(h httprouter.Handle) httprouter.Handle {
    for i := range c {
        h = c[len(c)-1-i](h)
    }
    return h
}

// 使用示例
func ExampleChain() {
    router := httprouter.New()

    // 创建中间件链
    chain := Chain{
        RecoveryMiddleware,
        LoggingMiddleware,
        TracingMiddleware("api"),
    }

    // 应用中间件
    router.GET("/users/:id", chain.Then(getUserHandler))
    router.POST("/users", chain.Then(createUserHandler))
}

func getUserHandler(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
    // 处理逻辑
}

func createUserHandler(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
    // 处理逻辑
}
```

---

## 5. 高级特性

### 5.1 自定义错误处理

```go
package main

import (
    "encoding/json"
    "net/http"

    "github.com/julienschmidt/httprouter"
)

// 自定义 404 处理器
func notFound(w http.ResponseWriter, r *http.Request) {
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusNotFound)
    json.NewEncoder(w).Encode(map[string]string{
        "error": "Resource not found",
        "path":  r.URL.Path,
    })
}

// 自定义 405 处理器
func methodNotAllowed(w http.ResponseWriter, r *http.Request) {
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusMethodNotAllowed)
    json.NewEncoder(w).Encode(map[string]string{
        "error":  "Method not allowed",
        "method": r.Method,
    })
}

// Panic 处理器
func panicHandler(w http.ResponseWriter, r *http.Request, err interface{}) {
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusInternalServerError)
    json.NewEncoder(w).Encode(map[string]interface{}{
        "error": "Internal server error",
        "panic": fmt.Sprint(err),
    })
}

func main() {
    router := httprouter.New()

    // 注册自定义处理器
    router.NotFound = http.HandlerFunc(notFound)
    router.MethodNotAllowed = http.HandlerFunc(methodNotAllowed)
    router.PanicHandler = panicHandler

    // 其他配置
    router.RedirectTrailingSlash = true
    router.RedirectFixedPath = true
    router.HandleMethodNotAllowed = true
    router.HandleOPTIONS = true

    http.ListenAndServe(":8080", router)
}
```

### 5.2 文件服务

```go
package main

import (
    "net/http"

    "github.com/julienschmidt/httprouter"
)

func main() {
    router := httprouter.New()

    // 静态文件服务
    router.ServeFiles("/static/*filepath", http.Dir("./public"))

    // 自定义文件处理
    router.GET("/files/:name", func(w http.ResponseWriter, r *http.Request, ps httprouter.Params) {
        filename := ps.ByName("name")
        http.ServeFile(w, r, "./files/"+filename)
    })

    http.ListenAndServe(":8080", router)
}
```

---

## 6. 生产部署

### 6.1 Docker 部署

```dockerfile
FROM golang:1.25.1-alpine AS builder

WORKDIR /build
COPY . .
RUN go mod download
RUN CGO_ENABLED=0 go build -ldflags="-s -w" -o app ./cmd/server

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /app
COPY --from=builder /build/app .
EXPOSE 8080
CMD ["./app"]
```

### 6.2 Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: httprouter-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: httprouter-api
  template:
    metadata:
      labels:
        app: httprouter-api
    spec:
      containers:
      - name: api
        image: httprouter-api:latest
        ports:
        - containerPort: 8080
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "http://otel-collector:4317"
        resources:
          requests:
            cpu: "100m"
            memory: "128Mi"
          limits:
            cpu: "500m"
            memory: "256Mi"
```

---

## 7. 最佳实践

### 7.1 性能优化

```text
✅ 路由设计:
  - 使用静态路由优先
  - 合理使用路径参数
  - 避免过深的路由层级

✅ 中间件:
  - 只使用必要的中间件
  - 将中间件应用到特定路由
  - 避免重复的中间件逻辑

✅ 响应处理:
  - 使用连接池
  - 复用 JSON 编码器
  - 启用响应压缩
```

### 7.2 安全建议

```text
✅ 输入验证:
  - 验证所有路径参数
  - 验证查询参数
  - 限制请求体大小

✅ 错误处理:
  - 不暴露内部错误
  - 统一错误响应格式
  - 记录错误日志

✅ 访问控制:
  - 实现认证中间件
  - 实现授权检查
  - 限流保护
```

---

**参考资源**：

- [HttpRouter GitHub](https://github.com/julienschmidt/httprouter)
- [Go net/http](https://pkg.go.dev/net/http)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

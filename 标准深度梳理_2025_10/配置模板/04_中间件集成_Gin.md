# Gin + GORM + Redis 完整 OTLP 集成

> **场景**: Gin Web 服务 + GORM 数据库 + Redis 缓存  
> **特点**: 全自动追踪、零侵入、生产级配置  
> **难度**: ⭐⭐  

---

## 快速开始

```go:main.go
package main

import (
    "context"
    "log"

    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin"
    "go.opentelemetry.io/otel"
    "gorm.io/driver/postgres"
    "gorm.io/gorm"
    "gorm.io/plugin/opentelemetry/tracing"
    "github.com/redis/go-redis/extra/redisotel/v9"
    "github.com/redis/go-redis/v9"
)

func main() {
    ctx := context.Background()

    // 1. 初始化 Telemetry
    shutdown, err := initTelemetry(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer shutdown(ctx)

    // 2. 初始化 GORM (自动追踪)
    db, err := gorm.Open(postgres.Open("host=localhost user=postgres password=password dbname=mydb"), &gorm.Config{})
    if err != nil {
        log.Fatal(err)
    }
    if err := db.Use(tracing.NewPlugin()); err != nil {
        log.Fatal(err)
    }

    // 3. 初始化 Redis (自动追踪)
    rdb := redis.NewClient(&redis.Options{Addr: "localhost:6379"})
    if err := redisotel.InstrumentTracing(rdb); err != nil {
        log.Fatal(err)
    }

    // 4. 创建 Gin Router
    router := gin.New()
    router.Use(otelgin.Middleware("my-service"))  // OpenTelemetry 中间件

    // 5. 定义路由
    router.GET("/users/:id", func(c *gin.Context) {
        ctx := c.Request.Context()
        
        // GORM 查询（自动追踪）
        var user User
        db.WithContext(ctx).First(&user, c.Param("id"))

        // Redis 缓存（自动追踪）
        rdb.Get(ctx, "user:"+c.Param("id"))

        c.JSON(200, user)
    })

    router.Run(":8080")
}
```

---

## 依赖安装

```bash
go get go.opentelemetry.io/otel
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc
go get go.opentelemetry.io/otel/sdk
go get go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin
go get gorm.io/plugin/opentelemetry/tracing
go get github.com/redis/go-redis/extra/redisotel/v9
```

---

## 完整示例

### 1. Telemetry 初始化

```go:pkg/telemetry/init.go
package telemetry

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func Init(ctx context.Context, serviceName string) (func(context.Context) error, error) {
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String(serviceName),
        ),
    )
    if err != nil {
        return nil, err
    }

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.TraceContext{})

    return tp.Shutdown, nil
}
```

### 2. HTTP Handler

```go:internal/handler/user.go
package handler

import (
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

var tracer = otel.Tracer("user-handler")

type UserHandler struct {
    service *UserService
}

func (h *UserHandler) GetUser(c *gin.Context) {
    ctx := c.Request.Context()
    
    // 创建子 Span
    ctx, span := tracer.Start(ctx, "handler.GetUser")
    defer span.End()

    userID := c.Param("id")
    span.SetAttributes(attribute.String("user.id", userID))

    // 调用 Service（会创建子 Span）
    user, err := h.service.GetUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        c.JSON(500, gin.H{"error": err.Error()})
        return
    }

    c.JSON(200, user)
}
```

### 3. Service Layer

```go:internal/service/user.go
package service

import (
    "context"
    "go.opentelemetry.io/otel"
    "gorm.io/gorm"
    "github.com/redis/go-redis/v9"
)

var tracer = otel.Tracer("user-service")

type UserService struct {
    db  *gorm.DB
    rdb *redis.Client
}

func (s *UserService) GetUser(ctx context.Context, userID string) (*User, error) {
    ctx, span := tracer.Start(ctx, "service.GetUser")
    defer span.End()

    // 1. 先查 Redis 缓存（自动追踪）
    if cached, err := s.rdb.Get(ctx, "user:"+userID).Result(); err == nil {
        span.AddEvent("cache_hit")
        return parseUser(cached), nil
    }

    // 2. 查询数据库（自动追踪）
    var user User
    if err := s.db.WithContext(ctx).First(&user, userID).Error; err != nil {
        return nil, err
    }

    // 3. 写入缓存
    s.rdb.Set(ctx, "user:"+userID, user, 5*time.Minute)

    return &user, nil
}
```

---

## 效果展示

### Trace 链路

```text
GET /users/123
├─ handler.GetUser (10ms)
│  └─ service.GetUser (8ms)
│     ├─ redis.GET user:123 (1ms) [cache_hit]
│     └─ db.SELECT * FROM users WHERE id=123 (5ms)
└─ response (200 OK)
```

### Jaeger UI 截图

```text
Service: my-service
Operation: GET /users/:id
Duration: 10.5ms
Spans: 4
Status: OK

Span Details:
1. GET /users/:id (10.5ms)
   - http.method: GET
   - http.route: /users/:id
   - http.status_code: 200

2. handler.GetUser (10ms)
   - user.id: 123

3. service.GetUser (8ms)
   - cache_hit: true

4. redis.GET (1ms)
   - db.system: redis
   - db.statement: GET user:123
```

---

## 最佳实践

### 1. 错误处理

```go
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
    return err
}
```

### 2. 自定义属性

```go
span.SetAttributes(
    attribute.String("user.id", userID),
    attribute.String("user.role", user.Role),
    attribute.Int("query.limit", limit),
)
```

### 3. 事件记录

```go
span.AddEvent("cache_miss")
span.AddEvent("db_query_slow", trace.WithAttributes(
    attribute.Int64("duration_ms", duration),
))
```

---

## 常见问题

### Q: 如何追踪外部 HTTP 调用？

```go
import "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

client := &http.Client{
    Transport: otelhttp.NewTransport(http.DefaultTransport),
}
```

### Q: 如何自定义 Span 名称？

```go
router.Use(otelgin.Middleware("my-service",
    otelgin.WithSpanNameFormatter(func(r *http.Request) string {
        return r.Method + " " + r.URL.Path
    }),
))
```

---

**🎊 完成！** 您的 Gin 应用现在已经有完整的 OTLP 集成了！

- 📚 [Echo 集成](./04_中间件集成_Echo.md)
- 📚 [实战案例](../实战案例/)

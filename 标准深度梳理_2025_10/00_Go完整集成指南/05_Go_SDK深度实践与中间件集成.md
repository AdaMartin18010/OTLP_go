# Go SDK 深度实践与中间件集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry Go SDK**: v1.24.0+  
> **最后更新**: 2025年10月8日

---

## 目录

- [Go SDK 深度实践与中间件集成](#go-sdk-深度实践与中间件集成)
  - [目录](#目录)
  - [1. HTTP 中间件集成](#1-http-中间件集成)
    - [1.1 标准库 net/http 集成](#11-标准库-nethttp-集成)
    - [1.2 Gin 框架集成](#12-gin-框架集成)
    - [1.3 Echo 框架集成](#13-echo-框架集成)
  - [2. gRPC 拦截器集成](#2-grpc-拦截器集成)
    - [2.1 Unary 拦截器](#21-unary-拦截器)
    - [2.2 Stream 拦截器](#22-stream-拦截器)
    - [2.3 完整使用示例](#23-完整使用示例)
  - [3. 数据库追踪集成](#3-数据库追踪集成)
    - [3.1 database/sql 集成](#31-databasesql-集成)
    - [3.2 GORM 集成](#32-gorm-集成)
    - [3.3 Redis 集成](#33-redis-集成)
  - [4. 消息队列集成](#4-消息队列集成)
    - [4.1 Kafka 集成](#41-kafka-集成)
    - [4.2 RabbitMQ 集成](#42-rabbitmq-集成)
  - [5. Context 传播深度实践](#5-context-传播深度实践)
    - [5.1 HTTP 跨服务传播](#51-http-跨服务传播)
    - [5.2 完整的微服务追踪示例](#52-完整的微服务追踪示例)
  - [6. 自定义 Instrumentation](#6-自定义-instrumentation)
    - [6.1 自定义 Span 处理器](#61-自定义-span-处理器)
    - [6.2 自定义采样器](#62-自定义采样器)
  - [7. 错误处理模式](#7-错误处理模式)
    - [7.1 标准错误处理](#71-标准错误处理)
    - [7.2 Panic 恢复](#72-panic-恢复)
  - [8. 高级配置](#8-高级配置)
    - [8.1 动态采样](#81-动态采样)
    - [8.2 批处理优化](#82-批处理优化)
  - [总结](#总结)

---

## 1. HTTP 中间件集成

### 1.1 标准库 net/http 集成

**自动追踪中间件**：

```go
package middleware

import (
    "net/http"
    "time"

    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/semconv/v1.24.0/httpconv"
    "go.opentelemetry.io/otel/trace"
)

// HTTPMiddleware HTTP 追踪中间件
func HTTPMiddleware(next http.Handler) http.Handler {
    return otelhttp.NewHandler(
        next,
        "http-server",
        otelhttp.WithSpanOptions(
            trace.WithSpanKind(trace.SpanKindServer),
        ),
        otelhttp.WithMessageEvents(otelhttp.ReadEvents, otelhttp.WriteEvents),
    )
}

// CustomHTTPMiddleware 自定义 HTTP 中间件
func CustomHTTPMiddleware(next http.Handler) http.Handler {
    tracer := otel.Tracer("http-middleware")
    propagator := otel.GetTextMapPropagator()

    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 1. 提取上下文
        ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

        // 2. 创建 Span
        ctx, span := tracer.Start(ctx, r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                httpconv.ServerRequest("", r)...,
            ),
        )
        defer span.End()

        // 3. 包装 ResponseWriter 以捕获状态码
        rw := &responseWriter{
            ResponseWriter: w,
            statusCode:     http.StatusOK,
        }

        // 4. 执行处理器
        start := time.Now()
        next.ServeHTTP(rw, r.WithContext(ctx))
        duration := time.Since(start)

        // 5. 记录响应信息
        span.SetAttributes(
            attribute.Int("http.status_code", rw.statusCode),
            attribute.Int64("http.response.size", rw.written),
            attribute.Float64("http.duration_ms", float64(duration.Milliseconds())),
        )

        // 6. 设置状态
        if rw.statusCode >= 400 {
            span.SetStatus(codes.Error, http.StatusText(rw.statusCode))
        } else {
            span.SetStatus(codes.Ok, "")
        }

        // 7. 注入响应头（用于客户端追踪）
        propagator.Inject(ctx, propagation.HeaderCarrier(w.Header()))
    })
}

// responseWriter 响应写入器包装
type responseWriter struct {
    http.ResponseWriter
    statusCode int
    written    int64
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    n, err := rw.ResponseWriter.Write(b)
    rw.written += int64(n)
    return n, err
}
```

**使用示例**：

```go
package main

import (
    "fmt"
    "net/http"

    "go.opentelemetry.io/otel"
)

func main() {
    // 初始化 OpenTelemetry (省略)
    
    mux := http.NewServeMux()
    
    // 注册处理器
    mux.HandleFunc("/api/users", handleUsers)
    mux.HandleFunc("/api/orders", handleOrders)
    
    // 应用中间件
    handler := middleware.CustomHTTPMiddleware(mux)
    
    // 启动服务器
    http.ListenAndServe(":8080", handler)
}

func handleUsers(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("users-handler")
    
    // 创建子 Span
    ctx, span := tracer.Start(ctx, "fetch-users")
    defer span.End()
    
    // 业务逻辑
    users := fetchUsers(ctx)
    
    // 记录信息
    span.SetAttributes(
        attribute.Int("user.count", len(users)),
    )
    
    fmt.Fprintf(w, "Users: %v", users)
}
```

### 1.2 Gin 框架集成

**Gin 中间件**：

```go
package ginmiddleware

import (
    "time"

    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// OTelMiddleware Gin OpenTelemetry 中间件
func OTelMiddleware(serviceName string) gin.HandlerFunc {
    // 使用官方中间件
    return otelgin.Middleware(serviceName)
}

// CustomGinMiddleware 自定义 Gin 中间件
func CustomGinMiddleware(serviceName string) gin.HandlerFunc {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()

    return func(c *gin.Context) {
        // 1. 提取上下文
        ctx := propagator.Extract(c.Request.Context(), 
            propagation.HeaderCarrier(c.Request.Header))

        // 2. 创建 Span
        spanName := c.Request.Method + " " + c.FullPath()
        ctx, span := tracer.Start(ctx, spanName,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("http.method", c.Request.Method),
                attribute.String("http.url", c.Request.URL.String()),
                attribute.String("http.route", c.FullPath()),
                attribute.String("http.client_ip", c.ClientIP()),
                attribute.String("http.user_agent", c.Request.UserAgent()),
            ),
        )
        defer span.End()

        // 3. 设置 Context
        c.Request = c.Request.WithContext(ctx)

        // 4. 执行处理器
        start := time.Now()
        c.Next()
        duration := time.Since(start)

        // 5. 记录响应信息
        span.SetAttributes(
            attribute.Int("http.status_code", c.Writer.Status()),
            attribute.Int("http.response.size", c.Writer.Size()),
            attribute.Float64("http.duration_ms", float64(duration.Milliseconds())),
        )

        // 6. 处理错误
        if len(c.Errors) > 0 {
            span.RecordError(c.Errors.Last())
            span.SetStatus(codes.Error, c.Errors.Last().Error())
        } else if c.Writer.Status() >= 400 {
            span.SetStatus(codes.Error, http.StatusText(c.Writer.Status()))
        } else {
            span.SetStatus(codes.Ok, "")
        }

        // 7. 注入响应头
        propagator.Inject(ctx, propagation.HeaderCarrier(c.Writer.Header()))
    }
}
```

**Gin 使用示例**：

```go
package main

import (
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

func main() {
    // 初始化 OpenTelemetry (省略)
    
    r := gin.Default()
    
    // 应用中间件
    r.Use(ginmiddleware.CustomGinMiddleware("my-service"))
    
    // 注册路由
    r.GET("/api/users/:id", getUser)
    r.POST("/api/users", createUser)
    
    r.Run(":8080")
}

func getUser(c *gin.Context) {
    ctx := c.Request.Context()
    tracer := otel.Tracer("user-handler")
    
    userID := c.Param("id")
    
    // 创建子 Span
    ctx, span := tracer.Start(ctx, "get-user")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("user.id", userID),
    )
    
    // 业务逻辑
    user := fetchUser(ctx, userID)
    
    c.JSON(200, user)
}
```

### 1.3 Echo 框架集成

```go
package echomiddleware

import (
    "github.com/labstack/echo/v4"
    "go.opentelemetry.io/contrib/instrumentation/github.com/labstack/echo/otelecho"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// OTelMiddleware Echo OpenTelemetry 中间件
func OTelMiddleware(serviceName string) echo.MiddlewareFunc {
    return otelecho.Middleware(serviceName)
}

// CustomEchoMiddleware 自定义 Echo 中间件
func CustomEchoMiddleware(serviceName string) echo.MiddlewareFunc {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()

    return func(next echo.HandlerFunc) echo.HandlerFunc {
        return func(c echo.Context) error {
            req := c.Request()
            
            // 提取上下文
            ctx := propagator.Extract(req.Context(), 
                propagation.HeaderCarrier(req.Header))

            // 创建 Span
            spanName := req.Method + " " + c.Path()
            ctx, span := tracer.Start(ctx, spanName,
                trace.WithSpanKind(trace.SpanKindServer),
                trace.WithAttributes(
                    attribute.String("http.method", req.Method),
                    attribute.String("http.url", req.URL.String()),
                    attribute.String("http.route", c.Path()),
                ),
            )
            defer span.End()

            // 设置 Context
            c.SetRequest(req.WithContext(ctx))

            // 执行处理器
            err := next(c)

            // 记录响应
            status := c.Response().Status
            span.SetAttributes(
                attribute.Int("http.status_code", status),
                attribute.Int64("http.response.size", c.Response().Size),
            )

            if err != nil {
                span.RecordError(err)
                span.SetStatus(codes.Error, err.Error())
                return err
            }

            if status >= 400 {
                span.SetStatus(codes.Error, http.StatusText(status))
            } else {
                span.SetStatus(codes.Ok, "")
            }

            return nil
        }
    }
}
```

---

## 2. gRPC 拦截器集成

### 2.1 Unary 拦截器

**服务器端拦截器**：

```go
package grpcinterceptor

import (
    "context"
    "time"

    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    "google.golang.org/grpc/status"
)

// UnaryServerInterceptor Unary 服务器拦截器
func UnaryServerInterceptor() grpc.UnaryServerInterceptor {
    return otelgrpc.UnaryServerInterceptor()
}

// CustomUnaryServerInterceptor 自定义 Unary 服务器拦截器
func CustomUnaryServerInterceptor(serviceName string) grpc.UnaryServerInterceptor {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()

    return func(
        ctx context.Context,
        req interface{},
        info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler,
    ) (interface{}, error) {
        // 1. 提取元数据
        md, _ := metadata.FromIncomingContext(ctx)
        ctx = propagator.Extract(ctx, &metadataCarrier{md: md})

        // 2. 创建 Span
        ctx, span := tracer.Start(ctx, info.FullMethod,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("rpc.system", "grpc"),
                attribute.String("rpc.service", info.FullMethod),
                attribute.String("rpc.method", info.FullMethod),
            ),
        )
        defer span.End()

        // 3. 执行处理器
        start := time.Now()
        resp, err := handler(ctx, req)
        duration := time.Since(start)

        // 4. 记录指标
        span.SetAttributes(
            attribute.Float64("rpc.duration_ms", float64(duration.Milliseconds())),
        )

        // 5. 处理错误
        if err != nil {
            span.RecordError(err)
            st, _ := status.FromError(err)
            span.SetStatus(codes.Error, st.Message())
            span.SetAttributes(
                attribute.Int("rpc.grpc.status_code", int(st.Code())),
            )
        } else {
            span.SetStatus(codes.Ok, "")
        }

        return resp, err
    }
}

// metadataCarrier 元数据载体
type metadataCarrier struct {
    md metadata.MD
}

func (c *metadataCarrier) Get(key string) string {
    values := c.md.Get(key)
    if len(values) == 0 {
        return ""
    }
    return values[0]
}

func (c *metadataCarrier) Set(key, value string) {
    c.md.Set(key, value)
}

func (c *metadataCarrier) Keys() []string {
    keys := make([]string, 0, len(c.md))
    for k := range c.md {
        keys = append(keys, k)
    }
    return keys
}
```

**客户端拦截器**：

```go
// UnaryClientInterceptor Unary 客户端拦截器
func UnaryClientInterceptor() grpc.UnaryClientInterceptor {
    return otelgrpc.UnaryClientInterceptor()
}

// CustomUnaryClientInterceptor 自定义 Unary 客户端拦截器
func CustomUnaryClientInterceptor(serviceName string) grpc.UnaryClientInterceptor {
    tracer := otel.Tracer(serviceName)
    propagator := otel.GetTextMapPropagator()

    return func(
        ctx context.Context,
        method string,
        req, reply interface{},
        cc *grpc.ClientConn,
        invoker grpc.UnaryInvoker,
        opts ...grpc.CallOption,
    ) error {
        // 1. 创建 Span
        ctx, span := tracer.Start(ctx, method,
            trace.WithSpanKind(trace.SpanKindClient),
            trace.WithAttributes(
                attribute.String("rpc.system", "grpc"),
                attribute.String("rpc.service", method),
                attribute.String("rpc.method", method),
                attribute.String("net.peer.name", cc.Target()),
            ),
        )
        defer span.End()

        // 2. 注入上下文
        md, ok := metadata.FromOutgoingContext(ctx)
        if !ok {
            md = metadata.New(nil)
        } else {
            md = md.Copy()
        }
        
        carrier := &metadataCarrier{md: md}
        propagator.Inject(ctx, carrier)
        ctx = metadata.NewOutgoingContext(ctx, md)

        // 3. 调用
        start := time.Now()
        err := invoker(ctx, method, req, reply, cc, opts...)
        duration := time.Since(start)

        // 4. 记录指标
        span.SetAttributes(
            attribute.Float64("rpc.duration_ms", float64(duration.Milliseconds())),
        )

        // 5. 处理错误
        if err != nil {
            span.RecordError(err)
            st, _ := status.FromError(err)
            span.SetStatus(codes.Error, st.Message())
            span.SetAttributes(
                attribute.Int("rpc.grpc.status_code", int(st.Code())),
            )
        } else {
            span.SetStatus(codes.Ok, "")
        }

        return err
    }
}
```

### 2.2 Stream 拦截器

```go
// StreamServerInterceptor Stream 服务器拦截器
func StreamServerInterceptor() grpc.StreamServerInterceptor {
    return otelgrpc.StreamServerInterceptor()
}

// StreamClientInterceptor Stream 客户端拦截器
func StreamClientInterceptor() grpc.StreamClientInterceptor {
    return otelgrpc.StreamClientInterceptor()
}
```

### 2.3 完整使用示例

```go
package main

import (
    "google.golang.org/grpc"
)

// 服务器端
func NewServer() *grpc.Server {
    return grpc.NewServer(
        grpc.UnaryInterceptor(grpcinterceptor.CustomUnaryServerInterceptor("my-service")),
        grpc.StreamInterceptor(grpcinterceptor.StreamServerInterceptor()),
    )
}

// 客户端
func NewClient(target string) (*grpc.ClientConn, error) {
    return grpc.Dial(target,
        grpc.WithUnaryInterceptor(grpcinterceptor.CustomUnaryClientInterceptor("my-client")),
        grpc.WithStreamInterceptor(grpcinterceptor.StreamClientInterceptor()),
    )
}
```

---

## 3. 数据库追踪集成

### 3.1 database/sql 集成

```go
package dbtracing

import (
    "context"
    "database/sql"
    "fmt"

    "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// InitDB 初始化数据库（自动追踪）
func InitDB(driverName, dataSourceName string) (*sql.DB, error) {
    // 使用 otelsql 包装驱动
    db, err := otelsql.Open(driverName, dataSourceName,
        otelsql.WithAttributes(
            semconv.DBSystemKey.String(driverName),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 注册统计信息
    if err := otelsql.RegisterDBStatsMetrics(db, otelsql.WithAttributes(
        semconv.DBSystemKey.String(driverName),
    )); err != nil {
        return nil, err
    }

    return db, nil
}

// TracedQuery 追踪查询
func TracedQuery(ctx context.Context, db *sql.DB, query string, args ...interface{}) (*sql.Rows, error) {
    tracer := otel.Tracer("database")

    ctx, span := tracer.Start(ctx, "db.query")
    defer span.End()

    span.SetAttributes(
        semconv.DBStatementKey.String(query),
        attribute.String("db.operation", "query"),
    )

    rows, err := db.QueryContext(ctx, query, args...)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetStatus(codes.Ok, "")
    return rows, nil
}

// TracedExec 追踪执行
func TracedExec(ctx context.Context, db *sql.DB, query string, args ...interface{}) (sql.Result, error) {
    tracer := otel.Tracer("database")

    ctx, span := tracer.Start(ctx, "db.exec")
    defer span.End()

    span.SetAttributes(
        semconv.DBStatementKey.String(query),
        attribute.String("db.operation", "exec"),
    )

    result, err := db.ExecContext(ctx, query, args...)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    // 记录受影响的行数
    if rowsAffected, err := result.RowsAffected(); err == nil {
        span.SetAttributes(
            attribute.Int64("db.rows_affected", rowsAffected),
        )
    }

    span.SetStatus(codes.Ok, "")
    return result, nil
}
```

### 3.2 GORM 集成

```go
package gormtracing

import (
    "go.opentelemetry.io/contrib/instrumentation/gorm.io/gorm/otelgorm"
    "gorm.io/driver/postgres"
    "gorm.io/gorm"
)

// InitGORM 初始化 GORM（自动追踪）
func InitGORM(dsn string) (*gorm.DB, error) {
    db, err := gorm.Open(postgres.Open(dsn), &gorm.Config{})
    if err != nil {
        return nil, err
    }

    // 使用 OpenTelemetry 插件
    if err := db.Use(otelgorm.NewPlugin()); err != nil {
        return nil, err
    }

    return db, nil
}

// 使用示例
func QueryUsers(ctx context.Context, db *gorm.DB) ([]User, error) {
    var users []User
    
    // GORM 会自动追踪这个查询
    result := db.WithContext(ctx).Find(&users)
    if result.Error != nil {
        return nil, result.Error
    }

    return users, nil
}
```

### 3.3 Redis 集成

```go
package redistracing

import (
    "context"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/contrib/instrumentation/github.com/redis/go-redis/v9/redisotel"
)

// InitRedis 初始化 Redis（自动追踪）
func InitRedis(addr string) *redis.Client {
    rdb := redis.NewClient(&redis.Options{
        Addr: addr,
    })

    // 启用追踪
    if err := redisotel.InstrumentTracing(rdb); err != nil {
        panic(err)
    }

    // 启用指标
    if err := redisotel.InstrumentMetrics(rdb); err != nil {
        panic(err)
    }

    return rdb
}

// 使用示例
func SetValue(ctx context.Context, rdb *redis.Client, key, value string) error {
    // Redis 命令会自动被追踪
    return rdb.Set(ctx, key, value, 0).Err()
}

func GetValue(ctx context.Context, rdb *redis.Client, key string) (string, error) {
    return rdb.Get(ctx, key).Result()
}
```

---

## 4. 消息队列集成

### 4.1 Kafka 集成

```go
package kafkatracing

import (
    "context"

    "github.com/segmentio/kafka-go"
    "go.opentelemetry.io/contrib/instrumentation/github.com/segmentio/kafka-go/otellkafka"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// TracedKafkaWriter 追踪的 Kafka Writer
type TracedKafkaWriter struct {
    writer     *kafka.Writer
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedKafkaWriter 创建追踪的 Writer
func NewTracedKafkaWriter(brokers []string, topic string) *TracedKafkaWriter {
    return &TracedKafkaWriter{
        writer: &kafka.Writer{
            Addr:     kafka.TCP(brokers...),
            Topic:    topic,
            Balancer: &kafka.LeastBytes{},
        },
        tracer:     otel.Tracer("kafka-producer"),
        propagator: otel.GetTextMapPropagator(),
    }
}

// WriteMessage 发送消息（带追踪）
func (w *TracedKafkaWriter) WriteMessage(ctx context.Context, msg kafka.Message) error {
    // 创建 Span
    ctx, span := w.tracer.Start(ctx, "kafka.produce",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "kafka"),
            attribute.String("messaging.destination", w.writer.Topic),
            attribute.String("messaging.operation", "send"),
        ),
    )
    defer span.End()

    // 注入追踪上下文到消息头
    headers := make([]kafka.Header, 0, len(msg.Headers)+2)
    headers = append(headers, msg.Headers...)
    
    carrier := &kafkaHeaderCarrier{headers: &headers}
    w.propagator.Inject(ctx, carrier)
    msg.Headers = headers

    // 发送消息
    err := w.writer.WriteMessages(ctx, msg)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// TracedKafkaReader 追踪的 Kafka Reader
type TracedKafkaReader struct {
    reader     *kafka.Reader
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedKafkaReader 创建追踪的 Reader
func NewTracedKafkaReader(brokers []string, topic, groupID string) *TracedKafkaReader {
    return &TracedKafkaReader{
        reader: kafka.NewReader(kafka.ReaderConfig{
            Brokers: brokers,
            Topic:   topic,
            GroupID: groupID,
        }),
        tracer:     otel.Tracer("kafka-consumer"),
        propagator: otel.GetTextMapPropagator(),
    }
}

// ReadMessage 读取消息（带追踪）
func (r *TracedKafkaReader) ReadMessage(ctx context.Context) (kafka.Message, error) {
    msg, err := r.reader.ReadMessage(ctx)
    if err != nil {
        return msg, err
    }

    // 提取追踪上下文
    carrier := &kafkaHeaderCarrier{headers: &msg.Headers}
    ctx = r.propagator.Extract(ctx, carrier)

    // 创建 Span
    _, span := r.tracer.Start(ctx, "kafka.consume",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("messaging.system", "kafka"),
            attribute.String("messaging.destination", msg.Topic),
            attribute.String("messaging.operation", "receive"),
            attribute.Int("messaging.message.partition", msg.Partition),
            attribute.Int64("messaging.message.offset", msg.Offset),
        ),
    )
    defer span.End()

    span.SetStatus(codes.Ok, "")
    return msg, nil
}

// kafkaHeaderCarrier Kafka 头部载体
type kafkaHeaderCarrier struct {
    headers *[]kafka.Header
}

func (c *kafkaHeaderCarrier) Get(key string) string {
    for _, h := range *c.headers {
        if h.Key == key {
            return string(h.Value)
        }
    }
    return ""
}

func (c *kafkaHeaderCarrier) Set(key, value string) {
    // 更新或添加头部
    for i, h := range *c.headers {
        if h.Key == key {
            (*c.headers)[i].Value = []byte(value)
            return
        }
    }
    *c.headers = append(*c.headers, kafka.Header{
        Key:   key,
        Value: []byte(value),
    })
}

func (c *kafkaHeaderCarrier) Keys() []string {
    keys := make([]string, len(*c.headers))
    for i, h := range *c.headers {
        keys[i] = h.Key
    }
    return keys
}
```

### 4.2 RabbitMQ 集成

```go
package rabbitmqtracing

import (
    "context"

    amqp "github.com/rabbitmq/amqp091-go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// TracedPublisher 追踪的发布者
type TracedPublisher struct {
    channel    *amqp.Channel
    exchange   string
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedPublisher 创建追踪的发布者
func NewTracedPublisher(ch *amqp.Channel, exchange string) *TracedPublisher {
    return &TracedPublisher{
        channel:    ch,
        exchange:   exchange,
        tracer:     otel.Tracer("rabbitmq-publisher"),
        propagator: otel.GetTextMapPropagator(),
    }
}

// Publish 发布消息（带追踪）
func (p *TracedPublisher) Publish(ctx context.Context, routingKey string, body []byte) error {
    // 创建 Span
    ctx, span := p.tracer.Start(ctx, "rabbitmq.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "rabbitmq"),
            attribute.String("messaging.destination", p.exchange),
            attribute.String("messaging.routing_key", routingKey),
        ),
    )
    defer span.End()

    // 注入追踪上下文
    headers := make(amqp.Table)
    carrier := &amqpHeaderCarrier{headers: headers}
    p.propagator.Inject(ctx, carrier)

    // 发布消息
    err := p.channel.PublishWithContext(ctx,
        p.exchange,
        routingKey,
        false,
        false,
        amqp.Publishing{
            ContentType: "text/plain",
            Body:        body,
            Headers:     headers,
        },
    )

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// amqpHeaderCarrier AMQP 头部载体
type amqpHeaderCarrier struct {
    headers amqp.Table
}

func (c *amqpHeaderCarrier) Get(key string) string {
    if val, ok := c.headers[key]; ok {
        if str, ok := val.(string); ok {
            return str
        }
    }
    return ""
}

func (c *amqpHeaderCarrier) Set(key, value string) {
    c.headers[key] = value
}

func (c *amqpHeaderCarrier) Keys() []string {
    keys := make([]string, 0, len(c.headers))
    for k := range c.headers {
        keys = append(keys, k)
    }
    return keys
}
```

---

## 5. Context 传播深度实践

### 5.1 HTTP 跨服务传播

```go
package propagation

import (
    "context"
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// HTTPClient 带追踪的 HTTP 客户端
type HTTPClient struct {
    client     *http.Client
    propagator propagation.TextMapPropagator
}

// NewHTTPClient 创建 HTTP 客户端
func NewHTTPClient() *HTTPClient {
    return &HTTPClient{
        client:     &http.Client{},
        propagator: otel.GetTextMapPropagator(),
    }
}

// Do 执行请求（自动注入追踪上下文）
func (c *HTTPClient) Do(ctx context.Context, req *http.Request) (*http.Response, error) {
    // 注入追踪上下文到请求头
    c.propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    // 执行请求
    req = req.WithContext(ctx)
    return c.client.Do(req)
}
```

### 5.2 完整的微服务追踪示例

```go
package example

import (
    "context"
    "encoding/json"
    "fmt"
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// Service A: API Gateway
func handleUserRequest(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    tracer := otel.Tracer("api-gateway")

    // 创建 Span
    ctx, span := tracer.Start(ctx, "handle-user-request")
    defer span.End()

    userID := r.URL.Query().Get("user_id")
    span.SetAttributes(attribute.String("user.id", userID))

    // 调用 User Service
    user, err := callUserService(ctx, userID)
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 调用 Order Service
    orders, err := callOrderService(ctx, userID)
    if err != nil {
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // 返回响应
    response := map[string]interface{}{
        "user":   user,
        "orders": orders,
    }
    
    json.NewEncoder(w).Encode(response)
}

// Service B: User Service
func callUserService(ctx context.Context, userID string) (*User, error) {
    tracer := otel.Tracer("api-gateway")
    ctx, span := tracer.Start(ctx, "call-user-service")
    defer span.End()

    // 创建 HTTP 请求
    req, _ := http.NewRequestWithContext(ctx, "GET",
        fmt.Sprintf("http://user-service/users/%s", userID), nil)

    // 注入追踪上下文
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))

    // 执行请求
    client := &http.Client{}
    resp, err := client.Do(req)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    defer resp.Body.Close()

    // 解析响应
    var user User
    json.NewDecoder(resp.Body).Decode(&user)

    return &user, nil
}

// Service C: Order Service
func callOrderService(ctx context.Context, userID string) ([]Order, error) {
    tracer := otel.Tracer("api-gateway")
    ctx, span := tracer.Start(ctx, "call-order-service")
    defer span.End()

    // 类似 callUserService
    // ...

    return orders, nil
}
```

---

## 6. 自定义 Instrumentation

### 6.1 自定义 Span 处理器

```go
package custom

import (
    "context"

    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// CustomSpanProcessor 自定义 Span 处理器
type CustomSpanProcessor struct {
    // 自定义字段
}

// OnStart 当 Span 开始时调用
func (p *CustomSpanProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
    // 自定义逻辑
    // 例如: 添加自定义属性
    s.SetAttributes(
        attribute.String("custom.processor", "v1"),
    )
}

// OnEnd 当 Span 结束时调用
func (p *CustomSpanProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
    // 自定义逻辑
    // 例如: 发送到自定义后端
    duration := s.EndTime().Sub(s.StartTime())
    fmt.Printf("Span %s took %v\n", s.Name(), duration)
}

// Shutdown 关闭处理器
func (p *CustomSpanProcessor) Shutdown(ctx context.Context) error {
    return nil
}

// ForceFlush 强制刷新
func (p *CustomSpanProcessor) ForceFlush(ctx context.Context) error {
    return nil
}
```

### 6.2 自定义采样器

```go
package custom

import (
    "go.opentelemetry.io/otel/attribute"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/trace"
)

// CustomSampler 自定义采样器
type CustomSampler struct {
    // 配置
    defaultRate float64
    ruleRates   map[string]float64
}

// NewCustomSampler 创建自定义采样器
func NewCustomSampler(defaultRate float64) *CustomSampler {
    return &CustomSampler{
        defaultRate: defaultRate,
        ruleRates: map[string]float64{
            "/api/health":   0.01, // 健康检查 1% 采样
            "/api/critical": 1.0,  // 关键API 100% 采样
        },
    }
}

// ShouldSample 决定是否采样
func (s *CustomSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 检查路由规则
    for _, attr := range p.Attributes {
        if attr.Key == "http.route" {
            route := attr.Value.AsString()
            if rate, ok := s.ruleRates[route]; ok {
                sampler := sdktrace.TraceIDRatioBased(rate)
                return sampler.ShouldSample(p)
            }
        }
    }

    // 使用默认采样率
    sampler := sdktrace.TraceIDRatioBased(s.defaultRate)
    return sampler.ShouldSample(p)
}

// Description 描述
func (s *CustomSampler) Description() string {
    return "CustomRuleBasedSampler"
}
```

---

## 7. 错误处理模式

### 7.1 标准错误处理

```go
package errorhandling

import (
    "context"
    "errors"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// TracedOperation 带追踪的操作
func TracedOperation(ctx context.Context) error {
    tracer := otel.Tracer("error-handling")
    ctx, span := tracer.Start(ctx, "traced-operation")
    defer span.End()

    // 执行操作
    err := doSomething(ctx)
    if err != nil {
        // 记录错误
        span.RecordError(err)
        
        // 设置状态
        span.SetStatus(codes.Error, err.Error())
        
        // 添加错误相关属性
        span.SetAttributes(
            attribute.String("error.type", fmt.Sprintf("%T", err)),
        )
        
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// 包装错误以保留追踪信息
func WrapError(ctx context.Context, err error, msg string) error {
    if err == nil {
        return nil
    }

    tracer := otel.Tracer("error-handling")
    _, span := tracer.Start(ctx, "error-wrap")
    defer span.End()

    wrapped := fmt.Errorf("%s: %w", msg, err)
    
    span.RecordError(wrapped)
    span.SetStatus(codes.Error, wrapped.Error())

    return wrapped
}
```

### 7.2 Panic 恢复

```go
package recovery

import (
    "context"
    "fmt"
    "runtime/debug"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// RecoverMiddleware Panic 恢复中间件
func RecoverMiddleware(next http.Handler) http.Handler {
    tracer := otel.Tracer("recovery")

    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        defer func() {
            if r := recover(); r != nil {
                ctx := r.Context()
                _, span := tracer.Start(ctx, "panic-recovery")
                defer span.End()

                // 记录 Panic 信息
                err := fmt.Errorf("panic: %v", r)
                span.RecordError(err)
                span.SetStatus(codes.Error, err.Error())
                
                // 记录堆栈
                stack := string(debug.Stack())
                span.SetAttributes(
                    attribute.String("panic.stack", stack),
                )

                // 返回错误响应
                http.Error(w, "Internal Server Error", http.StatusInternalServerError)
            }
        }()

        next.ServeHTTP(w, r)
    })
}
```

---

## 8. 高级配置

### 8.1 动态采样

```go
package advanced

import (
    "sync"
    "time"

    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// DynamicSampler 动态采样器
type DynamicSampler struct {
    mu           sync.RWMutex
    currentRate  float64
    sampler      sdktrace.Sampler
    updateTicker *time.Ticker
}

// NewDynamicSampler 创建动态采样器
func NewDynamicSampler(initialRate float64) *DynamicSampler {
    ds := &DynamicSampler{
        currentRate: initialRate,
        sampler:     sdktrace.TraceIDRatioBased(initialRate),
    }

    // 定期更新采样率
    ds.updateTicker = time.NewTicker(1 * time.Minute)
    go ds.updateLoop()

    return ds
}

// updateLoop 更新循环
func (ds *DynamicSampler) updateLoop() {
    for range ds.updateTicker.C {
        // 根据系统负载动态调整采样率
        newRate := ds.calculateOptimalRate()
        ds.UpdateRate(newRate)
    }
}

// calculateOptimalRate 计算最优采样率
func (ds *DynamicSampler) calculateOptimalRate() float64 {
    // 实现自定义逻辑
    // 例如: 基于 CPU 使用率、内存、请求量等
    return 0.1
}

// UpdateRate 更新采样率
func (ds *DynamicSampler) UpdateRate(rate float64) {
    ds.mu.Lock()
    defer ds.mu.Unlock()

    ds.currentRate = rate
    ds.sampler = sdktrace.TraceIDRatioBased(rate)
}

// ShouldSample 决定是否采样
func (ds *DynamicSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    ds.mu.RLock()
    defer ds.mu.RUnlock()

    return ds.sampler.ShouldSample(p)
}

// Description 描述
func (ds *DynamicSampler) Description() string {
    return "DynamicSampler"
}
```

### 8.2 批处理优化

```go
package advanced

import (
    "context"
    "time"

    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// OptimizedBatchProcessor 优化的批处理器
type OptimizedBatchProcessor struct {
    *sdktrace.BatchSpanProcessor
}

// NewOptimizedBatchProcessor 创建优化的批处理器
func NewOptimizedBatchProcessor(exporter sdktrace.SpanExporter) *OptimizedBatchProcessor {
    bsp := sdktrace.NewBatchSpanProcessor(exporter,
        // 批大小
        sdktrace.WithMaxExportBatchSize(512),
        
        // 批超时
        sdktrace.WithBatchTimeout(5*time.Second),
        
        // 队列大小
        sdktrace.WithMaxQueueSize(2048),
        
        // 导出超时
        sdktrace.WithExportTimeout(30*time.Second),
    )

    return &OptimizedBatchProcessor{
        BatchSpanProcessor: bsp,
    }
}
```

---

## 总结

本文档提供了 Go SDK 深度实践的完整指南，涵盖：

1. ✅ **HTTP 中间件集成** - net/http、Gin、Echo
2. ✅ **gRPC 拦截器** - Unary、Stream（客户端和服务器端）
3. ✅ **数据库追踪** - database/sql、GORM、Redis
4. ✅ **消息队列集成** - Kafka、RabbitMQ
5. ✅ **Context 传播** - 跨服务追踪
6. ✅ **自定义 Instrumentation** - Span 处理器、采样器
7. ✅ **错误处理** - 标准模式、Panic 恢复
8. ✅ **高级配置** - 动态采样、批处理优化

**相关文档**：

- [Go_1.25.1_完整集成指南.md](./01_Go_1.25.1_完整集成指南.md) - 基础集成
- [Go并发模式与OTLP集成.md](./02_Go并发模式与OTLP集成.md) - 并发模式
- [Go性能优化与最佳实践.md](./03_Go性能优化与最佳实践.md) - 性能优化

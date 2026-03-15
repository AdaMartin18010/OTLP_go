# RPC 与 gRPC 追踪属性完整指南

> **文档版本**: v2.0.0  
> **最后更新**: 2025-10-09  
> **OpenTelemetry 版本**: v1.32.0  
> **Go 版本**: 1.25.1

## 目录

- [RPC 与 gRPC 追踪属性完整指南](#rpc-与-grpc-追踪属性完整指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 RPC 语义约定](#11-rpc-语义约定)
    - [1.2 gRPC 特点](#12-grpc-特点)
  - [2. RPC 通用属性](#2-rpc-通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. gRPC 特定属性](#3-grpc-特定属性)
    - [3.1 gRPC 核心属性](#31-grpc-核心属性)
    - [3.2 gRPC 状态码映射](#32-grpc-状态码映射)
  - [4. gRPC 客户端追踪](#4-grpc-客户端追踪)
    - [4.1 基础客户端](#41-基础客户端)
    - [4.2 自定义客户端拦截器](#42-自定义客户端拦截器)
  - [5. gRPC 服务器追踪](#5-grpc-服务器追踪)
    - [5.1 基础服务器](#51-基础服务器)
    - [5.2 自定义服务器拦截器](#52-自定义服务器拦截器)
  - [6. 流式 RPC 追踪](#6-流式-rpc-追踪)
    - [6.1 服务器流式](#61-服务器流式)
    - [6.2 客户端流式](#62-客户端流式)
    - [6.3 双向流式](#63-双向流式)
  - [7. 错误处理](#7-错误处理)
    - [7.1 结构化错误](#71-结构化错误)
    - [7.2 重试策略](#72-重试策略)
  - [8. 拦截器模式](#8-拦截器模式)
    - [8.1 链式拦截器](#81-链式拦截器)
    - [8.2 条件拦截器](#82-条件拦截器)
  - [9. 完整实现](#9-完整实现)
    - [9.1 完整客户端](#91-完整客户端)
    - [9.2 完整服务器](#92-完整服务器)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 元数据传播](#101-元数据传播)
    - [10.2 超时控制](#102-超时控制)
    - [10.3 性能监控](#103-性能监控)
  - [总结](#总结)

---

## 1. 概述

### 1.1 RPC 语义约定

RPC (Remote Procedure Call) 追踪涵盖所有远程过程调用,包括 gRPC、Thrift、JSON-RPC 等。

**关键特征**:

- **客户端 Span Kind**: `SPAN_KIND_CLIENT`
- **服务器端 Span Kind**: `SPAN_KIND_SERVER`
- **命名规范**: `{rpc.system}/{rpc.service}/{rpc.method}`

### 1.2 gRPC 特点

gRPC 基于 HTTP/2,具有以下特性:

- **多路复用**: 单个连接支持多个并发请求
- **流式传输**: 支持四种调用模式 (Unary, Server Streaming, Client Streaming, Bidirectional Streaming)
- **Protocol Buffers**: 高效的二进制序列化
- **元数据**: 类似 HTTP 头的键值对

---

## 2. RPC 通用属性

### 2.1 必需属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `rpc.system` | string | `grpc`, `thrift` | RPC 系统名称 |
| `rpc.service` | string | `UserService` | 服务名称 |
| `rpc.method` | string | `GetUser` | 方法名称 |

### 2.2 推荐属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `server.address` | string | `api.example.com` | 服务器地址 |
| `server.port` | int | `9090` | 服务器端口 |
| `network.protocol.version` | string | `2` | 协议版本 (HTTP/2) |

---

## 3. gRPC 特定属性

### 3.1 gRPC 核心属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `rpc.grpc.status_code` | int | `0` (OK), `2` (UNKNOWN) | gRPC 状态码 |
| `rpc.grpc.request.metadata.<key>` | string[] | `["value1"]` | 请求元数据 |
| `rpc.grpc.response.metadata.<key>` | string[] | `["value2"]` | 响应元数据 |

### 3.2 gRPC 状态码映射

| gRPC Code | 值 | 描述 | Span Status |
|-----------|-----|------|-------------|
| `OK` | 0 | 成功 | `Ok` |
| `CANCELLED` | 1 | 客户端取消 | `Error` |
| `UNKNOWN` | 2 | 未知错误 | `Error` |
| `INVALID_ARGUMENT` | 3 | 无效参数 | `Error` |
| `DEADLINE_EXCEEDED` | 4 | 超时 | `Error` |
| `NOT_FOUND` | 5 | 未找到 | `Error` |
| `ALREADY_EXISTS` | 6 | 已存在 | `Error` |
| `PERMISSION_DENIED` | 7 | 权限拒绝 | `Error` |
| `RESOURCE_EXHAUSTED` | 8 | 资源耗尽 | `Error` |
| `FAILED_PRECONDITION` | 9 | 前置条件失败 | `Error` |
| `ABORTED` | 10 | 中止 | `Error` |
| `OUT_OF_RANGE` | 11 | 超出范围 | `Error` |
| `UNIMPLEMENTED` | 12 | 未实现 | `Error` |
| `INTERNAL` | 13 | 内部错误 | `Error` |
| `UNAVAILABLE` | 14 | 服务不可用 | `Error` |
| `DATA_LOSS` | 15 | 数据丢失 | `Error` |
| `UNAUTHENTICATED` | 16 | 未认证 | `Error` |

---

## 4. gRPC 客户端追踪

### 4.1 基础客户端

```go
package grpctracing

import (
    "context"

    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

// NewTracedClient 创建带追踪的 gRPC 客户端
func NewTracedClient(target string) (*grpc.ClientConn, error) {
    return grpc.Dial(target,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
    )
}

// 使用示例
func ExampleClient(ctx context.Context) error {
    conn, err := NewTracedClient("localhost:9090")
    if err != nil {
        return err
    }
    defer conn.Close()

    client := pb.NewUserServiceClient(conn)

    // 调用自动追踪
    resp, err := client.GetUser(ctx, &pb.GetUserRequest{
        Id: "user123",
    })
    if err != nil {
        return err
    }

    log.Printf("User: %v", resp)
    return nil
}
```

### 4.2 自定义客户端拦截器

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    "google.golang.org/grpc/status"
)

// CustomUnaryClientInterceptor 自定义一元 RPC 客户端拦截器
func CustomUnaryClientInterceptor() grpc.UnaryClientInterceptor {
    tracer := otel.Tracer("grpc-client")

    return func(ctx context.Context, method string, req, reply interface{},
        cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {

        // 创建客户端 Span
        ctx, span := tracer.Start(ctx, method,
            trace.WithSpanKind(trace.SpanKindClient),
            trace.WithAttributes(
                attribute.String("rpc.system", "grpc"),
                attribute.String("rpc.service", extractService(method)),
                attribute.String("rpc.method", extractMethod(method)),
                attribute.String("server.address", cc.Target()),
            ),
        )
        defer span.End()

        // 注入追踪上下文到 gRPC 元数据
        md, ok := metadata.FromOutgoingContext(ctx)
        if !ok {
            md = metadata.New(nil)
        }
        propagator := otel.GetTextMapPropagator()
        propagator.Inject(ctx, &metadataCarrier{md: &md})
        ctx = metadata.NewOutgoingContext(ctx, md)

        // 调用 RPC
        err := invoker(ctx, method, req, reply, cc, opts...)

        // 记录 gRPC 状态码
        st, _ := status.FromError(err)
        span.SetAttributes(
            attribute.Int("rpc.grpc.status_code", int(st.Code())),
        )

        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, st.Message())
        } else {
            span.SetStatus(codes.Ok, "")
        }

        return err
    }
}

// metadataCarrier 用于在 gRPC 元数据中传播追踪上下文
type metadataCarrier struct {
    md *metadata.MD
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
    keys := make([]string, 0, len(*c.md))
    for k := range *c.md {
        keys = append(keys, k)
    }
    return keys
}

// extractService 从方法全名提取服务名
// "/package.Service/Method" -> "Service"
func extractService(fullMethod string) string {
    parts := strings.Split(fullMethod, "/")
    if len(parts) < 2 {
        return ""
    }
    serviceParts := strings.Split(parts[1], ".")
    return serviceParts[len(serviceParts)-1]
}

// extractMethod 从方法全名提取方法名
// "/package.Service/Method" -> "Method"
func extractMethod(fullMethod string) string {
    parts := strings.Split(fullMethod, "/")
    if len(parts) < 3 {
        return ""
    }
    return parts[2]
}
```

---

## 5. gRPC 服务器追踪

### 5.1 基础服务器

```go
// NewTracedServer 创建带追踪的 gRPC 服务器
func NewTracedServer() *grpc.Server {
    return grpc.NewServer(
        grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
        grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
    )
}

// 使用示例
type userServer struct {
    pb.UnimplementedUserServiceServer
}

func (s *userServer) GetUser(ctx context.Context, req *pb.GetUserRequest) (*pb.GetUserResponse, error) {
    span := trace.SpanFromContext(ctx)
    
    // 添加自定义属性
    span.SetAttributes(
        attribute.String("user.id", req.Id),
    )

    // 业务逻辑
    user := &pb.User{
        Id:   req.Id,
        Name: "John Doe",
    }

    return &pb.GetUserResponse{User: user}, nil
}

func main() {
    // 初始化追踪
    tp := initTracer()
    defer tp.Shutdown(context.Background())

    // 创建服务器
    server := NewTracedServer()
    pb.RegisterUserServiceServer(server, &userServer{})

    // 启动监听
    lis, _ := net.Listen("tcp", ":9090")
    log.Println("Server starting on :9090")
    log.Fatal(server.Serve(lis))
}
```

### 5.2 自定义服务器拦截器

```go
// CustomUnaryServerInterceptor 自定义一元 RPC 服务器拦截器
func CustomUnaryServerInterceptor() grpc.UnaryServerInterceptor {
    tracer := otel.Tracer("grpc-server")

    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler) (interface{}, error) {

        // 从 gRPC 元数据提取追踪上下文
        md, ok := metadata.FromIncomingContext(ctx)
        if ok {
            propagator := otel.GetTextMapPropagator()
            ctx = propagator.Extract(ctx, &metadataCarrier{md: &md})
        }

        // 创建服务器 Span
        ctx, span := tracer.Start(ctx, info.FullMethod,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("rpc.system", "grpc"),
                attribute.String("rpc.service", extractService(info.FullMethod)),
                attribute.String("rpc.method", extractMethod(info.FullMethod)),
            ),
        )
        defer span.End()

        // 调用处理器
        resp, err := handler(ctx, req)

        // 记录 gRPC 状态码
        st, _ := status.FromError(err)
        span.SetAttributes(
            attribute.Int("rpc.grpc.status_code", int(st.Code())),
        )

        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, st.Message())
        } else {
            span.SetStatus(codes.Ok, "")
        }

        return resp, err
    }
}
```

---

## 6. 流式 RPC 追踪

### 6.1 服务器流式

```go
func (s *userServer) ListUsers(req *pb.ListUsersRequest, stream pb.UserService_ListUsersServer) error {
    ctx := stream.Context()
    span := trace.SpanFromContext(ctx)

    span.AddEvent("Stream started")

    users := []*pb.User{
        {Id: "1", Name: "Alice"},
        {Id: "2", Name: "Bob"},
    }

    for i, user := range users {
        if err := stream.Send(&pb.ListUsersResponse{User: user}); err != nil {
            span.RecordError(err)
            return err
        }

        span.AddEvent("Message sent", trace.WithAttributes(
            attribute.Int("message.index", i),
            attribute.String("user.id", user.Id),
        ))
    }

    span.AddEvent("Stream completed")
    return nil
}
```

### 6.2 客户端流式

```go
func (c *client) UploadUsers(ctx context.Context, users []*pb.User) error {
    span := trace.SpanFromContext(ctx)
    span.AddEvent("Stream started")

    stream, err := c.client.UploadUsers(ctx)
    if err != nil {
        return err
    }

    for i, user := range users {
        if err := stream.Send(user); err != nil {
            span.RecordError(err)
            return err
        }

        span.AddEvent("Message sent", trace.WithAttributes(
            attribute.Int("message.index", i),
            attribute.String("user.id", user.Id),
        ))
    }

    resp, err := stream.CloseAndRecv()
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.AddEvent("Stream completed", trace.WithAttributes(
        attribute.Int("uploaded_count", int(resp.Count)),
    ))

    return nil
}
```

### 6.3 双向流式

```go
func (c *client) Chat(ctx context.Context) error {
    span := trace.SpanFromContext(ctx)
    span.AddEvent("Bidirectional stream started")

    stream, err := c.client.Chat(ctx)
    if err != nil {
        return err
    }

    // 发送 goroutine
    go func() {
        messages := []string{"Hello", "How are you?", "Goodbye"}
        for i, msg := range messages {
            if err := stream.Send(&pb.ChatMessage{Text: msg}); err != nil {
                span.RecordError(err)
                return
            }

            span.AddEvent("Message sent", trace.WithAttributes(
                attribute.Int("message.index", i),
                attribute.String("message.text", msg),
            ))

            time.Sleep(1 * time.Second)
        }
        stream.CloseSend()
    }()

    // 接收 goroutine
    for {
        resp, err := stream.Recv()
        if err == io.EOF {
            break
        }
        if err != nil {
            span.RecordError(err)
            return err
        }

        span.AddEvent("Message received", trace.WithAttributes(
            attribute.String("message.text", resp.Text),
        ))
    }

    span.AddEvent("Bidirectional stream completed")
    return nil
}
```

---

## 7. 错误处理

### 7.1 结构化错误

```go
import (
    "google.golang.org/grpc/codes"
    "google.golang.org/grpc/status"
)

// HandleGRPCError 处理 gRPC 错误并记录到 Span
func HandleGRPCError(span trace.Span, err error) error {
    if err == nil {
        return nil
    }

    st, ok := status.FromError(err)
    if !ok {
        // 非 gRPC 错误
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return status.Error(codes.Unknown, err.Error())
    }

    // 记录 gRPC 状态码
    span.SetAttributes(
        attribute.Int("rpc.grpc.status_code", int(st.Code())),
        attribute.String("rpc.grpc.status_message", st.Message()),
    )

    span.RecordError(err)
    span.SetStatus(codes.Error, st.Message())

    return err
}
```

### 7.2 重试策略

```go
// RetryableUnaryClientInterceptor 支持重试的客户端拦截器
func RetryableUnaryClientInterceptor(maxRetries int) grpc.UnaryClientInterceptor {
    return func(ctx context.Context, method string, req, reply interface{},
        cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {

        span := trace.SpanFromContext(ctx)

        var lastErr error
        for attempt := 0; attempt <= maxRetries; attempt++ {
            if attempt > 0 {
                span.AddEvent("Retry attempt", trace.WithAttributes(
                    attribute.Int("attempt", attempt),
                ))

                // 指数退避
                backoff := time.Duration(1<<uint(attempt-1)) * time.Second
                time.Sleep(backoff)
            }

            err := invoker(ctx, method, req, reply, cc, opts...)
            if err == nil {
                span.SetAttributes(attribute.Int("rpc.retry.count", attempt))
                return nil
            }

            lastErr = err

            // 检查是否可重试
            st, _ := status.FromError(err)
            if !isRetryable(st.Code()) {
                break
            }
        }

        return lastErr
    }
}

func isRetryable(code codes.Code) bool {
    switch code {
    case codes.Unavailable, codes.DeadlineExceeded, codes.ResourceExhausted:
        return true
    default:
        return false
    }
}
```

---

## 8. 拦截器模式

### 8.1 链式拦截器

```go
// ChainUnaryClient 链接多个一元客户端拦截器
func ChainUnaryClient(interceptors ...grpc.UnaryClientInterceptor) grpc.UnaryClientInterceptor {
    return func(ctx context.Context, method string, req, reply interface{},
        cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {

        chain := func(current grpc.UnaryClientInterceptor, next grpc.UnaryInvoker) grpc.UnaryInvoker {
            return func(ctx context.Context, method string, req, reply interface{},
                cc *grpc.ClientConn, opts ...grpc.CallOption) error {
                return current(ctx, method, req, reply, cc, next, opts...)
            }
        }

        chainedInvoker := invoker
        for i := len(interceptors) - 1; i >= 0; i-- {
            chainedInvoker = chain(interceptors[i], chainedInvoker)
        }

        return chainedInvoker(ctx, method, req, reply, cc, opts...)
    }
}

// 使用示例
conn, _ := grpc.Dial(target,
    grpc.WithUnaryInterceptor(
        ChainUnaryClient(
            otelgrpc.UnaryClientInterceptor(),
            LoggingClientInterceptor(),
            RetryableUnaryClientInterceptor(3),
        ),
    ),
)
```

### 8.2 条件拦截器

```go
// ConditionalInterceptor 基于条件的拦截器
func ConditionalInterceptor(condition func(string) bool, interceptor grpc.UnaryServerInterceptor) grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler) (interface{}, error) {

        if condition(info.FullMethod) {
            return interceptor(ctx, req, info, handler)
        }
        return handler(ctx, req)
    }
}

// 仅追踪特定服务
tracingInterceptor := ConditionalInterceptor(
    func(method string) bool {
        return strings.HasPrefix(method, "/UserService/")
    },
    CustomUnaryServerInterceptor(),
)
```

---

## 9. 完整实现

### 9.1 完整客户端

```go
package main

import (
    "context"
    "log"

    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

func main() {
    // 初始化追踪
    tp := initTracer()
    defer tp.Shutdown(context.Background())

    // 创建 gRPC 连接
    conn, err := grpc.Dial("localhost:9090",
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
    )
    if err != nil {
        log.Fatal(err)
    }
    defer conn.Close()

    // 创建客户端
    client := pb.NewUserServiceClient(conn)

    // 发起请求
    ctx := context.Background()
    resp, err := client.GetUser(ctx, &pb.GetUserRequest{
        Id: "user123",
    })
    if err != nil {
        log.Fatal(err)
    }

    log.Printf("User: %v", resp.User)
}

func initTracer() *sdktrace.TracerProvider {
    exporter, _ := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )

    resource := resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceName("grpc-client"),
        semconv.ServiceVersion("1.0.0"),
    )

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(resource),
    )

    otel.SetTracerProvider(tp)
    return tp
}
```

### 9.2 完整服务器

```go
package main

import (
    "context"
    "log"
    "net"

    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
)

type userServer struct {
    pb.UnimplementedUserServiceServer
}

func (s *userServer) GetUser(ctx context.Context, req *pb.GetUserRequest) (*pb.GetUserResponse, error) {
    span := trace.SpanFromContext(ctx)
    span.SetAttributes(attribute.String("user.id", req.Id))

    // 模拟数据库查询
    user := &pb.User{
        Id:    req.Id,
        Name:  "John Doe",
        Email: "john@example.com",
    }

    return &pb.GetUserResponse{User: user}, nil
}

func main() {
    // 初始化追踪
    tp := initTracer()
    defer tp.Shutdown(context.Background())

    // 创建 gRPC 服务器
    server := grpc.NewServer(
        grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
        grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
    )

    // 注册服务
    pb.RegisterUserServiceServer(server, &userServer{})

    // 启动监听
    lis, err := net.Listen("tcp", ":9090")
    if err != nil {
        log.Fatal(err)
    }

    log.Println("Server starting on :9090")
    log.Fatal(server.Serve(lis))
}
```

---

## 10. 最佳实践

### 10.1 元数据传播

```go
// 客户端设置元数据
md := metadata.Pairs(
    "request-id", "req-123",
    "user-id", "user-456",
)
ctx := metadata.NewOutgoingContext(ctx, md)

// 服务器读取元数据
md, ok := metadata.FromIncomingContext(ctx)
if ok {
    requestID := md.Get("request-id")
    span.SetAttributes(attribute.String("request.id", requestID[0]))
}
```

### 10.2 超时控制

```go
// 设置调用超时
ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
defer cancel()

resp, err := client.GetUser(ctx, req)
if err != nil {
    st, _ := status.FromError(err)
    if st.Code() == codes.DeadlineExceeded {
        log.Println("Request timeout")
    }
}
```

### 10.3 性能监控

```go
// PerformanceInterceptor 监控 RPC 性能
func PerformanceInterceptor() grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler) (interface{}, error) {

        start := time.Now()
        span := trace.SpanFromContext(ctx)

        resp, err := handler(ctx, req)

        duration := time.Since(start)
        span.SetAttributes(
            attribute.Int64("rpc.duration_ms", duration.Milliseconds()),
        )

        // 慢调用告警
        if duration > 1*time.Second {
            span.AddEvent("slow_rpc", trace.WithAttributes(
                attribute.String("duration", duration.String()),
            ))
        }

        return resp, err
    }
}
```

---

## 总结

✅ **RPC 通用属性**: `rpc.system`, `rpc.service`, `rpc.method`  
✅ **gRPC 特定属性**: `rpc.grpc.status_code`  
✅ **流式追踪**: 服务器流、客户端流、双向流  
✅ **拦截器模式**: 链式、条件、重试  
✅ **错误处理**: gRPC 状态码映射、结构化错误  
✅ **完整实现**: 生产级客户端和服务器

**下一步**: 参见 `04_数据库.md` 了解数据库追踪。

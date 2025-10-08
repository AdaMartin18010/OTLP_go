# Go 微服务架构与 OTLP 完整集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0+  
> **最后更新**: 2025年10月8日

---

## 📋 目录

- [Go 微服务架构与 OTLP 完整集成](#go-微服务架构与-otlp-完整集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [微服务可观测性架构](#微服务可观测性架构)
    - [核心集成模式](#核心集成模式)
  - [gRPC 微服务集成](#grpc-微服务集成)
    - [1. gRPC 服务端完整集成](#1-grpc-服务端完整集成)
    - [2. gRPC 客户端集成](#2-grpc-客户端集成)
    - [3. gRPC 拦截器链](#3-grpc-拦截器链)
  - [REST API 微服务集成](#rest-api-微服务集成)
    - [4. RESTful 服务实现](#4-restful-服务实现)
    - [5. HTTP 客户端追踪](#5-http-客户端追踪)
  - [GraphQL 微服务集成](#graphql-微服务集成)
    - [6. GraphQL 服务器集成](#6-graphql-服务器集成)
  - [服务间通信模式](#服务间通信模式)
    - [7. 分布式追踪传播](#7-分布式追踪传播)
    - [8. 服务网格集成](#8-服务网格集成)
  - [微服务可观测性最佳实践](#微服务可观测性最佳实践)
    - [9. 统一可观测性层](#9-统一可观测性层)
    - [10. 服务健康检查](#10-服务健康检查)
  - [总结](#总结)
    - [核心集成](#核心集成)
    - [可观测性模式](#可观测性模式)
    - [相关文档](#相关文档)

---

## 概述

### 微服务可观测性架构

```text
┌─────────────────────────────────────────────────────────────────┐
│                      API Gateway / Load Balancer                │
│                    (Trace Context Propagation)                  │
└────────────────────────┬────────────────────────────────────────┘
                         │
         ┌───────────────┼───────────────┐
         │               │               │
         ▼               ▼               ▼
    ┌────────┐      ┌────────┐     ┌────────┐
    │  gRPC  │      │  REST  │     │GraphQL │
    │Service │◄────►│Service │◄───►│Service │
    │        │      │        │     │        │
    └───┬────┘      └───┬────┘     └───┬────┘
        │               │               │
        └───────────────┼───────────────┘
                        │
                        ▼
              ┌──────────────────┐
              │ OpenTelemetry    │
              │ Collector        │
              └──────────────────┘
                        │
         ┌──────────────┼──────────────┐
         ▼              ▼              ▼
    ┌────────┐    ┌────────┐    ┌────────┐
    │ Jaeger │    │Prometheus│  │  Loki  │
    │(Traces)│    │(Metrics) │  │ (Logs) │
    └────────┘    └────────┘    └────────┘
```

### 核心集成模式

```text
✅ Context 传播 - W3C Trace Context
✅ 服务间追踪 - Distributed Tracing
✅ 错误传播 - Error Context Propagation
✅ 指标收集 - RED Metrics (Rate, Errors, Duration)
✅ 日志关联 - Trace ID Correlation
✅ 服务发现 - Service Discovery Integration
```

---

## gRPC 微服务集成

### 1. gRPC 服务端完整集成

```go
package grpcservice

import (
    "context"
    "fmt"
    "time"

    "google.golang.org/grpc"
    "google.golang.org/grpc/codes"
    "google.golang.org/grpc/metadata"
    "google.golang.org/grpc/status"

    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// UserService gRPC 用户服务
type UserService struct {
    tracer         trace.Tracer
    meter          metric.Meter
    requestCounter metric.Int64Counter
    durationHisto  metric.Float64Histogram
}

// NewUserService 创建用户服务
func NewUserService() (*UserService, error) {
    tracer := otel.Tracer("user-service")
    meter := otel.Meter("user-service")

    requestCounter, err := meter.Int64Counter(
        "grpc.server.requests",
        metric.WithDescription("gRPC 服务器请求数"),
    )
    if err != nil {
        return nil, err
    }

    durationHisto, err := meter.Float64Histogram(
        "grpc.server.duration",
        metric.WithDescription("gRPC 请求处理时间"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }

    return &UserService{
        tracer:         tracer,
        meter:          meter,
        requestCounter: requestCounter,
        durationHisto:  durationHisto,
    }, nil
}

// GetUser 获取用户信息
func (s *UserService) GetUser(ctx context.Context, req *GetUserRequest) (*GetUserResponse, error) {
    start := time.Now()

    // 创建 span
    ctx, span := s.tracer.Start(ctx, "GetUser",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("user.id", req.UserId),
            attribute.String("rpc.system", "grpc"),
            attribute.String("rpc.service", "UserService"),
            attribute.String("rpc.method", "GetUser"),
        ),
    )
    defer span.End()

    // 从 metadata 中提取额外信息
    if md, ok := metadata.FromIncomingContext(ctx); ok {
        if requestID := md.Get("x-request-id"); len(requestID) > 0 {
            span.SetAttributes(attribute.String("request.id", requestID[0]))
        }
    }

    // 业务逻辑
    user, err := s.fetchUserFromDB(ctx, req.UserId)
    if err != nil {
        span.RecordError(err)
        
        // 记录指标
        s.recordMetrics(ctx, "GetUser", "error", time.Since(start))
        
        return nil, status.Errorf(codes.NotFound, "用户不存在: %v", err)
    }

    // 成功响应
    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )
    span.AddEvent("用户查询成功")

    // 记录指标
    s.recordMetrics(ctx, "GetUser", "success", time.Since(start))

    return &GetUserResponse{
        User: user,
    }, nil
}

// CreateUser 创建用户
func (s *UserService) CreateUser(ctx context.Context, req *CreateUserRequest) (*CreateUserResponse, error) {
    start := time.Now()

    ctx, span := s.tracer.Start(ctx, "CreateUser",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("user.name", req.Name),
            attribute.String("user.email", req.Email),
        ),
    )
    defer span.End()

    // 验证输入
    if err := s.validateCreateUserRequest(req); err != nil {
        span.RecordError(err)
        s.recordMetrics(ctx, "CreateUser", "validation_error", time.Since(start))
        return nil, status.Errorf(codes.InvalidArgument, "验证失败: %v", err)
    }

    // 创建用户
    user, err := s.createUserInDB(ctx, req)
    if err != nil {
        span.RecordError(err)
        s.recordMetrics(ctx, "CreateUser", "error", time.Since(start))
        return nil, status.Errorf(codes.Internal, "创建用户失败: %v", err)
    }

    span.SetAttributes(attribute.String("user.id", user.Id))
    span.AddEvent("用户创建成功")

    s.recordMetrics(ctx, "CreateUser", "success", time.Since(start))

    return &CreateUserResponse{
        User: user,
    }, nil
}

// fetchUserFromDB 从数据库获取用户
func (s *UserService) fetchUserFromDB(ctx context.Context, userID string) (*User, error) {
    ctx, span := s.tracer.Start(ctx, "fetchUserFromDB",
        trace.WithAttributes(
            attribute.String("db.operation", "SELECT"),
            attribute.String("db.table", "users"),
        ),
    )
    defer span.End()

    // 模拟数据库查询
    time.Sleep(50 * time.Millisecond)

    return &User{
        Id:    userID,
        Name:  "张三",
        Email: "zhangsan@example.com",
    }, nil
}

// createUserInDB 在数据库中创建用户
func (s *UserService) createUserInDB(ctx context.Context, req *CreateUserRequest) (*User, error) {
    ctx, span := s.tracer.Start(ctx, "createUserInDB",
        trace.WithAttributes(
            attribute.String("db.operation", "INSERT"),
            attribute.String("db.table", "users"),
        ),
    )
    defer span.End()

    // 模拟数据库操作
    time.Sleep(100 * time.Millisecond)

    return &User{
        Id:    "user-" + time.Now().Format("20060102150405"),
        Name:  req.Name,
        Email: req.Email,
    }, nil
}

// validateCreateUserRequest 验证创建用户请求
func (s *UserService) validateCreateUserRequest(req *CreateUserRequest) error {
    if req.Name == "" {
        return fmt.Errorf("用户名不能为空")
    }
    if req.Email == "" {
        return fmt.Errorf("邮箱不能为空")
    }
    return nil
}

// recordMetrics 记录指标
func (s *UserService) recordMetrics(ctx context.Context, method, status string, duration time.Duration) {
    attrs := metric.WithAttributes(
        attribute.String("method", method),
        attribute.String("status", status),
    )

    s.requestCounter.Add(ctx, 1, attrs)
    s.durationHisto.Record(ctx, float64(duration.Milliseconds()), attrs)
}

// StartGRPCServer 启动 gRPC 服务器
func StartGRPCServer(port int) error {
    // 创建 gRPC 服务器，集成 OpenTelemetry
    server := grpc.NewServer(
        grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
        grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
        grpc.ChainUnaryInterceptor(
            loggingInterceptor(),
            recoveryInterceptor(),
            metricsInterceptor(),
        ),
    )

    // 注册服务
    userService, err := NewUserService()
    if err != nil {
        return fmt.Errorf("创建用户服务失败: %w", err)
    }

    RegisterUserServiceServer(server, userService)

    // 启动服务器
    lis, err := net.Listen("tcp", fmt.Sprintf(":%d", port))
    if err != nil {
        return fmt.Errorf("监听端口失败: %w", err)
    }

    return server.Serve(lis)
}

// loggingInterceptor 日志拦截器
func loggingInterceptor() grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
        start := time.Now()

        // 提取 trace ID
        span := trace.SpanFromContext(ctx)
        traceID := span.SpanContext().TraceID().String()

        log.Printf("[gRPC] Method: %s, TraceID: %s, Started", info.FullMethod, traceID)

        resp, err := handler(ctx, req)

        duration := time.Since(start)
        status := "success"
        if err != nil {
            status = "error"
        }

        log.Printf("[gRPC] Method: %s, TraceID: %s, Status: %s, Duration: %v", 
            info.FullMethod, traceID, status, duration)

        return resp, err
    }
}

// recoveryInterceptor 恢复拦截器
func recoveryInterceptor() grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (resp interface{}, err error) {
        defer func() {
            if r := recover(); r != nil {
                span := trace.SpanFromContext(ctx)
                span.RecordError(fmt.Errorf("panic recovered: %v", r))
                err = status.Errorf(codes.Internal, "内部错误: %v", r)
            }
        }()

        return handler(ctx, req)
    }
}

// metricsInterceptor 指标拦截器
func metricsInterceptor() grpc.UnaryServerInterceptor {
    meter := otel.Meter("grpc-interceptor")
    
    activeRequests, _ := meter.Int64UpDownCounter(
        "grpc.server.active_requests",
        metric.WithDescription("活跃请求数"),
    )

    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
        activeRequests.Add(ctx, 1)
        defer activeRequests.Add(ctx, -1)

        return handler(ctx, req)
    }
}
```

### 2. gRPC 客户端集成

```go
package grpcclient

import (
    "context"
    "fmt"
    "time"

    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
    "google.golang.org/grpc/metadata"

    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// UserServiceClient gRPC 客户端包装器
type UserServiceClient struct {
    client UserServiceClient
    tracer trace.Tracer
    conn   *grpc.ClientConn
}

// NewUserServiceClient 创建客户端
func NewUserServiceClient(address string) (*UserServiceClient, error) {
    // 创建带 OpenTelemetry 的 gRPC 连接
    conn, err := grpc.Dial(
        address,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
        grpc.WithChainUnaryInterceptor(
            retryInterceptor(3),
            timeoutInterceptor(5*time.Second),
        ),
    )
    if err != nil {
        return nil, fmt.Errorf("连接 gRPC 服务器失败: %w", err)
    }

    return &UserServiceClient{
        client: NewUserServiceClient(conn),
        tracer: otel.Tracer("user-service-client"),
        conn:   conn,
    }, nil
}

// GetUser 获取用户
func (c *UserServiceClient) GetUser(ctx context.Context, userID string) (*User, error) {
    ctx, span := c.tracer.Start(ctx, "UserServiceClient.GetUser",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("user.id", userID),
            attribute.String("rpc.system", "grpc"),
        ),
    )
    defer span.End()

    // 添加自定义 metadata
    md := metadata.New(map[string]string{
        "x-request-id": generateRequestID(),
        "x-client-name": "user-service-client",
    })
    ctx = metadata.NewOutgoingContext(ctx, md)

    // 调用 gRPC 方法
    resp, err := c.client.GetUser(ctx, &GetUserRequest{
        UserId: userID,
    })

    if err != nil {
        span.RecordError(err)
        return nil, fmt.Errorf("获取用户失败: %w", err)
    }

    span.SetAttributes(
        attribute.String("user.name", resp.User.Name),
    )

    return resp.User, nil
}

// Close 关闭连接
func (c *UserServiceClient) Close() error {
    return c.conn.Close()
}

// retryInterceptor 重试拦截器
func retryInterceptor(maxRetries int) grpc.UnaryClientInterceptor {
    return func(ctx context.Context, method string, req, reply interface{}, cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {
        var err error
        
        for i := 0; i < maxRetries; i++ {
            err = invoker(ctx, method, req, reply, cc, opts...)
            
            if err == nil {
                return nil
            }

            // 检查是否应该重试
            if !shouldRetry(err) {
                return err
            }

            // 指数退避
            backoff := time.Duration(i+1) * 100 * time.Millisecond
            time.Sleep(backoff)

            span := trace.SpanFromContext(ctx)
            span.AddEvent("重试请求", trace.WithAttributes(
                attribute.Int("retry.attempt", i+1),
            ))
        }

        return err
    }
}

// timeoutInterceptor 超时拦截器
func timeoutInterceptor(timeout time.Duration) grpc.UnaryClientInterceptor {
    return func(ctx context.Context, method string, req, reply interface{}, cc *grpc.ClientConn, invoker grpc.UnaryInvoker, opts ...grpc.CallOption) error {
        ctx, cancel := context.WithTimeout(ctx, timeout)
        defer cancel()

        return invoker(ctx, method, req, reply, cc, opts...)
    }
}

// shouldRetry 判断是否应该重试
func shouldRetry(err error) bool {
    // 实现重试逻辑
    return true
}

// generateRequestID 生成请求 ID
func generateRequestID() string {
    return fmt.Sprintf("req-%d", time.Now().UnixNano())
}
```

### 3. gRPC 拦截器链

```go
package interceptors

import (
    "context"
    "time"

    "google.golang.org/grpc"
    "google.golang.org/grpc/codes"
    "google.golang.org/grpc/status"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// InterceptorChain 拦截器链管理器
type InterceptorChain struct {
    tracer trace.Tracer
    meter  metric.Meter
}

// NewInterceptorChain 创建拦截器链
func NewInterceptorChain() *InterceptorChain {
    return &InterceptorChain{
        tracer: otel.Tracer("interceptor-chain"),
        meter:  otel.Meter("interceptor-chain"),
    }
}

// AuthenticationInterceptor 认证拦截器
func (ic *InterceptorChain) AuthenticationInterceptor() grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
        ctx, span := ic.tracer.Start(ctx, "authentication")
        defer span.End()

        // 从 metadata 中提取认证信息
        token := extractToken(ctx)
        
        if token == "" {
            span.RecordError(fmt.Errorf("缺少认证令牌"))
            return nil, status.Errorf(codes.Unauthenticated, "缺少认证令牌")
        }

        // 验证令牌
        userID, err := validateToken(token)
        if err != nil {
            span.RecordError(err)
            return nil, status.Errorf(codes.Unauthenticated, "认证失败")
        }

        span.SetAttributes(attribute.String("user.id", userID))
        
        // 将用户信息添加到 context
        ctx = context.WithValue(ctx, "userID", userID)

        return handler(ctx, req)
    }
}

// RateLimitInterceptor 限流拦截器
func (ic *InterceptorChain) RateLimitInterceptor(limiter RateLimiter) grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
        ctx, span := ic.tracer.Start(ctx, "rate-limit")
        defer span.End()

        if !limiter.Allow() {
            span.SetAttributes(attribute.Bool("rate_limited", true))
            return nil, status.Errorf(codes.ResourceExhausted, "请求频率超限")
        }

        return handler(ctx, req)
    }
}

// ValidationInterceptor 验证拦截器
func (ic *InterceptorChain) ValidationInterceptor() grpc.UnaryServerInterceptor {
    return func(ctx context.Context, req interface{}, info *grpc.UnaryServerInfo, handler grpc.UnaryHandler) (interface{}, error) {
        ctx, span := ic.tracer.Start(ctx, "validation")
        defer span.End()

        // 验证请求
        if validator, ok := req.(interface{ Validate() error }); ok {
            if err := validator.Validate(); err != nil {
                span.RecordError(err)
                return nil, status.Errorf(codes.InvalidArgument, "验证失败: %v", err)
            }
        }

        return handler(ctx, req)
    }
}
```

---

## REST API 微服务集成

### 4. RESTful 服务实现

```go
package restapi

import (
    "encoding/json"
    "net/http"
    "time"

    "github.com/gorilla/mux"
    
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// UserAPIServer REST API 服务器
type UserAPIServer struct {
    router *mux.Router
    tracer trace.Tracer
}

// NewUserAPIServer 创建 REST API 服务器
func NewUserAPIServer() *UserAPIServer {
    server := &UserAPIServer{
        router: mux.NewRouter(),
        tracer: otel.Tracer("user-api"),
    }

    server.setupRoutes()
    return server
}

// setupRoutes 设置路由
func (s *UserAPIServer) setupRoutes() {
    // 使用 OpenTelemetry HTTP 中间件
    s.router.Use(otelhttp.NewMiddleware("user-api"))
    s.router.Use(loggingMiddleware)
    s.router.Use(corsMiddleware)

    // 用户路由
    s.router.HandleFunc("/api/v1/users/{id}", s.GetUser).Methods("GET")
    s.router.HandleFunc("/api/v1/users", s.CreateUser).Methods("POST")
    s.router.HandleFunc("/api/v1/users/{id}", s.UpdateUser).Methods("PUT")
    s.router.HandleFunc("/api/v1/users/{id}", s.DeleteUser).Methods("DELETE")

    // 健康检查
    s.router.HandleFunc("/health", s.HealthCheck).Methods("GET")
}

// GetUser 获取用户
func (s *UserAPIServer) GetUser(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    ctx, span := s.tracer.Start(ctx, "GetUser",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("http.method", r.Method),
            attribute.String("http.route", "/api/v1/users/{id}"),
        ),
    )
    defer span.End()

    vars := mux.Vars(r)
    userID := vars["id"]

    span.SetAttributes(attribute.String("user.id", userID))

    // 获取用户
    user, err := s.fetchUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        http.Error(w, "用户不存在", http.StatusNotFound)
        return
    }

    // 返回响应
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusOK)
    json.NewEncoder(w).Encode(user)

    span.SetStatus(codes.Ok, "成功")
}

// CreateUser 创建用户
func (s *UserAPIServer) CreateUser(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    ctx, span := s.tracer.Start(ctx, "CreateUser",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    var req CreateUserRequest
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        span.RecordError(err)
        http.Error(w, "无效的请求", http.StatusBadRequest)
        return
    }

    span.SetAttributes(
        attribute.String("user.name", req.Name),
        attribute.String("user.email", req.Email),
    )

    // 创建用户
    user, err := s.createUser(ctx, &req)
    if err != nil {
        span.RecordError(err)
        http.Error(w, "创建用户失败", http.StatusInternalServerError)
        return
    }

    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusCreated)
    json.NewEncoder(w).Encode(user)
}

// Start 启动服务器
func (s *UserAPIServer) Start(port int) error {
    addr := fmt.Sprintf(":%d", port)
    
    server := &http.Server{
        Addr:         addr,
        Handler:      s.router,
        ReadTimeout:  15 * time.Second,
        WriteTimeout: 15 * time.Second,
        IdleTimeout:  60 * time.Second,
    }

    return server.ListenAndServe()
}

// loggingMiddleware 日志中间件
func loggingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()

        // 提取 trace ID
        span := trace.SpanFromContext(r.Context())
        traceID := span.SpanContext().TraceID().String()

        log.Printf("[HTTP] %s %s TraceID=%s", r.Method, r.URL.Path, traceID)

        next.ServeHTTP(w, r)

        log.Printf("[HTTP] %s %s completed in %v", r.Method, r.URL.Path, time.Since(start))
    })
}

// corsMiddleware CORS 中间件
func corsMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        w.Header().Set("Access-Control-Allow-Origin", "*")
        w.Header().Set("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS")
        w.Header().Set("Access-Control-Allow-Headers", "Content-Type, Authorization")

        if r.Method == "OPTIONS" {
            w.WriteHeader(http.StatusOK)
            return
        }

        next.ServeHTTP(w, r)
    })
}
```

### 5. HTTP 客户端追踪

```go
package httpclient

import (
    "context"
    "fmt"
    "net/http"
    "time"

    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TracedHTTPClient 带追踪的 HTTP 客户端
type TracedHTTPClient struct {
    client *http.Client
    tracer trace.Tracer
}

// NewTracedHTTPClient 创建客户端
func NewTracedHTTPClient() *TracedHTTPClient {
    return &TracedHTTPClient{
        client: &http.Client{
            Transport: otelhttp.NewTransport(http.DefaultTransport),
            Timeout:   30 * time.Second,
        },
        tracer: otel.Tracer("http-client"),
    }
}

// Get 发送 GET 请求
func (c *TracedHTTPClient) Get(ctx context.Context, url string) (*http.Response, error) {
    ctx, span := c.tracer.Start(ctx, "HTTP GET",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("http.method", "GET"),
            attribute.String("http.url", url),
        ),
    )
    defer span.End()

    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    resp, err := c.client.Do(req)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(
        attribute.Int("http.status_code", resp.StatusCode),
    )

    return resp, nil
}
```

---

## GraphQL 微服务集成

### 6. GraphQL 服务器集成

```go
package graphqlservice

import (
    "context"
    "net/http"

    "github.com/graphql-go/graphql"
    "github.com/graphql-go/handler"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// GraphQLServer GraphQL 服务器
type GraphQLServer struct {
    schema graphql.Schema
    tracer trace.Tracer
}

// NewGraphQLServer 创建 GraphQL 服务器
func NewGraphQLServer() (*GraphQLServer, error) {
    server := &GraphQLServer{
        tracer: otel.Tracer("graphql-server"),
    }

    schema, err := server.buildSchema()
    if err != nil {
        return nil, err
    }

    server.schema = schema
    return server, nil
}

// buildSchema 构建 GraphQL Schema
func (s *GraphQLServer) buildSchema() (graphql.Schema, error) {
    // 用户类型
    userType := graphql.NewObject(graphql.ObjectConfig{
        Name: "User",
        Fields: graphql.Fields{
            "id":    &graphql.Field{Type: graphql.String},
            "name":  &graphql.Field{Type: graphql.String},
            "email": &graphql.Field{Type: graphql.String},
        },
    })

    // 查询
    queryType := graphql.NewObject(graphql.ObjectConfig{
        Name: "Query",
        Fields: graphql.Fields{
            "user": &graphql.Field{
                Type: userType,
                Args: graphql.FieldConfigArgument{
                    "id": &graphql.ArgumentConfig{
                        Type: graphql.String,
                    },
                },
                Resolve: s.resolveUser,
            },
        },
    })

    // 变更
    mutationType := graphql.NewObject(graphql.ObjectConfig{
        Name: "Mutation",
        Fields: graphql.Fields{
            "createUser": &graphql.Field{
                Type: userType,
                Args: graphql.FieldConfigArgument{
                    "name": &graphql.ArgumentConfig{
                        Type: graphql.NewNonNull(graphql.String),
                    },
                    "email": &graphql.ArgumentConfig{
                        Type: graphql.NewNonNull(graphql.String),
                    },
                },
                Resolve: s.resolveCreateUser,
            },
        },
    })

    return graphql.NewSchema(graphql.SchemaConfig{
        Query:    queryType,
        Mutation: mutationType,
    })
}

// resolveUser 解析用户查询
func (s *GraphQLServer) resolveUser(p graphql.ResolveParams) (interface{}, error) {
    ctx := p.Context
    ctx, span := s.tracer.Start(ctx, "resolveUser",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("graphql.field", "user"),
        ),
    )
    defer span.End()

    userID, ok := p.Args["id"].(string)
    if !ok {
        return nil, fmt.Errorf("无效的用户 ID")
    }

    span.SetAttributes(attribute.String("user.id", userID))

    // 查询用户
    user, err := s.fetchUser(ctx, userID)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return user, nil
}

// resolveCreateUser 解析创建用户变更
func (s *GraphQLServer) resolveCreateUser(p graphql.ResolveParams) (interface{}, error) {
    ctx := p.Context
    ctx, span := s.tracer.Start(ctx, "resolveCreateUser",
        trace.WithAttributes(
            attribute.String("graphql.field", "createUser"),
        ),
    )
    defer span.End()

    name := p.Args["name"].(string)
    email := p.Args["email"].(string)

    span.SetAttributes(
        attribute.String("user.name", name),
        attribute.String("user.email", email),
    )

    // 创建用户
    user, err := s.createUser(ctx, name, email)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return user, nil
}

// Start 启动服务器
func (s *GraphQLServer) Start(port int) error {
    h := handler.New(&handler.Config{
        Schema:   &s.schema,
        Pretty:   true,
        GraphiQL: true,
    })

    // 包装 OpenTelemetry 中间件
    http.Handle("/graphql", otelhttp.NewHandler(h, "graphql"))

    return http.ListenAndServe(fmt.Sprintf(":%d", port), nil)
}
```

---

## 服务间通信模式

### 7. 分布式追踪传播

```go
package propagation

import (
    "context"
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// PropagationManager 传播管理器
type PropagationManager struct {
    propagator propagation.TextMapPropagator
}

// NewPropagationManager 创建传播管理器
func NewPropagationManager() *PropagationManager {
    return &PropagationManager{
        propagator: otel.GetTextMapPropagator(),
    }
}

// InjectHTTP 注入 HTTP 头
func (pm *PropagationManager) InjectHTTP(ctx context.Context, header http.Header) {
    pm.propagator.Inject(ctx, propagation.HeaderCarrier(header))
}

// ExtractHTTP 从 HTTP 头提取
func (pm *PropagationManager) ExtractHTTP(ctx context.Context, header http.Header) context.Context {
    return pm.propagator.Extract(ctx, propagation.HeaderCarrier(header))
}
```

### 8. 服务网格集成

```go
package servicemesh

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ServiceMeshIntegration 服务网格集成
type ServiceMeshIntegration struct {
    tracer trace.Tracer
}

// NewServiceMeshIntegration 创建服务网格集成
func NewServiceMeshIntegration() *ServiceMeshIntegration {
    return &ServiceMeshIntegration{
        tracer: otel.Tracer("service-mesh"),
    }
}

// CallService 调用服务（通过服务网格）
func (smi *ServiceMeshIntegration) CallService(ctx context.Context, serviceName string) error {
    ctx, span := smi.tracer.Start(ctx, "CallService",
        trace.WithAttributes(
            attribute.String("service.name", serviceName),
            attribute.String("service.mesh", "istio"),
        ),
    )
    defer span.End()

    // 服务调用逻辑
    return nil
}
```

---

## 微服务可观测性最佳实践

### 9. 统一可观测性层

```go
package observability

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// ObservabilityLayer 统一可观测性层
type ObservabilityLayer struct {
    tracer trace.Tracer
    meter  metric.Meter
}

// NewObservabilityLayer 创建可观测性层
func NewObservabilityLayer(serviceName string) *ObservabilityLayer {
    return &ObservabilityLayer{
        tracer: otel.Tracer(serviceName),
        meter:  otel.Meter(serviceName),
    }
}

// TraceOperation 追踪操作
func (ol *ObservabilityLayer) TraceOperation(ctx context.Context, operationName string, fn func(context.Context) error) error {
    ctx, span := ol.tracer.Start(ctx, operationName)
    defer span.End()

    if err := fn(ctx); err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}
```

### 10. 服务健康检查

```go
package health

import (
    "context"
    "net/http"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// HealthChecker 健康检查器
type HealthChecker struct {
    tracer trace.Tracer
}

// NewHealthChecker 创建健康检查器
func NewHealthChecker() *HealthChecker {
    return &HealthChecker{
        tracer: otel.Tracer("health-checker"),
    }
}

// CheckHealth 检查健康状态
func (hc *HealthChecker) CheckHealth(w http.ResponseWriter, r *http.Request) {
    ctx, span := hc.tracer.Start(r.Context(), "health-check")
    defer span.End()

    // 执行健康检查
    if err := hc.performChecks(ctx); err != nil {
        span.RecordError(err)
        w.WriteHeader(http.StatusServiceUnavailable)
        return
    }

    w.WriteHeader(http.StatusOK)
    w.Write([]byte("OK"))
}

// performChecks 执行检查
func (hc *HealthChecker) performChecks(ctx context.Context) error {
    // 检查逻辑
    return nil
}
```

---

## 总结

本文档提供了 Go 微服务架构与 OTLP 的完整集成方案，涵盖：

### 核心集成

1. ✅ **gRPC 服务** - 服务端、客户端、拦截器链
2. ✅ **REST API** - HTTP 服务器、客户端、中间件
3. ✅ **GraphQL** - Schema 定义、Resolver 追踪
4. ✅ **服务间通信** - Context 传播、分布式追踪

### 可观测性模式

1. ✅ **统一可观测性** - Traces、Metrics、Logs 关联
2. ✅ **服务网格集成** - Istio、Linkerd 兼容
3. ✅ **健康检查** - 服务健康监控
4. ✅ **错误处理** - 统一错误追踪

### 相关文档

- [Go_1.25.1_完整集成指南.md](./01_Go_1.25.1_完整集成指南.md)
- [Go并发模式与OTLP集成.md](./02_Go并发模式与OTLP集成.md)
- [Go主流框架深度集成指南.md](./09_Go主流框架深度集成指南.md)
- [Go容器化与Kubernetes深度集成.md](./08_Go容器化与Kubernetes深度集成.md)

# 51. gRPC 完整集成指南与最佳实践

## 📚 目录

- [51. gRPC 完整集成指南与最佳实践](#51-grpc-完整集成指南与最佳实践)
  - [📚 目录](#-目录)
  - [1. gRPC 概述](#1-grpc-概述)
    - [1.1 什么是 gRPC](#11-什么是-grpc)
    - [1.2 依赖版本](#12-依赖版本)
  - [2. Protocol Buffers 定义](#2-protocol-buffers-定义)
    - [2.1 服务定义](#21-服务定义)
    - [2.2 编译 Protocol Buffers](#22-编译-protocol-buffers)
  - [3. 服务端实现](#3-服务端实现)
    - [3.1 基础服务器](#31-基础服务器)
    - [3.2 启动 gRPC 服务器](#32-启动-grpc-服务器)
  - [4. 客户端实现](#4-客户端实现)
    - [4.1 基础客户端](#41-基础客户端)
  - [5. 流式 RPC](#5-流式-rpc)
    - [5.1 服务端流](#51-服务端流)
    - [5.2 客户端流](#52-客户端流)
    - [5.3 双向流](#53-双向流)
  - [6. OTLP 完整集成](#6-otlp-完整集成)
    - [6.1 服务端拦截器](#61-服务端拦截器)
  - [7. 拦截器模式](#7-拦截器模式)
    - [7.1 认证拦截器](#71-认证拦截器)
    - [7.2 日志拦截器](#72-日志拦截器)
  - [8. 错误处理](#8-错误处理)
    - [8.1 自定义错误](#81-自定义错误)
    - [8.2 错误处理示例](#82-错误处理示例)
  - [9. 生产级实践](#9-生产级实践)
    - [9.1 连接池和负载均衡](#91-连接池和负载均衡)
    - [9.2 健康检查](#92-健康检查)
  - [10. 总结](#10-总结)
    - [核心优势](#核心优势)
    - [最佳实践](#最佳实践)
    - [相关文档](#相关文档)

---

## 1. gRPC 概述

### 1.1 什么是 gRPC

gRPC 是 Google 开发的高性能、开源 RPC 框架，基于 HTTP/2 和 Protocol Buffers。

**核心特点**:

- ✅ 基于 HTTP/2（多路复用、流式传输）
- ✅ Protocol Buffers 序列化（高效、强类型）
- ✅ 支持多种语言
- ✅ 双向流式传输
- ✅ 内置负载均衡和超时
- ✅ 完善的认证机制

### 1.2 依赖版本

```go
// go.mod
module github.com/yourorg/grpc-service

go 1.25.1

require (
    // gRPC
    google.golang.org/grpc v1.69.2
    google.golang.org/protobuf v1.36.0
    
    // OTLP
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc v0.57.0
    
    // 工具
    github.com/grpc-ecosystem/go-grpc-middleware/v2 v2.1.0
)
```

---

## 2. Protocol Buffers 定义

### 2.1 服务定义

```protobuf
// proto/user/v1/user.proto
syntax = "proto3";

package user.v1;

option go_package = "github.com/yourorg/grpc-service/gen/user/v1;userv1";

import "google/protobuf/timestamp.proto";
import "google/protobuf/empty.proto";

// UserService 用户服务
service UserService {
  // CreateUser 创建用户
  rpc CreateUser(CreateUserRequest) returns (CreateUserResponse);
  
  // GetUser 获取用户
  rpc GetUser(GetUserRequest) returns (GetUserResponse);
  
  // ListUsers 列出用户
  rpc ListUsers(ListUsersRequest) returns (ListUsersResponse);
  
  // UpdateUser 更新用户
  rpc UpdateUser(UpdateUserRequest) returns (UpdateUserResponse);
  
  // DeleteUser 删除用户
  rpc DeleteUser(DeleteUserRequest) returns (google.protobuf.Empty);
  
  // StreamUsers 流式获取用户（服务端流）
  rpc StreamUsers(StreamUsersRequest) returns (stream User);
  
  // UpdateUsers 批量更新用户（客户端流）
  rpc UpdateUsers(stream UpdateUserRequest) returns (BatchUpdateResponse);
  
  // Chat 双向流式聊天
  rpc Chat(stream ChatMessage) returns (stream ChatMessage);
}

// User 用户消息
message User {
  string id = 1;
  string email = 2;
  string username = 3;
  google.protobuf.Timestamp created_at = 4;
  google.protobuf.Timestamp updated_at = 5;
}

// CreateUserRequest 创建用户请求
message CreateUserRequest {
  string email = 1;
  string username = 2;
  string password = 3;
}

// CreateUserResponse 创建用户响应
message CreateUserResponse {
  User user = 1;
}

// GetUserRequest 获取用户请求
message GetUserRequest {
  string id = 1;
}

// GetUserResponse 获取用户响应
message GetUserResponse {
  User user = 1;
}

// ListUsersRequest 列出用户请求
message ListUsersRequest {
  int32 page_size = 1;
  string page_token = 2;
}

// ListUsersResponse 列出用户响应
message ListUsersResponse {
  repeated User users = 1;
  string next_page_token = 2;
}

// UpdateUserRequest 更新用户请求
message UpdateUserRequest {
  string id = 1;
  string email = 2;
  string username = 3;
}

// UpdateUserResponse 更新用户响应
message UpdateUserResponse {
  User user = 1;
}

// DeleteUserRequest 删除用户请求
message DeleteUserRequest {
  string id = 1;
}

// StreamUsersRequest 流式用户请求
message StreamUsersRequest {
  int32 batch_size = 1;
}

// BatchUpdateResponse 批量更新响应
message BatchUpdateResponse {
  int32 updated_count = 1;
}

// ChatMessage 聊天消息
message ChatMessage {
  string user_id = 1;
  string content = 2;
  google.protobuf.Timestamp timestamp = 3;
}
```

### 2.2 编译 Protocol Buffers

```bash
# 安装工具
go install google.golang.org/protobuf/cmd/protoc-gen-go@latest
go install google.golang.org/grpc/cmd/protoc-gen-go-grpc@latest

# 编译
protoc \
  --go_out=. \
  --go_opt=paths=source_relative \
  --go-grpc_out=. \
  --go-grpc_opt=paths=source_relative \
  proto/user/v1/user.proto
```

---

## 3. 服务端实现

### 3.1 基础服务器

```go
// internal/server/user_server.go
package server

import (
    "context"
    "time"
    
    "google.golang.org/grpc"
    "google.golang.org/grpc/codes"
    "google.golang.org/grpc/status"
    "google.golang.org/protobuf/types/known/emptypb"
    "google.golang.org/protobuf/types/known/timestamppb"
    
    "go.opentelemetry.io/otel/trace"
    
    userv1 "github.com/yourorg/grpc-service/gen/user/v1"
)

// UserServer 用户服务器
type UserServer struct {
    userv1.UnimplementedUserServiceServer
    
    tracer  trace.Tracer
    service *UserService
}

// NewUserServer 创建用户服务器
func NewUserServer(tracer trace.Tracer, service *UserService) *UserServer {
    return &UserServer{
        tracer:  tracer,
        service: service,
    }
}

// CreateUser 创建用户
func (s *UserServer) CreateUser(ctx context.Context, req *userv1.CreateUserRequest) (*userv1.CreateUserResponse, error) {
    ctx, span := s.tracer.Start(ctx, "UserServer.CreateUser")
    defer span.End()
    
    // 验证请求
    if err := s.validateCreateUserRequest(req); err != nil {
        return nil, status.Error(codes.InvalidArgument, err.Error())
    }
    
    // 调用业务逻辑
    user, err := s.service.CreateUser(ctx, req.GetEmail(), req.GetUsername(), req.GetPassword())
    if err != nil {
        span.RecordError(err)
        return nil, status.Error(codes.Internal, "failed to create user")
    }
    
    return &userv1.CreateUserResponse{
        User: &userv1.User{
            Id:        user.ID,
            Email:     user.Email,
            Username:  user.Username,
            CreatedAt: timestamppb.New(user.CreatedAt),
            UpdatedAt: timestamppb.New(user.UpdatedAt),
        },
    }, nil
}

// GetUser 获取用户
func (s *UserServer) GetUser(ctx context.Context, req *userv1.GetUserRequest) (*userv1.GetUserResponse, error) {
    ctx, span := s.tracer.Start(ctx, "UserServer.GetUser")
    defer span.End()
    
    user, err := s.service.GetUser(ctx, req.GetId())
    if err != nil {
        span.RecordError(err)
        if err == ErrUserNotFound {
            return nil, status.Error(codes.NotFound, "user not found")
        }
        return nil, status.Error(codes.Internal, "failed to get user")
    }
    
    return &userv1.GetUserResponse{
        User: &userv1.User{
            Id:        user.ID,
            Email:     user.Email,
            Username:  user.Username,
            CreatedAt: timestamppb.New(user.CreatedAt),
            UpdatedAt: timestamppb.New(user.UpdatedAt),
        },
    }, nil
}

// ListUsers 列出用户
func (s *UserServer) ListUsers(ctx context.Context, req *userv1.ListUsersRequest) (*userv1.ListUsersResponse, error) {
    ctx, span := s.tracer.Start(ctx, "UserServer.ListUsers")
    defer span.End()
    
    pageSize := req.GetPageSize()
    if pageSize == 0 {
        pageSize = 10
    }
    
    users, nextToken, err := s.service.ListUsers(ctx, int(pageSize), req.GetPageToken())
    if err != nil {
        span.RecordError(err)
        return nil, status.Error(codes.Internal, "failed to list users")
    }
    
    pbUsers := make([]*userv1.User, len(users))
    for i, user := range users {
        pbUsers[i] = &userv1.User{
            Id:        user.ID,
            Email:     user.Email,
            Username:  user.Username,
            CreatedAt: timestamppb.New(user.CreatedAt),
            UpdatedAt: timestamppb.New(user.UpdatedAt),
        }
    }
    
    return &userv1.ListUsersResponse{
        Users:         pbUsers,
        NextPageToken: nextToken,
    }, nil
}

// DeleteUser 删除用户
func (s *UserServer) DeleteUser(ctx context.Context, req *userv1.DeleteUserRequest) (*emptypb.Empty, error) {
    ctx, span := s.tracer.Start(ctx, "UserServer.DeleteUser")
    defer span.End()
    
    if err := s.service.DeleteUser(ctx, req.GetId()); err != nil {
        span.RecordError(err)
        return nil, status.Error(codes.Internal, "failed to delete user")
    }
    
    return &emptypb.Empty{}, nil
}

// validateCreateUserRequest 验证创建用户请求
func (s *UserServer) validateCreateUserRequest(req *userv1.CreateUserRequest) error {
    if req.GetEmail() == "" {
        return ErrInvalidEmail
    }
    if req.GetUsername() == "" {
        return ErrInvalidUsername
    }
    if len(req.GetPassword()) < 8 {
        return ErrPasswordTooShort
    }
    return nil
}
```

### 3.2 启动 gRPC 服务器

```go
// cmd/server/main.go
package main

import (
    "context"
    "log"
    "net"
    "os"
    "os/signal"
    "syscall"
    
    "google.golang.org/grpc"
    "google.golang.org/grpc/reflection"
    
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/otel"
    
    "github.com/yourorg/grpc-service/internal/server"
)

func main() {
    // 初始化 OTLP
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())
    
    tracer := otel.Tracer("user-service")
    
    // 创建服务
    userService := server.NewUserService()
    userServer := server.NewUserServer(tracer, userService)
    
    // 创建 gRPC 服务器
    grpcServer := grpc.NewServer(
        grpc.StatsHandler(otelgrpc.NewServerHandler()),
        grpc.UnaryInterceptor(unaryServerInterceptor()),
        grpc.StreamInterceptor(streamServerInterceptor()),
    )
    
    // 注册服务
    userv1.RegisterUserServiceServer(grpcServer, userServer)
    
    // 注册反射（用于 grpcurl 等工具）
    reflection.Register(grpcServer)
    
    // 监听端口
    lis, err := net.Listen("tcp", ":50051")
    if err != nil {
        log.Fatalf("Failed to listen: %v", err)
    }
    
    // 优雅关闭
    go func() {
        sigint := make(chan os.Signal, 1)
        signal.Notify(sigint, os.Interrupt, syscall.SIGTERM)
        <-sigint
        
        log.Println("Shutting down gRPC server...")
        grpcServer.GracefulStop()
    }()
    
    log.Println("gRPC server starting on :50051")
    if err := grpcServer.Serve(lis); err != nil {
        log.Fatalf("Failed to serve: %v", err)
    }
}
```

---

## 4. 客户端实现

### 4.1 基础客户端

```go
// internal/client/user_client.go
package client

import (
    "context"
    "time"
    
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
    
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    
    userv1 "github.com/yourorg/grpc-service/gen/user/v1"
)

// UserClient 用户客户端
type UserClient struct {
    conn   *grpc.ClientConn
    client userv1.UserServiceClient
}

// NewUserClient 创建用户客户端
func NewUserClient(address string) (*UserClient, error) {
    // 创建连接
    conn, err := grpc.NewClient(
        address,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithStatsHandler(otelgrpc.NewClientHandler()),
        grpc.WithUnaryInterceptor(unaryClientInterceptor()),
        grpc.WithStreamInterceptor(streamClientInterceptor()),
    )
    if err != nil {
        return nil, err
    }
    
    client := userv1.NewUserServiceClient(conn)
    
    return &UserClient{
        conn:   conn,
        client: client,
    }, nil
}

// Close 关闭连接
func (c *UserClient) Close() error {
    return c.conn.Close()
}

// CreateUser 创建用户
func (c *UserClient) CreateUser(ctx context.Context, email, username, password string) (*userv1.User, error) {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    resp, err := c.client.CreateUser(ctx, &userv1.CreateUserRequest{
        Email:    email,
        Username: username,
        Password: password,
    })
    if err != nil {
        return nil, err
    }
    
    return resp.GetUser(), nil
}

// GetUser 获取用户
func (c *UserClient) GetUser(ctx context.Context, id string) (*userv1.User, error) {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    resp, err := c.client.GetUser(ctx, &userv1.GetUserRequest{
        Id: id,
    })
    if err != nil {
        return nil, err
    }
    
    return resp.GetUser(), nil
}

// ListUsers 列出用户
func (c *UserClient) ListUsers(ctx context.Context, pageSize int32, pageToken string) ([]*userv1.User, string, error) {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    resp, err := c.client.ListUsers(ctx, &userv1.ListUsersRequest{
        PageSize:  pageSize,
        PageToken: pageToken,
    })
    if err != nil {
        return nil, "", err
    }
    
    return resp.GetUsers(), resp.GetNextPageToken(), nil
}
```

---

## 5. 流式 RPC

### 5.1 服务端流

```go
// StreamUsers 服务端流式传输用户
func (s *UserServer) StreamUsers(req *userv1.StreamUsersRequest, stream userv1.UserService_StreamUsersServer) error {
    ctx := stream.Context()
    
    ctx, span := s.tracer.Start(ctx, "UserServer.StreamUsers")
    defer span.End()
    
    batchSize := req.GetBatchSize()
    if batchSize == 0 {
        batchSize = 10
    }
    
    // 分批获取并流式发送
    offset := 0
    for {
        users, err := s.service.GetUsersBatch(ctx, int(batchSize), offset)
        if err != nil {
            span.RecordError(err)
            return status.Error(codes.Internal, "failed to get users")
        }
        
        if len(users) == 0 {
            break
        }
        
        // 发送每个用户
        for _, user := range users {
            if err := stream.Send(&userv1.User{
                Id:        user.ID,
                Email:     user.Email,
                Username:  user.Username,
                CreatedAt: timestamppb.New(user.CreatedAt),
                UpdatedAt: timestamppb.New(user.UpdatedAt),
            }); err != nil {
                span.RecordError(err)
                return err
            }
        }
        
        offset += len(users)
        
        // 检查上下文是否取消
        select {
        case <-ctx.Done():
            return ctx.Err()
        default:
        }
    }
    
    return nil
}

// 客户端调用
func (c *UserClient) StreamUsers(ctx context.Context, batchSize int32) ([]*userv1.User, error) {
    stream, err := c.client.StreamUsers(ctx, &userv1.StreamUsersRequest{
        BatchSize: batchSize,
    })
    if err != nil {
        return nil, err
    }
    
    var users []*userv1.User
    for {
        user, err := stream.Recv()
        if err == io.EOF {
            break
        }
        if err != nil {
            return nil, err
        }
        users = append(users, user)
    }
    
    return users, nil
}
```

### 5.2 客户端流

```go
// UpdateUsers 客户端流式更新用户
func (s *UserServer) UpdateUsers(stream userv1.UserService_UpdateUsersServer) error {
    ctx := stream.Context()
    
    ctx, span := s.tracer.Start(ctx, "UserServer.UpdateUsers")
    defer span.End()
    
    count := 0
    for {
        req, err := stream.Recv()
        if err == io.EOF {
            // 客户端发送完成
            return stream.SendAndClose(&userv1.BatchUpdateResponse{
                UpdatedCount: int32(count),
            })
        }
        if err != nil {
            span.RecordError(err)
            return err
        }
        
        // 更新用户
        if err := s.service.UpdateUser(ctx, req.GetId(), req.GetEmail(), req.GetUsername()); err != nil {
            span.RecordError(err)
            return status.Error(codes.Internal, "failed to update user")
        }
        
        count++
    }
}

// 客户端调用
func (c *UserClient) UpdateUsers(ctx context.Context, updates []*userv1.UpdateUserRequest) (int32, error) {
    stream, err := c.client.UpdateUsers(ctx)
    if err != nil {
        return 0, err
    }
    
    // 发送所有更新请求
    for _, update := range updates {
        if err := stream.Send(update); err != nil {
            return 0, err
        }
    }
    
    // 关闭并接收响应
    resp, err := stream.CloseAndRecv()
    if err != nil {
        return 0, err
    }
    
    return resp.GetUpdatedCount(), nil
}
```

### 5.3 双向流

```go
// Chat 双向流式聊天
func (s *UserServer) Chat(stream userv1.UserService_ChatServer) error {
    ctx := stream.Context()
    
    ctx, span := s.tracer.Start(ctx, "UserServer.Chat")
    defer span.End()
    
    for {
        msg, err := stream.Recv()
        if err == io.EOF {
            return nil
        }
        if err != nil {
            span.RecordError(err)
            return err
        }
        
        // 处理消息并回复
        reply := &userv1.ChatMessage{
            UserId:    "server",
            Content:   "Echo: " + msg.GetContent(),
            Timestamp: timestamppb.Now(),
        }
        
        if err := stream.Send(reply); err != nil {
            span.RecordError(err)
            return err
        }
    }
}

// 客户端调用
func (c *UserClient) Chat(ctx context.Context) error {
    stream, err := c.client.Chat(ctx)
    if err != nil {
        return err
    }
    
    // 启动接收协程
    go func() {
        for {
            msg, err := stream.Recv()
            if err == io.EOF {
                return
            }
            if err != nil {
                log.Printf("Receive error: %v", err)
                return
            }
            log.Printf("Received: %s", msg.GetContent())
        }
    }()
    
    // 发送消息
    messages := []string{"Hello", "How are you?", "Goodbye"}
    for _, content := range messages {
        if err := stream.Send(&userv1.ChatMessage{
            UserId:    "client",
            Content:   content,
            Timestamp: timestamppb.Now(),
        }); err != nil {
            return err
        }
        time.Sleep(time.Second)
    }
    
    return stream.CloseSend()
}
```

---

## 6. OTLP 完整集成

### 6.1 服务端拦截器

```go
// internal/interceptor/tracing.go
package interceptor

import (
    "context"
    
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// UnaryServerInterceptor 一元 RPC 服务端拦截器
func UnaryServerInterceptor() grpc.UnaryServerInterceptor {
    tracer := otel.Tracer("grpc-server")
    
    return func(
        ctx context.Context,
        req interface{},
        info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler,
    ) (interface{}, error) {
        ctx, span := tracer.Start(ctx, info.FullMethod,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("rpc.system", "grpc"),
                attribute.String("rpc.service", info.FullMethod),
            ),
        )
        defer span.End()
        
        // 从 metadata 提取追踪信息
        if md, ok := metadata.FromIncomingContext(ctx); ok {
            for k, v := range md {
                if len(v) > 0 {
                    span.SetAttributes(attribute.String("metadata."+k, v[0]))
                }
            }
        }
        
        // 调用处理器
        resp, err := handler(ctx, req)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        } else {
            span.SetStatus(codes.Ok, "")
        }
        
        return resp, err
    }
}

// StreamServerInterceptor 流式 RPC 服务端拦截器
func StreamServerInterceptor() grpc.StreamServerInterceptor {
    tracer := otel.Tracer("grpc-server")
    
    return func(
        srv interface{},
        ss grpc.ServerStream,
        info *grpc.StreamServerInfo,
        handler grpc.StreamHandler,
    ) error {
        ctx := ss.Context()
        
        ctx, span := tracer.Start(ctx, info.FullMethod,
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                attribute.String("rpc.system", "grpc"),
                attribute.String("rpc.service", info.FullMethod),
                attribute.Bool("rpc.is_client_stream", info.IsClientStream),
                attribute.Bool("rpc.is_server_stream", info.IsServerStream),
            ),
        )
        defer span.End()
        
        // 包装流
        wrappedStream := &wrappedServerStream{
            ServerStream: ss,
            ctx:          ctx,
        }
        
        err := handler(srv, wrappedStream)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        } else {
            span.SetStatus(codes.Ok, "")
        }
        
        return err
    }
}

type wrappedServerStream struct {
    grpc.ServerStream
    ctx context.Context
}

func (w *wrappedServerStream) Context() context.Context {
    return w.ctx
}
```

---

## 7. 拦截器模式

### 7.1 认证拦截器

```go
// AuthInterceptor 认证拦截器
func AuthInterceptor(secret string) grpc.UnaryServerInterceptor {
    return func(
        ctx context.Context,
        req interface{},
        info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler,
    ) (interface{}, error) {
        // 跳过某些方法
        if info.FullMethod == "/user.v1.UserService/HealthCheck" {
            return handler(ctx, req)
        }
        
        // 从 metadata 获取 token
        md, ok := metadata.FromIncomingContext(ctx)
        if !ok {
            return nil, status.Error(codes.Unauthenticated, "missing metadata")
        }
        
        tokens := md.Get("authorization")
        if len(tokens) == 0 {
            return nil, status.Error(codes.Unauthenticated, "missing authorization token")
        }
        
        // 验证 token
        token := strings.TrimPrefix(tokens[0], "Bearer ")
        userID, err := validateToken(token, secret)
        if err != nil {
            return nil, status.Error(codes.Unauthenticated, "invalid token")
        }
        
        // 将用户 ID 存入 context
        ctx = context.WithValue(ctx, "user_id", userID)
        
        return handler(ctx, req)
    }
}
```

### 7.2 日志拦截器

```go
// LoggingInterceptor 日志拦截器
func LoggingInterceptor(logger *zap.Logger) grpc.UnaryServerInterceptor {
    return func(
        ctx context.Context,
        req interface{},
        info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler,
    ) (interface{}, error) {
        start := time.Now()
        
        resp, err := handler(ctx, req)
        
        duration := time.Since(start)
        
        fields := []zap.Field{
            zap.String("method", info.FullMethod),
            zap.Duration("duration", duration),
        }
        
        if err != nil {
            fields = append(fields, zap.Error(err))
            logger.Error("RPC call failed", fields...)
        } else {
            logger.Info("RPC call succeeded", fields...)
        }
        
        return resp, err
    }
}
```

---

## 8. 错误处理

### 8.1 自定义错误

```go
// errors.go
package server

import (
    "google.golang.org/grpc/codes"
    "google.golang.org/grpc/status"
)

// 业务错误
var (
    ErrUserNotFound      = status.Error(codes.NotFound, "user not found")
    ErrInvalidEmail      = status.Error(codes.InvalidArgument, "invalid email")
    ErrInvalidUsername   = status.Error(codes.InvalidArgument, "invalid username")
    ErrPasswordTooShort  = status.Error(codes.InvalidArgument, "password too short")
    ErrEmailExists       = status.Error(codes.AlreadyExists, "email already exists")
    ErrUnauthorized      = status.Error(codes.Unauthenticated, "unauthorized")
    ErrPermissionDenied  = status.Error(codes.PermissionDenied, "permission denied")
)

// NewError 创建错误
func NewError(code codes.Code, message string) error {
    return status.Error(code, message)
}

// NewErrorWithDetails 创建带详情的错误
func NewErrorWithDetails(code codes.Code, message string, details ...interface{}) error {
    st := status.New(code, message)
    st, _ = st.WithDetails(details...)
    return st.Err()
}
```

### 8.2 错误处理示例

```go
// 服务端
func (s *UserServer) CreateUser(ctx context.Context, req *userv1.CreateUserRequest) (*userv1.CreateUserResponse, error) {
    user, err := s.service.CreateUser(ctx, req)
    if err != nil {
        switch err {
        case ErrEmailExists:
            return nil, status.Error(codes.AlreadyExists, "email already exists")
        case ErrInvalidEmail:
            return nil, status.Error(codes.InvalidArgument, "invalid email format")
        default:
            return nil, status.Error(codes.Internal, "internal server error")
        }
    }
    return &userv1.CreateUserResponse{User: user}, nil
}

// 客户端
func (c *UserClient) CreateUser(ctx context.Context, email, username, password string) (*userv1.User, error) {
    user, err := c.client.CreateUser(ctx, &userv1.CreateUserRequest{
        Email:    email,
        Username: username,
        Password: password,
    })
    if err != nil {
        st, ok := status.FromError(err)
        if !ok {
            return nil, err
        }
        
        switch st.Code() {
        case codes.AlreadyExists:
            return nil, fmt.Errorf("email already exists")
        case codes.InvalidArgument:
            return nil, fmt.Errorf("invalid input: %s", st.Message())
        default:
            return nil, fmt.Errorf("failed to create user: %s", st.Message())
        }
    }
    return user, nil
}
```

---

## 9. 生产级实践

### 9.1 连接池和负载均衡

```go
// NewUserClientWithLoadBalancer 创建带负载均衡的客户端
func NewUserClientWithLoadBalancer(endpoints []string) (*UserClient, error) {
    // 使用 round-robin 负载均衡
    target := fmt.Sprintf("dns:///%s", strings.Join(endpoints, ","))
    
    conn, err := grpc.NewClient(
        target,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithStatsHandler(otelgrpc.NewClientHandler()),
        grpc.WithDefaultServiceConfig(`{"loadBalancingPolicy":"round_robin"}`),
    )
    if err != nil {
        return nil, err
    }
    
    return &UserClient{
        conn:   conn,
        client: userv1.NewUserServiceClient(conn),
    }, nil
}
```

### 9.2 健康检查

```proto
// proto/health/v1/health.proto
syntax = "proto3";

package grpc.health.v1;

message HealthCheckRequest {
  string service = 1;
}

message HealthCheckResponse {
  enum ServingStatus {
    UNKNOWN = 0;
    SERVING = 1;
    NOT_SERVING = 2;
    SERVICE_UNKNOWN = 3;
  }
  ServingStatus status = 1;
}

service Health {
  rpc Check(HealthCheckRequest) returns (HealthCheckResponse);
  rpc Watch(HealthCheckRequest) returns (stream HealthCheckResponse);
}
```

```go
// 实现健康检查
import "google.golang.org/grpc/health/grpc_health_v1"

type healthServer struct {
    grpc_health_v1.UnimplementedHealthServer
}

func (h *healthServer) Check(ctx context.Context, req *grpc_health_v1.HealthCheckRequest) (*grpc_health_v1.HealthCheckResponse, error) {
    return &grpc_health_v1.HealthCheckResponse{
        Status: grpc_health_v1.HealthCheckResponse_SERVING,
    }, nil
}

// 注册
grpc_health_v1.RegisterHealthServer(grpcServer, &healthServer{})
```

---

## 10. 总结

### 核心优势

✅ **高性能** - 基于 HTTP/2 和 Protocol Buffers  
✅ **类型安全** - 强类型 API 定义  
✅ **流式传输** - 支持双向流  
✅ **跨语言** - 多语言支持  
✅ **可观测性** - 完整 OTLP 集成

### 最佳实践

1. ✅ 使用 Protocol Buffers 定义 API
2. ✅ 集成 OpenTelemetry 追踪
3. ✅ 实现拦截器链
4. ✅ 优雅的错误处理
5. ✅ 实现健康检查
6. ✅ 配置负载均衡
7. ✅ 使用连接池
8. ✅ 设置超时和重试

### 相关文档

- [49_Chi框架深度集成与最佳实践](./49_Chi框架深度集成与最佳实践.md)
- [36_Go微服务间通信与分布式追踪](./36_Go微服务间通信与分布式追踪.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**gRPC 版本**: v1.69.2

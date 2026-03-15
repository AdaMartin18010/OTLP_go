# Kitex 与 OTLP 完整集成指南 (2025版)

> **最新更新**: 2025年10月  
> **Go版本**: 1.25.1  
> **Kitex版本**: v0.11.0+  
> **OpenTelemetry SDK**: v1.31.0+

## 📋 目录

- [Kitex 与 OTLP 完整集成指南 (2025版)](#kitex-与-otlp-完整集成指南-2025版)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [Kitex 简介](#kitex-简介)
    - [为什么集成 OTLP？](#为什么集成-otlp)
    - [架构图](#架构图)
  - [Kitex 架构概览](#kitex-架构概览)
    - [核心组件](#核心组件)
  - [快速开始](#快速开始)
    - [1. 安装依赖](#1-安装依赖)
    - [2. 初始化 OTLP Provider](#2-初始化-otlp-provider)
  - [Thrift IDL 与代码生成](#thrift-idl-与代码生成)
    - [1. 定义 Thrift IDL](#1-定义-thrift-idl)
    - [2. 生成代码](#2-生成代码)
  - [Server 端集成](#server-端集成)
    - [1. Server 配置](#1-server-配置)
    - [2. Handler 实现](#2-handler-实现)
  - [Client 端集成](#client-端集成)
    - [1. Client 配置](#1-client-配置)
    - [2. Client 自定义 Tracer](#2-client-自定义-tracer)
  - [服务注册与发现](#服务注册与发现)
    - [1. Etcd 集成](#1-etcd-集成)
    - [2. Nacos 集成](#2-nacos-集成)
  - [多协议支持](#多协议支持)
    - [1. Protobuf 协议](#1-protobuf-协议)
    - [2. gRPC 协议](#2-grpc-协议)
  - [流式 RPC 追踪](#流式-rpc-追踪)
    - [1. 定义流式接口](#1-定义流式接口)
    - [2. Server 端流式追踪](#2-server-端流式追踪)
    - [3. Client 端流式追踪](#3-client-端流式追踪)
  - [性能优化](#性能优化)
    - [1. 连接池配置](#1-连接池配置)
    - [2. 采样优化](#2-采样优化)
    - [3. 批量导出优化](#3-批量导出优化)
    - [4. 性能基准测试](#4-性能基准测试)
  - [生产部署](#生产部署)
    - [1. Docker Compose 部署](#1-docker-compose-部署)
    - [2. Kubernetes Deployment](#2-kubernetes-deployment)
    - [3. HPA 自动扩缩容](#3-hpa-自动扩缩容)
  - [最佳实践](#最佳实践)
    - [1. Span 命名规范](#1-span-命名规范)
    - [2. Context 传递](#2-context-传递)
    - [3. 错误处理](#3-错误处理)
    - [4. 属性添加](#4-属性添加)
    - [5. 资源清理](#5-资源清理)
  - [总结](#总结)
    - [Kitex + OTLP 集成优势](#kitex--otlp-集成优势)
    - [性能指标（参考）](#性能指标参考)
    - [推荐配置](#推荐配置)
  - [参考资源](#参考资源)

---

## 概述

### Kitex 简介

**Kitex** 是字节跳动开源的高性能、强可扩展的 Go RPC 框架，主要特点：

- **高性能**: 自研网络库 Netpoll，吞吐量比 gRPC 高 2-4 倍
- **多协议**: 支持 Thrift、Protobuf、gRPC 等多种协议
- **代码生成**: 强大的代码生成工具，自动生成客户端/服务端代码
- **扩展性**: 丰富的中间件和 Suite 机制
- **服务治理**: 内置服务发现、负载均衡、熔断限流等能力

### 为什么集成 OTLP？

1. **分布式追踪**: 在复杂微服务架构中追踪请求链路
2. **性能分析**: 识别性能瓶颈和延迟来源
3. **故障排查**: 快速定位错误和异常
4. **标准化**: 采用 OpenTelemetry 标准，多后端兼容

### 架构图

```text
┌─────────────────────────────────────────────────────────────┐
│                      Client Application                     │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Kitex Client with OTLP Tracer                       │   │
│  │  • Trace Context Injection                           │   │
│  │  • Request Instrumentation                           │   │
│  │  • Error Recording                                   │   │
│  └────────────────────┬─────────────────────────────────┘   │
└───────────────────────┼─────────────────────────────────────┘
                        │ RPC Call (Thrift/Protobuf)
            ┌───────────▼───────────┐
            │  Kitex Server         │
            │  • OTLP Tracer Suite  │
            │  • Span Creation      │
            │  • Metadata Extract   │
            └───────────┬───────────┘
                        │
            ┌───────────▼───────────┐
            │  Business Logic       │
            │  • Handler Tracing    │
            │  • Database Calls     │
            │  • External Services  │
            └───────────┬───────────┘
                        │
            ┌───────────▼───────────┐
            │  OTel Collector       │
            │  • Trace Aggregation  │
            │  • Export to Backends │
            └───────────────────────┘
```

---

## Kitex 架构概览

### 核心组件

```go
// 1. Server 选项
server.WithSuite(oteltracer.NewServerSuite())
server.WithTracer(tracer)
server.WithMiddleware(middleware)

// 2. Client 选项
client.WithSuite(oteltracer.NewClientSuite())
client.WithTracer(tracer)
client.WithMiddleware(middleware)

// 3. 传输层
// Thrift: thrift.NewServer(), thrift.NewClient()
// Protobuf: protobuf.NewServer(), protobuf.NewClient()
```

---

## 快速开始

### 1. 安装依赖

```bash
# 安装 Kitex 工具
go install github.com/cloudwego/kitex/tool/cmd/kitex@latest

# 安装 Thriftgo（如果使用 Thrift）
go install github.com/cloudwego/thriftgo@latest

# 安装 Kitex 核心库
go get github.com/cloudwego/kitex

# 安装 Kitex OpenTelemetry 插件
go get github.com/kitex-contrib/obs-opentelemetry/tracing

# 安装 OpenTelemetry SDK
go get go.opentelemetry.io/otel
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc
go get go.opentelemetry.io/otel/sdk
```

### 2. 初始化 OTLP Provider

```go
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
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

type ProviderConfig struct {
    ServiceName   string
    ServiceVersion string
    Endpoint      string
    SamplerRatio  float64
}

func InitProvider(ctx context.Context, cfg ProviderConfig) (func() error, error) {
    // 创建 OTLP exporter
    conn, err := grpc.NewClient(cfg.Endpoint,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
    )
    if err != nil {
        return nil, err
    }

    exporter, err := otlptracegrpc.New(ctx, otlptracegrpc.WithGRPCConn(conn))
    if err != nil {
        return nil, err
    }

    // 创建 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String(cfg.ServiceName),
            semconv.ServiceVersionKey.String(cfg.ServiceVersion),
            semconv.DeploymentEnvironmentKey.String("production"),
        ),
        resource.WithHost(),
        resource.WithOS(),
        resource.WithProcess(),
    )
    if err != nil {
        return nil, err
    }

    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
        ),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(cfg.SamplerRatio)),
    )

    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return func() error {
        ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
        defer cancel()
        return tp.Shutdown(ctx)
    }, nil
}
```

---

## Thrift IDL 与代码生成

### 1. 定义 Thrift IDL

```thrift
// user.thrift
namespace go user

struct User {
    1: required i64 id
    2: required string name
    3: required string email
    4: optional string phone
    5: required i64 created_at
}

struct GetUserRequest {
    1: required i64 user_id
}

struct GetUserResponse {
    1: required User user
    2: required string message
}

struct CreateUserRequest {
    1: required string name
    2: required string email
    3: optional string phone
}

struct CreateUserResponse {
    1: required i64 user_id
    2: required string message
}

service UserService {
    GetUserResponse GetUser(1: GetUserRequest req)
    CreateUserResponse CreateUser(1: CreateUserRequest req)
}
```

### 2. 生成代码

```bash
# 生成服务端和客户端代码
kitex -module your-module -service user_service user.thrift

# 生成的目录结构：
# .
# ├── kitex_gen/
# │   └── user/
# │       ├── user.go           # Thrift 结构体
# │       ├── userservice.go    # 服务接口
# │       └── ...
# ├── handler.go                # 业务处理逻辑（需要实现）
# └── main.go                   # 服务启动入口（需要实现）
```

---

## Server 端集成

### 1. Server 配置

```go
package main

import (
    "context"
    "log"
    "net"

    "github.com/cloudwego/kitex/server"
    oteltracer "github.com/kitex-contrib/obs-opentelemetry/tracing"

    "your-module/kitex_gen/user/userservice"
    "your-module/pkg/telemetry"
)

func main() {
    // 初始化 OTLP
    ctx := context.Background()
    shutdown, err := telemetry.InitProvider(ctx, telemetry.ProviderConfig{
        ServiceName:    "user-service",
        ServiceVersion: "1.0.0",
        Endpoint:       "localhost:4317",
        SamplerRatio:   1.0,
    })
    if err != nil {
        log.Fatalf("failed to initialize OTLP: %v", err)
    }
    defer shutdown()

    // 创建 Server
    addr, _ := net.ResolveTCPAddr("tcp", ":8888")
    
    svr := userservice.NewServer(
        new(UserServiceImpl),
        server.WithServiceAddr(addr),
        // 添加 OTLP Tracer Suite
        server.WithSuite(oteltracer.NewServerSuite()),
        server.WithServerBasicInfo(&rpcinfo.EndpointBasicInfo{
            ServiceName: "user-service",
        }),
    )

    log.Println("Server started at :8888")
    if err := svr.Run(); err != nil {
        log.Fatalf("server stopped with error: %v", err)
    }
}
```

### 2. Handler 实现

```go
package main

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-module/kitex_gen/user"
)

var tracer = otel.Tracer("user-service-handler")

type UserServiceImpl struct{}

// GetUser 获取用户信息
func (s *UserServiceImpl) GetUser(ctx context.Context, req *user.GetUserRequest) (*user.GetUserResponse, error) {
    // 创建 Span
    ctx, span := tracer.Start(ctx, "UserService.GetUser")
    defer span.End()

    span.SetAttributes(
        attribute.Int64("user.id", req.UserId),
    )

    // 1. 参数验证
    if req.UserId <= 0 {
        err := fmt.Errorf("invalid user_id: %d", req.UserId)
        span.RecordError(err)
        span.SetStatus(codes.Error, "Invalid parameter")
        return nil, err
    }

    // 2. 从数据库获取用户
    userData, err := s.getUserFromDB(ctx, req.UserId)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Database query failed")
        return nil, err
    }

    // 3. 从缓存获取额外信息（演示多层 span）
    _, cacheSpan := tracer.Start(ctx, "GetUserFromCache")
    cacheSpan.SetAttributes(
        attribute.String("cache.system", "redis"),
        attribute.Int64("user.id", req.UserId),
    )
    // ... 缓存逻辑
    cacheSpan.End()

    span.SetStatus(codes.Ok, "Success")
    return &user.GetUserResponse{
        User: userData,
        Message: "success",
    }, nil
}

// CreateUser 创建用户
func (s *UserServiceImpl) CreateUser(ctx context.Context, req *user.CreateUserRequest) (*user.CreateUserResponse, error) {
    ctx, span := tracer.Start(ctx, "UserService.CreateUser")
    defer span.End()

    span.SetAttributes(
        attribute.String("user.name", req.Name),
        attribute.String("user.email", req.Email),
    )

    // 1. 验证参数
    if req.Name == "" || req.Email == "" {
        err := fmt.Errorf("name and email are required")
        span.RecordError(err)
        span.SetStatus(codes.Error, "Invalid parameters")
        return nil, err
    }

    // 2. 插入数据库
    userID, err := s.insertUserToDB(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Database insert failed")
        return nil, err
    }

    span.SetAttributes(attribute.Int64("user.id", userID))
    span.SetStatus(codes.Ok, "User created successfully")

    return &user.CreateUserResponse{
        UserId:  userID,
        Message: "user created successfully",
    }, nil
}

// getUserFromDB 模拟数据库查询
func (s *UserServiceImpl) getUserFromDB(ctx context.Context, userID int64) (*user.User, error) {
    _, span := tracer.Start(ctx, "MySQL.SelectUser")
    defer span.End()

    span.SetAttributes(
        attribute.String("db.system", "mysql"),
        attribute.String("db.operation", "SELECT"),
        attribute.String("db.table", "users"),
        attribute.Int64("db.user_id", userID),
    )

    // 模拟数据库查询
    time.Sleep(10 * time.Millisecond)

    // 返回模拟数据
    return &user.User{
        Id:        userID,
        Name:      "John Doe",
        Email:     "john@example.com",
        Phone:     stringPtr("1234567890"),
        CreatedAt: time.Now().Unix(),
    }, nil
}

// insertUserToDB 模拟数据库插入
func (s *UserServiceImpl) insertUserToDB(ctx context.Context, req *user.CreateUserRequest) (int64, error) {
    _, span := tracer.Start(ctx, "MySQL.InsertUser")
    defer span.End()

    span.SetAttributes(
        attribute.String("db.system", "mysql"),
        attribute.String("db.operation", "INSERT"),
        attribute.String("db.table", "users"),
    )

    // 模拟数据库插入
    time.Sleep(15 * time.Millisecond)

    userID := time.Now().Unix()
    span.SetAttributes(attribute.Int64("db.insert_id", userID))

    return userID, nil
}

func stringPtr(s string) *string {
    return &s
}
```

---

## Client 端集成

### 1. Client 配置

```go
package main

import (
    "context"
    "log"

    "github.com/cloudwego/kitex/client"
    oteltracer "github.com/kitex-contrib/obs-opentelemetry/tracing"

    "your-module/kitex_gen/user"
    "your-module/kitex_gen/user/userservice"
    "your-module/pkg/telemetry"
)

func main() {
    // 初始化 OTLP
    ctx := context.Background()
    shutdown, err := telemetry.InitProvider(ctx, telemetry.ProviderConfig{
        ServiceName:    "user-client",
        ServiceVersion: "1.0.0",
        Endpoint:       "localhost:4317",
        SamplerRatio:   1.0,
    })
    if err != nil {
        log.Fatalf("failed to initialize OTLP: %v", err)
    }
    defer shutdown()

    // 创建 Client
    cli, err := userservice.NewClient(
        "user-service",
        client.WithHostPorts("localhost:8888"),
        // 添加 OTLP Tracer Suite
        client.WithSuite(oteltracer.NewClientSuite()),
    )
    if err != nil {
        log.Fatalf("failed to create client: %v", err)
    }

    // 调用服务
    if err := callUserService(ctx, cli); err != nil {
        log.Fatalf("call failed: %v", err)
    }
}

func callUserService(ctx context.Context, cli userservice.Client) error {
    // GetUser 调用
    getUserResp, err := cli.GetUser(ctx, &user.GetUserRequest{
        UserId: 12345,
    })
    if err != nil {
        return err
    }
    log.Printf("GetUser response: %+v", getUserResp)

    // CreateUser 调用
    createUserResp, err := cli.CreateUser(ctx, &user.CreateUserRequest{
        Name:  "Alice",
        Email: "alice@example.com",
        Phone: stringPtr("9876543210"),
    })
    if err != nil {
        return err
    }
    log.Printf("CreateUser response: %+v", createUserResp)

    return nil
}

func stringPtr(s string) *string {
    return &s
}
```

### 2. Client 自定义 Tracer

```go
package main

import (
    "context"

    "github.com/cloudwego/kitex/client"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-module/kitex_gen/user"
    "your-module/kitex_gen/user/userservice"
)

var clientTracer = otel.Tracer("user-client")

func CallWithCustomTracing(ctx context.Context) error {
    // 创建顶层 Span
    ctx, span := clientTracer.Start(ctx, "CallUserServiceWorkflow")
    defer span.End()

    span.SetAttributes(
        attribute.String("workflow.name", "user-management"),
    )

    // 创建 Client
    cli, err := userservice.NewClient(
        "user-service",
        client.WithHostPorts("localhost:8888"),
        client.WithSuite(oteltracer.NewClientSuite()),
    )
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to create client")
        return err
    }

    // 步骤 1: 创建用户
    createResp, err := cli.CreateUser(ctx, &user.CreateUserRequest{
        Name:  "Bob",
        Email: "bob@example.com",
    })
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "CreateUser failed")
        return err
    }
    span.SetAttributes(attribute.Int64("created.user_id", createResp.UserId))

    // 步骤 2: 获取用户信息
    getResp, err := cli.GetUser(ctx, &user.GetUserRequest{
        UserId: createResp.UserId,
    })
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "GetUser failed")
        return err
    }
    span.SetAttributes(attribute.String("fetched.user_name", getResp.User.Name))

    span.SetStatus(codes.Ok, "Workflow completed successfully")
    return nil
}
```

---

## 服务注册与发现

### 1. Etcd 集成

```go
package main

import (
    "github.com/cloudwego/kitex/client"
    "github.com/cloudwego/kitex/server"
    etcd "github.com/kitex-contrib/registry-etcd"
)

func main() {
    // Server 端注册
    r, err := etcd.NewEtcdRegistry([]string{"localhost:2379"})
    if err != nil {
        panic(err)
    }

    svr := userservice.NewServer(
        new(UserServiceImpl),
        server.WithRegistry(r),
        server.WithServiceAddr(addr),
        server.WithSuite(oteltracer.NewServerSuite()),
    )

    // Client 端发现
    resolver, err := etcd.NewEtcdResolver([]string{"localhost:2379"})
    if err != nil {
        panic(err)
    }

    cli, err := userservice.NewClient(
        "user-service",
        client.WithResolver(resolver),
        client.WithSuite(oteltracer.NewClientSuite()),
    )
}
```

### 2. Nacos 集成

```go
package main

import (
    "github.com/cloudwego/kitex/client"
    "github.com/cloudwego/kitex/server"
    nacos "github.com/kitex-contrib/registry-nacos"
    "github.com/nacos-group/nacos-sdk-go/clients"
    "github.com/nacos-group/nacos-sdk-go/common/constant"
)

func main() {
    // Nacos 配置
    sc := []constant.ServerConfig{
        *constant.NewServerConfig("127.0.0.1", 8848),
    }
    cc := constant.ClientConfig{
        TimeoutMs:           5000,
        NotLoadCacheAtStart: true,
    }

    // Server 注册
    cli, _ := clients.NewNamingClient(
        vo.NacosClientParam{
            ClientConfig:  &cc,
            ServerConfigs: sc,
        },
    )
    r := nacos.NewNacosRegistry(cli)

    svr := userservice.NewServer(
        new(UserServiceImpl),
        server.WithRegistry(r),
        server.WithSuite(oteltracer.NewServerSuite()),
    )

    // Client 发现
    resolver := nacos.NewNacosResolver(cli)
    
    cli, err := userservice.NewClient(
        "user-service",
        client.WithResolver(resolver),
        client.WithSuite(oteltracer.NewClientSuite()),
    )
}
```

---

## 多协议支持

### 1. Protobuf 协议

```protobuf
// user.proto
syntax = "proto3";

package user;
option go_package = "user";

message User {
    int64 id = 1;
    string name = 2;
    string email = 3;
    string phone = 4;
    int64 created_at = 5;
}

message GetUserRequest {
    int64 user_id = 1;
}

message GetUserResponse {
    User user = 1;
    string message = 2;
}

service UserService {
    rpc GetUser(GetUserRequest) returns (GetUserResponse);
}
```

```bash
# 生成 Protobuf 代码
kitex -module your-module -service user_service -type protobuf user.proto
```

### 2. gRPC 协议

```go
package main

import (
    "github.com/cloudwego/kitex/server"
    "github.com/cloudwego/kitex/pkg/transmeta"
    "github.com/cloudwego/kitex/pkg/remote/trans/nphttp2"
)

func main() {
    // 启用 gRPC 传输
    svr := userservice.NewServer(
        new(UserServiceImpl),
        server.WithMetaHandler(transmeta.ServerHTTP2Handler),
        server.WithTransHandlerFactory(nphttp2.NewServerTransHandlerFactory()),
        server.WithSuite(oteltracer.NewServerSuite()),
    )
    
    svr.Run()
}
```

---

## 流式 RPC 追踪

### 1. 定义流式接口

```thrift
// streaming.thrift
service StreamService {
    // 服务端流式
    stream<DataChunk> ServerStream(1: StreamRequest req)
    
    // 客户端流式
    DataResponse ClientStream(1: stream<DataChunk> chunks)
    
    // 双向流式
    stream<DataResponse> BidirectionalStream(1: stream<DataChunk> chunks)
}
```

### 2. Server 端流式追踪

```go
func (s *StreamServiceImpl) ServerStream(ctx context.Context, req *streaming.StreamRequest) (streaming.StreamService_ServerStreamServer, error) {
    ctx, span := tracer.Start(ctx, "StreamService.ServerStream")
    defer span.End()

    span.SetAttributes(
        attribute.Int64("stream.request_id", req.RequestId),
    )

    stream := &serverStreamImpl{
        ctx:    ctx,
        tracer: tracer,
    }

    go func() {
        for i := 0; i < 10; i++ {
            _, chunkSpan := tracer.Start(ctx, "SendChunk")
            chunkSpan.SetAttributes(attribute.Int("chunk.index", i))
            
            // 发送数据块
            stream.Send(&streaming.DataChunk{
                Data: fmt.Sprintf("chunk-%d", i),
            })
            
            chunkSpan.End()
        }
    }()

    return stream, nil
}
```

### 3. Client 端流式追踪

```go
func ClientStreamExample(ctx context.Context, cli streamservice.Client) error {
    ctx, span := tracer.Start(ctx, "ClientStreamExample")
    defer span.End()

    stream, err := cli.ClientStream(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }

    // 发送多个数据块
    for i := 0; i < 5; i++ {
        _, sendSpan := tracer.Start(ctx, "SendDataChunk")
        sendSpan.SetAttributes(attribute.Int("chunk.index", i))

        if err := stream.Send(&streaming.DataChunk{
            Data: fmt.Sprintf("data-%d", i),
        }); err != nil {
            sendSpan.RecordError(err)
            sendSpan.End()
            return err
        }
        sendSpan.End()
    }

    // 接收响应
    resp, err := stream.CloseAndRecv()
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(attribute.String("response.message", resp.Message))
    return nil
}
```

---

## 性能优化

### 1. 连接池配置

```go
import (
    "github.com/cloudwego/kitex/client"
    "github.com/cloudwego/kitex/pkg/connpool"
)

cli, err := userservice.NewClient(
    "user-service",
    client.WithLongConnection(
        connpool.IdleConfig{
            MaxIdlePerAddress: 10,
            MaxIdleGlobal:     100,
            MaxIdleTimeout:    time.Minute,
        },
    ),
    client.WithSuite(oteltracer.NewClientSuite()),
)
```

### 2. 采样优化

```go
// 基于错误的智能采样
type ErrorBasedSampler struct {
    defaultSampler sdktrace.Sampler
    errorSampler   sdktrace.Sampler
}

func (s *ErrorBasedSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 如果请求有错误，100% 采样
    for _, attr := range params.Attributes {
        if attr.Key == "error" && attr.Value.AsBool() {
            return s.errorSampler.ShouldSample(params)
        }
    }
    // 否则使用默认采样率
    return s.defaultSampler.ShouldSample(params)
}

func (s *ErrorBasedSampler) Description() string {
    return "ErrorBasedSampler"
}

// 使用
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(&ErrorBasedSampler{
        defaultSampler: sdktrace.TraceIDRatioBased(0.1),  // 10%
        errorSampler:   sdktrace.AlwaysSample(),          // 100%
    }),
)
```

### 3. 批量导出优化

```go
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        // 更大的批次 = 更高的吞吐量
        sdktrace.WithMaxExportBatchSize(1024),
        // 更短的超时 = 更低的延迟
        sdktrace.WithBatchTimeout(3*time.Second),
        // 更大的队列 = 更少的丢失
        sdktrace.WithMaxQueueSize(4096),
    ),
)
```

### 4. 性能基准测试

```go
func BenchmarkKitexWithTracing(b *testing.B) {
    // 初始化
    ctx := context.Background()
    shutdown, _ := telemetry.InitProvider(ctx, telemetry.ProviderConfig{
        ServiceName:  "benchmark",
        Endpoint:     "localhost:4317",
        SamplerRatio: 0.01, // 1% 采样
    })
    defer shutdown()

    cli, _ := userservice.NewClient(
        "user-service",
        client.WithHostPorts("localhost:8888"),
        client.WithSuite(oteltracer.NewClientSuite()),
    )

    b.ResetTimer()
    b.RunParallel(func(pb *testing.PB) {
        for pb.Next() {
            _, _ = cli.GetUser(ctx, &user.GetUserRequest{UserId: 123})
        }
    })
}

// 结果示例：
// BenchmarkKitexWithTracing-8   100000   11500 ns/op   2800 B/op   38 allocs/op
```

---

## 生产部署

### 1. Docker Compose 部署

```yaml
version: '3.8'

services:
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.112.0
    command: ["--config=/etc/otel-config.yaml"]
    volumes:
      - ./otel-config.yaml:/etc/otel-config.yaml
    ports:
      - "4317:4317"
      - "4318:4318"
    networks:
      - kitex-net

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686"
      - "14250:14250"
    networks:
      - kitex-net

  # Etcd (服务发现)
  etcd:
    image: bitnami/etcd:3.5
    environment:
      - ALLOW_NONE_AUTHENTICATION=yes
    ports:
      - "2379:2379"
    networks:
      - kitex-net

  # User Service (Kitex Server)
  user-service:
    build:
      context: .
      dockerfile: Dockerfile.server
    environment:
      - OTEL_ENDPOINT=otel-collector:4317
      - ETCD_ENDPOINTS=etcd:2379
    depends_on:
      - otel-collector
      - etcd
    ports:
      - "8888:8888"
    networks:
      - kitex-net
    deploy:
      replicas: 3

  # API Gateway (Kitex Client)
  api-gateway:
    build:
      context: .
      dockerfile: Dockerfile.client
    environment:
      - OTEL_ENDPOINT=otel-collector:4317
      - ETCD_ENDPOINTS=etcd:2379
    depends_on:
      - user-service
    ports:
      - "8080:8080"
    networks:
      - kitex-net

networks:
  kitex-net:
    driver: bridge
```

### 2. Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: user-service
  namespace: microservices
spec:
  replicas: 3
  selector:
    matchLabels:
      app: user-service
  template:
    metadata:
      labels:
        app: user-service
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
    spec:
      containers:
      - name: user-service
        image: your-registry/user-service:latest
        ports:
        - containerPort: 8888
          name: rpc
        - containerPort: 9090
          name: metrics
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "otel-collector.observability:4317"
        - name: OTEL_SERVICE_NAME
          value: "user-service"
        - name: ETCD_ENDPOINTS
          value: "etcd.etcd:2379"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          tcpSocket:
            port: 8888
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          tcpSocket:
            port: 8888
          initialDelaySeconds: 10
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: user-service
  namespace: microservices
spec:
  selector:
    app: user-service
  ports:
  - name: rpc
    port: 8888
    targetPort: 8888
  - name: metrics
    port: 9090
    targetPort: 9090
```

### 3. HPA 自动扩缩容

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: user-service-hpa
  namespace: microservices
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: user-service
  minReplicas: 3
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  - type: Pods
    pods:
      metric:
        name: rpc_requests_per_second
      target:
        type: AverageValue
        averageValue: "1000"
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 50
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 30
      - type: Pods
        value: 5
        periodSeconds: 30
      selectPolicy: Max
```

---

## 最佳实践

### 1. Span 命名规范

```go
// ✅ 好的命名
tracer.Start(ctx, "UserService.GetUser")
tracer.Start(ctx, "MySQL.SelectUser")
tracer.Start(ctx, "Redis.GetCache")
tracer.Start(ctx, "HTTP.POST /api/users")

// ❌ 避免的命名
tracer.Start(ctx, "handler")
tracer.Start(ctx, "query")
tracer.Start(ctx, "func123")
```

### 2. Context 传递

```go
// ✅ 正确的 context 传递
func (s *UserServiceImpl) GetUser(ctx context.Context, req *user.GetUserRequest) (*user.GetUserResponse, error) {
    ctx, span := tracer.Start(ctx, "GetUser")
    defer span.End()

    // 传递 ctx 到下层
    userData, err := s.repository.FindByID(ctx, req.UserId)
    return processUser(ctx, userData)
}

// ❌ 错误：创建新的 background context
func (s *UserServiceImpl) GetUser(ctx context.Context, req *user.GetUserRequest) (*user.GetUserResponse, error) {
    newCtx := context.Background() // 丢失了追踪上下文
    return s.repository.FindByID(newCtx, req.UserId)
}
```

### 3. 错误处理

```go
// ✅ 完整的错误记录
if err != nil {
    span.RecordError(err,
        trace.WithAttributes(
            attribute.String("error.type", "database"),
            attribute.String("error.operation", "SELECT"),
            attribute.Int64("user.id", userID),
        ),
    )
    span.SetStatus(codes.Error, err.Error())
    return nil, err
}
```

### 4. 属性添加

```go
// ✅ 使用语义化属性
span.SetAttributes(
    semconv.RPCSystemKey.String("kitex"),
    semconv.RPCServiceKey.String("UserService"),
    semconv.RPCMethodKey.String("GetUser"),
    attribute.Int64("user.id", userID),
    attribute.String("request.source", "api-gateway"),
)
```

### 5. 资源清理

```go
func main() {
    // 初始化
    shutdown, err := telemetry.InitProvider(...)
    if err != nil {
        log.Fatal(err)
    }

    // ✅ 使用 defer 确保清理
    defer func() {
        if err := shutdown(); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }()

    // 或使用 signal 处理
    sigCh := make(chan os.Signal, 1)
    signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)

    go func() {
        <-sigCh
        log.Println("Shutting down gracefully...")
        shutdown()
        os.Exit(0)
    }()

    // 启动服务
    svr.Run()
}
```

---

## 总结

### Kitex + OTLP 集成优势

1. **极致性能**: Kitex 的高性能特性 + OTLP 的低开销追踪
2. **多协议支持**: Thrift、Protobuf、gRPC 全覆盖
3. **完整追踪**: Client → Server → Database 全链路可观测
4. **生态丰富**: 与 Etcd、Nacos 等服务发现无缝集成
5. **生产就绪**: 字节跳动大规模生产验证

### 性能指标（参考）

| 指标 | 无追踪 | 启用 OTLP (1% 采样) | 启用 OTLP (100% 采样) |
|------|--------|---------------------|----------------------|
| QPS | 150K | 148K (-1.3%) | 135K (-10%) |
| P99 延迟 | 8ms | 8.5ms (+6%) | 11ms (+37%) |
| 内存占用 | 50MB | 55MB (+10%) | 80MB (+60%) |
| CPU 使用 | 40% | 42% (+5%) | 52% (+30%) |

### 推荐配置

```go
// 生产环境推荐配置
telemetry.ProviderConfig{
    ServiceName:    "your-service",
    ServiceVersion: "1.0.0",
    Endpoint:       "otel-collector:4317",
    SamplerRatio:   0.1, // 10% 采样
}

// 批量导出配置
sdktrace.WithBatcher(exporter,
    sdktrace.WithMaxExportBatchSize(512),
    sdktrace.WithBatchTimeout(5*time.Second),
    sdktrace.WithMaxQueueSize(2048),
)
```

---

## 参考资源

- [Kitex 官方文档](https://www.cloudwego.io/docs/kitex/)
- [Kitex GitHub](https://github.com/cloudwego/kitex)
- [Kitex OpenTelemetry 插件](https://github.com/kitex-contrib/obs-opentelemetry)
- [OpenTelemetry Go SDK](https://github.com/open-telemetry/opentelemetry-go)
- [Thrift 官方文档](https://thrift.apache.org/)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-12  
**维护者**: OpenTelemetry Go Integration Team

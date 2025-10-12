# Go-Zero 与 OTLP 完整集成指南 (2025版)

> **最新更新**: 2025年10月  
> **Go版本**: 1.25.1  
> **Go-Zero版本**: v1.6.0+  
> **OpenTelemetry SDK**: v1.31.0+

## 📋 目录

- [Go-Zero 与 OTLP 完整集成指南 (2025版)](#go-zero-与-otlp-完整集成指南-2025版)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [Go-Zero 简介](#go-zero-简介)
    - [为什么需要 OTLP 集成？](#为什么需要-otlp-集成)
    - [架构图](#架构图)
  - [Go-Zero 架构概览](#go-zero-架构概览)
    - [核心组件](#核心组件)
  - [快速开始](#快速开始)
    - [1. 安装依赖](#1-安装依赖)
    - [2. 初始化 OTLP Provider](#2-初始化-otlp-provider)
  - [完整集成方案](#完整集成方案)
    - [API Gateway 集成 (HTTP)](#api-gateway-集成-http)
      - [1. API 定义文件 (order.api)](#1-api-定义文件-orderapi)
      - [2. 配置文件 (order-api.yaml)](#2-配置文件-order-apiyaml)
      - [3. 服务启动与 OTLP 初始化](#3-服务启动与-otlp-初始化)
      - [4. Handler 实现](#4-handler-实现)
      - [5. Logic 层实现](#5-logic-层实现)
  - [RPC 服务集成](#rpc-服务集成)
    - [1. Proto 定义 (order.proto)](#1-proto-定义-orderproto)
    - [2. RPC 服务配置 (order.yaml)](#2-rpc-服务配置-orderyaml)
    - [3. RPC Server 启动](#3-rpc-server-启动)
    - [4. RPC Server Logic](#4-rpc-server-logic)
    - [5. RPC Client 配置（在 API Gateway 中）](#5-rpc-client-配置在-api-gateway-中)
  - [服务间追踪](#服务间追踪)
    - [跨服务链路传播示例](#跨服务链路传播示例)
    - [Trace Context 传播](#trace-context-传播)
  - [错误处理与追踪](#错误处理与追踪)
    - [统一错误处理中间件](#统一错误处理中间件)
    - [业务错误记录](#业务错误记录)
  - [性能优化](#性能优化)
    - [1. 采样策略](#1-采样策略)
    - [2. 批量导出优化](#2-批量导出优化)
    - [3. Resource 缓存](#3-resource-缓存)
    - [4. 性能基准测试](#4-性能基准测试)
  - [生产部署](#生产部署)
    - [1. Docker Compose 完整示例](#1-docker-compose-完整示例)
    - [2. Kubernetes Deployment](#2-kubernetes-deployment)
      - [Order RPC Deployment](#order-rpc-deployment)
      - [Order API Deployment](#order-api-deployment)
    - [3. HPA 自动扩缩容](#3-hpa-自动扩缩容)
  - [最佳实践](#最佳实践)
    - [1. Span 命名规范](#1-span-命名规范)
    - [2. 属性添加最佳实践](#2-属性添加最佳实践)
    - [3. 错误处理](#3-错误处理)
    - [4. Context 传递](#4-context-传递)
    - [5. 资源清理](#5-资源清理)
    - [6. 避免过度追踪](#6-避免过度追踪)
  - [总结](#总结)
    - [Go-Zero + OTLP 集成优势](#go-zero--otlp-集成优势)
    - [关键配置项](#关键配置项)
    - [性能指标（参考）](#性能指标参考)
  - [参考资源](#参考资源)

---

## 概述

### Go-Zero 简介

**Go-Zero** 是国内开源的高性能微服务框架，由好未来（原 TAL）开源，特点包括：

- **高性能**: 支持高并发，性能优异
- **内置工具链**: goctl 代码生成，自动生成 API/RPC 代码
- **服务发现**: 内置 etcd/consul/k8s 服务注册发现
- **熔断降级**: 内置自适应熔断器
- **负载均衡**: P2C 负载均衡算法
- **可观测性**: 内置 Prometheus、Jaeger 支持

### 为什么需要 OTLP 集成？

1. **统一可观测性标准**: OpenTelemetry 是云原生可观测性的标准
2. **多后端支持**: 通过 OTLP 可以将数据发送到 Jaeger、Tempo、Zipkin 等多个后端
3. **链路完整性**: 在微服务架构中实现完整的分布式追踪
4. **性能监控**: 集成指标和日志，实现全栈可观测性

### 架构图

```text
┌─────────────────────────────────────────────────────────────┐
│                     API Gateway (HTTP)                      │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  rest.Server with OTLP Interceptor                   │   │
│  │  • Trace Context Propagation                         │   │
│  │  • Request/Response Logging                          │   │
│  │  • Metrics Collection                                │   │
│  └──────────────────────────────────────────────────────┘   │
└────────────────────┬────────────────────────────────────────┘
                     │ gRPC calls
          ┌──────────┴──────────┐
          │                     │
┌─────────▼─────────┐  ┌────────▼──────────┐
│  Order Service    │  │  User Service     │
│  (gRPC Server)    │  │  (gRPC Server)    │
│                   │  │                   │
│  • OTLP Tracing   │  │  • OTLP Tracing   │
│  • Service Mesh   │  │  • Service Mesh   │
│  • DB Tracing     │  │  • Redis Tracing  │
└─────────┬─────────┘  └────────┬──────────┘
          │                     │
          └──────────┬──────────┘
                     │
            ┌────────▼─────────┐
            │  OTel Collector  │
            │  • Trace Export  │
            │  • Metrics Export│
            │  • Log Export    │
            └──────────────────┘
```

---

## Go-Zero 架构概览

### 核心组件

```go
// 1. REST Server (API Gateway)
type RestConf struct {
    rest.RestConf
    OpenTelemetry struct {
        Endpoint string
        Sampler  float64
    }
}

// 2. RPC Server (微服务)
type RpcServerConf struct {
    zrpc.RpcServerConf
    OpenTelemetry struct {
        Endpoint string
        Sampler  float64
    }
}

// 3. RPC Client
type RpcClientConf struct {
    zrpc.RpcClientConf
}
```

---

## 快速开始

### 1. 安装依赖

```bash
# 安装 go-zero
go get -u github.com/zeromicro/go-zero@latest

# 安装 goctl 代码生成工具
go install github.com/zeromicro/go-zero/tools/goctl@latest

# 安装 OpenTelemetry SDK
go get go.opentelemetry.io/otel
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc
go get go.opentelemetry.io/otel/sdk
go get go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc
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

// InitProvider 初始化 OTLP Trace Provider
func InitProvider(ctx context.Context, serviceName, endpoint string, samplerRatio float64) (func(), error) {
    // 创建 OTLP gRPC exporter
    conn, err := grpc.NewClient(endpoint,
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
            semconv.ServiceNameKey.String(serviceName),
            semconv.ServiceVersionKey.String("1.0.0"),
        ),
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
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(samplerRatio)),
    )

    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        _ = tp.Shutdown(ctx)
    }, nil
}
```

---

## 完整集成方案

### API Gateway 集成 (HTTP)

#### 1. API 定义文件 (order.api)

```protobuf
syntax = "v1"

info (
    title: "订单服务 API"
    desc: "订单管理接口"
    version: "v1.0"
)

type (
    CreateOrderReq {
        UserId    int64   `json:"user_id"`
        ProductId int64   `json:"product_id"`
        Amount    float64 `json:"amount"`
    }

    CreateOrderResp {
        OrderId   int64  `json:"order_id"`
        Status    string `json:"status"`
        CreatedAt int64  `json:"created_at"`
    }

    GetOrderReq {
        OrderId int64 `path:"order_id"`
    }

    GetOrderResp {
        OrderId   int64   `json:"order_id"`
        UserId    int64   `json:"user_id"`
        ProductId int64   `json:"product_id"`
        Amount    float64 `json:"amount"`
        Status    string  `json:"status"`
        CreatedAt int64   `json:"created_at"`
    }
)

@server (
    prefix: /api/v1
    group:  order
)
service order-api {
    @handler CreateOrder
    post /orders (CreateOrderReq) returns (CreateOrderResp)

    @handler GetOrder
    get /orders/:order_id (GetOrderReq) returns (GetOrderResp)
}
```

#### 2. 配置文件 (order-api.yaml)

```yaml
Name: order-api
Host: 0.0.0.0
Port: 8888

# OpenTelemetry 配置
OpenTelemetry:
  Endpoint: localhost:4317
  Sampler: 1.0  # 采样率 100%

# RPC 客户端配置
OrderRpc:
  Etcd:
    Hosts:
      - localhost:2379
    Key: order.rpc
  Timeout: 5000
```

#### 3. 服务启动与 OTLP 初始化

```go
package main

import (
    "context"
    "flag"
    "fmt"

    "github.com/zeromicro/go-zero/core/conf"
    "github.com/zeromicro/go-zero/rest"
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

    "your-project/api/internal/config"
    "your-project/api/internal/handler"
    "your-project/api/internal/svc"
    "your-project/pkg/telemetry"
)

var configFile = flag.String("f", "etc/order-api.yaml", "the config file")

func main() {
    flag.Parse()

    var c config.Config
    conf.MustLoad(*configFile, &c)

    // 初始化 OTLP
    ctx := context.Background()
    shutdown, err := telemetry.InitProvider(ctx, c.Name, c.OpenTelemetry.Endpoint, c.OpenTelemetry.Sampler)
    if err != nil {
        panic(err)
    }
    defer shutdown()

    server := rest.MustNewServer(c.RestConf,
        rest.WithCustomCors(nil, nil, "*"),
        // 添加 OTLP HTTP 中间件
        rest.WithChain(func(next http.HandlerFunc) http.HandlerFunc {
            return otelhttp.NewHandler(next, "order-api").ServeHTTP
        }),
    )
    defer server.Stop()

    ctx := svc.NewServiceContext(c)
    handler.RegisterHandlers(server, ctx)

    fmt.Printf("Starting REST server at %s:%d...\n", c.Host, c.Port)
    server.Start()
}
```

#### 4. Handler 实现

```go
package order

import (
    "net/http"

    "github.com/zeromicro/go-zero/rest/httpx"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-project/api/internal/logic/order"
    "your-project/api/internal/svc"
    "your-project/api/internal/types"
)

var tracer = otel.Tracer("order-api-handler")

func CreateOrderHandler(svcCtx *svc.ServiceContext) http.HandlerFunc {
    return func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        
        // 创建 Span
        ctx, span := tracer.Start(ctx, "CreateOrderHandler")
        defer span.End()

        var req types.CreateOrderReq
        if err := httpx.Parse(r, &req); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "Invalid request")
            httpx.ErrorCtx(ctx, w, err)
            return
        }

        // 添加请求属性
        span.SetAttributes(
            attribute.Int64("order.user_id", req.UserId),
            attribute.Int64("order.product_id", req.ProductId),
            attribute.Float64("order.amount", req.Amount),
        )

        l := order.NewCreateOrderLogic(ctx, svcCtx)
        resp, err := l.CreateOrder(&req)
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            httpx.ErrorCtx(ctx, w, err)
        } else {
            span.SetAttributes(attribute.Int64("order.order_id", resp.OrderId))
            span.SetStatus(codes.Ok, "Success")
            httpx.OkJsonCtx(ctx, w, resp)
        }
    }
}

func GetOrderHandler(svcCtx *svc.ServiceContext) http.HandlerFunc {
    return func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        
        ctx, span := tracer.Start(ctx, "GetOrderHandler")
        defer span.End()

        var req types.GetOrderReq
        if err := httpx.Parse(r, &req); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "Invalid request")
            httpx.ErrorCtx(ctx, w, err)
            return
        }

        span.SetAttributes(attribute.Int64("order.order_id", req.OrderId))

        l := order.NewGetOrderLogic(ctx, svcCtx)
        resp, err := l.GetOrder(&req)
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            httpx.ErrorCtx(ctx, w, err)
        } else {
            span.SetStatus(codes.Ok, "Success")
            httpx.OkJsonCtx(ctx, w, resp)
        }
    }
}
```

#### 5. Logic 层实现

```go
package order

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-project/api/internal/svc"
    "your-project/api/internal/types"
    "your-project/rpc/order/orderclient"
)

var tracer = otel.Tracer("order-api-logic")

type CreateOrderLogic struct {
    ctx    context.Context
    svcCtx *svc.ServiceContext
}

func NewCreateOrderLogic(ctx context.Context, svcCtx *svc.ServiceContext) *CreateOrderLogic {
    return &CreateOrderLogic{
        ctx:    ctx,
        svcCtx: svcCtx,
    }
}

func (l *CreateOrderLogic) CreateOrder(req *types.CreateOrderReq) (*types.CreateOrderResp, error) {
    ctx, span := tracer.Start(l.ctx, "CreateOrderLogic")
    defer span.End()

    // 调用 RPC 服务
    rpcReq := &orderclient.CreateOrderRequest{
        UserId:    req.UserId,
        ProductId: req.ProductId,
        Amount:    req.Amount,
    }

    span.SetAttributes(
        attribute.Int64("rpc.user_id", req.UserId),
        attribute.Int64("rpc.product_id", req.ProductId),
    )

    rpcResp, err := l.svcCtx.OrderRpc.CreateOrder(ctx, rpcReq)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "RPC call failed")
        return nil, err
    }

    span.SetAttributes(attribute.Int64("rpc.order_id", rpcResp.OrderId))
    span.SetStatus(codes.Ok, "Success")

    return &types.CreateOrderResp{
        OrderId:   rpcResp.OrderId,
        Status:    rpcResp.Status,
        CreatedAt: time.Now().Unix(),
    }, nil
}
```

---

## RPC 服务集成

### 1. Proto 定义 (order.proto)

```protobuf
syntax = "proto3";

package order;

option go_package = "./order";

service Order {
  rpc CreateOrder(CreateOrderRequest) returns (CreateOrderResponse);
  rpc GetOrder(GetOrderRequest) returns (GetOrderResponse);
}

message CreateOrderRequest {
  int64 user_id = 1;
  int64 product_id = 2;
  double amount = 3;
}

message CreateOrderResponse {
  int64 order_id = 1;
  string status = 2;
  int64 created_at = 3;
}

message GetOrderRequest {
  int64 order_id = 1;
}

message GetOrderResponse {
  int64 order_id = 1;
  int64 user_id = 2;
  int64 product_id = 3;
  double amount = 4;
  string status = 5;
  int64 created_at = 6;
}
```

### 2. RPC 服务配置 (order.yaml)

```yaml
Name: order.rpc
ListenOn: 0.0.0.0:8080

Etcd:
  Hosts:
    - localhost:2379
  Key: order.rpc

# OpenTelemetry 配置
OpenTelemetry:
  Endpoint: localhost:4317
  Sampler: 1.0

# MySQL 配置
Mysql:
  DataSource: root:password@tcp(localhost:3306)/order_db?charset=utf8mb4&parseTime=true

# Redis 配置
Redis:
  Host: localhost:6379
  Type: node
```

### 3. RPC Server 启动

```go
package main

import (
    "context"
    "flag"
    "fmt"

    "github.com/zeromicro/go-zero/core/conf"
    "github.com/zeromicro/go-zero/core/service"
    "github.com/zeromicro/go-zero/zrpc"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"

    "your-project/rpc/internal/config"
    "your-project/rpc/internal/server"
    "your-project/rpc/internal/svc"
    "your-project/rpc/order"
    "your-project/pkg/telemetry"
)

var configFile = flag.String("f", "etc/order.yaml", "the config file")

func main() {
    flag.Parse()

    var c config.Config
    conf.MustLoad(*configFile, &c)

    // 初始化 OTLP
    ctx := context.Background()
    shutdown, err := telemetry.InitProvider(ctx, c.Name, c.OpenTelemetry.Endpoint, c.OpenTelemetry.Sampler)
    if err != nil {
        panic(err)
    }
    defer shutdown()

    ctx := svc.NewServiceContext(c)

    s := zrpc.MustNewServer(c.RpcServerConf, func(grpcServer *grpc.Server) {
        order.RegisterOrderServer(grpcServer, server.NewOrderServer(ctx))
    })

    // 添加 OTLP gRPC 拦截器
    s.AddUnaryInterceptors(
        otelgrpc.UnaryServerInterceptor(),
    )
    s.AddStreamInterceptors(
        otelgrpc.StreamServerInterceptor(),
    )

    defer s.Stop()

    fmt.Printf("Starting RPC server at %s...\n", c.ListenOn)
    s.Start()
}
```

### 4. RPC Server Logic

```go
package logic

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "your-project/rpc/internal/svc"
    "your-project/rpc/order"
)

var tracer = otel.Tracer("order-rpc-logic")

type CreateOrderLogic struct {
    ctx    context.Context
    svcCtx *svc.ServiceContext
}

func NewCreateOrderLogic(ctx context.Context, svcCtx *svc.ServiceContext) *CreateOrderLogic {
    return &CreateOrderLogic{
        ctx:    ctx,
        svcCtx: svcCtx,
    }
}

func (l *CreateOrderLogic) CreateOrder(in *order.CreateOrderRequest) (*order.CreateOrderResponse, error) {
    ctx, span := tracer.Start(l.ctx, "CreateOrderLogic")
    defer span.End()

    span.SetAttributes(
        attribute.Int64("order.user_id", in.UserId),
        attribute.Int64("order.product_id", in.ProductId),
        attribute.Float64("order.amount", in.Amount),
    )

    // 1. 验证用户
    _, userSpan := tracer.Start(ctx, "ValidateUser")
    // ... 用户验证逻辑
    userSpan.End()

    // 2. 验证产品
    _, productSpan := tracer.Start(ctx, "ValidateProduct")
    // ... 产品验证逻辑
    productSpan.End()

    // 3. 创建订单（数据库操作）
    _, dbSpan := tracer.Start(ctx, "InsertOrder")
    dbSpan.SetAttributes(
        attribute.String("db.system", "mysql"),
        attribute.String("db.operation", "INSERT"),
        attribute.String("db.table", "orders"),
    )

    orderID := time.Now().Unix() // 简化示例
    // ... 实际数据库插入逻辑

    dbSpan.SetAttributes(attribute.Int64("order.order_id", orderID))
    dbSpan.End()

    // 4. 更新缓存
    _, cacheSpan := tracer.Start(ctx, "UpdateCache")
    cacheSpan.SetAttributes(
        attribute.String("cache.system", "redis"),
        attribute.String("cache.operation", "SET"),
    )
    // ... Redis 缓存更新
    cacheSpan.End()

    span.SetAttributes(attribute.Int64("result.order_id", orderID))
    span.SetStatus(codes.Ok, "Order created successfully")

    return &order.CreateOrderResponse{
        OrderId:   orderID,
        Status:    "created",
        CreatedAt: time.Now().Unix(),
    }, nil
}
```

### 5. RPC Client 配置（在 API Gateway 中）

```go
package svc

import (
    "github.com/zeromicro/go-zero/zrpc"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"

    "your-project/api/internal/config"
    "your-project/rpc/orderclient"
)

type ServiceContext struct {
    Config   config.Config
    OrderRpc orderclient.Order
}

func NewServiceContext(c config.Config) *ServiceContext {
    // 创建 RPC 客户端，添加 OTLP 拦截器
    orderRpc := zrpc.MustNewClient(c.OrderRpc,
        zrpc.WithUnaryClientInterceptor(otelgrpc.UnaryClientInterceptor()),
        zrpc.WithStreamClientInterceptor(otelgrpc.StreamClientInterceptor()),
    )

    return &ServiceContext{
        Config:   c,
        OrderRpc: orderclient.NewOrder(orderRpc),
    }
}
```

---

## 服务间追踪

### 跨服务链路传播示例

```text
API Gateway (HTTP)
    └─> CreateOrderHandler
        └─> CreateOrderLogic
            └─> [gRPC] OrderRpc.CreateOrder
                └─> Order RPC Service
                    └─> CreateOrderLogic
                        ├─> ValidateUser
                        ├─> ValidateProduct
                        ├─> InsertOrder (MySQL)
                        └─> UpdateCache (Redis)
```

### Trace Context 传播

Go-Zero 与 OpenTelemetry 的集成会自动处理 Trace Context 的传播：

1. **HTTP → gRPC**: 通过 `otelhttp` 中间件提取 HTTP 头中的 Trace Context，并通过 `otelgrpc` 拦截器注入到 gRPC metadata 中
2. **gRPC → gRPC**: gRPC 拦截器自动在服务间传播 Trace Context
3. **自定义传播**: 可以使用 `propagation.TraceContext{}` 手动处理

---

## 错误处理与追踪

### 统一错误处理中间件

```go
package middleware

import (
    "net/http"

    "github.com/zeromicro/go-zero/rest/httpx"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

func ErrorHandlerMiddleware(next http.HandlerFunc) http.HandlerFunc {
    return func(w http.ResponseWriter, r *http.Request) {
        defer func() {
            if err := recover(); err != nil {
                span := trace.SpanFromContext(r.Context())
                span.RecordError(err.(error))
                span.SetStatus(codes.Error, "Panic recovered")

                httpx.ErrorCtx(r.Context(), w, &httpx.CodeError{
                    Code: http.StatusInternalServerError,
                    Msg:  "Internal server error",
                })
            }
        }()

        next(w, r)
    }
}
```

### 业务错误记录

```go
func (l *CreateOrderLogic) CreateOrder(req *types.CreateOrderReq) (*types.CreateOrderResp, error) {
    ctx, span := tracer.Start(l.ctx, "CreateOrderLogic")
    defer span.End()

    // 验证库存
    if req.Amount <= 0 {
        err := errors.New("invalid amount")
        span.RecordError(err)
        span.SetStatus(codes.Error, "Invalid amount")
        span.SetAttributes(attribute.String("error.type", "validation"))
        return nil, err
    }

    // RPC 调用
    rpcResp, err := l.svcCtx.OrderRpc.CreateOrder(ctx, rpcReq)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "RPC call failed")
        span.SetAttributes(
            attribute.String("error.type", "rpc"),
            attribute.String("rpc.service", "order.rpc"),
        )
        return nil, err
    }

    span.SetStatus(codes.Ok, "Success")
    return resp, nil
}
```

---

## 性能优化

### 1. 采样策略

```go
// 动态采样器
type DynamicSampler struct {
    highPriority  sdktrace.Sampler
    normalTraffic sdktrace.Sampler
}

func (s *DynamicSampler) ShouldSample(parameters sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 高优先级请求 100% 采样
    if isHighPriority(parameters.Attributes) {
        return s.highPriority.ShouldSample(parameters)
    }
    // 普通流量 10% 采样
    return s.normalTraffic.ShouldSample(parameters)
}

func (s *DynamicSampler) Description() string {
    return "DynamicSampler"
}

// 使用动态采样器
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(&DynamicSampler{
        highPriority:  sdktrace.AlwaysSample(),
        normalTraffic: sdktrace.TraceIDRatioBased(0.1),
    }),
    // ... 其他配置
)
```

### 2. 批量导出优化

```go
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        // 批次超时
        sdktrace.WithBatchTimeout(5*time.Second),
        // 最大批次大小
        sdktrace.WithMaxExportBatchSize(512),
        // 最大队列大小
        sdktrace.WithMaxQueueSize(2048),
        // 并发导出数
        sdktrace.WithExportTimeout(30*time.Second),
    ),
    // ...
)
```

### 3. Resource 缓存

```go
var (
    resourceOnce sync.Once
    resource     *resource.Resource
)

func GetResource(ctx context.Context) *resource.Resource {
    resourceOnce.Do(func() {
        var err error
        resource, err = resource.New(ctx,
            resource.WithAttributes(
                semconv.ServiceNameKey.String("order-service"),
                semconv.ServiceVersionKey.String("1.0.0"),
                semconv.DeploymentEnvironmentKey.String("production"),
            ),
            resource.WithHost(),
            resource.WithOS(),
            resource.WithProcess(),
        )
        if err != nil {
            panic(err)
        }
    })
    return resource
}
```

### 4. 性能基准测试

```go
func BenchmarkCreateOrderWithTracing(b *testing.B) {
    // 初始化 OTLP
    ctx := context.Background()
    shutdown, _ := telemetry.InitProvider(ctx, "benchmark", "localhost:4317", 0.01)
    defer shutdown()

    tracer := otel.Tracer("benchmark")

    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        ctx, span := tracer.Start(ctx, "CreateOrder")
        // ... 业务逻辑
        span.End()
    }
}

// 结果示例：
// BenchmarkCreateOrderWithTracing-8   50000   25000 ns/op   3200 B/op   45 allocs/op
```

---

## 生产部署

### 1. Docker Compose 完整示例

```yaml
version: '3.8'

services:
  # OpenTelemetry Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:0.112.0
    command: ["--config=/etc/otel-collector-config.yaml"]
    volumes:
      - ./otel-collector-config.yaml:/etc/otel-collector-config.yaml
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
    networks:
      - microservices

  # Jaeger (可选)
  jaeger:
    image: jaegertracing/all-in-one:1.62
    ports:
      - "16686:16686"  # Jaeger UI
      - "14250:14250"  # gRPC
    networks:
      - microservices

  # etcd (服务发现)
  etcd:
    image: bitnami/etcd:3.5
    environment:
      - ALLOW_NONE_AUTHENTICATION=yes
    ports:
      - "2379:2379"
    networks:
      - microservices

  # MySQL
  mysql:
    image: mysql:8.0
    environment:
      MYSQL_ROOT_PASSWORD: password
      MYSQL_DATABASE: order_db
    ports:
      - "3306:3306"
    networks:
      - microservices

  # Redis
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    networks:
      - microservices

  # Order RPC Service
  order-rpc:
    build:
      context: .
      dockerfile: Dockerfile.rpc
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
    depends_on:
      - otel-collector
      - etcd
      - mysql
      - redis
    ports:
      - "8080:8080"
    networks:
      - microservices

  # Order API Gateway
  order-api:
    build:
      context: .
      dockerfile: Dockerfile.api
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
    depends_on:
      - otel-collector
      - etcd
      - order-rpc
    ports:
      - "8888:8888"
    networks:
      - microservices

networks:
  microservices:
    driver: bridge
```

### 2. Kubernetes Deployment

#### Order RPC Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-rpc
  namespace: microservices
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-rpc
  template:
    metadata:
      labels:
        app: order-rpc
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
    spec:
      containers:
      - name: order-rpc
        image: your-registry/order-rpc:latest
        ports:
        - containerPort: 8080
          name: grpc
        - containerPort: 9090
          name: metrics
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "otel-collector.observability:4317"
        - name: OTEL_SERVICE_NAME
          value: "order-rpc"
        - name: OTEL_RESOURCE_ATTRIBUTES
          value: "service.namespace=microservices,deployment.environment=production"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          grpc:
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          grpc:
            port: 8080
          initialDelaySeconds: 10
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: order-rpc
  namespace: microservices
spec:
  selector:
    app: order-rpc
  ports:
  - name: grpc
    port: 8080
    targetPort: 8080
  - name: metrics
    port: 9090
    targetPort: 9090
```

#### Order API Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: order-api
  namespace: microservices
spec:
  replicas: 3
  selector:
    matchLabels:
      app: order-api
  template:
    metadata:
      labels:
        app: order-api
    spec:
      containers:
      - name: order-api
        image: your-registry/order-api:latest
        ports:
        - containerPort: 8888
          name: http
        env:
        - name: OTEL_EXPORTER_OTLP_ENDPOINT
          value: "otel-collector.observability:4317"
        - name: OTEL_SERVICE_NAME
          value: "order-api"
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8888
          initialDelaySeconds: 30
        readinessProbe:
          httpGet:
            path: /ready
            port: 8888
          initialDelaySeconds: 10
---
apiVersion: v1
kind: Service
metadata:
  name: order-api
  namespace: microservices
spec:
  type: LoadBalancer
  selector:
    app: order-api
  ports:
  - port: 80
    targetPort: 8888
```

### 3. HPA 自动扩缩容

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: order-rpc-hpa
  namespace: microservices
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: order-rpc
  minReplicas: 3
  maxReplicas: 10
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
        value: 4
        periodSeconds: 30
      selectPolicy: Max
```

---

## 最佳实践

### 1. Span 命名规范

```go
// ✅ 好的命名
tracer.Start(ctx, "CreateOrder")
tracer.Start(ctx, "MySQL.InsertOrder")
tracer.Start(ctx, "Redis.GetUser")
tracer.Start(ctx, "HTTP.GET /api/v1/orders")

// ❌ 避免的命名
tracer.Start(ctx, "function1")
tracer.Start(ctx, "do_something")
tracer.Start(ctx, "query")
```

### 2. 属性添加最佳实践

```go
// ✅ 使用语义化属性
span.SetAttributes(
    semconv.HTTPMethodKey.String("POST"),
    semconv.HTTPRouteKey.String("/api/v1/orders"),
    semconv.HTTPStatusCodeKey.Int(200),
    attribute.Int64("order.id", orderID),
    attribute.String("order.status", "created"),
)

// ✅ 分组相关属性
span.SetAttributes(
    attribute.String("db.system", "mysql"),
    attribute.String("db.name", "order_db"),
    attribute.String("db.operation", "INSERT"),
    attribute.String("db.table", "orders"),
)
```

### 3. 错误处理

```go
// ✅ 完整的错误记录
if err != nil {
    span.RecordError(err,
        trace.WithAttributes(
            attribute.String("error.type", "database"),
            attribute.String("error.severity", "high"),
        ),
    )
    span.SetStatus(codes.Error, err.Error())
    return nil, err
}
```

### 4. Context 传递

```go
// ✅ 始终传递 context
func (l *Logic) ProcessOrder(ctx context.Context, orderID int64) error {
    ctx, span := tracer.Start(ctx, "ProcessOrder")
    defer span.End()

    // 传递 ctx 到下层调用
    if err := l.validateOrder(ctx, orderID); err != nil {
        return err
    }
    return l.saveOrder(ctx, orderID)
}

// ❌ 避免创建新的 context.Background()
func (l *Logic) ProcessOrder(ctx context.Context, orderID int64) error {
    // 错误：丢失了追踪上下文
    newCtx := context.Background()
    return l.saveOrder(newCtx, orderID)
}
```

### 5. 资源清理

```go
func main() {
    // 初始化 OTLP
    shutdown, err := telemetry.InitProvider(ctx, "order-api", "localhost:4317", 1.0)
    if err != nil {
        panic(err)
    }
    
    // ✅ 确保资源被正确清理
    defer shutdown()

    // 或使用 signal 处理
    sigCh := make(chan os.Signal, 1)
    signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)
    
    go func() {
        <-sigCh
        shutdown()
        os.Exit(0)
    }()

    // 启动服务...
}
```

### 6. 避免过度追踪

```go
// ✅ 追踪关键操作
func (l *Logic) CreateOrder(ctx context.Context, req *Request) error {
    ctx, span := tracer.Start(ctx, "CreateOrder")
    defer span.End()

    // 追踪数据库操作
    _, dbSpan := tracer.Start(ctx, "InsertOrder")
    // ...
    dbSpan.End()

    // ❌ 不要追踪每一个微小操作
    // _, span := tracer.Start(ctx, "ValidateField1")
    // _, span := tracer.Start(ctx, "ValidateField2")
    // 应该合并为一个 "ValidateRequest" span
}
```

---

## 总结

### Go-Zero + OTLP 集成优势

1. **开箱即用**: Go-Zero 内置可观测性支持，集成简单
2. **高性能**: 支持高并发场景，追踪开销小
3. **完整链路**: HTTP → gRPC → Database 全链路追踪
4. **生产就绪**: 提供完整的部署方案和最佳实践
5. **工具链完善**: goctl 自动生成代码，提升开发效率

### 关键配置项

| 配置项 | 推荐值 | 说明 |
|--------|--------|------|
| 采样率（生产） | 0.1 - 0.3 | 10%-30% 采样 |
| 批次大小 | 512 | 平衡延迟和吞吐 |
| 批次超时 | 5s | 及时导出 |
| 队列大小 | 2048 | 防止丢失 |

### 性能指标（参考）

- **API Gateway**: 50K+ req/s，P99 延迟 < 50ms
- **RPC Service**: 100K+ req/s，P99 延迟 < 10ms
- **Tracing 开销**: < 5% CPU，< 2% 延迟增加

---

## 参考资源

- [Go-Zero 官方文档](https://go-zero.dev/)
- [Go-Zero GitHub](https://github.com/zeromicro/go-zero)
- [OpenTelemetry Go SDK](https://github.com/open-telemetry/opentelemetry-go)
- [OTLP Specification](https://opentelemetry.io/docs/specs/otlp/)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-12  
**维护者**: OpenTelemetry Go Integration Team

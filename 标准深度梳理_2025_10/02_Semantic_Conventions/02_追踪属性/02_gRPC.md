# gRPC语义约定详解

> **Semantic Conventions版本**: v1.27.0  
> **稳定性**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [gRPC语义约定详解](#grpc语义约定详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 gRPC特性](#11-grpc特性)
    - [1.2 适用范围](#12-适用范围)
  - [2. 通用属性](#2-通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. gRPC客户端属性](#3-grpc客户端属性)
  - [4. gRPC服务器属性](#4-grpc服务器属性)
  - [5. gRPC状态码映射](#5-grpc状态码映射)
    - [5.1 状态码定义](#51-状态码定义)
    - [5.2 Span状态映射](#52-span状态映射)
  - [6. gRPC方法命名](#6-grpc方法命名)
  - [7. gRPC元数据](#7-grpc元数据)
  - [8. 流式RPC](#8-流式rpc)
    - [8.1 Unary RPC](#81-unary-rpc)
    - [8.2 Server Streaming](#82-server-streaming)
    - [8.3 Client Streaming](#83-client-streaming)
    - [8.4 Bidirectional Streaming](#84-bidirectional-streaming)
  - [9. gRPC事件](#9-grpc事件)
  - [10. gRPC指标](#10-grpc指标)
  - [11. 实现示例](#11-实现示例)
    - [11.1 gRPC客户端 (Go)](#111-grpc客户端-go)
    - [11.2 gRPC服务器 (Go)](#112-grpc服务器-go)
  - [12. 最佳实践](#12-最佳实践)
  - [13. 参考资源](#13-参考资源)

## 1. 概述

### 1.1 gRPC特性

**gRPC核心特性**：

```text
1. 基于HTTP/2
   - 多路复用
   - 双向流
   - 头部压缩

2. Protocol Buffers
   - 强类型
   - 高效序列化
   - 跨语言

3. 四种调用模式
   - Unary (一元)
   - Server Streaming (服务器流)
   - Client Streaming (客户端流)
   - Bidirectional Streaming (双向流)

4. 内置特性
   - 负载均衡
   - 认证
   - 重试
   - 超时
```

### 1.2 适用范围

**语义约定适用于**：

```text
1. gRPC客户端
   - Span kind: CLIENT

2. gRPC服务器
   - Span kind: SERVER

3. 所有调用模式
   - Unary
   - Streaming

4. 所有传输
   - HTTP/2
   - HTTP/3 (实验性)
```

---

## 2. 通用属性

### 2.1 必需属性

**所有gRPC span必需的属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `rpc.system` | string | RPC系统标识 | `grpc` |
| `rpc.service` | string | 服务全限定名 | `myapp.UserService` |
| `rpc.method` | string | 方法名 | `GetUser` |

**rpc.system 定义**：

```text
固定值: "grpc"

用途:
- 标识RPC类型
- 区分gRPC和其他RPC (如Thrift)
- 后端统计分类
```

**rpc.service 格式**：

```text
格式: package.Service

示例:
protobuf定义:
  package myapp;
  service UserService { ... }

rpc.service: "myapp.UserService"

注意:
- 包含package前缀
- 使用点号分隔
- 区分大小写
```

**rpc.method 格式**：

```text
格式: MethodName (不含service前缀)

示例:
protobuf定义:
  rpc GetUser(GetUserRequest) returns (User) {}

rpc.method: "GetUser"

注意:
- 仅方法名
- 不包含package和service
- 区分大小写
```

### 2.2 推荐属性

**推荐的gRPC属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `rpc.grpc.status_code` | int | gRPC状态码 | `0` (OK), `5` (NOT_FOUND) |
| `server.address` | string | 服务器地址 | `api.example.com` |
| `server.port` | int | 服务器端口 | `50051` |
| `network.protocol.version` | string | HTTP版本 | `2` |

---

## 3. gRPC客户端属性

**客户端特定属性**：

```text
必需:
- rpc.system: "grpc"
- rpc.service: "package.Service"
- rpc.method: "MethodName"

推荐:
- rpc.grpc.status_code: 0-16
- server.address: "api.example.com"
- server.port: 50051
- network.protocol.name: "http"
- network.protocol.version: "2"

示例:
ctx, span := tracer.Start(ctx, "myapp.UserService/GetUser",
    trace.WithSpanKind(trace.SpanKindClient),
    trace.WithAttributes(
        semconv.RPCSystemGRPC,
        semconv.RPCService("myapp.UserService"),
        semconv.RPCMethod("GetUser"),
        semconv.ServerAddress("api.example.com"),
        semconv.ServerPort(50051),
    ),
)
```

---

## 4. gRPC服务器属性

**服务器特定属性**：

```text
必需:
- rpc.system: "grpc"
- rpc.service: "package.Service"
- rpc.method: "MethodName"

推荐:
- rpc.grpc.status_code: 0-16
- client.address: "192.168.1.100"
- client.port: 54321
- network.protocol.name: "http"
- network.protocol.version: "2"

示例:
func (s *userService) GetUser(ctx context.Context, req *pb.GetUserRequest) (*pb.User, error) {
    // ctx已包含SERVER span (通过拦截器创建)
    // 自动设置:
    // - rpc.system: "grpc"
    // - rpc.service: "myapp.UserService"
    // - rpc.method: "GetUser"
    // - span.kind: SERVER
    
    // 业务逻辑...
}
```

---

## 5. gRPC状态码映射

### 5.1 状态码定义

**gRPC状态码列表**：

| 代码 | 名称 | 含义 | HTTP等价 |
|------|------|------|---------|
| 0 | OK | 成功 | 200 |
| 1 | CANCELLED | 操作被取消 | 499 |
| 2 | UNKNOWN | 未知错误 | 500 |
| 3 | INVALID_ARGUMENT | 无效参数 | 400 |
| 4 | DEADLINE_EXCEEDED | 超时 | 504 |
| 5 | NOT_FOUND | 未找到 | 404 |
| 6 | ALREADY_EXISTS | 已存在 | 409 |
| 7 | PERMISSION_DENIED | 权限拒绝 | 403 |
| 8 | RESOURCE_EXHAUSTED | 资源耗尽 | 429 |
| 9 | FAILED_PRECONDITION | 前置条件失败 | 400 |
| 10 | ABORTED | 操作中止 | 409 |
| 11 | OUT_OF_RANGE | 超出范围 | 400 |
| 12 | UNIMPLEMENTED | 未实现 | 501 |
| 13 | INTERNAL | 内部错误 | 500 |
| 14 | UNAVAILABLE | 服务不可用 | 503 |
| 15 | DATA_LOSS | 数据丢失 | 500 |
| 16 | UNAUTHENTICATED | 未认证 | 401 |

### 5.2 Span状态映射

**gRPC状态码 → Span Status**：

```text
映射规则:

OK (0):
→ Span Status: OK

CANCELLED (1):
→ Span Status: ERROR
→ Status Message: "CANCELLED"

所有其他错误 (2-16):
→ Span Status: ERROR
→ Status Message: gRPC状态码名称

示例:
grpc_status_code: 5 (NOT_FOUND)
→ span.status.code: ERROR
→ span.status.message: "NOT_FOUND"

grpc_status_code: 0 (OK)
→ span.status.code: OK
→ span.status.message: ""
```

**映射实现**：

```go
func setSpanStatus(span trace.Span, grpcStatus codes.Code) {
    span.SetAttributes(
        semconv.RPCGRPCStatusCodeKey.Int(int(grpcStatus)),
    )
    
    if grpcStatus == codes.OK {
        span.SetStatus(codes.Ok, "")
    } else {
        span.SetStatus(codes.Error, grpcStatus.String())
    }
}
```

---

## 6. gRPC方法命名

**Span名称约定**：

```text
格式: {package}.{Service}/{Method}

示例:
protobuf:
  package myapp;
  service UserService {
    rpc GetUser(GetUserRequest) returns (User) {}
  }

Span name: "myapp.UserService/GetUser"

规则:
1. 包含完整的service路径
2. 使用斜杠分隔service和method
3. 区分大小写
4. 不包含参数类型

用途:
- 唯一标识RPC调用
- 便于搜索和过滤
- 与Protobuf定义一致
```

**命名示例**：

```text
示例1:
package: google.pubsub.v1
service: Publisher
method: Publish
→ Span name: "google.pubsub.v1.Publisher/Publish"

示例2:
package: (空)
service: Greeter
method: SayHello
→ Span name: "Greeter/SayHello"

示例3:
package: api.v2
service: OrderService
method: CreateOrder
→ Span name: "api.v2.OrderService/CreateOrder"
```

---

## 7. gRPC元数据

**Metadata属性捕获**：

```text
gRPC metadata类似HTTP headers

捕获规则:
1. 不要默认捕获所有metadata
2. 选择性捕获有用的metadata
3. 注意敏感信息

推荐捕获:
- request-id
- correlation-id
- user-agent
- timeout

禁止捕获:
- authorization
- api-key
- token

属性格式:
rpc.grpc.request.metadata.<key>: string[]
rpc.grpc.response.metadata.<key>: string[]

示例:
rpc.grpc.request.metadata.request_id: ["abc-123"]
rpc.grpc.request.metadata.user_agent: ["grpc-go/1.50.0"]
```

---

## 8. 流式RPC

### 8.1 Unary RPC

**一元RPC (请求-响应)**：

```text
定义:
客户端发送一个请求，服务器返回一个响应

Span结构:
[CLIENT span                    ]
  └─ [SERVER span            ]

特点:
- 类似HTTP请求
- Span在响应返回时结束
- 最简单的模式

示例:
rpc GetUser(GetUserRequest) returns (User) {}

追踪属性:
- rpc.system: "grpc"
- rpc.service: "myapp.UserService"
- rpc.method: "GetUser"
- rpc.grpc.status_code: 0
```

### 8.2 Server Streaming

**服务器流式RPC**：

```text
定义:
客户端发送一个请求，服务器返回消息流

Span结构:
[CLIENT span                              ]
  └─ [SERVER span                      ]
      └─ [INTERNAL span "send message 1"]
      └─ [INTERNAL span "send message 2"]
      └─ [INTERNAL span "send message 3"]

特点:
- Span在流关闭时结束
- 可选择为每个消息创建event

示例:
rpc ListUsers(ListUsersRequest) returns (stream User) {}

追踪策略:
1. 单个span (推荐):
   - 整个流用一个span
   - 记录消息数量为属性
   
2. Span + Events:
   - 一个span
   - 每个消息一个event
   
3. 多span (不推荐):
   - 一个父span
   - 每个消息一个子span
   - 可能导致span数量爆炸
```

### 8.3 Client Streaming

**客户端流式RPC**：

```text
定义:
客户端发送消息流，服务器返回一个响应

Span结构:
[CLIENT span                              ]
  └─ [INTERNAL span "send message 1"]
  └─ [INTERNAL span "send message 2"]
  └─ [INTERNAL span "send message 3"]
    └─ [SERVER span                      ]

示例:
rpc UploadFile(stream FileChunk) returns (UploadResult) {}

追踪策略:
- 单个CLIENT span
- 单个SERVER span
- 可选择记录消息数量
```

### 8.4 Bidirectional Streaming

**双向流式RPC**：

```text
定义:
客户端和服务器都发送消息流

Span结构:
[CLIENT span                                        ]
  └─ [SERVER span                                ]
      ├─ Client消息事件
      └─ Server消息事件

示例:
rpc Chat(stream ChatMessage) returns (stream ChatMessage) {}

追踪策略:
- CLIENT span: 整个客户端流
- SERVER span: 整个服务器流
- 使用events记录消息
```

**流式RPC属性**：

```text
推荐属性:
rpc.grpc.request.message_count: 发送消息数
rpc.grpc.response.message_count: 接收消息数

示例:
span.SetAttributes(
    attribute.Int64("rpc.grpc.request.message_count", 100),
    attribute.Int64("rpc.grpc.response.message_count", 50),
)
```

---

## 9. gRPC事件

**推荐的gRPC事件**：

```text
消息发送事件:
span.AddEvent("message.send",
    trace.WithAttributes(
        attribute.Int("message.id", 1),
        attribute.Int("message.type", int(MessageType_Request)),
        attribute.Int("message.compressed_size", 1024),
        attribute.Int("message.uncompressed_size", 2048),
    ),
)

消息接收事件:
span.AddEvent("message.receive",
    trace.WithAttributes(
        attribute.Int("message.id", 1),
        attribute.Int("message.type", int(MessageType_Response)),
        attribute.Int("message.compressed_size", 512),
        attribute.Int("message.uncompressed_size", 1024),
    ),
)

适用场景:
- 调试流式RPC
- 性能分析
- 消息大小监控
```

---

## 10. gRPC指标

**推荐的gRPC指标**：

```text
客户端指标:
rpc.client.duration (Histogram):
- 描述: RPC调用持续时间
- 单位: 秒 (s)
- 维度:
  * rpc.system: "grpc"
  * rpc.service
  * rpc.method
  * rpc.grpc.status_code
  * server.address

rpc.client.request.size (Histogram):
- 描述: 请求大小
- 单位: 字节 (By)

rpc.client.response.size (Histogram):
- 描述: 响应大小
- 单位: 字节 (By)

服务器指标:
rpc.server.duration (Histogram):
- 描述: RPC处理时间
- 单位: 秒 (s)
- 维度:
  * rpc.system: "grpc"
  * rpc.service
  * rpc.method
  * rpc.grpc.status_code

rpc.server.active_requests (UpDownCounter):
- 描述: 并发RPC数
- 单位: {request}

rpc.server.request.size (Histogram):
- 描述: 请求大小
- 单位: 字节 (By)

rpc.server.response.size (Histogram):
- 描述: 响应大小
- 单位: 字节 (By)
```

---

## 11. 实现示例

### 11.1 gRPC客户端 (Go)

**使用拦截器自动追踪**：

```go
package main

import (
    "context"
    
    "google.golang.org/grpc"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/otel"
)

func main() {
    // 创建gRPC连接,使用OTel拦截器
    conn, err := grpc.Dial("localhost:50051",
        grpc.WithInsecure(),
        // 自动创建CLIENT span
        grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
    )
    if err != nil {
        panic(err)
    }
    defer conn.Close()
    
    client := pb.NewUserServiceClient(conn)
    
    // 调用会自动创建span
    ctx := context.Background()
    user, err := client.GetUser(ctx, &pb.GetUserRequest{Id: 123})
    
    // Span自动包含:
    // - rpc.system: "grpc"
    // - rpc.service: "myapp.UserService"
    // - rpc.method: "GetUser"
    // - rpc.grpc.status_code: 0 (或错误码)
    // - server.address: "localhost"
    // - server.port: 50051
}
```

**手动追踪**：

```go
func CallGetUser(ctx context.Context, client pb.UserServiceClient, userID int64) (*pb.User, error) {
    // 手动创建CLIENT span
    ctx, span := otel.Tracer("my-client").Start(ctx, "myapp.UserService/GetUser",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.RPCSystemGRPC,
            semconv.RPCService("myapp.UserService"),
            semconv.RPCMethod("GetUser"),
            semconv.ServerAddress("localhost"),
            semconv.ServerPort(50051),
        ),
    )
    defer span.End()
    
    // 调用gRPC
    user, err := client.GetUser(ctx, &pb.GetUserRequest{Id: userID})
    
    if err != nil {
        // 提取gRPC状态码
        st, ok := status.FromError(err)
        if ok {
            span.SetAttributes(
                semconv.RPCGRPCStatusCodeKey.Int(int(st.Code())),
            )
            span.SetStatus(codes.Error, st.Code().String())
        } else {
            span.SetStatus(codes.Error, err.Error())
        }
        return nil, err
    }
    
    // 成功
    span.SetAttributes(
        semconv.RPCGRPCStatusCodeKey.Int(int(codes.OK)),
    )
    span.SetStatus(codes.Ok, "")
    
    return user, nil
}
```

### 11.2 gRPC服务器 (Go)

**使用拦截器自动追踪**：

```go
package main

import (
    "context"
    "net"
    
    "google.golang.org/grpc"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
)

type userServiceServer struct {
    pb.UnimplementedUserServiceServer
}

func (s *userServiceServer) GetUser(ctx context.Context, req *pb.GetUserRequest) (*pb.User, error) {
    // ctx已包含SERVER span (通过拦截器创建)
    
    // 可以获取当前span
    span := trace.SpanFromContext(ctx)
    
    // 添加自定义属性
    span.SetAttributes(
        attribute.Int64("user.id", req.Id),
    )
    
    // 业务逻辑
    user := &pb.User{
        Id:   req.Id,
        Name: "Alice",
    }
    
    return user, nil
}

func main() {
    lis, err := net.Listen("tcp", ":50051")
    if err != nil {
        panic(err)
    }
    
    // 创建gRPC服务器,使用OTel拦截器
    server := grpc.NewServer(
        // 自动创建SERVER span
        grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
        grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
    )
    
    pb.RegisterUserServiceServer(server, &userServiceServer{})
    
    server.Serve(lis)
}
```

**流式RPC追踪**：

```go
func (s *userServiceServer) ListUsers(req *pb.ListUsersRequest, stream pb.UserService_ListUsersServer) error {
    // stream.Context()包含SERVER span
    ctx := stream.Context()
    span := trace.SpanFromContext(ctx)
    
    messageCount := 0
    
    // 发送多个响应
    for _, user := range getAllUsers() {
        if err := stream.Send(&user); err != nil {
            span.RecordError(err)
            return err
        }
        
        messageCount++
        
        // 记录消息发送事件 (可选)
        span.AddEvent("message.send",
            trace.WithAttributes(
                attribute.Int("message.id", messageCount),
            ),
        )
    }
    
    // 记录总消息数
    span.SetAttributes(
        attribute.Int("rpc.grpc.response.message_count", messageCount),
    )
    
    return nil
}
```

---

## 12. 最佳实践

```text
1. Span命名
   ✅ 使用 {package}.{Service}/{Method}
   ✅ 包含完整路径
   ❌ 不要省略package

2. 状态码
   ✅ 总是设置 rpc.grpc.status_code
   ✅ 映射到Span Status
   ✅ 记录错误详情

3. 拦截器
   ✅ 使用官方otelgrpc拦截器
   ✅ 客户端和服务器都配置
   ✅ 放在拦截器链的第一个

4. 流式RPC
   ✅ 使用单个span
   ✅ 记录消息数量
   ⚠️ 谨慎使用events (高频消息)
   ❌ 不要为每个消息创建span

5. Metadata
   ✅ 选择性捕获
   ❌ 不要捕获敏感信息
   ✅ 使用allow/block list

6. 性能
   ✅ 使用拦截器减少手动代码
   ✅ 避免在热路径上创建过多span
   ✅ 采样高流量服务

7. 错误处理
   ✅ 捕获gRPC状态码
   ✅ 记录错误详情
   ✅ 区分客户端和服务器错误

8. 指标
   ✅ 记录rpc.server.duration
   ✅ 按service和method分组
   ✅ 监控错误率和延迟
```

---

## 13. 参考资源

- **Semantic Conventions (RPC)**: <https://opentelemetry.io/docs/specs/semconv/rpc/rpc-spans/>
- **gRPC Instrumentation**: <https://github.com/open-telemetry/opentelemetry-go-contrib/tree/main/instrumentation/google.golang.org/grpc>
- **gRPC Status Codes**: <https://grpc.github.io/grpc/core/md_doc_statuscodes.html>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**下一步**: [04_消息队列.md](./04_消息队列.md)

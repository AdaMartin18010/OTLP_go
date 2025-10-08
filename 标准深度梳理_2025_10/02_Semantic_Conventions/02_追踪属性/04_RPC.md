# RPC 语义约定

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [RPC 语义约定](#rpc-语义约定)
  - [目录](#目录)
  - [1. RPC概述](#1-rpc概述)
    - [1.1 什么是RPC](#11-什么是rpc)
    - [1.2 RPC系统分类](#12-rpc系统分类)
  - [2. RPC Span基本属性](#2-rpc-span基本属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
    - [2.3 可选属性](#23-可选属性)
  - [3. RPC客户端Span](#3-rpc客户端span)
    - [3.1 Span命名](#31-span命名)
    - [3.2 客户端属性](#32-客户端属性)
    - [3.3 Go示例](#33-go示例)
  - [4. RPC服务器Span](#4-rpc服务器span)
    - [4.1 Span命名](#41-span命名)
    - [4.2 服务器属性](#42-服务器属性)
    - [4.3 Go示例](#43-go示例)
  - [5. RPC Status映射](#5-rpc-status映射)
    - [5.1 Status Code映射规则](#51-status-code映射规则)
    - [5.2 错误处理](#52-错误处理)
  - [6. 特定RPC系统](#6-特定rpc系统)
    - [6.1 gRPC](#61-grpc)
    - [6.2 Apache Thrift](#62-apache-thrift)
    - [6.3 Apache Dubbo](#63-apache-dubbo)
    - [6.4 JSON-RPC](#64-json-rpc)
  - [7. Context传播](#7-context传播)
    - [7.1 传播机制](#71-传播机制)
    - [7.2 Go实现](#72-go实现)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 命名规范](#81-命名规范)
    - [8.2 属性选择](#82-属性选择)
    - [8.3 性能考虑](#83-性能考虑)
  - [9. 完整示例](#9-完整示例)
    - [9.1 Go gRPC客户端](#91-go-grpc客户端)
    - [9.2 Python gRPC服务器](#92-python-grpc服务器)
    - [9.3 Java Dubbo示例](#93-java-dubbo示例)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [RPC系统文档](#rpc系统文档)
    - [实现参考](#实现参考)

---

## 1. RPC概述

### 1.1 什么是RPC

**RPC (Remote Procedure Call)** 是一种允许程序调用另一个地址空间（通常是远程服务器）的过程或函数的通信协议。

**核心特点**:

```text
✅ 抽象网络通信细节
✅ 像调用本地函数一样调用远程服务
✅ 支持多种传输协议（TCP/HTTP/HTTP2）
✅ 通常使用IDL定义接口
```

### 1.2 RPC系统分类

| RPC系统 | 传输协议 | 编码格式 | 特点 |
|---------|----------|----------|------|
| **gRPC** | HTTP/2 | Protocol Buffers | Google开发，高性能，流式支持 |
| **Apache Thrift** | TCP/HTTP | Binary/Compact/JSON | Facebook开发，多语言支持 |
| **Apache Dubbo** | TCP/HTTP | Hessian2/Protobuf | 阿里开发，Java生态 |
| **JSON-RPC** | HTTP | JSON | 简单轻量，广泛支持 |
| **XML-RPC** | HTTP | XML | 早期标准，逐渐淘汰 |
| **tRPC** | HTTP/2 | Protocol Buffers | 腾讯开发，企业级 |

---

## 2. RPC Span基本属性

### 2.1 必需属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `rpc.system` | string | RPC系统标识 | `grpc`, `apache_dubbo`, `dotnet_wcf` |
| `rpc.service` | string | 完整服务名 | `myservice.EchoService` |
| `rpc.method` | string | RPC方法名 | `exampleMethod` |

### 2.2 推荐属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `net.peer.name` | string | 远程主机名 | `example.com` |
| `net.peer.port` | int | 远程端口 | `8080` |
| `net.transport` | string | 网络传输协议 | `ip_tcp`, `ip_udp` |

### 2.3 可选属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `rpc.jsonrpc.version` | string | JSON-RPC版本 | `2.0` |
| `rpc.jsonrpc.request_id` | string/int | JSON-RPC请求ID | `1`, `"request-1"` |
| `rpc.jsonrpc.error_code` | int | JSON-RPC错误码 | `-32700` |
| `rpc.jsonrpc.error_message` | string | JSON-RPC错误消息 | `Parse error` |

---

## 3. RPC客户端Span

### 3.1 Span命名

**命名规则**: `{rpc.service}/{rpc.method}`

**示例**:

```text
✅ myservice.EchoService/Echo
✅ google.pubsub.v1.Publisher/CreateTopic
✅ com.example.UserService/GetUser
```

### 3.2 客户端属性

**SpanKind**: `CLIENT`

**核心属性**:

```text
✅ rpc.system (必需)
✅ rpc.service (必需)
✅ rpc.method (必需)
✅ net.peer.name (推荐)
✅ net.peer.port (推荐)
✅ net.transport (推荐)
```

### 3.3 Go示例

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

func CallRPCMethod(ctx context.Context, service, method, host string, port int) error {
    tracer := otel.Tracer("rpc-client")
    
    // 创建客户端Span
    ctx, span := tracer.Start(ctx, service+"/"+method,
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            // RPC基本属性
            attribute.String("rpc.system", "grpc"),
            attribute.String("rpc.service", service),
            attribute.String("rpc.method", method),
            
            // 网络属性
            attribute.String("net.peer.name", host),
            attribute.Int("net.peer.port", port),
            attribute.String("net.transport", "ip_tcp"),
        ),
    )
    defer span.End()
    
    // 执行RPC调用
    err := performRPCCall(ctx, service, method, host, port)
    
    if err != nil {
        span.SetStatus(codes.Error, err.Error())
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "RPC call successful")
    return nil
}

func performRPCCall(ctx context.Context, service, method, host string, port int) error {
    // 实际RPC调用逻辑
    return nil
}
```

---

## 4. RPC服务器Span

### 4.1 Span命名

**命名规则**: 与客户端相同 `{rpc.service}/{rpc.method}`

### 4.2 服务器属性

**SpanKind**: `SERVER`

**核心属性**:

```text
✅ rpc.system (必需)
✅ rpc.service (必需)
✅ rpc.method (必需)
✅ net.host.name (推荐) - 服务器主机名
✅ net.host.port (推荐) - 服务器端口
```

### 4.3 Go示例

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

type RPCServer struct {
    tracer trace.Tracer
}

func NewRPCServer() *RPCServer {
    return &RPCServer{
        tracer: otel.Tracer("rpc-server"),
    }
}

func (s *RPCServer) HandleRPCRequest(ctx context.Context, service, method string) error {
    // 创建服务器Span
    ctx, span := s.tracer.Start(ctx, service+"/"+method,
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            // RPC基本属性
            attribute.String("rpc.system", "grpc"),
            attribute.String("rpc.service", service),
            attribute.String("rpc.method", method),
            
            // 服务器网络属性
            attribute.String("net.host.name", "api.example.com"),
            attribute.Int("net.host.port", 8080),
            attribute.String("net.transport", "ip_tcp"),
        ),
    )
    defer span.End()
    
    // 处理RPC请求
    err := processRequest(ctx, service, method)
    
    if err != nil {
        span.SetStatus(codes.Error, err.Error())
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "Request processed successfully")
    return nil
}

func processRequest(ctx context.Context, service, method string) error {
    // 实际请求处理逻辑
    return nil
}
```

---

## 5. RPC Status映射

### 5.1 Status Code映射规则

**通用映射**:

| RPC Status | Span Status | 说明 |
|------------|-------------|------|
| OK | `Ok` | 成功 |
| Cancelled | `Error` | 客户端取消 |
| Unknown | `Error` | 未知错误 |
| InvalidArgument | `Error` | 无效参数 |
| DeadlineExceeded | `Error` | 超时 |
| NotFound | `Error` | 未找到 |
| AlreadyExists | `Error` | 已存在 |
| PermissionDenied | `Error` | 权限拒绝 |
| ResourceExhausted | `Error` | 资源耗尽 |
| FailedPrecondition | `Error` | 前置条件失败 |
| Aborted | `Error` | 中止 |
| OutOfRange | `Error` | 超出范围 |
| Unimplemented | `Error` | 未实现 |
| Internal | `Error` | 内部错误 |
| Unavailable | `Error` | 不可用 |
| DataLoss | `Error` | 数据丢失 |
| Unauthenticated | `Error` | 未认证 |

### 5.2 错误处理

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc/status"
    "google.golang.org/grpc/codes as grpccodes"
)

func HandleRPCError(ctx context.Context, span trace.Span, err error) {
    if err == nil {
        span.SetStatus(codes.Ok, "Success")
        return
    }
    
    // 获取gRPC status
    st, ok := status.FromError(err)
    if !ok {
        span.SetStatus(codes.Error, err.Error())
        span.RecordError(err)
        return
    }
    
    // 设置Span状态
    span.SetStatus(codes.Error, st.Message())
    span.RecordError(err)
    
    // 记录错误码
    span.SetAttributes(
        attribute.String("rpc.grpc.status_code", st.Code().String()),
    )
}
```

---

## 6. 特定RPC系统

### 6.1 gRPC

**系统标识**: `grpc`

**额外属性**:

```text
rpc.grpc.status_code: gRPC状态码 (int)
```

**示例**:

```go
span.SetAttributes(
    attribute.String("rpc.system", "grpc"),
    attribute.String("rpc.service", "myservice.Greeter"),
    attribute.String("rpc.method", "SayHello"),
    attribute.Int("rpc.grpc.status_code", 0), // OK
)
```

### 6.2 Apache Thrift

**系统标识**: `apache_thrift`

**示例**:

```python
span.set_attributes({
    "rpc.system": "apache_thrift",
    "rpc.service": "Calculator",
    "rpc.method": "add",
})
```

### 6.3 Apache Dubbo

**系统标识**: `apache_dubbo`

**额外属性**:

```text
rpc.dubbo.version: Dubbo协议版本
rpc.dubbo.group: 服务分组
rpc.dubbo.timeout: 超时时间
```

**示例**:

```java
span.setAttributes(
    AttributeKey.stringKey("rpc.system").set("apache_dubbo"),
    AttributeKey.stringKey("rpc.service").set("com.example.DemoService"),
    AttributeKey.stringKey("rpc.method").set("sayHello"),
    AttributeKey.stringKey("rpc.dubbo.version").set("1.0.0"),
    AttributeKey.stringKey("rpc.dubbo.group").set("production")
);
```

### 6.4 JSON-RPC

**系统标识**: `jsonrpc`

**额外属性**:

```text
rpc.jsonrpc.version: JSON-RPC版本 (通常为 "2.0")
rpc.jsonrpc.request_id: 请求ID
rpc.jsonrpc.error_code: 错误码（如果有错误）
rpc.jsonrpc.error_message: 错误消息
```

**示例**:

```javascript
span.setAttributes({
    "rpc.system": "jsonrpc",
    "rpc.service": "Calculator",
    "rpc.method": "subtract",
    "rpc.jsonrpc.version": "2.0",
    "rpc.jsonrpc.request_id": "1"
});
```

---

## 7. Context传播

### 7.1 传播机制

RPC调用需要传播trace context以建立分布式追踪链路。

**传播流程**:

```text
Client                          Server
  │                               │
  ├─ Start Span (CLIENT)         │
  │  └─ Inject Context           │
  │     └─ Add to RPC Metadata ─►│
  │                               ├─ Extract Context
  │                               ├─ Start Span (SERVER)
  │                               ├─ Process Request
  │                               └─ End Span
  ├─ Receive Response             │
  └─ End Span                     │
```

### 7.2 Go实现

**gRPC客户端传播**:

```go
package main

import (
    "context"
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// gRPC客户端拦截器 - 注入context
func ClientInterceptor() grpc.UnaryClientInterceptor {
    return func(
        ctx context.Context,
        method string,
        req, reply interface{},
        cc *grpc.ClientConn,
        invoker grpc.UnaryInvoker,
        opts ...grpc.CallOption,
    ) error {
        // 获取propagator
        propagator := otel.GetTextMapPropagator()
        
        // 创建metadata
        md, ok := metadata.FromOutgoingContext(ctx)
        if !ok {
            md = metadata.New(nil)
        }
        
        // 注入trace context
        propagator.Inject(ctx, &metadataCarrier{md: md})
        
        // 设置metadata到context
        ctx = metadata.NewOutgoingContext(ctx, md)
        
        // 调用RPC
        return invoker(ctx, method, req, reply, cc, opts...)
    }
}

// Metadata carrier实现
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

**gRPC服务器传播**:

```go
package main

import (
    "context"
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    "go.opentelemetry.io/otel"
)

// gRPC服务器拦截器 - 提取context
func ServerInterceptor() grpc.UnaryServerInterceptor {
    return func(
        ctx context.Context,
        req interface{},
        info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler,
    ) (interface{}, error) {
        // 获取propagator
        propagator := otel.GetTextMapPropagator()
        
        // 从metadata提取trace context
        md, ok := metadata.FromIncomingContext(ctx)
        if ok {
            ctx = propagator.Extract(ctx, &metadataCarrier{md: md})
        }
        
        // 处理请求
        return handler(ctx, req)
    }
}
```

---

## 8. 最佳实践

### 8.1 命名规范

**✅ 推荐**:

```text
myservice.Greeter/SayHello
google.pubsub.v1.Publisher/CreateTopic
com.example.UserService/GetUser
```

**❌ 不推荐**:

```text
SayHello (缺少服务名)
Greeter.SayHello (使用.而不是/)
greeter/sayhello (使用小写)
```

### 8.2 属性选择

**优先级**:

```text
P0 (必需):
  ✅ rpc.system
  ✅ rpc.service
  ✅ rpc.method

P1 (强烈推荐):
  ✅ net.peer.name / net.host.name
  ✅ net.peer.port / net.host.port
  ✅ net.transport

P2 (可选但有用):
  ✅ 系统特定属性 (如 rpc.grpc.status_code)
  ✅ 自定义业务属性
```

### 8.3 性能考虑

**性能优化建议**:

1. **使用采样**

    ```go
    // 配置采样率
    sampler := trace.TraceIDRatioBased(0.1) // 10%采样
    ```

2. **批量导出**

    ```go
    exporter := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )

    bsp := sdktrace.NewBatchSpanProcessor(exporter,
        sdktrace.WithMaxQueueSize(2048),
        sdktrace.WithBatchTimeout(5*time.Second),
    )
    ```

3. **避免记录敏感信息**

    ```go
    // ❌ 不要记录
    span.SetAttributes(
        attribute.String("request.body", requestBody), // 可能包含敏感数据
        attribute.String("auth.token", authToken),     // 敏感
    )

    // ✅ 推荐
    span.SetAttributes(
        attribute.Int("request.size", len(requestBody)),
        attribute.String("request.content_type", contentType),
    )
    ```

---

## 9. 完整示例

### 9.1 Go gRPC客户端

```go
package main

import (
    "context"
    "log"
    "time"
    
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
    "go.opentelemetry.io/otel/trace"
)

func initTracer() func() {
    ctx := context.Background()
    
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatal(err)
    }
    
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("rpc-client"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        log.Fatal(err)
    }
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )
    otel.SetTracerProvider(tp)
    
    return func() {
        ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
        defer cancel()
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }
}

type GreeterClient struct {
    conn   *grpc.ClientConn
    tracer trace.Tracer
}

func NewGreeterClient(target string) (*GreeterClient, error) {
    conn, err := grpc.Dial(target,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithUnaryInterceptor(ClientInterceptor()),
    )
    if err != nil {
        return nil, err
    }
    
    return &GreeterClient{
        conn:   conn,
        tracer: otel.Tracer("grpc-client"),
    }, nil
}

func (c *GreeterClient) SayHello(ctx context.Context, name string) error {
    // 创建Span
    ctx, span := c.tracer.Start(ctx, "myservice.Greeter/SayHello",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("rpc.system", "grpc"),
            attribute.String("rpc.service", "myservice.Greeter"),
            attribute.String("rpc.method", "SayHello"),
            attribute.String("net.peer.name", "localhost"),
            attribute.Int("net.peer.port", 50051),
            attribute.String("net.transport", "ip_tcp"),
        ),
    )
    defer span.End()
    
    // 模拟RPC调用
    time.Sleep(100 * time.Millisecond)
    
    span.SetStatus(trace.StatusCodeOk, "Success")
    return nil
}

func main() {
    shutdown := initTracer()
    defer shutdown()
    
    client, err := NewGreeterClient("localhost:50051")
    if err != nil {
        log.Fatal(err)
    }
    defer client.conn.Close()
    
    ctx := context.Background()
    if err := client.SayHello(ctx, "World"); err != nil {
        log.Fatal(err)
    }
    
    log.Println("RPC call successful")
}
```

### 9.2 Python gRPC服务器

```python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource
from opentelemetry.semconv.resource import ResourceAttributes
from opentelemetry.trace import Status, StatusCode
import grpc
from concurrent import futures

def init_tracer():
    resource = Resource.create({
        ResourceAttributes.SERVICE_NAME: "rpc-server",
        ResourceAttributes.SERVICE_VERSION: "1.0.0",
    })
    
    provider = TracerProvider(resource=resource)
    processor = BatchSpanProcessor(
        OTLPSpanExporter(endpoint="localhost:4317", insecure=True)
    )
    provider.add_span_processor(processor)
    trace.set_tracer_provider(provider)
    
    return trace.get_tracer(__name__)

class GreeterServicer:
    def __init__(self):
        self.tracer = init_tracer()
    
    def SayHello(self, request, context):
        # 创建服务器Span
        with self.tracer.start_as_current_span(
            "myservice.Greeter/SayHello",
            kind=trace.SpanKind.SERVER,
            attributes={
                "rpc.system": "grpc",
                "rpc.service": "myservice.Greeter",
                "rpc.method": "SayHello",
                "net.host.name": "localhost",
                "net.host.port": 50051,
                "net.transport": "ip_tcp",
            }
        ) as span:
            try:
                # 处理请求
                response = f"Hello, {request.name}!"
                
                span.set_status(Status(StatusCode.OK))
                return response
                
            except Exception as e:
                span.set_status(Status(StatusCode.ERROR, str(e)))
                span.record_exception(e)
                raise

def serve():
    server = grpc.server(futures.ThreadPoolExecutor(max_workers=10))
    # 注册服务
    server.add_insecure_port('[::]:50051')
    server.start()
    print("Server started on port 50051")
    server.wait_for_termination()

if __name__ == '__main__':
    serve()
```

### 9.3 Java Dubbo示例

```java
import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.api.common.AttributeKey;

public class DubboConsumerExample {
    private final Tracer tracer;
    
    public DubboConsumerExample(OpenTelemetry openTelemetry) {
        this.tracer = openTelemetry.getTracer("dubbo-consumer");
    }
    
    public String callDubboService(String serviceName, String methodName) {
        // 创建客户端Span
        Span span = tracer.spanBuilder(serviceName + "/" + methodName)
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute(AttributeKey.stringKey("rpc.system"), "apache_dubbo")
            .setAttribute(AttributeKey.stringKey("rpc.service"), serviceName)
            .setAttribute(AttributeKey.stringKey("rpc.method"), methodName)
            .setAttribute(AttributeKey.stringKey("net.peer.name"), "dubbo-provider")
            .setAttribute(AttributeKey.intKey("net.peer.port"), 20880)
            .setAttribute(AttributeKey.stringKey("rpc.dubbo.version"), "2.7.0")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 执行Dubbo调用
            String result = invokeDubboService(serviceName, methodName);
            
            span.setStatus(io.opentelemetry.api.trace.StatusCode.OK);
            return result;
            
        } catch (Exception e) {
            span.setStatus(io.opentelemetry.api.trace.StatusCode.ERROR, e.getMessage());
            span.recordException(e);
            throw e;
            
        } finally {
            span.end();
        }
    }
    
    private String invokeDubboService(String serviceName, String methodName) {
        // 实际Dubbo调用逻辑
        return "result";
    }
}
```

---

## 10. 参考资源

### 官方文档

- **OpenTelemetry RPC Conventions**: <https://opentelemetry.io/docs/specs/semconv/rpc/>
- **gRPC Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/rpc/grpc/>
- **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>

### RPC系统文档

- **gRPC**: <https://grpc.io/>
- **Apache Thrift**: <https://thrift.apache.org/>
- **Apache Dubbo**: <https://dubbo.apache.org/>
- **JSON-RPC 2.0**: <https://www.jsonrpc.org/specification>

### 实现参考

- **OpenTelemetry Go**: <https://github.com/open-telemetry/opentelemetry-go>
- **OpenTelemetry Python**: <https://github.com/open-telemetry/opentelemetry-python>
- **OpenTelemetry Java**: <https://github.com/open-telemetry/opentelemetry-java>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

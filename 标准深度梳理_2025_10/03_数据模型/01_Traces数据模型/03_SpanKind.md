# SpanKind 完整指南

## 📋 目录

- [SpanKind 完整指南](#spankind-完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [关键特性](#关键特性)
  - [SpanKind 定义](#spankind-定义)
    - [枚举值](#枚举值)
    - [OTLP Protocol Buffers](#otlp-protocol-buffers)
  - [五种 SpanKind](#五种-spankind)
    - [1. INTERNAL (内部操作)](#1-internal-内部操作)
      - [定义](#定义)
      - [使用场景](#使用场景)
      - [Go 示例](#go-示例)
      - [完整示例](#完整示例)
    - [2. SERVER (服务器端)](#2-server-服务器端)
      - [定义2](#定义2)
      - [使用场景2](#使用场景2)
      - [Go 示例2](#go-示例2)
    - [3. CLIENT (客户端)](#3-client-客户端)
      - [定义3](#定义3)
      - [使用场景3](#使用场景3)
      - [Go 示例3](#go-示例3)
    - [4. PRODUCER (消息生产者)](#4-producer-消息生产者)
      - [定义4](#定义4)
      - [使用场景4](#使用场景4)
      - [特点](#特点)
      - [Go 示例4](#go-示例4)
    - [5. CONSUMER (消息消费者)](#5-consumer-消息消费者)
      - [定义5](#定义5)
      - [使用场景5](#使用场景5)
      - [特点5](#特点5)
      - [Go 示例5](#go-示例5)
  - [使用场景51](#使用场景51)
    - [场景矩阵](#场景矩阵)
    - [追踪模式](#追踪模式)
      - [1. 同步 RPC 模式](#1-同步-rpc-模式)
      - [2. 异步消息模式](#2-异步消息模式)
      - [3. 混合模式](#3-混合模式)
  - [Go 完整实现](#go-完整实现)
    - [完整的微服务示例](#完整的微服务示例)
  - [最佳实践](#最佳实践)
    - [1. 正确选择 SpanKind](#1-正确选择-spankind)
    - [2. 消息系统使用 PRODUCER/CONSUMER](#2-消息系统使用-producerconsumer)
    - [3. 数据库操作使用 CLIENT](#3-数据库操作使用-client)
    - [4. 内部逻辑使用 INTERNAL](#4-内部逻辑使用-internal)
  - [常见问题](#常见问题)
    - [Q1: 什么时候使用 INTERNAL？](#q1-什么时候使用-internal)
    - [Q2: 数据库查询应该用什么 Kind？](#q2-数据库查询应该用什么-kind)
    - [Q3: WebSocket 应该用什么 Kind？](#q3-websocket-应该用什么-kind)
    - [Q4: PRODUCER 和 CLIENT 有什么区别？](#q4-producer-和-client-有什么区别)
    - [Q5: 可以省略 SpanKind 吗？](#q5-可以省略-spankind-吗)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Go 实现](#go-实现)
    - [相关文档](#相关文档)

---

## 概述

**SpanKind** 描述了 Span 在分布式追踪中的角色，帮助后端理解 Span 之间的关系并正确可视化追踪图。

### 关键特性

- ✅ **语义明确**: 清晰定义 Span 的角色
- ✅ **可视化友好**: 帮助后端正确渲染追踪图
- ✅ **指标聚合**: 支持按 Kind 聚合指标
- ✅ **错误分类**: 区分客户端错误和服务器错误

---

## SpanKind 定义

### 枚举值

```go
type SpanKind int

const (
    SpanKindUnspecified SpanKind = 0  // 未指定（不推荐使用）
    SpanKindInternal    SpanKind = 1  // 内部操作
    SpanKindServer      SpanKind = 2  // 服务器端 RPC
    SpanKindClient      SpanKind = 3  // 客户端 RPC
    SpanKindProducer    SpanKind = 4  // 消息生产者
    SpanKindConsumer    SpanKind = 5  // 消息消费者
)
```

### OTLP Protocol Buffers

```protobuf
enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;
  SPAN_KIND_SERVER = 2;
  SPAN_KIND_CLIENT = 3;
  SPAN_KIND_PRODUCER = 4;
  SPAN_KIND_CONSUMER = 5;
}
```

---

## 五种 SpanKind

### 1. INTERNAL (内部操作)

#### 定义

表示应用内部的操作，不涉及远程调用或消息传递。

#### 使用场景

- 函数调用
- 数据库操作（本地）
- 文件 I/O
- 数据处理逻辑

#### Go 示例

```go
import "go.opentelemetry.io/otel/trace"

// 内部操作（默认）
ctx, span := tracer.Start(ctx, "process_data",
    trace.WithSpanKind(trace.SpanKindInternal),
)
defer span.End()

// 或者省略（默认就是 INTERNAL）
ctx, span := tracer.Start(ctx, "process_data")
defer span.End()
```

#### 完整示例

```go
func processOrder(ctx context.Context, order *Order) error {
    ctx, span := tracer.Start(ctx, "process_order",
        trace.WithSpanKind(trace.SpanKindInternal),
    )
    defer span.End()

    // 验证订单
    if err := validateOrder(ctx, order); err != nil {
        span.RecordError(err)
        return err
    }

    // 计算价格
    price := calculatePrice(ctx, order)
    span.SetAttributes(attribute.Float64("order.total", price))

    return nil
}

func validateOrder(ctx context.Context, order *Order) error {
    ctx, span := tracer.Start(ctx, "validate_order")
    defer span.End()
    
    // 验证逻辑
    return nil
}
```

---

### 2. SERVER (服务器端)

#### 定义2

表示服务器端接收并处理远程请求的操作。

#### 使用场景2

- HTTP 服务器处理请求
- gRPC 服务器处理 RPC
- WebSocket 服务器接收消息
- GraphQL 服务器处理查询

#### Go 示例2

```go
// HTTP 服务器
func httpHandler(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), r.URL.Path,
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.HTTPMethodKey.String(r.Method),
        semconv.HTTPTargetKey.String(r.URL.Path),
    )

    // 处理请求
    handleRequest(ctx, w, r)
}

// gRPC 服务器
func (s *server) GetUser(ctx context.Context, req *pb.GetUserRequest) (*pb.User, error) {
    ctx, span := tracer.Start(ctx, "GetUser",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.RPCSystemKey.String("grpc"),
        semconv.RPCServiceKey.String("UserService"),
        semconv.RPCMethodKey.String("GetUser"),
    )

    // 处理 RPC
    return s.getUserFromDB(ctx, req.UserId)
}
```

---

### 3. CLIENT (客户端)

#### 定义3

表示客户端发起远程调用的操作。

#### 使用场景3

- HTTP 客户端发起请求
- gRPC 客户端调用 RPC
- 数据库客户端查询
- 外部 API 调用

#### Go 示例3

```go
// HTTP 客户端
func callExternalAPI(ctx context.Context, url string) (*Response, error) {
    ctx, span := tracer.Start(ctx, "GET "+url,
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    span.SetAttributes(
        semconv.HTTPMethodKey.String("GET"),
        semconv.HTTPURLKey.String(url),
    )

    resp, err := http.DefaultClient.Do(req)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(semconv.HTTPStatusCodeKey.Int(resp.StatusCode))
    return resp, nil
}

// gRPC 客户端
func getUserFromService(ctx context.Context, userID string) (*User, error) {
    ctx, span := tracer.Start(ctx, "UserService/GetUser",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    span.SetAttributes(
        semconv.RPCSystemKey.String("grpc"),
        semconv.RPCServiceKey.String("UserService"),
        semconv.RPCMethodKey.String("GetUser"),
    )

    user, err := userServiceClient.GetUser(ctx, &pb.GetUserRequest{
        UserId: userID,
    })
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return user, nil
}
```

---

### 4. PRODUCER (消息生产者)

#### 定义4

表示向消息系统发送消息的操作。

#### 使用场景4

- Kafka 生产消息
- RabbitMQ 发布消息
- Redis Pub/Sub 发布
- AWS SQS 发送消息

#### 特点

- **异步**: 通常不等待消费者处理
- **批量**: 可能批量发送多条消息
- **单向**: 不期望同步响应

#### Go 示例4

```go
// Kafka 生产者
func sendKafkaMessage(ctx context.Context, topic string, message []byte) error {
    ctx, span := tracer.Start(ctx, "kafka.send",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.MessagingSystemKey.String("kafka"),
        semconv.MessagingDestinationKey.String(topic),
        semconv.MessagingOperationKey.String("send"),
    )

    err := kafkaProducer.SendMessage(&sarama.ProducerMessage{
        Topic: topic,
        Value: sarama.ByteEncoder(message),
    })
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// RabbitMQ 生产者
func publishToRabbitMQ(ctx context.Context, exchange, routingKey string, body []byte) error {
    ctx, span := tracer.Start(ctx, "rabbitmq.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.MessagingSystemKey.String("rabbitmq"),
        semconv.MessagingDestinationKey.String(exchange),
        attribute.String("messaging.rabbitmq.routing_key", routingKey),
    )

    err := channel.Publish(
        exchange,
        routingKey,
        false,  // mandatory
        false,  // immediate
        amqp.Publishing{
            ContentType: "application/json",
            Body:        body,
        },
    )
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}
```

---

### 5. CONSUMER (消息消费者)

#### 定义5

表示从消息系统接收并处理消息的操作。

#### 使用场景5

- Kafka 消费消息
- RabbitMQ 订阅消息
- Redis Pub/Sub 订阅
- AWS SQS 接收消息

#### 特点5

- **异步**: 独立于生产者运行
- **长时间运行**: 通常持续监听
- **批量**: 可能批量处理多条消息

#### Go 示例5

```go
// Kafka 消费者
func consumeKafkaMessages(ctx context.Context) {
    for {
        select {
        case msg := <-kafkaConsumer.Messages():
            processKafkaMessage(ctx, msg)
        case <-ctx.Done():
            return
        }
    }
}

func processKafkaMessage(parentCtx context.Context, msg *sarama.ConsumerMessage) {
    // 提取追踪上下文（如果有）
    ctx := extractTraceContext(parentCtx, msg.Headers)

    ctx, span := tracer.Start(ctx, "kafka.process",
        trace.WithSpanKind(trace.SpanKindConsumer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.MessagingSystemKey.String("kafka"),
        semconv.MessagingDestinationKey.String(msg.Topic),
        semconv.MessagingOperationKey.String("process"),
        semconv.MessagingMessageIDKey.String(fmt.Sprintf("%d-%d", msg.Partition, msg.Offset)),
    )

    // 处理消息
    if err := handleMessage(ctx, msg.Value); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
    }
}

// RabbitMQ 消费者
func consumeRabbitMQMessages(ctx context.Context, queue string) {
    msgs, err := channel.Consume(
        queue,
        "",    // consumer
        false, // auto-ack
        false, // exclusive
        false, // no-local
        false, // no-wait
        nil,   // args
    )
    if err != nil {
        log.Fatal(err)
    }

    for msg := range msgs {
        processRabbitMQMessage(ctx, msg)
    }
}

func processRabbitMQMessage(parentCtx context.Context, msg amqp.Delivery) {
    ctx := extractTraceContext(parentCtx, msg.Headers)

    ctx, span := tracer.Start(ctx, "rabbitmq.process",
        trace.WithSpanKind(trace.SpanKindConsumer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.MessagingSystemKey.String("rabbitmq"),
        semconv.MessagingDestinationKey.String(msg.Exchange),
        attribute.String("messaging.rabbitmq.routing_key", msg.RoutingKey),
    )

    // 处理消息
    if err := handleMessage(ctx, msg.Body); err != nil {
        span.RecordError(err)
        msg.Nack(false, true)  // 重新入队
    } else {
        msg.Ack(false)
    }
}
```

---

## 使用场景51

### 场景矩阵

| 操作类型 | SpanKind | 父 Span Kind | 示例 |
|---------|----------|--------------|------|
| HTTP 请求处理 | SERVER | CLIENT (远程) | Web 服务器 |
| HTTP 请求发起 | CLIENT | INTERNAL/SERVER | HTTP 客户端 |
| gRPC 服务端 | SERVER | CLIENT (远程) | gRPC 服务 |
| gRPC 客户端 | CLIENT | INTERNAL/SERVER | gRPC 调用 |
| Kafka 生产 | PRODUCER | INTERNAL/SERVER | 发送消息 |
| Kafka 消费 | CONSUMER | PRODUCER (远程) | 处理消息 |
| 内部逻辑 | INTERNAL | ANY | 数据处理 |
| 数据库查询 | CLIENT | INTERNAL/SERVER | SQL 查询 |

### 追踪模式

#### 1. 同步 RPC 模式

```text
[Service A]                    [Service B]
    |                              |
    | CLIENT Span                  |
    |----------------------------->| SERVER Span
    |                              |  INTERNAL Span (处理)
    |<-----------------------------|
    |                              |
```

#### 2. 异步消息模式

```text
[Producer]                     [Consumer]
    |                              |
    | PRODUCER Span                |
    |---> [Message Queue] -------->| CONSUMER Span
    |                              |  INTERNAL Span (处理)
```

#### 3. 混合模式

```text
[API Gateway]           [Service A]            [Message Queue]         [Service B]
      |                     |                        |                      |
      | SERVER              |                        |                      |
      |  CLIENT ----------->| SERVER                 |                      |
      |                     |  INTERNAL              |                      |
      |                     |  PRODUCER ------------>| ------------------>  | CONSUMER
      |<--------------------|                        |                      |  INTERNAL
```

---

## Go 完整实现

### 完整的微服务示例

```go
package main

import (
    "context"
    "encoding/json"
    "net/http"
    
    "github.com/Shopify/sarama"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("order-service")

// 1. API Gateway: SERVER -> CLIENT
func apiGatewayHandler(w http.ResponseWriter, r *http.Request) {
    // SERVER Span: 接收客户端请求
    ctx, serverSpan := tracer.Start(r.Context(), r.URL.Path,
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer serverSpan.End()

    serverSpan.SetAttributes(
        semconv.HTTPMethodKey.String(r.Method),
        semconv.HTTPTargetKey.String(r.URL.Path),
    )

    // CLIENT Span: 调用订单服务
    order, err := callOrderService(ctx, "order-123")
    if err != nil {
        serverSpan.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    json.NewEncoder(w).Encode(order)
}

// 2. Order Service: CLIENT -> INTERNAL -> PRODUCER
func callOrderService(ctx context.Context, orderID string) (*Order, error) {
    // CLIENT Span: 调用远程服务
    ctx, clientSpan := tracer.Start(ctx, "OrderService/GetOrder",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer clientSpan.End()

    clientSpan.SetAttributes(
        semconv.RPCSystemKey.String("http"),
        semconv.RPCServiceKey.String("OrderService"),
        semconv.RPCMethodKey.String("GetOrder"),
    )

    // 发起 HTTP 请求（实际会创建新的 SERVER Span）
    resp, err := http.Get("http://order-service/orders/" + orderID)
    if err != nil {
        clientSpan.RecordError(err)
        return nil, err
    }
    defer resp.Body.Close()

    var order Order
    json.NewDecoder(resp.Body).Decode(&order)

    return &order, nil
}

func orderServiceHandler(w http.ResponseWriter, r *http.Request) {
    // SERVER Span: 处理订单请求
    ctx, serverSpan := tracer.Start(r.Context(), "GET /orders/:id",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer serverSpan.End()

    orderID := extractOrderID(r.URL.Path)

    // INTERNAL Span: 处理业务逻辑
    order, err := processOrder(ctx, orderID)
    if err != nil {
        serverSpan.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }

    // PRODUCER Span: 发送事件
    if err := sendOrderEvent(ctx, order); err != nil {
        serverSpan.RecordError(err)
    }

    json.NewEncoder(w).Encode(order)
}

func processOrder(ctx context.Context, orderID string) (*Order, error) {
    // INTERNAL Span: 内部逻辑
    ctx, span := tracer.Start(ctx, "process_order",
        trace.WithSpanKind(trace.SpanKindInternal),
    )
    defer span.End()

    span.SetAttributes(attribute.String("order.id", orderID))

    // 查询数据库（CLIENT Span）
    order, err := queryDatabase(ctx, orderID)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return order, nil
}

func queryDatabase(ctx context.Context, orderID string) (*Order, error) {
    // CLIENT Span: 数据库查询
    ctx, span := tracer.Start(ctx, "SELECT orders",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    span.SetAttributes(
        semconv.DBSystemKey.String("postgresql"),
        semconv.DBStatementKey.String("SELECT * FROM orders WHERE id = $1"),
    )

    // 执行查询
    var order Order
    // ... 数据库操作

    return &order, nil
}

func sendOrderEvent(ctx context.Context, order *Order) error {
    // PRODUCER Span: 发送消息
    ctx, span := tracer.Start(ctx, "kafka.send order_events",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()

    span.SetAttributes(
        semconv.MessagingSystemKey.String("kafka"),
        semconv.MessagingDestinationKey.String("order_events"),
    )

    message, _ := json.Marshal(order)
    err := kafkaProducer.SendMessage(&sarama.ProducerMessage{
        Topic: "order_events",
        Value: sarama.ByteEncoder(message),
    })
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// 3. Notification Service: CONSUMER -> INTERNAL -> CLIENT
func consumeOrderEvents(ctx context.Context) {
    for {
        select {
        case msg := <-kafkaConsumer.Messages():
            processOrderEvent(ctx, msg)
        case <-ctx.Done():
            return
        }
    }
}

func processOrderEvent(ctx context.Context, msg *sarama.ConsumerMessage) {
    // CONSUMER Span: 接收消息
    ctx, consumerSpan := tracer.Start(ctx, "kafka.process order_events",
        trace.WithSpanKind(trace.SpanKindConsumer),
    )
    defer consumerSpan.End()

    consumerSpan.SetAttributes(
        semconv.MessagingSystemKey.String("kafka"),
        semconv.MessagingDestinationKey.String(msg.Topic),
    )

    var order Order
    if err := json.Unmarshal(msg.Value, &order); err != nil {
        consumerSpan.RecordError(err)
        return
    }

    // INTERNAL Span: 处理事件
    if err := handleOrderEvent(ctx, &order); err != nil {
        consumerSpan.RecordError(err)
        consumerSpan.SetStatus(codes.Error, err.Error())
    }
}

func handleOrderEvent(ctx context.Context, order *Order) error {
    // INTERNAL Span
    ctx, span := tracer.Start(ctx, "handle_order_event",
        trace.WithSpanKind(trace.SpanKindInternal),
    )
    defer span.End()

    // CLIENT Span: 调用通知服务
    return sendNotification(ctx, order.UserID, "Order confirmed")
}

func sendNotification(ctx context.Context, userID, message string) error {
    // CLIENT Span: 调用外部服务
    ctx, span := tracer.Start(ctx, "POST /notifications",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    span.SetAttributes(
        semconv.HTTPMethodKey.String("POST"),
        semconv.HTTPURLKey.String("http://notification-service/notifications"),
    )

    // 发送通知
    // ...

    return nil
}

type Order struct {
    ID     string
    UserID string
    Amount float64
}
```

---

## 最佳实践

### 1. 正确选择 SpanKind

```go
// ✅ 推荐：HTTP 服务器
tracer.Start(ctx, "handle_request", trace.WithSpanKind(trace.SpanKindServer))

// ✅ 推荐：HTTP 客户端
tracer.Start(ctx, "call_api", trace.WithSpanKind(trace.SpanKindClient))

// ✅ 推荐：内部逻辑
tracer.Start(ctx, "process_data", trace.WithSpanKind(trace.SpanKindInternal))

// ❌ 避免：HTTP 服务器使用 CLIENT
tracer.Start(ctx, "handle_request", trace.WithSpanKind(trace.SpanKindClient))
```

### 2. 消息系统使用 PRODUCER/CONSUMER

```go
// ✅ 推荐：发送消息
tracer.Start(ctx, "kafka.send", trace.WithSpanKind(trace.SpanKindProducer))

// ✅ 推荐：接收消息
tracer.Start(ctx, "kafka.process", trace.WithSpanKind(trace.SpanKindConsumer))

// ❌ 避免：使用 CLIENT/SERVER
tracer.Start(ctx, "kafka.send", trace.WithSpanKind(trace.SpanKindClient))
```

### 3. 数据库操作使用 CLIENT

```go
// ✅ 推荐：数据库查询
tracer.Start(ctx, "db.query", trace.WithSpanKind(trace.SpanKindClient))

// ❌ 避免：使用 INTERNAL
tracer.Start(ctx, "db.query", trace.WithSpanKind(trace.SpanKindInternal))
```

### 4. 内部逻辑使用 INTERNAL

```go
// ✅ 推荐：业务逻辑
tracer.Start(ctx, "validate_input", trace.WithSpanKind(trace.SpanKindInternal))
tracer.Start(ctx, "calculate_price", trace.WithSpanKind(trace.SpanKindInternal))

// ⚠️ 注意：INTERNAL 是默认值，可以省略
tracer.Start(ctx, "validate_input")  // 自动使用 INTERNAL
```

---

## 常见问题

### Q1: 什么时候使用 INTERNAL？

**A**: 所有不涉及远程调用或消息传递的操作。

```go
// INTERNAL 适用场景
- 函数调用
- 数据验证
- 价格计算
- 数据转换
- 本地文件操作
```

### Q2: 数据库查询应该用什么 Kind？

**A**: 使用 CLIENT，因为数据库是外部系统。

```go
// ✅ 推荐
tracer.Start(ctx, "db.query", trace.WithSpanKind(trace.SpanKindClient))
```

### Q3: WebSocket 应该用什么 Kind？

**A**:

- **服务器端**: SERVER (接受连接)
- **客户端**: CLIENT (建立连接)
- **消息处理**: INTERNAL

### Q4: PRODUCER 和 CLIENT 有什么区别？

**A**:

- **PRODUCER**: 异步消息，不等待响应
- **CLIENT**: 同步调用，等待响应

### Q5: 可以省略 SpanKind 吗？

**A**: 可以，默认是 INTERNAL，但建议显式指定以提高可读性。

---

## 参考资源

### 官方文档

- [OpenTelemetry SpanKind](https://opentelemetry.io/docs/specs/otel/trace/api/#spankind)
- [Trace Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/general/trace/)

### Go 实现

- [go.opentelemetry.io/otel/trace](https://pkg.go.dev/go.opentelemetry.io/otel/trace)

### 相关文档

- [01_Span结构.md](./01_Span结构.md)
- [02_SpanContext.md](./02_SpanContext.md)
- [04_Status.md](./04_Status.md)

---

**🎉 恭喜！你已经掌握了 SpanKind 的完整知识！**

下一步：学习 [Status](./04_Status.md) 了解 Span 状态。

# RabbitMQ语义约定详解

> **企业级消息队列**: RabbitMQ Tracing与Metrics完整规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [RabbitMQ语义约定详解](#rabbitmq语义约定详解)
  - [目录](#目录)
  - [1. RabbitMQ概述](#1-rabbitmq概述)
    - [1.1 AMQP协议](#11-amqp协议)
    - [1.2 核心概念](#12-核心概念)
  - [2. RabbitMQ通用属性](#2-rabbitmq通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Producer属性](#3-producer属性)
    - [3.1 发布属性](#31-发布属性)
    - [3.2 Exchange属性](#32-exchange属性)
  - [4. Consumer属性](#4-consumer属性)
    - [4.1 消费属性](#41-消费属性)
    - [4.2 Queue属性](#42-queue属性)
  - [5. Context传播](#5-context传播)
    - [5.1 AMQP Headers](#51-amqp-headers)
    - [5.2 传播实现](#52-传播实现)
  - [6. Go实现示例](#6-go实现示例)
    - [6.1 Publisher](#61-publisher)
    - [6.2 Consumer](#62-consumer)
    - [6.3 RPC模式](#63-rpc模式)
  - [7. Python实现示例](#7-python实现示例)
    - [7.1 Pika实现](#71-pika实现)
    - [7.2 aio-pika实现](#72-aio-pika实现)
  - [8. Metrics定义](#8-metrics定义)
    - [8.1 Producer Metrics](#81-producer-metrics)
    - [8.2 Consumer Metrics](#82-consumer-metrics)
    - [8.3 Queue Metrics](#83-queue-metrics)
  - [9. 最佳实践](#9-最佳实践)
    - [9.1 可靠性保证](#91-可靠性保证)
    - [9.2 性能优化](#92-性能优化)
    - [9.3 监控告警](#93-监控告警)
  - [10. 完整示例](#10-完整示例)
    - [10.1 Work Queue模式](#101-work-queue模式)
    - [10.2 Topic Exchange模式](#102-topic-exchange模式)

---

## 1. RabbitMQ概述

### 1.1 AMQP协议

```text
AMQP (Advanced Message Queuing Protocol)

协议特点:
✅ 开放标准 (ISO/IEC 19464)
✅ 跨平台互操作
✅ 可靠消息传递
✅ 事务支持
✅ 确认机制

RabbitMQ特性:
✅ 高可用 (集群/镜像)
✅ 灵活路由 (Exchange)
✅ 消息持久化
✅ 多种Exchange类型
✅ 插件系统
✅ 管理界面
```

### 1.2 核心概念

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

RabbitMQ架构:

Producer → Exchange → Queue → Consumer

组件说明:

1. Producer (生产者)
   - 发布消息到Exchange

2. Exchange (交换器)
   - Direct: 精确匹配routing key
   - Fanout: 广播到所有绑定队列
   - Topic: 模式匹配routing key
   - Headers: 根据header匹配

3. Queue (队列)
   - 存储消息
   - FIFO顺序
   - 持久化/临时
   - 排他/共享

4. Binding (绑定)
   - Exchange与Queue的关联
   - Routing Key规则

5. Consumer (消费者)
   - 订阅Queue
   - 接收消息
   - ACK确认

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. RabbitMQ通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统标识 | `"rabbitmq"` |
| `messaging.destination.name` | string | Exchange或Queue名称 | `"orders_exchange"` |
| `messaging.operation` | string | 操作类型 | `"publish"`, `"receive"` |
| `messaging.protocol` | string | 协议名称 | `"AMQP"` |
| `messaging.protocol_version` | string | 协议版本 | `"0.9.1"` |
| `net.peer.name` | string | RabbitMQ服务器地址 | `"rabbitmq.example.com"` |
| `net.peer.port` | int | RabbitMQ服务器端口 | `5672` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.rabbitmq.routing_key` | string | Routing Key | `"order.created"` |
| `messaging.rabbitmq.exchange.type` | string | Exchange类型 | `"topic"`, `"direct"`, `"fanout"` |
| `messaging.rabbitmq.delivery_mode` | int | 投递模式 | `1` (transient), `2` (persistent) |
| `messaging.message.id` | string | 消息ID | `"msg-123456"` |
| `messaging.message.correlation_id` | string | 关联ID | `"corr-789"` |
| `messaging.message.body.size` | int | 消息体大小(字节) | `1024` |
| `messaging.rabbitmq.priority` | int | 消息优先级 | `5` (0-255) |
| `messaging.rabbitmq.expiration` | string | 消息过期时间(ms) | `"60000"` |

---

## 3. Producer属性

### 3.1 发布属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

RabbitMQ Publisher属性:

必需:
✅ messaging.system = "rabbitmq"
✅ messaging.destination.name (Exchange名称)
✅ messaging.operation = "publish"
✅ messaging.protocol = "AMQP"

推荐:
📋 messaging.rabbitmq.routing_key
📋 messaging.rabbitmq.exchange.type
📋 messaging.rabbitmq.delivery_mode
📋 messaging.message.id
📋 messaging.message.body.size

示例:
    ```go
    span.SetAttributes(
        semconv.MessagingSystemKey.String("rabbitmq"),
        semconv.MessagingDestinationNameKey.String("orders_exchange"),
        semconv.MessagingOperationKey.String("publish"),
        semconv.MessagingProtocolKey.String("AMQP"),
        semconv.MessagingProtocolVersionKey.String("0.9.1"),
        attribute.String("messaging.rabbitmq.routing_key", "order.created"),
        attribute.String("messaging.rabbitmq.exchange.type", "topic"),
        attribute.Int("messaging.rabbitmq.delivery_mode", 2), // persistent
        attribute.String("messaging.message.id", messageID),
        attribute.Int("messaging.message.body.size", len(body)),
    )
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 3.2 Exchange属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.rabbitmq.exchange.name` | string | Exchange名称 | `"orders_exchange"` |
| `messaging.rabbitmq.exchange.type` | string | Exchange类型 | `"topic"` |
| `messaging.rabbitmq.exchange.durable` | boolean | 持久化 | `true` |
| `messaging.rabbitmq.exchange.auto_delete` | boolean | 自动删除 | `false` |
| `messaging.rabbitmq.exchange.internal` | boolean | 内部Exchange | `false` |

---

## 4. Consumer属性

### 4.1 消费属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

RabbitMQ Consumer属性:

必需:
✅ messaging.system = "rabbitmq"
✅ messaging.destination.name (Queue名称)
✅ messaging.operation = "receive"
✅ messaging.protocol = "AMQP"

推荐:
📋 messaging.rabbitmq.consumer_tag
📋 messaging.rabbitmq.delivery_tag
📋 messaging.rabbitmq.redelivered
📋 messaging.message.id
📋 messaging.message.body.size

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.rabbitmq.consumer_tag` | string | Consumer标识 | `"ctag-1234"` |
| `messaging.rabbitmq.delivery_tag` | int | 投递标签 | `123` |
| `messaging.rabbitmq.redelivered` | boolean | 是否重投递 | `false` |
| `messaging.rabbitmq.exclusive` | boolean | 排他消费 | `false` |
| `messaging.rabbitmq.no_ack` | boolean | 自动ACK | `false` |

### 4.2 Queue属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.rabbitmq.queue.name` | string | Queue名称 | `"orders_queue"` |
| `messaging.rabbitmq.queue.durable` | boolean | 持久化 | `true` |
| `messaging.rabbitmq.queue.exclusive` | boolean | 排他队列 | `false` |
| `messaging.rabbitmq.queue.auto_delete` | boolean | 自动删除 | `false` |
| `messaging.rabbitmq.queue.message_count` | int | 队列消息数 | `100` |
| `messaging.rabbitmq.queue.consumer_count` | int | 消费者数 | `3` |

---

## 5. Context传播

### 5.1 AMQP Headers

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

AMQP消息Headers支持:

RabbitMQ原生支持消息Headers:

Headers Table:
- traceparent: <w3c-trace-context>
- tracestate: <vendor-state>
- baggage: <baggage-value>
- x-custom-header: <custom-value>

Properties:
- message_id
- correlation_id
- reply_to
- expiration
- timestamp
- type
- user_id
- app_id

优点:
✅ 标准AMQP Properties
✅ 自定义Headers
✅ 不影响消息体
✅ 完美支持追踪

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.2 传播实现

```go
// Inject trace context
func injectTraceContext(ctx context.Context, headers amqp.Table) {
    // 注入W3C Trace Context
    propagator := otel.GetTextMapPropagator()
    carrier := &AMQPHeaderCarrier{headers: headers}
    propagator.Inject(ctx, carrier)
}

// Extract trace context
func extractTraceContext(headers amqp.Table) context.Context {
    propagator := otel.GetTextMapPropagator()
    carrier := &AMQPHeaderCarrier{headers: headers}
    return propagator.Extract(context.Background(), carrier)
}

// AMQP Header Carrier实现
type AMQPHeaderCarrier struct {
    headers amqp.Table
}

func (c *AMQPHeaderCarrier) Get(key string) string {
    if val, ok := c.headers[key]; ok {
        if str, ok := val.(string); ok {
            return str
        }
    }
    return ""
}

func (c *AMQPHeaderCarrier) Set(key, value string) {
    c.headers[key] = value
}

func (c *AMQPHeaderCarrier) Keys() []string {
    keys := make([]string, 0, len(c.headers))
    for k := range c.headers {
        keys = append(keys, k)
    }
    return keys
}
```

---

## 6. Go实现示例

### 6.1 Publisher

```go
package main

import (
    "context"
    "time"
    
    amqp "github.com/rabbitmq/amqp091-go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

func PublishWithTracing(
    ctx context.Context,
    ch *amqp.Channel,
    exchange, routingKey string,
    body []byte,
) error {
    tracer := otel.Tracer("rabbitmq-publisher")
    
    // 创建Producer Span
    ctx, span := tracer.Start(ctx, "rabbitmq.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("rabbitmq"),
            semconv.MessagingDestinationNameKey.String(exchange),
            semconv.MessagingOperationKey.String("publish"),
            semconv.MessagingProtocolKey.String("AMQP"),
            semconv.MessagingProtocolVersionKey.String("0.9.1"),
            attribute.String("messaging.rabbitmq.routing_key", routingKey),
            attribute.String("messaging.rabbitmq.exchange.type", "topic"),
            attribute.Int("messaging.rabbitmq.delivery_mode", 2), // persistent
            attribute.Int("messaging.message.body.size", len(body)),
        ),
    )
    defer span.End()
    
    // 创建消息
    messageID := generateMessageID()
    headers := make(amqp.Table)
    
    // 注入Trace Context
    injectTraceContext(ctx, headers)
    
    msg := amqp.Publishing{
        MessageId:    messageID,
        Timestamp:    time.Now(),
        ContentType:  "application/json",
        DeliveryMode: 2, // persistent
        Headers:      headers,
        Body:         body,
    }
    
    // 添加消息ID到span
    span.SetAttributes(
        attribute.String("messaging.message.id", messageID),
    )
    
    // 发布消息
    err := ch.PublishWithContext(
        ctx,
        exchange,
        routingKey,
        false, // mandatory
        false, // immediate
        msg,
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "publish failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "published")
    return nil
}

// 使用Publisher Confirms确保可靠性
func PublishWithConfirms(
    ctx context.Context,
    ch *amqp.Channel,
    exchange, routingKey string,
    body []byte,
) error {
    tracer := otel.Tracer("rabbitmq-publisher")
    
    ctx, span := tracer.Start(ctx, "rabbitmq.publish.confirmed",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()
    
    // 启用Publisher Confirms
    if err := ch.Confirm(false); err != nil {
        span.RecordError(err)
        return err
    }
    
    confirms := ch.NotifyPublish(make(chan amqp.Confirmation, 1))
    
    // 发布消息
    err := PublishWithTracing(ctx, ch, exchange, routingKey, body)
    if err != nil {
        return err
    }
    
    // 等待确认
    select {
    case confirm := <-confirms:
        if confirm.Ack {
            span.SetStatus(codes.Ok, "confirmed")
            return nil
        } else {
            span.SetStatus(codes.Error, "nacked")
            return ErrPublishNacked
        }
    case <-time.After(5 * time.Second):
        span.SetStatus(codes.Error, "confirm timeout")
        return ErrConfirmTimeout
    }
}
```

### 6.2 Consumer

```go
func ConsumeWithTracing(
    ch *amqp.Channel,
    queueName string,
    handler func(context.Context, amqp.Delivery) error,
) error {
    tracer := otel.Tracer("rabbitmq-consumer")
    
    // 声明Queue
    q, err := ch.QueueDeclare(
        queueName,
        true,  // durable
        false, // auto-delete
        false, // exclusive
        false, // no-wait
        nil,   // arguments
    )
    if err != nil {
        return err
    }
    
    // 设置Qos
    err = ch.Qos(
        10,    // prefetch count
        0,     // prefetch size
        false, // global
    )
    if err != nil {
        return err
    }
    
    // 开始消费
    msgs, err := ch.Consume(
        q.Name,
        "",    // consumer tag (auto-generated)
        false, // auto-ack
        false, // exclusive
        false, // no-local
        false, // no-wait
        nil,   // args
    )
    if err != nil {
        return err
    }
    
    // 处理消息
    for msg := range msgs {
        // 提取Trace Context
        ctx := extractTraceContext(msg.Headers)
        
        // 创建Consumer Span
        ctx, span := tracer.Start(ctx, "rabbitmq.receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("rabbitmq"),
                semconv.MessagingDestinationNameKey.String(q.Name),
                semconv.MessagingOperationKey.String("receive"),
                semconv.MessagingProtocolKey.String("AMQP"),
                attribute.String("messaging.message.id", msg.MessageId),
                attribute.String("messaging.rabbitmq.routing_key", msg.RoutingKey),
                attribute.Int64("messaging.rabbitmq.delivery_tag", 
                    int64(msg.DeliveryTag)),
                attribute.Bool("messaging.rabbitmq.redelivered", 
                    msg.Redelivered),
                attribute.Int("messaging.message.body.size", len(msg.Body)),
            ),
        )
        
        // 处理消息
        err := handler(ctx, msg)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            
            // Nack with requeue
            msg.Nack(false, true)
        } else {
            span.SetStatus(codes.Ok, "processed")
            
            // Ack
            msg.Ack(false)
        }
        
        span.End()
    }
    
    return nil
}
```

### 6.3 RPC模式

```go
// RPC Client
func RPCCallWithTracing(
    ctx context.Context,
    ch *amqp.Channel,
    exchange, routingKey string,
    body []byte,
) ([]byte, error) {
    tracer := otel.Tracer("rabbitmq-rpc-client")
    
    ctx, span := tracer.Start(ctx, "rabbitmq.rpc.call",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("rabbitmq"),
            semconv.MessagingDestinationNameKey.String(exchange),
            semconv.MessagingOperationKey.String("rpc"),
        ),
    )
    defer span.End()
    
    // 声明reply queue
    replyQueue, err := ch.QueueDeclare(
        "",    // name (auto-generated)
        false, // durable
        true,  // auto-delete
        true,  // exclusive
        false, // no-wait
        nil,   // args
    )
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    // 生成correlation ID
    correlationID := generateCorrelationID()
    
    // 注入trace context
    headers := make(amqp.Table)
    injectTraceContext(ctx, headers)
    
    // 发布请求
    err = ch.PublishWithContext(
        ctx,
        exchange,
        routingKey,
        false,
        false,
        amqp.Publishing{
            CorrelationId: correlationID,
            ReplyTo:       replyQueue.Name,
            Headers:       headers,
            Body:          body,
        },
    )
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.String("messaging.message.correlation_id", correlationID),
        attribute.String("messaging.rabbitmq.reply_to", replyQueue.Name),
    )
    
    // 等待响应
    msgs, err := ch.Consume(
        replyQueue.Name,
        "",
        true,
        false,
        false,
        false,
        nil,
    )
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    select {
    case msg := <-msgs:
        if msg.CorrelationId == correlationID {
            span.SetStatus(codes.Ok, "rpc completed")
            return msg.Body, nil
        }
    case <-time.After(30 * time.Second):
        span.SetStatus(codes.Error, "rpc timeout")
        return nil, ErrRPCTimeout
    }
    
    return nil, ErrRPCFailed
}

// RPC Server
func RPCServerWithTracing(
    ch *amqp.Channel,
    queueName string,
    handler func(context.Context, []byte) ([]byte, error),
) error {
    tracer := otel.Tracer("rabbitmq-rpc-server")
    
    msgs, err := ch.Consume(
        queueName,
        "",
        false,
        false,
        false,
        false,
        nil,
    )
    if err != nil {
        return err
    }
    
    for msg := range msgs {
        // 提取context
        ctx := extractTraceContext(msg.Headers)
        
        ctx, span := tracer.Start(ctx, "rabbitmq.rpc.handle",
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("rabbitmq"),
                semconv.MessagingOperationKey.String("rpc"),
                attribute.String("messaging.message.correlation_id", 
                    msg.CorrelationId),
            ),
        )
        
        // 处理请求
        response, err := handler(ctx, msg.Body)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            msg.Nack(false, false)
            span.End()
            continue
        }
        
        // 注入trace context到响应
        responseHeaders := make(amqp.Table)
        injectTraceContext(ctx, responseHeaders)
        
        // 发送响应
        err = ch.PublishWithContext(
            ctx,
            "",
            msg.ReplyTo,
            false,
            false,
            amqp.Publishing{
                CorrelationId: msg.CorrelationId,
                Headers:       responseHeaders,
                Body:          response,
            },
        )
        
        if err != nil {
            span.RecordError(err)
            msg.Nack(false, true)
        } else {
            span.SetStatus(codes.Ok, "replied")
            msg.Ack(false)
        }
        
        span.End()
    }
    
    return nil
}
```

---

## 7. Python实现示例

### 7.1 Pika实现

```python
import pika
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

def publish_with_tracing(
    channel: pika.BlockingChannel,
    exchange: str,
    routing_key: str,
    body: bytes
):
    """发布消息with tracing"""
    with tracer.start_as_current_span(
        "rabbitmq.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "rabbitmq",
            SpanAttributes.MESSAGING_DESTINATION_NAME: exchange,
            SpanAttributes.MESSAGING_OPERATION: "publish",
            SpanAttributes.MESSAGING_PROTOCOL: "AMQP",
            "messaging.rabbitmq.routing_key": routing_key,
            "messaging.message.body.size": len(body),
        }
    ) as span:
        # 注入trace context
        headers = {}
        propagate.inject(headers)
        
        # 发布消息
        properties = pika.BasicProperties(
            delivery_mode=2,  # persistent
            headers=headers,
        )
        
        try:
            channel.basic_publish(
                exchange=exchange,
                routing_key=routing_key,
                body=body,
                properties=properties,
            )
            span.set_status(Status(StatusCode.OK))
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def consume_with_tracing(
    channel: pika.BlockingChannel,
    queue_name: str,
    handler
):
    """消费消息with tracing"""
    def callback(ch, method, properties, body):
        # 提取trace context
        headers = properties.headers or {}
        ctx = propagate.extract(headers)
        
        # 创建span
        with tracer.start_as_current_span(
            "rabbitmq.receive",
            context=ctx,
            kind=SpanKind.CONSUMER,
            attributes={
                SpanAttributes.MESSAGING_SYSTEM: "rabbitmq",
                SpanAttributes.MESSAGING_DESTINATION_NAME: queue_name,
                SpanAttributes.MESSAGING_OPERATION: "receive",
                "messaging.rabbitmq.routing_key": method.routing_key,
                "messaging.rabbitmq.delivery_tag": method.delivery_tag,
                "messaging.rabbitmq.redelivered": method.redelivered,
                "messaging.message.body.size": len(body),
            }
        ) as span:
            try:
                # 处理消息
                handler(body)
                
                # ACK
                ch.basic_ack(delivery_tag=method.delivery_tag)
                span.set_status(Status(StatusCode.OK))
            except Exception as e:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR))
                
                # NACK with requeue
                ch.basic_nack(
                    delivery_tag=method.delivery_tag,
                    requeue=True
                )
    
    # 设置Qos
    channel.basic_qos(prefetch_count=10)
    
    # 开始消费
    channel.basic_consume(
        queue=queue_name,
        on_message_callback=callback,
        auto_ack=False
    )
    
    channel.start_consuming()
```

### 7.2 aio-pika实现

```python
import asyncio
import aio_pika
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

async def publish_async_with_tracing(
    channel: aio_pika.Channel,
    exchange_name: str,
    routing_key: str,
    body: bytes
):
    """异步发布消息with tracing"""
    with tracer.start_as_current_span(
        "rabbitmq.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "rabbitmq",
            SpanAttributes.MESSAGING_DESTINATION_NAME: exchange_name,
            SpanAttributes.MESSAGING_OPERATION: "publish",
            "messaging.rabbitmq.routing_key": routing_key,
        }
    ) as span:
        # 注入trace context
        headers = {}
        propagate.inject(headers)
        
        # 获取exchange
        exchange = await channel.get_exchange(exchange_name)
        
        # 创建消息
        message = aio_pika.Message(
            body=body,
            delivery_mode=aio_pika.DeliveryMode.PERSISTENT,
            headers=headers,
        )
        
        span.set_attribute("messaging.message.body.size", len(body))
        
        try:
            # 发布
            await exchange.publish(
                message,
                routing_key=routing_key,
            )
            span.set_status(Status(StatusCode.OK))
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

async def consume_async_with_tracing(
    channel: aio_pika.Channel,
    queue_name: str,
    handler
):
    """异步消费消息with tracing"""
    # 声明queue
    queue = await channel.declare_queue(
        queue_name,
        durable=True,
    )
    
    # 设置Qos
    await channel.set_qos(prefetch_count=10)
    
    async with queue.iterator() as queue_iter:
        async for message in queue_iter:
            async with message.process():
                # 提取trace context
                headers = message.headers or {}
                ctx = propagate.extract(headers)
                
                # 创建span
                with tracer.start_as_current_span(
                    "rabbitmq.receive",
                    context=ctx,
                    kind=SpanKind.CONSUMER,
                    attributes={
                        SpanAttributes.MESSAGING_SYSTEM: "rabbitmq",
                        SpanAttributes.MESSAGING_DESTINATION_NAME: queue_name,
                        SpanAttributes.MESSAGING_OPERATION: "receive",
                        "messaging.rabbitmq.routing_key": message.routing_key,
                        "messaging.rabbitmq.delivery_tag": message.delivery_tag,
                        "messaging.rabbitmq.redelivered": message.redelivered,
                        "messaging.message.body.size": len(message.body),
                    }
                ) as span:
                    try:
                        # 处理消息
                        await handler(message.body)
                        span.set_status(Status(StatusCode.OK))
                        # message.process()会自动ACK
                    except Exception as e:
                        span.record_exception(e)
                        span.set_status(Status(StatusCode.ERROR))
                        # 异常会触发NACK with requeue
                        raise
```

---

## 8. Metrics定义

### 8.1 Producer Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.rabbitmq.publish.duration` | Histogram | ms | 发布延迟 |
| `messaging.rabbitmq.publish.messages` | Counter | messages | 发布消息数 |
| `messaging.rabbitmq.publish.bytes` | Counter | bytes | 发布字节数 |
| `messaging.rabbitmq.publish.errors` | Counter | errors | 发布错误数 |
| `messaging.rabbitmq.publish.confirms` | Counter | confirms | 确认数 |
| `messaging.rabbitmq.publish.returns` | Counter | returns | 返回数 |

### 8.2 Consumer Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.rabbitmq.receive.duration` | Histogram | ms | 消费延迟 |
| `messaging.rabbitmq.receive.messages` | Counter | messages | 接收消息数 |
| `messaging.rabbitmq.receive.bytes` | Counter | bytes | 接收字节数 |
| `messaging.rabbitmq.ack.messages` | Counter | messages | ACK消息数 |
| `messaging.rabbitmq.nack.messages` | Counter | messages | NACK消息数 |
| `messaging.rabbitmq.reject.messages` | Counter | messages | Reject消息数 |

### 8.3 Queue Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.rabbitmq.queue.messages` | Gauge | messages | 队列消息数 |
| `messaging.rabbitmq.queue.messages.ready` | Gauge | messages | Ready消息数 |
| `messaging.rabbitmq.queue.messages.unacked` | Gauge | messages | 未ACK消息数 |
| `messaging.rabbitmq.queue.consumers` | Gauge | consumers | 消费者数 |
| `messaging.rabbitmq.queue.memory` | Gauge | bytes | 队列内存使用 |

---

## 9. 最佳实践

### 9.1 可靠性保证

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

可靠性保证机制:

1. Publisher Confirms ⭐⭐⭐⭐⭐
   - 确保消息到达Broker
   - 等待Broker确认
   - 重试机制

2. 消息持久化 ⭐⭐⭐⭐⭐
   - Queue Durable
   - Message Persistent
   - Exchange Durable

3. 手动ACK ⭐⭐⭐⭐⭐
   - 禁用Auto-ACK
   - 处理成功后ACK
   - 失败后NACK/Reject

4. Prefetch设置 ⭐⭐⭐⭐
   - 合理设置prefetch_count
   - 避免消息堆积
   - 平衡负载

5. Dead Letter Exchange ⭐⭐⭐⭐
   - 处理失败消息
   - 重试队列
   - 错误追踪

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 性能优化

```go
// 连接池
type ConnectionPool struct {
    connections chan *amqp.Connection
    factory     func() (*amqp.Connection, error)
}

// 批量发布
func PublishBatch(
    ch *amqp.Channel,
    exchange, routingKey string,
    messages [][]byte,
) error {
    for _, msg := range messages {
        err := ch.Publish(exchange, routingKey, false, false,
            amqp.Publishing{Body: msg})
        if err != nil {
            return err
        }
    }
    return nil
}

// 并发消费
func StartWorkerPool(
    conn *amqp.Connection,
    queueName string,
    numWorkers int,
    handler func(amqp.Delivery) error,
) {
    for i := 0; i < numWorkers; i++ {
        go func(workerID int) {
            ch, _ := conn.Channel()
            defer ch.Close()
            
            ConsumeWithTracing(ch, queueName, handler)
        }(i)
    }
}
```

### 9.3 监控告警

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键监控指标:

1. 连接/Channel
   - 连接数
   - Channel数
   - 连接状态

2. Queue
   - Ready消息数
   - Unacked消息数
   - 消费者数
   - 消息堆积

3. 性能
   - 发布/消费速率
   - 消息延迟
   - 吞吐量

4. 错误
   - 连接失败
   - 发布失败
   - 消费失败
   - NACK率

告警规则:
- Queue深度 > 10000
- Unacked消息 > 5000
- 无消费者 > 5分钟
- 消息堆积速率 > 100/s
- NACK率 > 5%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 10. 完整示例

### 10.1 Work Queue模式

```go
// Worker Queue实现
func WorkQueueExample() {
    conn, _ := amqp.Dial("amqp://guest:guest@localhost:5672/")
    defer conn.Close()
    
    // Producer
    go func() {
        ch, _ := conn.Channel()
        defer ch.Close()
        
        // 声明queue
        q, _ := ch.QueueDeclare("tasks", true, false, false, false, nil)
        
        // 发布任务
        for i := 0; i < 100; i++ {
            body := []byte(fmt.Sprintf("Task %d", i))
            PublishWithTracing(
                context.Background(),
                ch,
                "",      // default exchange
                q.Name,
                body,
            )
            time.Sleep(100 * time.Millisecond)
        }
    }()
    
    // Workers
    for i := 0; i < 5; i++ {
        go func(workerID int) {
            ch, _ := conn.Channel()
            defer ch.Close()
            
            ConsumeWithTracing(ch, "tasks", 
                func(ctx context.Context, msg amqp.Delivery) error {
                    log.Printf("Worker %d: %s", workerID, msg.Body)
                    time.Sleep(1 * time.Second) // 模拟处理
                    return nil
                })
        }(i)
    }
    
    select {}
}
```

### 10.2 Topic Exchange模式

```go
// Topic Exchange实现
func TopicExchangeExample() {
    conn, _ := amqp.Dial("amqp://guest:guest@localhost:5672/")
    defer conn.Close()
    
    ch, _ := conn.Channel()
    defer ch.Close()
    
    // 声明topic exchange
    err := ch.ExchangeDeclare(
        "logs_topic", // name
        "topic",      // type
        true,         // durable
        false,        // auto-deleted
        false,        // internal
        false,        // no-wait
        nil,          // arguments
    )
    
    // 订阅不同的routing key pattern
    patterns := []string{
        "*.error",        // 所有error日志
        "auth.*",         // auth服务所有日志
        "order.critical", // order关键日志
    }
    
    for _, pattern := range patterns {
        go func(p string) {
            ch, _ := conn.Channel()
            q, _ := ch.QueueDeclare("", false, true, true, false, nil)
            
            // 绑定
            ch.QueueBind(q.Name, p, "logs_topic", false, nil)
            
            // 消费
            ConsumeWithTracing(ch, q.Name,
                func(ctx context.Context, msg amqp.Delivery) error {
                    log.Printf("Pattern %s: %s", p, msg.Body)
                    return nil
                })
        }(pattern)
    }
    
    // 发布不同routing key的消息
    routingKeys := []string{
        "auth.info",
        "auth.error",
        "order.info",
        "order.critical",
    }
    
    for _, rk := range routingKeys {
        body := []byte(fmt.Sprintf("Log message: %s", rk))
        PublishWithTracing(
            context.Background(),
            ch,
            "logs_topic",
            rk,
            body,
        )
    }
}
```

---

**文档状态**: ✅ 完成  
**RabbitMQ版本**: v3.12+  
**AMQP版本**: 0.9.1  
**适用场景**: 企业消息队列、微服务通信、任务队列

**关键特性**:

- ✅ AMQP原生Headers支持
- ✅ Publisher Confirms可靠性
- ✅ 多种Exchange类型
- ✅ RPC模式追踪
- ✅ Dead Letter机制
- ✅ Go/Python完整示例

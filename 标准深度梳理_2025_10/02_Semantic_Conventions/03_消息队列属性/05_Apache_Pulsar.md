# Apache Pulsar语义约定详解

> **下一代消息队列**: Apache Pulsar Tracing与Metrics完整规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [Apache Pulsar语义约定详解](#apache-pulsar语义约定详解)
  - [目录](#目录)
  - [1. Pulsar概述](#1-pulsar概述)
    - [1.1 Pulsar特点](#11-pulsar特点)
    - [1.2 核心架构](#12-核心架构)
  - [2. Pulsar通用属性](#2-pulsar通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Producer属性](#3-producer属性)
    - [3.1 基本属性](#31-基本属性)
    - [3.2 分区属性](#32-分区属性)
  - [4. Consumer属性](#4-consumer属性)
    - [4.1 订阅属性](#41-订阅属性)
    - [4.2 消费模式](#42-消费模式)
  - [5. Context传播](#5-context传播)
    - [5.1 Message Properties](#51-message-properties)
    - [5.2 传播实现](#52-传播实现)
  - [6. Go实现示例](#6-go实现示例)
    - [6.1 Producer](#61-producer)
    - [6.2 Consumer](#62-consumer)
    - [6.3 Reader模式](#63-reader模式)
  - [7. Java实现示例](#7-java实现示例)
    - [7.1 Producer](#71-producer)
    - [7.2 Consumer](#72-consumer)
  - [8. Python实现示例](#8-python实现示例)
    - [8.1 Producer](#81-producer)
    - [8.2 Consumer](#82-consumer)
  - [9. Metrics定义](#9-metrics定义)
    - [9.1 Producer Metrics](#91-producer-metrics)
    - [9.2 Consumer Metrics](#92-consumer-metrics)
    - [9.3 Topic Metrics](#93-topic-metrics)
  - [10. 高级特性](#10-高级特性)
    - [10.1 多租户](#101-多租户)
    - [10.2 Geo-Replication](#102-geo-replication)
    - [10.3 分层存储](#103-分层存储)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 性能优化](#111-性能优化)
    - [11.2 可靠性保证](#112-可靠性保证)
    - [11.3 监控建议](#113-监控建议)

---

## 1. Pulsar概述

### 1.1 Pulsar特点

```text
Apache Pulsar - 下一代云原生消息平台

核心特性:
✅ 多租户 (Tenant/Namespace/Topic)
✅ 分层存储 (BookKeeper + S3/HDFS)
✅ Geo-Replication (跨地域复制)
✅ 统一消息模型 (Queue + Stream)
✅ 分区Topic (水平扩展)
✅ Schema Registry (内置)
✅ Pulsar Functions (Serverless)
✅ Pulsar IO (Connector)

vs Kafka对比:
✅ 更好的多租户隔离
✅ 真正的分层存储
✅ 更灵活的订阅模式
✅ 内置Schema支持
✅ 更简单的运维

vs RabbitMQ对比:
✅ 更高的吞吐量
✅ 更好的持久化
✅ 水平扩展能力
✅ 分布式架构
```

### 1.2 核心架构

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar架构:

┌─────────────────────────────────────────────────┐
│                   Producers                      │
└──────────────────┬──────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────┐
│             Pulsar Brokers (无状态)              │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐      │
│  │ Broker 1 │  │ Broker 2 │  │ Broker 3 │      │
│  └──────────┘  └──────────┘  └──────────┘      │
└──────────────────┬──────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────┐
│         BookKeeper (存储层 - 有状态)             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐      │
│  │  Bookie 1│  │  Bookie 2│  │  Bookie 3│      │
│  └──────────┘  └──────────┘  └──────────┘      │
└─────────────────────────────────────────────────┘

组件职责:

1. Broker (计算层)
   - 无状态服务
   - 负责消息路由
   - 处理Producer/Consumer
   - 可自由扩缩容

2. BookKeeper (存储层)
   - 有状态存储
   - 高性能日志存储
   - 多副本保证
   - 自动分片

3. ZooKeeper (协调)
   - 元数据管理
   - Leader选举
   - 配置管理

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Pulsar通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统标识 | `"pulsar"` |
| `messaging.destination.name` | string | Topic名称 | `"persistent://tenant/namespace/topic"` |
| `messaging.operation` | string | 操作类型 | `"publish"`, `"receive"` |
| `net.peer.name` | string | Pulsar服务地址 | `"pulsar.example.com"` |
| `net.peer.port` | int | Pulsar服务端口 | `6650` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.pulsar.tenant` | string | 租户名称 | `"public"` |
| `messaging.pulsar.namespace` | string | 命名空间 | `"default"` |
| `messaging.pulsar.topic` | string | Topic名称 | `"orders"` |
| `messaging.pulsar.topic.type` | string | Topic类型 | `"persistent"`, `"non-persistent"` |
| `messaging.pulsar.partition` | int | 分区索引 | `0` |
| `messaging.message.id` | string | 消息ID | `"123:45:0"` |
| `messaging.message.body.size` | int | 消息体大小(字节) | `1024` |
| `messaging.pulsar.schema.type` | string | Schema类型 | `"avro"`, `"json"`, `"protobuf"` |

---

## 3. Producer属性

### 3.1 基本属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar Producer属性:

必需:
✅ messaging.system = "pulsar"
✅ messaging.destination.name (完整Topic名称)
✅ messaging.operation = "publish"
✅ net.peer.name
✅ net.peer.port

推荐:
📋 messaging.pulsar.tenant
📋 messaging.pulsar.namespace
📋 messaging.pulsar.topic
📋 messaging.pulsar.partition (分区Topic)
📋 messaging.pulsar.producer.name
📋 messaging.message.id
📋 messaging.message.body.size

示例:
    ```go
    span.SetAttributes(
        semconv.MessagingSystemKey.String("pulsar"),
        semconv.MessagingDestinationNameKey.String(
            "persistent://public/default/orders"),
        semconv.MessagingOperationKey.String("publish"),
        attribute.String("messaging.pulsar.tenant", "public"),
        attribute.String("messaging.pulsar.namespace", "default"),
        attribute.String("messaging.pulsar.topic", "orders"),
        attribute.String("messaging.pulsar.producer.name", "producer-1"),
        attribute.String("messaging.message.id", msgID.String()),
        attribute.Int("messaging.message.body.size", len(payload)),
    )
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 3.2 分区属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.pulsar.partition.count` | int | 分区总数 | `10` |
| `messaging.pulsar.partition.index` | int | 分区索引 | `3` |
| `messaging.pulsar.partition.key` | string | 分区键 | `"user-123"` |
| `messaging.pulsar.routing.mode` | string | 路由模式 | `"RoundRobinPartition"`, `"SinglePartition"` |
| `messaging.pulsar.batching.enabled` | boolean | 批处理启用 | `true` |
| `messaging.pulsar.batching.max_messages` | int | 批处理最大消息数 | `1000` |

---

## 4. Consumer属性

### 4.1 订阅属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar Consumer属性:

必需:
✅ messaging.system = "pulsar"
✅ messaging.destination.name (Topic名称)
✅ messaging.operation = "receive"
✅ messaging.pulsar.subscription.name

推荐:
📋 messaging.pulsar.subscription.type
📋 messaging.pulsar.consumer.name
📋 messaging.pulsar.partition
📋 messaging.message.id
📋 messaging.pulsar.redelivery_count

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.pulsar.subscription.name` | string | 订阅名称 | `"my-subscription"` |
| `messaging.pulsar.subscription.type` | string | 订阅类型 | `"Exclusive"`, `"Shared"`, `"Failover"`, `"Key_Shared"` |
| `messaging.pulsar.consumer.name` | string | Consumer名称 | `"consumer-1"` |
| `messaging.pulsar.message.redelivery_count` | int | 重投递次数 | `0` |
| `messaging.pulsar.message.publish_time` | int64 | 发布时间戳(ms) | `1609459200000` |

### 4.2 消费模式

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar订阅类型:

1. Exclusive (独占)
   - 单个Consumer
   - 顺序保证
   - 故障转移

2. Shared (共享)
   - 多个Consumer
   - 负载均衡
   - 无顺序保证

3. Failover (故障转移)
   - 主Consumer + 备Consumer
   - 自动故障转移
   - 顺序保证

4. Key_Shared (键共享)
   - 按Key分配Consumer
   - 同Key顺序保证
   - 负载均衡

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 5. Context传播

### 5.1 Message Properties

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar Message Properties:

Pulsar原生支持消息Properties (类似Headers):

Properties (Map<String, String>):
- traceparent: <w3c-trace-context>
- tracestate: <vendor-state>
- baggage: <baggage-value>
- custom-key: <custom-value>

优点:
✅ 原生支持
✅ 键值对存储
✅ 不影响消息体
✅ 完美支持追踪

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.2 传播实现

```go
// Pulsar Message Properties Carrier
type PulsarPropertiesCarrier struct {
    properties map[string]string
}

func (c *PulsarPropertiesCarrier) Get(key string) string {
    return c.properties[key]
}

func (c *PulsarPropertiesCarrier) Set(key, value string) {
    c.properties[key] = value
}

func (c *PulsarPropertiesCarrier) Keys() []string {
    keys := make([]string, 0, len(c.properties))
    for k := range c.properties {
        keys = append(keys, k)
    }
    return keys
}

// Inject trace context
func injectTraceContext(ctx context.Context, properties map[string]string) {
    carrier := &PulsarPropertiesCarrier{properties: properties}
    otel.GetTextMapPropagator().Inject(ctx, carrier)
}

// Extract trace context
func extractTraceContext(properties map[string]string) context.Context {
    carrier := &PulsarPropertiesCarrier{properties: properties}
    return otel.GetTextMapPropagator().Extract(context.Background(), carrier)
}
```

---

## 6. Go实现示例

### 6.1 Producer

```go
package main

import (
    "context"
    
    "github.com/apache/pulsar-client-go/pulsar"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

func ProduceWithTracing(
    ctx context.Context,
    producer pulsar.Producer,
    payload []byte,
) error {
    tracer := otel.Tracer("pulsar-producer")
    
    // 创建Producer Span
    ctx, span := tracer.Start(ctx, "pulsar.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("pulsar"),
            semconv.MessagingDestinationNameKey.String(producer.Topic()),
            semconv.MessagingOperationKey.String("publish"),
            attribute.Int("messaging.message.body.size", len(payload)),
        ),
    )
    defer span.End()
    
    // 解析Topic名称
    topicName := producer.Topic()
    span.SetAttributes(
        attribute.String("messaging.pulsar.topic", parseTopic(topicName)),
    )
    
    // 创建消息Properties
    properties := make(map[string]string)
    
    // 注入Trace Context
    injectTraceContext(ctx, properties)
    
    // 构建消息
    msg := &pulsar.ProducerMessage{
        Payload:    payload,
        Properties: properties,
    }
    
    // 发送消息
    msgID, err := producer.Send(ctx, msg)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "send failed")
        return err
    }
    
    // 记录消息ID
    span.SetAttributes(
        attribute.String("messaging.message.id", msgID.String()),
    )
    
    span.SetStatus(codes.Ok, "sent")
    return nil
}

// 异步发送
func ProduceAsyncWithTracing(
    ctx context.Context,
    producer pulsar.Producer,
    payload []byte,
) {
    tracer := otel.Tracer("pulsar-producer")
    
    ctx, span := tracer.Start(ctx, "pulsar.publish.async",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    
    properties := make(map[string]string)
    injectTraceContext(ctx, properties)
    
    msg := &pulsar.ProducerMessage{
        Payload:    payload,
        Properties: properties,
    }
    
    // 异步发送
    producer.SendAsync(ctx, msg, func(
        id pulsar.MessageID,
        message *pulsar.ProducerMessage,
        err error,
    ) {
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "send failed")
        } else {
            span.SetAttributes(
                attribute.String("messaging.message.id", id.String()),
            )
            span.SetStatus(codes.Ok, "sent")
        }
        span.End()
    })
}
```

### 6.2 Consumer

```go
func ConsumeWithTracing(
    ctx context.Context,
    consumer pulsar.Consumer,
    handler func(context.Context, pulsar.Message) error,
) error {
    tracer := otel.Tracer("pulsar-consumer")
    
    for {
        // 接收消息
        msg, err := consumer.Receive(ctx)
        if err != nil {
            return err
        }
        
        // 提取Trace Context
        msgCtx := extractTraceContext(msg.Properties())
        
        // 创建Consumer Span
        msgCtx, span := tracer.Start(msgCtx, "pulsar.receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("pulsar"),
                semconv.MessagingDestinationNameKey.String(msg.Topic()),
                semconv.MessagingOperationKey.String("receive"),
                attribute.String("messaging.message.id", msg.ID().String()),
                attribute.String("messaging.pulsar.subscription.name", 
                    consumer.Subscription()),
                attribute.Int("messaging.message.body.size", 
                    len(msg.Payload())),
                attribute.Int("messaging.pulsar.message.redelivery_count", 
                    int(msg.RedeliveryCount())),
                attribute.Int64("messaging.pulsar.message.publish_time", 
                    msg.PublishTime().UnixMilli()),
            ),
        )
        
        // 处理消息
        err = handler(msgCtx, msg)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            
            // Nack消息
            consumer.Nack(msg)
        } else {
            span.SetStatus(codes.Ok, "processed")
            
            // Ack消息
            consumer.Ack(msg)
        }
        
        span.End()
    }
}

// 批量接收
func ConsumeBatchWithTracing(
    ctx context.Context,
    consumer pulsar.Consumer,
    handler func(context.Context, []pulsar.Message) error,
) error {
    tracer := otel.Tracer("pulsar-consumer")
    
    for {
        // 批量接收
        messages, err := consumer.ReceiveWithTimeout(ctx, 5*time.Second)
        if err != nil {
            continue
        }
        
        // 创建batch span
        ctx, span := tracer.Start(ctx, "pulsar.receive.batch",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("pulsar"),
                attribute.Int("messaging.batch.message_count", 
                    len(messages)),
            ),
        )
        
        // 处理消息
        err = handler(ctx, messages)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            
            // Nack所有消息
            for _, msg := range messages {
                consumer.Nack(msg)
            }
        } else {
            span.SetStatus(codes.Ok, "processed")
            
            // Ack所有消息
            for _, msg := range messages {
                consumer.Ack(msg)
            }
        }
        
        span.End()
    }
}
```

### 6.3 Reader模式

```go
// Reader模式 (类似Kafka Consumer手动管理offset)
func ReadWithTracing(
    ctx context.Context,
    reader pulsar.Reader,
    handler func(context.Context, pulsar.Message) error,
) error {
    tracer := otel.Tracer("pulsar-reader")
    
    for reader.HasNext() {
        // 读取消息
        msg, err := reader.Next(ctx)
        if err != nil {
            return err
        }
        
        // 提取trace context
        msgCtx := extractTraceContext(msg.Properties())
        
        // 创建span
        msgCtx, span := tracer.Start(msgCtx, "pulsar.read",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("pulsar"),
                semconv.MessagingDestinationNameKey.String(msg.Topic()),
                semconv.MessagingOperationKey.String("read"),
                attribute.String("messaging.message.id", msg.ID().String()),
            ),
        )
        
        // 处理消息
        err = handler(msgCtx, msg)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
        } else {
            span.SetStatus(codes.Ok, "processed")
        }
        
        span.End()
    }
    
    return nil
}
```

---

## 7. Java实现示例

### 7.1 Producer

```java
import org.apache.pulsar.client.api.*;
import io.opentelemetry.api.trace.*;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.propagation.TextMapSetter;

public class PulsarProducerTracing {
    
    private static final Tracer tracer = 
        openTelemetry.getTracer("pulsar-producer");
    
    public void produceWithTracing(
        Producer<byte[]> producer,
        byte[] payload
    ) throws PulsarClientException {
        
        // 创建span
        Span span = tracer.spanBuilder("pulsar.publish")
            .setSpanKind(SpanKind.PRODUCER)
            .setAttribute("messaging.system", "pulsar")
            .setAttribute("messaging.destination.name", producer.getTopic())
            .setAttribute("messaging.operation", "publish")
            .setAttribute("messaging.message.body.size", payload.length)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 创建消息
            TypedMessageBuilder<byte[]> msgBuilder = producer.newMessage()
                .value(payload);
            
            // 注入trace context
            Context.current().propagate(new TextMapSetter<TypedMessageBuilder<?>>() {
                @Override
                public void set(TypedMessageBuilder<?> carrier, String key, String value) {
                    carrier.property(key, value);
                }
            });
            
            // 发送消息
            MessageId msgId = msgBuilder.send();
            
            // 记录消息ID
            span.setAttribute("messaging.message.id", msgId.toString());
            span.setStatus(StatusCode.OK);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "send failed");
            throw e;
        } finally {
            span.end();
        }
    }
    
    // 异步发送
    public void produceAsyncWithTracing(
        Producer<byte[]> producer,
        byte[] payload
    ) {
        Span span = tracer.spanBuilder("pulsar.publish.async")
            .setSpanKind(SpanKind.PRODUCER)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            TypedMessageBuilder<byte[]> msgBuilder = producer.newMessage()
                .value(payload);
            
            // 注入trace context到properties
            injectContext(Context.current(), msgBuilder);
            
            // 异步发送
            msgBuilder.sendAsync()
                .thenAccept(msgId -> {
                    span.setAttribute("messaging.message.id", msgId.toString());
                    span.setStatus(StatusCode.OK);
                    span.end();
                })
                .exceptionally(ex -> {
                    span.recordException(ex);
                    span.setStatus(StatusCode.ERROR);
                    span.end();
                    return null;
                });
        }
    }
}
```

### 7.2 Consumer

```java
public class PulsarConsumerTracing {
    
    private static final Tracer tracer = 
        openTelemetry.getTracer("pulsar-consumer");
    
    public void consumeWithTracing(
        Consumer<byte[]> consumer,
        MessageHandler handler
    ) throws PulsarClientException {
        
        while (true) {
            // 接收消息
            Message<byte[]> msg = consumer.receive();
            
            // 提取trace context
            Context extractedContext = extractContext(msg.getProperties());
            
            // 创建span
            Span span = tracer.spanBuilder("pulsar.receive")
                .setParent(extractedContext)
                .setSpanKind(SpanKind.CONSUMER)
                .setAttribute("messaging.system", "pulsar")
                .setAttribute("messaging.destination.name", msg.getTopicName())
                .setAttribute("messaging.operation", "receive")
                .setAttribute("messaging.message.id", msg.getMessageId().toString())
                .setAttribute("messaging.pulsar.subscription.name", 
                    consumer.getSubscription())
                .setAttribute("messaging.message.body.size", msg.getData().length)
                .setAttribute("messaging.pulsar.message.redelivery_count", 
                    msg.getRedeliveryCount())
                .startSpan();
            
            try (Scope scope = span.makeCurrent()) {
                // 处理消息
                handler.handle(msg);
                
                // ACK
                consumer.acknowledge(msg);
                span.setStatus(StatusCode.OK);
                
            } catch (Exception e) {
                span.recordException(e);
                span.setStatus(StatusCode.ERROR, "handler failed");
                
                // Negative ACK
                consumer.negativeAcknowledge(msg);
                
            } finally {
                span.end();
            }
        }
    }
}
```

---

## 8. Python实现示例

### 8.1 Producer

```python
import pulsar
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

def produce_with_tracing(
    producer: pulsar.Producer,
    payload: bytes
):
    """发布消息with tracing"""
    with tracer.start_as_current_span(
        "pulsar.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "pulsar",
            SpanAttributes.MESSAGING_DESTINATION_NAME: producer.topic(),
            SpanAttributes.MESSAGING_OPERATION: "publish",
            SpanAttributes.MESSAGING_MESSAGE_BODY_SIZE: len(payload),
        }
    ) as span:
        # 注入trace context
        properties = {}
        propagate.inject(properties)
        
        try:
            # 发送消息
            msg_id = producer.send(
                payload,
                properties=properties
            )
            
            # 记录消息ID
            span.set_attribute("messaging.message.id", str(msg_id))
            span.set_status(Status(StatusCode.OK))
            
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def produce_async_with_tracing(
    producer: pulsar.Producer,
    payload: bytes
):
    """异步发布消息with tracing"""
    span = tracer.start_span(
        "pulsar.publish.async",
        kind=SpanKind.PRODUCER
    )
    
    properties = {}
    propagate.inject(properties)
    
    def callback(res, msg_id):
        if res == pulsar.Result.Ok:
            span.set_attribute("messaging.message.id", str(msg_id))
            span.set_status(Status(StatusCode.OK))
        else:
            span.set_status(Status(StatusCode.ERROR))
        span.end()
    
    producer.send_async(
        payload,
        callback=callback,
        properties=properties
    )
```

### 8.2 Consumer

```python
def consume_with_tracing(
    consumer: pulsar.Consumer,
    handler
):
    """消费消息with tracing"""
    while True:
        # 接收消息
        msg = consumer.receive()
        
        # 提取trace context
        properties = msg.properties() or {}
        ctx = propagate.extract(properties)
        
        # 创建span
        with tracer.start_as_current_span(
            "pulsar.receive",
            context=ctx,
            kind=SpanKind.CONSUMER,
            attributes={
                SpanAttributes.MESSAGING_SYSTEM: "pulsar",
                SpanAttributes.MESSAGING_DESTINATION_NAME: msg.topic_name(),
                SpanAttributes.MESSAGING_OPERATION: "receive",
                "messaging.message.id": str(msg.message_id()),
                "messaging.pulsar.subscription.name": consumer.subscription_name(),
                "messaging.message.body.size": len(msg.data()),
                "messaging.pulsar.message.redelivery_count": msg.redelivery_count(),
            }
        ) as span:
            try:
                # 处理消息
                handler(msg.data())
                
                # ACK
                consumer.acknowledge(msg)
                span.set_status(Status(StatusCode.OK))
                
            except Exception as e:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR))
                
                # Negative ACK
                consumer.negative_acknowledge(msg)
```

---

## 9. Metrics定义

### 9.1 Producer Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.pulsar.producer.send.duration` | Histogram | ms | 发送延迟 |
| `messaging.pulsar.producer.send.messages` | Counter | messages | 发送消息数 |
| `messaging.pulsar.producer.send.bytes` | Counter | bytes | 发送字节数 |
| `messaging.pulsar.producer.send.errors` | Counter | errors | 发送错误数 |
| `messaging.pulsar.producer.pending.messages` | Gauge | messages | 待发送消息数 |
| `messaging.pulsar.producer.pending.bytes` | Gauge | bytes | 待发送字节数 |

### 9.2 Consumer Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.pulsar.consumer.receive.duration` | Histogram | ms | 接收延迟 |
| `messaging.pulsar.consumer.receive.messages` | Counter | messages | 接收消息数 |
| `messaging.pulsar.consumer.receive.bytes` | Counter | bytes | 接收字节数 |
| `messaging.pulsar.consumer.ack.messages` | Counter | messages | ACK消息数 |
| `messaging.pulsar.consumer.nack.messages` | Counter | messages | NACK消息数 |
| `messaging.pulsar.consumer.available.permits` | Gauge | permits | 可用许可数 |

### 9.3 Topic Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.pulsar.topic.producers` | Gauge | producers | Producer数量 |
| `messaging.pulsar.topic.subscriptions` | Gauge | subscriptions | 订阅数量 |
| `messaging.pulsar.topic.storage.size` | Gauge | bytes | 存储大小 |
| `messaging.pulsar.topic.backlog.size` | Gauge | messages | Backlog大小 |
| `messaging.pulsar.topic.throughput.in` | Gauge | bytes/s | 入站吞吐量 |
| `messaging.pulsar.topic.throughput.out` | Gauge | bytes/s | 出站吞吐量 |

---

## 10. 高级特性

### 10.1 多租户

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar多租户模型:

Tenant (租户)
  └─ Namespace (命名空间)
      └─ Topic (主题)

完整Topic名称:
persistent://tenant/namespace/topic
non-persistent://tenant/namespace/topic

示例:
persistent://my-company/marketing/orders
          │           │          │
       Tenant    Namespace   Topic

租户隔离:
✅ 独立配额
✅ 独立权限
✅ 独立存储
✅ 独立策略

追踪属性:
span.SetAttributes(
    attribute.String("messaging.pulsar.tenant", "my-company"),
    attribute.String("messaging.pulsar.namespace", "marketing"),
    attribute.String("messaging.pulsar.topic", "orders"),
)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.2 Geo-Replication

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar Geo-Replication (跨地域复制):

┌─────────────┐     Replication     ┌─────────────┐
│  Cluster A  │ ◄─────────────────► │  Cluster B  │
│   (US-East) │                     │   (EU-West) │
└─────────────┘                     └─────────────┘
       │                                   │
       │ Replication                       │ Replication
       ▼                                   ▼
┌─────────────┐                     ┌─────────────┐
│  Cluster C  │                     │  Cluster D  │
│ (Asia-Pac)  │                     │  (US-West)  │
└─────────────┘                     └─────────────┘

配置:
pulsar-admin namespaces set-clusters \
  --clusters us-east,eu-west,asia-pac \
  my-tenant/my-namespace

追踪属性:
span.SetAttributes(
    attribute.String("messaging.pulsar.cluster", "us-east"),
    attribute.StringSlice("messaging.pulsar.replication.clusters", 
        []string{"us-east", "eu-west", "asia-pac"}),
)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.3 分层存储

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pulsar分层存储 (Tiered Storage):

热数据 (BookKeeper)
  │
  │ 自动Offload
  ▼
冷数据 (S3/HDFS/GCS/Azure Blob)

配置:
pulsar-admin namespaces set-offload-threshold \
  --size 10G \
  my-tenant/my-namespace

优点:
✅ 无限存储容量
✅ 成本优化 (冷数据便宜)
✅ 自动管理
✅ 透明读取

追踪属性:
span.SetAttributes(
    attribute.String("messaging.pulsar.tiered_storage.enabled", "true"),
    attribute.String("messaging.pulsar.tiered_storage.type", "S3"),
)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 11. 最佳实践

### 11.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

性能优化建议:

1. 批处理 ⭐⭐⭐⭐⭐
   producer := client.CreateProducer(pulsar.ProducerOptions{
       Topic:                   "my-topic",
       BatchingMaxMessages:     1000,
       BatchingMaxPublishDelay: 10 * time.Millisecond,
   })

2. 异步发送 ⭐⭐⭐⭐⭐
   producer.SendAsync()

3. 分区Topic ⭐⭐⭐⭐
   persistent://tenant/namespace/my-topic-partition-0
   persistent://tenant/namespace/my-topic-partition-1
   ...

4. 连接池 ⭐⭐⭐⭐
   复用Client和Producer

5. Prefetch设置 ⭐⭐⭐⭐
   consumer := client.Subscribe(pulsar.ConsumerOptions{
       ReceiverQueueSize: 1000, // prefetch
   })

6. Key_Shared订阅 ⭐⭐⭐⭐
   适用于需要按Key顺序的场景

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 11.2 可靠性保证

```go
// 可靠性配置
producer := client.CreateProducer(pulsar.ProducerOptions{
    Topic:           "my-topic",
    // 发送超时
    SendTimeout:     10 * time.Second,
    // 阻塞队列满
    BlockIfQueueFull: true,
    // 压缩
    CompressionType: pulsar.LZ4,
})

consumer := client.Subscribe(pulsar.ConsumerOptions{
    Topic:            "my-topic",
    SubscriptionName: "my-sub",
    // 订阅类型
    Type:             pulsar.Exclusive,
    // ACK超时
    AckTimeout:       30 * time.Second,
    // 负ACK重投递延迟
    NackRedeliveryDelay: 1 * time.Minute,
    // DLQ
    DLQ: &pulsar.DLQPolicy{
        MaxDeliveries:    10,
        DeadLetterTopic:  "my-topic-dlq",
    },
})
```

### 11.3 监控建议

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键监控指标:

1. Producer
   - 发送延迟
   - 发送速率
   - 失败率
   - 待发送队列大小

2. Consumer
   - 接收延迟
   - 消费速率
   - ACK延迟
   - Backlog大小

3. Topic
   - 存储大小
   - 吞吐量
   - 分区数
   - 订阅数

4. 集群
   - Broker CPU/内存
   - BookKeeper磁盘
   - 网络带宽
   - 连接数

告警规则:
- Backlog > 100,000
- 消费延迟 > 60秒
- 失败率 > 1%
- 磁盘使用率 > 80%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**Pulsar版本**: v3.0+  
**适用场景**: 大规模消息系统、多租户平台、云原生架构

**关键特性**:

- ✅ 原生Message Properties支持
- ✅ 多租户隔离
- ✅ Geo-Replication追踪
- ✅ 分层存储
- ✅ 4种订阅模式
- ✅ Go/Java/Python完整示例

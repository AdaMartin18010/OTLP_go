# Kafka 语义约定详解

> **规范版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [Kafka 语义约定详解](#kafka-语义约定详解)
  - [目录](#目录)
  - [1. Kafka概述](#1-kafka概述)
    - [1.1 Kafka在可观测性中的重要性](#11-kafka在可观测性中的重要性)
    - [1.2 Kafka追踪模型](#12-kafka追踪模型)
  - [2. Kafka通用属性](#2-kafka通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Producer (生产者) 属性](#3-producer-生产者-属性)
    - [3.1 Producer Span属性](#31-producer-span属性)
    - [3.2 Producer实现示例](#32-producer实现示例)
  - [4. Consumer (消费者) 属性](#4-consumer-消费者-属性)
    - [4.1 Consumer Span属性](#41-consumer-span属性)
    - [4.2 Consumer实现示例](#42-consumer实现示例)
  - [5. SpanKind约定](#5-spankind约定)
  - [6. TraceContext传播](#6-tracecontext传播)
    - [6.1 消息Header传播](#61-消息header传播)
    - [6.2 传播实现](#62-传播实现)
  - [7. 批量操作](#7-批量操作)
  - [8. 错误处理](#8-错误处理)
  - [9. 性能指标](#9-性能指标)
  - [10. 完整实现示例](#10-完整实现示例)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 参考资源](#12-参考资源)

---

## 1. Kafka概述

### 1.1 Kafka在可观测性中的重要性

**为什么追踪Kafka很重要**：

```text
1. 异步解耦
   - 生产者和消费者独立
   - 难以追踪端到端流程
   - TraceContext打通链路

2. 性能瓶颈
   - 生产延迟
   - 消费延迟
   - 积压监控

3. 数据一致性
   - 消息丢失
   - 重复消费
   - 顺序问题

4. 故障定位
   - 哪个消费者慢
   - 哪个分区有问题
   - 哪个Topic积压

示例场景:
订单服务 → Kafka → 库存服务 → Kafka → 物流服务
完整TraceID跨越3个服务和2个Kafka Topic
```

### 1.2 Kafka追踪模型

**Span关系**：

```text
┌────────────────────────────────────────────────────────┐
│                   订单服务 Trace                        │
│                                                        │
│  ┌─────────────────┐                                   │
│  │  POST /orders   │  (SpanKind: SERVER)               │
│  │  TraceID: abc   │                                   │
│  └────────┬────────┘                                   │
│           │                                            │
│           ▼                                            │
│  ┌─────────────────┐                                   │
│  │  Kafka Produce  │  (SpanKind: PRODUCER)             │
│  │  Topic: orders  │                                   │
│  │  TraceID: abc   │  ← 注入到消息Header                │
│  └─────────────────┘                                   │
└────────────────────────────────────────────────────────┘
                       │
                       │ Kafka Message (携带TraceContext)
                       │
                       ▼
┌────────────────────────────────────────────────────────┐
│                   库存服务 Trace                        │
│                                                        │
│  ┌─────────────────┐                                   │
│  │  Kafka Consume  │  (SpanKind: CONSUMER)             │
│  │  Topic: orders  │                                   │
│  │  TraceID: abc   │  ← 从消息Header提取                │
│  └────────┬────────┘                                   │
│           │                                            │
│           ▼                                            │
│  ┌─────────────────┐                                   │
│  │ Process Order   │  (SpanKind: INTERNAL)             │
│  │  TraceID: abc   │                                   │
│  └─────────────────┘                                   │
└────────────────────────────────────────────────────────┘

关键:
- Producer和Consumer的Span共享同一个TraceID
- 通过消息Header传播TraceContext
- 实现端到端追踪
```

---

## 2. Kafka通用属性

### 2.1 必需属性

```text
messaging.system: "kafka"
  类型: string
  值: 固定为 "kafka"
  示例: "kafka"

messaging.destination.name: Topic名称
  类型: string
  值: Kafka Topic名称
  示例: "orders", "user-events"

messaging.operation: 操作类型
  类型: string
  值: "publish" | "receive" | "process"
  示例: 
    - "publish": Producer发送
    - "receive": Consumer接收
    - "process": Consumer处理
```

### 2.2 推荐属性

```text
messaging.kafka.destination.partition: 分区号
  类型: int
  示例: 0, 1, 2

messaging.kafka.message.offset: 消息偏移量
  类型: int
  示例: 12345

messaging.kafka.message.key: 消息Key
  类型: string
  示例: "user-123"

messaging.kafka.consumer.group: 消费者组
  类型: string
  示例: "order-processor-group"

messaging.message.id: 消息ID
  类型: string
  示例: "msg-abc-123"

messaging.message.payload_size_bytes: 消息大小
  类型: int
  单位: 字节
  示例: 1024

messaging.batch.message_count: 批次消息数量
  类型: int
  示例: 100

network.peer.address: Kafka集群地址
  类型: string
  示例: "kafka.example.com"

network.peer.port: Kafka端口
  类型: int
  示例: 9092
```

---

## 3. Producer (生产者) 属性

### 3.1 Producer Span属性

**完整属性列表**：

```text
必需属性:
- messaging.system: "kafka"
- messaging.destination.name: "orders"
- messaging.operation: "publish"

推荐属性:
- messaging.kafka.destination.partition: 2
- messaging.kafka.message.key: "order-12345"
- messaging.message.payload_size_bytes: 512
- network.peer.address: "kafka1.example.com"
- network.peer.port: 9092

Span属性:
- span.kind: PRODUCER
- span.name: "{topic} publish"

示例完整Span:
{
  "span_id": "def456",
  "trace_id": "abc123",
  "parent_span_id": "789xyz",
  "name": "orders publish",
  "kind": "PRODUCER",
  "attributes": {
    "messaging.system": "kafka",
    "messaging.destination.name": "orders",
    "messaging.operation": "publish",
    "messaging.kafka.destination.partition": 2,
    "messaging.kafka.message.key": "order-12345",
    "messaging.kafka.message.offset": 98765,
    "messaging.message.payload_size_bytes": 512,
    "network.peer.address": "kafka1.example.com",
    "network.peer.port": 9092
  }
}
```

### 3.2 Producer实现示例

**Go Producer**：

```go
package main

import (
    "context"
    "github.com/segmentio/kafka-go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

type KafkaProducer struct {
    writer *kafka.Writer
    tracer trace.Tracer
}

func NewKafkaProducer(brokers []string, topic string) *KafkaProducer {
    return &KafkaProducer{
        writer: &kafka.Writer{
            Addr:     kafka.TCP(brokers...),
            Topic:    topic,
            Balancer: &kafka.LeastBytes{},
        },
        tracer: otel.Tracer("kafka-producer"),
    }
}

func (p *KafkaProducer) Publish(ctx context.Context, key, value []byte) error {
    // 创建Producer Span
    ctx, span := p.tracer.Start(ctx, p.writer.Topic+" publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystem("kafka"),
            semconv.MessagingDestinationName(p.writer.Topic),
            semconv.MessagingOperationPublish,
        ),
    )
    defer span.End()
    
    // 创建消息
    msg := kafka.Message{
        Key:   key,
        Value: value,
        Headers: []kafka.Header{},
    }
    
    // 注入TraceContext到消息Header
    propagator := otel.GetTextMapPropagator()
    carrier := NewKafkaHeaderCarrier(&msg.Headers)
    propagator.Inject(ctx, carrier)
    
    // 发送消息
    err := p.writer.WriteMessages(ctx, msg)
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to publish message")
        return err
    }
    
    // 记录额外属性
    span.SetAttributes(
        attribute.String("messaging.kafka.message.key", string(key)),
        attribute.Int("messaging.message.payload_size_bytes", len(value)),
    )
    
    span.SetStatus(codes.Ok, "Message published successfully")
    return nil
}

// KafkaHeaderCarrier实现TextMapCarrier接口
type KafkaHeaderCarrier struct {
    headers *[]kafka.Header
}

func NewKafkaHeaderCarrier(headers *[]kafka.Header) *KafkaHeaderCarrier {
    return &KafkaHeaderCarrier{headers: headers}
}

func (c *KafkaHeaderCarrier) Get(key string) string {
    for _, h := range *c.headers {
        if h.Key == key {
            return string(h.Value)
        }
    }
    return ""
}

func (c *KafkaHeaderCarrier) Set(key, value string) {
    // 删除已存在的key
    for i, h := range *c.headers {
        if h.Key == key {
            *c.headers = append((*c.headers)[:i], (*c.headers)[i+1:]...)
            break
        }
    }
    // 添加新header
    *c.headers = append(*c.headers, kafka.Header{
        Key:   key,
        Value: []byte(value),
    })
}

func (c *KafkaHeaderCarrier) Keys() []string {
    keys := make([]string, len(*c.headers))
    for i, h := range *c.headers {
        keys[i] = h.Key
    }
    return keys
}

// 使用示例
func main() {
    producer := NewKafkaProducer(
        []string{"localhost:9092"},
        "orders",
    )
    
    ctx := context.Background()
    err := producer.Publish(ctx,
        []byte("order-12345"),
        []byte(`{"order_id": "12345", "amount": 99.99}`),
    )
    
    if err != nil {
        panic(err)
    }
}
```

**Java Producer**：

```java
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.propagation.TextMapSetter;
import org.apache.kafka.clients.producer.KafkaProducer;
import org.apache.kafka.clients.producer.ProducerRecord;
import org.apache.kafka.common.header.Headers;

public class TracedKafkaProducer {
    private final KafkaProducer<String, String> producer;
    private final Tracer tracer;
    private final String topic;
    
    public TracedKafkaProducer(KafkaProducer<String, String> producer, 
                               Tracer tracer, 
                               String topic) {
        this.producer = producer;
        this.tracer = tracer;
        this.topic = topic;
    }
    
    public void publish(String key, String value) {
        // 创建Producer Span
        Span span = tracer.spanBuilder(topic + " publish")
            .setSpanKind(SpanKind.PRODUCER)
            .setAttribute("messaging.system", "kafka")
            .setAttribute("messaging.destination.name", topic)
            .setAttribute("messaging.operation", "publish")
            .startSpan();
        
        try (var scope = span.makeCurrent()) {
            // 创建消息
            ProducerRecord<String, String> record = 
                new ProducerRecord<>(topic, key, value);
            
            // 注入TraceContext到Header
            TextMapSetter<Headers> setter = (carrier, k, v) -> 
                carrier.add(k, v.getBytes());
            propagator.inject(Context.current(), record.headers(), setter);
            
            // 发送消息
            producer.send(record, (metadata, exception) -> {
                if (exception != null) {
                    span.recordException(exception);
                    span.setStatus(StatusCode.ERROR);
                } else {
                    span.setAttribute("messaging.kafka.destination.partition", 
                                    metadata.partition());
                    span.setAttribute("messaging.kafka.message.offset", 
                                    metadata.offset());
                    span.setStatus(StatusCode.OK);
                }
                span.end();
            });
        }
    }
}
```

---

## 4. Consumer (消费者) 属性

### 4.1 Consumer Span属性

**完整属性列表**：

```text
必需属性:
- messaging.system: "kafka"
- messaging.destination.name: "orders"
- messaging.operation: "receive" 或 "process"

推荐属性:
- messaging.kafka.destination.partition: 2
- messaging.kafka.message.offset: 98765
- messaging.kafka.message.key: "order-12345"
- messaging.kafka.consumer.group: "order-processor"
- messaging.message.payload_size_bytes: 512

Span属性:
- span.kind: CONSUMER
- span.name: "{topic} receive" 或 "{topic} process"

两种Consumer Span模式:
1. receive: 接收消息
   span.name: "orders receive"
   span.kind: CONSUMER
   
2. process: 处理消息
   span.name: "orders process"
   span.kind: CONSUMER
   parent: receive span
```

### 4.2 Consumer实现示例

**Go Consumer**：

```go
package main

import (
    "context"
    "github.com/segmentio/kafka-go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

type KafkaConsumer struct {
    reader *kafka.Reader
    tracer trace.Tracer
}

func NewKafkaConsumer(brokers []string, topic, groupID string) *KafkaConsumer {
    return &KafkaConsumer{
        reader: kafka.NewReader(kafka.ReaderConfig{
            Brokers:  brokers,
            Topic:    topic,
            GroupID:  groupID,
            MinBytes: 10e3, // 10KB
            MaxBytes: 10e6, // 10MB
        }),
        tracer: otel.Tracer("kafka-consumer"),
    }
}

func (c *KafkaConsumer) Consume(ctx context.Context) error {
    for {
        // 读取消息
        msg, err := c.reader.ReadMessage(ctx)
        if err != nil {
            return err
        }
        
        // 从消息Header提取TraceContext
        propagator := otel.GetTextMapPropagator()
        carrier := NewKafkaHeaderCarrier(&msg.Headers)
        ctx = propagator.Extract(ctx, carrier)
        
        // 创建Consumer receive Span
        ctx, receiveSpan := c.tracer.Start(ctx, 
            c.reader.Config().Topic+" receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystem("kafka"),
                semconv.MessagingDestinationName(c.reader.Config().Topic),
                semconv.MessagingOperationReceive,
                attribute.Int("messaging.kafka.destination.partition", msg.Partition),
                attribute.Int64("messaging.kafka.message.offset", msg.Offset),
                attribute.String("messaging.kafka.message.key", string(msg.Key)),
                attribute.String("messaging.kafka.consumer.group", c.reader.Config().GroupID),
                attribute.Int("messaging.message.payload_size_bytes", len(msg.Value)),
            ),
        )
        
        // 处理消息
        err = c.processMessage(ctx, msg)
        
        if err != nil {
            receiveSpan.RecordError(err)
            receiveSpan.SetStatus(codes.Error, "Failed to process message")
        } else {
            receiveSpan.SetStatus(codes.Ok, "Message processed successfully")
        }
        
        receiveSpan.End()
    }
}

func (c *KafkaConsumer) processMessage(ctx context.Context, msg kafka.Message) error {
    // 创建process Span (可选，用于细粒度追踪)
    ctx, processSpan := c.tracer.Start(ctx,
        c.reader.Config().Topic+" process",
        trace.WithSpanKind(trace.SpanKindInternal),
    )
    defer processSpan.End()
    
    // 业务逻辑处理
    // ...
    
    return nil
}

// 使用示例
func main() {
    consumer := NewKafkaConsumer(
        []string{"localhost:9092"},
        "orders",
        "order-processor-group",
    )
    
    ctx := context.Background()
    if err := consumer.Consume(ctx); err != nil {
        panic(err)
    }
}
```

**Python Consumer**：

```python
from opentelemetry import trace
from opentelemetry.propagate import extract
from opentelemetry.semconv.trace import SpanAttributes
from kafka import KafkaConsumer

tracer = trace.get_tracer(__name__)

def consume_messages():
    consumer = KafkaConsumer(
        'orders',
        group_id='order-processor',
        bootstrap_servers=['localhost:9092']
    )
    
    for message in consumer:
        # 从Header提取TraceContext
        headers = {k: v.decode() for k, v in message.headers}
        ctx = extract(headers)
        
        # 创建Consumer Span
        with tracer.start_as_current_span(
            f"{message.topic} receive",
            context=ctx,
            kind=trace.SpanKind.CONSUMER,
            attributes={
                SpanAttributes.MESSAGING_SYSTEM: "kafka",
                SpanAttributes.MESSAGING_DESTINATION_NAME: message.topic,
                SpanAttributes.MESSAGING_OPERATION: "receive",
                "messaging.kafka.destination.partition": message.partition,
                "messaging.kafka.message.offset": message.offset,
                "messaging.kafka.message.key": message.key.decode(),
                "messaging.kafka.consumer.group": "order-processor",
                "messaging.message.payload_size_bytes": len(message.value),
            }
        ) as span:
            # 处理消息
            process_message(message.value)
```

---

## 5. SpanKind约定

```text
Producer:
- SpanKind: PRODUCER
- 操作: 发送消息到Kafka
- Span Name: "{topic} publish"

Consumer (两种模式):
1. 接收模式:
   - SpanKind: CONSUMER
   - 操作: 从Kafka接收消息
   - Span Name: "{topic} receive"

2. 处理模式:
   - SpanKind: CONSUMER (或INTERNAL)
   - 操作: 处理消息业务逻辑
   - Span Name: "{topic} process"
   - Parent: receive span

推荐: 同时创建receive和process两个Span
- receive: 记录接收延迟
- process: 记录处理延迟
```

---

## 6. TraceContext传播

### 6.1 消息Header传播

**W3C Trace Context格式**：

```text
Kafka消息Header:
┌────────────────────────────────────────────┐
│ Key: traceparent                           │
│ Value: 00-abc123...-def456...-01          │
├────────────────────────────────────────────┤
│ Key: tracestate                            │
│ Value: vendor1=value1,vendor2=value2      │
└────────────────────────────────────────────┘

traceparent格式:
00-{trace-id}-{span-id}-{trace-flags}

00: 版本
abc123...: TraceID (32字符十六进制)
def456...: SpanID (16字符十六进制)
01: Flags (采样标志)
```

### 6.2 传播实现

**完整传播流程**：

```go
// Producer端: 注入
func injectTraceContext(ctx context.Context, msg *kafka.Message) {
    propagator := otel.GetTextMapPropagator()
    carrier := NewKafkaHeaderCarrier(&msg.Headers)
    propagator.Inject(ctx, carrier)
}

// Consumer端: 提取
func extractTraceContext(msg kafka.Message) context.Context {
    propagator := otel.GetTextMapPropagator()
    carrier := NewKafkaHeaderCarrier(&msg.Headers)
    return propagator.Extract(context.Background(), carrier)
}

// 端到端示例
// Producer
ctx, span := tracer.Start(context.Background(), "orders publish")
msg := kafka.Message{Value: []byte("data")}
injectTraceContext(ctx, &msg)  // TraceContext注入到Header
writer.WriteMessages(ctx, msg)
span.End()

// Consumer
msg := reader.ReadMessage(context.Background())
ctx := extractTraceContext(msg)  // 从Header提取TraceContext
ctx, span := tracer.Start(ctx, "orders receive")  // 继承相同TraceID
// 处理消息...
span.End()
```

---

## 7. 批量操作

**批量发送**：

```go
func (p *KafkaProducer) PublishBatch(ctx context.Context, messages []Message) error {
    ctx, span := p.tracer.Start(ctx, p.writer.Topic+" publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystem("kafka"),
            semconv.MessagingDestinationName(p.writer.Topic),
            semconv.MessagingOperationPublish,
            attribute.Int("messaging.batch.message_count", len(messages)),
        ),
    )
    defer span.End()
    
    kafkaMessages := make([]kafka.Message, len(messages))
    for i, msg := range messages {
        kafkaMessages[i] = kafka.Message{
            Key:   msg.Key,
            Value: msg.Value,
        }
        // 每条消息注入TraceContext
        propagator := otel.GetTextMapPropagator()
        carrier := NewKafkaHeaderCarrier(&kafkaMessages[i].Headers)
        propagator.Inject(ctx, carrier)
    }
    
    err := p.writer.WriteMessages(ctx, kafkaMessages...)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to publish batch")
        return err
    }
    
    span.SetStatus(codes.Ok, "Batch published successfully")
    return nil
}
```

---

## 8. 错误处理

```go
// Producer错误
if err != nil {
    span.RecordError(err)
    span.SetAttributes(
        attribute.String("error.type", "ProducerError"),
        attribute.String("error.message", err.Error()),
    )
    span.SetStatus(codes.Error, "Failed to publish message")
}

// Consumer错误
if err != nil {
    span.RecordError(err)
    span.SetAttributes(
        attribute.String("error.type", "ProcessingError"),
        attribute.String("error.message", err.Error()),
        attribute.Bool("messaging.message.redelivered", true),
    )
    span.SetStatus(codes.Error, "Failed to process message")
}

// 重试逻辑
span.AddEvent("Retrying message processing", trace.WithAttributes(
    attribute.Int("retry.attempt", 3),
))
```

---

## 9. 性能指标

**推荐Metrics**：

```text
1. kafka_producer_send_duration
   类型: Histogram
   单位: milliseconds
   标签: topic, partition

2. kafka_producer_message_size
   类型: Histogram
   单位: bytes
   标签: topic

3. kafka_consumer_lag
   类型: Gauge
   单位: messages
   标签: topic, partition, consumer_group

4. kafka_consumer_process_duration
   类型: Histogram
   单位: milliseconds
   标签: topic, consumer_group

5. kafka_message_errors
   类型: Counter
   标签: topic, error_type, operation
```

---

## 10. 完整实现示例

**端到端电商订单系统**：

```go
// 订单服务 (Producer)
func CreateOrder(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "POST /orders",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()
    
    // 创建订单
    order := Order{ID: "order-123", Amount: 99.99}
    orderJSON, _ := json.Marshal(order)
    
    // 发送到Kafka
    err := kafkaProducer.Publish(ctx, []byte(order.ID), orderJSON)
    if err != nil {
        span.RecordError(err)
        http.Error(w, "Failed to create order", 500)
        return
    }
    
    w.WriteHeader(201)
    json.NewEncoder(w).Encode(order)
}

// 库存服务 (Consumer)
func ConsumeOrders() {
    for {
        msg, _ := reader.ReadMessage(context.Background())
        
        // 提取TraceContext
        ctx := extractTraceContext(msg)
        ctx, span := tracer.Start(ctx, "orders receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
        )
        
        // 处理订单
        var order Order
        json.Unmarshal(msg.Value, &order)
        
        // 更新库存
        ctx, processSpan := tracer.Start(ctx, "Update inventory")
        updateInventory(order)
        processSpan.End()
        
        // 发送到下游Topic
        shipmentMsg, _ := json.Marshal(Shipment{OrderID: order.ID})
        kafkaProducer.Publish(ctx, []byte(order.ID), shipmentMsg)
        
        span.End()
    }
}
```

---

## 11. 最佳实践

```text
✅ DO (推荐)
1. 始终通过Header传播TraceContext
2. Producer使用SpanKind.PRODUCER
3. Consumer使用SpanKind.CONSUMER
4. 记录partition和offset
5. 批量操作记录message_count
6. 记录消息key (如果不敏感)
7. 监控consumer lag
8. 错误时记录error详情

❌ DON'T (避免)
1. 不要在消息body中传播TraceContext
2. 不要记录完整消息内容 (可能很大)
3. 不要忽略错误
4. 不要跳过receive span
5. 不要在SpanName中包含动态内容
6. 不要记录敏感数据 (PII)

性能优化:
- 使用批量发送减少Span数量
- 异步发送不阻塞主流程
- 合理设置采样率 (如10%)
- 控制属性数量 (< 20)

调试技巧:
- 使用logging exporter查看原始数据
- 检查消息Header确认TraceContext
- 监控Span数量和大小
- 验证TraceID连续性
```

---

## 12. 参考资源

- **Kafka语义约定**: <https://opentelemetry.io/docs/specs/semconv/messaging/kafka/>
- **消息传递**: <https://opentelemetry.io/docs/specs/semconv/messaging/>
- **Kafka文档**: <https://kafka.apache.org/documentation/>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [HTTP语义约定](../02_追踪属性/01_HTTP.md), [gRPC语义约定](../02_追踪属性/02_gRPC.md)

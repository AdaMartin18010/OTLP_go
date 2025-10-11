# 52. 事件驱动架构 - NATS 与 Kafka 集成指南

## 📚 目录

- [52. 事件驱动架构 - NATS 与 Kafka 集成指南](#52-事件驱动架构---nats-与-kafka-集成指南)
  - [📚 目录](#-目录)
  - [1. 事件驱动架构概述](#1-事件驱动架构概述)
    - [1.1 什么是事件驱动架构](#11-什么是事件驱动架构)
    - [1.2 NATS vs Kafka](#12-nats-vs-kafka)
    - [1.3 依赖版本](#13-依赖版本)
  - [2. NATS 完整集成](#2-nats-完整集成)
    - [2.1 基础连接](#21-基础连接)
    - [2.2 发布消息（带追踪）](#22-发布消息带追踪)
    - [2.3 订阅消息（带追踪）](#23-订阅消息带追踪)
    - [2.4 JetStream（持久化）](#24-jetstream持久化)
  - [3. Kafka 完整集成](#3-kafka-完整集成)
    - [3.1 Sarama 生产者](#31-sarama-生产者)
    - [3.2 Sarama 消费者](#32-sarama-消费者)
  - [4. OTLP 追踪集成](#4-otlp-追踪集成)
    - [4.1 统一事件包装器](#41-统一事件包装器)
  - [5. 事件模式](#5-事件模式)
    - [5.1 Event Sourcing（事件溯源）](#51-event-sourcing事件溯源)
    - [5.2 CQRS（命令查询职责分离）](#52-cqrs命令查询职责分离)
    - [5.3 Saga 模式](#53-saga-模式)
  - [6. 生产级实践](#6-生产级实践)
    - [6.1 重试机制](#61-重试机制)
    - [6.2 Dead Letter Queue](#62-dead-letter-queue)
  - [7. 性能优化](#7-性能优化)
    - [7.1 批量发送](#71-批量发送)
  - [8. 总结](#8-总结)
    - [核心优势](#核心优势)
    - [最佳实践](#最佳实践)
    - [相关文档](#相关文档)

---

## 1. 事件驱动架构概述

### 1.1 什么是事件驱动架构

事件驱动架构（EDA）是一种软件架构模式，系统通过事件的生产、检测、消费和响应来实现松耦合。

**核心概念**:

- ✅ **事件（Event）** - 系统状态的变化
- ✅ **生产者（Producer）** - 发布事件
- ✅ **消费者（Consumer）** - 订阅和处理事件
- ✅ **事件总线（Event Bus）** - 传输事件

### 1.2 NATS vs Kafka

| 特性 | NATS | Kafka |
|------|------|-------|
| 类型 | 消息队列 | 分布式日志 |
| 性能 | 极高（百万级 msg/s） | 高（十万级 msg/s） |
| 持久化 | 可选（JetStream） | 默认持久化 |
| 顺序保证 | Subject 级别 | Partition 级别 |
| 复杂度 | 低 | 中高 |
| 适用场景 | 实时通信、微服务 | 日志聚合、事件溯源 |

### 1.3 依赖版本

```go
// go.mod
module github.com/yourorg/event-driven-service

go 1.25.1

require (
    // NATS
    github.com/nats-io/nats.go v1.37.0
    
    // Kafka
    github.com/IBM/sarama v1.43.3
    github.com/twmb/franz-go v1.18.0
    
    // OTLP
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/otel/metric v1.32.0
    
    // 工具
    github.com/google/uuid v1.6.0
    google.golang.org/protobuf v1.36.0
)
```

---

## 2. NATS 完整集成

### 2.1 基础连接

```go
// internal/messaging/nats_client.go
package messaging

import (
    "context"
    "encoding/json"
    "fmt"
    "time"
    
    "github.com/nats-io/nats.go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// NATSClient NATS 客户端
type NATSClient struct {
    conn   *nats.Conn
    tracer trace.Tracer
}

// NewNATSClient 创建 NATS 客户端
func NewNATSClient(url string) (*NATSClient, error) {
    // 连接选项
    opts := []nats.Option{
        nats.Name("go-service"),
        nats.MaxReconnects(-1),
        nats.ReconnectWait(2 * time.Second),
        nats.DisconnectErrHandler(func(nc *nats.Conn, err error) {
            if err != nil {
                fmt.Printf("NATS disconnected: %v\n", err)
            }
        }),
        nats.ReconnectHandler(func(nc *nats.Conn) {
            fmt.Printf("NATS reconnected: %s\n", nc.ConnectedUrl())
        }),
    }
    
    conn, err := nats.Connect(url, opts...)
    if err != nil {
        return nil, fmt.Errorf("failed to connect to NATS: %w", err)
    }
    
    return &NATSClient{
        conn:   conn,
        tracer: otel.Tracer("nats-client"),
    }, nil
}

// Close 关闭连接
func (c *NATSClient) Close() error {
    c.conn.Close()
    return nil
}
```

### 2.2 发布消息（带追踪）

```go
// Event 事件
type Event struct {
    ID        string                 `json:"id"`
    Type      string                 `json:"type"`
    Source    string                 `json:"source"`
    Timestamp time.Time              `json:"timestamp"`
    Data      map[string]interface{} `json:"data"`
    TraceID   string                 `json:"trace_id,omitempty"`
    SpanID    string                 `json:"span_id,omitempty"`
}

// Publish 发布事件
func (c *NATSClient) Publish(ctx context.Context, subject string, event *Event) error {
    ctx, span := c.tracer.Start(ctx, "nats.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "nats"),
            attribute.String("messaging.destination", subject),
            attribute.String("messaging.message_id", event.ID),
        ),
    )
    defer span.End()
    
    // 注入追踪信息
    spanCtx := span.SpanContext()
    event.TraceID = spanCtx.TraceID().String()
    event.SpanID = spanCtx.SpanID().String()
    
    // 序列化
    data, err := json.Marshal(event)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to marshal event")
        return err
    }
    
    // 发布
    if err := c.conn.Publish(subject, data); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to publish message")
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// PublishWithReply 发布请求-响应消息
func (c *NATSClient) PublishWithReply(ctx context.Context, subject string, event *Event, timeout time.Duration) (*Event, error) {
    ctx, span := c.tracer.Start(ctx, "nats.request",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("messaging.system", "nats"),
            attribute.String("messaging.destination", subject),
        ),
    )
    defer span.End()
    
    // 注入追踪信息
    spanCtx := span.SpanContext()
    event.TraceID = spanCtx.TraceID().String()
    event.SpanID = spanCtx.SpanID().String()
    
    // 序列化
    data, err := json.Marshal(event)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    // 发送请求
    msg, err := c.conn.Request(subject, data, timeout)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "request failed")
        return nil, err
    }
    
    // 解析响应
    var response Event
    if err := json.Unmarshal(msg.Data, &response); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "")
    return &response, nil
}
```

### 2.3 订阅消息（带追踪）

```go
// Subscribe 订阅事件
func (c *NATSClient) Subscribe(subject string, handler func(context.Context, *Event) error) (*nats.Subscription, error) {
    return c.conn.Subscribe(subject, func(msg *nats.Msg) {
        // 解析事件
        var event Event
        if err := json.Unmarshal(msg.Data, &event); err != nil {
            fmt.Printf("Failed to unmarshal event: %v\n", err)
            return
        }
        
        // 创建追踪上下文
        ctx := context.Background()
        
        // 提取追踪信息
        var span trace.Span
        if event.TraceID != "" && event.SpanID != "" {
            traceID, _ := trace.TraceIDFromHex(event.TraceID)
            spanID, _ := trace.SpanIDFromHex(event.SpanID)
            
            spanContext := trace.NewSpanContext(trace.SpanContextConfig{
                TraceID: traceID,
                SpanID:  spanID,
            })
            
            ctx = trace.ContextWithSpanContext(ctx, spanContext)
        }
        
        ctx, span = c.tracer.Start(ctx, "nats.consume",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                attribute.String("messaging.system", "nats"),
                attribute.String("messaging.destination", subject),
                attribute.String("messaging.message_id", event.ID),
            ),
        )
        defer span.End()
        
        // 处理事件
        if err := handler(ctx, &event); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            fmt.Printf("Handler error: %v\n", err)
            return
        }
        
        span.SetStatus(codes.Ok, "")
    })
}

// QueueSubscribe 队列订阅（负载均衡）
func (c *NATSClient) QueueSubscribe(subject, queue string, handler func(context.Context, *Event) error) (*nats.Subscription, error) {
    return c.conn.QueueSubscribe(subject, queue, func(msg *nats.Msg) {
        var event Event
        if err := json.Unmarshal(msg.Data, &event); err != nil {
            return
        }
        
        ctx := context.Background()
        ctx, span := c.tracer.Start(ctx, "nats.queue.consume",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                attribute.String("messaging.system", "nats"),
                attribute.String("messaging.destination", subject),
                attribute.String("messaging.consumer_group", queue),
            ),
        )
        defer span.End()
        
        if err := handler(ctx, &event); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            return
        }
        
        span.SetStatus(codes.Ok, "")
    })
}
```

### 2.4 JetStream（持久化）

```go
// JetStreamClient JetStream 客户端
type JetStreamClient struct {
    js     nats.JetStreamContext
    tracer trace.Tracer
}

// NewJetStreamClient 创建 JetStream 客户端
func NewJetStreamClient(nc *nats.Conn) (*JetStreamClient, error) {
    js, err := nc.JetStream()
    if err != nil {
        return nil, err
    }
    
    return &JetStreamClient{
        js:     js,
        tracer: otel.Tracer("jetstream-client"),
    }, nil
}

// CreateStream 创建流
func (c *JetStreamClient) CreateStream(name string, subjects []string) error {
    _, err := c.js.AddStream(&nats.StreamConfig{
        Name:      name,
        Subjects:  subjects,
        Retention: nats.WorkQueuePolicy,
        MaxAge:    24 * time.Hour,
        Storage:   nats.FileStorage,
    })
    return err
}

// PublishAsync 异步发布
func (c *JetStreamClient) PublishAsync(ctx context.Context, subject string, event *Event) error {
    ctx, span := c.tracer.Start(ctx, "jetstream.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()
    
    data, err := json.Marshal(event)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    _, err = c.js.PublishAsync(subject, data)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "publish failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// Subscribe 订阅（持久化消费者）
func (c *JetStreamClient) Subscribe(subject, consumer string, handler func(context.Context, *Event) error) (*nats.Subscription, error) {
    return c.js.Subscribe(subject, func(msg *nats.Msg) {
        var event Event
        if err := json.Unmarshal(msg.Data, &event); err != nil {
            msg.Nak()
            return
        }
        
        ctx := context.Background()
        ctx, span := c.tracer.Start(ctx, "jetstream.consume")
        defer span.End()
        
        if err := handler(ctx, &event); err != nil {
            span.RecordError(err)
            msg.Nak()
            return
        }
        
        msg.Ack()
        span.SetStatus(codes.Ok, "")
    }, nats.Durable(consumer))
}
```

---

## 3. Kafka 完整集成

### 3.1 Sarama 生产者

```go
// internal/messaging/kafka_producer.go
package messaging

import (
    "context"
    "encoding/json"
    
    "github.com/IBM/sarama"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// KafkaProducer Kafka 生产者
type KafkaProducer struct {
    producer sarama.SyncProducer
    tracer   trace.Tracer
}

// NewKafkaProducer 创建 Kafka 生产者
func NewKafkaProducer(brokers []string) (*KafkaProducer, error) {
    config := sarama.NewConfig()
    config.Producer.Return.Successes = true
    config.Producer.Return.Errors = true
    config.Producer.RequiredAcks = sarama.WaitForAll
    config.Producer.Compression = sarama.CompressionSnappy
    config.Producer.Idempotent = true
    config.Producer.MaxMessageBytes = 10 * 1024 * 1024
    
    producer, err := sarama.NewSyncProducer(brokers, config)
    if err != nil {
        return nil, err
    }
    
    return &KafkaProducer{
        producer: producer,
        tracer:   otel.Tracer("kafka-producer"),
    }, nil
}

// Close 关闭生产者
func (p *KafkaProducer) Close() error {
    return p.producer.Close()
}

// Publish 发布消息
func (p *KafkaProducer) Publish(ctx context.Context, topic string, key string, event *Event) error {
    ctx, span := p.tracer.Start(ctx, "kafka.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "kafka"),
            attribute.String("messaging.destination", topic),
            attribute.String("messaging.message_id", event.ID),
        ),
    )
    defer span.End()
    
    // 序列化
    data, err := json.Marshal(event)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    // 创建消息
    msg := &sarama.ProducerMessage{
        Topic: topic,
        Key:   sarama.StringEncoder(key),
        Value: sarama.ByteEncoder(data),
    }
    
    // 注入追踪信息到 Headers
    headers := make([]sarama.RecordHeader, 0)
    propagator := otel.GetTextMapPropagator()
    carrier := &kafkaHeaderCarrier{headers: &headers}
    propagator.Inject(ctx, carrier)
    msg.Headers = headers
    
    // 发送消息
    partition, offset, err := p.producer.SendMessage(msg)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "send failed")
        return err
    }
    
    span.SetAttributes(
        attribute.Int("messaging.kafka.partition", int(partition)),
        attribute.Int64("messaging.kafka.offset", offset),
    )
    span.SetStatus(codes.Ok, "")
    
    return nil
}

// kafkaHeaderCarrier Kafka Header 载体
type kafkaHeaderCarrier struct {
    headers *[]sarama.RecordHeader
}

func (c *kafkaHeaderCarrier) Get(key string) string {
    for _, h := range *c.headers {
        if string(h.Key) == key {
            return string(h.Value)
        }
    }
    return ""
}

func (c *kafkaHeaderCarrier) Set(key, value string) {
    *c.headers = append(*c.headers, sarama.RecordHeader{
        Key:   []byte(key),
        Value: []byte(value),
    })
}

func (c *kafkaHeaderCarrier) Keys() []string {
    keys := make([]string, len(*c.headers))
    for i, h := range *c.headers {
        keys[i] = string(h.Key)
    }
    return keys
}
```

### 3.2 Sarama 消费者

```go
// KafkaConsumer Kafka 消费者
type KafkaConsumer struct {
    consumer sarama.ConsumerGroup
    tracer   trace.Tracer
}

// NewKafkaConsumer 创建 Kafka 消费者
func NewKafkaConsumer(brokers []string, groupID string) (*KafkaConsumer, error) {
    config := sarama.NewConfig()
    config.Consumer.Group.Rebalance.Strategy = sarama.NewBalanceStrategyRoundRobin()
    config.Consumer.Offsets.Initial = sarama.OffsetNewest
    config.Consumer.Return.Errors = true
    
    consumer, err := sarama.NewConsumerGroup(brokers, groupID, config)
    if err != nil {
        return nil, err
    }
    
    return &KafkaConsumer{
        consumer: consumer,
        tracer:   otel.Tracer("kafka-consumer"),
    }, nil
}

// Close 关闭消费者
func (c *KafkaConsumer) Close() error {
    return c.consumer.Close()
}

// Consume 消费消息
func (c *KafkaConsumer) Consume(ctx context.Context, topics []string, handler func(context.Context, *Event) error) error {
    consumerHandler := &consumerGroupHandler{
        tracer:  c.tracer,
        handler: handler,
    }
    
    for {
        if err := c.consumer.Consume(ctx, topics, consumerHandler); err != nil {
            return err
        }
        
        if ctx.Err() != nil {
            return ctx.Err()
        }
    }
}

// consumerGroupHandler 消费者组处理器
type consumerGroupHandler struct {
    tracer  trace.Tracer
    handler func(context.Context, *Event) error
}

func (h *consumerGroupHandler) Setup(sarama.ConsumerGroupSession) error {
    return nil
}

func (h *consumerGroupHandler) Cleanup(sarama.ConsumerGroupSession) error {
    return nil
}

func (h *consumerGroupHandler) ConsumeClaim(session sarama.ConsumerGroupSession, claim sarama.ConsumerGroupClaim) error {
    for msg := range claim.Messages() {
        // 提取追踪上下文
        ctx := context.Background()
        propagator := otel.GetTextMapPropagator()
        carrier := &kafkaHeaderCarrier{headers: &msg.Headers}
        ctx = propagator.Extract(ctx, carrier)
        
        ctx, span := h.tracer.Start(ctx, "kafka.consume",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                attribute.String("messaging.system", "kafka"),
                attribute.String("messaging.destination", msg.Topic),
                attribute.Int("messaging.kafka.partition", int(msg.Partition)),
                attribute.Int64("messaging.kafka.offset", msg.Offset),
            ),
        )
        
        // 解析事件
        var event Event
        if err := json.Unmarshal(msg.Value, &event); err != nil {
            span.RecordError(err)
            span.End()
            continue
        }
        
        // 处理事件
        if err := h.handler(ctx, &event); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
            span.End()
            continue
        }
        
        // 标记消息已处理
        session.MarkMessage(msg, "")
        span.SetStatus(codes.Ok, "")
        span.End()
    }
    
    return nil
}
```

---

## 4. OTLP 追踪集成

### 4.1 统一事件包装器

```go
// TracedEventBus 带追踪的事件总线
type TracedEventBus struct {
    nats  *NATSClient
    kafka *KafkaProducer
    tracer trace.Tracer
    meter  metric.Meter
    
    publishCounter   metric.Int64Counter
    publishDuration  metric.Float64Histogram
}

// NewTracedEventBus 创建带追踪的事件总线
func NewTracedEventBus(nats *NATSClient, kafka *KafkaProducer) (*TracedEventBus, error) {
    tracer := otel.Tracer("event-bus")
    meter := otel.Meter("event-bus")
    
    publishCounter, err := meter.Int64Counter(
        "eventbus.publish.count",
        metric.WithDescription("Number of published events"),
    )
    if err != nil {
        return nil, err
    }
    
    publishDuration, err := meter.Float64Histogram(
        "eventbus.publish.duration",
        metric.WithDescription("Event publish duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    return &TracedEventBus{
        nats:            nats,
        kafka:           kafka,
        tracer:          tracer,
        meter:           meter,
        publishCounter:  publishCounter,
        publishDuration: publishDuration,
    }, nil
}

// PublishEvent 发布事件（自动选择后端）
func (b *TracedEventBus) PublishEvent(ctx context.Context, eventType, destination string, data map[string]interface{}) error {
    start := time.Now()
    
    ctx, span := b.tracer.Start(ctx, "eventbus.publish",
        trace.WithAttributes(
            attribute.String("event.type", eventType),
            attribute.String("event.destination", destination),
        ),
    )
    defer span.End()
    
    event := &Event{
        ID:        uuid.New().String(),
        Type:      eventType,
        Source:    "service",
        Timestamp: time.Now(),
        Data:      data,
    }
    
    var err error
    
    // 根据事件类型选择后端
    if eventType == "realtime" {
        err = b.nats.Publish(ctx, destination, event)
    } else {
        err = b.kafka.Publish(ctx, destination, event.ID, event)
    }
    
    duration := time.Since(start)
    
    // 记录指标
    attrs := metric.WithAttributes(
        attribute.String("event.type", eventType),
        attribute.String("backend", getBackend(eventType)),
        attribute.Bool("success", err == nil),
    )
    
    b.publishCounter.Add(ctx, 1, attrs)
    b.publishDuration.Record(ctx, float64(duration.Milliseconds()), attrs)
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "publish failed")
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

func getBackend(eventType string) string {
    if eventType == "realtime" {
        return "nats"
    }
    return "kafka"
}
```

---

## 5. 事件模式

### 5.1 Event Sourcing（事件溯源）

```go
// EventStore 事件存储
type EventStore struct {
    kafka *KafkaProducer
}

// AppendEvent 追加事件
func (s *EventStore) AppendEvent(ctx context.Context, aggregateID string, event *Event) error {
    topic := fmt.Sprintf("events.%s", event.Type)
    return s.kafka.Publish(ctx, topic, aggregateID, event)
}

// Replay 重放事件
func (s *EventStore) Replay(ctx context.Context, aggregateID string, handler func(*Event) error) error {
    // 从 Kafka 读取所有相关事件
    // 按顺序应用到聚合根
    return nil
}
```

### 5.2 CQRS（命令查询职责分离）

```go
// CommandBus 命令总线
type CommandBus struct {
    nats *NATSClient
}

// SendCommand 发送命令
func (b *CommandBus) SendCommand(ctx context.Context, command *Event) (*Event, error) {
    subject := fmt.Sprintf("commands.%s", command.Type)
    return b.nats.PublishWithReply(ctx, subject, command, 5*time.Second)
}

// QueryBus 查询总线
type QueryBus struct {
    nats *NATSClient
}

// SendQuery 发送查询
func (b *QueryBus) SendQuery(ctx context.Context, query *Event) (*Event, error) {
    subject := fmt.Sprintf("queries.%s", query.Type)
    return b.nats.PublishWithReply(ctx, subject, query, 5*time.Second)
}
```

### 5.3 Saga 模式

```go
// SagaOrchestrator Saga 编排器
type SagaOrchestrator struct {
    bus    *TracedEventBus
    tracer trace.Tracer
}

// ExecuteSaga 执行 Saga
func (o *SagaOrchestrator) ExecuteSaga(ctx context.Context, sagaID string, steps []SagaStep) error {
    ctx, span := o.tracer.Start(ctx, "saga.execute",
        trace.WithAttributes(
            attribute.String("saga.id", sagaID),
            attribute.Int("saga.steps", len(steps)),
        ),
    )
    defer span.End()
    
    completedSteps := make([]SagaStep, 0)
    
    for i, step := range steps {
        stepSpan := trace.SpanFromContext(ctx)
        stepSpan.AddEvent(fmt.Sprintf("Executing step %d", i+1))
        
        if err := step.Execute(ctx, o.bus); err != nil {
            // 回滚已完成的步骤
            for j := len(completedSteps) - 1; j >= 0; j-- {
                completedSteps[j].Compensate(ctx, o.bus)
            }
            
            span.RecordError(err)
            span.SetStatus(codes.Error, "saga failed")
            return err
        }
        
        completedSteps = append(completedSteps, step)
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// SagaStep Saga 步骤
type SagaStep interface {
    Execute(context.Context, *TracedEventBus) error
    Compensate(context.Context, *TracedEventBus) error
}
```

---

## 6. 生产级实践

### 6.1 重试机制

```go
// RetryablePublisher 可重试发布器
type RetryablePublisher struct {
    bus        *TracedEventBus
    maxRetries int
    backoff    time.Duration
}

// PublishWithRetry 带重试的发布
func (p *RetryablePublisher) PublishWithRetry(ctx context.Context, eventType, dest string, data map[string]interface{}) error {
    var lastErr error
    
    for i := 0; i < p.maxRetries; i++ {
        if err := p.bus.PublishEvent(ctx, eventType, dest, data); err == nil {
            return nil
        } else {
            lastErr = err
            time.Sleep(p.backoff * time.Duration(i+1))
        }
    }
    
    return fmt.Errorf("failed after %d retries: %w", p.maxRetries, lastErr)
}
```

### 6.2 Dead Letter Queue

```go
// DLQHandler 死信队列处理器
type DLQHandler struct {
    kafka *KafkaProducer
}

// SendToDLQ 发送到死信队列
func (h *DLQHandler) SendToDLQ(ctx context.Context, originalTopic string, event *Event, err error) error {
    dlqTopic := fmt.Sprintf("%s.dlq", originalTopic)
    
    event.Data["error"] = err.Error()
    event.Data["original_topic"] = originalTopic
    event.Data["failed_at"] = time.Now()
    
    return h.kafka.Publish(ctx, dlqTopic, event.ID, event)
}
```

---

## 7. 性能优化

### 7.1 批量发送

```go
// BatchPublisher 批量发布器
type BatchPublisher struct {
    kafka     *KafkaProducer
    batchSize int
    interval  time.Duration
    buffer    chan *Event
}

// Start 启动批量发送
func (p *BatchPublisher) Start(ctx context.Context) {
    ticker := time.NewTicker(p.interval)
    defer ticker.Stop()
    
    batch := make([]*Event, 0, p.batchSize)
    
    for {
        select {
        case event := <-p.buffer:
            batch = append(batch, event)
            if len(batch) >= p.batchSize {
                p.flush(ctx, batch)
                batch = batch[:0]
            }
            
        case <-ticker.C:
            if len(batch) > 0 {
                p.flush(ctx, batch)
                batch = batch[:0]
            }
            
        case <-ctx.Done():
            return
        }
    }
}

func (p *BatchPublisher) flush(ctx context.Context, batch []*Event) {
    for _, event := range batch {
        p.kafka.Publish(ctx, "events", event.ID, event)
    }
}
```

---

## 8. 总结

### 核心优势

✅ **松耦合** - 服务间解耦  
✅ **可扩展** - 水平扩展  
✅ **异步处理** - 提高吞吐量  
✅ **事件溯源** - 完整历史  
✅ **完整追踪** - OTLP 集成

### 最佳实践

1. ✅ 选择合适的消息系统（NATS vs Kafka）
2. ✅ 实现完整的 OTLP 追踪
3. ✅ 处理失败和重试
4. ✅ 使用死信队列
5. ✅ 监控消息延迟
6. ✅ 实现幂等性
7. ✅ 批量发送优化
8. ✅ 优雅关闭

### 相关文档

- [51_gRPC完整集成指南](./51_gRPC完整集成指南与最佳实践.md)
- [36_Go微服务间通信与分布式追踪](./36_Go微服务间通信与分布式追踪.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**NATS 版本**: v1.37.0  
**Kafka 版本**: Sarama v1.43.3

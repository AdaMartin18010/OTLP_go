# Apache Pulsar 与 OTLP 完整集成（2025版）

> **Pulsar 版本**: 3.3+  
> **pulsar-client-go 版本**: v0.13.0  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [1. Apache Pulsar 概述](#1-apache-pulsar-概述)
- [2. 快速开始](#2-快速开始)
- [3. OTLP 完整集成](#3-otlp-完整集成)
- [4. 高级特性](#4-高级特性)
- [5. 完整示例](#5-完整示例)
- [6. 性能优化](#6-性能优化)
- [7. 最佳实践](#7-最佳实践)
- [8. 总结](#8-总结)

---

## 1. Apache Pulsar 概述

### 1.1 为什么选择 Pulsar

**Apache Pulsar** 是下一代云原生分布式消息和流平台，由 Yahoo 开源。

```text
✅ 核心优势:
  - 云原生架构 - 存储计算分离
  - 多租户支持 - 企业级隔离
  - 地理复制 - 跨数据中心复制
  - 统一模型 - 消息队列 + 流处理
  - 分层存储 - 自动冷热数据分离
  - 高性能 - 百万级 TPS
  - Schema Registry - 内置 Schema 管理

📊 使用统计:
  - 生产部署: 数百家大型企业
  - 社区: Apache 顶级项目
  - 性能: 1M+ msg/s
  - 用户: Yahoo, Tencent, Alibaba等
```

### 1.2 与 Kafka/RabbitMQ 对比

```text
┌──────────────────┬─────────┬──────────┬──────────┬────────────┐
│   特性           │ Pulsar  │  Kafka   │ RabbitMQ │  NATS      │
├──────────────────┼─────────┼──────────┼──────────┼────────────┤
│ 吞吐量           │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐⭐  │
│ 延迟             │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐   │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐⭐  │
│ 多租户           │  ⭐⭐⭐⭐⭐ │ ⭐⭐      │ ⭐⭐⭐    │  ⭐⭐⭐    │
│ 地理复制         │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐   │ ⭐⭐⭐    │  ⭐⭐⭐⭐   │
│ 分层存储         │  ⭐⭐⭐⭐⭐ │ ⭐⭐      │ ⭐       │  ⭐⭐     │
│ 易用性           │  ⭐⭐⭐⭐  │ ⭐⭐⭐    │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐⭐⭐  │
│ 消息模型         │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐    │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐⭐   │
└──────────────────┴─────────┴──────────┴──────────┴────────────┘

核心区别:
  ✅ Pulsar: 存储计算分离，多租户，统一消息+流
  ✅ Kafka: 最成熟，生态最完善，日志流
  ✅ RabbitMQ: 路由最灵活，易用性高
  ✅ NATS: 最轻量，云原生首选
```

### 1.3 核心架构

```text
┌─────────────────────────────────────────────────────────┐
│                    Pulsar 架构                          │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐    │
│  │   Broker 1  │  │   Broker 2  │  │   Broker 3  │    │
│  │  (无状态)   │  │  (无状态)   │  │  (无状态)   │    │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘    │
│         │                │                │            │
│         └────────────────┼────────────────┘            │
│                          │                             │
│  ┌───────────────────────┴──────────────────────┐      │
│  │           BookKeeper (存储层)                │      │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐      │      │
│  │  │ Bookie1 │  │ Bookie2 │  │ Bookie3 │      │      │
│  │  └─────────┘  └─────────┘  └─────────┘      │      │
│  └──────────────────────────────────────────────┘      │
│                                                         │
│  ┌──────────────────────────────────────────────┐      │
│  │        ZooKeeper (元数据管理)                │      │
│  └──────────────────────────────────────────────┘      │
└─────────────────────────────────────────────────────────┘
```

### 1.4 适用场景

```go
// ✅ 适合场景
scenarios := []string{
    "多租户 SaaS 平台",
    "地理复制需求",
    "消息 + 流统一处理",
    "大规模实时数据管道",
    "金融交易系统",
    "物联网数据采集",
    "需要分层存储",
}

// ⚠️ 考虑其他方案
alternatives := []string{
    "简单场景（考虑 RabbitMQ/NATS）",
    "成熟生态（考虑 Kafka）",
    "团队熟悉度（Kafka 更普及）",
}
```

---

## 2. 快速开始

### 2.1 Docker 部署 Pulsar

```bash
# 单机模式（开发环境）
docker run -d \
  --name pulsar-standalone \
  -p 6650:6650 \
  -p 8080:8080 \
  apachepulsar/pulsar:3.3.0 \
  bin/pulsar standalone

# 集群模式（使用 docker-compose）
cat > docker-compose-pulsar.yml <<EOF
version: '3'
services:
  zookeeper:
    image: apachepulsar/pulsar:3.3.0
    command: bin/pulsar zookeeper
    ports:
      - "2181:2181"
    environment:
      - PULSAR_MEM=-Xms256m -Xmx256m

  bookie:
    image: apachepulsar/pulsar:3.3.0
    command: bin/pulsar bookie
    ports:
      - "3181:3181"
    environment:
      - PULSAR_MEM=-Xms512m -Xmx512m
    depends_on:
      - zookeeper

  broker:
    image: apachepulsar/pulsar:3.3.0
    command: bin/pulsar broker
    ports:
      - "6650:6650"
      - "8080:8080"
    environment:
      - PULSAR_MEM=-Xms512m -Xmx512m
    depends_on:
      - zookeeper
      - bookie
EOF

docker-compose -f docker-compose-pulsar.yml up -d

# 访问管理界面（需要安装 Pulsar Manager）
# http://localhost:9527
```

### 2.2 Go 依赖安装

```bash
# Pulsar Go 客户端
go get github.com/apache/pulsar-client-go@v0.13.0

# OTLP 依赖
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.32.0
```

### 2.3 基础配置

```go
package main

import (
    "context"
    "log"
    "time"
    
    "github.com/apache/pulsar-client-go/pulsar"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func main() {
    ctx := context.Background()
    
    // 初始化 OTLP
    tp, err := initOTLP(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(ctx)
    
    // 创建 Pulsar 客户端
    client, err := pulsar.NewClient(pulsar.ClientOptions{
        URL:               "pulsar://localhost:6650",
        OperationTimeout:  30 * time.Second,
        ConnectionTimeout: 30 * time.Second,
    })
    if err != nil {
        log.Fatal(err)
    }
    defer client.Close()
    
    log.Println("Connected to Pulsar")
}

func initOTLP(ctx context.Context) (*trace.TracerProvider, error) {
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
        trace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceName("pulsar-service"),
            semconv.ServiceVersion("1.0.0"),
        )),
    )
    
    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
    
    return tp, nil
}
```

---

## 3. OTLP 完整集成

### 3.1 追踪生产者

```go
package pulsarotel

import (
    "context"
    "fmt"
    "time"
    
    "github.com/apache/pulsar-client-go/pulsar"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// TracedProducer 带追踪的生产者
type TracedProducer struct {
    producer   pulsar.Producer
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
    topic      string
}

// NewTracedProducer 创建追踪生产者
func NewTracedProducer(client pulsar.Client, config pulsar.ProducerOptions) (*TracedProducer, error) {
    producer, err := client.CreateProducer(config)
    if err != nil {
        return nil, err
    }
    
    return &TracedProducer{
        producer:   producer,
        tracer:     otel.Tracer("pulsar-producer"),
        propagator: otel.GetTextMapPropagator(),
        topic:      config.Topic,
    }, nil
}

// Send 发送消息（带追踪）
func (p *TracedProducer) Send(ctx context.Context, msg *pulsar.ProducerMessage) (pulsar.MessageID, error) {
    // 创建 span
    ctx, span := p.tracer.Start(ctx, "pulsar.send",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "pulsar"),
            attribute.String("messaging.destination", p.topic),
            attribute.Int("messaging.message_size", len(msg.Payload)),
        ),
    )
    defer span.End()
    
    // 注入 trace context
    if msg.Properties == nil {
        msg.Properties = make(map[string]string)
    }
    
    carrier := propagation.MapCarrier(msg.Properties)
    p.propagator.Inject(ctx, carrier)
    
    // 添加元数据
    msg.Properties["trace_id"] = span.SpanContext().TraceID().String()
    msg.Properties["span_id"] = span.SpanContext().SpanID().String()
    msg.Properties["sent_at"] = fmt.Sprintf("%d", time.Now().Unix())
    
    // 发送消息
    start := time.Now()
    msgID, err := p.producer.Send(ctx, msg)
    duration := time.Since(start)
    
    span.SetAttributes(
        attribute.Int64("messaging.send_time_ms", duration.Milliseconds()),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    
    // 记录消息 ID
    span.SetAttributes(
        attribute.String("messaging.message_id", msgID.String()),
    )
    
    span.SetStatus(codes.Ok, "message sent")
    return msgID, nil
}

// SendAsync 异步发送消息（带追踪）
func (p *TracedProducer) SendAsync(
    ctx context.Context,
    msg *pulsar.ProducerMessage,
    callback func(pulsar.MessageID, *pulsar.ProducerMessage, error),
) {
    // 创建 span
    ctx, span := p.tracer.Start(ctx, "pulsar.send_async",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "pulsar"),
            attribute.String("messaging.destination", p.topic),
        ),
    )
    
    // 注入 trace context
    if msg.Properties == nil {
        msg.Properties = make(map[string]string)
    }
    
    carrier := propagation.MapCarrier(msg.Properties)
    p.propagator.Inject(ctx, carrier)
    
    // 异步发送
    p.producer.SendAsync(ctx, msg, func(msgID pulsar.MessageID, message *pulsar.ProducerMessage, err error) {
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        } else {
            span.SetAttributes(
                attribute.String("messaging.message_id", msgID.String()),
            )
            span.SetStatus(codes.Ok, "message sent")
        }
        span.End()
        
        if callback != nil {
            callback(msgID, message, err)
        }
    })
}

// Close 关闭生产者
func (p *TracedProducer) Close() {
    p.producer.Close()
}
```

### 3.2 追踪消费者

```go
// TracedConsumer 带追踪的消费者
type TracedConsumer struct {
    consumer   pulsar.Consumer
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedConsumer 创建追踪消费者
func NewTracedConsumer(client pulsar.Client, config pulsar.ConsumerOptions) (*TracedConsumer, error) {
    consumer, err := client.Subscribe(config)
    if err != nil {
        return nil, err
    }
    
    return &TracedConsumer{
        consumer:   consumer,
        tracer:     otel.Tracer("pulsar-consumer"),
        propagator: otel.GetTextMapPropagator(),
    }, nil
}

// Receive 接收消息（带追踪）
func (c *TracedConsumer) Receive(parentCtx context.Context) (pulsar.Message, context.Context, trace.Span, error) {
    // 接收消息
    msg, err := c.consumer.Receive(parentCtx)
    if err != nil {
        return nil, parentCtx, nil, err
    }
    
    // 提取 trace context
    carrier := propagation.MapCarrier(msg.Properties())
    ctx := c.propagator.Extract(parentCtx, carrier)
    
    // 创建 span
    ctx, span := c.tracer.Start(ctx, "pulsar.receive",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("messaging.system", "pulsar"),
            attribute.String("messaging.destination", msg.Topic()),
            attribute.String("messaging.message_id", msg.ID().String()),
            attribute.Int("messaging.message_size", len(msg.Payload())),
        ),
    )
    
    // 记录消息元数据
    if traceID, ok := msg.Properties()["trace_id"]; ok {
        span.SetAttributes(attribute.String("messaging.parent_trace_id", traceID))
    }
    
    if sentAt, ok := msg.Properties()["sent_at"]; ok {
        var sentTime int64
        fmt.Sscanf(sentAt, "%d", &sentTime)
        latency := time.Now().Unix() - sentTime
        span.SetAttributes(attribute.Int64("messaging.latency_seconds", latency))
    }
    
    return msg, ctx, span, nil
}

// Process 处理消息（带追踪和自动确认）
func (c *TracedConsumer) Process(
    parentCtx context.Context,
    handler func(context.Context, pulsar.Message) error,
) error {
    msg, ctx, span, err := c.Receive(parentCtx)
    if err != nil {
        return err
    }
    defer span.End()
    
    // 处理消息
    start := time.Now()
    err = handler(ctx, msg)
    duration := time.Since(start)
    
    span.SetAttributes(
        attribute.Int64("messaging.process_time_ms", duration.Milliseconds()),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        
        // Nack 消息
        c.consumer.Nack(msg)
        return err
    }
    
    span.SetStatus(codes.Ok, "message processed")
    
    // Ack 消息
    c.consumer.Ack(msg)
    return nil
}

// Close 关闭消费者
func (c *TracedConsumer) Close() {
    c.consumer.Close()
}
```

---

## 4. 高级特性

### 4.1 多租户支持

```go
// 创建租户和命名空间
func SetupTenant(adminURL, tenant, namespace string) error {
    // 实际应该使用 Pulsar Admin API
    // 这里仅做示例
    
    // 创建租户
    // POST /admin/v2/tenants/{tenant}
    
    // 创建命名空间
    // PUT /admin/v2/namespaces/{tenant}/{namespace}
    
    return nil
}

// 使用租户和命名空间
func CreateProducerWithTenant(client pulsar.Client, tenant, namespace, topic string) (pulsar.Producer, error) {
    fullTopic := fmt.Sprintf("persistent://%s/%s/%s", tenant, namespace, topic)
    
    producer, err := client.CreateProducer(pulsar.ProducerOptions{
        Topic: fullTopic,
    })
    
    return producer, err
}
```

### 4.2 Schema Registry

```go
// 定义 Schema
type User struct {
    ID       int64  `json:"id"`
    Name     string `json:"name"`
    Email    string `json:"email"`
    CreateAt int64  `json:"create_at"`
}

// 使用 JSON Schema
func CreateProducerWithSchema(client pulsar.Client, topic string) (pulsar.Producer, error) {
    jsonSchema := pulsar.NewJSONSchema(`{
        "type": "record",
        "name": "User",
        "fields": [
            {"name": "id", "type": "long"},
            {"name": "name", "type": "string"},
            {"name": "email", "type": "string"},
            {"name": "create_at", "type": "long"}
        ]
    }`, nil)
    
    producer, err := client.CreateProducer(pulsar.ProducerOptions{
        Topic:  topic,
        Schema: jsonSchema,
    })
    
    return producer, err
}

// 发送带 Schema 的消息
func SendWithSchema(producer pulsar.Producer, user User) error {
    data, err := json.Marshal(user)
    if err != nil {
        return err
    }
    
    _, err = producer.Send(context.Background(), &pulsar.ProducerMessage{
        Payload: data,
    })
    
    return err
}
```

### 4.3 延迟消息

```go
// 延迟消息
func SendDelayedMessage(producer pulsar.Producer, payload []byte, delay time.Duration) error {
    _, err := producer.Send(context.Background(), &pulsar.ProducerMessage{
        Payload:      payload,
        DeliverAfter: delay,  // 延迟投递
    })
    return err
}

// 示例：延迟 30 秒
err := SendDelayedMessage(producer, []byte("delayed message"), 30*time.Second)
```

### 4.4 死信队列

```go
// 配置死信队列
consumer, err := client.Subscribe(pulsar.ConsumerOptions{
    Topic:            "main-topic",
    SubscriptionName: "my-sub",
    Type:             pulsar.Shared,
    
    // 死信队列配置
    DLQ: &pulsar.DLQPolicy{
        MaxDeliveries:    3,                // 最大重试次数
        DeadLetterTopic:  "dead-letter",    // 死信主题
        RetryLetterTopic: "retry",          // 重试主题
    },
    
    // 重试配置
    RetryEnable: true,
})
```

### 4.5 地理复制

```go
// 配置地理复制（需要在 Pulsar 集群配置）
// 1. 配置集群
// bin/pulsar-admin clusters create cluster-us-west --url http://us-west:8080
// bin/pulsar-admin clusters create cluster-us-east --url http://us-east:8080

// 2. 创建全局命名空间
// bin/pulsar-admin namespaces create my-tenant/my-global-namespace --clusters cluster-us-west,cluster-us-east

// 3. 使用全局主题
fullTopic := "persistent://my-tenant/my-global-namespace/my-topic"
producer, err := client.CreateProducer(pulsar.ProducerOptions{
    Topic: fullTopic,
})
```

---

## 5. 完整示例

### 5.1 电商订单处理系统

```go
package main

import (
    "context"
    "encoding/json"
    "log"
    "time"
    
    "github.com/apache/pulsar-client-go/pulsar"
    "your-project/pulsarotel"
)

type Order struct {
    ID        string    `json:"id"`
    UserID    string    `json:"user_id"`
    Amount    float64   `json:"amount"`
    Status    string    `json:"status"`
    CreatedAt time.Time `json:"created_at"`
}

type OrderService struct {
    producer *pulsarotel.TracedProducer
    consumer *pulsarotel.TracedConsumer
}

func NewOrderService(client pulsar.Client) (*OrderService, error) {
    // 创建生产者
    producer, err := pulsarotel.NewTracedProducer(client, pulsar.ProducerOptions{
        Topic:                   "persistent://public/default/orders",
        BatchingMaxPublishDelay: 10 * time.Millisecond,
        CompressionType:         pulsar.LZ4,
    })
    if err != nil {
        return nil, err
    }
    
    // 创建消费者
    consumer, err := pulsarotel.NewTracedConsumer(client, pulsar.ConsumerOptions{
        Topic:            "persistent://public/default/orders",
        SubscriptionName: "order-processor",
        Type:             pulsar.Shared,
    })
    if err != nil {
        producer.Close()
        return nil, err
    }
    
    return &OrderService{
        producer: producer,
        consumer: consumer,
    }, nil
}

// CreateOrder 创建订单
func (s *OrderService) CreateOrder(ctx context.Context, order Order) error {
    tracer := otel.Tracer("order-service")
    ctx, span := tracer.Start(ctx, "create-order")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
        attribute.String("user.id", order.UserID),
        attribute.Float64("order.amount", order.Amount),
    )
    
    // 序列化订单
    payload, err := json.Marshal(order)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    // 发送消息
    msgID, err := s.producer.Send(ctx, &pulsar.ProducerMessage{
        Payload: payload,
        Key:     order.UserID, // 分区键
        Properties: map[string]string{
            "order_id": order.ID,
            "type":     "order.created",
        },
    })
    
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    log.Printf("Order created: %s, MessageID: %s", order.ID, msgID.String())
    span.SetStatus(codes.Ok, "order created")
    return nil
}

// ProcessOrders 处理订单
func (s *OrderService) ProcessOrders(ctx context.Context) error {
    log.Println("Start processing orders...")
    
    for {
        select {
        case <-ctx.Done():
            log.Println("Stop processing orders")
            return ctx.Err()
            
        default:
            if err := s.consumer.Process(ctx, s.handleOrder); err != nil {
                log.Printf("Process error: %v", err)
                continue
            }
        }
    }
}

// handleOrder 处理单个订单
func (s *OrderService) handleOrder(ctx context.Context, msg pulsar.Message) error {
    tracer := otel.Tracer("order-processor")
    ctx, span := tracer.Start(ctx, "handle-order")
    defer span.End()
    
    var order Order
    if err := json.Unmarshal(msg.Payload(), &order); err != nil {
        span.RecordError(err)
        return err
    }
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
    )
    
    log.Printf("Processing order: %s", order.ID)
    
    // 1. 验证库存
    if err := checkInventory(ctx, order); err != nil {
        span.RecordError(err)
        return err
    }
    
    // 2. 处理支付
    if err := processPayment(ctx, order); err != nil {
        span.RecordError(err)
        return err
    }
    
    // 3. 发货
    if err := shipOrder(ctx, order); err != nil {
        span.RecordError(err)
        return err
    }
    
    log.Printf("Order processed successfully: %s", order.ID)
    span.SetStatus(codes.Ok, "order processed")
    return nil
}

func checkInventory(ctx context.Context, order Order) error {
    time.Sleep(100 * time.Millisecond)
    return nil
}

func processPayment(ctx context.Context, order Order) error {
    time.Sleep(200 * time.Millisecond)
    return nil
}

func shipOrder(ctx context.Context, order Order) error {
    time.Sleep(150 * time.Millisecond)
    return nil
}

func main() {
    ctx := context.Background()
    
    // 初始化 OTLP
    tp, err := initOTLP(ctx)
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(ctx)
    
    // 创建 Pulsar 客户端
    client, err := pulsar.NewClient(pulsar.ClientOptions{
        URL:               "pulsar://localhost:6650",
        OperationTimeout:  30 * time.Second,
        ConnectionTimeout: 30 * time.Second,
    })
    if err != nil {
        log.Fatal(err)
    }
    defer client.Close()
    
    // 创建订单服务
    service, err := NewOrderService(client)
    if err != nil {
        log.Fatal(err)
    }
    defer service.producer.Close()
    defer service.consumer.Close()
    
    // 启动消费者
    go func() {
        if err := service.ProcessOrders(ctx); err != nil {
            log.Printf("Consumer error: %v", err)
        }
    }()
    
    // 模拟创建订单
    for i := 0; i < 10; i++ {
        order := Order{
            ID:        fmt.Sprintf("order-%d", i+1),
            UserID:    "user-123",
            Amount:    99.99,
            Status:    "pending",
            CreatedAt: time.Now(),
        }
        
        if err := service.CreateOrder(ctx, order); err != nil {
            log.Printf("Failed to create order: %v", err)
        }
        
        time.Sleep(time.Second)
    }
    
    // 等待处理完成
    time.Sleep(30 * time.Second)
}
```

---

## 6. 性能优化

### 6.1 批量发送

```go
// 配置批量发送
producer, err := client.CreateProducer(pulsar.ProducerOptions{
    Topic:                   "my-topic",
    BatchingMaxPublishDelay: 10 * time.Millisecond,  // 批量延迟
    BatchingMaxMessages:     100,                     // 批量大小
    CompressionType:         pulsar.LZ4,              // 压缩
})
```

### 6.2 异步发送

```go
// 异步发送（更高吞吐）
for i := 0; i < 1000; i++ {
    producer.SendAsync(ctx, &pulsar.ProducerMessage{
        Payload: []byte(fmt.Sprintf("message-%d", i)),
    }, func(msgID pulsar.MessageID, msg *pulsar.ProducerMessage, err error) {
        if err != nil {
            log.Printf("Send failed: %v", err)
        } else {
            log.Printf("Message sent: %s", msgID.String())
        }
    })
}

// 等待所有消息发送完成
producer.Flush()
```

### 6.3 分区主题

```go
// 创建分区主题（使用 Pulsar Admin API）
// bin/pulsar-admin topics create-partitioned-topic persistent://public/default/my-topic --partitions 10

// 使用分区主题
producer, err := client.CreateProducer(pulsar.ProducerOptions{
    Topic:                   "persistent://public/default/my-topic",
    MessageRouter:           pulsar.NewDefaultRouter(pulsar.JavaStringHash), // 路由策略
})
```

---

## 7. 最佳实践

### 7.1 连接管理

```go
// 1. 复用客户端
var globalClient pulsar.Client

func init() {
    var err error
    globalClient, err = pulsar.NewClient(pulsar.ClientOptions{
        URL: "pulsar://localhost:6650",
    })
    if err != nil {
        panic(err)
    }
}

// 2. 优雅关闭
func Shutdown() {
    globalClient.Close()
}
```

### 7.2 错误处理

```go
// 重试逻辑
func SendWithRetry(producer pulsar.Producer, msg *pulsar.ProducerMessage, maxRetries int) error {
    var err error
    for i := 0; i < maxRetries; i++ {
        _, err = producer.Send(context.Background(), msg)
        if err == nil {
            return nil
        }
        
        log.Printf("Send failed (attempt %d/%d): %v", i+1, maxRetries, err)
        time.Sleep(time.Second * time.Duration(i+1))
    }
    return fmt.Errorf("failed after %d retries: %w", maxRetries, err)
}
```

---

## 8. 总结

### 8.1 优势与劣势

```text
✅ 优势:
  - 云原生架构，存储计算分离
  - 多租户支持完善
  - 地理复制功能强大
  - 统一消息+流模型
  - 分层存储降低成本

❌ 劣势:
  - 部署复杂度高
  - 学习曲线陡峭
  - 社区相对 Kafka 小
  - 运维成本较高
```

### 8.2 vs Kafka 选择指南

```text
选择 Pulsar:
  ✅ 需要多租户隔离
  ✅ 需要地理复制
  ✅ 需要分层存储
  ✅ 云原生架构优先

选择 Kafka:
  ✅ 生态成熟度优先
  ✅ 团队熟悉度高
  ✅ 日志流场景
  ✅ 简单部署
```

**相关文档**:

- [01_RabbitMQ与OTLP完整集成_2025版.md](./01_RabbitMQ与OTLP完整集成_2025版.md)
- [52_事件驱动架构_NATS与Kafka集成.md](../52_事件驱动架构_NATS与Kafka集成.md)

---

**更新日期**: 2025-10-11  
**Pulsar 版本**: 3.3+  
**性能级别**: ⭐⭐⭐⭐⭐  
**推荐指数**: ⭐⭐⭐⭐⭐

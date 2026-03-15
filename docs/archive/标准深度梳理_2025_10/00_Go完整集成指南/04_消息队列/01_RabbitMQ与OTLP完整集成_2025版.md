# RabbitMQ 与 OTLP 完整集成（2025版）

> **RabbitMQ 版本**: 3.13+  
> **amqp091-go 版本**: v1.10.0  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [1. RabbitMQ 概述](#1-rabbitmq-概述)
- [2. 快速开始](#2-快速开始)
- [3. OTLP 完整集成](#3-otlp-完整集成)
- [4. 高级特性](#4-高级特性)
- [5. 完整示例](#5-完整示例)
- [6. 性能优化](#6-性能优化)
- [7. 最佳实践](#7-最佳实践)
- [8. 总结](#8-总结)

---

## 1. RabbitMQ 概述

### 1.1 为什么选择 RabbitMQ

**RabbitMQ** 是最流行的开源消息队列之一，基于 AMQP 协议。

```text
✅ 核心优势:
  - 成熟稳定 - 15+ 年生产验证
  - 功能丰富 - 完整的 AMQP 0-9-1 支持
  - 灵活路由 - Exchange/Queue/Binding 模式
  - 可靠投递 - 消息确认、持久化
  - 管理界面 - Web UI 完善
  - 插件生态 - 丰富的插件支持
  - 多语言 - 客户端库完善

📊 使用统计:
  - 生产部署: 数万家公司
  - 社区: 非常活跃
  - 性能: 40,000+ msg/s
```

### 1.2 与其他消息队列对比

```text
┌──────────────┬─────────┬──────────┬──────────┬────────────┐
│   消息队列   │  性能   │ 功能     │ 易用性   │ 推荐指数   │
├──────────────┼─────────┼──────────┼──────────┼────────────┤
│ RabbitMQ     │  ⭐⭐⭐⭐  │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐⭐  │
│ Kafka        │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐   │ ⭐⭐⭐    │  ⭐⭐⭐⭐⭐  │
│ NATS         │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐    │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐⭐   │
│ Pulsar       │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐    │  ⭐⭐⭐⭐   │
│ Redis Stream │  ⭐⭐⭐⭐  │ ⭐⭐⭐    │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐    │
└──────────────┴─────────┴──────────┴──────────┴────────────┘

特点:
  - RabbitMQ: 功能最完整，路由最灵活
  - Kafka: 吞吐量最高，日志流场景
  - NATS: 最轻量，云原生首选
  - Pulsar: 多租户，企业级特性
```

### 1.3 适用场景

```go
// ✅ 适合场景
scenarios := []string{
    "任务队列",
    "发布订阅",
    "RPC 通信",
    "工作流编排",
    "事件驱动架构",
    "微服务解耦",
}

// ⚠️ 考虑其他方案
alternatives := []string{
    "日志流处理（考虑 Kafka）",
    "云原生轻量级（考虑 NATS）",
    "多租户场景（考虑 Pulsar）",
}
```

---

## 2. 快速开始

### 2.1 Docker 部署 RabbitMQ

```bash
# 启动 RabbitMQ（带管理界面）
docker run -d --name rabbitmq \
  -p 5672:5672 \
  -p 15672:15672 \
  -e RABBITMQ_DEFAULT_USER=admin \
  -e RABBITMQ_DEFAULT_PASS=admin \
  rabbitmq:3.13-management

# 访问管理界面
# http://localhost:15672
# 用户名: admin, 密码: admin
```

### 2.2 Go 依赖安装

```bash
# RabbitMQ Go 客户端
go get github.com/rabbitmq/amqp091-go

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
    
    amqp "github.com/rabbitmq/amqp091-go"
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
    
    // 连接 RabbitMQ
    conn, err := amqp.Dial("amqp://admin:admin@localhost:5672/")
    if err != nil {
        log.Fatal(err)
    }
    defer conn.Close()
    
    // 创建 Channel
    ch, err := conn.Channel()
    if err != nil {
        log.Fatal(err)
    }
    defer ch.Close()
    
    // 声明队列
    q, err := ch.QueueDeclare(
        "hello",  // name
        false,    // durable
        false,    // delete when unused
        false,    // exclusive
        false,    // no-wait
        nil,      // arguments
    )
    if err != nil {
        log.Fatal(err)
    }
    
    log.Printf("Queue declared: %s", q.Name)
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
            semconv.ServiceName("rabbitmq-service"),
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
package rabbitmq

import (
    "context"
    "encoding/json"
    "fmt"
    "time"
    
    amqp "github.com/rabbitmq/amqp091-go"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// TracedProducer 带追踪的生产者
type TracedProducer struct {
    conn       *amqp.Connection
    ch         *amqp.Channel
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedProducer 创建追踪生产者
func NewTracedProducer(url string) (*TracedProducer, error) {
    conn, err := amqp.Dial(url)
    if err != nil {
        return nil, err
    }
    
    ch, err := conn.Channel()
    if err != nil {
        conn.Close()
        return nil, err
    }
    
    return &TracedProducer{
        conn:       conn,
        ch:         ch,
        tracer:     otel.Tracer("rabbitmq-producer"),
        propagator: otel.GetTextMapPropagator(),
    }, nil
}

// Publish 发布消息（带追踪）
func (p *TracedProducer) Publish(
    ctx context.Context,
    exchange, routingKey string,
    mandatory, immediate bool,
    msg amqp.Publishing,
) error {
    // 创建 span
    ctx, span := p.tracer.Start(ctx, "rabbitmq.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "rabbitmq"),
            attribute.String("messaging.destination", exchange),
            attribute.String("messaging.routing_key", routingKey),
            attribute.Int("messaging.message_size", len(msg.Body)),
        ),
    )
    defer span.End()
    
    // 注入 trace context 到消息头
    if msg.Headers == nil {
        msg.Headers = amqp.Table{}
    }
    
    carrier := &amqpHeaderCarrier{headers: msg.Headers}
    p.propagator.Inject(ctx, carrier)
    
    // 添加其他元数据
    msg.Headers["trace_id"] = span.SpanContext().TraceID().String()
    msg.Headers["span_id"] = span.SpanContext().SpanID().String()
    msg.Headers["published_at"] = time.Now().Unix()
    
    // 发布消息
    start := time.Now()
    err := p.ch.PublishWithContext(
        ctx,
        exchange,
        routingKey,
        mandatory,
        immediate,
        msg,
    )
    duration := time.Since(start)
    
    span.SetAttributes(
        attribute.Int64("messaging.publish_time_ms", duration.Milliseconds()),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "message published")
    return nil
}

// Close 关闭生产者
func (p *TracedProducer) Close() error {
    if p.ch != nil {
        p.ch.Close()
    }
    if p.conn != nil {
        return p.conn.Close()
    }
    return nil
}

// amqpHeaderCarrier AMQP 头部载体
type amqpHeaderCarrier struct {
    headers amqp.Table
}

func (c *amqpHeaderCarrier) Get(key string) string {
    if val, ok := c.headers[key]; ok {
        if str, ok := val.(string); ok {
            return str
        }
    }
    return ""
}

func (c *amqpHeaderCarrier) Set(key, value string) {
    c.headers[key] = value
}

func (c *amqpHeaderCarrier) Keys() []string {
    keys := make([]string, 0, len(c.headers))
    for k := range c.headers {
        keys = append(keys, k)
    }
    return keys
}
```

### 3.2 追踪消费者

```go
// TracedConsumer 带追踪的消费者
type TracedConsumer struct {
    conn       *amqp.Connection
    ch         *amqp.Channel
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedConsumer 创建追踪消费者
func NewTracedConsumer(url string) (*TracedConsumer, error) {
    conn, err := amqp.Dial(url)
    if err != nil {
        return nil, err
    }
    
    ch, err := conn.Channel()
    if err != nil {
        conn.Close()
        return nil, err
    }
    
    // 设置 QoS
    err = ch.Qos(
        10,    // prefetch count
        0,     // prefetch size
        false, // global
    )
    if err != nil {
        ch.Close()
        conn.Close()
        return nil, err
    }
    
    return &TracedConsumer{
        conn:       conn,
        ch:         ch,
        tracer:     otel.Tracer("rabbitmq-consumer"),
        propagator: otel.GetTextMapPropagator(),
    }, nil
}

// Consume 消费消息（带追踪）
func (c *TracedConsumer) Consume(
    ctx context.Context,
    queue string,
    handler func(context.Context, amqp.Delivery) error,
) error {
    // 开始消费
    msgs, err := c.ch.Consume(
        queue,
        "",    // consumer
        false, // auto-ack
        false, // exclusive
        false, // no-local
        false, // no-wait
        nil,   // args
    )
    if err != nil {
        return err
    }
    
    log.Printf("Start consuming from queue: %s", queue)
    
    // 处理消息
    for {
        select {
        case <-ctx.Done():
            log.Println("Consumer stopped")
            return ctx.Err()
            
        case msg, ok := <-msgs:
            if !ok {
                log.Println("Channel closed")
                return nil
            }
            
            c.handleMessage(ctx, msg, handler)
        }
    }
}

// handleMessage 处理单个消息
func (c *TracedConsumer) handleMessage(
    parentCtx context.Context,
    msg amqp.Delivery,
    handler func(context.Context, amqp.Delivery) error,
) {
    // 提取 trace context
    carrier := &amqpHeaderCarrier{headers: msg.Headers}
    ctx := c.propagator.Extract(parentCtx, carrier)
    
    // 创建 span
    ctx, span := c.tracer.Start(ctx, "rabbitmq.consume",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("messaging.system", "rabbitmq"),
            attribute.String("messaging.destination", msg.Exchange),
            attribute.String("messaging.routing_key", msg.RoutingKey),
            attribute.String("messaging.message_id", msg.MessageId),
            attribute.Int("messaging.message_size", len(msg.Body)),
        ),
    )
    defer span.End()
    
    // 记录消息元数据
    if traceID, ok := msg.Headers["trace_id"].(string); ok {
        span.SetAttributes(attribute.String("messaging.parent_trace_id", traceID))
    }
    
    if publishedAt, ok := msg.Headers["published_at"].(int64); ok {
        latency := time.Now().Unix() - publishedAt
        span.SetAttributes(attribute.Int64("messaging.latency_seconds", latency))
    }
    
    // 处理消息
    start := time.Now()
    err := handler(ctx, msg)
    duration := time.Since(start)
    
    span.SetAttributes(
        attribute.Int64("messaging.process_time_ms", duration.Milliseconds()),
    )
    
    if err != nil {
        // 处理失败
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        
        // Nack 消息（重新入队）
        if nackErr := msg.Nack(false, true); nackErr != nil {
            span.RecordError(fmt.Errorf("nack failed: %w", nackErr))
        }
        
        log.Printf("Message processing failed: %v", err)
        return
    }
    
    // 处理成功
    span.SetStatus(codes.Ok, "message processed")
    
    // Ack 消息
    if err := msg.Ack(false); err != nil {
        span.RecordError(fmt.Errorf("ack failed: %w", err))
        log.Printf("Failed to ack message: %v", err)
    }
}

// Close 关闭消费者
func (c *TracedConsumer) Close() error {
    if c.ch != nil {
        c.ch.Close()
    }
    if c.conn != nil {
        return c.conn.Close()
    }
    return nil
}
```

---

## 4. 高级特性

### 4.1 工作队列模式

```go
// WorkQueue 工作队列
type WorkQueue struct {
    producer *TracedProducer
    consumer *TracedConsumer
}

// Task 任务定义
type Task struct {
    ID      string                 `json:"id"`
    Type    string                 `json:"type"`
    Payload map[string]interface{} `json:"payload"`
}

// SubmitTask 提交任务
func (wq *WorkQueue) SubmitTask(ctx context.Context, task Task) error {
    tracer := otel.Tracer("work-queue")
    ctx, span := tracer.Start(ctx, "submit-task")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("task.id", task.ID),
        attribute.String("task.type", task.Type),
    )
    
    body, err := json.Marshal(task)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    err = wq.producer.Publish(ctx, "", "tasks", false, false, amqp.Publishing{
        ContentType:  "application/json",
        Body:         body,
        DeliveryMode: amqp.Persistent, // 持久化
    })
    
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "task submitted")
    return nil
}

// ProcessTasks 处理任务
func (wq *WorkQueue) ProcessTasks(ctx context.Context) error {
    return wq.consumer.Consume(ctx, "tasks", func(ctx context.Context, msg amqp.Delivery) error {
        tracer := otel.Tracer("task-processor")
        ctx, span := tracer.Start(ctx, "process-task")
        defer span.End()
        
        var task Task
        if err := json.Unmarshal(msg.Body, &task); err != nil {
            span.RecordError(err)
            return err
        }
        
        span.SetAttributes(
            attribute.String("task.id", task.ID),
            attribute.String("task.type", task.Type),
        )
        
        // 处理任务
        switch task.Type {
        case "email":
            return sendEmail(ctx, task.Payload)
        case "notification":
            return sendNotification(ctx, task.Payload)
        default:
            return fmt.Errorf("unknown task type: %s", task.Type)
        }
    })
}
```

### 4.2 发布订阅模式

```go
// PubSub 发布订阅
type PubSub struct {
    producer *TracedProducer
    consumer *TracedConsumer
}

// Publish 发布事件
func (ps *PubSub) Publish(ctx context.Context, eventType string, payload interface{}) error {
    tracer := otel.Tracer("pubsub")
    ctx, span := tracer.Start(ctx, "publish-event")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("event.type", eventType),
    )
    
    body, err := json.Marshal(payload)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    err = ps.producer.Publish(ctx, "events", eventType, false, false, amqp.Publishing{
        ContentType: "application/json",
        Body:        body,
    })
    
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "event published")
    return nil
}

// Subscribe 订阅事件
func (ps *PubSub) Subscribe(
    ctx context.Context,
    eventType string,
    handler func(context.Context, []byte) error,
) error {
    // 声明 exchange
    err := ps.consumer.ch.ExchangeDeclare(
        "events",  // name
        "topic",   // type
        true,      // durable
        false,     // auto-deleted
        false,     // internal
        false,     // no-wait
        nil,       // arguments
    )
    if err != nil {
        return err
    }
    
    // 声明队列
    q, err := ps.consumer.ch.QueueDeclare(
        "",    // name (auto-generated)
        false, // durable
        true,  // delete when unused
        true,  // exclusive
        false, // no-wait
        nil,   // arguments
    )
    if err != nil {
        return err
    }
    
    // 绑定队列
    err = ps.consumer.ch.QueueBind(
        q.Name,     // queue name
        eventType,  // routing key
        "events",   // exchange
        false,
        nil,
    )
    if err != nil {
        return err
    }
    
    return ps.consumer.Consume(ctx, q.Name, func(ctx context.Context, msg amqp.Delivery) error {
        return handler(ctx, msg.Body)
    })
}
```

---

## 5. 完整示例

### 5.1 订单处理系统

```go
package main

import (
    "context"
    "encoding/json"
    "log"
    "time"
    
    "your-project/rabbitmq"
)

type Order struct {
    ID        string    `json:"id"`
    UserID    string    `json:"user_id"`
    Amount    float64   `json:"amount"`
    Status    string    `json:"status"`
    CreatedAt time.Time `json:"created_at"`
}

type OrderService struct {
    producer *rabbitmq.TracedProducer
    consumer *rabbitmq.TracedConsumer
}

func NewOrderService(url string) (*OrderService, error) {
    producer, err := rabbitmq.NewTracedProducer(url)
    if err != nil {
        return nil, err
    }
    
    consumer, err := rabbitmq.NewTracedConsumer(url)
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
    
    // 发布订单创建事件
    body, _ := json.Marshal(order)
    err := s.producer.Publish(ctx, "orders", "order.created", false, false, amqp.Publishing{
        ContentType:  "application/json",
        Body:         body,
        DeliveryMode: amqp.Persistent,
    })
    
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "order created")
    return nil
}

// ProcessOrders 处理订单
func (s *OrderService) ProcessOrders(ctx context.Context) error {
    return s.consumer.Consume(ctx, "orders", func(ctx context.Context, msg amqp.Delivery) error {
        tracer := otel.Tracer("order-processor")
        ctx, span := tracer.Start(ctx, "process-order")
        defer span.End()
        
        var order Order
        if err := json.Unmarshal(msg.Body, &order); err != nil {
            span.RecordError(err)
            return err
        }
        
        span.SetAttributes(
            attribute.String("order.id", order.ID),
        )
        
        // 处理订单逻辑
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
        
        span.SetStatus(codes.Ok, "order processed")
        return nil
    })
}

func checkInventory(ctx context.Context, order Order) error {
    // 实现库存检查
    time.Sleep(100 * time.Millisecond)
    return nil
}

func processPayment(ctx context.Context, order Order) error {
    // 实现支付处理
    time.Sleep(200 * time.Millisecond)
    return nil
}

func shipOrder(ctx context.Context, order Order) error {
    // 实现发货
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
    
    // 创建订单服务
    service, err := NewOrderService("amqp://admin:admin@localhost:5672/")
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

### 6.1 连接池

```go
type ConnectionPool struct {
    url   string
    conns chan *amqp.Connection
    size  int
}

func NewConnectionPool(url string, size int) (*ConnectionPool, error) {
    pool := &ConnectionPool{
        url:   url,
        conns: make(chan *amqp.Connection, size),
        size:  size,
    }
    
    for i := 0; i < size; i++ {
        conn, err := amqp.Dial(url)
        if err != nil {
            return nil, err
        }
        pool.conns <- conn
    }
    
    return pool, nil
}

func (p *ConnectionPool) Get() *amqp.Connection {
    return <-p.conns
}

func (p *ConnectionPool) Put(conn *amqp.Connection) {
    p.conns <- conn
}
```

### 6.2 批量发布

```go
// BatchPublish 批量发布
func BatchPublish(ctx context.Context, producer *TracedProducer, messages []amqp.Publishing) error {
    tracer := otel.Tracer("batch-publisher")
    ctx, span := tracer.Start(ctx, "batch-publish")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("batch.size", len(messages)),
    )
    
    for _, msg := range messages {
        if err := producer.Publish(ctx, "", "queue", false, false, msg); err != nil {
            span.RecordError(err)
            return err
        }
    }
    
    span.SetStatus(codes.Ok, fmt.Sprintf("published %d messages", len(messages)))
    return nil
}
```

---

## 7. 最佳实践

### 7.1 消息持久化

```go
// 持久化队列
queue, err := ch.QueueDeclare(
    "durable-queue",
    true,  // durable = true
    false,
    false,
    false,
    nil,
)

// 持久化消息
err = ch.Publish(
    "",
    "durable-queue",
    false,
    false,
    amqp.Publishing{
        DeliveryMode: amqp.Persistent,  // 持久化
        ContentType:  "application/json",
        Body:         body,
    },
)
```

### 7.2 死信队列

```go
// 声明死信交换机
err := ch.ExchangeDeclare("dlx", "direct", true, false, false, false, nil)

// 声明主队列（配置死信）
_, err = ch.QueueDeclare(
    "main-queue",
    true,
    false,
    false,
    false,
    amqp.Table{
        "x-dead-letter-exchange":    "dlx",
        "x-dead-letter-routing-key": "dead-letter",
        "x-message-ttl":             30000, // 30秒TTL
    },
)

// 声明死信队列
_, err = ch.QueueDeclare("dead-letter-queue", true, false, false, false, nil)
err = ch.QueueBind("dead-letter-queue", "dead-letter", "dlx", false, nil)
```

---

## 8. 总结

### 8.1 优势与劣势

```text
✅ 优势:
  - 功能丰富，路由灵活
  - 可靠性高，消息确认
  - 管理界面完善
  - 生态成熟

❌ 劣势:
  - 性能不如 Kafka/NATS
  - 配置复杂
  - 资源占用较高
```

**相关文档**:

- [52_事件驱动架构_NATS与Kafka集成.md](../52_事件驱动架构_NATS与Kafka集成.md)

---

**更新日期**: 2025-10-11  
**RabbitMQ 版本**: 3.13+  
**性能级别**: ⭐⭐⭐⭐  
**推荐指数**: ⭐⭐⭐⭐⭐

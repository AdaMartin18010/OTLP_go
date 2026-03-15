# NSQ 与 OTLP 完整集成（2025版）

> **NSQ 版本**: v1.3.0+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [1. NSQ 概述](#1-nsq-概述)
- [2. 快速开始](#2-快速开始)
- [3. 完整集成示例](#3-完整集成示例)
- [4. 高级特性](#4-高级特性)
- [5. 生产部署](#5-生产部署)
- [6. 最佳实践](#6-最佳实践)

---

## 1. NSQ 概述

**NSQ** 是一个实时分布式消息平台，专为大规模分布式系统设计。

```text
🚀 核心特性:
  ✅ 分布式 - 无单点故障
  ✅ 高性能 - 单机 50K+ msg/s
  ✅ 简单部署 - 无依赖，单一二进制
  ✅ 消息持久化 - 磁盘队列
  ✅ 发现服务 - nsqlookupd 自动发现
  ✅ 负载均衡 - 自动分发消息

📊 适用场景:
  - 异步任务处理
  - 事件通知
  - 日志收集
  - 实时数据流
  - 微服务解耦
```

### 1.1 NSQ vs Kafka vs RabbitMQ

```text
┌───────────────┬─────────┬─────────┬──────────┐
│   特性        │   NSQ   │  Kafka  │ RabbitMQ │
├───────────────┼─────────┼─────────┼──────────┤
│ 吞吐量        │   50K   │  1000K  │   20K    │
│ 延迟          │   5ms   │  10ms   │   1ms    │
│ 持久化        │   ✅    │   ✅    │   ✅     │
│ 顺序保证      │   ❌    │   ✅    │   ✅     │
│ 分区          │   ❌    │   ✅    │   ❌     │
│ 部署复杂度    │   低    │   高    │   中     │
│ 依赖          │   无    │  ZK/KRaft│  Erlang │
└───────────────┴─────────┴─────────┴──────────┘

✅ 选择 NSQ:
  - 需要简单部署
  - 不需要消息顺序保证
  - 中等吞吐量需求
  - 多语言支持

✅ 选择 Kafka:
  - 需要高吞吐量
  - 需要消息顺序
  - 需要数据replay
  - 流处理

✅ 选择 RabbitMQ:
  - 需要复杂路由
  - 需要低延迟
  - 需要事务支持
  - AMQP协议
```

---

## 2. 快速开始

### 2.1 安装 NSQ

```bash
# macOS
brew install nsq

# Linux
wget https://s3.amazonaws.com/bitly-downloads/nsq/nsq-1.3.0.linux-amd64.go1.21.5.tar.gz
tar zxvf nsq-1.3.0.linux-amd64.go1.21.5.tar.gz
cd nsq-1.3.0.linux-amd64.go1.21.5/bin

# 启动 nsqlookupd (服务发现)
./nsqlookupd &

# 启动 nsqd (消息代理)
./nsqd --lookupd-tcp-address=127.0.0.1:4160 &

# 启动 nsqadmin (Web管理界面)
./nsqadmin --lookupd-http-address=127.0.0.1:4161 &
```

访问 `http://localhost:4171` 查看管理界面。

### 2.2 依赖安装

```bash
# 安装 NSQ Go客户端
go get -u github.com/nsqio/go-nsq@v1.1.0

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u go.opentelemetry.io/otel/propagation@v1.32.0
```

### 2.3 基础集成

```go
package main

import (
    "context"
    "encoding/json"
    "log"
    "time"

    "github.com/nsqio/go-nsq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
    "go.opentelemetry.io/otel/trace"
)

// Message 消息结构
type Message struct {
    ID        string                 `json:"id"`
    Data      map[string]interface{} `json:"data"`
    Timestamp time.Time              `json:"timestamp"`
    TraceID   string                 `json:"trace_id"`
    SpanID    string                 `json:"span_id"`
}

// 初始化Tracer
func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("nsq-demo"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return tp, nil
}

// Producer 生产者
type Producer struct {
    producer *nsq.Producer
    tracer   trace.Tracer
}

func NewProducer(nsqdAddr string) (*Producer, error) {
    config := nsq.NewConfig()
    producer, err := nsq.NewProducer(nsqdAddr, config)
    if err != nil {
        return nil, err
    }

    return &Producer{
        producer: producer,
        tracer:   otel.Tracer("nsq-producer"),
    }, nil
}

// Publish 发布消息
func (p *Producer) Publish(ctx context.Context, topic string, data map[string]interface{}) error {
    _, span := p.tracer.Start(ctx, "NSQ.Publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "nsq"),
            attribute.String("messaging.destination", topic),
        ),
    )
    defer span.End()

    // 创建消息
    msg := Message{
        ID:        fmt.Sprintf("%d", time.Now().UnixNano()),
        Data:      data,
        Timestamp: time.Now(),
        TraceID:   span.SpanContext().TraceID().String(),
        SpanID:    span.SpanContext().SpanID().String(),
    }

    // 序列化
    body, err := json.Marshal(msg)
    if err != nil {
        span.RecordError(err)
        return err
    }

    // 发布消息
    if err := p.producer.Publish(topic, body); err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(
        attribute.String("message.id", msg.ID),
        attribute.Int("message.size", len(body)),
    )

    return nil
}

// Consumer 消费者
type Consumer struct {
    consumer *nsq.Consumer
    tracer   trace.Tracer
}

// MessageHandler 消息处理器
type MessageHandler struct {
    tracer trace.Tracer
}

func (h *MessageHandler) HandleMessage(message *nsq.Message) error {
    // 解析消息
    var msg Message
    if err := json.Unmarshal(message.Body, &msg); err != nil {
        log.Printf("Failed to unmarshal message: %v", err)
        return err
    }

    // 提取追踪上下文
    traceID, _ := trace.TraceIDFromHex(msg.TraceID)
    spanID, _ := trace.SpanIDFromHex(msg.SpanID)

    spanContext := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID: traceID,
        SpanID:  spanID,
        TraceFlags: trace.FlagsSampled,
    })

    ctx := trace.ContextWithSpanContext(context.Background(), spanContext)

    // 创建消费者 span
    ctx, span := h.tracer.Start(ctx, "NSQ.Consume",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("messaging.system", "nsq"),
            attribute.String("message.id", msg.ID),
        ),
    )
    defer span.End()

    // 处理消息
    log.Printf("Received message: %s, Data: %+v", msg.ID, msg.Data)

    // 模拟处理
    time.Sleep(100 * time.Millisecond)

    return nil
}

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 创建生产者
    producer, err := NewProducer("127.0.0.1:4150")
    if err != nil {
        log.Fatal(err)
    }

    // 发布消息
    ctx := context.Background()
    for i := 0; i < 10; i++ {
        err := producer.Publish(ctx, "test-topic", map[string]interface{}{
            "index": i,
            "text":  fmt.Sprintf("Message %d", i),
        })
        if err != nil {
            log.Printf("Failed to publish: %v", err)
        }
        time.Sleep(1 * time.Second)
    }

    // 创建消费者
    config := nsq.NewConfig()
    consumer, err := nsq.NewConsumer("test-topic", "test-channel", config)
    if err != nil {
        log.Fatal(err)
    }

    // 设置处理器
    handler := &MessageHandler{
        tracer: otel.Tracer("nsq-consumer"),
    }
    consumer.AddHandler(handler)

    // 连接到 nsqlookupd
    err = consumer.ConnectToNSQLookupd("127.0.0.1:4161")
    if err != nil {
        log.Fatal(err)
    }

    // 等待中断信号
    select {}
}
```

---

## 3. 完整集成示例

### 3.1 高级生产者

```go
package producer

import (
    "context"
    "encoding/json"
    "fmt"
    "sync"
    "time"

    "github.com/nsqio/go-nsq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// NSQProducer 高级生产者
type NSQProducer struct {
    producers map[string]*nsq.Producer
    mu        sync.RWMutex
    config    *nsq.Config
    tracer    trace.Tracer
}

func NewNSQProducer() *NSQProducer {
    config := nsq.NewConfig()
    config.MaxInFlight = 200
    config.MaxRequeueDelay = 15 * time.Minute
    config.DefaultRequeueDelay = 90 * time.Second

    return &NSQProducer{
        producers: make(map[string]*nsq.Producer),
        config:    config,
        tracer:    otel.Tracer("nsq-advanced-producer"),
    }
}

// getOrCreateProducer 获取或创建生产者
func (p *NSQProducer) getOrCreateProducer(nsqdAddr string) (*nsq.Producer, error) {
    p.mu.RLock()
    producer, exists := p.producers[nsqdAddr]
    p.mu.RUnlock()

    if exists {
        return producer, nil
    }

    p.mu.Lock()
    defer p.mu.Unlock()

    // 双重检查
    producer, exists = p.producers[nsqdAddr]
    if exists {
        return producer, nil
    }

    // 创建新生产者
    producer, err := nsq.NewProducer(nsqdAddr, p.config)
    if err != nil {
        return nil, err
    }

    p.producers[nsqdAddr] = producer
    return producer, nil
}

// PublishMessage 发布消息
type PublishMessage struct {
    Topic   string
    Body    []byte
    Delay   time.Duration
    Context context.Context
}

func (p *NSQProducer) Publish(msg *PublishMessage) error {
    ctx, span := p.tracer.Start(msg.Context, "NSQ.Publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "nsq"),
            attribute.String("messaging.destination", msg.Topic),
            attribute.Int("message.size", len(msg.Body)),
        ),
    )
    defer span.End()

    producer, err := p.getOrCreateProducer("127.0.0.1:4150")
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to get producer")
        return err
    }

    // 带延迟的发布
    if msg.Delay > 0 {
        err = producer.DeferredPublish(msg.Topic, msg.Delay, msg.Body)
        span.SetAttributes(attribute.Int64("message.delay_ms", msg.Delay.Milliseconds()))
    } else {
        err = producer.Publish(msg.Topic, msg.Body)
    }

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to publish message")
        return err
    }

    span.SetStatus(codes.Ok, "Message published successfully")
    return nil
}

// PublishMulti 批量发布
func (p *NSQProducer) PublishMulti(ctx context.Context, topic string, messages [][]byte) error {
    ctx, span := p.tracer.Start(ctx, "NSQ.PublishMulti",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            attribute.String("messaging.system", "nsq"),
            attribute.String("messaging.destination", topic),
            attribute.Int("message.count", len(messages)),
        ),
    )
    defer span.End()

    producer, err := p.getOrCreateProducer("127.0.0.1:4150")
    if err != nil {
        span.RecordError(err)
        return err
    }

    if err := producer.MultiPublish(topic, messages); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to publish messages")
        return err
    }

    span.SetStatus(codes.Ok, "Messages published successfully")
    return nil
}

// Stop 停止所有生产者
func (p *NSQProducer) Stop() {
    p.mu.Lock()
    defer p.mu.Unlock()

    for _, producer := range p.producers {
        producer.Stop()
    }

    p.producers = make(map[string]*nsq.Producer)
}
```

### 3.2 高级消费者

```go
package consumer

import (
    "context"
    "encoding/json"
    "log"
    "sync"
    "time"

    "github.com/nsqio/go-nsq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// NSQConsumer 高级消费者
type NSQConsumer struct {
    consumer      *nsq.Consumer
    tracer        trace.Tracer
    handler       MessageProcessFunc
    concurrency   int
    maxAttempts   uint16
    requeueDelay  time.Duration
    metrics       *ConsumerMetrics
}

// MessageProcessFunc 消息处理函数
type MessageProcessFunc func(context.Context, *Message) error

// ConsumerMetrics 消费者指标
type ConsumerMetrics struct {
    mu              sync.RWMutex
    TotalReceived   int64
    TotalProcessed  int64
    TotalFailed     int64
    TotalRequeued   int64
}

// ConsumerConfig 消费者配置
type ConsumerConfig struct {
    Topic           string
    Channel         string
    NSQLookupdAddrs []string
    Concurrency     int
    MaxAttempts     uint16
    RequeueDelay    time.Duration
    Handler         MessageProcessFunc
}

func NewNSQConsumer(cfg *ConsumerConfig) (*NSQConsumer, error) {
    config := nsq.NewConfig()
    config.MaxInFlight = cfg.Concurrency
    config.MaxAttempts = cfg.MaxAttempts
    config.DefaultRequeueDelay = cfg.RequeueDelay

    consumer, err := nsq.NewConsumer(cfg.Topic, cfg.Channel, config)
    if err != nil {
        return nil, err
    }

    c := &NSQConsumer{
        consumer:     consumer,
        tracer:       otel.Tracer("nsq-advanced-consumer"),
        handler:      cfg.Handler,
        concurrency:  cfg.Concurrency,
        maxAttempts:  cfg.MaxAttempts,
        requeueDelay: cfg.RequeueDelay,
        metrics:      &ConsumerMetrics{},
    }

    // 设置处理器
    consumer.AddConcurrentHandlers(c, cfg.Concurrency)

    // 连接到 nsqlookupd
    for _, addr := range cfg.NSQLookupdAddrs {
        if err := consumer.ConnectToNSQLookupd(addr); err != nil {
            return nil, err
        }
    }

    return c, nil
}

// HandleMessage 实现 nsq.Handler 接口
func (c *NSQConsumer) HandleMessage(message *nsq.Message) error {
    // 更新指标
    c.metrics.mu.Lock()
    c.metrics.TotalReceived++
    c.metrics.mu.Unlock()

    // 解析消息
    var msg Message
    if err := json.Unmarshal(message.Body, &msg); err != nil {
        log.Printf("Failed to unmarshal message: %v", err)
        c.metrics.mu.Lock()
        c.metrics.TotalFailed++
        c.metrics.mu.Unlock()
        return err
    }

    // 提取追踪上下文
    ctx := extractTraceContext(&msg)

    // 创建 span
    ctx, span := c.tracer.Start(ctx, "NSQ.ProcessMessage",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("messaging.system", "nsq"),
            attribute.String("message.id", msg.ID),
            attribute.Int("message.attempts", int(message.Attempts)),
        ),
    )
    defer span.End()

    // 处理消息
    if err := c.handler(ctx, &msg); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "Failed to process message")

        c.metrics.mu.Lock()
        c.metrics.TotalFailed++
        c.metrics.mu.Unlock()

        // 如果未达到最大重试次数，重新入队
        if message.Attempts < c.maxAttempts {
            message.Requeue(c.requeueDelay)
            c.metrics.mu.Lock()
            c.metrics.TotalRequeued++
            c.metrics.mu.Unlock()
            return nil
        }

        return err
    }

    // 更新成功指标
    c.metrics.mu.Lock()
    c.metrics.TotalProcessed++
    c.metrics.mu.Unlock()

    span.SetStatus(codes.Ok, "Message processed successfully")
    return nil
}

// GetMetrics 获取指标
func (c *NSQConsumer) GetMetrics() ConsumerMetrics {
    c.metrics.mu.RLock()
    defer c.metrics.mu.RUnlock()

    return ConsumerMetrics{
        TotalReceived:  c.metrics.TotalReceived,
        TotalProcessed: c.metrics.TotalProcessed,
        TotalFailed:    c.metrics.TotalFailed,
        TotalRequeued:  c.metrics.TotalRequeued,
    }
}

// Stop 停止消费者
func (c *NSQConsumer) Stop() {
    c.consumer.Stop()
    <-c.consumer.StopChan
}

// extractTraceContext 提取追踪上下文
func extractTraceContext(msg *Message) context.Context {
    traceID, err := trace.TraceIDFromHex(msg.TraceID)
    if err != nil {
        return context.Background()
    }

    spanID, err := trace.SpanIDFromHex(msg.SpanID)
    if err != nil {
        return context.Background()
    }

    spanContext := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    traceID,
        SpanID:     spanID,
        TraceFlags: trace.FlagsSampled,
    })

    return trace.ContextWithSpanContext(context.Background(), spanContext)
}
```

### 3.3 实战：异步任务处理系统

```go
package taskqueue

import (
    "context"
    "encoding/json"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Task 任务定义
type Task struct {
    ID        string                 `json:"id"`
    Type      string                 `json:"type"`
    Payload   map[string]interface{} `json:"payload"`
    Priority  int                    `json:"priority"`
    MaxRetry  int                    `json:"max_retry"`
    CreatedAt time.Time              `json:"created_at"`
    TraceID   string                 `json:"trace_id"`
    SpanID    string                 `json:"span_id"`
}

// TaskQueue 任务队列
type TaskQueue struct {
    producer *NSQProducer
    tracer   trace.Tracer
}

func NewTaskQueue(producer *NSQProducer) *TaskQueue {
    return &TaskQueue{
        producer: producer,
        tracer:   otel.Tracer("task-queue"),
    }
}

// EnqueueTask 入队任务
func (q *TaskQueue) EnqueueTask(ctx context.Context, task *Task) error {
    ctx, span := q.tracer.Start(ctx, "TaskQueue.Enqueue",
        trace.WithAttributes(
            attribute.String("task.id", task.ID),
            attribute.String("task.type", task.Type),
            attribute.Int("task.priority", task.Priority),
        ),
    )
    defer span.End()

    // 设置追踪信息
    task.TraceID = span.SpanContext().TraceID().String()
    task.SpanID = span.SpanContext().SpanID().String()
    task.CreatedAt = time.Now()

    // 序列化任务
    body, err := json.Marshal(task)
    if err != nil {
        span.RecordError(err)
        return err
    }

    // 根据优先级选择不同的topic
    topic := fmt.Sprintf("tasks-%s", getPriorityLevel(task.Priority))

    // 发布任务
    err = q.producer.Publish(&PublishMessage{
        Topic:   topic,
        Body:    body,
        Context: ctx,
    })

    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// TaskWorker 任务处理器
type TaskWorker struct {
    consumers []*NSQConsumer
    handlers  map[string]TaskHandlerFunc
    tracer    trace.Tracer
}

// TaskHandlerFunc 任务处理函数
type TaskHandlerFunc func(context.Context, *Task) error

func NewTaskWorker() *TaskWorker {
    return &TaskWorker{
        consumers: make([]*NSQConsumer, 0),
        handlers:  make(map[string]TaskHandlerFunc),
        tracer:    otel.Tracer("task-worker"),
    }
}

// RegisterHandler 注册任务处理器
func (w *TaskWorker) RegisterHandler(taskType string, handler TaskHandlerFunc) {
    w.handlers[taskType] = handler
}

// Start 启动工作器
func (w *TaskWorker) Start(priorities []string) error {
    for _, priority := range priorities {
        topic := fmt.Sprintf("tasks-%s", priority)
        channel := fmt.Sprintf("workers-%s", priority)

        consumer, err := NewNSQConsumer(&ConsumerConfig{
            Topic:           topic,
            Channel:         channel,
            NSQLookupdAddrs: []string{"127.0.0.1:4161"},
            Concurrency:     getConcurrency(priority),
            MaxAttempts:     3,
            RequeueDelay:    5 * time.Second,
            Handler:         w.processTask,
        })

        if err != nil {
            return err
        }

        w.consumers = append(w.consumers, consumer)
    }

    return nil
}

// processTask 处理任务
func (w *TaskWorker) processTask(ctx context.Context, msg *Message) error {
    // 解析任务
    var task Task
    if err := json.Unmarshal([]byte(msg.Data["raw"].(string)), &task); err != nil {
        return err
    }

    ctx, span := w.tracer.Start(ctx, "TaskWorker.Process",
        trace.WithAttributes(
            attribute.String("task.id", task.ID),
            attribute.String("task.type", task.Type),
        ),
    )
    defer span.End()

    // 查找处理器
    handler, exists := w.handlers[task.Type]
    if !exists {
        err := fmt.Errorf("no handler for task type: %s", task.Type)
        span.RecordError(err)
        return err
    }

    // 执行处理器
    if err := handler(ctx, &task); err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// Stop 停止所有消费者
func (w *TaskWorker) Stop() {
    for _, consumer := range w.consumers {
        consumer.Stop()
    }
}

// 辅助函数
func getPriorityLevel(priority int) string {
    switch {
    case priority >= 80:
        return "high"
    case priority >= 50:
        return "medium"
    default:
        return "low"
    }
}

func getConcurrency(priority string) int {
    switch priority {
    case "high":
        return 20
    case "medium":
        return 10
    default:
        return 5
    }
}

// 使用示例
func ExampleUsage() {
    ctx := context.Background()

    // 创建任务队列
    producer := NewNSQProducer()
    queue := NewTaskQueue(producer)

    // 入队任务
    task := &Task{
        ID:       "task-001",
        Type:     "send-email",
        Payload:  map[string]interface{}{
            "to":      "user@example.com",
            "subject": "Hello",
            "body":    "Welcome!",
        },
        Priority: 80,
        MaxRetry: 3,
    }

    queue.EnqueueTask(ctx, task)

    // 创建工作器
    worker := NewTaskWorker()
    
    // 注册处理器
    worker.RegisterHandler("send-email", func(ctx context.Context, task *Task) error {
        // 发送邮件逻辑
        log.Printf("Sending email to: %s", task.Payload["to"])
        return nil
    })

    // 启动工作器
    worker.Start([]string{"high", "medium", "low"})

    // 等待中断
    select {}
}
```

---

## 4. 高级特性

### 4.1 消息去重

```go
package dedup

import (
    "context"
    "sync"
    "time"

    "github.com/go-redis/redis/v8"
)

// MessageDeduplicator 消息去重器
type MessageDeduplicator struct {
    redis  *redis.Client
    ttl    time.Duration
    mu     sync.RWMutex
    local  map[string]time.Time
}

func NewMessageDeduplicator(redisClient *redis.Client, ttl time.Duration) *MessageDeduplicator {
    d := &MessageDeduplicator{
        redis: redisClient,
        ttl:   ttl,
        local: make(map[string]time.Time),
    }

    // 启动本地缓存清理
    go d.cleanupLocal()

    return d
}

// IsDuplicate 检查是否重复
func (d *MessageDeduplicator) IsDuplicate(ctx context.Context, messageID string) (bool, error) {
    // 1. 检查本地缓存
    d.mu.RLock()
    if _, exists := d.local[messageID]; exists {
        d.mu.RUnlock()
        return true, nil
    }
    d.mu.RUnlock()

    // 2. 检查 Redis
    key := fmt.Sprintf("nsq:msg:%s", messageID)
    result, err := d.redis.SetNX(ctx, key, "1", d.ttl).Result()
    if err != nil {
        return false, err
    }

    if !result {
        return true, nil // Redis中已存在
    }

    // 3. 添加到本地缓存
    d.mu.Lock()
    d.local[messageID] = time.Now().Add(d.ttl)
    d.mu.Unlock()

    return false, nil
}

// cleanupLocal 清理过期的本地缓存
func (d *MessageDeduplicator) cleanupLocal() {
    ticker := time.NewTicker(1 * time.Minute)
    defer ticker.Stop()

    for range ticker.C {
        now := time.Now()
        d.mu.Lock()
        for id, expiry := range d.local {
            if now.After(expiry) {
                delete(d.local, id)
            }
        }
        d.mu.Unlock()
    }
}
```

### 4.2 死信队列

```go
package deadletter

import (
    "context"
    "encoding/json"
    "time"

    "github.com/nsqio/go-nsq"
)

// DeadLetterQueue 死信队列
type DeadLetterQueue struct {
    producer *nsq.Producer
    topic    string
}

func NewDeadLetterQueue(nsqdAddr, topic string) (*DeadLetterQueue, error) {
    config := nsq.NewConfig()
    producer, err := nsq.NewProducer(nsqdAddr, config)
    if err != nil {
        return nil, err
    }

    return &DeadLetterQueue{
        producer: producer,
        topic:    topic,
    }, nil
}

// DeadLetter 死信消息
type DeadLetter struct {
    OriginalTopic   string      `json:"original_topic"`
    OriginalChannel string      `json:"original_channel"`
    MessageID       string      `json:"message_id"`
    Body            []byte      `json:"body"`
    Attempts        uint16      `json:"attempts"`
    Error           string      `json:"error"`
    Timestamp       time.Time   `json:"timestamp"`
}

// Send 发送到死信队列
func (dlq *DeadLetterQueue) Send(ctx context.Context, msg *nsq.Message, err error) error {
    deadLetter := DeadLetter{
        OriginalTopic:   "",  // NSQ doesn't expose topic in message
        OriginalChannel: "",  // NSQ doesn't expose channel in message
        MessageID:       string(msg.ID[:]),
        Body:            msg.Body,
        Attempts:        msg.Attempts,
        Error:           err.Error(),
        Timestamp:       time.Now(),
    }

    body, marshalErr := json.Marshal(deadLetter)
    if marshalErr != nil {
        return marshalErr
    }

    return dlq.producer.Publish(dlq.topic, body)
}
```

---

## 5. 生产部署

### 5.1 Docker Compose 部署

```yaml
version: '3.8'

services:
  nsqlookupd:
    image: nsqio/nsq:latest
    command: /nsqlookupd
    ports:
      - "4160:4160"  # TCP
      - "4161:4161"  # HTTP
    restart: unless-stopped

  nsqd-1:
    image: nsqio/nsq:latest
    command: /nsqd --lookupd-tcp-address=nsqlookupd:4160 --broadcast-address=nsqd-1
    ports:
      - "4150:4150"  # TCP
      - "4151:4151"  # HTTP
    depends_on:
      - nsqlookupd
    restart: unless-stopped
    volumes:
      - nsqd-1-data:/data

  nsqd-2:
    image: nsqio/nsq:latest
    command: /nsqd --lookupd-tcp-address=nsqlookupd:4160 --broadcast-address=nsqd-2
    ports:
      - "4152:4150"
      - "4153:4151"
    depends_on:
      - nsqlookupd
    restart: unless-stopped
    volumes:
      - nsqd-2-data:/data

  nsqadmin:
    image: nsqio/nsq:latest
    command: /nsqadmin --lookupd-http-address=nsqlookupd:4161
    ports:
      - "4171:4171"
    depends_on:
      - nsqlookupd
    restart: unless-stopped

volumes:
  nsqd-1-data:
  nsqd-2-data:
```

### 5.2 Kubernetes 部署

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: nsqd
spec:
  serviceName: nsqd
  replicas: 3
  selector:
    matchLabels:
      app: nsqd
  template:
    metadata:
      labels:
        app: nsqd
    spec:
      containers:
      - name: nsqd
        image: nsqio/nsq:latest
        command:
        - /nsqd
        - --lookupd-tcp-address=nsqlookupd:4160
        - --broadcast-address=$(POD_NAME).nsqd.$(NAMESPACE).svc.cluster.local
        ports:
        - containerPort: 4150
          name: tcp
        - containerPort: 4151
          name: http
        env:
        - name: POD_NAME
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        - name: NAMESPACE
          valueFrom:
            fieldRef:
              fieldPath: metadata.namespace
        volumeMounts:
        - name: data
          mountPath: /data
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: ["ReadWriteOnce"]
      resources:
        requests:
          storage: 10Gi
```

---

## 6. 最佳实践

### 6.1 性能优化

```text
✅ 生产者优化:
  - 使用连接池
  - 批量发布消息
  - 异步发布
  - 合理设置超时

✅ 消费者优化:
  - 设置合适的并发数
  - 实现幂等性
  - 使用消息去重
  - 合理的重试策略

✅ 系统配置:
  - mem-queue-size: 10000
  - max-msg-size: 1MB
  - max-msg-timeout: 15m
  - max-req-timeout: 60s
```

### 6.2 监控指标

```text
✅ 关键指标:
  - 消息发布速率
  - 消息消费速率
  - 队列深度
  - 消费延迟
  - 重试次数
  - 失败率

✅ 告警规则:
  - 队列积压 > 10000
  - 消费延迟 > 5分钟
  - 失败率 > 5%
  - 重试率 > 20%
```

---

**参考资源**：

- [NSQ官方文档](https://nsq.io/)
- [NSQ GitHub](https://github.com/nsqio/nsq)
- [go-nsq客户端](https://github.com/nsqio/go-nsq)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)


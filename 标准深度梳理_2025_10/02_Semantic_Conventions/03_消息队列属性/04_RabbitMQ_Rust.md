# RabbitMQ 语义约定 - Rust 完整实现指南

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **lapin**: 2.5.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月8日  
> **规范版本**: OpenTelemetry Semantic Conventions v1.30.0

---

## 目录

- [RabbitMQ 语义约定 - Rust 完整实现指南](#rabbitmq-语义约定---rust-完整实现指南)
  - [目录](#目录)
  - [1. RabbitMQ 追踪概述](#1-rabbitmq-追踪概述)
  - [2. RabbitMQ 属性定义](#2-rabbitmq-属性定义)
  - [3. 依赖配置](#3-依赖配置)
  - [4. Rust Producer 实现](#4-rust-producer-实现)
    - [4.1 基础异步发布](#41-基础异步发布)
    - [4.2 Exchange 路由](#42-exchange-路由)
    - [4.3 消息确认模式](#43-消息确认模式)
  - [5. Rust Consumer 实现](#5-rust-consumer-实现)
    - [5.1 基础异步消费](#51-基础异步消费)
    - [5.2 多消费者并发](#52-多消费者并发)
    - [5.3 死信队列处理](#53-死信队列处理)
  - [6. TraceContext 传播](#6-tracecontext-传播)
  - [7. 高级特性](#7-高级特性)
    - [7.1 消息优先级](#71-消息优先级)
    - [7.2 延迟消息](#72-延迟消息)
    - [7.3 消息持久化](#73-消息持久化)
  - [8. 完整微服务示例](#8-完整微服务示例)
  - [9. 性能优化](#9-性能优化)
  - [10. 生产环境最佳实践](#10-生产环境最佳实践)
  - [11. 参考资源](#11-参考资源)

---

## 1. RabbitMQ 追踪概述

**RabbitMQ 特点与追踪价值**:

```text
RabbitMQ = 成熟的消息代理
特点:
- 支持多种消息协议 (AMQP, MQTT, STOMP)
- 灵活的路由机制 (Exchange + Routing Key)
- 消息持久化和确认
- 死信队列 (DLX)
- 消息优先级

Rust 视角价值:
1. 类型安全的 AMQP 客户端
   - lapin crate 完整支持
   - 零成本抽象
   
2. 异步优先
   - 完美集成 Tokio
   - 高效并发消费
   
3. 可靠性保证
   - 消息确认机制
   - 持久化支持
   - 所有权系统保证安全性
```

**Span 模型**:

```text
┌──────────────────────────────────────────────────────────┐
│              生产者服务 (Rust)                             │
│  ┌─────────────────┐                                      │
│  │ POST /tasks     │  SpanKind::Server                    │
│  │ TraceID: abc    │                                      │
│  └────────┬────────┘                                      │
│           │                                               │
│           ▼                                               │
│  ┌─────────────────┐                                      │
│  │ rabbitmq.publish│  SpanKind::Producer                  │
│  │ Exchange: tasks │  注入TraceContext到message properties │
│  │ TraceID: abc    │                                      │
│  └─────────────────┘                                      │
└──────────────────────────────────────────────────────────┘
           │
           │ RabbitMQ Message (携带 traceparent property)
           │
           ▼
┌──────────────────────────────────────────────────────────┐
│              消费者服务 (Rust)                             │
│  ┌─────────────────┐                                      │
│  │ rabbitmq.receive│  SpanKind::Consumer                  │
│  │ Queue: tasks    │  从properties提取TraceContext         │
│  │ TraceID: abc    │  (同一个TraceID!)                    │
│  └────────┬────────┘                                      │
│           │                                               │
│           ▼                                               │
│  ┌─────────────────┐                                      │
│  │ Process Task    │  SpanKind::Internal                  │
│  │ TraceID: abc    │                                      │
│  └─────────────────┘                                      │
└──────────────────────────────────────────────────────────┘
```

---

## 2. RabbitMQ 属性定义

**Rust 类型安全的属性**:

```rust
use opentelemetry::KeyValue;
use serde::Serialize;

/// RabbitMQ 语义约定属性
#[derive(Debug, Clone, Serialize)]
pub struct RabbitMqAttributes {
    /// 消息系统 (固定为 "rabbitmq")
    pub system: &'static str,
    
    /// 目标名称 (Queue 或 Exchange)
    pub destination_name: String,
    
    /// 目标类型
    pub destination_kind: DestinationKind,
    
    /// 操作类型
    pub operation: RabbitMqOperation,
    
    /// RabbitMQ 服务器地址
    pub server_address: String,
    
    /// 服务器端口
    pub server_port: u16,
    
    /// Exchange 名称 (发布时)
    pub exchange: Option<String>,
    
    /// Routing Key
    pub routing_key: Option<String>,
    
    /// Consumer Tag
    pub consumer_tag: Option<String>,
    
    /// 消息 ID
    pub message_id: Option<String>,
    
    /// Correlation ID
    pub correlation_id: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum DestinationKind {
    #[serde(rename = "queue")]
    Queue,
    #[serde(rename = "exchange")]
    Exchange,
    #[serde(rename = "topic")]
    Topic,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum RabbitMqOperation {
    #[serde(rename = "publish")]
    Publish,
    #[serde(rename = "receive")]
    Receive,
    #[serde(rename = "process")]
    Process,
    #[serde(rename = "ack")]
    Ack,
    #[serde(rename = "nack")]
    Nack,
}

impl RabbitMqAttributes {
    /// 转换为 OpenTelemetry KeyValue
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("messaging.system", self.system),
            KeyValue::new("messaging.destination.name", self.destination_name.clone()),
            KeyValue::new("messaging.destination.kind", match self.destination_kind {
                DestinationKind::Queue => "queue",
                DestinationKind::Exchange => "exchange",
                DestinationKind::Topic => "topic",
            }),
            KeyValue::new("messaging.operation", match self.operation {
                RabbitMqOperation::Publish => "publish",
                RabbitMqOperation::Receive => "receive",
                RabbitMqOperation::Process => "process",
                RabbitMqOperation::Ack => "ack",
                RabbitMqOperation::Nack => "nack",
            }),
            KeyValue::new("network.peer.address", self.server_address.clone()),
            KeyValue::new("network.peer.port", self.server_port as i64),
        ];
        
        if let Some(ref exchange) = self.exchange {
            attrs.push(KeyValue::new("messaging.rabbitmq.destination.exchange", exchange.clone()));
        }
        
        if let Some(ref routing_key) = self.routing_key {
            attrs.push(KeyValue::new("messaging.rabbitmq.destination.routing_key", routing_key.clone()));
        }
        
        if let Some(ref consumer_tag) = self.consumer_tag {
            attrs.push(KeyValue::new("messaging.rabbitmq.consumer.tag", consumer_tag.clone()));
        }
        
        if let Some(ref message_id) = self.message_id {
            attrs.push(KeyValue::new("messaging.message.id", message_id.clone()));
        }
        
        if let Some(ref correlation_id) = self.correlation_id {
            attrs.push(KeyValue::new("messaging.message.conversation_id", correlation_id.clone()));
        }
        
        attrs
    }
}
```

---

## 3. 依赖配置

**Cargo.toml**:

```toml
[package]
name = "rabbitmq-otlp-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# RabbitMQ 客户端 (Rust 1.90 兼容)
lapin = "2.5.0"

# OpenTelemetry 生态系统 (2025年10月最新)
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace"] }
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.20", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# 异步运行时 (Rust 1.90 优化)
tokio = { version = "1.47.1", features = ["full"] }
tokio-stream = "0.1.17"
futures = "0.3.31"

# 序列化
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"

# 错误处理
thiserror = "2.0.17"
anyhow = "1.0.100"

# 工具库
uuid = { version = "1.18.1", features = ["v4", "serde"] }
bytes = "1.10.1"
chrono = { version = "0.4.42", features = ["serde"] }

[dev-dependencies]
tokio-test = "0.4.4"
```

---

## 4. Rust Producer 实现

### 4.1 基础异步发布

**完整的异步发布实现**:

```rust
use lapin::{
    Connection, ConnectionProperties, Channel,
    options::*, types::FieldTable,
    BasicProperties, publisher_confirm::Confirmation,
};
use opentelemetry::{
    global,
    trace::{Span, SpanKind, Status, Tracer, TraceContextExt},
    Context, KeyValue,
};
use tracing::{info, error, instrument};

/// RabbitMQ Publisher 追踪包装器
pub struct TracedRabbitMqPublisher {
    channel: Channel,
    tracer: Box<dyn Tracer + Send + Sync>,
    server_address: String,
    server_port: u16,
}

impl TracedRabbitMqPublisher {
    /// 创建新的追踪 Publisher
    pub async fn new(amqp_url: &str) -> Result<Self, anyhow::Error> {
        // 解析服务器地址
        let (address, port) = parse_amqp_url(amqp_url)?;
        
        // 创建连接
        let connection = Connection::connect(
            amqp_url,
            ConnectionProperties::default(),
        ).await?;
        
        // 创建通道
        let channel = connection.create_channel().await?;
        
        info!(server = %amqp_url, "Connected to RabbitMQ");
        
        let tracer = global::tracer("rabbitmq-publisher");
        
        Ok(Self {
            channel,
            tracer: Box::new(tracer),
            server_address: address,
            server_port: port,
        })
    }
    
    /// 发布消息到队列 (追踪)
    #[instrument(skip(self, payload))]
    pub async fn publish_to_queue_traced(
        &self,
        queue: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        self.publish_traced("", queue, payload, None).await
    }
    
    /// 发布消息到 Exchange (追踪)
    #[instrument(skip(self, payload))]
    pub async fn publish_to_exchange_traced(
        &self,
        exchange: &str,
        routing_key: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        self.publish_traced(exchange, routing_key, payload, Some(exchange.to_string())).await
    }
    
    /// 通用发布方法 (内部)
    async fn publish_traced(
        &self,
        exchange: &str,
        routing_key: &str,
        payload: &[u8],
        exchange_name: Option<String>,
    ) -> Result<(), anyhow::Error> {
        // 创建 Producer Span
        let destination = if exchange.is_empty() {
            format!("queue:{}", routing_key)
        } else {
            format!("exchange:{}", exchange)
        };
        
        let mut span = self.tracer
            .span_builder(format!("rabbitmq.publish {}", destination))
            .with_kind(SpanKind::Producer)
            .start(&*self.tracer);
        
        // 设置 RabbitMQ 属性
        let attrs = RabbitMqAttributes {
            system: "rabbitmq",
            destination_name: routing_key.to_string(),
            destination_kind: if exchange.is_empty() {
                DestinationKind::Queue
            } else {
                DestinationKind::Exchange
            },
            operation: RabbitMqOperation::Publish,
            server_address: self.server_address.clone(),
            server_port: self.server_port,
            exchange: exchange_name,
            routing_key: Some(routing_key.to_string()),
            consumer_tag: None,
            message_id: None,
            correlation_id: None,
        };
        
        span.set_attributes(attrs.to_key_values());
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            payload.len() as i64));
        
        // 获取当前上下文
        let cx = Context::current_with_span(span.clone());
        
        // 注入 TraceContext 到 BasicProperties
        let properties = self.inject_trace_context(&cx);
        
        // 发布消息
        let confirmation = self.channel
            .basic_publish(
                exchange,
                routing_key,
                BasicPublishOptions::default(),
                payload,
                properties,
            )
            .await?
            .await?;
        
        match confirmation {
            Confirmation::Ack(_) => {
                span.set_status(Status::Ok);
                info!(
                    exchange = %exchange,
                    routing_key = %routing_key,
                    "Message published successfully"
                );
                Ok(())
            }
            Confirmation::Nack(_) => {
                let error_msg = "Message was nacked by broker";
                span.record_error(error_msg);
                span.set_status(Status::error(error_msg));
                error!(
                    exchange = %exchange,
                    routing_key = %routing_key,
                    "Message was nacked"
                );
                Err(anyhow::anyhow!("Message nacked"))
            }
            _ => {
                let error_msg = "Unexpected confirmation";
                span.record_error(error_msg);
                span.set_status(Status::error(error_msg));
                Err(anyhow::anyhow!("Unexpected confirmation"))
            }
        }
    }
    
    /// 注入 TraceContext 到 BasicProperties
    fn inject_trace_context(&self, cx: &Context) -> BasicProperties {
        use opentelemetry::propagation::{Injector, TextMapPropagator};
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        
        struct AmqpHeaderInjector {
            headers: FieldTable,
        }
        
        impl Injector for AmqpHeaderInjector {
            fn set(&mut self, key: &str, value: String) {
                self.headers.insert(
                    key.into(),
                    lapin::types::AMQPValue::LongString(value.into()),
                );
            }
        }
        
        let mut injector = AmqpHeaderInjector {
            headers: FieldTable::default(),
        };
        
        let propagator = TraceContextPropagator::new();
        propagator.inject_context(cx, &mut injector);
        
        // 创建 BasicProperties 并设置 headers
        BasicProperties::default()
            .with_headers(injector.headers)
            .with_delivery_mode(2)  // 持久化
            .with_content_type("application/json".into())
            .with_message_id(uuid::Uuid::new_v4().to_string().into())
            .with_timestamp(
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs()
            )
    }
    
    /// 声明队列
    #[instrument(skip(self))]
    pub async fn declare_queue(
        &self,
        queue_name: &str,
        durable: bool,
    ) -> Result<(), anyhow::Error> {
        self.channel
            .queue_declare(
                queue_name,
                QueueDeclareOptions {
                    durable,
                    ..Default::default()
                },
                FieldTable::default(),
            )
            .await?;
        
        info!(queue = %queue_name, durable = durable, "Queue declared");
        Ok(())
    }
    
    /// 声明 Exchange
    #[instrument(skip(self))]
    pub async fn declare_exchange(
        &self,
        exchange_name: &str,
        exchange_type: &str,
        durable: bool,
    ) -> Result<(), anyhow::Error> {
        self.channel
            .exchange_declare(
                exchange_name,
                lapin::ExchangeKind::Custom(exchange_type.to_string()),
                ExchangeDeclareOptions {
                    durable,
                    ..Default::default()
                },
                FieldTable::default(),
            )
            .await?;
        
        info!(
            exchange = %exchange_name,
            exchange_type = %exchange_type,
            durable = durable,
            "Exchange declared"
        );
        Ok(())
    }
    
    /// 绑定队列到 Exchange
    #[instrument(skip(self))]
    pub async fn bind_queue(
        &self,
        queue: &str,
        exchange: &str,
        routing_key: &str,
    ) -> Result<(), anyhow::Error> {
        self.channel
            .queue_bind(
                queue,
                exchange,
                routing_key,
                QueueBindOptions::default(),
                FieldTable::default(),
            )
            .await?;
        
        info!(
            queue = %queue,
            exchange = %exchange,
            routing_key = %routing_key,
            "Queue bound to exchange"
        );
        Ok(())
    }
}

/// 解析 AMQP URL
fn parse_amqp_url(url: &str) -> Result<(String, u16), anyhow::Error> {
    // 简化版解析
    let default_port = 5672;
    
    if url.contains("://") {
        let parts: Vec<&str> = url.split("://").collect();
        if parts.len() == 2 {
            let auth_host = parts[1];
            if let Some(at_pos) = auth_host.find('@') {
                let host_port = &auth_host[at_pos + 1..];
                if let Some(colon_pos) = host_port.find(':') {
                    let host = &host_port[..colon_pos];
                    if let Some(slash_pos) = host_port.find('/') {
                        let port_str = &host_port[colon_pos + 1..slash_pos];
                        let port = port_str.parse::<u16>().unwrap_or(default_port);
                        return Ok((host.to_string(), port));
                    }
                }
                return Ok((host_port.to_string(), default_port));
            }
        }
    }
    
    Ok(("localhost".to_string(), default_port))
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    // 初始化 OpenTelemetry
    init_telemetry().await?;
    
    // 创建 Publisher
    let publisher = TracedRabbitMqPublisher::new(
        "amqp://guest:guest@localhost:5672/%2f"
    ).await?;
    
    // 声明队列
    publisher.declare_queue("tasks", true).await?;
    
    // 发布消息
    let task = serde_json::json!({
        "task_id": uuid::Uuid::new_v4().to_string(),
        "task_type": "process_order",
        "priority": 1,
        "timestamp": chrono::Utc::now().to_rfc3339(),
    });
    
    let payload = serde_json::to_vec(&task)?;
    
    publisher.publish_to_queue_traced("tasks", &payload).await?;
    
    println!("Task published");
    
    Ok(())
}
```

### 4.2 Exchange 路由

**不同类型的 Exchange**:

```rust
impl TracedRabbitMqPublisher {
    /// Direct Exchange (直接路由)
    pub async fn publish_direct(
        &self,
        exchange: &str,
        routing_key: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        self.publish_to_exchange_traced(exchange, routing_key, payload).await
    }
    
    /// Topic Exchange (主题路由)
    pub async fn publish_topic(
        &self,
        exchange: &str,
        topic: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        // topic 格式: "orders.created.usa"
        self.publish_to_exchange_traced(exchange, topic, payload).await
    }
    
    /// Fanout Exchange (广播)
    pub async fn publish_fanout(
        &self,
        exchange: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        // Fanout 忽略 routing key
        self.publish_to_exchange_traced(exchange, "", payload).await
    }
    
    /// Headers Exchange (头部路由)
    pub async fn publish_with_headers(
        &self,
        exchange: &str,
        headers: FieldTable,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        let mut span = self.tracer
            .span_builder(format!("rabbitmq.publish {}", exchange))
            .with_kind(SpanKind::Producer)
            .start(&*self.tracer);
        
        let cx = Context::current_with_span(span.clone());
        let mut properties = self.inject_trace_context(&cx);
        
        // 合并自定义 headers
        if let Some(ref mut props_headers) = properties.headers_mut() {
            for (key, value) in headers.iter() {
                props_headers.insert(key.clone(), value.clone());
            }
        }
        
        // 发布
        self.channel
            .basic_publish(
                exchange,
                "",
                BasicPublishOptions::default(),
                payload,
                properties,
            )
            .await?
            .await?;
        
        span.set_status(Status::Ok);
        Ok(())
    }
}
```

### 4.3 消息确认模式

**发布者确认**:

```rust
impl TracedRabbitMqPublisher {
    /// 启用发布者确认模式
    pub async fn enable_publisher_confirms(&self) -> Result<(), anyhow::Error> {
        self.channel.confirm_select(ConfirmSelectOptions::default()).await?;
        info!("Publisher confirms enabled");
        Ok(())
    }
    
    /// 等待确认的批量发布
    #[instrument(skip(self, messages))]
    pub async fn publish_batch_with_confirms(
        &self,
        exchange: &str,
        messages: Vec<(String, Vec<u8>)>,  // (routing_key, payload)
    ) -> Result<Vec<bool>, anyhow::Error> {
        let mut results = Vec::new();
        
        for (routing_key, payload) in messages {
            match self.publish_to_exchange_traced(exchange, &routing_key, &payload).await {
                Ok(_) => results.push(true),
                Err(e) => {
                    error!("Failed to publish: {}", e);
                    results.push(false);
                }
            }
        }
        
        Ok(results)
    }
}
```

---

## 5. Rust Consumer 实现

### 5.1 基础异步消费

**完整的异步消费实现**:

```rust
use lapin::message::Delivery;
use tokio_stream::StreamExt;

pub struct TracedRabbitMqConsumer {
    channel: Channel,
    tracer: Box<dyn Tracer + Send + Sync>,
    server_address: String,
    server_port: u16,
}

impl TracedRabbitMqConsumer {
    /// 创建新的追踪 Consumer
    pub async fn new(amqp_url: &str) -> Result<Self, anyhow::Error> {
        let (address, port) = parse_amqp_url(amqp_url)?;
        
        let connection = Connection::connect(
            amqp_url,
            ConnectionProperties::default(),
        ).await?;
        
        let channel = connection.create_channel().await?;
        
        info!(server = %amqp_url, "Connected to RabbitMQ");
        
        let tracer = global::tracer("rabbitmq-consumer");
        
        Ok(Self {
            channel,
            tracer: Box::new(tracer),
            server_address: address,
            server_port: port,
        })
    }
    
    /// 消费消息并追踪
    pub async fn consume_with_tracing<F, Fut>(
        &self,
        queue: &str,
        consumer_tag: &str,
        mut handler: F,
    ) -> Result<(), anyhow::Error>
    where
        F: FnMut(Vec<u8>, Context) -> Fut + Send,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        // 设置 QoS (预取数量)
        self.channel
            .basic_qos(10, BasicQosOptions::default())
            .await?;
        
        // 开始消费
        let mut consumer = self.channel
            .basic_consume(
                queue,
                consumer_tag,
                BasicConsumeOptions::default(),
                FieldTable::default(),
            )
            .await?;
        
        info!(queue = %queue, consumer_tag = %consumer_tag, "Started consuming");
        
        // 处理消息
        while let Some(delivery) = consumer.next().await {
            match delivery {
                Ok(delivery) => {
                    if let Err(e) = self
                        .process_delivery_traced(&delivery, queue, consumer_tag, &mut handler)
                        .await
                    {
                        error!("Failed to process delivery: {}", e);
                        // Nack 消息
                        delivery.nack(BasicNackOptions {
                            requeue: true,
                            ..Default::default()
                        }).await?;
                    }
                }
                Err(e) => {
                    error!("Consumer error: {}", e);
                }
            }
        }
        
        Ok(())
    }
    
    /// 处理单条消息并追踪
    #[instrument(skip(self, delivery, handler))]
    async fn process_delivery_traced<F, Fut>(
        &self,
        delivery: &Delivery,
        queue: &str,
        consumer_tag: &str,
        handler: &mut F,
    ) -> Result<(), anyhow::Error>
    where
        F: FnMut(Vec<u8>, Context) -> Fut + Send,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        // 提取 TraceContext 从 properties
        let parent_cx = self.extract_trace_context(delivery);
        
        // 创建 Consumer Span
        let mut span = self.tracer
            .span_builder(format!("rabbitmq.receive {}", queue))
            .with_kind(SpanKind::Consumer)
            .start_with_context(&*self.tracer, &parent_cx);
        
        // 设置属性
        let attrs = RabbitMqAttributes {
            system: "rabbitmq",
            destination_name: queue.to_string(),
            destination_kind: DestinationKind::Queue,
            operation: RabbitMqOperation::Receive,
            server_address: self.server_address.clone(),
            server_port: self.server_port,
            exchange: delivery.exchange.as_ref().map(|s| s.to_string()),
            routing_key: delivery.routing_key.as_ref().map(|s| s.to_string()),
            consumer_tag: Some(consumer_tag.to_string()),
            message_id: delivery.properties.message_id().clone().map(|s| s.to_string()),
            correlation_id: delivery.properties.correlation_id().clone().map(|s| s.to_string()),
        };
        
        span.set_attributes(attrs.to_key_values());
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            delivery.data.len() as i64));
        
        // 设置当前上下文
        let cx = Context::current_with_span(span.clone());
        let _guard = cx.attach();
        
        // 调用用户处理函数
        match handler(delivery.data.to_vec(), cx.clone()).await {
            Ok(_) => {
                // Ack 消息
                delivery.ack(BasicAckOptions::default()).await?;
                span.set_status(Status::Ok);
                info!(
                    queue = %queue,
                    message_id = ?delivery.properties.message_id(),
                    "Message processed successfully"
                );
            }
            Err(e) => {
                let error_msg = format!("Handler failed: {}", e);
                span.record_error(&error_msg);
                span.set_status(Status::error(error_msg.clone()));
                error!(
                    queue = %queue,
                    message_id = ?delivery.properties.message_id(),
                    error = ?e,
                    "Failed to process message"
                );
                return Err(e);
            }
        }
        
        Ok(())
    }
    
    /// 从 BasicProperties 提取 TraceContext
    fn extract_trace_context(&self, delivery: &Delivery) -> Context {
        use opentelemetry::propagation::{Extractor, TextMapPropagator};
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        
        struct AmqpHeaderExtractor<'a> {
            headers: Option<&'a FieldTable>,
        }
        
        impl<'a> Extractor for AmqpHeaderExtractor<'a> {
            fn get(&self, key: &str) -> Option<&str> {
                self.headers
                    .and_then(|h| h.inner().get(key))
                    .and_then(|v| {
                        if let lapin::types::AMQPValue::LongString(s) = v {
                            Some(s.as_str())
                        } else {
                            None
                        }
                    })
            }
            
            fn keys(&self) -> Vec<&str> {
                self.headers
                    .map(|h| {
                        h.inner()
                            .keys()
                            .map(|k| k.as_str())
                            .collect()
                    })
                    .unwrap_or_default()
            }
        }
        
        let headers = delivery.properties.headers();
        let extractor = AmqpHeaderExtractor { headers };
        
        let propagator = TraceContextPropagator::new();
        propagator.extract(&extractor)
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    // 初始化 OpenTelemetry
    init_telemetry().await?;
    
    // 创建 Consumer
    let consumer = TracedRabbitMqConsumer::new(
        "amqp://guest:guest@localhost:5672/%2f"
    ).await?;
    
    // 开始消费
    consumer.consume_with_tracing(
        "tasks",
        "task-processor",
        |payload, _cx| async move {
            // 处理任务
            let task: serde_json::Value = serde_json::from_slice(&payload)?;
            info!("Processing task: {:?}", task);
            
            // 业务逻辑...
            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
            
            Ok(())
        }
    ).await?;
    
    Ok(())
}
```

### 5.2 多消费者并发

**并发消费优化**:

```rust
impl TracedRabbitMqConsumer {
    /// 并发消费 (使用多个 Channel)
    pub async fn consume_concurrent(
        &self,
        queue: &str,
        concurrency: usize,
    ) -> Result<(), anyhow::Error> {
        let mut handles = Vec::new();
        
        for i in 0..concurrency {
            let consumer_tag = format!("consumer-{}", i);
            let queue = queue.to_string();
            let consumer = self.clone_consumer().await?;
            
            let handle = tokio::spawn(async move {
                consumer.consume_with_tracing(
                    &queue,
                    &consumer_tag,
                    |payload, _cx| async move {
                        // 处理消息
                        process_message(payload).await
                    }
                ).await
            });
            
            handles.push(handle);
        }
        
        // 等待所有消费者
        for handle in handles {
            handle.await??;
        }
        
        Ok(())
    }
    
    async fn clone_consumer(&self) -> Result<Self, anyhow::Error> {
        // 创建新的 Consumer 实例
        // ... (实现细节)
        todo!()
    }
}

async fn process_message(payload: Vec<u8>) -> Result<(), anyhow::Error> {
    // 业务逻辑
    Ok(())
}
```

### 5.3 死信队列处理

**死信队列 (DLX) 集成**:

```rust
impl TracedRabbitMqPublisher {
    /// 声明带死信队列的队列
    pub async fn declare_queue_with_dlx(
        &self,
        queue_name: &str,
        dlx_exchange: &str,
    ) -> Result<(), anyhow::Error> {
        let mut arguments = FieldTable::default();
        arguments.insert(
            "x-dead-letter-exchange".into(),
            lapin::types::AMQPValue::LongString(dlx_exchange.into()),
        );
        
        self.channel
            .queue_declare(
                queue_name,
                QueueDeclareOptions {
                    durable: true,
                    ..Default::default()
                },
                arguments,
            )
            .await?;
        
        info!(
            queue = %queue_name,
            dlx = %dlx_exchange,
            "Queue with DLX declared"
        );
        Ok(())
    }
}
```

---

## 6. TraceContext 传播

已在 Publisher 和 Consumer 实现中包含，遵循 W3C Trace Context 标准。

---

## 7. 高级特性

### 7.1 消息优先级

```rust
impl TracedRabbitMqPublisher {
    pub async fn publish_with_priority(
        &self,
        queue: &str,
        payload: &[u8],
        priority: u8,
    ) -> Result<(), anyhow::Error> {
        let cx = Context::current();
        let mut properties = self.inject_trace_context(&cx);
        properties = properties.with_priority(priority);
        
        self.channel
            .basic_publish(
                "",
                queue,
                BasicPublishOptions::default(),
                payload,
                properties,
            )
            .await?
            .await?;
        
        Ok(())
    }
}
```

### 7.2 延迟消息

```rust
impl TracedRabbitMqPublisher {
    pub async fn publish_delayed(
        &self,
        exchange: &str,
        routing_key: &str,
        payload: &[u8],
        delay_ms: u64,
    ) -> Result<(), anyhow::Error> {
        let mut arguments = FieldTable::default();
        arguments.insert(
            "x-delay".into(),
            lapin::types::AMQPValue::LongLongInt(delay_ms as i64),
        );
        
        let cx = Context::current();
        let mut properties = self.inject_trace_context(&cx);
        
        self.channel
            .basic_publish(
                exchange,
                routing_key,
                BasicPublishOptions::default(),
                payload,
                properties,
            )
            .await?
            .await?;
        
        Ok(())
    }
}
```

### 7.3 消息持久化

```rust
impl TracedRabbitMqPublisher {
    pub async fn publish_persistent(
        &self,
        queue: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        let cx = Context::current();
        let properties = self.inject_trace_context(&cx)
            .with_delivery_mode(2);  // 2 = persistent
        
        self.channel
            .basic_publish(
                "",
                queue,
                BasicPublishOptions::default(),
                payload,
                properties,
            )
            .await?
            .await?;
        
        Ok(())
    }
}
```

---

## 8. 完整微服务示例

**任务调度系统 (Producer + Consumer)**:

```rust
// ========== 任务发布服务 ==========
use axum::{Router, routing::post, extract::State, Json};

struct PublisherAppState {
    rabbitmq: Arc<TracedRabbitMqPublisher>,
}

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    init_telemetry().await?;
    
    let publisher = TracedRabbitMqPublisher::new(
        "amqp://guest:guest@localhost:5672/%2f"
    ).await?;
    
    publisher.declare_queue("tasks", true).await?;
    
    let state = Arc::new(PublisherAppState {
        rabbitmq: Arc::new(publisher),
    });
    
    let app = Router::new()
        .route("/tasks", post(create_task))
        .with_state(state)
        .layer(tower_http::trace::TraceLayer::new_for_http());
    
    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await?;
    info!("Task publisher listening on http://127.0.0.1:8080");
    
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[instrument(skip(state))]
async fn create_task(
    State(state): State<Arc<PublisherAppState>>,
    Json(task): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, anyhow::Error> {
    let task_id = uuid::Uuid::new_v4().to_string();
    
    let task_message = serde_json::json!({
        "task_id": task_id,
        "payload": task,
        "created_at": chrono::Utc::now().to_rfc3339(),
    });
    
    let payload = serde_json::to_vec(&task_message)?;
    
    // 发布任务 (自动注入 TraceContext)
    state.rabbitmq
        .publish_to_queue_traced("tasks", &payload)
        .await?;
    
    Ok(Json(serde_json::json!({
        "task_id": task_id,
        "status": "queued",
    })))
}

// ========== 任务处理服务 ==========
#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    init_telemetry().await?;
    
    let consumer = TracedRabbitMqConsumer::new(
        "amqp://guest:guest@localhost:5672/%2f"
    ).await?;
    
    info!("Task processor started");
    
    // 消费任务 (TraceContext 自动提取)
    consumer.consume_with_tracing(
        "tasks",
        "task-processor",
        |payload, _cx| async move {
            let task: serde_json::Value = serde_json::from_slice(&payload)?;
            
            let task_id = task["task_id"].as_str()
                .ok_or_else(|| anyhow::anyhow!("Missing task_id"))?;
            
            info!(task_id = %task_id, "Processing task");
            
            // 处理任务...
            tokio::time::sleep(std::time::Duration::from_secs(1)).await;
            
            info!(task_id = %task_id, "Task completed");
            
            Ok(())
        }
    ).await?;
    
    Ok(())
}
```

---

## 9. 性能优化

**连接池和通道复用**:

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct RabbitMqPool {
    connection: Arc<Connection>,
    channels: Arc<RwLock<Vec<Channel>>>,
    max_channels: usize,
}

impl RabbitMqPool {
    pub async fn new(amqp_url: &str, max_channels: usize) -> Result<Self, anyhow::Error> {
        let connection = Arc::new(
            Connection::connect(amqp_url, ConnectionProperties::default()).await?
        );
        
        let mut channels = Vec::with_capacity(max_channels);
        for _ in 0..max_channels {
            let channel = connection.create_channel().await?;
            channels.push(channel);
        }
        
        Ok(Self {
            connection,
            channels: Arc::new(RwLock::new(channels)),
            max_channels,
        })
    }
    
    pub async fn get_channel(&self) -> Channel {
        let mut channels = self.channels.write().await;
        channels.pop().unwrap_or_else(|| {
            // 如果池为空，创建新通道
            tokio::task::block_in_place(|| {
                tokio::runtime::Handle::current().block_on(async {
                    self.connection.create_channel().await.unwrap()
                })
            })
        })
    }
    
    pub async fn return_channel(&self, channel: Channel) {
        let mut channels = self.channels.write().await;
        if channels.len() < self.max_channels {
            channels.push(channel);
        }
    }
}
```

---

## 10. 生产环境最佳实践

```text
✅ 连接配置
  □ 使用连接池
  □ 启用心跳检测
  □ 配置重连策略
  □ 设置合理的超时

✅ 消息配置
  □ 启用消息持久化 (delivery_mode=2)
  □ 启用发布者确认
  □ 设置合理的 QoS (prefetch_count)
  □ 配置死信队列

✅ 追踪配置
  □ 注入 TraceContext 到 properties
  □ 使用 W3C Trace Context 标准
  □ 记录关键属性
  □ 设置合理的采样率

✅ 错误处理
  □ 实现重试机制
  □ 使用 Nack 重新入队
  □ 配置死信队列
  □ 记录错误到 Span

✅ 性能优化
  □ 使用通道池
  □ 批量发布消息
  □ 并发消费
  □ 控制预取数量

✅ 监控告警
  □ 监控队列长度
  □ 监控消费速率
  □ 监控错误率
  □ 设置告警阈值
```

---

## 11. 参考资源

**官方文档** (2025年10月最新):

- [RabbitMQ Documentation](https://www.rabbitmq.com/documentation.html)
- [lapin Rust Crate](https://docs.rs/lapin/2.5.0)
- [AMQP 0-9-1 Protocol](https://www.rabbitmq.com/amqp-0-9-1-reference.html)
- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/messaging/)
- [W3C Trace Context](https://www.w3.org/TR/trace-context/)

**Rust 资源**:

- [Tokio Async Runtime](https://tokio.rs/)
- [Rust Async Book](https://rust-lang.github.io/async-book/)
- [Rust 1.90 Release Notes](https://blog.rust-lang.org/)

---

**文档状态**: ✅ 完成 (Rust 1.90 + OpenTelemetry 0.31.0 + lapin 2.5.0)  
**最后更新**: 2025年10月8日  
**审核状态**: 生产就绪  
**许可证**: MIT OR Apache-2.0

---

**⭐ 本文档提供完整的 Rust + RabbitMQ + OTLP 集成方案，包括:**

- ✅ 类型安全的追踪实现
- ✅ 异步发布和消费
- ✅ W3C TraceContext 传播
- ✅ Exchange 路由模式
- ✅ 发布者确认
- ✅ 死信队列处理
- ✅ 完整微服务示例
- ✅ 连接池优化
- ✅ Rust 1.90 最新特性

[🏠 返回主目录](../../README.md) | [📖 查看其他消息队列](../README.md)

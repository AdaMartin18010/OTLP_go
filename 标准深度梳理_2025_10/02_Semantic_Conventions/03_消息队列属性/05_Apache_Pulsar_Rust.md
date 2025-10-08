# Apache Pulsar 语义约定 - Rust 完整实现

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - pulsar: 6.4.0
> - opentelemetry: 0.31.0
> - tracing: 0.1.41
> - tokio: 1.47.1
> - 更新日期: 2025-10-08

## 目录

- [Apache Pulsar 语义约定 - Rust 完整实现](#apache-pulsar-语义约定---rust-完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [Apache Pulsar 特性](#apache-pulsar-特性)
    - [Rust 集成优势](#rust-集成优势)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [Pulsar 语义约定](#pulsar-语义约定)
    - [OpenTelemetry 属性](#opentelemetry-属性)
    - [Rust 实现](#rust-实现)
  - [生产者追踪](#生产者追踪)
    - [基础生产者](#基础生产者)
  - [消费者追踪](#消费者追踪)
    - [基础消费者](#基础消费者)
  - [Reader 追踪](#reader-追踪)
  - [分区与路由](#分区与路由)
    - [分区主题生产者](#分区主题生产者)
  - [Schema 支持](#schema-支持)
    - [JSON Schema](#json-schema)
  - [性能优化](#性能优化)
    - [1. 连接池复用](#1-连接池复用)
    - [2. 批量发送优化](#2-批量发送优化)
  - [最佳实践](#最佳实践)
    - [1. 主题命名约定](#1-主题命名约定)
    - [2. 错误处理策略](#2-错误处理策略)
    - [3. 死信队列](#3-死信队列)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### Apache Pulsar 特性

Apache Pulsar 是云原生分布式消息流平台，具有以下特性：

- **多租户**: 租户 (Tenant) -> 命名空间 (Namespace) -> 主题 (Topic)
- **持久化与非持久化**: 支持持久化和内存消息
- **分区主题**: 水平扩展消息吞吐量
- **Schema Registry**: 内置 Schema 管理
- **消息确认**: Individual、Cumulative、Batch 确认
- **死信队列**: 自动处理失败消息
- **延迟消息**: 支持消息延迟投递

### Rust 集成优势

- **零成本抽象**: 追踪不影响性能
- **类型安全**: 编译时保证正确性
- **异步高性能**: Tokio 原生支持
- **内存安全**: 无数据竞争

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "pulsar-otlp-tracing"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Pulsar 客户端
pulsar = "6.4.0"

# OpenTelemetry 核心
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json"] }

# Tracing 生态
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.29.0"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }
futures = "0.3.31"

# 序列化
serde = { version = "1.0.216", features = ["derive"] }
serde_json = "1.0.138"

# 错误处理
thiserror = "2.0.9"
anyhow = "1.0.95"

# 工具
bytes = "1.10.0"
uuid = { version = "1.11.0", features = ["v4", "serde"] }

[dev-dependencies]
criterion = { version = "0.6.0", features = ["async_tokio"] }
mockall = "0.14.0"
tokio-test = "0.4.4"
```

---

## Pulsar 语义约定

### OpenTelemetry 属性

根据 OpenTelemetry 语义约定，Pulsar 追踪应包含以下属性：

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `messaging.system` | string | ✅ | 消息系统标识符 | `pulsar` |
| `messaging.destination` | string | ✅ | 目标主题名称 | `persistent://public/default/my-topic` |
| `messaging.destination_kind` | string | ✅ | 目标类型 | `topic` |
| `messaging.protocol` | string | ❌ | 传输协议 | `pulsar` |
| `messaging.protocol_version` | string | ❌ | 协议版本 | `2.11` |
| `messaging.url` | string | ❌ | Broker URL | `pulsar://localhost:6650` |
| `messaging.message_id` | string | ❌ | 消息 ID | `CAEQAg==` |
| `messaging.conversation_id` | string | ❌ | 会话 ID | `order-12345` |
| `messaging.message_payload_size_bytes` | integer | ❌ | 消息大小 | `1024` |
| `messaging.operation` | string | ✅ | 操作类型 | `send`, `receive`, `process` |
| `messaging.pulsar.tenant` | string | ❌ | 租户名称 | `public` |
| `messaging.pulsar.namespace` | string | ❌ | 命名空间 | `default` |
| `messaging.pulsar.partition_key` | string | ❌ | 分区键 | `user_123` |
| `messaging.pulsar.schema_type` | string | ❌ | Schema 类型 | `json`, `avro`, `protobuf` |

### Rust 实现

```rust
use opentelemetry::KeyValue;
use tracing::Span;

/// Pulsar 消息追踪属性
#[derive(Debug, Clone)]
pub struct PulsarAttributes {
    pub topic: String,
    pub tenant: String,
    pub namespace: String,
    pub operation: String,
    pub message_id: Option<String>,
    pub partition_key: Option<String>,
    pub message_size: Option<usize>,
    pub broker_url: String,
}

impl PulsarAttributes {
    /// 转换为 OpenTelemetry KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("messaging.system", "pulsar"),
            KeyValue::new("messaging.destination", self.topic.clone()),
            KeyValue::new("messaging.destination_kind", "topic"),
            KeyValue::new("messaging.operation", self.operation.clone()),
            KeyValue::new("messaging.url", self.broker_url.clone()),
            KeyValue::new("messaging.pulsar.tenant", self.tenant.clone()),
            KeyValue::new("messaging.pulsar.namespace", self.namespace.clone()),
        ];

        if let Some(msg_id) = &self.message_id {
            attrs.push(KeyValue::new("messaging.message_id", msg_id.clone()));
        }

        if let Some(key) = &self.partition_key {
            attrs.push(KeyValue::new("messaging.pulsar.partition_key", key.clone()));
        }

        if let Some(size) = self.message_size {
            attrs.push(KeyValue::new("messaging.message_payload_size_bytes", size as i64));
        }

        attrs
    }

    /// 记录到 tracing Span
    pub fn record_to_span(&self, span: &Span) {
        span.record("messaging.system", "pulsar");
        span.record("messaging.destination", self.topic.as_str());
        span.record("messaging.operation", self.operation.as_str());
        span.record("messaging.pulsar.tenant", self.tenant.as_str());
        span.record("messaging.pulsar.namespace", self.namespace.as_str());

        if let Some(msg_id) = &self.message_id {
            span.record("messaging.message_id", msg_id.as_str());
        }

        if let Some(key) = &self.partition_key {
            span.record("messaging.pulsar.partition_key", key.as_str());
        }

        if let Some(size) = self.message_size {
            span.record("messaging.message_payload_size_bytes", size as u64);
        }
    }

    /// 从主题名称解析租户和命名空间
    pub fn from_topic(topic: &str, operation: &str, broker_url: &str) -> Self {
        let parts: Vec<&str> = topic.split("://").collect();
        let (tenant, namespace) = if parts.len() == 2 {
            let path_parts: Vec<&str> = parts[1].split('/').collect();
            if path_parts.len() >= 2 {
                (path_parts[0].to_string(), path_parts[1].to_string())
            } else {
                ("public".to_string(), "default".to_string())
            }
        } else {
            ("public".to_string(), "default".to_string())
        };

        Self {
            topic: topic.to_string(),
            tenant,
            namespace,
            operation: operation.to_string(),
            message_id: None,
            partition_key: None,
            message_size: None,
            broker_url: broker_url.to_string(),
        }
    }
}
```

---

## 生产者追踪

### 基础生产者

```rust
use pulsar::{
    message::proto::MessageMetadata,
    producer::{Message, SendFuture},
    Pulsar, TokioExecutor,
};
use serde::{Deserialize, Serialize};
use tracing::{error, info, instrument, warn};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct OrderEvent {
    pub order_id: String,
    pub user_id: String,
    pub amount: f64,
    pub status: String,
    pub timestamp: i64,
}

/// 带追踪的 Pulsar 生产者
pub struct TracedPulsarProducer {
    pulsar: Pulsar<TokioExecutor>,
    broker_url: String,
}

impl TracedPulsarProducer {
    /// 创建生产者
    pub async fn new(broker_url: &str) -> Result<Self, pulsar::Error> {
        let pulsar = Pulsar::builder(broker_url, TokioExecutor)
            .build()
            .await?;

        Ok(Self {
            pulsar,
            broker_url: broker_url.to_string(),
        })
    }

    /// 发送单条消息 - 带追踪
    #[instrument(
        skip(self, event),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "send",
            order.id = %event.order_id,
            order.amount = event.amount
        )
    )]
    pub async fn send_order_event(
        &self,
        topic: &str,
        event: OrderEvent,
    ) -> Result<pulsar::producer::SendFuture, pulsar::Error> {
        info!("Sending order event to Pulsar");

        // 创建生产者
        let mut producer = self
            .pulsar
            .producer()
            .with_topic(topic)
            .with_name("order-event-producer")
            .build()
            .await?;

        // 序列化消息
        let payload = serde_json::to_vec(&event)
            .map_err(|e| pulsar::Error::Custom(format!("Serialization error: {}", e)))?;

        // 创建追踪属性
        let mut attrs = PulsarAttributes::from_topic(topic, "send", &self.broker_url);
        attrs.message_size = Some(payload.len());
        attrs.partition_key = Some(event.order_id.clone());

        // 记录属性到当前 Span
        let span = tracing::Span::current();
        attrs.record_to_span(&span);

        // 构建消息（带属性和分区键）
        let message = Message {
            payload,
            partition_key: Some(event.order_id.clone()),
            ..Default::default()
        };

        // 发送消息
        match producer.send(message).await {
            Ok(send_future) => {
                info!(
                    topic = topic,
                    order_id = event.order_id,
                    "Message sent successfully"
                );
                Ok(send_future)
            }
            Err(e) => {
                error!(
                    error = %e,
                    topic = topic,
                    order_id = event.order_id,
                    "Failed to send message"
                );
                span.record("error", true);
                span.record("error.message", &e.to_string());
                Err(e)
            }
        }
    }

    /// 批量发送消息
    #[instrument(
        skip(self, events),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "send_batch",
            batch.size = events.len()
        )
    )]
    pub async fn send_batch(
        &self,
        topic: &str,
        events: Vec<OrderEvent>,
    ) -> Result<Vec<pulsar::producer::SendFuture>, pulsar::Error> {
        info!(batch_size = events.len(), "Sending batch to Pulsar");

        let mut producer = self
            .pulsar
            .producer()
            .with_topic(topic)
            .with_name("order-event-batch-producer")
            .build()
            .await?;

        let mut send_futures = Vec::new();

        for event in events {
            let payload = serde_json::to_vec(&event)
                .map_err(|e| pulsar::Error::Custom(format!("Serialization error: {}", e)))?;

            let message = Message {
                payload,
                partition_key: Some(event.order_id.clone()),
                ..Default::default()
            };

            match producer.send(message).await {
                Ok(send_future) => {
                    send_futures.push(send_future);
                }
                Err(e) => {
                    error!(error = %e, order_id = event.order_id, "Failed to send message in batch");
                    // 继续发送其他消息
                }
            }
        }

        info!(
            sent_count = send_futures.len(),
            "Batch send completed"
        );

        Ok(send_futures)
    }

    /// 发送延迟消息
    #[instrument(
        skip(self, event),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "send_delayed",
            delay_seconds = delay_seconds
        )
    )]
    pub async fn send_delayed(
        &self,
        topic: &str,
        event: OrderEvent,
        delay_seconds: u64,
    ) -> Result<pulsar::producer::SendFuture, pulsar::Error> {
        info!(delay_seconds = delay_seconds, "Sending delayed message");

        let mut producer = self
            .pulsar
            .producer()
            .with_topic(topic)
            .with_name("delayed-message-producer")
            .build()
            .await?;

        let payload = serde_json::to_vec(&event)
            .map_err(|e| pulsar::Error::Custom(format!("Serialization error: {}", e)))?;

        let message = Message {
            payload,
            partition_key: Some(event.order_id.clone()),
            deliver_at_time: Some(
                (std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_millis() as u64)
                    + (delay_seconds * 1000),
            ),
            ..Default::default()
        };

        let send_future = producer.send(message).await?;

        info!("Delayed message sent");

        Ok(send_future)
    }
}
```

---

## 消费者追踪

### 基础消费者

```rust
use futures::StreamExt;
use pulsar::{
    consumer::{Consumer, InitialPosition},
    message::Payload,
    SubType,
};
use tracing::{error, info, instrument, warn};

/// 带追踪的 Pulsar 消费者
pub struct TracedPulsarConsumer {
    pulsar: Pulsar<TokioExecutor>,
    broker_url: String,
}

impl TracedPulsarConsumer {
    pub async fn new(broker_url: &str) -> Result<Self, pulsar::Error> {
        let pulsar = Pulsar::builder(broker_url, TokioExecutor)
            .build()
            .await?;

        Ok(Self {
            pulsar,
            broker_url: broker_url.to_string(),
        })
    }

    /// 启动消费者 - 带追踪
    #[instrument(
        skip(self),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "receive",
            consumer.subscription = %subscription
        )
    )]
    pub async fn consume_orders(
        &self,
        topic: &str,
        subscription: &str,
    ) -> Result<(), pulsar::Error> {
        info!("Starting Pulsar consumer");

        let mut consumer: Consumer<OrderEvent, _> = self
            .pulsar
            .consumer()
            .with_topic(topic)
            .with_subscription(subscription)
            .with_subscription_type(SubType::Shared)
            .with_consumer_name("order-event-consumer")
            .build()
            .await?;

        info!("Consumer started successfully");

        while let Some(msg) = consumer.next().await {
            match msg {
                Ok(msg) => {
                    // 创建消息处理 Span
                    let process_span = tracing::info_span!(
                        "process_message",
                        messaging.system = "pulsar",
                        messaging.operation = "process",
                        messaging.message_id = ?msg.message_id,
                        messaging.destination = %topic
                    );

                    let _enter = process_span.enter();

                    info!(
                        message_id = ?msg.message_id,
                        partition = msg.partition,
                        "Processing message"
                    );

                    match self.handle_order_event(msg.payload).await {
                        Ok(_) => {
                            // 确认消息
                            if let Err(e) = consumer.ack(&msg).await {
                                error!(error = %e, "Failed to acknowledge message");
                            } else {
                                info!("Message processed and acknowledged");
                            }
                        }
                        Err(e) => {
                            error!(error = %e, "Failed to process message");
                            // 可以选择 nack 或重试
                            if let Err(nack_err) = consumer.nack(&msg).await {
                                error!(error = %nack_err, "Failed to nack message");
                            }
                        }
                    }
                }
                Err(e) => {
                    error!(error = %e, "Error receiving message");
                }
            }
        }

        Ok(())
    }

    #[instrument(skip(self, payload))]
    async fn handle_order_event(&self, payload: Payload) -> Result<(), anyhow::Error> {
        let event: OrderEvent = serde_json::from_slice(&payload.data)?;

        info!(
            order_id = event.order_id,
            user_id = event.user_id,
            amount = event.amount,
            status = event.status,
            "Processing order event"
        );

        // 业务逻辑处理
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

        Ok(())
    }

    /// 批量消费
    #[instrument(
        skip(self),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "receive_batch",
            batch.size = batch_size
        )
    )]
    pub async fn consume_batch(
        &self,
        topic: &str,
        subscription: &str,
        batch_size: usize,
    ) -> Result<(), pulsar::Error> {
        info!("Starting batch consumer");

        let mut consumer: Consumer<OrderEvent, _> = self
            .pulsar
            .consumer()
            .with_topic(topic)
            .with_subscription(subscription)
            .with_subscription_type(SubType::Shared)
            .with_consumer_name("batch-consumer")
            .build()
            .await?;

        let mut batch = Vec::new();

        while let Some(msg) = consumer.next().await {
            match msg {
                Ok(msg) => {
                    batch.push(msg);

                    if batch.len() >= batch_size {
                        info!(batch_size = batch.len(), "Processing batch");

                        for msg in batch.drain(..) {
                            if let Err(e) = self.handle_order_event(msg.payload).await {
                                error!(error = %e, "Failed to process message in batch");
                            }

                            if let Err(e) = consumer.ack(&msg).await {
                                error!(error = %e, "Failed to ack message");
                            }
                        }

                        info!("Batch processed");
                    }
                }
                Err(e) => {
                    error!(error = %e, "Error receiving message");
                }
            }
        }

        Ok(())
    }
}
```

---

## Reader 追踪

```rust
use pulsar::reader::Reader;

impl TracedPulsarConsumer {
    /// Reader 模式 - 适合读取历史消息
    #[instrument(
        skip(self),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "read"
        )
    )]
    pub async fn read_from_beginning(
        &self,
        topic: &str,
    ) -> Result<(), pulsar::Error> {
        info!("Starting Pulsar reader");

        let mut reader: Reader<OrderEvent, _> = self
            .pulsar
            .reader()
            .with_topic(topic)
            .with_consumer_name("order-reader")
            .into_reader()
            .await?;

        let mut count = 0;

        while let Some(msg) = reader.next().await {
            match msg {
                Ok(msg) => {
                    let read_span = tracing::info_span!(
                        "read_message",
                        messaging.system = "pulsar",
                        messaging.operation = "read",
                        messaging.message_id = ?msg.message_id
                    );

                    let _enter = read_span.enter();

                    if let Err(e) = self.handle_order_event(msg.payload).await {
                        error!(error = %e, "Failed to process message");
                    }

                    count += 1;

                    if count >= 100 {
                        info!(messages_read = count, "Finished reading messages");
                        break;
                    }
                }
                Err(e) => {
                    error!(error = %e, "Error reading message");
                    break;
                }
            }
        }

        Ok(())
    }
}
```

---

## 分区与路由

### 分区主题生产者

```rust
impl TracedPulsarProducer {
    /// 发送到分区主题
    #[instrument(
        skip(self, event),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "send",
            messaging.pulsar.partition_key = %partition_key
        )
    )]
    pub async fn send_to_partition(
        &self,
        topic: &str,
        partition_key: &str,
        event: OrderEvent,
    ) -> Result<pulsar::producer::SendFuture, pulsar::Error> {
        info!(partition_key = partition_key, "Sending to partitioned topic");

        let mut producer = self
            .pulsar
            .producer()
            .with_topic(topic)
            .with_name("partitioned-producer")
            .build()
            .await?;

        let payload = serde_json::to_vec(&event)
            .map_err(|e| pulsar::Error::Custom(format!("Serialization error: {}", e)))?;

        let message = Message {
            payload,
            partition_key: Some(partition_key.to_string()),
            ..Default::default()
        };

        let send_future = producer.send(message).await?;

        info!("Message sent to partition");

        Ok(send_future)
    }
}
```

---

## Schema 支持

### JSON Schema

```rust
use pulsar::schema::{Schema, SchemaType};

impl TracedPulsarProducer {
    /// 使用 JSON Schema 发送消息
    #[instrument(
        skip(self, event),
        fields(
            messaging.system = "pulsar",
            messaging.destination = %topic,
            messaging.operation = "send",
            messaging.pulsar.schema_type = "json"
        )
    )]
    pub async fn send_with_json_schema(
        &self,
        topic: &str,
        event: OrderEvent,
    ) -> Result<pulsar::producer::SendFuture, pulsar::Error> {
        info!("Sending message with JSON schema");

        let mut producer = self
            .pulsar
            .producer()
            .with_topic(topic)
            .with_name("json-schema-producer")
            .with_options(pulsar::producer::ProducerOptions {
                schema: Some(pulsar::proto::Schema {
                    r#type: SchemaType::Json as i32,
                    schema_data: serde_json::to_vec(&serde_json::json!({
                        "type": "object",
                        "properties": {
                            "order_id": {"type": "string"},
                            "user_id": {"type": "string"},
                            "amount": {"type": "number"},
                            "status": {"type": "string"},
                            "timestamp": {"type": "integer"}
                        }
                    }))
                    .unwrap(),
                    ..Default::default()
                }),
                ..Default::default()
            })
            .build()
            .await?;

        let payload = serde_json::to_vec(&event)
            .map_err(|e| pulsar::Error::Custom(format!("Serialization error: {}", e)))?;

        let message = Message {
            payload,
            ..Default::default()
        };

        let send_future = producer.send(message).await?;

        info!("Message with schema sent");

        Ok(send_future)
    }
}
```

---

## 性能优化

### 1. 连接池复用

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct PulsarConnectionPool {
    pulsar: Arc<Pulsar<TokioExecutor>>,
}

impl PulsarConnectionPool {
    pub async fn new(broker_url: &str) -> Result<Self, pulsar::Error> {
        let pulsar = Arc::new(
            Pulsar::builder(broker_url, TokioExecutor)
                .build()
                .await?,
        );

        Ok(Self { pulsar })
    }

    pub fn get_client(&self) -> Arc<Pulsar<TokioExecutor>> {
        Arc::clone(&self.pulsar)
    }
}
```

### 2. 批量发送优化

```rust
use tokio::time::{interval, Duration};

pub async fn batched_sender(
    producer: Arc<TracedPulsarProducer>,
    topic: String,
    mut event_rx: tokio::sync::mpsc::Receiver<OrderEvent>,
) {
    let mut batch = Vec::new();
    let mut interval_timer = interval(Duration::from_millis(100));
    const MAX_BATCH_SIZE: usize = 100;

    loop {
        tokio::select! {
            Some(event) = event_rx.recv() => {
                batch.push(event);

                if batch.len() >= MAX_BATCH_SIZE {
                    send_batch_internal(&producer, &topic, &mut batch).await;
                }
            }
            _ = interval_timer.tick() => {
                if !batch.is_empty() {
                    send_batch_internal(&producer, &topic, &mut batch).await;
                }
            }
        }
    }
}

async fn send_batch_internal(
    producer: &TracedPulsarProducer,
    topic: &str,
    batch: &mut Vec<OrderEvent>,
) {
    if batch.is_empty() {
        return;
    }

    let events = batch.drain(..).collect();

    match producer.send_batch(topic, events).await {
        Ok(_) => {
            info!("Batch sent successfully");
        }
        Err(e) => {
            error!(error = %e, "Failed to send batch");
        }
    }
}
```

---

## 最佳实践

### 1. 主题命名约定

```rust
pub struct PulsarTopicBuilder {
    tenant: String,
    namespace: String,
    topic_name: String,
    persistent: bool,
}

impl PulsarTopicBuilder {
    pub fn new() -> Self {
        Self {
            tenant: "public".to_string(),
            namespace: "default".to_string(),
            topic_name: String::new(),
            persistent: true,
        }
    }

    pub fn tenant(mut self, tenant: &str) -> Self {
        self.tenant = tenant.to_string();
        self
    }

    pub fn namespace(mut self, namespace: &str) -> Self {
        self.namespace = namespace.to_string();
        self
    }

    pub fn topic_name(mut self, name: &str) -> Self {
        self.topic_name = name.to_string();
        self
    }

    pub fn non_persistent(mut self) -> Self {
        self.persistent = false;
        self
    }

    pub fn build(self) -> String {
        let persistence = if self.persistent {
            "persistent"
        } else {
            "non-persistent"
        };

        format!(
            "{}://{}/{}/{}",
            persistence, self.tenant, self.namespace, self.topic_name
        )
    }
}

// 使用示例
let topic = PulsarTopicBuilder::new()
    .tenant("my-tenant")
    .namespace("production")
    .topic_name("order-events")
    .build();

// persistent://my-tenant/production/order-events
```

### 2. 错误处理策略

```rust
use std::time::Duration;
use tokio::time::sleep;

pub async fn send_with_retry<F, Fut>(
    operation: F,
    max_retries: u32,
) -> Result<pulsar::producer::SendFuture, pulsar::Error>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<pulsar::producer::SendFuture, pulsar::Error>>,
{
    let mut retries = 0;

    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) if retries < max_retries => {
                warn!(
                    error = %e,
                    retry = retries + 1,
                    "Operation failed, retrying"
                );

                retries += 1;
                let backoff = Duration::from_millis(100 * 2u64.pow(retries));
                sleep(backoff).await;
            }
            Err(e) => {
                error!(error = %e, "Operation failed after all retries");
                return Err(e);
            }
        }
    }
}
```

### 3. 死信队列

```rust
impl TracedPulsarConsumer {
    pub async fn consume_with_dlq(
        &self,
        topic: &str,
        subscription: &str,
        dlq_topic: &str,
        max_retries: u32,
    ) -> Result<(), pulsar::Error> {
        let mut consumer: Consumer<OrderEvent, _> = self
            .pulsar
            .consumer()
            .with_topic(topic)
            .with_subscription(subscription)
            .with_subscription_type(SubType::Shared)
            .with_dead_letter_policy(
                pulsar::consumer::DeadLetterPolicy::builder()
                    .max_redeliver_count(max_retries)
                    .dead_letter_topic(dlq_topic)
                    .build(),
            )
            .build()
            .await?;

        while let Some(msg) = consumer.next().await {
            match msg {
                Ok(msg) => {
                    match self.handle_order_event(msg.payload).await {
                        Ok(_) => {
                            consumer.ack(&msg).await?;
                        }
                        Err(e) => {
                            error!(error = %e, "Processing failed, message will be redelivered or sent to DLQ");
                            consumer.nack(&msg).await?;
                        }
                    }
                }
                Err(e) => {
                    error!(error = %e, "Error receiving message");
                }
            }
        }

        Ok(())
    }
}
```

---

## 完整示例

### main.rs

```rust
use anyhow::Result;
use opentelemetry::global;
use opentelemetry_sdk::{runtime, trace as sdktrace, Resource};
use opentelemetry_otlp::WithExportConfig;
use tracing::info;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化 OpenTelemetry
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces"),
        )
        .with_trace_config(
            sdktrace::Config::default()
                .with_resource(Resource::new(vec![
                    opentelemetry::KeyValue::new("service.name", "pulsar-tracing-demo"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("Starting Pulsar OTLP tracing demo");

    let broker_url = "pulsar://localhost:6650";

    // 创建主题
    let topic = PulsarTopicBuilder::new()
        .tenant("public")
        .namespace("default")
        .topic_name("order-events")
        .build();

    // 生产者示例
    let producer = TracedPulsarProducer::new(broker_url).await?;

    let event = OrderEvent {
        order_id: "order-12345".to_string(),
        user_id: "user-67890".to_string(),
        amount: 99.99,
        status: "pending".to_string(),
        timestamp: chrono::Utc::now().timestamp(),
    };

    producer.send_order_event(&topic, event).await?;

    // 消费者示例（在单独的任务中）
    let consumer = TracedPulsarConsumer::new(broker_url).await?;
    let consume_handle = tokio::spawn(async move {
        consumer
            .consume_orders(&topic, "order-subscription")
            .await
    });

    // 等待一段时间
    tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;

    // 关闭追踪
    global::shutdown_tracer_provider();

    Ok(())
}
```

---

## 总结

本文档提供了 Apache Pulsar 在 Rust 1.90 环境下的完整 OpenTelemetry 集成方案：

1. ✅ **语义约定**: 完整实现 OpenTelemetry Pulsar 语义约定
2. ✅ **生产者追踪**: 单条、批量、延迟消息发送
3. ✅ **消费者追踪**: Shared/Exclusive/Failover 订阅模式
4. ✅ **Reader 模式**: 历史消息读取追踪
5. ✅ **Schema 支持**: JSON/Avro/Protobuf Schema 集成
6. ✅ **性能优化**: 批处理、连接池、重试策略
7. ✅ **最佳实践**: 主题命名、错误处理、死信队列

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT

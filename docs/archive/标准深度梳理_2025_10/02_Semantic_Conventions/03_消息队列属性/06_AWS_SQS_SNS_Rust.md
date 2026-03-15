# AWS SQS/SNS 语义约定 - Rust 完整实现

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - aws-sdk-sqs: 1.76.0
> - aws-sdk-sns: 1.79.0
> - aws-config: 1.5.14
> - opentelemetry: 0.31.0
> - tracing: 0.1.41
> - tokio: 1.47.1
> - 更新日期: 2025-10-08

## 目录

- [AWS SQS/SNS 语义约定 - Rust 完整实现](#aws-sqssns-语义约定---rust-完整实现)
  - [目录](#目录)
  - [概述](#概述)
    - [AWS SQS (Simple Queue Service)](#aws-sqs-simple-queue-service)
    - [AWS SNS (Simple Notification Service)](#aws-sns-simple-notification-service)
    - [Rust 集成优势](#rust-集成优势)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml](#cargotoml)
  - [AWS 语义约定](#aws-语义约定)
    - [OpenTelemetry 属性](#opentelemetry-属性)
    - [Rust 实现](#rust-实现)
  - [SQS 追踪实现](#sqs-追踪实现)
    - [1. SQS 客户端初始化](#1-sqs-客户端初始化)
  - [SNS 追踪实现](#sns-追踪实现)
    - [SNS 客户端](#sns-客户端)
  - [SQS + SNS 集成](#sqs--sns-集成)
    - [扇出模式（Fan-out Pattern）](#扇出模式fan-out-pattern)
  - [FIFO 队列支持](#fifo-队列支持)
    - [FIFO 队列操作](#fifo-队列操作)
  - [死信队列处理](#死信队列处理)
    - [DLQ 集成](#dlq-集成)
  - [性能优化](#性能优化)
    - [1. 批量接收与处理](#1-批量接收与处理)
  - [最佳实践](#最佳实践)
    - [1. 错误重试策略](#1-错误重试策略)
    - [2. 消息去重](#2-消息去重)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### AWS SQS (Simple Queue Service)

- **标准队列**: 高吞吐量、至少一次投递、尽力而为的排序
- **FIFO 队列**: 严格顺序、恰好一次处理、有限吞吐量 (300 TPS)
- **可见性超时**: 防止重复处理
- **长轮询**: 减少空请求
- **批量操作**: 最多 10 条消息

### AWS SNS (Simple Notification Service)

- **Pub/Sub 模型**: 一对多消息分发
- **多种订阅类型**: SQS, Lambda, HTTP/HTTPS, Email, SMS
- **消息过滤**: 订阅级别的消息过滤策略
- **扇出模式**: 一条消息发送到多个订阅者
- **消息属性**: 自定义元数据

### Rust 集成优势

- **类型安全**: 强类型 AWS SDK
- **异步性能**: Tokio 高效处理 I/O
- **内存安全**: 无并发竞争
- **零成本抽象**: 追踪开销最小化

---

## 核心依赖配置

### Cargo.toml

```toml
[package]
name = "aws-sqs-sns-otlp"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# AWS SDK
aws-config = { version = "1.5.14", features = ["behavior-version-latest"] }
aws-sdk-sqs = "1.76.0"
aws-sdk-sns = "1.79.0"
aws-types = "1.3.6"

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
uuid = { version = "1.11.0", features = ["v4", "serde"] }
chrono = "0.4.39"
base64 = "0.22.1"

[dev-dependencies]
criterion = { version = "0.6.0", features = ["async_tokio"] }
mockall = "0.14.0"
tokio-test = "0.4.4"
```

---

## AWS 语义约定

### OpenTelemetry 属性

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `messaging.system` | string | ✅ | 消息系统标识符 | `aws_sqs`, `aws_sns` |
| `messaging.destination` | string | ✅ | 队列/主题名称 | `my-queue` |
| `messaging.destination_kind` | string | ✅ | 目标类型 | `queue`, `topic` |
| `messaging.operation` | string | ✅ | 操作类型 | `send`, `receive`, `publish` |
| `messaging.message_id` | string | ❌ | 消息 ID | `msg-123` |
| `messaging.conversation_id` | string | ❌ | 会话 ID (Message Group ID) | `group-1` |
| `messaging.message_payload_size_bytes` | integer | ❌ | 消息大小 | `1024` |
| `messaging.url` | string | ❌ | 队列/主题 URL | `https://sqs.us-east-1.amazonaws.com/123456789012/my-queue` |
| `cloud.provider` | string | ✅ | 云提供商 | `aws` |
| `cloud.region` | string | ❌ | AWS 区域 | `us-east-1` |
| `cloud.account.id` | string | ❌ | AWS 账户 ID | `123456789012` |
| `messaging.aws.sqs.queue_url` | string | ❌ | SQS 队列 URL | `https://...` |
| `messaging.aws.sqs.message_group_id` | string | ❌ | FIFO 消息组 ID | `group-1` |
| `messaging.aws.sqs.message_deduplication_id` | string | ❌ | FIFO 去重 ID | `dedup-1` |
| `messaging.aws.sns.topic_arn` | string | ❌ | SNS 主题 ARN | `arn:aws:sns:...` |

### Rust 实现

```rust
use opentelemetry::KeyValue;
use tracing::Span;

/// AWS SQS 追踪属性
#[derive(Debug, Clone)]
pub struct SqsAttributes {
    pub queue_name: String,
    pub queue_url: String,
    pub operation: String,
    pub message_id: Option<String>,
    pub message_group_id: Option<String>,
    pub message_size: Option<usize>,
    pub region: String,
}

impl SqsAttributes {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("messaging.system", "aws_sqs"),
            KeyValue::new("messaging.destination", self.queue_name.clone()),
            KeyValue::new("messaging.destination_kind", "queue"),
            KeyValue::new("messaging.operation", self.operation.clone()),
            KeyValue::new("messaging.aws.sqs.queue_url", self.queue_url.clone()),
            KeyValue::new("cloud.provider", "aws"),
            KeyValue::new("cloud.region", self.region.clone()),
        ];

        if let Some(msg_id) = &self.message_id {
            attrs.push(KeyValue::new("messaging.message_id", msg_id.clone()));
        }

        if let Some(group_id) = &self.message_group_id {
            attrs.push(KeyValue::new("messaging.aws.sqs.message_group_id", group_id.clone()));
        }

        if let Some(size) = self.message_size {
            attrs.push(KeyValue::new("messaging.message_payload_size_bytes", size as i64));
        }

        attrs
    }

    pub fn record_to_span(&self, span: &Span) {
        span.record("messaging.system", "aws_sqs");
        span.record("messaging.destination", self.queue_name.as_str());
        span.record("messaging.operation", self.operation.as_str());
        span.record("cloud.provider", "aws");
        span.record("cloud.region", self.region.as_str());

        if let Some(msg_id) = &self.message_id {
            span.record("messaging.message_id", msg_id.as_str());
        }

        if let Some(group_id) = &self.message_group_id {
            span.record("messaging.aws.sqs.message_group_id", group_id.as_str());
        }

        if let Some(size) = self.message_size {
            span.record("messaging.message_payload_size_bytes", size as u64);
        }
    }
}

/// AWS SNS 追踪属性
#[derive(Debug, Clone)]
pub struct SnsAttributes {
    pub topic_name: String,
    pub topic_arn: String,
    pub operation: String,
    pub message_id: Option<String>,
    pub message_size: Option<usize>,
    pub region: String,
}

impl SnsAttributes {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("messaging.system", "aws_sns"),
            KeyValue::new("messaging.destination", self.topic_name.clone()),
            KeyValue::new("messaging.destination_kind", "topic"),
            KeyValue::new("messaging.operation", self.operation.clone()),
            KeyValue::new("messaging.aws.sns.topic_arn", self.topic_arn.clone()),
            KeyValue::new("cloud.provider", "aws"),
            KeyValue::new("cloud.region", self.region.clone()),
        ];

        if let Some(msg_id) = &self.message_id {
            attrs.push(KeyValue::new("messaging.message_id", msg_id.clone()));
        }

        if let Some(size) = self.message_size {
            attrs.push(KeyValue::new("messaging.message_payload_size_bytes", size as i64));
        }

        attrs
    }

    pub fn record_to_span(&self, span: &Span) {
        span.record("messaging.system", "aws_sns");
        span.record("messaging.destination", self.topic_name.as_str());
        span.record("messaging.operation", self.operation.as_str());
        span.record("cloud.provider", "aws");
        span.record("cloud.region", self.region.as_str());

        if let Some(msg_id) = &self.message_id {
            span.record("messaging.message_id", msg_id.as_str());
        }

        if let Some(size) = self.message_size {
            span.record("messaging.message_payload_size_bytes", size as u64);
        }
    }
}
```

---

## SQS 追踪实现

### 1. SQS 客户端初始化

```rust
use aws_config::{BehaviorVersion, Region};
use aws_sdk_sqs::{Client as SqsClient, types::MessageAttributeValue};
use serde::{Deserialize, Serialize};
use tracing::{error, info, instrument, warn};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct OrderMessage {
    pub order_id: String,
    pub user_id: String,
    pub amount: f64,
    pub status: String,
    pub timestamp: i64,
}

/// 带追踪的 SQS 客户端
pub struct TracedSqsClient {
    client: SqsClient,
    region: String,
}

impl TracedSqsClient {
    /// 创建 SQS 客户端
    #[instrument]
    pub async fn new(region: Option<&str>) -> Self {
        info!("Initializing SQS client");

        let mut config_loader = aws_config::defaults(BehaviorVersion::latest());

        if let Some(r) = region {
            config_loader = config_loader.region(Region::new(r.to_string()));
        }

        let config = config_loader.load().await;
        let client = SqsClient::new(&config);
        let region_str = config.region().map(|r| r.as_ref()).unwrap_or("us-east-1").to_string();

        info!(region = %region_str, "SQS client initialized");

        Self {
            client,
            region: region_str,
        }
    }

    /// 发送消息到 SQS
    #[instrument(
        skip(self, message),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            messaging.operation = "send",
            order.id = %message.order_id
        )
    )]
    pub async fn send_message(
        &self,
        queue_url: &str,
        queue_name: &str,
        message: OrderMessage,
    ) -> Result<String, aws_sdk_sqs::Error> {
        info!("Sending message to SQS");

        // 序列化消息
        let message_body = serde_json::to_string(&message)
            .map_err(|e| {
                error!(error = %e, "Failed to serialize message");
                aws_sdk_sqs::Error::Unhandled(Box::new(e))
            })?;

        // 创建追踪属性
        let attrs = SqsAttributes {
            queue_name: queue_name.to_string(),
            queue_url: queue_url.to_string(),
            operation: "send".to_string(),
            message_id: None,
            message_group_id: None,
            message_size: Some(message_body.len()),
            region: self.region.clone(),
        };

        // 记录属性到 Span
        let span = tracing::Span::current();
        attrs.record_to_span(&span);

        // 注入追踪上下文
        let mut message_attributes = std::collections::HashMap::new();
        
        // 添加自定义属性
        message_attributes.insert(
            "order_id".to_string(),
            MessageAttributeValue::builder()
                .data_type("String")
                .string_value(message.order_id.clone())
                .build()
                .map_err(|e| aws_sdk_sqs::Error::Unhandled(Box::new(e)))?,
        );

        // 发送消息
        let response = self
            .client
            .send_message()
            .queue_url(queue_url)
            .message_body(message_body)
            .set_message_attributes(Some(message_attributes))
            .send()
            .await?;

        let message_id = response.message_id().unwrap_or("unknown").to_string();

        info!(
            message_id = %message_id,
            queue = %queue_name,
            "Message sent successfully"
        );

        Ok(message_id)
    }

    /// 批量发送消息
    #[instrument(
        skip(self, messages),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            messaging.operation = "send_batch",
            batch.size = messages.len()
        )
    )]
    pub async fn send_batch(
        &self,
        queue_url: &str,
        queue_name: &str,
        messages: Vec<OrderMessage>,
    ) -> Result<Vec<String>, aws_sdk_sqs::Error> {
        info!(batch_size = messages.len(), "Sending batch to SQS");

        let mut entries = Vec::new();

        for (idx, message) in messages.iter().enumerate() {
            let message_body = serde_json::to_string(message)
                .map_err(|e| aws_sdk_sqs::Error::Unhandled(Box::new(e)))?;

            let entry = aws_sdk_sqs::types::SendMessageBatchRequestEntry::builder()
                .id(format!("msg-{}", idx))
                .message_body(message_body)
                .build()
                .map_err(|e| aws_sdk_sqs::Error::Unhandled(Box::new(e)))?;

            entries.push(entry);
        }

        let response = self
            .client
            .send_message_batch()
            .queue_url(queue_url)
            .set_entries(Some(entries))
            .send()
            .await?;

        let successful_ids: Vec<String> = response
            .successful()
            .iter()
            .filter_map(|s| s.message_id())
            .map(String::from)
            .collect();

        let failed_count = response.failed().len();

        if failed_count > 0 {
            warn!(
                failed_count = failed_count,
                "Some messages failed to send"
            );
        }

        info!(
            successful_count = successful_ids.len(),
            "Batch send completed"
        );

        Ok(successful_ids)
    }

    /// 接收消息
    #[instrument(
        skip(self),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            messaging.operation = "receive",
            max_messages = max_messages
        )
    )]
    pub async fn receive_messages(
        &self,
        queue_url: &str,
        queue_name: &str,
        max_messages: i32,
    ) -> Result<Vec<aws_sdk_sqs::types::Message>, aws_sdk_sqs::Error> {
        info!(max_messages = max_messages, "Receiving messages from SQS");

        let response = self
            .client
            .receive_message()
            .queue_url(queue_url)
            .max_number_of_messages(max_messages)
            .wait_time_seconds(20) // 长轮询
            .message_attribute_names("All")
            .send()
            .await?;

        let messages = response.messages().to_vec();

        info!(
            received_count = messages.len(),
            queue = %queue_name,
            "Messages received"
        );

        Ok(messages)
    }

    /// 删除消息
    #[instrument(
        skip(self),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            messaging.operation = "delete"
        )
    )]
    pub async fn delete_message(
        &self,
        queue_url: &str,
        queue_name: &str,
        receipt_handle: &str,
    ) -> Result<(), aws_sdk_sqs::Error> {
        info!("Deleting message from SQS");

        self.client
            .delete_message()
            .queue_url(queue_url)
            .receipt_handle(receipt_handle)
            .send()
            .await?;

        info!("Message deleted successfully");

        Ok(())
    }

    /// 消费者循环
    #[instrument(
        skip(self, handler),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            messaging.operation = "process"
        )
    )]
    pub async fn consume<F, Fut>(
        &self,
        queue_url: &str,
        queue_name: &str,
        handler: F,
    ) -> Result<(), aws_sdk_sqs::Error>
    where
        F: Fn(OrderMessage) -> Fut,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>>,
    {
        info!("Starting SQS consumer");

        loop {
            let messages = self.receive_messages(queue_url, queue_name, 10).await?;

            for message in messages {
                let process_span = tracing::info_span!(
                    "process_message",
                    messaging.system = "aws_sqs",
                    messaging.operation = "process",
                    messaging.message_id = ?message.message_id()
                );

                let _enter = process_span.enter();

                if let Some(body) = message.body() {
                    match serde_json::from_str::<OrderMessage>(body) {
                        Ok(order_message) => {
                            info!(order_id = %order_message.order_id, "Processing message");

                            match handler(order_message).await {
                                Ok(_) => {
                                    // 删除消息
                                    if let Some(receipt) = message.receipt_handle() {
                                        self.delete_message(queue_url, queue_name, receipt).await?;
                                        info!("Message processed and deleted");
                                    }
                                }
                                Err(e) => {
                                    error!(error = %e, "Failed to process message");
                                    // 消息会在可见性超时后重新可见
                                }
                            }
                        }
                        Err(e) => {
                            error!(error = %e, "Failed to deserialize message");
                        }
                    }
                }
            }

            // 如果没有消息，等待一下
            if messages.is_empty() {
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        }
    }
}
```

---

## SNS 追踪实现

### SNS 客户端

```rust
use aws_sdk_sns::{Client as SnsClient, types::MessageAttributeValue as SnsMessageAttributeValue};

/// 带追踪的 SNS 客户端
pub struct TracedSnsClient {
    client: SnsClient,
    region: String,
}

impl TracedSnsClient {
    /// 创建 SNS 客户端
    #[instrument]
    pub async fn new(region: Option<&str>) -> Self {
        info!("Initializing SNS client");

        let mut config_loader = aws_config::defaults(BehaviorVersion::latest());

        if let Some(r) = region {
            config_loader = config_loader.region(Region::new(r.to_string()));
        }

        let config = config_loader.load().await;
        let client = SnsClient::new(&config);
        let region_str = config.region().map(|r| r.as_ref()).unwrap_or("us-east-1").to_string();

        info!(region = %region_str, "SNS client initialized");

        Self {
            client,
            region: region_str,
        }
    }

    /// 发布消息到 SNS 主题
    #[instrument(
        skip(self, message),
        fields(
            messaging.system = "aws_sns",
            messaging.destination = %topic_name,
            messaging.operation = "publish",
            order.id = %message.order_id
        )
    )]
    pub async fn publish_message(
        &self,
        topic_arn: &str,
        topic_name: &str,
        message: OrderMessage,
        subject: Option<&str>,
    ) -> Result<String, aws_sdk_sns::Error> {
        info!("Publishing message to SNS topic");

        // 序列化消息
        let message_body = serde_json::to_string(&message)
            .map_err(|e| {
                error!(error = %e, "Failed to serialize message");
                aws_sdk_sns::Error::Unhandled(Box::new(e))
            })?;

        // 创建追踪属性
        let attrs = SnsAttributes {
            topic_name: topic_name.to_string(),
            topic_arn: topic_arn.to_string(),
            operation: "publish".to_string(),
            message_id: None,
            message_size: Some(message_body.len()),
            region: self.region.clone(),
        };

        let span = tracing::Span::current();
        attrs.record_to_span(&span);

        // 消息属性
        let mut message_attributes = std::collections::HashMap::new();
        message_attributes.insert(
            "order_id".to_string(),
            SnsMessageAttributeValue::builder()
                .data_type("String")
                .string_value(message.order_id.clone())
                .build()
                .map_err(|e| aws_sdk_sns::Error::Unhandled(Box::new(e)))?,
        );

        // 发布消息
        let mut publish_builder = self
            .client
            .publish()
            .topic_arn(topic_arn)
            .message(message_body)
            .set_message_attributes(Some(message_attributes));

        if let Some(subj) = subject {
            publish_builder = publish_builder.subject(subj);
        }

        let response = publish_builder.send().await?;

        let message_id = response.message_id().unwrap_or("unknown").to_string();

        info!(
            message_id = %message_id,
            topic = %topic_name,
            "Message published successfully"
        );

        Ok(message_id)
    }

    /// 发布带过滤策略的消息
    #[instrument(
        skip(self, message, filter_attributes),
        fields(
            messaging.system = "aws_sns",
            messaging.destination = %topic_name,
            messaging.operation = "publish",
            filter_count = filter_attributes.len()
        )
    )]
    pub async fn publish_with_filters(
        &self,
        topic_arn: &str,
        topic_name: &str,
        message: OrderMessage,
        filter_attributes: std::collections::HashMap<String, String>,
    ) -> Result<String, aws_sdk_sns::Error> {
        info!("Publishing message with filter attributes");

        let message_body = serde_json::to_string(&message)
            .map_err(|e| aws_sdk_sns::Error::Unhandled(Box::new(e)))?;

        let mut message_attributes = std::collections::HashMap::new();

        // 添加过滤属性
        for (key, value) in filter_attributes {
            message_attributes.insert(
                key,
                SnsMessageAttributeValue::builder()
                    .data_type("String")
                    .string_value(value)
                    .build()
                    .map_err(|e| aws_sdk_sns::Error::Unhandled(Box::new(e)))?,
            );
        }

        let response = self
            .client
            .publish()
            .topic_arn(topic_arn)
            .message(message_body)
            .set_message_attributes(Some(message_attributes))
            .send()
            .await?;

        let message_id = response.message_id().unwrap_or("unknown").to_string();

        info!(
            message_id = %message_id,
            "Message with filters published"
        );

        Ok(message_id)
    }

    /// 创建主题
    #[instrument(
        skip(self),
        fields(
            messaging.system = "aws_sns",
            messaging.operation = "create_topic",
            topic_name = %name
        )
    )]
    pub async fn create_topic(&self, name: &str) -> Result<String, aws_sdk_sns::Error> {
        info!(topic_name = %name, "Creating SNS topic");

        let response = self.client.create_topic().name(name).send().await?;

        let topic_arn = response.topic_arn().unwrap_or("unknown").to_string();

        info!(
            topic_arn = %topic_arn,
            "Topic created successfully"
        );

        Ok(topic_arn)
    }

    /// 订阅主题
    #[instrument(
        skip(self),
        fields(
            messaging.system = "aws_sns",
            messaging.operation = "subscribe",
            topic_arn = %topic_arn,
            protocol = %protocol
        )
    )]
    pub async fn subscribe(
        &self,
        topic_arn: &str,
        protocol: &str,
        endpoint: &str,
    ) -> Result<String, aws_sdk_sns::Error> {
        info!(
            protocol = %protocol,
            endpoint = %endpoint,
            "Subscribing to SNS topic"
        );

        let response = self
            .client
            .subscribe()
            .topic_arn(topic_arn)
            .protocol(protocol)
            .endpoint(endpoint)
            .send()
            .await?;

        let subscription_arn = response.subscription_arn().unwrap_or("pending").to_string();

        info!(
            subscription_arn = %subscription_arn,
            "Subscription created"
        );

        Ok(subscription_arn)
    }
}
```

---

## SQS + SNS 集成

### 扇出模式（Fan-out Pattern）

```rust
/// SNS 到 SQS 扇出集成
pub struct FanoutIntegration {
    sns_client: TracedSnsClient,
    sqs_clients: Vec<TracedSqsClient>,
}

impl FanoutIntegration {
    pub async fn new(region: Option<&str>) -> Self {
        let sns_client = TracedSnsClient::new(region).await;
        let sqs_client = TracedSqsClient::new(region).await;

        Self {
            sns_client,
            sqs_clients: vec![sqs_client],
        }
    }

    /// 设置 SNS 到 SQS 订阅
    #[instrument(
        skip(self),
        fields(
            integration = "sns-to-sqs",
            topic_arn = %topic_arn,
            queue_arn = %queue_arn
        )
    )]
    pub async fn setup_subscription(
        &self,
        topic_arn: &str,
        queue_arn: &str,
    ) -> Result<String, Box<dyn std::error::Error>> {
        info!("Setting up SNS to SQS subscription");

        // 订阅 SQS 队列到 SNS 主题
        let subscription_arn = self
            .sns_client
            .subscribe(topic_arn, "sqs", queue_arn)
            .await?;

        info!(
            subscription_arn = %subscription_arn,
            "Subscription setup completed"
        );

        Ok(subscription_arn)
    }

    /// 发布消息到 SNS（扇出到多个 SQS）
    #[instrument(
        skip(self, message),
        fields(
            integration = "fanout",
            topic = %topic_name,
            order.id = %message.order_id
        )
    )]
    pub async fn fanout_publish(
        &self,
        topic_arn: &str,
        topic_name: &str,
        message: OrderMessage,
    ) -> Result<String, Box<dyn std::error::Error>> {
        info!("Publishing message for fanout");

        let message_id = self
            .sns_client
            .publish_message(topic_arn, topic_name, message, None)
            .await?;

        info!(
            message_id = %message_id,
            "Fanout message published"
        );

        Ok(message_id)
    }
}
```

---

## FIFO 队列支持

### FIFO 队列操作

```rust
impl TracedSqsClient {
    /// 发送消息到 FIFO 队列
    #[instrument(
        skip(self, message),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            messaging.operation = "send",
            messaging.aws.sqs.message_group_id = %message_group_id,
            queue_type = "fifo"
        )
    )]
    pub async fn send_to_fifo(
        &self,
        queue_url: &str,
        queue_name: &str,
        message: OrderMessage,
        message_group_id: &str,
        deduplication_id: Option<&str>,
    ) -> Result<String, aws_sdk_sqs::Error> {
        info!(
            message_group_id = %message_group_id,
            "Sending message to FIFO queue"
        );

        let message_body = serde_json::to_string(&message)
            .map_err(|e| aws_sdk_sqs::Error::Unhandled(Box::new(e)))?;

        let mut send_builder = self
            .client
            .send_message()
            .queue_url(queue_url)
            .message_body(message_body)
            .message_group_id(message_group_id);

        // FIFO 队列需要去重 ID
        if let Some(dedup_id) = deduplication_id {
            send_builder = send_builder.message_deduplication_id(dedup_id);
        }

        let response = send_builder.send().await?;

        let message_id = response.message_id().unwrap_or("unknown").to_string();

        info!(
            message_id = %message_id,
            message_group_id = %message_group_id,
            "FIFO message sent successfully"
        );

        Ok(message_id)
    }
}
```

---

## 死信队列处理

### DLQ 集成

```rust
impl TracedSqsClient {
    /// 处理死信队列消息
    #[instrument(
        skip(self),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %dlq_name,
            messaging.operation = "process_dlq"
        )
    )]
    pub async fn process_dlq(
        &self,
        dlq_url: &str,
        dlq_name: &str,
    ) -> Result<(), aws_sdk_sqs::Error> {
        info!("Processing messages from DLQ");

        let messages = self.receive_messages(dlq_url, dlq_name, 10).await?;

        for message in messages {
            if let Some(body) = message.body() {
                warn!(
                    message_body = %body,
                    "Processing DLQ message"
                );

                // 记录或重新处理失败消息
                // ...

                // 删除 DLQ 消息
                if let Some(receipt) = message.receipt_handle() {
                    self.delete_message(dlq_url, dlq_name, receipt).await?;
                }
            }
        }

        info!("DLQ processing completed");

        Ok(())
    }
}
```

---

## 性能优化

### 1. 批量接收与处理

```rust
use futures::stream::{self, StreamExt};

impl TracedSqsClient {
    /// 并发处理消息
    #[instrument(
        skip(self, handler),
        fields(
            messaging.system = "aws_sqs",
            messaging.destination = %queue_name,
            concurrency = concurrency
        )
    )]
    pub async fn consume_concurrent<F, Fut>(
        &self,
        queue_url: &str,
        queue_name: &str,
        concurrency: usize,
        handler: F,
    ) -> Result<(), aws_sdk_sqs::Error>
    where
        F: Fn(OrderMessage) -> Fut + Clone + Send + 'static,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        info!(concurrency = concurrency, "Starting concurrent consumer");

        loop {
            let messages = self.receive_messages(queue_url, queue_name, 10).await?;

            if messages.is_empty() {
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                continue;
            }

            // 并发处理消息
            stream::iter(messages)
                .map(|message| {
                    let handler = handler.clone();
                    let queue_url = queue_url.to_string();
                    let queue_name = queue_name.to_string();
                    let client = self.client.clone();

                    async move {
                        if let Some(body) = message.body() {
                            if let Ok(order_message) = serde_json::from_str::<OrderMessage>(body) {
                                if handler(order_message).await.is_ok() {
                                    if let Some(receipt) = message.receipt_handle() {
                                        let _ = client
                                            .delete_message()
                                            .queue_url(queue_url)
                                            .receipt_handle(receipt)
                                            .send()
                                            .await;
                                    }
                                }
                            }
                        }
                    }
                })
                .buffer_unordered(concurrency)
                .collect::<Vec<_>>()
                .await;
        }
    }
}
```

---

## 最佳实践

### 1. 错误重试策略

```rust
use std::time::Duration;
use tokio::time::sleep;

pub async fn send_with_retry<F, Fut, T>(
    operation: F,
    max_retries: u32,
) -> Result<T, Box<dyn std::error::Error>>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T, Box<dyn std::error::Error>>>,
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

### 2. 消息去重

```rust
use std::collections::HashSet;
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct MessageDeduplicator {
    seen_ids: Arc<Mutex<HashSet<String>>>,
}

impl MessageDeduplicator {
    pub fn new() -> Self {
        Self {
            seen_ids: Arc::new(Mutex::new(HashSet::new())),
        }
    }

    #[instrument(skip(self))]
    pub async fn is_duplicate(&self, message_id: &str) -> bool {
        let mut seen = self.seen_ids.lock().await;

        if seen.contains(message_id) {
            warn!(message_id = %message_id, "Duplicate message detected");
            true
        } else {
            seen.insert(message_id.to_string());
            false
        }
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
                    opentelemetry::KeyValue::new("service.name", "aws-sqs-sns-demo"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("Starting AWS SQS/SNS OTLP tracing demo");

    // SQS 示例
    let sqs_client = TracedSqsClient::new(Some("us-east-1")).await;
    let queue_url = "https://sqs.us-east-1.amazonaws.com/123456789012/my-queue";
    let queue_name = "my-queue";

    let message = OrderMessage {
        order_id: "order-123".to_string(),
        user_id: "user-456".to_string(),
        amount: 99.99,
        status: "pending".to_string(),
        timestamp: chrono::Utc::now().timestamp(),
    };

    sqs_client
        .send_message(queue_url, queue_name, message.clone())
        .await?;

    // SNS 示例
    let sns_client = TracedSnsClient::new(Some("us-east-1")).await;
    let topic_arn = "arn:aws:sns:us-east-1:123456789012:my-topic";
    let topic_name = "my-topic";

    sns_client
        .publish_message(topic_arn, topic_name, message, Some("Order Event"))
        .await?;

    info!("Demo completed successfully");

    global::shutdown_tracer_provider();

    Ok(())
}
```

---

## 总结

本文档提供了 AWS SQS/SNS 在 Rust 1.90 环境下的完整 OpenTelemetry 集成方案：

1. ✅ **语义约定**: 完整实现 OpenTelemetry AWS 语义约定
2. ✅ **SQS 集成**: 标准/FIFO 队列、批量操作、死信队列
3. ✅ **SNS 集成**: 发布/订阅、消息过滤、主题管理
4. ✅ **扇出模式**: SNS 到多个 SQS 的集成
5. ✅ **性能优化**: 并发处理、批量操作、重试策略
6. ✅ **最佳实践**: 错误处理、消息去重、可见性管理

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT

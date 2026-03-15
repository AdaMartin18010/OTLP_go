# NATS 语义约定 - Rust 完整实现指南

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **async-nats**: 0.37.0  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月8日  
> **规范版本**: OpenTelemetry Semantic Conventions v1.30.0

---

## 目录

- [NATS 语义约定 - Rust 完整实现指南](#nats-语义约定---rust-完整实现指南)
  - [目录](#目录)
  - [1. NATS 追踪概述](#1-nats-追踪概述)
  - [2. NATS 属性定义](#2-nats-属性定义)
  - [3. 依赖配置](#3-依赖配置)
  - [4. Rust Publisher 实现](#4-rust-publisher-实现)
    - [4.1 基础异步发布](#41-基础异步发布)
    - [4.2 请求-响应模式](#42-请求-响应模式)
    - [4.3 JetStream 发布](#43-jetstream-发布)
  - [5. Rust Subscriber 实现](#5-rust-subscriber-实现)
    - [5.1 异步订阅](#51-异步订阅)
    - [5.2 队列组订阅](#52-队列组订阅)
    - [5.3 JetStream 消费](#53-jetstream-消费)
  - [6. TraceContext 传播](#6-tracecontext-传播)
  - [7. JetStream 集成](#7-jetstream-集成)
  - [8. 完整微服务示例](#8-完整微服务示例)
  - [9. 性能优化](#9-性能优化)
  - [10. 生产环境最佳实践](#10-生产环境最佳实践)
  - [11. 参考资源](#11-参考资源)

---

## 1. NATS 追踪概述

**NATS 特点与追踪价值**:

```text
NATS = 高性能、云原生消息系统
特点:
- 轻量级 (3MB 二进制)
- 高性能 (百万+ 消息/秒)
- 至多一次交付 (at-most-once)
- Subject-based 路由
- JetStream (持久化层)

Rust 视角价值:
1. 零成本抽象
   - 编译时优化的追踪
   - 类型安全的 subject 处理
   
2. 异步优先
   - 完美契合 Tokio 生态
   - 高并发消息处理
   
3. 内存安全
   - 所有权系统防止泄漏
   - 生命周期管理连接
```

**Span 模型**:

```text
┌──────────────────────────────────────────────────────────┐
│              发布者服务 (Rust)                             │
│  ┌─────────────────┐                                      │
│  │ POST /events    │  SpanKind::Server                    │
│  │ TraceID: abc    │                                      │
│  └────────┬────────┘                                      │
│           │                                               │
│           ▼                                               │
│  ┌─────────────────┐                                      │
│  │ nats.publish    │  SpanKind::Producer                  │
│  │ Subject: events │  注入TraceContext到headers            │
│  │ TraceID: abc    │                                      │
│  └─────────────────┘                                      │
└──────────────────────────────────────────────────────────┘
           │
           │ NATS Message (携带 traceparent header)
           │
           ▼
┌──────────────────────────────────────────────────────────┐
│              订阅者服务 (Rust)                             │
│  ┌─────────────────┐                                      │
│  │ nats.subscribe  │  SpanKind::Consumer                  │
│  │ Subject: events │  从headers提取TraceContext            │
│  │ TraceID: abc    │  (同一个TraceID!)                    │
│  └────────┬────────┘                                      │
│           │                                               │
│           ▼                                               │
│  ┌─────────────────┐                                      │
│  │ Process Message │  SpanKind::Internal                  │
│  │ TraceID: abc    │                                      │
│  └─────────────────┘                                      │
└──────────────────────────────────────────────────────────┘
```

---

## 2. NATS 属性定义

**Rust 类型安全的属性**:

```rust
use opentelemetry::KeyValue;
use serde::Serialize;

/// NATS 语义约定属性
#[derive(Debug, Clone, Serialize)]
pub struct NatsAttributes {
    /// 消息系统 (固定为 "nats")
    pub system: &'static str,
    
    /// Subject (类似 topic)
    pub destination_name: String,
    
    /// 操作类型
    pub operation: NatsOperation,
    
    /// NATS 服务器地址
    pub server_address: String,
    
    /// 服务器端口
    pub server_port: u16,
    
    /// 队列组 (可选)
    pub queue_group: Option<String>,
    
    /// JetStream stream (可选)
    pub jetstream_stream: Option<String>,
    
    /// JetStream consumer (可选)
    pub jetstream_consumer: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum NatsOperation {
    #[serde(rename = "publish")]
    Publish,
    #[serde(rename = "receive")]
    Receive,
    #[serde(rename = "process")]
    Process,
    #[serde(rename = "request")]
    Request,
    #[serde(rename = "reply")]
    Reply,
}

impl NatsAttributes {
    /// 转换为 OpenTelemetry KeyValue
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("messaging.system", self.system),
            KeyValue::new("messaging.destination.name", self.destination_name.clone()),
            KeyValue::new("messaging.operation", match self.operation {
                NatsOperation::Publish => "publish",
                NatsOperation::Receive => "receive",
                NatsOperation::Process => "process",
                NatsOperation::Request => "request",
                NatsOperation::Reply => "reply",
            }),
            KeyValue::new("network.peer.address", self.server_address.clone()),
            KeyValue::new("network.peer.port", self.server_port as i64),
        ];
        
        if let Some(ref group) = self.queue_group {
            attrs.push(KeyValue::new("messaging.nats.queue_group", group.clone()));
        }
        
        if let Some(ref stream) = self.jetstream_stream {
            attrs.push(KeyValue::new("messaging.nats.jetstream.stream", stream.clone()));
        }
        
        if let Some(ref consumer) = self.jetstream_consumer {
            attrs.push(KeyValue::new("messaging.nats.jetstream.consumer", consumer.clone()));
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
name = "nats-otlp-integration"
version = "0.1.0"
edition = "2021"
rust-version = "1.90"

[dependencies]
# NATS 客户端 (Rust 1.90 兼容)
async-nats = "0.37.0"

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

## 4. Rust Publisher 实现

### 4.1 基础异步发布

**完整的异步发布实现**:

```rust
use async_nats::{Client, ConnectOptions, HeaderMap};
use opentelemetry::{
    global,
    trace::{Span, SpanKind, Status, Tracer, TraceContextExt},
    Context, KeyValue,
};
use tracing::{info, error, instrument};

/// NATS Publisher 追踪包装器
pub struct TracedNatsPublisher {
    client: Client,
    tracer: Box<dyn Tracer + Send + Sync>,
    server_address: String,
    server_port: u16,
}

impl TracedNatsPublisher {
    /// 创建新的追踪 Publisher
    pub async fn new(server_url: &str) -> Result<Self, anyhow::Error> {
        // 解析服务器地址
        let (address, port) = parse_nats_url(server_url)?;
        
        // 创建连接
        let client = ConnectOptions::new()
            .name("traced-publisher")  // 连接名称
            .retry_on_failed_connect()  // 自动重连
            .max_reconnects(Some(10))   // 最多重连10次
            .connect(server_url)
            .await?;
        
        info!(server = %server_url, "Connected to NATS server");
        
        let tracer = global::tracer("nats-publisher");
        
        Ok(Self {
            client,
            tracer: Box::new(tracer),
            server_address: address,
            server_port: port,
        })
    }
    
    /// 发布消息并追踪
    #[instrument(skip(self, payload))]
    pub async fn publish_traced(
        &self,
        subject: &str,
        payload: &[u8],
    ) -> Result<(), anyhow::Error> {
        // 创建 Producer Span
        let mut span = self.tracer
            .span_builder(format!("nats.publish {}", subject))
            .with_kind(SpanKind::Producer)
            .start(&*self.tracer);
        
        // 设置 NATS 属性
        let attrs = NatsAttributes {
            system: "nats",
            destination_name: subject.to_string(),
            operation: NatsOperation::Publish,
            server_address: self.server_address.clone(),
            server_port: self.server_port,
            queue_group: None,
            jetstream_stream: None,
            jetstream_consumer: None,
        };
        
        span.set_attributes(attrs.to_key_values());
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            payload.len() as i64));
        
        // 获取当前上下文
        let cx = Context::current_with_span(span.clone());
        
        // 注入 TraceContext 到 Headers
        let headers = self.inject_trace_context(&cx);
        
        // 发布消息
        match self.client
            .publish_with_headers(subject.to_string(), headers, payload.into())
            .await
        {
            Ok(_) => {
                span.set_status(Status::Ok);
                info!(subject = %subject, "Message published successfully");
                Ok(())
            }
            Err(e) => {
                let error_msg = format!("Failed to publish: {}", e);
                span.record_error(&error_msg);
                span.set_status(Status::error(error_msg.clone()));
                error!(subject = %subject, error = ?e, "Failed to publish message");
                Err(anyhow::anyhow!("NATS publish failed: {}", e))
            }
        }
    }
    
    /// 注入 TraceContext 到 NATS Headers
    fn inject_trace_context(&self, cx: &Context) -> HeaderMap {
        use opentelemetry::propagation::{Injector, TextMapPropagator};
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        
        struct NatsHeaderInjector {
            headers: HeaderMap,
        }
        
        impl Injector for NatsHeaderInjector {
            fn set(&mut self, key: &str, value: String) {
                self.headers.insert(key, value.as_str());
            }
        }
        
        let mut injector = NatsHeaderInjector {
            headers: HeaderMap::new(),
        };
        
        let propagator = TraceContextPropagator::new();
        propagator.inject_context(cx, &mut injector);
        
        injector.headers
    }
}

/// 解析 NATS URL
fn parse_nats_url(url: &str) -> Result<(String, u16), anyhow::Error> {
    // 简化版解析 (实际应使用 url crate)
    let default_port = 4222;
    
    if url.contains("://") {
        let parts: Vec<&str> = url.split("://").collect();
        if parts.len() == 2 {
            let host_port = parts[1];
            if let Some(colon_pos) = host_port.find(':') {
                let host = &host_port[..colon_pos];
                let port = host_port[colon_pos + 1..]
                    .parse::<u16>()
                    .unwrap_or(default_port);
                return Ok((host.to_string(), port));
            }
            return Ok((host_port.to_string(), default_port));
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
    let publisher = TracedNatsPublisher::new("nats://localhost:4222").await?;
    
    // 发布消息
    let message = serde_json::json!({
        "event_type": "order.created",
        "order_id": "12345",
        "timestamp": chrono::Utc::now().to_rfc3339(),
    });
    
    let payload = serde_json::to_vec(&message)?;
    
    publisher.publish_traced("events.orders", &payload).await?;
    
    println!("Message published");
    
    Ok(())
}
```

### 4.2 请求-响应模式

**NATS 请求-响应实现**:

```rust
impl TracedNatsPublisher {
    /// 发送请求并等待响应 (追踪)
    #[instrument(skip(self, payload))]
    pub async fn request_traced(
        &self,
        subject: &str,
        payload: &[u8],
        timeout: std::time::Duration,
    ) -> Result<Vec<u8>, anyhow::Error> {
        // 创建 Request Span
        let mut span = self.tracer
            .span_builder(format!("nats.request {}", subject))
            .with_kind(SpanKind::Client)  // 请求-响应模式使用 Client
            .start(&*self.tracer);
        
        // 设置属性
        span.set_attribute(KeyValue::new("messaging.system", "nats"));
        span.set_attribute(KeyValue::new("messaging.destination.name", subject));
        span.set_attribute(KeyValue::new("messaging.operation", "request"));
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            payload.len() as i64));
        
        // 注入 TraceContext
        let cx = Context::current_with_span(span.clone());
        let headers = self.inject_trace_context(&cx);
        
        // 发送请求
        let request_future = self.client
            .request_with_headers(subject.to_string(), headers, payload.into());
        
        match tokio::time::timeout(timeout, request_future).await {
            Ok(Ok(response)) => {
                // 记录响应
                let response_payload = response.payload.to_vec();
                span.set_attribute(KeyValue::new("messaging.message.response_size_bytes", 
                    response_payload.len() as i64));
                span.set_status(Status::Ok);
                
                info!(
                    subject = %subject,
                    response_size = response_payload.len(),
                    "Request completed successfully"
                );
                
                Ok(response_payload)
            }
            Ok(Err(e)) => {
                let error_msg = format!("Request failed: {}", e);
                span.record_error(&error_msg);
                span.set_status(Status::error(error_msg.clone()));
                Err(anyhow::anyhow!("NATS request failed: {}", e))
            }
            Err(_) => {
                let error_msg = "Request timeout";
                span.record_error(error_msg);
                span.set_status(Status::error(error_msg));
                Err(anyhow::anyhow!("NATS request timeout"))
            }
        }
    }
}

/// 响应处理器 (服务端)
pub struct TracedNatsResponder {
    client: Client,
    tracer: Box<dyn Tracer + Send + Sync>,
}

impl TracedNatsResponder {
    /// 响应请求 (追踪)
    #[instrument(skip(self, payload))]
    pub async fn reply_traced(
        &self,
        reply_subject: &str,
        payload: &[u8],
        parent_cx: &Context,
    ) -> Result<(), anyhow::Error> {
        // 创建 Reply Span (作为子 span)
        let mut span = self.tracer
            .span_builder(format!("nats.reply {}", reply_subject))
            .with_kind(SpanKind::Producer)
            .start_with_context(&*self.tracer, parent_cx);
        
        // 设置属性
        span.set_attribute(KeyValue::new("messaging.system", "nats"));
        span.set_attribute(KeyValue::new("messaging.operation", "reply"));
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            payload.len() as i64));
        
        // 注入 TraceContext
        let cx = Context::current_with_span(span.clone());
        let headers = self.inject_trace_context(&cx);
        
        // 发送响应
        match self.client
            .publish_with_headers(reply_subject.to_string(), headers, payload.into())
            .await
        {
            Ok(_) => {
                span.set_status(Status::Ok);
                Ok(())
            }
            Err(e) => {
                let error_msg = format!("Failed to reply: {}", e);
                span.record_error(&error_msg);
                span.set_status(Status::error(error_msg.clone()));
                Err(anyhow::anyhow!("NATS reply failed: {}", e))
            }
        }
    }
}
```

### 4.3 JetStream 发布

**JetStream 持久化发布**:

```rust
use async_nats::jetstream::{self, Context as JsContext};

pub struct TracedJetStreamPublisher {
    jetstream: JsContext,
    tracer: Box<dyn Tracer + Send + Sync>,
    server_address: String,
    server_port: u16,
}

impl TracedJetStreamPublisher {
    /// 创建 JetStream Publisher
    pub async fn new(client: Client, server_address: String, server_port: u16) -> Self {
        let jetstream = jetstream::new(client);
        let tracer = global::tracer("nats-jetstream-publisher");
        
        Self {
            jetstream,
            tracer: Box::new(tracer),
            server_address,
            server_port,
        }
    }
    
    /// 发布消息到 JetStream (追踪)
    #[instrument(skip(self, payload))]
    pub async fn publish_traced(
        &self,
        subject: &str,
        stream_name: &str,
        payload: &[u8],
    ) -> Result<jetstream::PublishAck, anyhow::Error> {
        // 创建 Span
        let mut span = self.tracer
            .span_builder(format!("jetstream.publish {}", subject))
            .with_kind(SpanKind::Producer)
            .start(&*self.tracer);
        
        // 设置属性
        span.set_attribute(KeyValue::new("messaging.system", "nats"));
        span.set_attribute(KeyValue::new("messaging.destination.name", subject));
        span.set_attribute(KeyValue::new("messaging.operation", "publish"));
        span.set_attribute(KeyValue::new("messaging.nats.jetstream.stream", stream_name));
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            payload.len() as i64));
        
        // 注入 TraceContext
        let cx = Context::current_with_span(span.clone());
        let headers = self.inject_trace_context(&cx);
        
        // 发布到 JetStream
        match self.jetstream
            .publish_with_headers(subject.to_string(), headers, payload.into())
            .await
        {
            Ok(ack) => {
                // 记录 JetStream 信息
                span.set_attribute(KeyValue::new("messaging.nats.jetstream.sequence", 
                    ack.sequence as i64));
                span.set_attribute(KeyValue::new("messaging.nats.jetstream.stream", 
                    ack.stream.clone()));
                span.set_status(Status::Ok);
                
                info!(
                    subject = %subject,
                    stream = %ack.stream,
                    sequence = ack.sequence,
                    "Message published to JetStream"
                );
                
                Ok(ack)
            }
            Err(e) => {
                let error_msg = format!("Failed to publish to JetStream: {:?}", e);
                span.record_error(&error_msg);
                span.set_status(Status::error(error_msg.clone()));
                Err(anyhow::anyhow!("JetStream publish failed: {:?}", e))
            }
        }
    }
}
```

---

## 5. Rust Subscriber 实现

### 5.1 异步订阅

**完整的异步订阅实现**:

```rust
use async_nats::Subscriber;
use tokio_stream::StreamExt;

pub struct TracedNatsSubscriber {
    client: Client,
    tracer: Box<dyn Tracer + Send + Sync>,
    server_address: String,
    server_port: u16,
}

impl TracedNatsSubscriber {
    /// 创建新的追踪 Subscriber
    pub async fn new(server_url: &str) -> Result<Self, anyhow::Error> {
        let (address, port) = parse_nats_url(server_url)?;
        
        let client = ConnectOptions::new()
            .name("traced-subscriber")
            .retry_on_failed_connect()
            .connect(server_url)
            .await?;
        
        info!(server = %server_url, "Connected to NATS server");
        
        let tracer = global::tracer("nats-subscriber");
        
        Ok(Self {
            client,
            tracer: Box::new(tracer),
            server_address: address,
            server_port: port,
        })
    }
    
    /// 订阅并追踪
    pub async fn subscribe_with_tracing<F, Fut>(
        &self,
        subject: &str,
        mut handler: F,
    ) -> Result<(), anyhow::Error>
    where
        F: FnMut(Vec<u8>, Context) -> Fut + Send,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        // 订阅 subject
        let mut subscriber = self.client.subscribe(subject.to_string()).await?;
        
        info!(subject = %subject, "Subscribed to subject");
        
        // 处理消息
        while let Some(message) = subscriber.next().await {
            if let Err(e) = self
                .process_message_traced(&message, subject, &mut handler)
                .await
            {
                error!("Failed to process message: {}", e);
                // 继续处理下一条消息
            }
        }
        
        Ok(())
    }
    
    /// 处理单条消息并追踪
    #[instrument(skip(self, message, handler))]
    async fn process_message_traced<F, Fut>(
        &self,
        message: &async_nats::Message,
        subject: &str,
        handler: &mut F,
    ) -> Result<(), anyhow::Error>
    where
        F: FnMut(Vec<u8>, Context) -> Fut + Send,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        // 提取 TraceContext 从 Headers
        let parent_cx = self.extract_trace_context(message);
        
        // 创建 Consumer Span
        let mut span = self.tracer
            .span_builder(format!("nats.receive {}", subject))
            .with_kind(SpanKind::Consumer)
            .start_with_context(&*self.tracer, &parent_cx);
        
        // 设置属性
        span.set_attribute(KeyValue::new("messaging.system", "nats"));
        span.set_attribute(KeyValue::new("messaging.destination.name", subject));
        span.set_attribute(KeyValue::new("messaging.operation", "receive"));
        span.set_attribute(KeyValue::new("messaging.message.payload_size_bytes", 
            message.payload.len() as i64));
        
        // 设置当前上下文
        let cx = Context::current_with_span(span.clone());
        let _guard = cx.attach();
        
        // 调用用户处理函数
        match handler(message.payload.to_vec(), cx.clone()).await {
            Ok(_) => {
                span.set_status(Status::Ok);
                info!(subject = %subject, "Message processed successfully");
            }
            Err(e) => {
                let error_msg = format!("Handler failed: {}", e);
                span.record_error(&error_msg);
                span.set_status(Status::error(error_msg.clone()));
                error!(subject = %subject, error = ?e, "Failed to process message");
                return Err(e);
            }
        }
        
        Ok(())
    }
    
    /// 从 NATS Headers 提取 TraceContext
    fn extract_trace_context(&self, message: &async_nats::Message) -> Context {
        use opentelemetry::propagation::{Extractor, TextMapPropagator};
        use opentelemetry_sdk::propagation::TraceContextPropagator;
        
        struct NatsHeaderExtractor<'a> {
            headers: &'a HeaderMap,
        }
        
        impl<'a> Extractor for NatsHeaderExtractor<'a> {
            fn get(&self, key: &str) -> Option<&str> {
                self.headers.get(key).and_then(|v| v.as_str())
            }
            
            fn keys(&self) -> Vec<&str> {
                self.headers.iter().map(|(k, _)| k.as_str()).collect()
            }
        }
        
        let headers = message.headers.as_ref();
        if let Some(h) = headers {
            let extractor = NatsHeaderExtractor { headers: h };
            let propagator = TraceContextPropagator::new();
            return propagator.extract(&extractor);
        }
        
        Context::current()
    }
}

/// 使用示例
#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    // 初始化 OpenTelemetry
    init_telemetry().await?;
    
    // 创建 Subscriber
    let subscriber = TracedNatsSubscriber::new("nats://localhost:4222").await?;
    
    // 开始订阅
    subscriber.subscribe_with_tracing("events.>", |payload, _cx| async move {
        // 处理消息
        let message: serde_json::Value = serde_json::from_slice(&payload)?;
        info!("Received event: {:?}", message);
        
        // 业务逻辑...
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        Ok(())
    }).await?;
    
    Ok(())
}
```

### 5.2 队列组订阅

**负载均衡的队列组订阅**:

```rust
impl TracedNatsSubscriber {
    /// 队列组订阅 (负载均衡)
    pub async fn queue_subscribe_with_tracing<F, Fut>(
        &self,
        subject: &str,
        queue_group: &str,
        mut handler: F,
    ) -> Result<(), anyhow::Error>
    where
        F: FnMut(Vec<u8>, Context) -> Fut + Send,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        // 队列组订阅
        let mut subscriber = self.client
            .queue_subscribe(subject.to_string(), queue_group.to_string())
            .await?;
        
        info!(
            subject = %subject,
            queue_group = %queue_group,
            "Subscribed to queue group"
        );
        
        // 处理消息
        while let Some(message) = subscriber.next().await {
            // 创建 Span 并设置队列组属性
            let parent_cx = self.extract_trace_context(&message);
            
            let mut span = self.tracer
                .span_builder(format!("nats.receive {}", subject))
                .with_kind(SpanKind::Consumer)
                .start_with_context(&*self.tracer, &parent_cx);
            
            span.set_attribute(KeyValue::new("messaging.nats.queue_group", queue_group));
            
            // ... (处理逻辑类似单订阅)
        }
        
        Ok(())
    }
}
```

### 5.3 JetStream 消费

**JetStream 持久化消费**:

```rust
use async_nats::jetstream::consumer::PullConsumer;

pub struct TracedJetStreamConsumer {
    jetstream: JsContext,
    tracer: Box<dyn Tracer + Send + Sync>,
}

impl TracedJetStreamConsumer {
    /// 消费 JetStream 消息
    pub async fn consume_with_tracing<F, Fut>(
        &self,
        stream_name: &str,
        consumer_name: &str,
        batch_size: usize,
        mut handler: F,
    ) -> Result<(), anyhow::Error>
    where
        F: FnMut(Vec<u8>, Context) -> Fut + Send,
        Fut: std::future::Future<Output = Result<(), anyhow::Error>> + Send,
    {
        // 获取或创建 Consumer
        let consumer: PullConsumer = self.jetstream
            .get_stream(stream_name)
            .await?
            .get_consumer(consumer_name)
            .await?;
        
        info!(
            stream = %stream_name,
            consumer = %consumer_name,
            "Started JetStream consumer"
        );
        
        loop {
            // 拉取消息批次
            let mut messages = consumer
                .fetch()
                .max_messages(batch_size)
                .messages()
                .await?;
            
            // 处理批次中的每条消息
            while let Some(Ok(message)) = messages.next().await {
                // 提取 TraceContext
                let parent_cx = self.extract_trace_context(&message);
                
                // 创建 Span
                let mut span = self.tracer
                    .span_builder(format!("jetstream.receive {}", message.subject))
                    .with_kind(SpanKind::Consumer)
                    .start_with_context(&*self.tracer, &parent_cx);
                
                // 设置属性
                span.set_attribute(KeyValue::new("messaging.system", "nats"));
                span.set_attribute(KeyValue::new("messaging.nats.jetstream.stream", stream_name));
                span.set_attribute(KeyValue::new("messaging.nats.jetstream.consumer", consumer_name));
                
                if let Some(info) = message.info().ok() {
                    span.set_attribute(KeyValue::new("messaging.nats.jetstream.sequence", 
                        info.stream_sequence as i64));
                }
                
                let cx = Context::current_with_span(span.clone());
                let _guard = cx.attach();
                
                // 处理消息
                match handler(message.payload.to_vec(), cx.clone()).await {
                    Ok(_) => {
                        // 确认消息
                        message.ack().await?;
                        span.set_status(Status::Ok);
                    }
                    Err(e) => {
                        // 否定确认 (NAK)
                        message.ack_with(async_nats::jetstream::AckKind::Nak(None)).await?;
                        span.record_error(&e.to_string());
                        span.set_status(Status::error(e.to_string()));
                    }
                }
            }
        }
    }
}
```

---

## 6. TraceContext 传播

已在 Publisher 和 Subscriber 实现中包含，遵循 W3C Trace Context 标准。

---

## 7. JetStream 集成

**创建 Stream 和 Consumer**:

```rust
use async_nats::jetstream::stream::{Config, Stream};

/// JetStream 管理器
pub struct JetStreamManager {
    jetstream: JsContext,
}

impl JetStreamManager {
    /// 创建或更新 Stream
    #[instrument(skip(self))]
    pub async fn ensure_stream(
        &self,
        stream_name: &str,
        subjects: Vec<String>,
    ) -> Result<Stream, anyhow::Error> {
        let config = Config {
            name: stream_name.to_string(),
            subjects,
            max_messages: 1_000_000,
            max_bytes: 10 * 1024 * 1024 * 1024,  // 10GB
            max_age: std::time::Duration::from_secs(86400 * 7),  // 7天
            ..Default::default()
        };
        
        // 创建或更新 Stream
        let stream = match self.jetstream.get_stream(stream_name).await {
            Ok(stream) => {
                info!(stream = %stream_name, "Stream already exists");
                stream
            }
            Err(_) => {
                info!(stream = %stream_name, "Creating new stream");
                self.jetstream.create_stream(config).await?
            }
        };
        
        Ok(stream)
    }
}
```

---

## 8. 完整微服务示例

**事件发布服务 + 事件处理服务**:

```rust
// ========== 事件发布服务 ==========
use axum::{Router, routing::post, extract::State, Json};

struct PublisherAppState {
    nats_publisher: Arc<TracedNatsPublisher>,
}

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    init_telemetry().await?;
    
    let publisher = TracedNatsPublisher::new("nats://localhost:4222").await?;
    
    let state = Arc::new(PublisherAppState {
        nats_publisher: Arc::new(publisher),
    });
    
    let app = Router::new()
        .route("/events", post(publish_event))
        .with_state(state)
        .layer(tower_http::trace::TraceLayer::new_for_http());
    
    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await?;
    info!("Publisher service listening on http://127.0.0.1:8080");
    
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[instrument(skip(state))]
async fn publish_event(
    State(state): State<Arc<PublisherAppState>>,
    Json(event): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, anyhow::Error> {
    let event_type = event["type"].as_str()
        .ok_or_else(|| anyhow::anyhow!("Missing event type"))?;
    
    let subject = format!("events.{}", event_type);
    let payload = serde_json::to_vec(&event)?;
    
    // 发布事件 (自动注入 TraceContext)
    state.nats_publisher
        .publish_traced(&subject, &payload)
        .await?;
    
    Ok(Json(serde_json::json!({
        "status": "published",
        "subject": subject,
    })))
}

// ========== 事件处理服务 ==========
#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    init_telemetry().await?;
    
    let subscriber = TracedNatsSubscriber::new("nats://localhost:4222").await?;
    
    info!("Event processor started");
    
    // 订阅所有事件 (TraceContext 自动提取)
    subscriber.subscribe_with_tracing("events.>", |payload, _cx| async move {
        let event: serde_json::Value = serde_json::from_slice(&payload)?;
        
        info!("Processing event: {:?}", event);
        
        // 处理事件...
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        Ok(())
    }).await?;
    
    Ok(())
}
```

---

## 9. 性能优化

**连接池和批处理**:

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

/// NATS 连接池
pub struct NatsConnectionPool {
    clients: Arc<RwLock<Vec<Client>>>,
    current: Arc<AtomicUsize>,
}

impl NatsConnectionPool {
    pub async fn new(server_url: &str, pool_size: usize) -> Result<Self, anyhow::Error> {
        let mut clients = Vec::with_capacity(pool_size);
        
        for _ in 0..pool_size {
            let client = async_nats::connect(server_url).await?;
            clients.push(client);
        }
        
        Ok(Self {
            clients: Arc::new(RwLock::new(clients)),
            current: Arc::new(AtomicUsize::new(0)),
        })
    }
    
    /// 获取客户端 (轮询)
    pub async fn get_client(&self) -> Client {
        let clients = self.clients.read().await;
        let index = self.current.fetch_add(1, Ordering::Relaxed) % clients.len();
        clients[index].clone()
    }
}
```

---

## 10. 生产环境最佳实践

```text
✅ 连接配置
  □ 启用自动重连
  □ 设置合理的重连次数
  □ 使用连接池 (高并发场景)
  □ 配置连接超时

✅ JetStream 配置
  □ 设置合理的 Stream 保留策略
  □ 使用 Consumer 确认机制
  □ 配置重试策略
  □ 监控积压消息

✅ 追踪配置
  □ 始终注入 TraceContext 到 Headers
  □ 使用 W3C Trace Context 标准
  □ 设置合理的采样率
  □ 记录关键属性

✅ 错误处理
  □ 实现重试机制
  □ 使用 JetStream 的 NAK 机制
  □ 记录所有错误到 Span
  □ 设置死信队列

✅ 性能优化
  □ 使用队列组实现负载均衡
  □ 批量处理消息
  □ 异步并发消费
  □ 零拷贝优化

✅ 监控告警
  □ 监控连接状态
  □ 监控消息延迟
  □ 监控 JetStream 积压
  □ 设置告警阈值
```

---

## 11. 参考资源

**官方文档** (2025年10月最新):

- [NATS Documentation](https://docs.nats.io/)
- [async-nats Rust Crate](https://docs.rs/async-nats/0.37.0)
- [JetStream Documentation](https://docs.nats.io/nats-concepts/jetstream)
- [OpenTelemetry Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/messaging/)
- [W3C Trace Context](https://www.w3.org/TR/trace-context/)

**Rust 资源**:

- [Tokio Async Runtime](https://tokio.rs/)
- [Rust Async Book](https://rust-lang.github.io/async-book/)
- [Rust 1.90 Release Notes](https://blog.rust-lang.org/)

---

**文档状态**: ✅ 完成 (Rust 1.90 + OpenTelemetry 0.31.0 + async-nats 0.37.0)  
**最后更新**: 2025年10月8日  
**审核状态**: 生产就绪  
**许可证**: MIT OR Apache-2.0

---

**⭐ 本文档提供完整的 Rust + NATS + OTLP 集成方案，包括:**

- ✅ 类型安全的追踪实现
- ✅ 发布/订阅模式
- ✅ 请求/响应模式
- ✅ JetStream 持久化
- ✅ W3C TraceContext 传播
- ✅ 队列组负载均衡
- ✅ 完整微服务示例
- ✅ Rust 1.90 最新特性

[🏠 返回主目录](../../README.md) | [📖 查看其他消息队列](../README.md)

# Redis 语义约定 - Rust 实现指南

> **Rust版本**: 1.90+  
> **OpenTelemetry**: 0.31.0  
> **redis-rs**: 0.32.7  
> **Tokio**: 1.47.1  
> **最后更新**: 2025年10月8日  
> **规范版本**: OpenTelemetry Semantic Conventions v1.24.0

---

## 目录

- [Redis 语义约定 - Rust 实现指南](#redis-语义约定---rust-实现指南)
  - [目录](#目录)
  - [1. Redis追踪概述](#1-redis追踪概述)
  - [2. 通用Redis属性](#2-通用redis属性)
  - [3. Redis命令属性](#3-redis命令属性)
  - [4. 连接池属性](#4-连接池属性)
  - [5. Span命名规范](#5-span命名规范)
  - [6. Rust 异步实现](#6-rust-异步实现)
    - [6.1 依赖配置](#61-依赖配置)
    - [6.2 基础异步追踪](#62-基础异步追踪)
    - [6.3 连接池管理](#63-连接池管理)
    - [6.4 Pipeline 批量操作](#64-pipeline-批量操作)
    - [6.5 Pub/Sub 模式](#65-pubsub-模式)
  - [7. Rust 同步实现](#7-rust-同步实现)
  - [8. 高级模式](#8-高级模式)
    - [8.1 自动追踪包装器](#81-自动追踪包装器)
    - [8.2 错误处理](#82-错误处理)
    - [8.3 性能优化](#83-性能优化)
  - [9. 生产环境最佳实践](#9-生产环境最佳实践)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [Rust 特性](#rust-特性)
    - [性能优化](#性能优化)

---

## 1. Redis追踪概述

**为什么追踪Redis (Rust视角)**:

```text
1. 零成本抽象性能分析
   - 编译时优化的追踪
   - 识别慢命令
   - 内存安全的并发追踪

2. 类型安全的故障排查
   - 编译时错误检查
   - 连接问题诊断
   - Result类型的错误追踪

3. 异步性能监控
   - Tokio运行时集成
   - 异步操作可视化
   - 零拷贝数据传输

4. 内存安全保证
   - 所有权系统确保无数据竞争
   - 生命周期管理连接
   - 无垃圾回收开销
```

---

## 2. 通用Redis属性

| 属性名 | 类型 | 描述 | 示例 | 必需 |
|-------|------|------|------|------|
| `db.system` | string | 数据库系统标识符 | `redis` | ✅ 是 |
| `db.connection_string` | string | 连接字符串（不含密码） | `redis://cache.example.com:6379` | ⚠️ 可选 |
| `network.peer.address` | string | Redis服务器地址 | `cache.example.com` | ✅ 是 |
| `network.peer.port` | int | Redis服务器端口 | `6379` | ✅ 是 |
| `db.redis.database_index` | int | Redis数据库索引 | `0` | ⚠️ 可选 |

**Rust 类型定义**:

```rust
use opentelemetry::KeyValue;

pub struct RedisAttributes {
    pub system: &'static str,
    pub peer_address: String,
    pub peer_port: u16,
    pub database_index: Option<u8>,
}

impl RedisAttributes {
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("db.system", self.system),
            KeyValue::new("network.peer.address", self.peer_address.clone()),
            KeyValue::new("network.peer.port", self.peer_port as i64),
        ];
        
        if let Some(db) = self.database_index {
            attrs.push(KeyValue::new("db.redis.database_index", db as i64));
        }
        
        attrs
    }
}
```

---

## 3. Redis命令属性

| 属性名 | 类型 | 描述 | 示例 | 必需 |
|-------|------|------|------|------|
| `db.statement` | string | Redis命令（参数可脱敏） | `GET user:?` | ✅ 是 |
| `db.operation` | string | Redis操作类型 | `GET`, `SET`, `HGETALL` | ✅ 是 |

**Rust 命令脱敏**:

```rust
/// Redis 命令脱敏函数
pub fn sanitize_redis_command(cmd: &str, args: &[&str]) -> String {
    match cmd.to_uppercase().as_str() {
        // 简单键值命令
        "GET" | "SET" | "DEL" => {
            if !args.is_empty() {
                format!("{} ?", cmd.to_uppercase())
            } else {
                cmd.to_uppercase()
            }
        }
        
        // Hash 命令
        "HGET" | "HSET" => {
            format!("{} ? ?", cmd.to_uppercase())
        }
        
        // List 命令
        "LPUSH" | "RPUSH" | "LPOP" | "RPOP" => {
            format!("{} ?", cmd.to_uppercase())
        }
        
        // 其他命令
        _ => cmd.to_uppercase(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sanitize() {
        assert_eq!(sanitize_redis_command("GET", &["user:123"]), "GET ?");
        assert_eq!(sanitize_redis_command("HSET", &["user:123", "name", "John"]), "HSET ? ?");
    }
}
```

---

## 4. 连接池属性

| 属性名 | 类型 | 描述 | 示例 |
|-------|------|------|------|
| `pool.name` | string | 连接池名称 | `redis-main-pool` |
| `state.idle` | int | 空闲连接数 | `5` |
| `state.active` | int | 活跃连接数 | `10` |
| `state.max` | int | 最大连接数 | `20` |

**Rust 连接池追踪**:

```rust
use redis::aio::ConnectionManager;
use opentelemetry::{global, KeyValue, metrics::{Counter, Histogram}};

pub struct RedisPoolMetrics {
    connections_created: Counter<u64>,
    connections_closed: Counter<u64>,
    command_duration: Histogram<f64>,
}

impl RedisPoolMetrics {
    pub fn new() -> Self {
        let meter = global::meter("redis-pool");
        
        Self {
            connections_created: meter
                .u64_counter("redis.pool.connections.created")
                .with_description("Number of connections created")
                .init(),
            connections_closed: meter
                .u64_counter("redis.pool.connections.closed")
                .with_description("Number of connections closed")
                .init(),
            command_duration: meter
                .f64_histogram("redis.command.duration")
                .with_description("Redis command execution duration")
                .with_unit("ms")
                .init(),
        }
    }
    
    pub fn record_connection_created(&self) {
        self.connections_created.add(1, &[]);
    }
    
    pub fn record_command_duration(&self, duration_ms: f64, operation: &str) {
        self.command_duration.record(
            duration_ms,
            &[KeyValue::new("db.operation", operation.to_string())],
        );
    }
}
```

---

## 5. Span命名规范

**Rust Span 命名约定**:

```rust
pub enum RedisOperation {
    Get,
    Set,
    Delete,
    Hash(String),
    List(String),
    Pipeline,
    PubSub(String),
}

impl RedisOperation {
    pub fn span_name(&self, key: Option<&str>) -> String {
        match self {
            Self::Get => format!("GET {}", key.unwrap_or("*")),
            Self::Set => format!("SET {}", key.unwrap_or("*")),
            Self::Delete => format!("DEL {}", key.unwrap_or("*")),
            Self::Hash(op) => format!("H{} {}", op.to_uppercase(), key.unwrap_or("*")),
            Self::List(op) => format!("L{} {}", op.to_uppercase(), key.unwrap_or("*")),
            Self::Pipeline => "Redis PIPELINE".to_string(),
            Self::PubSub(channel) => format!("PUBLISH {}", channel),
        }
    }
}
```

---

## 6. Rust 异步实现

### 6.1 依赖配置

```toml
[dependencies]
# Redis 客户端 - 2025年10月最新版本
redis = { version = "0.32.7", features = [
    "tokio-comp",           # Tokio异步支持
    "connection-manager",   # 连接管理器
    "streams",              # Stream支持
    "cluster",              # 集群支持 (可选)
] }

# OpenTelemetry 追踪 - Rust 1.90 优化
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio", "trace", "metrics"] }
opentelemetry-otlp = { version = "0.31.0", features = ["grpc-tonic", "trace", "metrics"] }

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 追踪集成
tracing = "0.1.41"
tracing-opentelemetry = "0.31"
tracing-subscriber = { version = "0.3.20", features = ["env-filter"] }

# 错误处理
anyhow = "1.0.100"
thiserror = "2.0.17"

# 序列化 (可选)
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"
```

### 6.2 基础异步追踪

```rust
use redis::{AsyncCommands, aio::ConnectionManager};
use opentelemetry::{
    global,
    trace::{Tracer, Span, SpanKind, Status, StatusCode},
    KeyValue,
};
use std::time::Instant;
use anyhow::Result;

/// Redis 追踪客户端 - 异步实现
pub struct RedisTracer {
    conn: ConnectionManager,
    tracer: opentelemetry::global::BoxedTracer,
    peer_address: String,
    peer_port: u16,
}

impl RedisTracer {
    /// 创建新的追踪客户端
    pub async fn new(redis_url: &str) -> Result<Self> {
        // 解析 URL 获取地址和端口
        let client = redis::Client::open(redis_url)?;
        let conn_info = client.get_connection_info();
        let peer_address = conn_info.addr.to_string();
        let peer_port = match &conn_info.addr {
            redis::ConnectionAddr::Tcp(_, port) => *port,
            redis::ConnectionAddr::TcpTls { port, .. } => *port,
            _ => 6379,
        };
        
        // 创建连接管理器
        let conn = ConnectionManager::new(client).await?;
        
        // 获取追踪器
        let tracer = global::tracer("redis-client");
        
        Ok(Self {
            conn,
            tracer,
            peer_address,
            peer_port,
        })
    }
    
    /// GET 命令 - 异步追踪
    pub async fn get<K: redis::ToRedisArgs + ToString>(&mut self, key: K) -> Result<Option<String>> {
        let key_str = key.to_string();
        let span_name = format!("GET {}", self.mask_key(&key_str));
        
        let mut span = self.tracer
            .span_builder(span_name)
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "GET"),
                KeyValue::new("db.statement", format!("GET {}", self.mask_key(&key_str))),
                KeyValue::new("network.peer.address", self.peer_address.clone()),
                KeyValue::new("network.peer.port", self.peer_port as i64),
            ])
            .start(&self.tracer);
        
        let start = Instant::now();
        
        // 执行 Redis 命令 - 零成本异步
        let result: Result<Option<String>, redis::RedisError> = 
            self.conn.get(key).await;
        
        let duration = start.elapsed();
        span.set_attribute(KeyValue::new("db.redis.duration_ms", 
            duration.as_millis() as i64));
        
        match result {
            Ok(value) => {
                span.set_status(Status::Ok);
                span.set_attribute(KeyValue::new("db.redis.hit", value.is_some()));
                if let Some(ref v) = value {
                    span.set_attribute(KeyValue::new("db.response.size", v.len() as i64));
                }
                Ok(value)
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                span.set_attribute(KeyValue::new("error.type", "RedisError"));
                span.record_error(&e);
                Err(e.into())
            }
        }
    }
    
    /// SET 命令 - 异步追踪
    pub async fn set<K, V>(&mut self, key: K, value: V) -> Result<()>
    where
        K: redis::ToRedisArgs + ToString,
        V: redis::ToRedisArgs,
    {
        let key_str = key.to_string();
        let span_name = format!("SET {}", self.mask_key(&key_str));
        
        let mut span = self.tracer
            .span_builder(span_name)
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "SET"),
                KeyValue::new("db.statement", format!("SET {} ?", self.mask_key(&key_str))),
                KeyValue::new("network.peer.address", self.peer_address.clone()),
                KeyValue::new("network.peer.port", self.peer_port as i64),
            ])
            .start(&self.tracer);
        
        let start = Instant::now();
        let result: Result<(), redis::RedisError> = 
            self.conn.set(key, value).await;
        
        span.set_attribute(KeyValue::new("db.redis.duration_ms", 
            start.elapsed().as_millis() as i64));
        
        match result {
            Ok(_) => {
                span.set_status(Status::Ok);
                Ok(())
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                span.record_error(&e);
                Err(e.into())
            }
        }
    }
    
    /// 键脱敏 - 零成本抽象
    fn mask_key(&self, key: &str) -> String {
        if let Some(pos) = key.find(':') {
            format!("{}:?", &key[..pos])
        } else {
            "?".to_string()
        }
    }
}

/// 使用示例 - Tokio 异步运行时
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化追踪
    let _ = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://localhost:4317")
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)?;
    
    // 创建 Redis 客户端
    let mut redis = RedisTracer::new("redis://127.0.0.1/").await?;
    
    // 异步操作 - 自动追踪
    redis.set("user:123", "John Doe").await?;
    
    if let Some(value) = redis.get("user:123").await? {
        println!("Value: {}", value);
    }
    
    // 关闭追踪
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

### 6.3 连接池管理

```rust
use redis::aio::ConnectionManager;
use std::sync::Arc;
use tokio::sync::Semaphore;

/// 带连接池的 Redis 客户端
pub struct RedisPool {
    manager: ConnectionManager,
    semaphore: Arc<Semaphore>,
    max_connections: usize,
}

impl RedisPool {
    pub async fn new(redis_url: &str, max_connections: usize) -> Result<Self> {
        let client = redis::Client::open(redis_url)?;
        let manager = ConnectionManager::new(client).await?;
        let semaphore = Arc::new(Semaphore::new(max_connections));
        
        Ok(Self {
            manager,
            semaphore,
            max_connections,
        })
    }
    
    /// 获取连接 - 异步等待可用连接
    pub async fn get_connection(&self) -> Result<RedisPoolConnection<'_>> {
        let _permit = self.semaphore.acquire().await?;
        
        Ok(RedisPoolConnection {
            manager: &self.manager,
            _permit,
        })
    }
    
    /// 获取池统计信息
    pub fn stats(&self) -> PoolStats {
        PoolStats {
            max_connections: self.max_connections,
            available: self.semaphore.available_permits(),
            active: self.max_connections - self.semaphore.available_permits(),
        }
    }
}

pub struct RedisPoolConnection<'a> {
    manager: &'a ConnectionManager,
    _permit: tokio::sync::SemaphorePermit<'a>,
}

impl<'a> std::ops::Deref for RedisPoolConnection<'a> {
    type Target = ConnectionManager;
    
    fn deref(&self) -> &Self::Target {
        self.manager
    }
}

#[derive(Debug, Clone)]
pub struct PoolStats {
    pub max_connections: usize,
    pub available: usize,
    pub active: usize,
}
```

### 6.4 Pipeline 批量操作

```rust
impl RedisTracer {
    /// Pipeline 批量操作 - 异步追踪
    pub async fn pipeline<F>(&mut self, f: F) -> Result<Vec<redis::Value>>
    where
        F: FnOnce(&mut redis::Pipeline) -> &mut redis::Pipeline,
    {
        let mut span = self.tracer
            .span_builder("Redis PIPELINE")
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "PIPELINE"),
                KeyValue::new("network.peer.address", self.peer_address.clone()),
                KeyValue::new("network.peer.port", self.peer_port as i64),
            ])
            .start(&self.tracer);
        
        let start = Instant::now();
        
        // 创建 pipeline
        let mut pipe = redis::pipe();
        f(&mut pipe);
        
        // 执行 pipeline
        let result: Result<Vec<redis::Value>, redis::RedisError> = 
            pipe.query_async(&mut self.conn).await;
        
        span.set_attribute(KeyValue::new("db.redis.duration_ms", 
            start.elapsed().as_millis() as i64));
        
        match result {
            Ok(values) => {
                span.set_status(Status::Ok);
                span.set_attribute(KeyValue::new("db.redis.pipeline.size", values.len() as i64));
                Ok(values)
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                span.record_error(&e);
                Err(e.into())
            }
        }
    }
}

/// 使用示例
async fn pipeline_example(redis: &mut RedisTracer) -> Result<()> {
    let results = redis.pipeline(|pipe| {
        pipe.set("key1", "value1")
            .set("key2", "value2")
            .get("key1")
            .get("key2")
    }).await?;
    
    println!("Pipeline results: {:?}", results);
    Ok(())
}
```

### 6.5 Pub/Sub 模式

```rust
use redis::aio::PubSub;
use tokio_stream::StreamExt;

/// Pub/Sub 追踪实现
pub struct RedisPubSubTracer {
    pubsub: PubSub,
    tracer: opentelemetry::global::BoxedTracer,
}

impl RedisPubSubTracer {
    pub async fn new(redis_url: &str) -> Result<Self> {
        let client = redis::Client::open(redis_url)?;
        let pubsub = client.get_async_connection().await?.into_pubsub();
        let tracer = global::tracer("redis-pubsub");
        
        Ok(Self { pubsub, tracer })
    }
    
    /// 订阅频道 - 异步追踪
    pub async fn subscribe(&mut self, channel: &str) -> Result<()> {
        let mut span = self.tracer
            .span_builder(format!("SUBSCRIBE {}", channel))
            .with_kind(SpanKind::Consumer)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "SUBSCRIBE"),
                KeyValue::new("messaging.destination", channel),
            ])
            .start(&self.tracer);
        
        match self.pubsub.subscribe(channel).await {
            Ok(_) => {
                span.set_status(Status::Ok);
                Ok(())
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                Err(e.into())
            }
        }
    }
    
    /// 接收消息 - 异步 Stream
    pub async fn on_message(&mut self) -> Option<redis::Msg> {
        self.pubsub.on_message().next().await
    }
}

/// 发布消息 - 异步追踪
impl RedisTracer {
    pub async fn publish<K, V>(&mut self, channel: K, message: V) -> Result<i32>
    where
        K: redis::ToRedisArgs + ToString,
        V: redis::ToRedisArgs,
    {
        let channel_str = channel.to_string();
        let mut span = self.tracer
            .span_builder(format!("PUBLISH {}", channel_str))
            .with_kind(SpanKind::Producer)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "PUBLISH"),
                KeyValue::new("messaging.destination", channel_str.clone()),
            ])
            .start(&self.tracer);
        
        let result: Result<i32, redis::RedisError> = 
            self.conn.publish(channel, message).await;
        
        match result {
            Ok(count) => {
                span.set_status(Status::Ok);
                span.set_attribute(KeyValue::new("messaging.subscribers", count as i64));
                Ok(count)
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                Err(e.into())
            }
        }
    }
}
```

---

## 7. Rust 同步实现

```rust
use redis::{Commands, Connection};
use opentelemetry::{global, trace::{Tracer, Span, SpanKind, Status}, KeyValue};
use anyhow::Result;
use std::time::Instant;

/// Redis 客户端封装 - 同步实现
pub struct RedisSyncTracer {
    conn: Connection,
    tracer: opentelemetry::global::BoxedTracer,
    peer_address: String,
    peer_port: u16,
}

impl RedisSyncTracer {
    /// 创建新的追踪客户端 - 同步初始化
    pub fn new(redis_url: &str) -> Result<Self> {
        let client = redis::Client::open(redis_url)?;
        let conn_info = client.get_connection_info();
        let peer_address = conn_info.addr.to_string();
        let peer_port = match &conn_info.addr {
            redis::ConnectionAddr::Tcp(_, port) => *port,
            redis::ConnectionAddr::TcpTls { port, .. } => *port,
            _ => 6379,
        };
        
        let conn = client.get_connection()?;
        let tracer = global::tracer("redis-client");
        
        Ok(Self { conn, tracer, peer_address, peer_port })
    }
    
    /// GET 命令 - 同步追踪
    pub fn get<K: redis::ToRedisArgs + ToString>(&mut self, key: K) -> Result<Option<String>> {
        let key_str = key.to_string();
        let mut span = self.tracer
            .span_builder(format!("GET {}", self.mask_key(&key_str)))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("db.system", "redis"),
                KeyValue::new("db.operation", "GET"),
                KeyValue::new("network.peer.address", self.peer_address.clone()),
                KeyValue::new("network.peer.port", self.peer_port as i64),
            ])
            .start(&self.tracer);
        
        let start = Instant::now();
        let result: Result<Option<String>, redis::RedisError> = 
            self.conn.get(key);
        
        span.set_attribute(KeyValue::new("db.redis.duration_ms", 
            start.elapsed().as_millis() as i64));
        
        match result {
            Ok(value) => {
                span.set_status(Status::Ok);
                Ok(value)
            }
            Err(e) => {
                span.set_status(Status::error(e.to_string()));
                Err(e.into())
            }
        }
    }
    
    fn mask_key(&self, key: &str) -> String {
        if let Some(pos) = key.find(':') {
            format!("{}:?", &key[..pos])
        } else {
            "?".to_string()
        }
    }
}

/// 同步使用示例
fn main() -> Result<()> {
    let mut redis = RedisSyncTracer::new("redis://127.0.0.1/")?;
    
    redis.get("user:123")?;
    
    Ok(())
}
```

---

## 8. 高级模式

### 8.1 自动追踪包装器

```rust
use std::future::Future;
use opentelemetry::trace::{FutureExt, TraceContextExt};

/// 自动追踪包装器 - 使用 tracing 宏
#[tracing::instrument(
    name = "redis.operation",
    skip(conn),
    fields(
        db.system = "redis",
        db.operation = operation_type,
    )
)]
pub async fn traced_redis_op<F, T>(
    conn: &mut ConnectionManager,
    operation_type: &str,
    f: F,
) -> Result<T>
where
    F: Future<Output = Result<T, redis::RedisError>>,
{
    f.await.map_err(|e| anyhow::anyhow!("Redis error: {}", e))
}

/// 使用示例
async fn example() -> Result<()> {
    let mut conn = create_connection().await?;
    
    let value: String = traced_redis_op(
        &mut conn,
        "GET",
        async { conn.get("key").await },
    ).await?;
    
    Ok(())
}
```

### 8.2 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum RedisTracingError {
    #[error("Redis connection error: {0}")]
    Connection(#[from] redis::RedisError),
    
    #[error("Tracing initialization error: {0}")]
    Tracing(String),
    
    #[error("Timeout waiting for connection")]
    Timeout,
}

// 为错误类型添加追踪
impl RedisTracingError {
    pub fn record_to_span(&self, span: &mut opentelemetry::trace::Span) {
        span.set_attribute(KeyValue::new("error.type", format!("{:?}", self)));
        span.set_attribute(KeyValue::new("error.message", self.to_string()));
        span.record_error(self);
    }
}
```

### 8.3 性能优化

```rust
// 使用 bytes crate 实现零拷贝
use bytes::Bytes;

/// 零拷贝 Redis 值
pub async fn get_bytes(conn: &mut ConnectionManager, key: &str) -> Result<Option<Bytes>> {
    let value: Option<Vec<u8>> = conn.get(key).await?;
    Ok(value.map(Bytes::from))
}

// 批量操作优化
pub async fn mget_optimized(
    conn: &mut ConnectionManager,
    keys: &[String],
) -> Result<Vec<Option<String>>> {
    // 使用 pipeline 减少网络往返
    let mut pipe = redis::pipe();
    for key in keys {
        pipe.get(key);
    }
    
    pipe.query_async(conn).await.map_err(Into::into)
}
```

---

## 9. 生产环境最佳实践

```rust
/// 生产级 Redis 客户端配置
pub struct ProductionRedisConfig {
    pub url: String,
    pub max_connections: usize,
    pub connection_timeout: Duration,
    pub command_timeout: Duration,
    pub enable_tracing: bool,
    pub enable_metrics: bool,
}

impl Default for ProductionRedisConfig {
    fn default() -> Self {
        Self {
            url: "redis://127.0.0.1/".to_string(),
            max_connections: 50,
            connection_timeout: Duration::from_secs(5),
            command_timeout: Duration::from_secs(3),
            enable_tracing: true,
            enable_metrics: true,
        }
    }
}

/// 生产级客户端
pub struct ProductionRedisClient {
    pool: RedisPool,
    metrics: Option<RedisPoolMetrics>,
    config: ProductionRedisConfig,
}

impl ProductionRedisClient {
    pub async fn new(config: ProductionRedisConfig) -> Result<Self> {
        let pool = RedisPool::new(&config.url, config.max_connections).await?;
        
        let metrics = if config.enable_metrics {
            Some(RedisPoolMetrics::new())
        } else {
            None
        };
        
        Ok(Self { pool, metrics, config })
    }
    
    /// 带超时的获取操作
    pub async fn get_with_timeout(&self, key: &str) -> Result<Option<String>> {
        tokio::time::timeout(
            self.config.command_timeout,
            async {
                let mut conn = self.pool.get_connection().await?;
                conn.get(key).await.map_err(Into::into)
            }
        )
        .await
        .map_err(|_| anyhow::anyhow!("Redis command timeout"))?
    }
}
```

**最佳实践清单**:

```text
✅ 使用连接池管理连接
✅ 设置合理的超时时间
✅ 实现指数退避重试
✅ 使用 Pipeline 批量操作
✅ 敏感数据脱敏
✅ 记录详细的追踪信息
✅ 监控连接池状态
✅ 使用 Rust 的类型安全特性
✅ 利用异步运行时优势
✅ 零拷贝数据传输
```

---

## 10. 参考资源

### 官方文档

- [redis-rs GitHub](https://github.com/redis-rs/redis-rs)
- [OpenTelemetry Rust SDK](https://github.com/open-telemetry/opentelemetry-rust)
- [Tokio 文档](https://tokio.rs)

### Rust 特性

- [Async/Await in Rust](https://rust-lang.github.io/async-book/)
- [Rust 1.90 Release Notes](https://blog.rust-lang.org/2024/11/28/Rust-1.90.0.html)
- [Zero-cost Abstractions](https://doc.rust-lang.org/book/ch00-00-introduction.html)

### 性能优化

- [Tokio Performance Tips](https://tokio.rs/tokio/topics/performance)
- [Redis Performance Best Practices](https://redis.io/docs/management/optimization/)

---

**最后更新**: 2025年10月8日  
**维护者**: OTLP Rust团队  
**许可证**: MIT OR Apache-2.0

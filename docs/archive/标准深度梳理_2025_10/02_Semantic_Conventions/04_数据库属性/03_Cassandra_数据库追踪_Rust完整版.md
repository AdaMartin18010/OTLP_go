# Cassandra 数据库追踪 - Rust 完整实现指南

> **版本信息**
>
> - Rust: 1.90 (2024 Edition)
> - cdrs-tokio: 8.1.2 / scylla: 0.15.0
> - opentelemetry: 0.31.0
> - tracing: 0.1.41
> - tokio: 1.47.1
> - 更新日期: 2025-10-08

## 目录

- [Cassandra 数据库追踪 - Rust 完整实现指南](#cassandra-数据库追踪---rust-完整实现指南)
  - [目录](#目录)
  - [概述](#概述)
    - [Cassandra 特性](#cassandra-特性)
    - [Rust 优势](#rust-优势)
    - [驱动选择](#驱动选择)
  - [核心依赖配置](#核心依赖配置)
    - [Cargo.toml (ScyllaDB驱动)](#cargotoml-scylladb驱动)
  - [Cassandra 语义约定](#cassandra-语义约定)
    - [核心属性](#核心属性)
    - [Rust 实现](#rust-实现)
  - [基础集成 - ScyllaDB 驱动](#基础集成---scylladb-驱动)
    - [1. 客户端初始化](#1-客户端初始化)
    - [2. 基础 CRUD 操作](#2-基础-crud-操作)
  - [高级追踪模式](#高级追踪模式)
    - [1. 批量操作](#1-批量操作)
    - [2. 预处理语句](#2-预处理语句)
    - [3. 异步批量插入](#3-异步批量插入)
  - [一致性级别管理](#一致性级别管理)
    - [一致性级别配置](#一致性级别配置)
  - [性能优化](#性能优化)
    - [1. 连接池监控](#1-连接池监控)
    - [2. 查询性能追踪](#2-查询性能追踪)
    - [3. 分页查询优化](#3-分页查询优化)
  - [错误处理](#错误处理)
    - [自定义错误类型](#自定义错误类型)
    - [错误追踪集成](#错误追踪集成)
  - [测试策略](#测试策略)
    - [集成测试](#集成测试)
  - [最佳实践](#最佳实践)
    - [1. 数据建模](#1-数据建模)
    - [2. 查询优化](#2-查询优化)
    - [3. 性能监控清单](#3-性能监控清单)
  - [完整示例](#完整示例)
    - [main.rs](#mainrs)
  - [总结](#总结)

---

## 概述

### Cassandra 特性

Apache Cassandra 是一个高性能、分布式 NoSQL 数据库，具有以下特点:

- **无中心架构**: Peer-to-peer 架构，无单点故障
- **线性扩展**: 可轻松水平扩展到数千节点
- **高可用性**: 多数据中心复制，故障自动恢复
- **可调一致性**: 从最终一致到强一致性可调
- **列族存储**: 宽列存储模型，灵活 Schema
- **CQL**: 类 SQL 查询语言，易于上手

### Rust 优势

- **零成本抽象**: 追踪开销最小化
- **类型安全**: 编译时保证查询正确性
- **异步性能**: Tokio 运行时高效处理 I/O
- **内存安全**: 无数据竞争和内存泄漏

### 驱动选择

Rust 生态中有两个主要的 Cassandra 驱动:

1. **scylla** (推荐): ScyllaDB 团队维护，高性能、功能完整
2. **cdrs-tokio**: 社区驱动，功能丰富但更新较慢

本文档主要使用 **scylla** 驱动。

---

## 核心依赖配置

### Cargo.toml (ScyllaDB驱动)

```toml
[package]
name = "cassandra-otlp-tracing"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

[dependencies]
# Cassandra 驱动
scylla = "0.15.0"
uuid = { version = "1.11.0", features = ["v4", "serde"] }

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

[dev-dependencies]
criterion = { version = "0.6.0", features = ["async_tokio"] }
tokio-test = "0.4.4"
testcontainers = "0.23.1"
```

---

## Cassandra 语义约定

### 核心属性

根据 OpenTelemetry 语义约定，Cassandra 追踪应包含以下属性:

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `db.system` | string | ✅ | 数据库系统标识符 | `cassandra` |
| `db.name` | string | ✅ | Keyspace 名称 | `myapp_keyspace` |
| `db.cassandra.table` | string | ✅ | 表名 | `users` |
| `db.operation` | string | ✅ | 操作类型 | `SELECT`, `INSERT`, `UPDATE` |
| `db.statement` | string | ❌ | CQL 语句 | `SELECT * FROM users WHERE id = ?` |
| `db.cassandra.consistency_level` | string | ❌ | 一致性级别 | `QUORUM`, `ONE`, `ALL` |
| `net.peer.name` | string | ✅ | Cassandra 节点地址 | `cassandra.example.com` |
| `net.peer.port` | integer | ✅ | Cassandra 端口 | `9042` |
| `db.cassandra.coordinator.id` | string | ❌ | 协调节点 ID | `node1` |
| `db.cassandra.speculative_execution_count` | integer | ❌ | 推测执行次数 | `2` |

### Rust 实现

```rust
use opentelemetry::{KeyValue, trace::SpanKind};
use tracing::Span;
use scylla::statement::Consistency;

/// Cassandra 操作追踪属性
#[derive(Debug, Clone)]
pub struct CassandraAttributes {
    pub keyspace: String,
    pub table: String,
    pub operation: String,
    pub statement: Option<String>,
    pub consistency_level: Option<Consistency>,
    pub host: String,
    pub port: u16,
}

impl CassandraAttributes {
    /// 转换为 OpenTelemetry KeyValue 数组
    pub fn to_key_values(&self) -> Vec<KeyValue> {
        let mut attrs = vec![
            KeyValue::new("db.system", "cassandra"),
            KeyValue::new("db.name", self.keyspace.clone()),
            KeyValue::new("db.cassandra.table", self.table.clone()),
            KeyValue::new("db.operation", self.operation.clone()),
            KeyValue::new("net.peer.name", self.host.clone()),
            KeyValue::new("net.peer.port", self.port as i64),
        ];

        if let Some(stmt) = &self.statement {
            attrs.push(KeyValue::new("db.statement", stmt.clone()));
        }

        if let Some(cl) = &self.consistency_level {
            attrs.push(KeyValue::new(
                "db.cassandra.consistency_level",
                format!("{:?}", cl),
            ));
        }

        attrs
    }

    /// 记录属性到 tracing Span
    pub fn record_to_span(&self, span: &Span) {
        span.record("db.system", "cassandra");
        span.record("db.name", self.keyspace.as_str());
        span.record("db.cassandra.table", self.table.as_str());
        span.record("db.operation", self.operation.as_str());
        span.record("net.peer.name", self.host.as_str());
        span.record("net.peer.port", self.port);

        if let Some(stmt) = &self.statement {
            span.record("db.statement", stmt.as_str());
        }

        if let Some(cl) = &self.consistency_level {
            span.record("db.cassandra.consistency_level", &format!("{:?}", cl));
        }
    }
}
```

---

## 基础集成 - ScyllaDB 驱动

### 1. 客户端初始化

```rust
use scylla::{Session, SessionBuilder};
use tracing::{info, instrument};
use anyhow::Result;

/// Cassandra 会话配置
pub struct CassandraConfig {
    pub nodes: Vec<String>,
    pub keyspace: String,
    pub username: Option<String>,
    pub password: Option<String>,
    pub compression: bool,
}

/// 创建带追踪的 Cassandra 会话
#[instrument(skip(config), fields(
    db.system = "cassandra",
    db.name = %config.keyspace
))]
pub async fn create_traced_session(config: CassandraConfig) -> Result<Session> {
    info!("Initializing Cassandra session with tracing");

    // 构建 Session
    let mut builder = SessionBuilder::new()
        .known_nodes(&config.nodes)
        .compression(if config.compression {
            Some(scylla::transport::Compression::Lz4)
        } else {
            None
        });

    // 添加认证
    if let (Some(username), Some(password)) = (&config.username, &config.password) {
        builder = builder.user(username, password);
    }

    // 创建会话
    let session = builder.build().await?;

    // 设置 Keyspace
    session.use_keyspace(&config.keyspace, false).await?;

    info!(
        keyspace = %config.keyspace,
        nodes = ?config.nodes,
        "Cassandra session initialized successfully"
    );

    Ok(session)
}
```

### 2. 基础 CRUD 操作

```rust
use scylla::{Session, IntoTypedRows};
use scylla::query::Query;
use scylla::macros::FromRow;
use serde::{Deserialize, Serialize};
use tracing::{info, error, instrument, warn};
use uuid::Uuid;

#[derive(Debug, Serialize, Deserialize, FromRow, Clone)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
    pub age: i32,
}

pub struct UserRepository {
    session: Session,
    keyspace: String,
}

impl UserRepository {
    pub fn new(session: Session, keyspace: String) -> Self {
        Self { session, keyspace }
    }

    /// 创建表
    #[instrument(
        skip(self),
        fields(
            db.system = "cassandra",
            db.operation = "CREATE TABLE",
            db.cassandra.table = "users"
        )
    )]
    pub async fn create_table(&self) -> Result<()> {
        info!("Creating users table");

        let create_table_cql = r#"
            CREATE TABLE IF NOT EXISTS users (
                id UUID PRIMARY KEY,
                name TEXT,
                email TEXT,
                age INT
            )
        "#;

        self.session.query_unpaged(create_table_cql, &[]).await?;

        info!("Users table created successfully");
        Ok(())
    }

    /// 插入用户 - 带追踪
    #[instrument(
        skip(self, user),
        fields(
            db.system = "cassandra",
            db.operation = "INSERT",
            db.cassandra.table = "users",
            user.email = %user.email
        )
    )]
    pub async fn insert_user(&self, user: &User) -> Result<()> {
        info!("Inserting user into Cassandra");

        let insert_cql = "INSERT INTO users (id, name, email, age) VALUES (?, ?, ?, ?)";

        let mut query = Query::new(insert_cql);
        query.set_consistency(scylla::statement::Consistency::Quorum);

        self.session
            .query_unpaged(query, (user.id, &user.name, &user.email, user.age))
            .await?;

        info!(
            user_id = %user.id,
            "User inserted successfully"
        );

        Ok(())
    }

    /// 查询用户 - 带追踪
    #[instrument(
        skip(self),
        fields(
            db.system = "cassandra",
            db.operation = "SELECT",
            db.cassandra.table = "users",
            user_id = %user_id
        )
    )]
    pub async fn find_user_by_id(&self, user_id: Uuid) -> Result<Option<User>> {
        info!("Finding user by ID");

        let select_cql = "SELECT id, name, email, age FROM users WHERE id = ?";

        let mut query = Query::new(select_cql);
        query.set_consistency(scylla::statement::Consistency::One);

        let result = self.session.query_unpaged(query, (user_id,)).await?;

        if let Some(rows) = result.rows {
            let mut typed_rows = rows.into_typed::<User>();
            
            if let Some(Ok(user)) = typed_rows.next() {
                info!(user_id = %user.id, "User found");
                return Ok(Some(user));
            }
        }

        warn!("User not found");
        Ok(None)
    }

    /// 更新用户 - 带追踪
    #[instrument(
        skip(self),
        fields(
            db.system = "cassandra",
            db.operation = "UPDATE",
            db.cassandra.table = "users",
            user_id = %user_id
        )
    )]
    pub async fn update_user_age(&self, user_id: Uuid, new_age: i32) -> Result<()> {
        info!(new_age = new_age, "Updating user age");

        let update_cql = "UPDATE users SET age = ? WHERE id = ?";

        let mut query = Query::new(update_cql);
        query.set_consistency(scylla::statement::Consistency::Quorum);

        self.session
            .query_unpaged(query, (new_age, user_id))
            .await?;

        info!("User age updated successfully");
        Ok(())
    }

    /// 删除用户 - 带追踪
    #[instrument(
        skip(self),
        fields(
            db.system = "cassandra",
            db.operation = "DELETE",
            db.cassandra.table = "users",
            user_id = %user_id
        )
    )]
    pub async fn delete_user(&self, user_id: Uuid) -> Result<()> {
        info!("Deleting user");

        let delete_cql = "DELETE FROM users WHERE id = ?";

        let mut query = Query::new(delete_cql);
        query.set_consistency(scylla::statement::Consistency::Quorum);

        self.session.query_unpaged(query, (user_id,)).await?;

        info!("User deleted successfully");
        Ok(())
    }

    /// 查询所有用户 (全表扫描 - 谨慎使用)
    #[instrument(
        skip(self),
        fields(
            db.system = "cassandra",
            db.operation = "SELECT",
            db.cassandra.table = "users",
            query.limit = limit
        )
    )]
    pub async fn find_all_users(&self, limit: i32) -> Result<Vec<User>> {
        info!("Finding all users");

        let select_cql = format!("SELECT id, name, email, age FROM users LIMIT {}", limit);

        let result = self.session.query_unpaged(select_cql, &[]).await?;

        let users = if let Some(rows) = result.rows {
            rows.into_typed::<User>()
                .filter_map(|r| r.ok())
                .collect()
        } else {
            Vec::new()
        };

        info!(
            users_count = users.len(),
            "Users found successfully"
        );

        Ok(users)
    }
}
```

---

## 高级追踪模式

### 1. 批量操作

```rust
use scylla::batch::Batch;
use tracing::{info, instrument};

impl UserRepository {
    /// 批量插入 - 带追踪
    #[instrument(
        skip(self, users),
        fields(
            db.system = "cassandra",
            db.operation = "BATCH INSERT",
            db.cassandra.table = "users",
            batch.size = users.len()
        )
    )]
    pub async fn batch_insert_users(&self, users: &[User]) -> Result<()> {
        info!(batch_size = users.len(), "Batch inserting users");

        let insert_cql = "INSERT INTO users (id, name, email, age) VALUES (?, ?, ?, ?)";

        let mut batch = Batch::default();
        batch.set_consistency(scylla::statement::Consistency::Quorum);

        for user in users {
            batch.append_statement(insert_cql);
        }

        // 准备批量参数
        let batch_values: Vec<_> = users
            .iter()
            .map(|u| (u.id, u.name.as_str(), u.email.as_str(), u.age))
            .collect();

        self.session.batch(&batch, batch_values).await?;

        info!(
            inserted_count = users.len(),
            "Batch insert completed"
        );

        Ok(())
    }

    /// 批量删除 - 带追踪
    #[instrument(
        skip(self, user_ids),
        fields(
            db.system = "cassandra",
            db.operation = "BATCH DELETE",
            db.cassandra.table = "users",
            batch.size = user_ids.len()
        )
    )]
    pub async fn batch_delete_users(&self, user_ids: &[Uuid]) -> Result<()> {
        info!(batch_size = user_ids.len(), "Batch deleting users");

        let delete_cql = "DELETE FROM users WHERE id = ?";

        let mut batch = Batch::default();
        batch.set_consistency(scylla::statement::Consistency::Quorum);

        for _ in user_ids {
            batch.append_statement(delete_cql);
        }

        let batch_values: Vec<_> = user_ids.iter().map(|&id| (id,)).collect();

        self.session.batch(&batch, batch_values).await?;

        info!(
            deleted_count = user_ids.len(),
            "Batch delete completed"
        );

        Ok(())
    }
}
```

### 2. 预处理语句

```rust
use scylla::prepared_statement::PreparedStatement;
use std::sync::Arc;
use tracing::instrument;

pub struct PreparedStatements {
    insert_user: Arc<PreparedStatement>,
    find_user_by_id: Arc<PreparedStatement>,
    update_user_age: Arc<PreparedStatement>,
}

impl PreparedStatements {
    #[instrument(skip(session))]
    pub async fn new(session: &Session) -> Result<Self> {
        info!("Preparing Cassandra statements");

        let insert_user = session
            .prepare("INSERT INTO users (id, name, email, age) VALUES (?, ?, ?, ?)")
            .await?;

        let find_user_by_id = session
            .prepare("SELECT id, name, email, age FROM users WHERE id = ?")
            .await?;

        let update_user_age = session
            .prepare("UPDATE users SET age = ? WHERE id = ?")
            .await?;

        info!("Prepared statements created");

        Ok(Self {
            insert_user: Arc::new(insert_user),
            find_user_by_id: Arc::new(find_user_by_id),
            update_user_age: Arc::new(update_user_age),
        })
    }
}

impl UserRepository {
    /// 使用预处理语句插入
    #[instrument(
        skip(self, prepared, user),
        fields(
            db.system = "cassandra",
            db.operation = "INSERT (prepared)",
            db.cassandra.table = "users"
        )
    )]
    pub async fn insert_user_prepared(
        &self,
        prepared: &PreparedStatement,
        user: &User,
    ) -> Result<()> {
        info!("Inserting user with prepared statement");

        self.session
            .execute_unpaged(prepared, (user.id, &user.name, &user.email, user.age))
            .await?;

        info!("User inserted successfully");
        Ok(())
    }
}
```

### 3. 异步批量插入

```rust
use futures::stream::{self, StreamExt};
use tracing::instrument;

impl UserRepository {
    /// 并发批量插入
    #[instrument(
        skip(self, users),
        fields(
            db.system = "cassandra",
            db.operation = "CONCURRENT INSERT",
            db.cassandra.table = "users",
            batch.size = users.len(),
            batch.concurrency = 10
        )
    )]
    pub async fn concurrent_insert_users(&self, users: Vec<User>) -> Result<Vec<Result<()>>> {
        info!(batch_size = users.len(), "Concurrent inserting users");

        let results = stream::iter(users)
            .map(|user| async move { self.insert_user(&user).await })
            .buffer_unordered(10) // 最多10个并发插入
            .collect::<Vec<_>>()
            .await;

        let success_count = results.iter().filter(|r| r.is_ok()).count();

        info!(
            total = results.len(),
            success = success_count,
            failed = results.len() - success_count,
            "Concurrent insert completed"
        );

        Ok(results)
    }
}
```

---

## 一致性级别管理

### 一致性级别配置

```rust
use scylla::statement::Consistency;
use tracing::instrument;

/// 一致性级别策略
#[derive(Debug, Clone, Copy)]
pub enum ConsistencyStrategy {
    /// 强一致性 (写: ALL, 读: QUORUM)
    Strong,
    /// 平衡 (写: QUORUM, 读: QUORUM)
    Balanced,
    /// 高性能 (写: ONE, 读: ONE)
    Fast,
    /// 自定义
    Custom(Consistency, Consistency),
}

impl ConsistencyStrategy {
    pub fn write_consistency(&self) -> Consistency {
        match self {
            Self::Strong => Consistency::All,
            Self::Balanced => Consistency::Quorum,
            Self::Fast => Consistency::One,
            Self::Custom(write, _) => *write,
        }
    }

    pub fn read_consistency(&self) -> Consistency {
        match self {
            Self::Strong => Consistency::Quorum,
            Self::Balanced => Consistency::Quorum,
            Self::Fast => Consistency::One,
            Self::Custom(_, read) => *read,
        }
    }
}

impl UserRepository {
    /// 使用自定义一致性级别查询
    #[instrument(
        skip(self),
        fields(
            db.system = "cassandra",
            db.operation = "SELECT",
            db.cassandra.table = "users",
            consistency_level = ?strategy.read_consistency()
        )
    )]
    pub async fn find_user_with_consistency(
        &self,
        user_id: Uuid,
        strategy: ConsistencyStrategy,
    ) -> Result<Option<User>> {
        info!("Finding user with custom consistency");

        let select_cql = "SELECT id, name, email, age FROM users WHERE id = ?";

        let mut query = Query::new(select_cql);
        query.set_consistency(strategy.read_consistency());

        let result = self.session.query_unpaged(query, (user_id,)).await?;

        if let Some(rows) = result.rows {
            let mut typed_rows = rows.into_typed::<User>();
            
            if let Some(Ok(user)) = typed_rows.next() {
                info!("User found");
                return Ok(Some(user));
            }
        }

        Ok(None)
    }
}
```

---

## 性能优化

### 1. 连接池监控

```rust
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tracing::{info, warn, instrument};

/// Cassandra 连接池监控器
pub struct SessionMonitor {
    session: Session,
    metrics: Arc<RwLock<SessionMetrics>>,
}

#[derive(Debug, Default, Clone)]
pub struct SessionMetrics {
    pub active_connections: u32,
    pub pending_requests: u32,
    pub total_requests: u64,
    pub failed_requests: u64,
}

impl SessionMonitor {
    pub fn new(session: Session) -> Self {
        Self {
            session,
            metrics: Arc::new(RwLock::new(SessionMetrics::default())),
        }
    }

    /// 启动监控任务
    #[instrument(skip(self))]
    pub fn start_monitoring(&self, interval: Duration) -> tokio::task::JoinHandle<()> {
        let metrics = Arc::clone(&self.metrics);

        tokio::spawn(async move {
            let mut interval_timer = tokio::time::interval(interval);

            loop {
                interval_timer.tick().await;

                let m = metrics.read().await;
                
                info!(
                    active_connections = m.active_connections,
                    pending_requests = m.pending_requests,
                    total_requests = m.total_requests,
                    failed_requests = m.failed_requests,
                    error_rate = (m.failed_requests as f64 / m.total_requests.max(1) as f64) * 100.0,
                    "Session metrics"
                );

                if m.pending_requests > 100 {
                    warn!("High number of pending requests detected!");
                }
            }
        })
    }

    /// 记录请求
    pub async fn record_request(&self, success: bool) {
        let mut m = self.metrics.write().await;
        m.total_requests += 1;
        if !success {
            m.failed_requests += 1;
        }
    }
}
```

### 2. 查询性能追踪

```rust
use std::time::Instant;
use tracing::{info, warn};

/// 查询性能追踪装饰器
pub async fn with_query_timing<F, T>(
    operation: &str,
    table: &str,
    f: F,
) -> Result<T>
where
    F: std::future::Future<Output = Result<T>>,
{
    let start = Instant::now();
    
    let result = f.await;
    
    let duration = start.elapsed();
    
    if duration > Duration::from_millis(50) {
        warn!(
            operation = operation,
            table = table,
            duration_ms = duration.as_millis() as u64,
            "Slow Cassandra query detected"
        );
    } else {
        info!(
            operation = operation,
            table = table,
            duration_ms = duration.as_millis() as u64,
            "Cassandra query completed"
        );
    }
    
    result
}

// 使用示例
impl UserRepository {
    pub async fn find_user_with_timing(&self, user_id: Uuid) -> Result<Option<User>> {
        with_query_timing("SELECT", "users", async {
            self.find_user_by_id(user_id).await
        })
        .await
    }
}
```

### 3. 分页查询优化

```rust
use scylla::query::Query;
use scylla::IntoTypedRows;
use tracing::instrument;

impl UserRepository {
    /// 分页查询
    #[instrument(
        skip(self, paging_state),
        fields(
            db.system = "cassandra",
            db.operation = "SELECT (paged)",
            db.cassandra.table = "users",
            page_size = page_size
        )
    )]
    pub async fn find_users_paged(
        &self,
        page_size: i32,
        paging_state: Option<Vec<u8>>,
    ) -> Result<(Vec<User>, Option<Vec<u8>>)> {
        info!("Finding users with pagination");

        let select_cql = "SELECT id, name, email, age FROM users";

        let mut query = Query::new(select_cql);
        query.set_page_size(page_size);

        if let Some(state) = paging_state {
            query.set_paging_state(state);
        }

        let result = self.session.query_unpaged(query, &[]).await?;

        let users = if let Some(rows) = result.rows {
            rows.into_typed::<User>()
                .filter_map(|r| r.ok())
                .collect()
        } else {
            Vec::new()
        };

        let next_paging_state = result.paging_state.map(|s| s.to_vec());

        info!(
            page_size = users.len(),
            has_next_page = next_paging_state.is_some(),
            "Paged query completed"
        );

        Ok((users, next_paging_state))
    }
}
```

---

## 错误处理

### 自定义错误类型

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CassandraError {
    #[error("Cassandra query error: {0}")]
    QueryError(#[from] scylla::transport::errors::QueryError),

    #[error("Cassandra new session error: {0}")]
    NewSessionError(#[from] scylla::transport::errors::NewSessionError),

    #[error("User not found: {id}")]
    UserNotFound { id: Uuid },

    #[error("Invalid consistency level: {0}")]
    InvalidConsistencyLevel(String),

    #[error("Batch operation failed: {0}")]
    BatchOperationFailed(String),

    #[error("Serialization error: {0}")]
    SerializationError(String),
}

impl CassandraError {
    /// 记录错误到当前 Span
    pub fn record_to_current_span(&self) {
        use tracing::Span;
        let span = Span::current();
        span.record("error", true);
        span.record("error.type", std::any::type_name::<Self>());
        span.record("error.message", &self.to_string());
    }
}
```

### 错误追踪集成

```rust
use tracing::error;

impl UserRepository {
    #[instrument(skip(self))]
    pub async fn find_user_or_error(&self, user_id: Uuid) -> Result<User, CassandraError> {
        match self.find_user_by_id(user_id).await {
            Ok(Some(user)) => Ok(user),
            Ok(None) => {
                let err = CassandraError::UserNotFound { id: user_id };
                err.record_to_current_span();
                error!(user_id = %user_id, "User not found");
                Err(err)
            }
            Err(e) => {
                let err = CassandraError::from(e);
                err.record_to_current_span();
                error!(user_id = %user_id, error = %err, "Database query failed");
                Err(err)
            }
        }
    }
}
```

---

## 测试策略

### 集成测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tracing_subscriber::prelude::*;

    async fn setup_test_session() -> Session {
        // 初始化追踪（用于测试观察）
        let _ = tracing_subscriber::registry()
            .with(tracing_subscriber::fmt::layer())
            .try_init();

        // 连接到本地 Cassandra
        let config = CassandraConfig {
            nodes: vec!["127.0.0.1:9042".to_string()],
            keyspace: "test_keyspace".to_string(),
            username: None,
            password: None,
            compression: true,
        };

        create_traced_session(config).await.unwrap()
    }

    #[tokio::test]
    async fn test_insert_and_find_user() {
        let session = setup_test_session().await;
        let repo = UserRepository::new(session, "test_keyspace".to_string());

        // 创建表
        repo.create_table().await.unwrap();

        // 插入用户
        let user = User {
            id: Uuid::new_v4(),
            name: "John Doe".to_string(),
            email: "john@example.com".to_string(),
            age: 30,
        };

        repo.insert_user(&user).await.unwrap();

        // 查找用户
        let found_user = repo.find_user_by_id(user.id).await.unwrap().unwrap();

        assert_eq!(found_user.name, "John Doe");
        assert_eq!(found_user.age, 30);
    }

    #[tokio::test]
    async fn test_update_user_age() {
        let session = setup_test_session().await;
        let repo = UserRepository::new(session, "test_keyspace".to_string());

        // 插入测试用户
        let user = User {
            id: Uuid::new_v4(),
            name: "Jane Doe".to_string(),
            email: "jane@example.com".to_string(),
            age: 25,
        };

        repo.insert_user(&user).await.unwrap();

        // 更新年龄
        repo.update_user_age(user.id, 26).await.unwrap();

        // 验证更新
        let found_user = repo.find_user_by_id(user.id).await.unwrap().unwrap();

        assert_eq!(found_user.age, 26);
    }

    #[tokio::test]
    async fn test_batch_insert() {
        let session = setup_test_session().await;
        let repo = UserRepository::new(session, "test_keyspace".to_string());

        repo.create_table().await.unwrap();

        let users = vec![
            User {
                id: Uuid::new_v4(),
                name: "User1".to_string(),
                email: "user1@example.com".to_string(),
                age: 20,
            },
            User {
                id: Uuid::new_v4(),
                name: "User2".to_string(),
                email: "user2@example.com".to_string(),
                age: 25,
            },
            User {
                id: Uuid::new_v4(),
                name: "User3".to_string(),
                email: "user3@example.com".to_string(),
                age: 30,
            },
        ];

        repo.batch_insert_users(&users).await.unwrap();

        // 验证批量插入
        for user in &users {
            let found = repo.find_user_by_id(user.id).await.unwrap();
            assert!(found.is_some());
        }
    }
}
```

---

## 最佳实践

### 1. 数据建模

```rust
// ✅ 推荐: 查询驱动的数据建模

// 按用户 ID 查询
// PRIMARY KEY (id)
pub struct UserById {
    pub id: Uuid,
    pub name: String,
    pub email: String,
}

// 按邮箱查询
// PRIMARY KEY (email)
pub struct UserByEmail {
    pub email: String,
    pub id: Uuid,
    pub name: String,
}

// 时序数据
// PRIMARY KEY ((user_id, date), timestamp)
pub struct UserActivity {
    pub user_id: Uuid,
    pub date: String,      // 分区键
    pub timestamp: i64,    // 聚簇键
    pub activity: String,
}
```

### 2. 查询优化

- **避免全表扫描**: 始终使用分区键查询
- **使用预处理语句**: 减少解析开销，提高性能
- **批量操作**: 使用 BATCH 语句减少网络往返
- **适当的一致性级别**: 根据业务需求选择
- **启用压缩**: 减少网络传输量

### 3. 性能监控清单

- ✅ 监控慢查询（> 50ms）
- ✅ 追踪一致性级别使用情况
- ✅ 记录错误率和类型
- ✅ 监控批量操作性能
- ✅ 追踪预处理语句缓存命中率

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
use uuid::Uuid;

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
                    opentelemetry::KeyValue::new("service.name", "cassandra-tracing-demo"),
                ])),
        )
        .install_batch(runtime::Tokio)?;

    // 初始化 tracing
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .init();

    info!("Starting Cassandra OTLP tracing demo");

    // 创建 Cassandra 会话
    let config = CassandraConfig {
        nodes: vec!["127.0.0.1:9042".to_string()],
        keyspace: "myapp_keyspace".to_string(),
        username: None,
        password: None,
        compression: true,
    };

    let session = create_traced_session(config).await?;
    let repo = UserRepository::new(session, "myapp_keyspace".to_string());

    // 创建表
    repo.create_table().await?;

    // 示例操作
    let user = User {
        id: Uuid::new_v4(),
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        age: 28,
    };

    repo.insert_user(&user).await?;
    info!(user_id = %user.id, "User created");

    let found_user = repo.find_user_by_id(user.id).await?.unwrap();
    info!(user = ?found_user, "User found");

    // 关闭追踪
    global::shutdown_tracer_provider();

    Ok(())
}
```

---

## 总结

本文档提供了 Cassandra 在 Rust 1.90 环境下的完整 OpenTelemetry 追踪集成方案：

1. ✅ **语义约定**: 完整实现 OpenTelemetry Cassandra 语义约定
2. ✅ **基础操作**: CRUD、批量、预处理语句等核心操作追踪
3. ✅ **一致性管理**: 可调一致性级别配置和追踪
4. ✅ **性能优化**: 连接池监控、查询性能追踪、分页优化
5. ✅ **错误处理**: 类型安全的错误处理和追踪集成
6. ✅ **测试支持**: 完整的集成测试
7. ✅ **最佳实践**: 数据建模、查询优化、监控建议

通过本文档的指导，您可以构建高性能、高可用、可观测性强的 Rust + Cassandra 应用。

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-08  
**维护者**: OTLP Rust Team  
**许可证**: MIT OR Apache-2.0

---

**相关资源**:

- [ScyllaDB Rust Driver](https://github.com/scylladb/scylla-rust-driver)
- [Apache Cassandra](https://cassandra.apache.org/)
- [OpenTelemetry Rust](https://github.com/open-telemetry/opentelemetry-rust)
- [CQL 语法参考](https://cassandra.apache.org/doc/latest/cql/)

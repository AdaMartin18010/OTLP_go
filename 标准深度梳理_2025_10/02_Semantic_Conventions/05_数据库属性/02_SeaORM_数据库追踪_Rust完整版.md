# SeaORM 数据库追踪 - Rust OTLP 完整实现

> **版本**: Rust 1.90 + SeaORM 1.1.6 + OpenTelemetry 0.31.0  
> **日期**: 2025年10月8日  
> **状态**: ✅ 生产就绪

---

## 📋 目录

- [概述](#概述)
- [依赖配置](#依赖配置)
- [核心概念](#核心概念)
- [基础集成](#基础集成)
- [实体追踪](#实体追踪)
- [查询追踪](#查询追踪)
- [事务追踪](#事务追踪)
- [连接池监控](#连接池监控)
- [关联查询追踪](#关联查询追踪)
- [批量操作追踪](#批量操作追踪)
- [迁移追踪](#迁移追踪)
- [错误处理](#错误处理)
- [性能优化](#性能优化)
- [完整示例](#完整示例)
- [最佳实践](#最佳实践)
- [参考资源](#参考资源)

---

## 概述

**SeaORM** 是一个现代的 Rust 异步 ORM 框架，基于 SQLx 构建，提供类型安全的数据库操作。本文档展示如何为 SeaORM 添加完整的 OpenTelemetry 追踪支持。

### 核心特性

- ✅ **类型安全**: 完全类型安全的实体和查询
- ✅ **异步优先**: 原生异步支持
- ✅ **多数据库**: PostgreSQL, MySQL, SQLite
- ✅ **关联查询**: 自动处理表关联
- ✅ **迁移管理**: 内置迁移系统
- ✅ **追踪集成**: 完整的 OTLP 追踪

### 数据库语义约定

遵循 [OpenTelemetry Database Semantic Conventions v1.28.0](https://opentelemetry.io/docs/specs/semconv/database/database-spans/):

| 属性 | 必需 | 描述 | 示例 |
|------|------|------|------|
| `db.system` | ✅ | 数据库系统 | `postgresql`, `mysql`, `sqlite` |
| `db.connection_string` | ❌ | 连接字符串 (需脱敏) | `postgresql://localhost/mydb` |
| `db.user` | ❌ | 数据库用户 | `app_user` |
| `db.name` | ✅ | 数据库名称 | `mydb` |
| `db.statement` | ✅ | SQL 语句 (参数化) | `SELECT * FROM users WHERE id = $1` |
| `db.operation` | ✅ | 操作类型 | `SELECT`, `INSERT`, `UPDATE`, `DELETE` |
| `db.sql.table` | ❌ | 主要表名 | `users` |
| `net.peer.name` | ❌ | 服务器主机名 | `localhost` |
| `net.peer.port` | ❌ | 服务器端口 | `5432` |
| `db.row_count` | ❌ | 受影响行数 | `1`, `42` |

---

## 依赖配置

### Cargo.toml

```toml
[dependencies]
# SeaORM
sea-orm = { version = "1.1.6", features = [
    "sqlx-postgres",    # PostgreSQL 支持
    "sqlx-mysql",       # MySQL 支持 (可选)
    "sqlx-sqlite",      # SQLite 支持 (可选)
    "runtime-tokio-rustls",
    "macros",           # 派生宏
    "with-chrono",      # 日期时间支持
    "with-json",        # JSON 支持
    "with-uuid",        # UUID 支持
] }

# OpenTelemetry
opentelemetry = "0.31.0"
opentelemetry_sdk = { version = "0.31.0", features = ["rt-tokio"] }
opentelemetry-otlp = { version = "0.31.0", features = ["http-json"] }
opentelemetry-semantic-conventions = "0.31.0"
tracing = "0.1.41"
tracing-subscriber = { version = "0.3.19", features = ["env-filter", "json"] }
tracing-opentelemetry = "0.31"

# 异步运行时
tokio = { version = "1.47.1", features = ["full"] }

# 错误处理
thiserror = "2.0.17"
anyhow = "1.0.100"

# 工具
uuid = { version = "1.18.1", features = ["v4", "serde"] }
chrono = "0.4.40"
serde = { version = "1.0.228", features = ["derive"] }
serde_json = "1.0.145"
```

---

## 核心概念

### 1. SeaORM 架构

```text
┌────────────────────────────────────────────┐
│          Application Layer                 │
│  (实体、查询构建器、事务管理)                   │
└─────────────────┬──────────────────────────┘
                  │
                  ▼
┌────────────────────────────────────────────┐
│         SeaORM Connection Pool             │
│  (DatabaseConnection, ConnectionTrait)     │
└─────────────────┬──────────────────────────┘
                  │
                  ▼
┌────────────────────────────────────────────┐
│           SQLx Backend                     │
│  (PgPool, MySqlPool, SqlitePool)           │
└─────────────────┬──────────────────────────┘
                  │
                  ▼
┌────────────────────────────────────────────┐
│           Database Server                  │
└────────────────────────────────────────────┘
```

### 2. 追踪集成点

```rust
use sea_orm::{
    Database, DatabaseConnection, EntityTrait, QueryTrait,
    ActiveModelTrait, ConnectionTrait,
};
use tracing::instrument;

// 1️⃣ 连接池创建
#[instrument(name = "db.connect")]
async fn connect_with_tracing(url: &str) -> Result<DatabaseConnection, DbErr>;

// 2️⃣ 实体查询
#[instrument(name = "db.query", skip(db))]
async fn find_user(db: &DatabaseConnection, id: i32) -> Result<Option<user::Model>, DbErr>;

// 3️⃣ 事务操作
#[instrument(name = "db.transaction", skip(db))]
async fn transfer_with_tracing(db: &DatabaseConnection, ...) -> Result<(), DbErr>;

// 4️⃣ 连接池监控
#[instrument(name = "db.pool.stats")]
fn record_pool_stats(db: &DatabaseConnection);
```

---

## 基础集成

### 1. OTLP 初始化

```rust
use opentelemetry::{global, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    propagation::TraceContextPropagator,
    runtime::TokioCurrentThread,
    trace::{self, Sampler},
    Resource,
};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

pub async fn init_telemetry(service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 设置 TraceContext 传播器
    global::set_text_map_propagator(TraceContextPropagator::new());
    
    // 创建 OTLP Tracer
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .http()
                .with_endpoint("http://localhost:4318/v1/traces")
                .with_timeout(std::time::Duration::from_secs(5))
        )
        .with_trace_config(
            trace::Config::default()
                .with_sampler(Sampler::AlwaysOn)
                .with_resource(Resource::new(vec![
                    KeyValue::new("service.name", service_name.to_string()),
                ]))
        )
        .install_batch(TokioCurrentThread)?;
    
    // 设置全局 Tracer
    global::set_tracer_provider(tracer.provider().unwrap().clone());
    
    // 创建 Tracing Subscriber
    tracing_subscriber::registry()
        .with(EnvFilter::from_default_env())
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(())
}
```

### 2. 数据库连接 (带追踪)

```rust
use sea_orm::{ConnectOptions, Database, DatabaseConnection, DbErr};
use std::time::Duration;
use tracing::{debug, info, instrument, Span};
use opentelemetry::trace::{SpanKind, Status};

#[instrument(
    name = "db.connect",
    skip(url),
    fields(
        db.system = "postgresql",
        db.name = %db_name,
        otel.kind = "client",
        otel.status_code = tracing::field::Empty,
    )
)]
pub async fn connect_with_tracing(
    url: &str,
    db_name: &str,
    max_connections: u32,
) -> Result<DatabaseConnection, DbErr> {
    let span = Span::current();
    
    info!("Connecting to database: {}", db_name);
    
    let mut opt = ConnectOptions::new(url.to_owned());
    opt.max_connections(max_connections)
        .min_connections(5)
        .connect_timeout(Duration::from_secs(10))
        .acquire_timeout(Duration::from_secs(10))
        .idle_timeout(Duration::from_secs(300))
        .max_lifetime(Duration::from_secs(3600))
        .sqlx_logging(true)
        .sqlx_logging_level(log::LevelFilter::Debug);
    
    match Database::connect(opt).await {
        Ok(conn) => {
            span.record("otel.status_code", "OK");
            debug!("Database connection established");
            Ok(conn)
        }
        Err(e) => {
            span.record("otel.status_code", "ERROR");
            tracing::error!("Failed to connect to database: {}", e);
            Err(e)
        }
    }
}
```

---

## 实体追踪

### 1. 定义实体

```rust
use sea_orm::entity::prelude::*;
use serde::{Deserialize, Serialize};

// 用户实体
#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    
    #[sea_orm(unique)]
    pub email: String,
    
    pub name: String,
    pub created_at: ChronoDateTime,
    pub updated_at: ChronoDateTime,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(has_many = "super::post::Entity")]
    Posts,
}

impl Related<super::post::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::Posts.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}

// 文章实体
#[derive(Clone, Debug, PartialEq, DeriveEntityModel, Serialize, Deserialize)]
#[sea_orm(table_name = "posts")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    
    pub user_id: i32,
    pub title: String,
    pub content: String,
    pub published: bool,
    pub created_at: ChronoDateTime,
    pub updated_at: ChronoDateTime,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::user::Entity",
        from = "Column::UserId",
        to = "super::user::Column::Id"
    )]
    User,
}

impl Related<super::user::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::User.def()
    }
}

impl ActiveModelBehavior for ActiveModel {}
```

### 2. 追踪包装器

```rust
use opentelemetry::{global, trace::{Span, SpanKind, Tracer}, KeyValue};
use tracing::{debug, error, info, instrument};

/// 带追踪的实体操作包装器
pub struct TracedEntity<E: EntityTrait> {
    _phantom: std::marker::PhantomData<E>,
}

impl<E: EntityTrait> TracedEntity<E> {
    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
    
    /// 查找单个实体 (带追踪)
    #[instrument(
        name = "db.query.find_by_id",
        skip(db, id),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = %E::default().table_name(),
            otel.kind = "client",
        )
    )]
    pub async fn find_by_id<C>(
        &self,
        db: &C,
        id: <E::PrimaryKey as PrimaryKeyTrait>::ValueType,
    ) -> Result<Option<E::Model>, DbErr>
    where
        C: ConnectionTrait,
        <E::PrimaryKey as PrimaryKeyTrait>::ValueType: std::fmt::Display,
    {
        debug!("Finding entity by id: {}", id);
        
        let result = E::find_by_id(id).one(db).await;
        
        match &result {
            Ok(Some(_)) => info!("Entity found"),
            Ok(None) => debug!("Entity not found"),
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
    
    /// 查找所有实体 (带追踪)
    #[instrument(
        name = "db.query.find_all",
        skip(db),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = %E::default().table_name(),
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub async fn find_all<C>(
        &self,
        db: &C,
    ) -> Result<Vec<E::Model>, DbErr>
    where
        C: ConnectionTrait,
    {
        debug!("Finding all entities");
        
        let result = E::find().all(db).await;
        
        match &result {
            Ok(models) => {
                let count = models.len();
                tracing::Span::current().record("db.row_count", count);
                info!("Found {} entities", count);
            }
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
    
    /// 插入实体 (带追踪)
    #[instrument(
        name = "db.query.insert",
        skip(db, model),
        fields(
            db.system = "postgresql",
            db.operation = "INSERT",
            db.sql.table = %E::default().table_name(),
            otel.kind = "client",
        )
    )]
    pub async fn insert<C>(
        &self,
        db: &C,
        model: E::ActiveModel,
    ) -> Result<E::Model, DbErr>
    where
        C: ConnectionTrait,
    {
        debug!("Inserting entity");
        
        let result = model.insert(db).await;
        
        match &result {
            Ok(_) => info!("Entity inserted successfully"),
            Err(e) => error!("Insert failed: {}", e),
        }
        
        result
    }
    
    /// 更新实体 (带追踪)
    #[instrument(
        name = "db.query.update",
        skip(db, model),
        fields(
            db.system = "postgresql",
            db.operation = "UPDATE",
            db.sql.table = %E::default().table_name(),
            otel.kind = "client",
        )
    )]
    pub async fn update<C>(
        &self,
        db: &C,
        model: E::ActiveModel,
    ) -> Result<E::Model, DbErr>
    where
        C: ConnectionTrait,
    {
        debug!("Updating entity");
        
        let result = model.update(db).await;
        
        match &result {
            Ok(_) => info!("Entity updated successfully"),
            Err(e) => error!("Update failed: {}", e),
        }
        
        result
    }
    
    /// 删除实体 (带追踪)
    #[instrument(
        name = "db.query.delete",
        skip(db, model),
        fields(
            db.system = "postgresql",
            db.operation = "DELETE",
            db.sql.table = %E::default().table_name(),
            otel.kind = "client",
        )
    )]
    pub async fn delete<C>(
        &self,
        db: &C,
        model: E::ActiveModel,
    ) -> Result<DeleteResult, DbErr>
    where
        C: ConnectionTrait,
    {
        debug!("Deleting entity");
        
        let result = model.delete(db).await;
        
        match &result {
            Ok(res) => info!("Entity deleted, rows affected: {}", res.rows_affected),
            Err(e) => error!("Delete failed: {}", e),
        }
        
        result
    }
}
```

---

## 查询追踪

### 1. 条件查询 (带追踪)

```rust
use sea_orm::{ColumnTrait, QueryFilter, QueryOrder, QuerySelect};

impl<E: EntityTrait> TracedEntity<E> {
    /// 条件查询 (带追踪)
    #[instrument(
        name = "db.query.find_by_condition",
        skip(db),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = %E::default().table_name(),
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub async fn find_by_condition<C>(
        &self,
        db: &C,
        condition: sea_orm::Condition,
        limit: Option<u64>,
        offset: Option<u64>,
    ) -> Result<Vec<E::Model>, DbErr>
    where
        C: ConnectionTrait,
    {
        debug!("Finding entities by condition");
        
        let mut query = E::find().filter(condition);
        
        if let Some(limit) = limit {
            query = query.limit(limit);
        }
        
        if let Some(offset) = offset {
            query = query.offset(offset);
        }
        
        let result = query.all(db).await;
        
        match &result {
            Ok(models) => {
                let count = models.len();
                tracing::Span::current().record("db.row_count", count);
                info!("Found {} entities", count);
            }
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
    
    /// 分页查询 (带追踪)
    #[instrument(
        name = "db.query.paginate",
        skip(db),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = %E::default().table_name(),
            db.page = page,
            db.per_page = per_page,
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub async fn paginate<C>(
        &self,
        db: &C,
        page: u64,
        per_page: u64,
    ) -> Result<(Vec<E::Model>, u64), DbErr>
    where
        C: ConnectionTrait,
    {
        debug!("Paginating entities: page={}, per_page={}", page, per_page);
        
        let paginator = E::find().paginate(db, per_page);
        let total_pages = paginator.num_pages().await?;
        let models = paginator.fetch_page(page - 1).await?;
        
        let count = models.len();
        tracing::Span::current().record("db.row_count", count);
        info!("Found {} entities (page {}/{})", count, page, total_pages);
        
        Ok((models, total_pages))
    }
}
```

### 2. 用户查询示例

```rust
use crate::entities::{prelude::*, user};
use sea_orm::{Condition, QueryFilter};

/// 用户仓储
pub struct UserRepository {
    traced_entity: TracedEntity<User>,
}

impl UserRepository {
    pub fn new() -> Self {
        Self {
            traced_entity: TracedEntity::new(),
        }
    }
    
    /// 根据邮箱查找用户
    #[instrument(name = "repo.user.find_by_email", skip(self, db))]
    pub async fn find_by_email(
        &self,
        db: &DatabaseConnection,
        email: &str,
    ) -> Result<Option<user::Model>, DbErr> {
        let condition = Condition::all().add(user::Column::Email.eq(email));
        
        let users = self.traced_entity
            .find_by_condition(db, condition, Some(1), None)
            .await?;
        
        Ok(users.into_iter().next())
    }
    
    /// 分页获取所有用户
    #[instrument(name = "repo.user.list", skip(self, db))]
    pub async fn list(
        &self,
        db: &DatabaseConnection,
        page: u64,
        per_page: u64,
    ) -> Result<(Vec<user::Model>, u64), DbErr> {
        self.traced_entity.paginate(db, page, per_page).await
    }
}
```

---

## 事务追踪

### 1. 事务包装器

```rust
use sea_orm::{ConnectionTrait, DatabaseTransaction, TransactionTrait};

/// 带追踪的事务管理器
pub struct TracedTransaction;

impl TracedTransaction {
    /// 执行事务 (带追踪)
    #[instrument(
        name = "db.transaction",
        skip(db, operation),
        fields(
            db.system = "postgresql",
            db.operation = "TRANSACTION",
            otel.kind = "client",
            otel.status_code = tracing::field::Empty,
        )
    )]
    pub async fn execute<F, T, E>(
        db: &DatabaseConnection,
        operation: F,
    ) -> Result<T, DbErr>
    where
        F: FnOnce(&DatabaseTransaction) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send + '_>>,
        E: std::error::Error + Send + Sync + 'static,
    {
        let span = tracing::Span::current();
        
        debug!("Starting transaction");
        let txn = db.begin().await?;
        
        match operation(&txn).await {
            Ok(result) => {
                debug!("Committing transaction");
                txn.commit().await?;
                span.record("otel.status_code", "OK");
                info!("Transaction committed successfully");
                Ok(result)
            }
            Err(e) => {
                error!("Rolling back transaction: {}", e);
                txn.rollback().await?;
                span.record("otel.status_code", "ERROR");
                Err(DbErr::Custom(format!("Transaction failed: {}", e)))
            }
        }
    }
    
    /// 手动管理的事务 (带追踪)
    #[instrument(
        name = "db.transaction.begin",
        skip(db),
        fields(
            db.system = "postgresql",
            db.operation = "BEGIN",
            otel.kind = "client",
        )
    )]
    pub async fn begin(
        db: &DatabaseConnection,
    ) -> Result<DatabaseTransaction, DbErr> {
        debug!("Beginning transaction");
        db.begin().await
    }
    
    /// 提交事务 (带追踪)
    #[instrument(
        name = "db.transaction.commit",
        skip(txn),
        fields(
            db.system = "postgresql",
            db.operation = "COMMIT",
            otel.kind = "client",
        )
    )]
    pub async fn commit(txn: DatabaseTransaction) -> Result<(), DbErr> {
        debug!("Committing transaction");
        let result = txn.commit().await;
        
        match &result {
            Ok(_) => info!("Transaction committed successfully"),
            Err(e) => error!("Commit failed: {}", e),
        }
        
        result
    }
    
    /// 回滚事务 (带追踪)
    #[instrument(
        name = "db.transaction.rollback",
        skip(txn),
        fields(
            db.system = "postgresql",
            db.operation = "ROLLBACK",
            otel.kind = "client",
        )
    )]
    pub async fn rollback(txn: DatabaseTransaction) -> Result<(), DbErr> {
        debug!("Rolling back transaction");
        let result = txn.rollback().await;
        
        match &result {
            Ok(_) => info!("Transaction rolled back successfully"),
            Err(e) => error!("Rollback failed: {}", e),
        }
        
        result
    }
}
```

### 2. 事务使用示例

```rust
use crate::entities::{prelude::*, user, post};
use sea_orm::ActiveValue::Set;

/// 创建用户并发布第一篇文章 (事务)
#[instrument(name = "service.user.create_with_first_post", skip(db))]
pub async fn create_user_with_first_post(
    db: &DatabaseConnection,
    email: String,
    name: String,
    post_title: String,
    post_content: String,
) -> Result<(user::Model, post::Model), anyhow::Error> {
    TracedTransaction::execute(db, |txn| {
        Box::pin(async move {
            // 1. 创建用户
            let new_user = user::ActiveModel {
                email: Set(email.clone()),
                name: Set(name.clone()),
                created_at: Set(chrono::Utc::now().naive_utc()),
                updated_at: Set(chrono::Utc::now().naive_utc()),
                ..Default::default()
            };
            
            let user = new_user.insert(txn).await?;
            info!("User created: {}", user.id);
            
            // 2. 创建第一篇文章
            let new_post = post::ActiveModel {
                user_id: Set(user.id),
                title: Set(post_title),
                content: Set(post_content),
                published: Set(false),
                created_at: Set(chrono::Utc::now().naive_utc()),
                updated_at: Set(chrono::Utc::now().naive_utc()),
                ..Default::default()
            };
            
            let post = new_post.insert(txn).await?;
            info!("Post created: {}", post.id);
            
            Ok::<_, DbErr>((user, post))
        })
    }).await.map_err(|e| anyhow::anyhow!("Transaction failed: {}", e))
}
```

---

## 连接池监控

### 1. 连接池状态记录

```rust
use sea_orm::{DatabaseConnection, DbBackend};
use sqlx::pool::PoolOptions;

/// 连接池监控器
pub struct PoolMonitor;

impl PoolMonitor {
    /// 记录连接池状态
    #[instrument(
        name = "db.pool.stats",
        fields(
            db.system = "postgresql",
            db.pool.connections = tracing::field::Empty,
            db.pool.idle = tracing::field::Empty,
            db.pool.max = tracing::field::Empty,
            otel.kind = "internal",
        )
    )]
    pub fn record_stats(db: &DatabaseConnection) {
        let span = tracing::Span::current();
        
        // 注意: SeaORM 目前没有直接暴露 SQLx 池的统计信息
        // 这里展示概念，实际需要根据 SeaORM 版本调整
        
        // 如果可以访问底层 SQLx 池:
        // if let Some(pool) = get_underlying_pool(db) {
        //     span.record("db.pool.connections", pool.size());
        //     span.record("db.pool.idle", pool.num_idle());
        //     span.record("db.pool.max", pool.options().get_max_connections());
        // }
        
        debug!("Recording pool statistics");
    }
    
    /// 定期监控连接池 (后台任务)
    pub async fn monitor_periodically(
        db: DatabaseConnection,
        interval: std::time::Duration,
    ) {
        let mut interval_timer = tokio::time::interval(interval);
        
        loop {
            interval_timer.tick().await;
            Self::record_stats(&db);
        }
    }
}
```

### 2. 启动连接池监控

```rust
/// 启动连接池监控任务
pub fn start_pool_monitoring(db: DatabaseConnection) {
    tokio::spawn(async move {
        PoolMonitor::monitor_periodically(
            db,
            std::time::Duration::from_secs(60),  // 每60秒记录一次
        ).await;
    });
}
```

---

## 关联查询追踪

### 1. 一对多关联

```rust
use sea_orm::{Related, RelationTrait, Select};

impl UserRepository {
    /// 获取用户及其所有文章 (带追踪)
    #[instrument(
        name = "repo.user.find_with_posts",
        skip(self, db),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            user_id = user_id,
            otel.kind = "client",
        )
    )]
    pub async fn find_with_posts(
        &self,
        db: &DatabaseConnection,
        user_id: i32,
    ) -> Result<Option<(user::Model, Vec<post::Model>)>, DbErr> {
        debug!("Finding user with posts: user_id={}", user_id);
        
        // 查找用户
        let user = User::find_by_id(user_id).one(db).await?;
        
        if let Some(user) = user {
            // 查找用户的所有文章
            let posts = user.find_related(Post).all(db).await?;
            
            info!("Found user with {} posts", posts.len());
            Ok(Some((user, posts)))
        } else {
            debug!("User not found");
            Ok(None)
        }
    }
}
```

### 2. 多对一关联

```rust
pub struct PostRepository {
    traced_entity: TracedEntity<Post>,
}

impl PostRepository {
    pub fn new() -> Self {
        Self {
            traced_entity: TracedEntity::new(),
        }
    }
    
    /// 获取文章及其作者 (带追踪)
    #[instrument(
        name = "repo.post.find_with_author",
        skip(self, db),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            post_id = post_id,
            otel.kind = "client",
        )
    )]
    pub async fn find_with_author(
        &self,
        db: &DatabaseConnection,
        post_id: i32,
    ) -> Result<Option<(post::Model, user::Model)>, DbErr> {
        debug!("Finding post with author: post_id={}", post_id);
        
        // 查找文章
        let post = Post::find_by_id(post_id).one(db).await?;
        
        if let Some(post) = post {
            // 查找作者
            let author = post.find_related(User).one(db).await?
                .ok_or_else(|| DbErr::RecordNotFound("Author not found".to_string()))?;
            
            info!("Found post with author");
            Ok(Some((post, author)))
        } else {
            debug!("Post not found");
            Ok(None)
        }
    }
}
```

---

## 批量操作追踪

### 1. 批量插入

```rust
impl<E: EntityTrait> TracedEntity<E> {
    /// 批量插入 (带追踪)
    #[instrument(
        name = "db.query.batch_insert",
        skip(db, models),
        fields(
            db.system = "postgresql",
            db.operation = "INSERT",
            db.sql.table = %E::default().table_name(),
            batch_size = models.len(),
            otel.kind = "client",
        )
    )]
    pub async fn batch_insert<C>(
        &self,
        db: &C,
        models: Vec<E::ActiveModel>,
    ) -> Result<(), DbErr>
    where
        C: ConnectionTrait,
    {
        let batch_size = models.len();
        debug!("Batch inserting {} entities", batch_size);
        
        let result = E::insert_many(models).exec(db).await;
        
        match &result {
            Ok(_) => info!("Batch insert successful: {} entities", batch_size),
            Err(e) => error!("Batch insert failed: {}", e),
        }
        
        result.map(|_| ())
    }
}
```

### 2. 批量更新

```rust
use sea_orm::{sea_query::Expr, UpdateMany};

impl UserRepository {
    /// 批量更新用户状态 (带追踪)
    #[instrument(
        name = "repo.user.batch_update_status",
        skip(self, db, user_ids),
        fields(
            db.system = "postgresql",
            db.operation = "UPDATE",
            db.sql.table = "users",
            batch_size = user_ids.len(),
            otel.kind = "client",
        )
    )]
    pub async fn batch_update_status(
        &self,
        db: &DatabaseConnection,
        user_ids: Vec<i32>,
        new_status: &str,
    ) -> Result<u64, DbErr> {
        let batch_size = user_ids.len();
        debug!("Batch updating {} users", batch_size);
        
        let result = User::update_many()
            .col_expr(
                user::Column::UpdatedAt,
                Expr::value(chrono::Utc::now().naive_utc()),
            )
            .filter(user::Column::Id.is_in(user_ids))
            .exec(db)
            .await?;
        
        info!("Batch update successful: {} rows affected", result.rows_affected);
        Ok(result.rows_affected)
    }
}
```

---

## 迁移追踪

### 1. 迁移管理器

```rust
use sea_orm_migration::prelude::*;

#[derive(DeriveMigrationName)]
pub struct Migration;

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    /// 执行迁移
    #[instrument(
        name = "db.migration.up",
        fields(
            db.system = "postgresql",
            db.operation = "DDL",
            migration.name = "create_users_table",
            otel.kind = "client",
        )
    )]
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        debug!("Running migration: create_users_table");
        
        manager
            .create_table(
                Table::create()
                    .table(User::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(User::Id)
                            .integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(ColumnDef::new(User::Email).string().not_null().unique_key())
                    .col(ColumnDef::new(User::Name).string().not_null())
                    .col(ColumnDef::new(User::CreatedAt).timestamp().not_null())
                    .col(ColumnDef::new(User::UpdatedAt).timestamp().not_null())
                    .to_owned(),
            )
            .await?;
        
        info!("Migration completed: create_users_table");
        Ok(())
    }
    
    /// 回滚迁移
    #[instrument(
        name = "db.migration.down",
        fields(
            db.system = "postgresql",
            db.operation = "DDL",
            migration.name = "create_users_table",
            otel.kind = "client",
        )
    )]
    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        debug!("Rolling back migration: create_users_table");
        
        manager
            .drop_table(Table::drop().table(User::Table).to_owned())
            .await?;
        
        info!("Migration rolled back: create_users_table");
        Ok(())
    }
}

#[derive(Iden)]
enum User {
    Table,
    Id,
    Email,
    Name,
    CreatedAt,
    UpdatedAt,
}
```

---

## 错误处理

### 1. 自定义错误类型

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum RepositoryError {
    #[error("Database error: {0}")]
    DatabaseError(#[from] DbErr),
    
    #[error("Entity not found: {0}")]
    NotFound(String),
    
    #[error("Validation error: {0}")]
    ValidationError(String),
    
    #[error("Transaction failed: {0}")]
    TransactionFailed(String),
}

pub type RepositoryResult<T> = Result<T, RepositoryError>;
```

### 2. 错误记录

```rust
impl UserRepository {
    /// 查找用户 (带完整错误处理)
    #[instrument(name = "repo.user.find_by_id", skip(self, db))]
    pub async fn find_by_id_safe(
        &self,
        db: &DatabaseConnection,
        id: i32,
    ) -> RepositoryResult<user::Model> {
        self.traced_entity
            .find_by_id(db, id)
            .await?
            .ok_or_else(|| {
                error!("User not found: id={}", id);
                RepositoryError::NotFound(format!("User {} not found", id))
            })
    }
}
```

---

## 性能优化

### 1. 查询优化

```rust
use sea_orm::{QuerySelect, SelectColumns};

impl PostRepository {
    /// 只选择需要的列 (减少数据传输)
    #[instrument(name = "repo.post.list_titles", skip(self, db))]
    pub async fn list_titles(
        &self,
        db: &DatabaseConnection,
    ) -> Result<Vec<(i32, String)>, DbErr> {
        let posts = Post::find()
            .select_only()
            .column(post::Column::Id)
            .column(post::Column::Title)
            .into_tuple()
            .all(db)
            .await?;
        
        Ok(posts)
    }
}
```

### 2. 批处理优化

```rust
/// 批量操作配置
pub struct BatchConfig {
    pub batch_size: usize,
    pub max_concurrent: usize,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            batch_size: 100,
            max_concurrent: 5,
        }
    }
}

impl UserRepository {
    /// 批量创建用户 (优化版)
    #[instrument(name = "repo.user.bulk_create", skip(self, db, users))]
    pub async fn bulk_create(
        &self,
        db: &DatabaseConnection,
        users: Vec<user::ActiveModel>,
        config: BatchConfig,
    ) -> Result<(), RepositoryError> {
        let total = users.len();
        debug!("Bulk creating {} users", total);
        
        let semaphore = Arc::new(tokio::sync::Semaphore::new(config.max_concurrent));
        let mut tasks = vec![];
        
        for chunk in users.chunks(config.batch_size) {
            let permit = semaphore.clone().acquire_owned().await.unwrap();
            let chunk = chunk.to_vec();
            let db = db.clone();
            
            let task = tokio::spawn(async move {
                let _permit = permit;
                let traced_entity = TracedEntity::<User>::new();
                traced_entity.batch_insert(&db, chunk).await
            });
            
            tasks.push(task);
        }
        
        for task in tasks {
            task.await.map_err(|e| {
                RepositoryError::DatabaseError(DbErr::Custom(format!("Task failed: {}", e)))
            })??;
        }
        
        info!("Bulk create completed: {} users", total);
        Ok(())
    }
}
```

### 3. 连接池优化

```rust
/// 创建优化的数据库连接
pub async fn create_optimized_connection(
    url: &str,
    db_name: &str,
) -> Result<DatabaseConnection, DbErr> {
    let mut opt = ConnectOptions::new(url.to_owned());
    
    // 连接池配置
    opt.max_connections(100)                    // 最大连接数
        .min_connections(10)                     // 最小连接数
        .connect_timeout(Duration::from_secs(10))   // 连接超时
        .acquire_timeout(Duration::from_secs(10))   // 获取连接超时
        .idle_timeout(Duration::from_secs(600))     // 空闲超时 (10分钟)
        .max_lifetime(Duration::from_secs(3600))    // 最大生命周期 (1小时)
        .sqlx_logging(false)                        // 生产环境关闭 SQL 日志
        .sqlx_logging_level(log::LevelFilter::Debug);
    
    connect_with_tracing(url, db_name, 100).await
}
```

---

## 完整示例

### 1. 应用程序入口

```rust
use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Clone)]
pub struct AppState {
    pub db: DatabaseConnection,
    pub user_repo: Arc<UserRepository>,
    pub post_repo: Arc<PostRepository>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 Telemetry
    init_telemetry("seaorm-otlp-example").await?;
    
    // 2. 连接数据库
    let db = create_optimized_connection(
        "postgresql://user:pass@localhost/mydb",
        "mydb",
    ).await?;
    
    // 3. 启动连接池监控
    start_pool_monitoring(db.clone());
    
    // 4. 创建仓储
    let user_repo = Arc::new(UserRepository::new());
    let post_repo = Arc::new(PostRepository::new());
    
    // 5. 创建应用状态
    let state = AppState {
        db,
        user_repo,
        post_repo,
    };
    
    // 6. 创建路由
    let app = Router::new()
        .route("/users", post(create_user))
        .route("/users/:id", get(get_user))
        .route("/users/:id/posts", get(get_user_posts))
        .route("/posts/:id", get(get_post_with_author))
        .with_state(state);
    
    // 7. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;
    
    // 8. 清理
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

### 2. API 处理器

```rust
#[derive(Deserialize)]
pub struct CreateUserRequest {
    pub email: String,
    pub name: String,
}

#[derive(Serialize)]
pub struct UserResponse {
    pub id: i32,
    pub email: String,
    pub name: String,
    pub created_at: String,
}

/// 创建用户
#[instrument(name = "handler.create_user", skip(state, req))]
async fn create_user(
    State(state): State<AppState>,
    Json(req): Json<CreateUserRequest>,
) -> Result<Json<UserResponse>, StatusCode> {
    let new_user = user::ActiveModel {
        email: Set(req.email.clone()),
        name: Set(req.name.clone()),
        created_at: Set(chrono::Utc::now().naive_utc()),
        updated_at: Set(chrono::Utc::now().naive_utc()),
        ..Default::default()
    };
    
    let user = state.user_repo.traced_entity
        .insert(&state.db, new_user)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(Json(UserResponse {
        id: user.id,
        email: user.email,
        name: user.name,
        created_at: user.created_at.to_string(),
    }))
}

/// 获取用户
#[instrument(name = "handler.get_user", skip(state))]
async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<i32>,
) -> Result<Json<UserResponse>, StatusCode> {
    let user = state.user_repo
        .find_by_id_safe(&state.db, id)
        .await
        .map_err(|_| StatusCode::NOT_FOUND)?;
    
    Ok(Json(UserResponse {
        id: user.id,
        email: user.email,
        name: user.name,
        created_at: user.created_at.to_string(),
    }))
}

/// 获取用户文章
#[instrument(name = "handler.get_user_posts", skip(state))]
async fn get_user_posts(
    State(state): State<AppState>,
    Path(id): Path<i32>,
) -> Result<Json<Vec<PostResponse>>, StatusCode> {
    let (_, posts) = state.user_repo
        .find_with_posts(&state.db, id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;
    
    let response = posts
        .into_iter()
        .map(|post| PostResponse {
            id: post.id,
            title: post.title,
            content: post.content,
            published: post.published,
            created_at: post.created_at.to_string(),
        })
        .collect();
    
    Ok(Json(response))
}

#[derive(Serialize)]
pub struct PostResponse {
    pub id: i32,
    pub title: String,
    pub content: String,
    pub published: bool,
    pub created_at: String,
}

/// 获取文章及作者
#[instrument(name = "handler.get_post_with_author", skip(state))]
async fn get_post_with_author(
    State(state): State<AppState>,
    Path(id): Path<i32>,
) -> Result<Json<PostWithAuthorResponse>, StatusCode> {
    let (post, author) = state.post_repo
        .find_with_author(&state.db, id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;
    
    Ok(Json(PostWithAuthorResponse {
        post: PostResponse {
            id: post.id,
            title: post.title,
            content: post.content,
            published: post.published,
            created_at: post.created_at.to_string(),
        },
        author: UserResponse {
            id: author.id,
            email: author.email,
            name: author.name,
            created_at: author.created_at.to_string(),
        },
    }))
}

#[derive(Serialize)]
pub struct PostWithAuthorResponse {
    pub post: PostResponse,
    pub author: UserResponse,
}
```

---

## 最佳实践

### ✅ 基础实践

1. **始终使用连接池**

   ```rust
   // ✅ 好的做法
   let db = Database::connect(opt).await?;
   
   // ❌ 避免为每个操作创建新连接
   ```

2. **使用事务保证一致性**

   ```rust
   // ✅ 使用事务
   TracedTransaction::execute(db, |txn| {
       // 多个操作...
   }).await?;
   ```

3. **参数化查询 (SeaORM 默认支持)**

   ```rust
   // ✅ SeaORM 自动参数化
   User::find().filter(user::Column::Email.eq(email)).one(db).await?;
   ```

### ⚡ 性能实践

1. **批量操作**

   ```rust
   // ✅ 批量插入
   Entity::insert_many(models).exec(db).await?;
   
   // ❌ 避免循环单独插入
   ```

2. **只查询需要的列**

   ```rust
   // ✅ 选择特定列
   Post::find()
       .select_only()
       .column(post::Column::Id)
       .column(post::Column::Title)
       .all(db).await?;
   ```

3. **使用分页**

   ```rust
   // ✅ 使用分页
   let paginator = Entity::find().paginate(db, per_page);
   ```

### 🔍 可观测性实践

1. **添加上下文信息**

   ```rust
   #[instrument(
       name = "repo.user.find",
       fields(user.id = %id),
       skip(db)
   )]
   ```

2. **记录关键指标**

   ```rust
   span.record("db.row_count", models.len());
   ```

3. **错误追踪**

   ```rust
   match result {
       Err(e) => {
           error!("Operation failed: {}", e);
           Err(e)
       }
       Ok(v) => Ok(v),
   }
   ```

### 🛡️ 安全实践

1. **连接字符串脱敏**

    ```rust
    // 记录时移除密码
    let sanitized = url.replace(r"://([^:]+):([^@]+)@", "://$1:***@");
    ```

2. **限制并发连接**

    ```rust
    let semaphore = Semaphore::new(max_concurrent);
    ```

---

## 参考资源

### 📚 官方文档

- [SeaORM Documentation](https://www.sea-ql.org/SeaORM/docs/index)
- [SeaORM Tutorial](https://www.sea-ql.org/SeaORM/docs/tutorials)
- [OpenTelemetry Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/)

### 🔧 相关库

- [sea-orm](https://crates.io/crates/sea-orm) - 异步 ORM 框架
- [sqlx](https://crates.io/crates/sqlx) - 异步 SQL 驱动
- [opentelemetry](https://crates.io/crates/opentelemetry) - OpenTelemetry API
- [tracing](https://crates.io/crates/tracing) - 结构化日志和追踪

### 📖 扩展阅读

- [SeaORM GitHub](https://github.com/SeaQL/sea-orm)
- [SeaQL Blog](https://www.sea-ql.org/blog/)
- [Rust Async Book](https://rust-lang.github.io/async-book/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025年10月8日  
**作者**: AI Assistant  
**许可证**: MIT OR Apache-2.0

[🏠 返回目录](../README.md) | [⬅️ SQLx 追踪](01_SQLx_数据库追踪_Rust完整版.md) | [➡️ Diesel 追踪](03_Diesel_数据库追踪_Rust完整版.md)

# Diesel 数据库追踪 - Rust OTLP 完整实现

> **版本**: Rust 1.90 + Diesel 2.2.9 + OpenTelemetry 0.31.0  
> **日期**: 2025年10月8日  
> **状态**: ✅ 生产就绪

---

## 📋 目录

- [Diesel 数据库追踪 - Rust OTLP 完整实现](#diesel-数据库追踪---rust-otlp-完整实现)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心特性](#核心特性)
    - [数据库语义约定](#数据库语义约定)
  - [依赖配置](#依赖配置)
    - [Cargo.toml](#cargotoml)
  - [核心概念](#核心概念)
    - [1. Diesel 架构](#1-diesel-架构)
    - [2. 追踪集成点](#2-追踪集成点)
  - [基础集成](#基础集成)
    - [1. OTLP 初始化 (同步环境)](#1-otlp-初始化-同步环境)
    - [2. Schema 定义](#2-schema-定义)
    - [3. 模型定义](#3-模型定义)
  - [连接池追踪](#连接池追踪)
    - [1. 创建连接池 (同步)](#1-创建连接池-同步)
    - [2. 获取连接 (带追踪)](#2-获取连接-带追踪)
  - [查询追踪](#查询追踪)
    - [1. 查询包装器](#1-查询包装器)
    - [2. 用户仓储 (同步)](#2-用户仓储-同步)
  - [事务追踪](#事务追踪)
    - [1. 事务包装器](#1-事务包装器)
    - [2. 事务使用示例](#2-事务使用示例)
  - [CRUD 操作追踪](#crud-操作追踪)
    - [1. INSERT 操作](#1-insert-操作)
    - [2. UPDATE 操作](#2-update-操作)
    - [3. DELETE 操作](#3-delete-操作)
  - [异步支持 (diesel-async)](#异步支持-diesel-async)
    - [1. 异步连接池](#1-异步连接池)
    - [2. 异步查询](#2-异步查询)
    - [3. 异步事务](#3-异步事务)
  - [连接池监控](#连接池监控)
    - [1. 连接池状态监控](#1-连接池状态监控)
  - [批量操作追踪](#批量操作追踪)
    - [1. 批量插入](#1-批量插入)
    - [2. 批量更新](#2-批量更新)
  - [自定义查询追踪](#自定义查询追踪)
    - [1. 原生 SQL 查询](#1-原生-sql-查询)
  - [错误处理](#错误处理)
    - [1. 自定义错误类型](#1-自定义错误类型)
    - [2. 错误记录](#2-错误记录)
  - [性能优化](#性能优化)
    - [1. 查询优化](#1-查询优化)
    - [2. 连接优化](#2-连接优化)
    - [3. 预编译查询 (宏)](#3-预编译查询-宏)
  - [完整示例](#完整示例)
    - [1. 应用程序入口](#1-应用程序入口)
    - [2. API 处理器](#2-api-处理器)
  - [最佳实践](#最佳实践)
    - [✅ 基础实践](#-基础实践)
    - [⚡ 性能实践](#-性能实践)
    - [🔍 可观测性实践](#-可观测性实践)
    - [🛡️ 安全实践](#️-安全实践)
  - [参考资源](#参考资源)
    - [📚 官方文档](#-官方文档)
    - [🔧 相关库](#-相关库)
    - [📖 扩展阅读](#-扩展阅读)

---

## 概述

**Diesel** 是 Rust 中最成熟的 ORM 框架之一，提供类型安全的查询构建器和编译时 SQL 验证。
本文档展示如何为 Diesel 添加完整的 OpenTelemetry 追踪支持。

### 核心特性

- ✅ **类型安全**: 编译时 SQL 验证
- ✅ **高性能**: 零成本抽象
- ✅ **同步优先**: 传统同步设计 (有异步版本)
- ✅ **多数据库**: PostgreSQL, MySQL, SQLite
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
# Diesel (同步版本)
diesel = { version = "2.2.9", features = [
    "postgres",         # PostgreSQL 支持
    "mysql",            # MySQL 支持 (可选)
    "sqlite",           # SQLite 支持 (可选)
    "r2d2",             # 连接池
    "chrono",           # 日期时间支持
    "uuid",             # UUID 支持
] }

# Diesel 异步版本 (可选)
diesel-async = { version = "0.5.4", features = [
    "postgres",
    "deadpool",         # 异步连接池
] }

# 连接池
r2d2 = "0.8.10"          # 同步连接池
deadpool = "0.12.2"      # 异步连接池 (用于 diesel-async)

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

### 1. Diesel 架构

```text
┌────────────────────────────────────────────┐
│        Application Layer                   │
│  (查询构建器、模型、连接管理)                   │
└─────────────────┬──────────────────────────┘
                  │
                  ▼
┌────────────────────────────────────────────┐
│         Diesel Connection Pool (R2D2)      │
│  (PgConnection, MysqlConnection, ...)      │
└─────────────────┬──────────────────────────┘
                  │
                  ▼
┌────────────────────────────────────────────┐
│      Database Backend (libpq, MySQL, ...)  │
└─────────────────┬──────────────────────────┘
                  │
                  ▼
┌────────────────────────────────────────────┐
│           Database Server                  │
└────────────────────────────────────────────┘
```

### 2. 追踪集成点

```rust
use diesel::prelude::*;
use diesel::r2d2::{ConnectionManager, Pool};
use tracing::instrument;

// 1️⃣ 连接池创建
#[instrument(name = "db.connect")]
fn create_pool_with_tracing(url: &str) -> Result<Pool<ConnectionManager<PgConnection>>, r2d2::Error>;

// 2️⃣ 查询执行
#[instrument(name = "db.query", skip(conn))]
fn find_user_traced(conn: &mut PgConnection, id: i32) -> QueryResult<User>;

// 3️⃣ 事务操作
#[instrument(name = "db.transaction", skip(conn))]
fn transfer_with_tracing(conn: &mut PgConnection, ...) -> QueryResult<()>;

// 4️⃣ 连接池监控
#[instrument(name = "db.pool.stats")]
fn record_pool_stats(pool: &Pool<ConnectionManager<PgConnection>>);
```

---

## 基础集成

### 1. OTLP 初始化 (同步环境)

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

### 2. Schema 定义

```rust
// schema.rs (由 Diesel CLI 生成)
diesel::table! {
    users (id) {
        id -> Int4,
        email -> Varchar,
        name -> Varchar,
        created_at -> Timestamp,
        updated_at -> Timestamp,
    }
}

diesel::table! {
    posts (id) {
        id -> Int4,
        user_id -> Int4,
        title -> Varchar,
        content -> Text,
        published -> Bool,
        created_at -> Timestamp,
        updated_at -> Timestamp,
    }
}

diesel::joinable!(posts -> users (user_id));
diesel::allow_tables_to_appear_in_same_query!(users, posts);
```

### 3. 模型定义

```rust
use chrono::NaiveDateTime;
use diesel::prelude::*;
use serde::{Deserialize, Serialize};

// 用户模型 (Queryable)
#[derive(Debug, Clone, Queryable, Selectable, Serialize, Deserialize)]
#[diesel(table_name = crate::schema::users)]
pub struct User {
    pub id: i32,
    pub email: String,
    pub name: String,
    pub created_at: NaiveDateTime,
    pub updated_at: NaiveDateTime,
}

// 新用户 (Insertable)
#[derive(Debug, Insertable)]
#[diesel(table_name = crate::schema::users)]
pub struct NewUser {
    pub email: String,
    pub name: String,
    pub created_at: NaiveDateTime,
    pub updated_at: NaiveDateTime,
}

// 文章模型 (Queryable)
#[derive(Debug, Clone, Queryable, Selectable, Serialize, Deserialize, Associations)]
#[diesel(belongs_to(User))]
#[diesel(table_name = crate::schema::posts)]
pub struct Post {
    pub id: i32,
    pub user_id: i32,
    pub title: String,
    pub content: String,
    pub published: bool,
    pub created_at: NaiveDateTime,
    pub updated_at: NaiveDateTime,
}

// 新文章 (Insertable)
#[derive(Debug, Insertable)]
#[diesel(table_name = crate::schema::posts)]
pub struct NewPost {
    pub user_id: i32,
    pub title: String,
    pub content: String,
    pub published: bool,
    pub created_at: NaiveDateTime,
    pub updated_at: NaiveDateTime,
}
```

---

## 连接池追踪

### 1. 创建连接池 (同步)

```rust
use diesel::pg::PgConnection;
use diesel::r2d2::{ConnectionManager, Pool, PooledConnection};
use std::time::Duration;
use tracing::{debug, error, info, instrument, Span};

pub type DbPool = Pool<ConnectionManager<PgConnection>>;
pub type DbConnection = PooledConnection<ConnectionManager<PgConnection>>;

#[instrument(
    name = "db.pool.create",
    skip(database_url),
    fields(
        db.system = "postgresql",
        db.name = %db_name,
        pool.max_size = max_size,
        otel.kind = "client",
        otel.status_code = tracing::field::Empty,
    )
)]
pub fn create_pool_with_tracing(
    database_url: &str,
    db_name: &str,
    max_size: u32,
) -> Result<DbPool, r2d2::Error> {
    let span = Span::current();
    
    info!("Creating database connection pool: {}", db_name);
    
    let manager = ConnectionManager::<PgConnection>::new(database_url);
    
    let pool = Pool::builder()
        .max_size(max_size)
        .min_idle(Some(5))
        .connection_timeout(Duration::from_secs(10))
        .idle_timeout(Some(Duration::from_secs(300)))
        .max_lifetime(Some(Duration::from_secs(3600)))
        .build(manager);
    
    match pool {
        Ok(p) => {
            span.record("otel.status_code", "OK");
            debug!("Pool created successfully");
            Ok(p)
        }
        Err(e) => {
            span.record("otel.status_code", "ERROR");
            error!("Failed to create pool: {}", e);
            Err(e)
        }
    }
}
```

### 2. 获取连接 (带追踪)

```rust
#[instrument(
    name = "db.pool.get_connection",
    skip(pool),
    fields(
        db.system = "postgresql",
        otel.kind = "client",
        otel.status_code = tracing::field::Empty,
    )
)]
pub fn get_connection_traced(pool: &DbPool) -> Result<DbConnection, r2d2::Error> {
    let span = Span::current();
    
    debug!("Acquiring connection from pool");
    
    match pool.get() {
        Ok(conn) => {
            span.record("otel.status_code", "OK");
            debug!("Connection acquired");
            Ok(conn)
        }
        Err(e) => {
            span.record("otel.status_code", "ERROR");
            error!("Failed to acquire connection: {}", e);
            Err(e)
        }
    }
}
```

---

## 查询追踪

### 1. 查询包装器

```rust
use diesel::query_dsl::methods::*;
use diesel::QueryResult;
use tracing::{debug, error, info, instrument};

/// 带追踪的查询执行器
pub struct TracedQueryExecutor;

impl TracedQueryExecutor {
    /// 执行查询 (单个结果)
    #[instrument(
        name = "db.query.get",
        skip(conn),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = table_name,
            otel.kind = "client",
        )
    )]
    pub fn get_one<T, Q>(
        conn: &mut PgConnection,
        query: Q,
        table_name: &str,
    ) -> QueryResult<T>
    where
        Q: diesel::query_dsl::LoadQuery<'static, PgConnection, T>,
    {
        debug!("Executing query: get_one from {}", table_name);
        
        let result = query.get_result(conn);
        
        match &result {
            Ok(_) => info!("Query successful: found 1 record"),
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
    
    /// 执行查询 (多个结果)
    #[instrument(
        name = "db.query.get_all",
        skip(conn),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = table_name,
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub fn get_all<T, Q>(
        conn: &mut PgConnection,
        query: Q,
        table_name: &str,
    ) -> QueryResult<Vec<T>>
    where
        Q: diesel::query_dsl::LoadQuery<'static, PgConnection, T>,
    {
        debug!("Executing query: get_all from {}", table_name);
        
        let result = query.load(conn);
        
        match &result {
            Ok(records) => {
                let count = records.len();
                tracing::Span::current().record("db.row_count", count);
                info!("Query successful: found {} records", count);
            }
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
    
    /// 执行查询 (可选结果)
    #[instrument(
        name = "db.query.get_optional",
        skip(conn),
        fields(
            db.system = "postgresql",
            db.operation = "SELECT",
            db.sql.table = table_name,
            otel.kind = "client",
        )
    )]
    pub fn get_optional<T, Q>(
        conn: &mut PgConnection,
        query: Q,
        table_name: &str,
    ) -> QueryResult<Option<T>>
    where
        Q: diesel::query_dsl::LoadQuery<'static, PgConnection, T>,
    {
        debug!("Executing query: get_optional from {}", table_name);
        
        let result = query.get_result(conn).optional();
        
        match &result {
            Ok(Some(_)) => info!("Query successful: found 1 record"),
            Ok(None) => debug!("Query successful: no records found"),
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
}
```

### 2. 用户仓储 (同步)

```rust
use crate::models::{NewUser, User};
use crate::schema::users;
use diesel::prelude::*;

pub struct UserRepository;

impl UserRepository {
    /// 根据 ID 查找用户
    #[instrument(name = "repo.user.find_by_id", skip(conn), fields(user.id = id))]
    pub fn find_by_id(conn: &mut PgConnection, id: i32) -> QueryResult<Option<User>> {
        debug!("Finding user by id: {}", id);
        
        let query = users::table.filter(users::id.eq(id));
        
        TracedQueryExecutor::get_optional(conn, query, "users")
    }
    
    /// 根据邮箱查找用户
    #[instrument(name = "repo.user.find_by_email", skip(conn), fields(user.email = %email))]
    pub fn find_by_email(conn: &mut PgConnection, email: &str) -> QueryResult<Option<User>> {
        debug!("Finding user by email: {}", email);
        
        let query = users::table.filter(users::email.eq(email));
        
        TracedQueryExecutor::get_optional(conn, query, "users")
    }
    
    /// 列出所有用户 (分页)
    #[instrument(
        name = "repo.user.list",
        skip(conn),
        fields(page = page, per_page = per_page)
    )]
    pub fn list(
        conn: &mut PgConnection,
        page: i64,
        per_page: i64,
    ) -> QueryResult<Vec<User>> {
        debug!("Listing users: page={}, per_page={}", page, per_page);
        
        let offset = (page - 1) * per_page;
        let query = users::table
            .order(users::id.asc())
            .limit(per_page)
            .offset(offset);
        
        TracedQueryExecutor::get_all(conn, query, "users")
    }
    
    /// 创建用户
    #[instrument(name = "repo.user.create", skip(conn, new_user))]
    pub fn create(conn: &mut PgConnection, new_user: NewUser) -> QueryResult<User> {
        debug!("Creating user: email={}", new_user.email);
        
        diesel::insert_into(users::table)
            .values(&new_user)
            .get_result(conn)
    }
    
    /// 更新用户
    #[instrument(name = "repo.user.update", skip(conn, user_id))]
    pub fn update(
        conn: &mut PgConnection,
        user_id: i32,
        new_name: &str,
    ) -> QueryResult<User> {
        debug!("Updating user: id={}, new_name={}", user_id, new_name);
        
        diesel::update(users::table.filter(users::id.eq(user_id)))
            .set((
                users::name.eq(new_name),
                users::updated_at.eq(chrono::Utc::now().naive_utc()),
            ))
            .get_result(conn)
    }
    
    /// 删除用户
    #[instrument(name = "repo.user.delete", skip(conn), fields(user.id = user_id))]
    pub fn delete(conn: &mut PgConnection, user_id: i32) -> QueryResult<usize> {
        debug!("Deleting user: id={}", user_id);
        
        let result = diesel::delete(users::table.filter(users::id.eq(user_id)))
            .execute(conn);
        
        match &result {
            Ok(count) => info!("User deleted: {} rows affected", count),
            Err(e) => error!("Delete failed: {}", e),
        }
        
        result
    }
}
```

---

## 事务追踪

### 1. 事务包装器

```rust
use diesel::Connection;

/// 带追踪的事务管理器
pub struct TracedTransaction;

impl TracedTransaction {
    /// 执行事务
    #[instrument(
        name = "db.transaction",
        skip(conn, operation),
        fields(
            db.system = "postgresql",
            db.operation = "TRANSACTION",
            otel.kind = "client",
            otel.status_code = tracing::field::Empty,
        )
    )]
    pub fn execute<F, T>(
        conn: &mut PgConnection,
        operation: F,
    ) -> QueryResult<T>
    where
        F: FnOnce(&mut PgConnection) -> QueryResult<T>,
    {
        let span = tracing::Span::current();
        
        debug!("Starting transaction");
        
        let result = conn.transaction(|txn_conn| {
            operation(txn_conn)
        });
        
        match &result {
            Ok(_) => {
                span.record("otel.status_code", "OK");
                info!("Transaction committed successfully");
            }
            Err(e) => {
                span.record("otel.status_code", "ERROR");
                error!("Transaction failed: {}", e);
            }
        }
        
        result
    }
}
```

### 2. 事务使用示例

```rust
use crate::models::{NewPost, NewUser, Post, User};
use crate::schema::{posts, users};

/// 创建用户并发布第一篇文章 (事务)
#[instrument(name = "service.user.create_with_first_post", skip(conn))]
pub fn create_user_with_first_post(
    conn: &mut PgConnection,
    email: String,
    name: String,
    post_title: String,
    post_content: String,
) -> QueryResult<(User, Post)> {
    TracedTransaction::execute(conn, |txn_conn| {
        // 1. 创建用户
        let new_user = NewUser {
            email: email.clone(),
            name: name.clone(),
            created_at: chrono::Utc::now().naive_utc(),
            updated_at: chrono::Utc::now().naive_utc(),
        };
        
        let user: User = diesel::insert_into(users::table)
            .values(&new_user)
            .get_result(txn_conn)?;
        
        info!("User created: id={}", user.id);
        
        // 2. 创建第一篇文章
        let new_post = NewPost {
            user_id: user.id,
            title: post_title,
            content: post_content,
            published: false,
            created_at: chrono::Utc::now().naive_utc(),
            updated_at: chrono::Utc::now().naive_utc(),
        };
        
        let post: Post = diesel::insert_into(posts::table)
            .values(&new_post)
            .get_result(txn_conn)?;
        
        info!("Post created: id={}", post.id);
        
        Ok((user, post))
    })
}
```

---

## CRUD 操作追踪

### 1. INSERT 操作

```rust
impl TracedQueryExecutor {
    /// 插入单条记录
    #[instrument(
        name = "db.query.insert",
        skip(conn, values),
        fields(
            db.system = "postgresql",
            db.operation = "INSERT",
            db.sql.table = table_name,
            otel.kind = "client",
        )
    )]
    pub fn insert_one<T, U>(
        conn: &mut PgConnection,
        target: T,
        values: U,
        table_name: &str,
    ) -> QueryResult<U::Model>
    where
        T: diesel::query_builder::InsertStatement<diesel::pg::Pg, U>,
        U: diesel::insertable::Insertable<T> + diesel::query_builder::IntoInsertStatement<diesel::pg::Pg>,
    {
        debug!("Inserting record into {}", table_name);
        
        let result = diesel::insert_into(target)
            .values(values)
            .get_result(conn);
        
        match &result {
            Ok(_) => info!("Insert successful"),
            Err(e) => error!("Insert failed: {}", e),
        }
        
        result
    }
}
```

### 2. UPDATE 操作

```rust
impl TracedQueryExecutor {
    /// 更新记录
    #[instrument(
        name = "db.query.update",
        skip(conn),
        fields(
            db.system = "postgresql",
            db.operation = "UPDATE",
            db.sql.table = table_name,
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub fn update<T>(
        conn: &mut PgConnection,
        target: diesel::query_builder::UpdateStatement<diesel::pg::Pg, T, ...>,
        table_name: &str,
    ) -> QueryResult<usize>
    where
        // 具体类型参数根据实际使用调整
    {
        debug!("Updating records in {}", table_name);
        
        let result = target.execute(conn);
        
        match &result {
            Ok(count) => {
                tracing::Span::current().record("db.row_count", *count);
                info!("Update successful: {} rows affected", count);
            }
            Err(e) => error!("Update failed: {}", e),
        }
        
        result
    }
}
```

### 3. DELETE 操作

```rust
impl TracedQueryExecutor {
    /// 删除记录
    #[instrument(
        name = "db.query.delete",
        skip(conn),
        fields(
            db.system = "postgresql",
            db.operation = "DELETE",
            db.sql.table = table_name,
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub fn delete<T>(
        conn: &mut PgConnection,
        target: T,
        table_name: &str,
    ) -> QueryResult<usize>
    where
        T: diesel::query_dsl::methods::ExecuteDsl<PgConnection>,
    {
        debug!("Deleting records from {}", table_name);
        
        let result = target.execute(conn);
        
        match &result {
            Ok(count) => {
                tracing::Span::current().record("db.row_count", *count);
                info!("Delete successful: {} rows affected", count);
            }
            Err(e) => error!("Delete failed: {}", e),
        }
        
        result
    }
}
```

---

## 异步支持 (diesel-async)

### 1. 异步连接池

```rust
use diesel_async::{AsyncPgConnection, pooled_connection::AsyncDieselConnectionManager};
use deadpool::managed::Pool;

pub type AsyncDbPool = Pool<AsyncDieselConnectionManager<AsyncPgConnection>>;

#[instrument(
    name = "db.async.pool.create",
    skip(database_url),
    fields(
        db.system = "postgresql",
        db.name = %db_name,
        pool.max_size = max_size,
        otel.kind = "client",
    )
)]
pub async fn create_async_pool(
    database_url: &str,
    db_name: &str,
    max_size: usize,
) -> Result<AsyncDbPool, Box<dyn std::error::Error>> {
    info!("Creating async database connection pool: {}", db_name);
    
    let config = AsyncDieselConnectionManager::<AsyncPgConnection>::new(database_url);
    let pool = Pool::builder(config)
        .max_size(max_size)
        .build()?;
    
    debug!("Async pool created successfully");
    Ok(pool)
}
```

### 2. 异步查询

```rust
use diesel_async::RunQueryDsl;

/// 异步用户仓储
pub struct AsyncUserRepository;

impl AsyncUserRepository {
    /// 异步查找用户
    #[instrument(name = "repo.user.async.find_by_id", skip(conn), fields(user.id = id))]
    pub async fn find_by_id(
        conn: &mut AsyncPgConnection,
        id: i32,
    ) -> QueryResult<Option<User>> {
        debug!("Async finding user by id: {}", id);
        
        let result = users::table
            .filter(users::id.eq(id))
            .first(conn)
            .await
            .optional();
        
        match &result {
            Ok(Some(_)) => info!("User found"),
            Ok(None) => debug!("User not found"),
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
    
    /// 异步创建用户
    #[instrument(name = "repo.user.async.create", skip(conn, new_user))]
    pub async fn create(
        conn: &mut AsyncPgConnection,
        new_user: NewUser,
    ) -> QueryResult<User> {
        debug!("Async creating user: email={}", new_user.email);
        
        let result = diesel::insert_into(users::table)
            .values(&new_user)
            .get_result(conn)
            .await;
        
        match &result {
            Ok(user) => info!("User created: id={}", user.id),
            Err(e) => error!("Create failed: {}", e),
        }
        
        result
    }
    
    /// 异步列出用户
    #[instrument(name = "repo.user.async.list", skip(conn))]
    pub async fn list(
        conn: &mut AsyncPgConnection,
        page: i64,
        per_page: i64,
    ) -> QueryResult<Vec<User>> {
        debug!("Async listing users: page={}, per_page={}", page, per_page);
        
        let offset = (page - 1) * per_page;
        let result = users::table
            .order(users::id.asc())
            .limit(per_page)
            .offset(offset)
            .load(conn)
            .await;
        
        match &result {
            Ok(users) => info!("Found {} users", users.len()),
            Err(e) => error!("Query failed: {}", e),
        }
        
        result
    }
}
```

### 3. 异步事务

```rust
use diesel_async::AsyncConnection;

/// 异步事务包装器
pub struct AsyncTracedTransaction;

impl AsyncTracedTransaction {
    /// 执行异步事务
    #[instrument(
        name = "db.async.transaction",
        skip(conn, operation),
        fields(
            db.system = "postgresql",
            db.operation = "TRANSACTION",
            otel.kind = "client",
            otel.status_code = tracing::field::Empty,
        )
    )]
    pub async fn execute<F, T, E>(
        conn: &mut AsyncPgConnection,
        operation: F,
    ) -> Result<T, E>
    where
        F: FnOnce(&mut AsyncPgConnection) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send + '_>>,
        E: From<diesel::result::Error>,
    {
        let span = tracing::Span::current();
        
        debug!("Starting async transaction");
        
        let result = conn.transaction(operation).await;
        
        match &result {
            Ok(_) => {
                span.record("otel.status_code", "OK");
                info!("Async transaction committed successfully");
            }
            Err(_) => {
                span.record("otel.status_code", "ERROR");
                error!("Async transaction failed");
            }
        }
        
        result
    }
}
```

---

## 连接池监控

### 1. 连接池状态监控

```rust
use diesel::r2d2::Pool;

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
    pub fn record_stats(pool: &DbPool) {
        let span = tracing::Span::current();
        let state = pool.state();
        
        span.record("db.pool.connections", state.connections);
        span.record("db.pool.idle", state.idle_connections);
        span.record("db.pool.max", pool.max_size());
        
        debug!(
            "Pool stats: connections={}, idle={}, max={}",
            state.connections,
            state.idle_connections,
            pool.max_size()
        );
    }
    
    /// 定期监控连接池 (后台任务)
    pub async fn monitor_periodically(
        pool: DbPool,
        interval: std::time::Duration,
    ) {
        let mut interval_timer = tokio::time::interval(interval);
        
        loop {
            interval_timer.tick().await;
            Self::record_stats(&pool);
        }
    }
}

/// 启动连接池监控
pub fn start_pool_monitoring(pool: DbPool) {
    tokio::spawn(async move {
        PoolMonitor::monitor_periodically(
            pool,
            std::time::Duration::from_secs(60),  // 每60秒记录一次
        ).await;
    });
}
```

---

## 批量操作追踪

### 1. 批量插入

```rust
impl UserRepository {
    /// 批量创建用户
    #[instrument(
        name = "repo.user.batch_create",
        skip(conn, users),
        fields(
            db.system = "postgresql",
            db.operation = "INSERT",
            db.sql.table = "users",
            batch_size = users.len(),
            otel.kind = "client",
        )
    )]
    pub fn batch_create(
        conn: &mut PgConnection,
        users: Vec<NewUser>,
    ) -> QueryResult<Vec<User>> {
        let batch_size = users.len();
        debug!("Batch creating {} users", batch_size);
        
        let result = diesel::insert_into(users::table)
            .values(&users)
            .get_results(conn);
        
        match &result {
            Ok(created) => info!("Batch insert successful: {} users created", created.len()),
            Err(e) => error!("Batch insert failed: {}", e),
        }
        
        result
    }
}
```

### 2. 批量更新

```rust
impl UserRepository {
    /// 批量更新用户状态
    #[instrument(
        name = "repo.user.batch_update",
        skip(conn, user_ids),
        fields(
            db.system = "postgresql",
            db.operation = "UPDATE",
            db.sql.table = "users",
            batch_size = user_ids.len(),
            db.row_count = tracing::field::Empty,
            otel.kind = "client",
        )
    )]
    pub fn batch_update(
        conn: &mut PgConnection,
        user_ids: Vec<i32>,
        new_name: &str,
    ) -> QueryResult<usize> {
        let batch_size = user_ids.len();
        debug!("Batch updating {} users", batch_size);
        
        let result = diesel::update(users::table)
            .filter(users::id.eq_any(user_ids))
            .set((
                users::name.eq(new_name),
                users::updated_at.eq(chrono::Utc::now().naive_utc()),
            ))
            .execute(conn);
        
        match &result {
            Ok(count) => {
                tracing::Span::current().record("db.row_count", *count);
                info!("Batch update successful: {} rows affected", count);
            }
            Err(e) => error!("Batch update failed: {}", e),
        }
        
        result
    }
}
```

---

## 自定义查询追踪

### 1. 原生 SQL 查询

```rust
use diesel::sql_query;
use diesel::sql_types::{Integer, Text};

#[derive(QueryableByName, Debug)]
struct UserStats {
    #[diesel(sql_type = Integer)]
    user_id: i32,
    
    #[diesel(sql_type = Text)]
    user_name: String,
    
    #[diesel(sql_type = Integer)]
    post_count: i32,
}

/// 执行原生 SQL (带追踪)
#[instrument(
    name = "db.query.raw_sql",
    skip(conn),
    fields(
        db.system = "postgresql",
        db.operation = "SELECT",
        db.statement = %sql,
        otel.kind = "client",
    )
)]
pub fn execute_raw_sql(
    conn: &mut PgConnection,
    sql: &str,
) -> QueryResult<Vec<UserStats>> {
    debug!("Executing raw SQL: {}", sql);
    
    let result = sql_query(sql).load(conn);
    
    match &result {
        Ok(stats) => info!("Raw SQL successful: {} results", stats.len()),
        Err(e) => error!("Raw SQL failed: {}", e),
    }
    
    result
}

/// 用户统计查询示例
#[instrument(name = "repo.user.stats", skip(conn))]
pub fn get_user_stats(conn: &mut PgConnection) -> QueryResult<Vec<UserStats>> {
    let sql = r#"
        SELECT 
            u.id as user_id,
            u.name as user_name,
            COUNT(p.id)::INTEGER as post_count
        FROM users u
        LEFT JOIN posts p ON p.user_id = u.id
        GROUP BY u.id, u.name
        ORDER BY post_count DESC
    "#;
    
    execute_raw_sql(conn, sql)
}
```

---

## 错误处理

### 1. 自定义错误类型

```rust
use diesel::result::{DatabaseErrorKind, Error as DieselError};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum RepositoryError {
    #[error("Database error: {0}")]
    DatabaseError(#[from] DieselError),
    
    #[error("Connection pool error: {0}")]
    PoolError(#[from] r2d2::Error),
    
    #[error("Entity not found: {0}")]
    NotFound(String),
    
    #[error("Unique constraint violation: {0}")]
    UniqueViolation(String),
    
    #[error("Foreign key constraint violation: {0}")]
    ForeignKeyViolation(String),
    
    #[error("Validation error: {0}")]
    ValidationError(String),
}

pub type RepositoryResult<T> = Result<T, RepositoryError>;

/// 错误转换
impl From<DieselError> for RepositoryError {
    fn from(err: DieselError) -> Self {
        match err {
            DieselError::NotFound => RepositoryError::NotFound("Record not found".to_string()),
            DieselError::DatabaseError(kind, info) => match kind {
                DatabaseErrorKind::UniqueViolation => {
                    RepositoryError::UniqueViolation(info.message().to_string())
                }
                DatabaseErrorKind::ForeignKeyViolation => {
                    RepositoryError::ForeignKeyViolation(info.message().to_string())
                }
                _ => RepositoryError::DatabaseError(DieselError::DatabaseError(kind, info)),
            },
            _ => RepositoryError::DatabaseError(err),
        }
    }
}
```

### 2. 错误记录

```rust
impl UserRepository {
    /// 查找用户 (带完整错误处理)
    #[instrument(name = "repo.user.find_by_id_safe", skip(conn), fields(user.id = id))]
    pub fn find_by_id_safe(
        conn: &mut PgConnection,
        id: i32,
    ) -> RepositoryResult<User> {
        Self::find_by_id(conn, id)?
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
use diesel::dsl::count_star;

impl UserRepository {
    /// 计数查询 (不加载数据)
    #[instrument(name = "repo.user.count", skip(conn))]
    pub fn count(conn: &mut PgConnection) -> QueryResult<i64> {
        users::table
            .select(count_star())
            .first(conn)
    }
    
    /// 只选择需要的列
    #[instrument(name = "repo.user.list_emails", skip(conn))]
    pub fn list_emails(conn: &mut PgConnection) -> QueryResult<Vec<String>> {
        users::table
            .select(users::email)
            .load(conn)
    }
}
```

### 2. 连接优化

```rust
/// 创建优化的连接池
pub fn create_optimized_pool(
    database_url: &str,
    db_name: &str,
) -> Result<DbPool, r2d2::Error> {
    create_pool_with_tracing(
        database_url,
        db_name,
        100,  // 最大连接数
    )
}
```

### 3. 预编译查询 (宏)

```rust
// Diesel 的查询会在编译时验证
// 使用 diesel_cli 生成 schema.rs 确保类型安全
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
use std::sync::Arc;

#[derive(Clone)]
pub struct AppState {
    pub pool: DbPool,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 初始化 Telemetry
    init_telemetry("diesel-otlp-example").await?;
    
    // 2. 创建连接池
    let database_url = std::env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgresql://user:pass@localhost/mydb".to_string());
    
    let pool = create_optimized_pool(&database_url, "mydb")?;
    
    // 3. 启动连接池监控
    start_pool_monitoring(pool.clone());
    
    // 4. 创建应用状态
    let state = AppState { pool };
    
    // 5. 创建路由
    let app = Router::new()
        .route("/users", post(create_user))
        .route("/users/:id", get(get_user))
        .route("/users", get(list_users))
        .with_state(state);
    
    // 6. 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("Server listening on {}", listener.local_addr()?);
    
    axum::serve(listener, app).await?;
    
    // 7. 清理
    global::shutdown_tracer_provider();
    
    Ok(())
}
```

### 2. API 处理器

```rust
use serde::{Deserialize, Serialize};

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
}

/// 创建用户
#[instrument(name = "handler.create_user", skip(state, req))]
async fn create_user(
    State(state): State<AppState>,
    Json(req): Json<CreateUserRequest>,
) -> Result<Json<UserResponse>, StatusCode> {
    let mut conn = get_connection_traced(&state.pool)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    let new_user = NewUser {
        email: req.email.clone(),
        name: req.name.clone(),
        created_at: chrono::Utc::now().naive_utc(),
        updated_at: chrono::Utc::now().naive_utc(),
    };
    
    let user = UserRepository::create(&mut conn, new_user)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(Json(UserResponse {
        id: user.id,
        email: user.email,
        name: user.name,
    }))
}

/// 获取用户
#[instrument(name = "handler.get_user", skip(state))]
async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<i32>,
) -> Result<Json<UserResponse>, StatusCode> {
    let mut conn = get_connection_traced(&state.pool)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    let user = UserRepository::find_by_id_safe(&mut conn, id)
        .map_err(|_| StatusCode::NOT_FOUND)?;
    
    Ok(Json(UserResponse {
        id: user.id,
        email: user.email,
        name: user.name,
    }))
}

/// 列出用户
#[instrument(name = "handler.list_users", skip(state))]
async fn list_users(
    State(state): State<AppState>,
) -> Result<Json<Vec<UserResponse>>, StatusCode> {
    let mut conn = get_connection_traced(&state.pool)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    let users = UserRepository::list(&mut conn, 1, 20)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    let response = users
        .into_iter()
        .map(|user| UserResponse {
            id: user.id,
            email: user.email,
            name: user.name,
        })
        .collect();
    
    Ok(Json(response))
}
```

---

## 最佳实践

### ✅ 基础实践

1. **始终使用连接池**

   ```rust
   // ✅ 使用连接池
   let pool = create_pool_with_tracing(url, "mydb", 100)?;
   let mut conn = pool.get()?;
   
   // ❌ 每次创建新连接
   ```

2. **使用 Diesel CLI 生成 schema**

   ```bash
   diesel migration run
   diesel print-schema > src/schema.rs
   ```

3. **参数化查询 (Diesel 默认)**

   ```rust
   // ✅ Diesel 自动参数化
   users::table.filter(users::email.eq(email))
   ```

### ⚡ 性能实践

1. **批量操作**

   ```rust
   // ✅ 批量插入
   diesel::insert_into(users::table)
       .values(&users)
       .execute(conn)?;
   ```

2. **只查询需要的列**

   ```rust
   // ✅ 只选择 email
   users::table.select(users::email).load(conn)?
   ```

3. **使用分页**

   ```rust
   users::table
       .limit(per_page)
       .offset(offset)
       .load(conn)?
   ```

### 🔍 可观测性实践

1. **添加追踪属性**

   ```rust
   #[instrument(name = "repo.user.find", fields(user.id = %id))]
   ```

2. **记录关键指标**

   ```rust
   span.record("db.row_count", count);
   ```

### 🛡️ 安全实践

1. **脱敏敏感信息**

   ```rust
   // 日志中移除密码
   let sanitized = url.replace(r"://([^:]+):([^@]+)@", "://$1:***@");
   ```

2. **使用事务保证一致性**

    ```rust
    TracedTransaction::execute(conn, |txn_conn| {
        // 多个操作...
    })?;
    ```

---

## 参考资源

### 📚 官方文档

- [Diesel Documentation](https://diesel.rs/)
- [Diesel Getting Started](https://diesel.rs/guides/getting-started)
- [OpenTelemetry Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/)

### 🔧 相关库

- [diesel](https://crates.io/crates/diesel) - ORM 框架
- [diesel-async](https://crates.io/crates/diesel-async) - 异步支持
- [r2d2](https://crates.io/crates/r2d2) - 连接池
- [opentelemetry](https://crates.io/crates/opentelemetry) - OpenTelemetry API

### 📖 扩展阅读

- [Diesel GitHub](https://github.com/diesel-rs/diesel)
- [Diesel async GitHub](https://github.com/weiznich/diesel_async)
- [Rust Database Performance](https://www.rust-lang.org/what/database)

---

**文档版本**: v1.0.0  
**最后更新**: 2025年10月8日  
**作者**: AI Assistant  
**许可证**: MIT OR Apache-2.0

[🏠 返回目录](../README.md) | [⬅️ SeaORM 追踪](02_SeaORM_数据库追踪_Rust完整版.md) | [➡️ MongoDB 追踪](04_MongoDB_追踪_Rust完整版.md)

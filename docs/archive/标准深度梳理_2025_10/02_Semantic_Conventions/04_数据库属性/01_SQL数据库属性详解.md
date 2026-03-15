# SQL数据库语义约定详解

> **Semantic Conventions版本**: v1.27.0  
> **稳定性**: Stable  
> **适用范围**: 所有SQL数据库（PostgreSQL, MySQL, SQL Server, Oracle等）  
> **最后更新**: 2025年10月8日

---

## 目录

- [SQL数据库语义约定详解](#sql数据库语义约定详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [适用范围](#适用范围)
    - [核心目标](#核心目标)
  - [2. SQL通用属性](#2-sql通用属性)
    - [2.1 核心必需属性](#21-核心必需属性)
    - [2.2 推荐属性](#22-推荐属性)
    - [2.3 SQL语句属性](#23-sql语句属性)
  - [3. 主流SQL数据库](#3-主流sql数据库)
    - [3.1 PostgreSQL](#31-postgresql)
    - [3.2 MySQL/MariaDB](#32-mysqlmariadb)
    - [3.3 SQL Server](#33-sql-server)
    - [3.4 Oracle Database](#34-oracle-database)
    - [3.5 SQLite](#35-sqlite)
  - [4. SQL语句处理](#4-sql语句处理)
    - [4.1 语句脱敏](#41-语句脱敏)
    - [4.2 SQL注入防护](#42-sql注入防护)
    - [4.3 参数化查询](#43-参数化查询)
  - [5. 连接池监控](#5-连接池监控)
    - [5.1 连接池属性](#51-连接池属性)
    - [5.2 连接池指标](#52-连接池指标)
  - [6. 事务追踪](#6-事务追踪)
    - [6.1 事务属性](#61-事务属性)
    - [6.2 事务隔离级别](#62-事务隔离级别)
  - [7. 实现示例](#7-实现示例)
    - [7.1 PostgreSQL (Go)](#71-postgresql-go)
    - [7.2 MySQL (Go)](#72-mysql-go)
    - [7.3 SQL Server (Go)](#73-sql-server-go)
    - [7.4 Python示例 (SQLAlchemy)](#74-python示例-sqlalchemy)
    - [7.5 Java示例 (JDBC)](#75-java示例-jdbc)
  - [8. 性能优化](#8-性能优化)
    - [8.1 慢查询追踪](#81-慢查询追踪)
    - [8.2 查询计划分析](#82-查询计划分析)
  - [9. 最佳实践](#9-最佳实践)
    - [✅ DO（推荐）](#-do推荐)
    - [❌ DON'T（避免）](#-dont避免)
  - [10. 故障排查](#10-故障排查)
    - [常见问题](#常见问题)
  - [11. 参考资源](#11-参考资源)
    - [官方文档](#官方文档)
    - [SDK文档](#sdk文档)
    - [数据库驱动](#数据库驱动)

---

## 1. 概述

SQL数据库语义约定定义了追踪SQL数据库操作的标准化属性，适用于所有关系型数据库。

### 适用范围

```text
✅ PostgreSQL
✅ MySQL / MariaDB
✅ Microsoft SQL Server
✅ Oracle Database
✅ IBM Db2
✅ SQLite
✅ CockroachDB
✅ Amazon Aurora
✅ Google Cloud SQL
✅ Azure SQL Database
```

### 核心目标

```text
1. 统一SQL追踪标准
2. 识别慢查询与性能瓶颈
3. 监控数据库连接与资源使用
4. 追踪事务与隔离级别
5. 确保敏感数据安全
```

---

## 2. SQL通用属性

### 2.1 核心必需属性

| 属性名 | 类型 | 必需性 | 描述 | 示例 |
|--------|------|--------|------|------|
| `db.system` | string | **必需** | 数据库系统标识符 | `postgresql`, `mysql`, `mssql` |
| `db.name` | string | **推荐** | 数据库名称 | `ecommerce`, `users_db` |
| `db.operation` | string | **推荐** | 数据库操作类型 | `SELECT`, `INSERT`, `UPDATE` |

### 2.2 推荐属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `db.user` | string | 数据库用户名 | `dbuser`, `app_readonly` |
| `db.connection_string` | string | 连接字符串（已脱敏） | `Server=mydb.example.com;Database=prod` |
| `server.address` | string | 数据库服务器地址 | `db.example.com` |
| `server.port` | int | 数据库服务器端口 | `5432`, `3306`, `1433` |
| `network.peer.address` | string | 对等网络地址 | `10.1.2.3` |
| `network.peer.port` | int | 对等网络端口 | `5432` |

### 2.3 SQL语句属性

| 属性名 | 类型 | 描述 | 注意事项 |
|--------|------|------|----------|
| `db.statement` | string | SQL语句（已脱敏） | **必须移除敏感数据** |
| `db.operation` | string | 操作类型 | 从SQL提取或手动设置 |
| `db.sql.table` | string | 主表名 | 简单查询可用 |

**语句脱敏示例**：

```sql
-- ❌ 原始SQL（不安全）
SELECT * FROM users WHERE email='user@example.com' AND password='secret123'

-- ✅ 脱敏SQL（安全）
SELECT * FROM users WHERE email=? AND password=?
```

---

## 3. 主流SQL数据库

### 3.1 PostgreSQL

**db.system**: `postgresql`  
**默认端口**: `5432`

**特定属性**：

| 属性名 | 描述 | 示例 |
|--------|------|------|
| `db.postgresql.schema` | PostgreSQL Schema | `public`, `analytics` |
| `db.postgresql.extension` | 使用的扩展 | `pg_stat_statements`, `pg_trgm` |

**连接字符串格式**：

```text
postgresql://user:password@host:5432/dbname?sslmode=require
```

**完整示例**：

```go
// PostgreSQL Span属性示例
attributes := []attribute.KeyValue{
    semconv.DBSystemPostgreSQL,
    semconv.DBNameKey.String("ecommerce"),
    semconv.DBOperationKey.String("SELECT"),
    semconv.DBStatementKey.String("SELECT id, name, email FROM users WHERE status = $1"),
    semconv.ServerAddressKey.String("db.example.com"),
    semconv.ServerPortKey.Int(5432),
    attribute.String("db.postgresql.schema", "public"),
}
```

### 3.2 MySQL/MariaDB

**db.system**: `mysql` (MySQL) 或 `mariadb` (MariaDB)  
**默认端口**: `3306`

**特定属性**：

| 属性名 | 描述 | 示例 |
|--------|------|------|
| `db.mysql.instance.id` | MySQL实例ID | `mysql-prod-001` |
| `db.mysql.character_set` | 字符集 | `utf8mb4` |

**连接字符串格式**：

```text
mysql://user:password@tcp(host:3306)/dbname?charset=utf8mb4&parseTime=True
```

**完整示例**：

```go
// MySQL Span属性示例
attributes := []attribute.KeyValue{
    semconv.DBSystemMySQL,
    semconv.DBNameKey.String("orders_db"),
    semconv.DBOperationKey.String("INSERT"),
    semconv.DBStatementKey.String("INSERT INTO orders (user_id, total) VALUES (?, ?)"),
    semconv.ServerAddressKey.String("mysql.example.com"),
    semconv.ServerPortKey.Int(3306),
    attribute.String("db.mysql.character_set", "utf8mb4"),
}
```

### 3.3 SQL Server

**db.system**: `mssql`  
**默认端口**: `1433`

**特定属性**：

| 属性名 | 描述 | 示例 |
|--------|------|------|
| `db.mssql.instance_name` | SQL Server实例名 | `SQLEXPRESS`, `PROD01` |
| `db.mssql.database_id` | 数据库ID | `5` |

**连接字符串格式**：

```text
sqlserver://user:password@host:1433?database=mydb&encrypt=true
```

**完整示例**：

```go
// SQL Server Span属性示例
attributes := []attribute.KeyValue{
    semconv.DBSystemMSSQL,
    semconv.DBNameKey.String("CRM"),
    semconv.DBOperationKey.String("UPDATE"),
    semconv.DBStatementKey.String("UPDATE Customers SET LastLogin = @p1 WHERE Id = @p2"),
    semconv.ServerAddressKey.String("sqlserver.example.com"),
    semconv.ServerPortKey.Int(1433),
    attribute.String("db.mssql.instance_name", "PROD01"),
}
```

### 3.4 Oracle Database

**db.system**: `oracle`  
**默认端口**: `1521`

**特定属性**：

| 属性名 | 描述 | 示例 |
|--------|------|------|
| `db.oracle.service_name` | Oracle服务名 | `ORCL`, `PRODDB` |
| `db.oracle.sid` | Oracle SID | `ORCL` |

**连接字符串格式**：

```text
oracle://user:password@host:1521/ORCL
```

**完整示例**：

```go
// Oracle Span属性示例
attributes := []attribute.KeyValue{
    semconv.DBSystemOracle,
    semconv.DBNameKey.String("HR"),
    semconv.DBOperationKey.String("SELECT"),
    semconv.DBStatementKey.String("SELECT * FROM employees WHERE department_id = :1"),
    semconv.ServerAddressKey.String("oracle.example.com"),
    semconv.ServerPortKey.Int(1521),
    attribute.String("db.oracle.service_name", "PRODDB"),
}
```

### 3.5 SQLite

**db.system**: `sqlite`  
**无网络连接**

**特定属性**：

| 属性名 | 描述 | 示例 |
|--------|------|------|
| `db.sqlite.file_path` | SQLite数据库文件路径 | `/data/app.db` |
| `db.sqlite.version` | SQLite版本 | `3.40.0` |

**完整示例**：

```go
// SQLite Span属性示例
attributes := []attribute.KeyValue{
    semconv.DBSystemSQLite,
    semconv.DBNameKey.String("app.db"),
    semconv.DBOperationKey.String("SELECT"),
    semconv.DBStatementKey.String("SELECT * FROM config WHERE key = ?"),
    attribute.String("db.sqlite.file_path", "/data/app.db"),
}
```

---

## 4. SQL语句处理

### 4.1 语句脱敏

**安全规则**：

```text
✅ DO: 使用占位符替换参数值
✅ DO: 移除敏感字段值（密码、信用卡号）
✅ DO: 限制SQL语句长度（建议≤2048字符）
❌ DON'T: 记录原始SQL语句
❌ DON'T: 包含用户输入的原始值
❌ DON'T: 记录加密密钥或token
```

**脱敏示例**：

```go
// 脱敏函数示例
func sanitizeSQL(query string, args []interface{}) string {
    // 方法1: 使用占位符
    sanitized := query
    for range args {
        sanitized = strings.Replace(sanitized, "?", "?", 1)
    }
    return sanitized
}

// 使用示例
originalSQL := "SELECT * FROM users WHERE email='user@example.com'"
sanitizedSQL := "SELECT * FROM users WHERE email=?"
span.SetAttributes(semconv.DBStatementKey.String(sanitizedSQL))
```

### 4.2 SQL注入防护

**追踪SQL注入风险**：

```go
import (
    "regexp"
)

func detectSQLInjection(query string) bool {
    // 检测常见SQL注入模式
    patterns := []string{
        `(?i)(\bunion\b.*\bselect\b)`,
        `(?i)(\bor\b.*=.*\bor\b)`,
        `(?i)(;.*drop\b)`,
        `(?i)(;.*delete\b)`,
        `(?i)(;.*insert\b)`,
    }
    
    for _, pattern := range patterns {
        matched, _ := regexp.MatchString(pattern, query)
        if matched {
            return true
        }
    }
    return false
}

// 使用示例
if detectSQLInjection(userInput) {
    span.SetAttributes(
        attribute.Bool("db.sql.injection_detected", true),
        attribute.String("security.threat.type", "sql_injection"),
    )
    span.SetStatus(codes.Error, "SQL injection attempt detected")
}
```

### 4.3 参数化查询

**最佳实践示例**：

```go
// ✅ 推荐：使用参数化查询
func getUserByEmail(ctx context.Context, email string) (*User, error) {
    ctx, span := tracer.Start(ctx, "db.query.user_by_email",
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            semconv.DBOperationKey.String("SELECT"),
            semconv.DBStatementKey.String("SELECT * FROM users WHERE email = $1"),
        ),
    )
    defer span.End()
    
    var user User
    err := db.QueryRowContext(ctx, 
        "SELECT * FROM users WHERE email = $1", 
        email,
    ).Scan(&user.ID, &user.Name, &user.Email)
    
    return &user, err
}

// ❌ 不推荐：字符串拼接
func getUserByEmailUnsafe(ctx context.Context, email string) (*User, error) {
    query := fmt.Sprintf("SELECT * FROM users WHERE email = '%s'", email)
    // 存在SQL注入风险！
    return nil, nil
}
```

---

## 5. 连接池监控

### 5.1 连接池属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `db.connection_pool.name` | string | 连接池名称 | `main_pool`, `readonly_pool` |
| `db.connection_pool.state` | string | 连接状态 | `idle`, `used` |

### 5.2 连接池指标

**推荐的Metrics**：

```go
import (
    "go.opentelemetry.io/otel/metric"
)

// 定义连接池指标
var (
    // 活跃连接数
    dbConnectionsActive, _ = meter.Int64ObservableGauge(
        "db.client.connections.active",
        metric.WithDescription("Active database connections"),
    )
    
    // 空闲连接数
    dbConnectionsIdle, _ = meter.Int64ObservableGauge(
        "db.client.connections.idle",
        metric.WithDescription("Idle database connections"),
    )
    
    // 最大连接数
    dbConnectionsMax, _ = meter.Int64ObservableGauge(
        "db.client.connections.max",
        metric.WithDescription("Maximum allowed connections"),
    )
    
    // 连接超时次数
    dbConnectionTimeouts, _ = meter.Int64Counter(
        "db.client.connections.timeouts",
        metric.WithDescription("Database connection timeout count"),
    )
)

// 定期采集连接池状态
func collectPoolStats(pool *sql.DB) {
    stats := pool.Stats()
    
    dbConnectionsActive.Observe(ctx, int64(stats.InUse),
        metric.WithAttributes(
            semconv.DBSystemPostgreSQL,
            attribute.String("pool.name", "main"),
        ),
    )
    
    dbConnectionsIdle.Observe(ctx, int64(stats.Idle),
        metric.WithAttributes(
            semconv.DBSystemPostgreSQL,
            attribute.String("pool.name", "main"),
        ),
    )
}
```

---

## 6. 事务追踪

### 6.1 事务属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `db.transaction.id` | string | 事务ID | `txn_123456` |
| `db.transaction.isolation_level` | string | 隔离级别 | `READ_COMMITTED`, `SERIALIZABLE` |
| `db.transaction.readonly` | boolean | 是否只读事务 | `true`, `false` |

### 6.2 事务隔离级别

**标准SQL隔离级别**：

```text
1. READ_UNCOMMITTED  - 读未提交
2. READ_COMMITTED    - 读已提交（默认）
3. REPEATABLE_READ   - 可重复读
4. SERIALIZABLE      - 串行化
```

**事务追踪示例**：

```go
func performTransaction(ctx context.Context, db *sql.DB) error {
    // 开始事务追踪
    ctx, txSpan := tracer.Start(ctx, "db.transaction",
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            attribute.String("db.transaction.isolation_level", "READ_COMMITTED"),
            attribute.Bool("db.transaction.readonly", false),
        ),
    )
    defer txSpan.End()
    
    // 开始数据库事务
    tx, err := db.BeginTx(ctx, &sql.TxOptions{
        Isolation: sql.LevelReadCommitted,
    })
    if err != nil {
        txSpan.RecordError(err)
        return err
    }
    defer tx.Rollback()
    
    // 执行操作1
    ctx, op1Span := tracer.Start(ctx, "db.transaction.operation1",
        trace.WithAttributes(
            semconv.DBOperationKey.String("INSERT"),
            semconv.DBStatementKey.String("INSERT INTO orders VALUES (?, ?, ?)"),
        ),
    )
    _, err = tx.ExecContext(ctx, "INSERT INTO orders VALUES (?, ?, ?)", 1, 100, "user1")
    op1Span.End()
    if err != nil {
        return err
    }
    
    // 执行操作2
    ctx, op2Span := tracer.Start(ctx, "db.transaction.operation2",
        trace.WithAttributes(
            semconv.DBOperationKey.String("UPDATE"),
            semconv.DBStatementKey.String("UPDATE inventory SET count = count - ? WHERE id = ?"),
        ),
    )
    _, err = tx.ExecContext(ctx, "UPDATE inventory SET count = count - ? WHERE id = ?", 1, 100)
    op2Span.End()
    if err != nil {
        return err
    }
    
    // 提交事务
    if err := tx.Commit(); err != nil {
        txSpan.RecordError(err)
        txSpan.SetStatus(codes.Error, "Transaction commit failed")
        return err
    }
    
    txSpan.SetAttributes(attribute.String("db.transaction.status", "committed"))
    return nil
}
```

---

## 7. 实现示例

### 7.1 PostgreSQL (Go)

```go
package main

import (
    "context"
    "database/sql"
    "fmt"
    
    _ "github.com/lib/pq"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("postgresql-example")

// User 用户模型
type User struct {
    ID    int
    Name  string
    Email string
}

// PostgresDB 封装数据库操作
type PostgresDB struct {
    db *sql.DB
}

// NewPostgresDB 创建数据库连接
func NewPostgresDB(dsn string) (*PostgresDB, error) {
    db, err := sql.Open("postgres", dsn)
    if err != nil {
        return nil, err
    }
    
    // 配置连接池
    db.SetMaxOpenConns(25)
    db.SetMaxIdleConns(5)
    
    return &PostgresDB{db: db}, nil
}

// GetUser 查询用户
func (p *PostgresDB) GetUser(ctx context.Context, userID int) (*User, error) {
    ctx, span := tracer.Start(ctx, "db.query.get_user",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            semconv.DBNameKey.String("users_db"),
            semconv.DBOperationKey.String("SELECT"),
            semconv.DBStatementKey.String("SELECT id, name, email FROM users WHERE id = $1"),
            semconv.ServerAddressKey.String("db.example.com"),
            semconv.ServerPortKey.Int(5432),
            attribute.String("db.postgresql.schema", "public"),
        ),
    )
    defer span.End()
    
    var user User
    query := "SELECT id, name, email FROM users WHERE id = $1"
    
    err := p.db.QueryRowContext(ctx, query, userID).Scan(
        &user.ID,
        &user.Name,
        &user.Email,
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    
    span.SetAttributes(
        attribute.Int("db.result.rows", 1),
        attribute.String("db.user.id", fmt.Sprintf("%d", user.ID)),
    )
    
    return &user, nil
}

// CreateUser 创建用户
func (p *PostgresDB) CreateUser(ctx context.Context, name, email string) (int, error) {
    ctx, span := tracer.Start(ctx, "db.query.create_user",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            semconv.DBNameKey.String("users_db"),
            semconv.DBOperationKey.String("INSERT"),
            semconv.DBStatementKey.String("INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id"),
            semconv.ServerAddressKey.String("db.example.com"),
            semconv.ServerPortKey.Int(5432),
        ),
    )
    defer span.End()
    
    var userID int
    query := "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id"
    
    err := p.db.QueryRowContext(ctx, query, name, email).Scan(&userID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return 0, err
    }
    
    span.SetAttributes(
        attribute.Int("db.user.created_id", userID),
        attribute.String("db.operation.status", "success"),
    )
    
    return userID, nil
}

// UpdateUser 更新用户
func (p *PostgresDB) UpdateUser(ctx context.Context, userID int, name string) error {
    ctx, span := tracer.Start(ctx, "db.query.update_user",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            semconv.DBNameKey.String("users_db"),
            semconv.DBOperationKey.String("UPDATE"),
            semconv.DBStatementKey.String("UPDATE users SET name = $1 WHERE id = $2"),
            semconv.ServerAddressKey.String("db.example.com"),
            semconv.ServerPortKey.Int(5432),
        ),
    )
    defer span.End()
    
    result, err := p.db.ExecContext(ctx, 
        "UPDATE users SET name = $1 WHERE id = $2", 
        name, userID,
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    rowsAffected, _ := result.RowsAffected()
    span.SetAttributes(
        attribute.Int64("db.result.rows_affected", rowsAffected),
    )
    
    return nil
}

// GetPoolStats 获取连接池统计
func (p *PostgresDB) GetPoolStats(ctx context.Context) sql.DBStats {
    _, span := tracer.Start(ctx, "db.pool.stats",
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
        ),
    )
    defer span.End()
    
    stats := p.db.Stats()
    
    span.SetAttributes(
        attribute.Int("db.connections.open", stats.OpenConnections),
        attribute.Int("db.connections.in_use", stats.InUse),
        attribute.Int("db.connections.idle", stats.Idle),
        attribute.Int64("db.connections.wait_count", stats.WaitCount),
        attribute.String("db.connections.wait_duration", stats.WaitDuration.String()),
    )
    
    return stats
}
```

### 7.2 MySQL (Go)

```go
package main

import (
    "context"
    "database/sql"
    
    _ "github.com/go-sql-driver/mysql"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

var mysqlTracer = otel.Tracer("mysql-example")

// Order 订单模型
type Order struct {
    ID     int
    UserID int
    Total  float64
    Status string
}

// MySQLDB MySQL数据库封装
type MySQLDB struct {
    db *sql.DB
}

// NewMySQLDB 创建MySQL连接
func NewMySQLDB(dsn string) (*MySQLDB, error) {
    // DSN格式: user:password@tcp(host:3306)/dbname?charset=utf8mb4&parseTime=True
    db, err := sql.Open("mysql", dsn)
    if err != nil {
        return nil, err
    }
    
    // 配置连接池
    db.SetMaxOpenConns(50)
    db.SetMaxIdleConns(10)
    
    return &MySQLDB{db: db}, nil
}

// CreateOrder 创建订单
func (m *MySQLDB) CreateOrder(ctx context.Context, userID int, total float64) (int64, error) {
    ctx, span := mysqlTracer.Start(ctx, "db.query.create_order",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMySQL,
            semconv.DBNameKey.String("orders_db"),
            semconv.DBOperationKey.String("INSERT"),
            semconv.DBStatementKey.String("INSERT INTO orders (user_id, total, status) VALUES (?, ?, ?)"),
            semconv.ServerAddressKey.String("mysql.example.com"),
            semconv.ServerPortKey.Int(3306),
            attribute.String("db.mysql.character_set", "utf8mb4"),
        ),
    )
    defer span.End()
    
    result, err := m.db.ExecContext(ctx,
        "INSERT INTO orders (user_id, total, status) VALUES (?, ?, ?)",
        userID, total, "pending",
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return 0, err
    }
    
    orderID, _ := result.LastInsertId()
    span.SetAttributes(
        attribute.Int64("db.order.created_id", orderID),
    )
    
    return orderID, nil
}

// GetOrdersByUser 查询用户订单
func (m *MySQLDB) GetOrdersByUser(ctx context.Context, userID int) ([]Order, error) {
    ctx, span := mysqlTracer.Start(ctx, "db.query.get_orders_by_user",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMySQL,
            semconv.DBNameKey.String("orders_db"),
            semconv.DBOperationKey.String("SELECT"),
            semconv.DBStatementKey.String("SELECT id, user_id, total, status FROM orders WHERE user_id = ?"),
            semconv.ServerAddressKey.String("mysql.example.com"),
            semconv.ServerPortKey.Int(3306),
        ),
    )
    defer span.End()
    
    rows, err := m.db.QueryContext(ctx,
        "SELECT id, user_id, total, status FROM orders WHERE user_id = ?",
        userID,
    )
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    defer rows.Close()
    
    var orders []Order
    for rows.Next() {
        var order Order
        if err := rows.Scan(&order.ID, &order.UserID, &order.Total, &order.Status); err != nil {
            span.RecordError(err)
            continue
        }
        orders = append(orders, order)
    }
    
    span.SetAttributes(
        attribute.Int("db.result.rows", len(orders)),
    )
    
    return orders, nil
}
```

### 7.3 SQL Server (Go)

```go
package main

import (
    "context"
    "database/sql"
    
    _ "github.com/denisenkom/go-mssqldb"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

var mssqlTracer = otel.Tracer("mssql-example")

// SQLServerDB SQL Server数据库封装
type SQLServerDB struct {
    db *sql.DB
}

// NewSQLServerDB 创建SQL Server连接
func NewSQLServerDB(dsn string) (*SQLServerDB, error) {
    // DSN格式: sqlserver://user:password@host:1433?database=mydb&encrypt=true
    db, err := sql.Open("sqlserver", dsn)
    if err != nil {
        return nil, err
    }
    
    return &SQLServerDB{db: db}, nil
}

// GetCustomer 查询客户
func (s *SQLServerDB) GetCustomer(ctx context.Context, customerID int) error {
    ctx, span := mssqlTracer.Start(ctx, "db.query.get_customer",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemMSSQL,
            semconv.DBNameKey.String("CRM"),
            semconv.DBOperationKey.String("SELECT"),
            semconv.DBStatementKey.String("SELECT * FROM Customers WHERE Id = @p1"),
            semconv.ServerAddressKey.String("sqlserver.example.com"),
            semconv.ServerPortKey.Int(1433),
            attribute.String("db.mssql.instance_name", "PROD01"),
        ),
    )
    defer span.End()
    
    // SQL Server使用命名参数
    _, err := s.db.ExecContext(ctx, 
        "SELECT * FROM Customers WHERE Id = @p1", 
        sql.Named("p1", customerID),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    return nil
}
```

### 7.4 Python示例 (SQLAlchemy)

```python
from opentelemetry import trace
from opentelemetry.semconv.trace import SpanAttributes
from sqlalchemy import create_engine, Column, Integer, String
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy.orm import sessionmaker

tracer = trace.get_tracer(__name__)
Base = declarative_base()

class User(Base):
    __tablename__ = 'users'
    id = Column(Integer, primary_key=True)
    name = Column(String)
    email = Column(String)

# 创建数据库连接
engine = create_engine('postgresql://user:pass@localhost:5432/mydb')
Session = sessionmaker(bind=engine)

def get_user(user_id: int):
    with tracer.start_as_current_span(
        "db.query.get_user",
        attributes={
            SpanAttributes.DB_SYSTEM: "postgresql",
            SpanAttributes.DB_NAME: "mydb",
            SpanAttributes.DB_OPERATION: "SELECT",
            SpanAttributes.DB_STATEMENT: "SELECT * FROM users WHERE id = ?",
            SpanAttributes.SERVER_ADDRESS: "localhost",
            SpanAttributes.SERVER_PORT: 5432,
        }
    ) as span:
        session = Session()
        try:
            user = session.query(User).filter(User.id == user_id).first()
            span.set_attribute("db.result.rows", 1 if user else 0)
            return user
        except Exception as e:
            span.record_exception(e)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
        finally:
            session.close()

def create_user(name: str, email: str):
    with tracer.start_as_current_span(
        "db.query.create_user",
        attributes={
            SpanAttributes.DB_SYSTEM: "postgresql",
            SpanAttributes.DB_NAME: "mydb",
            SpanAttributes.DB_OPERATION: "INSERT",
            SpanAttributes.DB_STATEMENT: "INSERT INTO users (name, email) VALUES (?, ?)",
        }
    ) as span:
        session = Session()
        try:
            new_user = User(name=name, email=email)
            session.add(new_user)
            session.commit()
            span.set_attribute("db.user.created_id", new_user.id)
            return new_user.id
        except Exception as e:
            session.rollback()
            span.record_exception(e)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise
        finally:
            session.close()
```

### 7.5 Java示例 (JDBC)

```java
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.semconv.trace.attributes.SemanticAttributes;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

public class PostgreSQLExample {
    private final Tracer tracer;
    private final Connection connection;

    public PostgreSQLExample(Tracer tracer, String url, String user, String password) 
            throws SQLException {
        this.tracer = tracer;
        this.connection = DriverManager.getConnection(url, user, password);
    }

    public User getUser(int userId) throws SQLException {
        Span span = tracer.spanBuilder("db.query.get_user")
            .setAttribute(SemanticAttributes.DB_SYSTEM, "postgresql")
            .setAttribute(SemanticAttributes.DB_NAME, "users_db")
            .setAttribute(SemanticAttributes.DB_OPERATION, "SELECT")
            .setAttribute(SemanticAttributes.DB_STATEMENT, 
                "SELECT id, name, email FROM users WHERE id = ?")
            .setAttribute(SemanticAttributes.SERVER_ADDRESS, "db.example.com")
            .setAttribute(SemanticAttributes.SERVER_PORT, 5432)
            .startSpan();

        try {
            String query = "SELECT id, name, email FROM users WHERE id = ?";
            PreparedStatement stmt = connection.prepareStatement(query);
            stmt.setInt(1, userId);
            
            ResultSet rs = stmt.executeQuery();
            if (rs.next()) {
                User user = new User(
                    rs.getInt("id"),
                    rs.getString("name"),
                    rs.getString("email")
                );
                span.setAttribute("db.result.rows", 1);
                return user;
            }
            
            span.setAttribute("db.result.rows", 0);
            return null;
            
        } catch (SQLException e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        } finally {
            span.end();
        }
    }

    public int createUser(String name, String email) throws SQLException {
        Span span = tracer.spanBuilder("db.query.create_user")
            .setAttribute(SemanticAttributes.DB_SYSTEM, "postgresql")
            .setAttribute(SemanticAttributes.DB_NAME, "users_db")
            .setAttribute(SemanticAttributes.DB_OPERATION, "INSERT")
            .setAttribute(SemanticAttributes.DB_STATEMENT, 
                "INSERT INTO users (name, email) VALUES (?, ?) RETURNING id")
            .setAttribute(SemanticAttributes.SERVER_ADDRESS, "db.example.com")
            .setAttribute(SemanticAttributes.SERVER_PORT, 5432)
            .startSpan();

        try {
            String query = "INSERT INTO users (name, email) VALUES (?, ?) RETURNING id";
            PreparedStatement stmt = connection.prepareStatement(query);
            stmt.setString(1, name);
            stmt.setString(2, email);
            
            ResultSet rs = stmt.executeQuery();
            if (rs.next()) {
                int userId = rs.getInt("id");
                span.setAttribute("db.user.created_id", userId);
                return userId;
            }
            
            throw new SQLException("Failed to create user");
            
        } catch (SQLException e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        } finally {
            span.end();
        }
    }
}

class User {
    private int id;
    private String name;
    private String email;

    public User(int id, String name, String email) {
        this.id = id;
        this.name = name;
        this.email = email;
    }
    
    // Getters and setters...
}
```

---

## 8. 性能优化

### 8.1 慢查询追踪

**自动检测慢查询**：

```go
import "time"

const slowQueryThreshold = 100 * time.Millisecond

func (p *PostgresDB) QueryWithSlowDetection(ctx context.Context, query string, args ...interface{}) error {
    start := time.Now()
    
    ctx, span := tracer.Start(ctx, "db.query",
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            semconv.DBStatementKey.String(sanitizeSQL(query)),
        ),
    )
    defer span.End()
    
    _, err := p.db.ExecContext(ctx, query, args...)
    
    duration := time.Since(start)
    span.SetAttributes(
        attribute.Int64("db.query.duration_ms", duration.Milliseconds()),
    )
    
    // 标记慢查询
    if duration > slowQueryThreshold {
        span.SetAttributes(
            attribute.Bool("db.query.slow", true),
            attribute.String("db.query.performance", "slow"),
        )
        // 可以触发告警
        fmt.Printf("SLOW QUERY DETECTED: %s (duration: %v)\n", query, duration)
    }
    
    return err
}
```

### 8.2 查询计划分析

**PostgreSQL EXPLAIN追踪**：

```go
func (p *PostgresDB) ExplainQuery(ctx context.Context, query string, args ...interface{}) (string, error) {
    ctx, span := tracer.Start(ctx, "db.explain",
        trace.WithAttributes(
            semconv.DBSystemPostgreSQL,
            semconv.DBOperationKey.String("EXPLAIN"),
            semconv.DBStatementKey.String(query),
        ),
    )
    defer span.End()
    
    explainQuery := "EXPLAIN (FORMAT JSON, ANALYZE) " + query
    
    var planJSON string
    err := p.db.QueryRowContext(ctx, explainQuery, args...).Scan(&planJSON)
    if err != nil {
        span.RecordError(err)
        return "", err
    }
    
    span.SetAttributes(
        attribute.String("db.query.plan", planJSON),
    )
    
    return planJSON, nil
}
```

---

## 9. 最佳实践

### ✅ DO（推荐）

```text
1. 语句脱敏
   ✅ 始终使用参数化查询
   ✅ 移除敏感数据值
   ✅ 限制语句长度

2. 属性完整性
   ✅ 设置db.system（必需）
   ✅ 设置db.operation
   ✅ 包含服务器地址和端口

3. 错误处理
   ✅ 使用span.RecordError()记录错误
   ✅ 设置适当的Status
   ✅ 区分客户端错误和服务器错误

4. 性能监控
   ✅ 追踪查询执行时间
   ✅ 监控慢查询
   ✅ 采集连接池指标

5. 事务追踪
   ✅ 为事务创建父Span
   ✅ 为每个操作创建子Span
   ✅ 记录隔离级别
```

### ❌ DON'T（避免）

```text
1. 安全风险
   ❌ 不要记录原始SQL（含参数值）
   ❌ 不要记录密码或敏感字段
   ❌ 不要忽略SQL注入风险

2. 性能问题
   ❌ 不要为每个查询都记录EXPLAIN
   ❌ 不要记录超长SQL语句
   ❌ 不要在高频查询中创建过多Span

3. 属性错误
   ❌ 不要遗漏db.system
   ❌ 不要混淆db.name和db.user
   ❌ 不要使用自定义数据库系统名称
```

---

## 10. 故障排查

### 常见问题

**问题1: 连接超时**:

```go
// 症状: 大量 "connection timeout" 错误

// 诊断: 检查连接池配置
stats := db.Stats()
fmt.Printf("MaxOpenConns: %d, InUse: %d, Idle: %d, WaitCount: %d\n",
    stats.MaxOpenConnections, stats.InUse, stats.Idle, stats.WaitCount)

// 解决方案: 调整连接池大小
db.SetMaxOpenConns(50)  // 增加最大连接数
db.SetMaxIdleConns(10)  // 增加空闲连接数
db.SetConnMaxLifetime(5 * time.Minute)  // 设置连接最大生命周期
```

**问题2: 慢查询**:

```go
// 症状: 查询响应时间过长

// 诊断: 使用EXPLAIN分析
planJSON, _ := db.ExplainQuery(ctx, "SELECT * FROM users WHERE email = $1", "user@example.com")
// 查找 "Seq Scan" (全表扫描) 或 "cost" 过高的节点

// 解决方案: 添加索引
_, err := db.ExecContext(ctx, "CREATE INDEX idx_users_email ON users(email)")
```

**问题3: 连接泄漏**:

```go
// 症状: 连接数持续增长，不释放

// 诊断: 检查是否忘记关闭rows
rows, err := db.QueryContext(ctx, query)
// ❌ 忘记 defer rows.Close()

// 解决方案: 始终关闭资源
rows, err := db.QueryContext(ctx, query)
if err != nil {
    return err
}
defer rows.Close()  // ✅ 确保关闭
```

---

## 11. 参考资源

### 官方文档

- [Database Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/database/)
- [Database Metrics](https://opentelemetry.io/docs/specs/semconv/database/database-metrics/)
- [SQL Database Conventions](https://opentelemetry.io/docs/specs/semconv/database/sql/)

### SDK文档

- [OpenTelemetry Go](https://github.com/open-telemetry/opentelemetry-go)
- [OpenTelemetry Python](https://github.com/open-telemetry/opentelemetry-python)
- [OpenTelemetry Java](https://github.com/open-telemetry/opentelemetry-java)

### 数据库驱动

- [PostgreSQL - pq](https://github.com/lib/pq)
- [MySQL - go-sql-driver](https://github.com/go-sql-driver/mysql)
- [SQL Server - go-mssqldb](https://github.com/denisenkom/go-mssqldb)

---

**文档版本**: v1.0  
**最后更新**: 2025年10月8日  
**维护者**: OTLP深度梳理项目组

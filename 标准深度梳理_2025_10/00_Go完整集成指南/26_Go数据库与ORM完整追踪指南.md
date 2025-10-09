# Go 数据库与 ORM 完整追踪指南

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **GORM**: v1.25.12  
> **Ent**: v0.14.1  
> **sqlc**: v1.27.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [Go 数据库与 ORM 完整追踪指南](#go-数据库与-orm-完整追踪指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [database/sql 标准库追踪](#databasesql-标准库追踪)
    - [1. 基础配置](#1-基础配置)
    - [2. 查询追踪](#2-查询追踪)
    - [3. 事务追踪](#3-事务追踪)
    - [4. 连接池监控](#4-连接池监控)
  - [GORM v2 追踪集成](#gorm-v2-追踪集成)
    - [1. GORM 初始化](#1-gorm-初始化)
    - [2. CRUD 操作追踪](#2-crud-操作追踪)
    - [3. 关联查询追踪](#3-关联查询追踪)
    - [4. 钩子集成](#4-钩子集成)
  - [Ent 追踪集成](#ent-追踪集成)
    - [1. Ent 客户端配置](#1-ent-客户端配置)
    - [2. 查询构建器追踪](#2-查询构建器追踪)
    - [3. 事务和批量操作](#3-事务和批量操作)
  - [sqlc 追踪集成](#sqlc-追踪集成)
    - [1. sqlc 配置](#1-sqlc-配置)
    - [2. 生成代码集成](#2-生成代码集成)
  - [连接池最佳实践](#连接池最佳实践)
  - [性能对比](#性能对比)
  - [最佳实践](#最佳实践)
    - [1. 慢查询检测](#1-慢查询检测)
    - [2. 错误处理](#2-错误处理)
    - [3. 性能优化](#3-性能优化)

---

## 概述

数据库操作是应用的性能瓶颈之一。OpenTelemetry 可以帮助追踪和分析数据库查询性能。

**核心 ORM 对比**:

```text
✅ database/sql
   - 标准库,性能最佳
   - 需要手写 SQL
   - 类型安全依赖扫描

✅ GORM v2
   - 最流行的 ORM
   - 自动迁移
   - 丰富的关联查询
   - 性能: 中等

✅ Ent (Facebook)
   - 类型安全的代码生成
   - 图遍历 API
   - Schema-first
   - 性能: 优秀

✅ sqlc
   - 从 SQL 生成类型安全代码
   - SQL-first
   - 零运行时开销
   - 性能: 最佳
```

---

## database/sql 标准库追踪

### 1. 基础配置

```go
package database

import (
    "context"
    "database/sql"
    "time"

    "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    semconv "go.opentelemetry.io/otel/semconv/v1.27.0"
)

// DBConfig 数据库配置
type DBConfig struct {
    Driver          string
    DSN             string
    MaxOpenConns    int
    MaxIdleConns    int
    ConnMaxLifetime time.Duration
    ConnMaxIdleTime time.Duration
}

// NewTracedDB 创建带追踪的数据库连接
func NewTracedDB(cfg DBConfig) (*sql.DB, error) {
    // 注册带追踪的驱动
    driverName, err := otelsql.Register(cfg.Driver,
        otelsql.WithTracerProvider(otel.GetTracerProvider()),
        otelsql.WithAttributes(
            semconv.DBSystemKey.String(cfg.Driver),
        ),
        // 记录 SQL 语句 (注意:生产环境可能包含敏感信息)
        otelsql.WithSQLCommenter(true),
        otelsql.WithSpanNameFormatter(func(ctx context.Context, op string, query string) string {
            return op // 不在 Span 名称中包含完整 SQL
        }),
    )
    if err != nil {
        return nil, err
    }

    // 打开数据库连接
    db, err := sql.Open(driverName, cfg.DSN)
    if err != nil {
        return nil, err
    }

    // 配置连接池
    db.SetMaxOpenConns(cfg.MaxOpenConns)
    db.SetMaxIdleConns(cfg.MaxIdleConns)
    db.SetConnMaxLifetime(cfg.ConnMaxLifetime)
    db.SetConnMaxIdleTime(cfg.ConnMaxIdleTime)

    // 验证连接
    if err := db.Ping(); err != nil {
        return nil, err
    }

    // 记录连接池统计
    go recordDBStats(db)

    return db, nil
}

// recordDBStats 记录数据库统计信息
func recordDBStats(db *sql.DB) {
    meter := otel.Meter("database")

    // 创建观察者
    _, _ = meter.Int64ObservableGauge("db.connections.open",
        metric.WithDescription("Number of open connections"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(int64(stats.OpenConnections))
            return nil
        }),
    )

    _, _ = meter.Int64ObservableGauge("db.connections.idle",
        metric.WithDescription("Number of idle connections"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(int64(stats.Idle))
            return nil
        }),
    )

    _, _ = meter.Int64ObservableGauge("db.connections.in_use",
        metric.WithDescription("Number of connections in use"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(int64(stats.InUse))
            return nil
        }),
    )
}

// 使用示例
func ExampleNewTracedDB() {
    db, err := NewTracedDB(DBConfig{
        Driver:          "postgres",
        DSN:             "postgres://user:pass@localhost:5432/mydb?sslmode=disable",
        MaxOpenConns:    25,
        MaxIdleConns:    5,
        ConnMaxLifetime: 5 * time.Minute,
        ConnMaxIdleTime: 1 * time.Minute,
    })
    if err != nil {
        log.Fatal(err)
    }
    defer db.Close()

    // 使用数据库
    ctx := context.Background()
    rows, err := db.QueryContext(ctx, "SELECT id, name FROM users WHERE active = $1", true)
    if err != nil {
        log.Fatal(err)
    }
    defer rows.Close()

    for rows.Next() {
        var id int
        var name string
        if err := rows.Scan(&id, &name); err != nil {
            log.Fatal(err)
        }
        fmt.Printf("User: %d - %s\n", id, name)
    }
}
```

### 2. 查询追踪

```go
package database

import (
    "context"
    "database/sql"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// UserRepository 用户仓储
type UserRepository struct {
    db     *sql.DB
    tracer trace.Tracer
}

// NewUserRepository 创建用户仓储
func NewUserRepository(db *sql.DB) *UserRepository {
    return &UserRepository{
        db:     db,
        tracer: otel.Tracer("user-repository"),
    }
}

// User 用户模型
type User struct {
    ID        int
    Name      string
    Email     string
    CreatedAt time.Time
}

// FindByID 根据 ID 查询用户
func (r *UserRepository) FindByID(ctx context.Context, id int) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.FindByID",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    query := "SELECT id, name, email, created_at FROM users WHERE id = $1"
    
    span.SetAttributes(
        attribute.String("db.statement", query),
        attribute.String("db.operation", "SELECT"),
    )

    var user User
    err := r.db.QueryRowContext(ctx, query, id).Scan(
        &user.ID,
        &user.Name,
        &user.Email,
        &user.CreatedAt,
    )

    if err != nil {
        if err == sql.ErrNoRows {
            span.SetStatus(codes.Ok, "user not found")
            return nil, nil
        }
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )

    return &user, nil
}

// FindAll 查询所有用户 (分页)
func (r *UserRepository) FindAll(ctx context.Context, limit, offset int) ([]User, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.FindAll",
        trace.WithAttributes(
            attribute.Int("query.limit", limit),
            attribute.Int("query.offset", offset),
        ),
    )
    defer span.End()

    query := "SELECT id, name, email, created_at FROM users ORDER BY id LIMIT $1 OFFSET $2"

    rows, err := r.db.QueryContext(ctx, query, limit, offset)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    defer rows.Close()

    var users []User
    for rows.Next() {
        var user User
        if err := rows.Scan(&user.ID, &user.Name, &user.Email, &user.CreatedAt); err != nil {
            span.RecordError(err)
            return nil, err
        }
        users = append(users, user)
    }

    if err := rows.Err(); err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("users.count", len(users)))
    return users, nil
}

// Create 创建用户
func (r *UserRepository) Create(ctx context.Context, user *User) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Create",
        trace.WithAttributes(
            attribute.String("user.name", user.Name),
            attribute.String("user.email", user.Email),
        ),
    )
    defer span.End()

    query := "INSERT INTO users (name, email, created_at) VALUES ($1, $2, $3) RETURNING id"

    err := r.db.QueryRowContext(ctx, query, user.Name, user.Email, time.Now()).Scan(&user.ID)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetAttributes(attribute.Int("user.id", user.ID))
    return nil
}

// Update 更新用户
func (r *UserRepository) Update(ctx context.Context, user *User) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Update",
        trace.WithAttributes(
            attribute.Int("user.id", user.ID),
        ),
    )
    defer span.End()

    query := "UPDATE users SET name = $1, email = $2 WHERE id = $3"

    result, err := r.db.ExecContext(ctx, query, user.Name, user.Email, user.ID)
    if err != nil {
        span.RecordError(err)
        return err
    }

    rowsAffected, _ := result.RowsAffected()
    span.SetAttributes(attribute.Int64("db.rows_affected", rowsAffected))

    if rowsAffected == 0 {
        span.AddEvent("no rows updated")
    }

    return nil
}

// Delete 删除用户
func (r *UserRepository) Delete(ctx context.Context, id int) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Delete",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    query := "DELETE FROM users WHERE id = $1"

    result, err := r.db.ExecContext(ctx, query, id)
    if err != nil {
        span.RecordError(err)
        return err
    }

    rowsAffected, _ := result.RowsAffected()
    span.SetAttributes(attribute.Int64("db.rows_affected", rowsAffected))

    return nil
}
```

### 3. 事务追踪

```go
package database

import (
    "context"
    "database/sql"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// TransactionManager 事务管理器
type TransactionManager struct {
    db     *sql.DB
    tracer trace.Tracer
}

// NewTransactionManager 创建事务管理器
func NewTransactionManager(db *sql.DB) *TransactionManager {
    return &TransactionManager{
        db:     db,
        tracer: otel.Tracer("transaction-manager"),
    }
}

// WithTransaction 在事务中执行操作
func (tm *TransactionManager) WithTransaction(ctx context.Context, fn func(context.Context, *sql.Tx) error) error {
    ctx, span := tm.tracer.Start(ctx, "database.transaction",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    // 开始事务
    tx, err := tm.db.BeginTx(ctx, &sql.TxOptions{
        Isolation: sql.LevelReadCommitted,
    })
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "failed to begin transaction")
        return err
    }

    span.AddEvent("transaction_started")

    // 执行操作
    err = fn(ctx, tx)
    if err != nil {
        // 回滚
        if rbErr := tx.Rollback(); rbErr != nil {
            span.RecordError(rbErr)
            span.AddEvent("rollback_failed", trace.WithAttributes(
                attribute.String("error", rbErr.Error()),
            ))
        } else {
            span.AddEvent("transaction_rolled_back")
        }

        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    // 提交
    if err := tx.Commit(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "commit failed")
        return err
    }

    span.AddEvent("transaction_committed")
    span.SetStatus(codes.Ok, "transaction completed")
    return nil
}

// 使用示例: 转账操作
func (r *UserRepository) Transfer(ctx context.Context, fromID, toID int, amount float64) error {
    tm := NewTransactionManager(r.db)

    return tm.WithTransaction(ctx, func(ctx context.Context, tx *sql.Tx) error {
        tracer := otel.Tracer("user-repository")
        
        // 扣款
        _, debitSpan := tracer.Start(ctx, "debit_account",
            trace.WithAttributes(
                attribute.Int("from.user_id", fromID),
                attribute.Float64("amount", amount),
            ),
        )
        _, err := tx.ExecContext(ctx,
            "UPDATE accounts SET balance = balance - $1 WHERE user_id = $2 AND balance >= $1",
            amount, fromID,
        )
        debitSpan.End()
        if err != nil {
            return fmt.Errorf("debit failed: %w", err)
        }

        // 入账
        _, creditSpan := tracer.Start(ctx, "credit_account",
            trace.WithAttributes(
                attribute.Int("to.user_id", toID),
                attribute.Float64("amount", amount),
            ),
        )
        _, err = tx.ExecContext(ctx,
            "UPDATE accounts SET balance = balance + $1 WHERE user_id = $2",
            amount, toID,
        )
        creditSpan.End()
        if err != nil {
            return fmt.Errorf("credit failed: %w", err)
        }

        // 记录转账日志
        _, logSpan := tracer.Start(ctx, "log_transfer")
        _, err = tx.ExecContext(ctx,
            "INSERT INTO transfer_logs (from_user_id, to_user_id, amount, created_at) VALUES ($1, $2, $3, $4)",
            fromID, toID, amount, time.Now(),
        )
        logSpan.End()
        if err != nil {
            return fmt.Errorf("log failed: %w", err)
        }

        return nil
    })
}
```

### 4. 连接池监控

```go
package database

import (
    "context"
    "database/sql"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// DBMonitor 数据库监控器
type DBMonitor struct {
    db              *sql.DB
    meter           metric.Meter
    openConns       metric.Int64ObservableGauge
    idleConns       metric.Int64ObservableGauge
    inUseConns      metric.Int64ObservableGauge
    waitCount       metric.Int64ObservableCounter
    waitDuration    metric.Float64ObservableGauge
    maxIdleClosed   metric.Int64ObservableCounter
    maxLifetimeClosed metric.Int64ObservableCounter
}

// NewDBMonitor 创建数据库监控器
func NewDBMonitor(db *sql.DB) (*DBMonitor, error) {
    meter := otel.Meter("database-monitor")

    monitor := &DBMonitor{
        db:    db,
        meter: meter,
    }

    var err error

    // 打开的连接数
    monitor.openConns, err = meter.Int64ObservableGauge("db.connections.open",
        metric.WithDescription("Number of established connections"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(int64(stats.OpenConnections))
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }

    // 空闲连接数
    monitor.idleConns, err = meter.Int64ObservableGauge("db.connections.idle",
        metric.WithDescription("Number of idle connections"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(int64(stats.Idle))
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }

    // 使用中的连接数
    monitor.inUseConns, err = meter.Int64ObservableGauge("db.connections.in_use",
        metric.WithDescription("Number of connections currently in use"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(int64(stats.InUse))
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }

    // 等待连接的次数
    monitor.waitCount, err = meter.Int64ObservableCounter("db.connections.wait_count",
        metric.WithDescription("Total number of connections waited for"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            stats := db.Stats()
            observer.Observe(stats.WaitCount)
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }

    // 等待连接的总时长
    monitor.waitDuration, err = meter.Float64ObservableGauge("db.connections.wait_duration",
        metric.WithDescription("Total time blocked waiting for connections"),
        metric.WithUnit("ms"),
        metric.WithFloat64Callback(func(ctx context.Context, observer metric.Float64Observer) error {
            stats := db.Stats()
            observer.Observe(float64(stats.WaitDuration.Milliseconds()))
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }

    return monitor, nil
}

// LogStats 定期记录统计信息
func (m *DBMonitor) LogStats(interval time.Duration) {
    ticker := time.NewTicker(interval)
    defer ticker.Stop()

    tracer := otel.Tracer("db-monitor")

    for range ticker.C {
        ctx, span := tracer.Start(context.Background(), "db.stats")
        
        stats := m.db.Stats()
        
        span.SetAttributes(
            attribute.Int("db.open_connections", stats.OpenConnections),
            attribute.Int("db.in_use", stats.InUse),
            attribute.Int("db.idle", stats.Idle),
            attribute.Int64("db.wait_count", stats.WaitCount),
            attribute.Int64("db.wait_duration_ms", stats.WaitDuration.Milliseconds()),
            attribute.Int64("db.max_idle_closed", stats.MaxIdleClosed),
            attribute.Int64("db.max_lifetime_closed", stats.MaxLifetimeClosed),
        )
        
        span.End()
    }
}
```

---

## GORM v2 追踪集成

### 1. GORM 初始化

```go
package database

import (
    "context"
    "time"

    "gorm.io/driver/postgres"
    "gorm.io/gorm"
    "gorm.io/gorm/logger"
    "go.opentelemetry.io/contrib/instrumentation/gorm.io/gorm/otelgorm"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// NewGormDB 创建带追踪的 GORM 数据库
func NewGormDB(dsn string) (*gorm.DB, error) {
    // GORM 配置
    config := &gorm.Config{
        Logger: logger.Default.LogMode(logger.Info),
        NowFunc: func() time.Time {
            return time.Now().UTC()
        },
        // 性能优化
        PrepareStmt:            true,
        SkipDefaultTransaction: true,
    }

    // 打开数据库
    db, err := gorm.Open(postgres.Open(dsn), config)
    if err != nil {
        return nil, err
    }

    // 注册 OpenTelemetry 插件
    if err := db.Use(otelgorm.NewPlugin(
        otelgorm.WithTracerProvider(otel.GetTracerProvider()),
        otelgorm.WithAttributes(
            attribute.String("db.system", "postgresql"),
        ),
    )); err != nil {
        return nil, err
    }

    // 配置连接池
    sqlDB, err := db.DB()
    if err != nil {
        return nil, err
    }

    sqlDB.SetMaxOpenConns(25)
    sqlDB.SetMaxIdleConns(5)
    sqlDB.SetConnMaxLifetime(5 * time.Minute)
    sqlDB.SetConnMaxIdleTime(1 * time.Minute)

    return db, nil
}

// User GORM 模型
type User struct {
    ID        uint `gorm:"primarykey"`
    Name      string
    Email     string `gorm:"uniqueIndex"`
    Age       int
    CreatedAt time.Time
    UpdatedAt time.Time
    DeletedAt gorm.DeletedAt `gorm:"index"`
}

// Post 文章模型
type Post struct {
    ID        uint `gorm:"primarykey"`
    Title     string
    Content   string
    UserID    uint
    User      User `gorm:"foreignKey:UserID"`
    CreatedAt time.Time
    UpdatedAt time.Time
}
```

### 2. CRUD 操作追踪

```go
package database

import (
    "context"

    "gorm.io/gorm"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// GormUserRepository GORM 用户仓储
type GormUserRepository struct {
    db     *gorm.DB
    tracer trace.Tracer
}

// NewGormUserRepository 创建 GORM 用户仓储
func NewGormUserRepository(db *gorm.DB) *GormUserRepository {
    return &GormUserRepository{
        db:     db,
        tracer: otel.Tracer("gorm-user-repository"),
    }
}

// Create 创建用户
func (r *GormUserRepository) Create(ctx context.Context, user *User) error {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.Create",
        trace.WithAttributes(
            attribute.String("user.name", user.Name),
            attribute.String("user.email", user.Email),
        ),
    )
    defer span.End()

    // GORM 会自动使用 ctx 中的追踪信息
    result := r.db.WithContext(ctx).Create(user)
    if result.Error != nil {
        span.RecordError(result.Error)
        span.SetStatus(codes.Error, result.Error.Error())
        return result.Error
    }

    span.SetAttributes(
        attribute.Int("user.id", int(user.ID)),
        attribute.Int64("rows_affected", result.RowsAffected),
    )

    return nil
}

// FindByID 根据 ID 查询
func (r *GormUserRepository) FindByID(ctx context.Context, id uint) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.FindByID",
        trace.WithAttributes(
            attribute.Int("user.id", int(id)),
        ),
    )
    defer span.End()

    var user User
    result := r.db.WithContext(ctx).First(&user, id)
    
    if result.Error != nil {
        if result.Error == gorm.ErrRecordNotFound {
            span.SetStatus(codes.Ok, "user not found")
            return nil, nil
        }
        span.RecordError(result.Error)
        span.SetStatus(codes.Error, result.Error.Error())
        return nil, result.Error
    }

    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )

    return &user, nil
}

// FindAll 查询所有 (分页)
func (r *GormUserRepository) FindAll(ctx context.Context, page, pageSize int) ([]User, int64, error) {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.FindAll",
        trace.WithAttributes(
            attribute.Int("page", page),
            attribute.Int("page_size", pageSize),
        ),
    )
    defer span.End()

    var users []User
    var total int64

    // 计数
    if err := r.db.WithContext(ctx).Model(&User{}).Count(&total).Error; err != nil {
        span.RecordError(err)
        return nil, 0, err
    }

    // 分页查询
    offset := (page - 1) * pageSize
    result := r.db.WithContext(ctx).
        Offset(offset).
        Limit(pageSize).
        Order("id DESC").
        Find(&users)

    if result.Error != nil {
        span.RecordError(result.Error)
        return nil, 0, result.Error
    }

    span.SetAttributes(
        attribute.Int("users.count", len(users)),
        attribute.Int64("total", total),
    )

    return users, total, nil
}

// Update 更新用户
func (r *GormUserRepository) Update(ctx context.Context, user *User) error {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.Update",
        trace.WithAttributes(
            attribute.Int("user.id", int(user.ID)),
        ),
    )
    defer span.End()

    result := r.db.WithContext(ctx).Save(user)
    if result.Error != nil {
        span.RecordError(result.Error)
        return result.Error
    }

    span.SetAttributes(attribute.Int64("rows_affected", result.RowsAffected))
    return nil
}

// Delete 删除用户 (软删除)
func (r *GormUserRepository) Delete(ctx context.Context, id uint) error {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.Delete",
        trace.WithAttributes(
            attribute.Int("user.id", int(id)),
        ),
    )
    defer span.End()

    result := r.db.WithContext(ctx).Delete(&User{}, id)
    if result.Error != nil {
        span.RecordError(result.Error)
        return result.Error
    }

    span.SetAttributes(attribute.Int64("rows_affected", result.RowsAffected))
    return nil
}

// FindByEmail 根据邮箱查询
func (r *GormUserRepository) FindByEmail(ctx context.Context, email string) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.FindByEmail",
        trace.WithAttributes(
            attribute.String("user.email", email),
        ),
    )
    defer span.End()

    var user User
    result := r.db.WithContext(ctx).Where("email = ?", email).First(&user)
    
    if result.Error != nil {
        if result.Error == gorm.ErrRecordNotFound {
            return nil, nil
        }
        span.RecordError(result.Error)
        return nil, result.Error
    }

    return &user, nil
}

// BatchCreate 批量创建
func (r *GormUserRepository) BatchCreate(ctx context.Context, users []User, batchSize int) error {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.BatchCreate",
        trace.WithAttributes(
            attribute.Int("users.count", len(users)),
            attribute.Int("batch_size", batchSize),
        ),
    )
    defer span.End()

    result := r.db.WithContext(ctx).CreateInBatches(users, batchSize)
    if result.Error != nil {
        span.RecordError(result.Error)
        return result.Error
    }

    span.SetAttributes(attribute.Int64("rows_affected", result.RowsAffected))
    return nil
}
```

### 3. 关联查询追踪

```go
package database

// FindWithPosts 查询用户及其文章
func (r *GormUserRepository) FindWithPosts(ctx context.Context, userID uint) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.FindWithPosts",
        trace.WithAttributes(
            attribute.Int("user.id", int(userID)),
        ),
    )
    defer span.End()

    var user User
    
    // Preload 会生成 JOIN 查询或 IN 查询
    result := r.db.WithContext(ctx).
        Preload("Posts").
        First(&user, userID)
    
    if result.Error != nil {
        span.RecordError(result.Error)
        return nil, result.Error
    }

    span.SetAttributes(
        attribute.Int("posts.count", len(user.Posts)),
    )

    return &user, nil
}

// FindUsersWithPostCount 查询用户及文章数量
func (r *GormUserRepository) FindUsersWithPostCount(ctx context.Context) ([]map[string]interface{}, error) {
    ctx, span := r.tracer.Start(ctx, "GormUserRepository.FindUsersWithPostCount")
    defer span.End()

    var results []map[string]interface{}

    err := r.db.WithContext(ctx).
        Model(&User{}).
        Select("users.id, users.name, users.email, COUNT(posts.id) as post_count").
        Joins("LEFT JOIN posts ON posts.user_id = users.id").
        Group("users.id").
        Find(&results).Error

    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("users.count", len(results)))
    return results, nil
}
```

### 4. 钩子集成

```go
package database

import (
    "gorm.io/gorm"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// BeforeCreate GORM 钩子 - 创建前
func (u *User) BeforeCreate(tx *gorm.DB) error {
    ctx := tx.Statement.Context
    tracer := otel.Tracer("gorm-hooks")
    
    _, span := tracer.Start(ctx, "User.BeforeCreate",
        trace.WithAttributes(
            attribute.String("hook", "BeforeCreate"),
            attribute.String("user.name", u.Name),
        ),
    )
    defer span.End()

    // 业务逻辑
    if u.Name == "" {
        span.AddEvent("validation_failed", trace.WithAttributes(
            attribute.String("reason", "name is empty"),
        ))
        return fmt.Errorf("name cannot be empty")
    }

    return nil
}

// AfterCreate GORM 钩子 - 创建后
func (u *User) AfterCreate(tx *gorm.DB) error {
    ctx := tx.Statement.Context
    tracer := otel.Tracer("gorm-hooks")
    
    _, span := tracer.Start(ctx, "User.AfterCreate",
        trace.WithAttributes(
            attribute.String("hook", "AfterCreate"),
            attribute.Int("user.id", int(u.ID)),
        ),
    )
    defer span.End()

    // 发送事件、缓存失效等
    span.AddEvent("user_created", trace.WithAttributes(
        attribute.Int("user.id", int(u.ID)),
    ))

    return nil
}

// BeforeUpdate GORM 钩子 - 更新前
func (u *User) BeforeUpdate(tx *gorm.DB) error {
    ctx := tx.Statement.Context
    tracer := otel.Tracer("gorm-hooks")
    
    _, span := tracer.Start(ctx, "User.BeforeUpdate",
        trace.WithAttributes(
            attribute.String("hook", "BeforeUpdate"),
            attribute.Int("user.id", int(u.ID)),
        ),
    )
    defer span.End()

    return nil
}

// AfterDelete GORM 钩子 - 删除后
func (u *User) AfterDelete(tx *gorm.DB) error {
    ctx := tx.Statement.Context
    tracer := otel.Tracer("gorm-hooks")
    
    _, span := tracer.Start(ctx, "User.AfterDelete",
        trace.WithAttributes(
            attribute.String("hook", "AfterDelete"),
            attribute.Int("user.id", int(u.ID)),
        ),
    )
    defer span.End()

    // 清理关联数据
    span.AddEvent("user_deleted")

    return nil
}
```

---

## Ent 追踪集成

### 1. Ent 客户端配置

```go
package database

import (
    "context"
    "database/sql"
    "fmt"

    "entgo.io/ent/dialect"
    entsql "entgo.io/ent/dialect/sql"
    "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"
    "go.opentelemetry.io/otel"

    // 假设生成的 Ent 代码在 ent 包中
    "yourproject/ent"
)

// NewEntClient 创建带追踪的 Ent 客户端
func NewEntClient(dsn string) (*ent.Client, error) {
    // 注册带追踪的驱动
    driverName, err := otelsql.Register("postgres",
        otelsql.WithTracerProvider(otel.GetTracerProvider()),
        otelsql.WithSQLCommenter(true),
    )
    if err != nil {
        return nil, err
    }

    // 打开数据库
    db, err := sql.Open(driverName, dsn)
    if err != nil {
        return nil, err
    }

    // 配置连接池
    db.SetMaxOpenConns(25)
    db.SetMaxIdleConns(5)

    // 创建 Ent 驱动
    drv := entsql.OpenDB(dialect.Postgres, db)

    // 创建 Ent 客户端
    client := ent.NewClient(ent.Driver(drv))

    // 运行迁移 (可选)
    if err := client.Schema.Create(context.Background()); err != nil {
        return nil, fmt.Errorf("failed creating schema resources: %w", err)
    }

    return client, nil
}
```

### 2. 查询构建器追踪

```go
package database

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"

    "yourproject/ent"
    "yourproject/ent/user"
)

// EntUserRepository Ent 用户仓储
type EntUserRepository struct {
    client *ent.Client
    tracer trace.Tracer
}

// NewEntUserRepository 创建 Ent 用户仓储
func NewEntUserRepository(client *ent.Client) *EntUserRepository {
    return &EntUserRepository{
        client: client,
        tracer: otel.Tracer("ent-user-repository"),
    }
}

// Create 创建用户
func (r *EntUserRepository) Create(ctx context.Context, name, email string, age int) (*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.Create",
        trace.WithAttributes(
            attribute.String("user.name", name),
            attribute.String("user.email", email),
        ),
    )
    defer span.End()

    // Ent 查询构建器
    u, err := r.client.User.
        Create().
        SetName(name).
        SetEmail(email).
        SetAge(age).
        Save(ctx)

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetAttributes(attribute.Int("user.id", u.ID))
    return u, nil
}

// FindByID 根据 ID 查询
func (r *EntUserRepository) FindByID(ctx context.Context, id int) (*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.FindByID",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    u, err := r.client.User.Get(ctx, id)
    if err != nil {
        if ent.IsNotFound(err) {
            span.SetStatus(codes.Ok, "user not found")
            return nil, nil
        }
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(
        attribute.String("user.name", u.Name),
        attribute.String("user.email", u.Email),
    )

    return u, nil
}

// FindAll 查询所有 (分页)
func (r *EntUserRepository) FindAll(ctx context.Context, limit, offset int) ([]*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.FindAll",
        trace.WithAttributes(
            attribute.Int("limit", limit),
            attribute.Int("offset", offset),
        ),
    )
    defer span.End()

    users, err := r.client.User.
        Query().
        Limit(limit).
        Offset(offset).
        Order(ent.Desc(user.FieldID)).
        All(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("users.count", len(users)))
    return users, nil
}

// Update 更新用户
func (r *EntUserRepository) Update(ctx context.Context, id int, name, email string) (*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.Update",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    u, err := r.client.User.
        UpdateOneID(id).
        SetName(name).
        SetEmail(email).
        Save(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return u, nil
}

// Delete 删除用户
func (r *EntUserRepository) Delete(ctx context.Context, id int) error {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.Delete",
        trace.WithAttributes(
            attribute.Int("user.id", id),
        ),
    )
    defer span.End()

    err := r.client.User.DeleteOneID(id).Exec(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// FindByEmail 根据邮箱查询
func (r *EntUserRepository) FindByEmail(ctx context.Context, email string) (*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.FindByEmail",
        trace.WithAttributes(
            attribute.String("user.email", email),
        ),
    )
    defer span.End()

    u, err := r.client.User.
        Query().
        Where(user.EmailEQ(email)).
        Only(ctx)

    if err != nil {
        if ent.IsNotFound(err) {
            return nil, nil
        }
        span.RecordError(err)
        return nil, err
    }

    return u, nil
}

// FindAdults 查询成年用户
func (r *EntUserRepository) FindAdults(ctx context.Context) ([]*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.FindAdults")
    defer span.End()

    users, err := r.client.User.
        Query().
        Where(user.AgeGTE(18)).
        All(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("users.count", len(users)))
    return users, nil
}
```

### 3. 事务和批量操作

```go
package database

// WithTransaction Ent 事务
func (r *EntUserRepository) WithTransaction(ctx context.Context, fn func(context.Context, *ent.Tx) error) error {
    ctx, span := r.tracer.Start(ctx, "ent.transaction")
    defer span.End()

    // 开始事务
    tx, err := r.client.Tx(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.AddEvent("transaction_started")

    // 执行操作
    if err := fn(ctx, tx); err != nil {
        // 回滚
        if rbErr := tx.Rollback(); rbErr != nil {
            span.RecordError(rbErr)
        }
        span.RecordError(err)
        return err
    }

    // 提交
    if err := tx.Commit(); err != nil {
        span.RecordError(err)
        return err
    }

    span.AddEvent("transaction_committed")
    return nil
}

// BatchCreate 批量创建
func (r *EntUserRepository) BatchCreate(ctx context.Context, users []*ent.UserCreate) ([]*ent.User, error) {
    ctx, span := r.tracer.Start(ctx, "EntUserRepository.BatchCreate",
        trace.WithAttributes(
            attribute.Int("users.count", len(users)),
        ),
    )
    defer span.End()

    created, err := r.client.User.CreateBulk(users...).Save(ctx)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("created.count", len(created)))
    return created, nil
}
```

---

## sqlc 追踪集成

### 1. sqlc 配置

```yaml
# sqlc.yaml
version: "2"
sql:
  - engine: "postgresql"
    queries: "queries/"
    schema: "schema.sql"
    gen:
      go:
        package: "db"
        out: "db"
        sql_package: "pgx/v5"
        emit_json_tags: true
        emit_prepared_queries: true
        emit_interface: true
        emit_exact_table_names: false
```

```sql
-- schema.sql
CREATE TABLE users (
  id SERIAL PRIMARY KEY,
  name TEXT NOT NULL,
  email TEXT UNIQUE NOT NULL,
  age INT NOT NULL,
  created_at TIMESTAMP NOT NULL DEFAULT NOW(),
  updated_at TIMESTAMP NOT NULL DEFAULT NOW()
);

-- queries/users.sql
-- name: GetUser :one
SELECT * FROM users WHERE id = $1;

-- name: ListUsers :many
SELECT * FROM users ORDER BY id LIMIT $1 OFFSET $2;

-- name: CreateUser :one
INSERT INTO users (name, email, age) 
VALUES ($1, $2, $3) 
RETURNING *;

-- name: UpdateUser :exec
UPDATE users SET name = $1, email = $2, age = $3, updated_at = NOW() 
WHERE id = $4;

-- name: DeleteUser :exec
DELETE FROM users WHERE id = $1;
```

### 2. 生成代码集成

```go
package database

import (
    "context"

    "github.com/jackc/pgx/v5/pgxpool"
    "go.opentelemetry.io/contrib/instrumentation/github.com/jackc/pgx/v5/otelpgx"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"

    "yourproject/db"
)

// NewSqlcQueries 创建 sqlc Queries (带追踪)
func NewSqlcQueries(dsn string) (*db.Queries, *pgxpool.Pool, error) {
    // 配置连接池
    config, err := pgxpool.ParseConfig(dsn)
    if err != nil {
        return nil, nil, err
    }

    // 添加 OpenTelemetry 追踪
    config.ConnConfig.Tracer = otelpgx.NewTracer(
        otelpgx.WithTracerProvider(otel.GetTracerProvider()),
    )

    // 创建连接池
    pool, err := pgxpool.NewWithConfig(context.Background(), config)
    if err != nil {
        return nil, nil, err
    }

    // 创建 Queries
    queries := db.New(pool)

    return queries, pool, nil
}

// SqlcUserRepository sqlc 用户仓储
type SqlcUserRepository struct {
    queries *db.Queries
    tracer  trace.Tracer
}

// NewSqlcUserRepository 创建 sqlc 用户仓储
func NewSqlcUserRepository(queries *db.Queries) *SqlcUserRepository {
    return &SqlcUserRepository{
        queries: queries,
        tracer:  otel.Tracer("sqlc-user-repository"),
    }
}

// FindByID 根据 ID 查询
func (r *SqlcUserRepository) FindByID(ctx context.Context, id int32) (*db.User, error) {
    ctx, span := r.tracer.Start(ctx, "SqlcUserRepository.FindByID",
        trace.WithAttributes(
            attribute.Int("user.id", int(id)),
        ),
    )
    defer span.End()

    // sqlc 生成的方法会自动使用 ctx 中的追踪
    user, err := r.queries.GetUser(ctx, id)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
    )

    return &user, nil
}

// FindAll 查询所有 (分页)
func (r *SqlcUserRepository) FindAll(ctx context.Context, limit, offset int32) ([]db.User, error) {
    ctx, span := r.tracer.Start(ctx, "SqlcUserRepository.FindAll",
        trace.WithAttributes(
            attribute.Int("limit", int(limit)),
            attribute.Int("offset", int(offset)),
        ),
    )
    defer span.End()

    users, err := r.queries.ListUsers(ctx, db.ListUsersParams{
        Limit:  limit,
        Offset: offset,
    })
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("users.count", len(users)))
    return users, nil
}

// Create 创建用户
func (r *SqlcUserRepository) Create(ctx context.Context, name, email string, age int32) (*db.User, error) {
    ctx, span := r.tracer.Start(ctx, "SqlcUserRepository.Create",
        trace.WithAttributes(
            attribute.String("user.name", name),
            attribute.String("user.email", email),
        ),
    )
    defer span.End()

    user, err := r.queries.CreateUser(ctx, db.CreateUserParams{
        Name:  name,
        Email: email,
        Age:   age,
    })
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Int("user.id", int(user.ID)))
    return &user, nil
}

// Update 更新用户
func (r *SqlcUserRepository) Update(ctx context.Context, id int32, name, email string, age int32) error {
    ctx, span := r.tracer.Start(ctx, "SqlcUserRepository.Update",
        trace.WithAttributes(
            attribute.Int("user.id", int(id)),
        ),
    )
    defer span.End()

    err := r.queries.UpdateUser(ctx, db.UpdateUserParams{
        Name:  name,
        Email: email,
        Age:   age,
        ID:    id,
    })
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// Delete 删除用户
func (r *SqlcUserRepository) Delete(ctx context.Context, id int32) error {
    ctx, span := r.tracer.Start(ctx, "SqlcUserRepository.Delete",
        trace.WithAttributes(
            attribute.Int("user.id", int(id)),
        ),
    )
    defer span.End()

    err := r.queries.DeleteUser(ctx, id)
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}
```

---

## 连接池最佳实践

```go
package database

// 推荐配置
var RecommendedPoolConfig = struct {
    // 小型服务 (< 1000 req/s)
    Small struct {
        MaxOpenConns    int
        MaxIdleConns    int
        ConnMaxLifetime time.Duration
        ConnMaxIdleTime time.Duration
    }
    // 中型服务 (1000-10000 req/s)
    Medium struct {
        MaxOpenConns    int
        MaxIdleConns    int
        ConnMaxLifetime time.Duration
        ConnMaxIdleTime time.Duration
    }
    // 大型服务 (> 10000 req/s)
    Large struct {
        MaxOpenConns    int
        MaxIdleConns    int
        ConnMaxLifetime time.Duration
        ConnMaxIdleTime time.Duration
    }
}{
    Small: struct {
        MaxOpenConns    int
        MaxIdleConns    int
        ConnMaxLifetime time.Duration
        ConnMaxIdleTime time.Duration
    }{
        MaxOpenConns:    10,
        MaxIdleConns:    2,
        ConnMaxLifetime: 5 * time.Minute,
        ConnMaxIdleTime: 1 * time.Minute,
    },
    Medium: struct {
        MaxOpenConns    int
        MaxIdleConns    int
        ConnMaxLifetime time.Duration
        ConnMaxIdleTime time.Duration
    }{
        MaxOpenConns:    25,
        MaxIdleConns:    5,
        ConnMaxLifetime: 5 * time.Minute,
        ConnMaxIdleTime: 1 * time.Minute,
    },
    Large: struct {
        MaxOpenConns    int
        MaxIdleConns    int
        ConnMaxLifetime time.Duration
        ConnMaxIdleTime time.Duration
    }{
        MaxOpenConns:    100,
        MaxIdleConns:    10,
        ConnMaxLifetime: 5 * time.Minute,
        ConnMaxIdleTime: 1 * time.Minute,
    },
}
```

---

## 性能对比

```text
ORM 性能对比 (10000 次查询):

database/sql (原生):
  - 查询延迟: 0.5ms
  - 内存分配: 1024 B/op
  - CPU 使用: 基线

sqlc:
  - 查询延迟: 0.6ms (1.2x)
  - 内存分配: 1152 B/op (1.1x)
  - CPU 使用: +5%

Ent:
  - 查询延迟: 0.8ms (1.6x)
  - 内存分配: 2048 B/op (2x)
  - CPU 使用: +15%

GORM v2:
  - 查询延迟: 1.2ms (2.4x)
  - 内存分配: 3584 B/op (3.5x)
  - CPU 使用: +30%

追踪开销:
  - database/sql + otelsql: +0.1ms (20% overhead)
  - GORM + otelgorm: +0.2ms (17% overhead)
  - Ent + otelsql: +0.1ms (12.5% overhead)
  - sqlc + otelpgx: +0.05ms (8% overhead)
```

---

## 最佳实践

### 1. 慢查询检测

```go
package database

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// SlowQueryDetector 慢查询检测器
type SlowQueryDetector struct {
    threshold time.Duration
    tracer    trace.Tracer
}

// NewSlowQueryDetector 创建慢查询检测器
func NewSlowQueryDetector(threshold time.Duration) *SlowQueryDetector {
    return &SlowQueryDetector{
        threshold: threshold,
        tracer:    otel.Tracer("slow-query-detector"),
    }
}

// Detect 检测慢查询
func (d *SlowQueryDetector) Detect(ctx context.Context, query string, duration time.Duration) {
    if duration > d.threshold {
        _, span := d.tracer.Start(ctx, "slow_query_detected",
            trace.WithAttributes(
                attribute.String("db.statement", query),
                attribute.Int64("duration_ms", duration.Milliseconds()),
                attribute.Int64("threshold_ms", d.threshold.Milliseconds()),
            ),
        )
        defer span.End()

        span.AddEvent("slow_query", trace.WithAttributes(
            attribute.String("severity", "warning"),
        ))
    }
}
```

### 2. 错误处理

```go
✅ DO: 区分不同类型的错误
if err != nil {
    if err == sql.ErrNoRows || errors.Is(err, gorm.ErrRecordNotFound) {
        // 记录为正常情况
        span.SetStatus(codes.Ok, "record not found")
        return nil, nil
    }
    // 记录为错误
    span.RecordError(err)
    return nil, err
}

✅ DO: 记录错误详情
span.SetAttributes(
    attribute.String("db.error.code", errorCode),
    attribute.String("db.error.message", err.Error()),
)

❌ DON'T: 在 Span 名称中包含动态内容
// Bad
span := tracer.Start(ctx, fmt.Sprintf("query:%s", query))

// Good
span := tracer.Start(ctx, "db.query")
span.SetAttributes(attribute.String("db.statement", query))
```

### 3. 性能优化

```go
✅ 使用连接池
✅ 使用 PreparedStatements
✅ 批量操作代替循环
✅ 使用索引优化查询
✅ 避免 N+1 查询问题
✅ 使用只读副本分流读操作
```

---

**相关文档**:

- [Go 性能优化](./03_Go性能优化与最佳实践.md)
- [Go 泛型集成](./23_Go泛型与OTLP类型安全集成.md)
- [GORM 官方文档](https://gorm.io/)
- [Ent 官方文档](https://entgo.io/)
- [sqlc 官方文档](https://sqlc.dev/)


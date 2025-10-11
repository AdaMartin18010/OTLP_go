# Bun ORM 与 OTLP 完整集成（2025版）

> **Bun 版本**: v1.2+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [1. Bun ORM 概述](#1-bun-orm-概述)
- [2. 快速开始](#2-快速开始)
- [3. 完整集成示例](#3-完整集成示例)
- [4. 高级特性](#4-高级特性)
- [5. 性能优化](#5-性能优化)
- [6. 生产部署](#6-生产部署)
- [7. 最佳实践](#7-最佳实践)

---

## 1. Bun ORM 概述

**Bun** 是一个现代化的 Go SQL ORM，支持 PostgreSQL, MySQL, SQLite。

```text
🚀 核心特性:
  ✅ 类型安全 - 完整的泛型支持
  ✅ 高性能 - 零反射，接近原生 SQL 性能
  ✅ 多数据库 - PostgreSQL, MySQL, SQLite
  ✅ 原生 OTLP - 内置 OpenTelemetry 支持
  ✅ 迁移工具 - 数据库迁移管理
  ✅ 关系映射 - 强大的关联查询

📊 性能对比:
  - GORM:     100%  (基线)
  - Bun:       50%  (快2倍)
  - sqlx:      40%  (快2.5倍)
  - database/sql: 35% (快3倍)
```

### 1.1 为什么选择 Bun

```go
// 1. 类型安全的查询构建器
// Bun: ✅ 编译时类型检查
var users []User
err := db.NewSelect().
    Model(&users).
    Where("age > ?", 18).
    Order("created_at DESC").
    Limit(10).
    Scan(ctx)

// GORM: ❌ 运行时错误
db.Where("age > ?", 18).
   Order("created_at DESC").
   Limit(10).
   Find(&users)

// 2. 泛型支持
// Bun: ✅ Go 1.18+ 泛型
func FindByID[T any](ctx context.Context, db *bun.DB, id int64) (*T, error) {
    var model T
    err := db.NewSelect().Model(&model).Where("id = ?", id).Scan(ctx)
    return &model, err
}

// 3. 原生 SQL 支持
// Bun: ✅ 完整的原生 SQL
err := db.NewRaw("SELECT * FROM users WHERE age > ?", 18).Scan(ctx, &users)

// 4. 批量操作优化
// Bun: ✅ 真正的批量插入（一条 SQL）
_, err := db.NewInsert().Model(&users).Exec(ctx)

// GORM: ❌ 循环插入（N 条 SQL）
db.Create(&users)
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 Bun ORM
go get -u github.com/uptrace/bun@v1.2.0
go get -u github.com/uptrace/bun/dialect/pgdialect@v1.2.0
go get -u github.com/uptrace/bun/driver/pgdriver@v1.2.0

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u github.com/uptrace/bun/extra/bunotel@v1.2.0  # Bun 的 OTLP 插件
```

### 2.2 基础集成

```go
package main

import (
    "context"
    "database/sql"
    "log"
    "time"

    "github.com/uptrace/bun"
    "github.com/uptrace/bun/dialect/pgdialect"
    "github.com/uptrace/bun/driver/pgdriver"
    "github.com/uptrace/bun/extra/bunotel"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

// User 模型
type User struct {
    ID        int64     `bun:"id,pk,autoincrement"`
    Username  string    `bun:"username,notnull"`
    Email     string    `bun:"email,notnull,unique"`
    Age       int       `bun:"age"`
    CreatedAt time.Time `bun:"created_at,notnull,default:current_timestamp"`
    UpdatedAt time.Time `bun:"updated_at,notnull,default:current_timestamp"`
}

// 初始化 Tracer
func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("bun-demo"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

// 初始化数据库
func initDB() *bun.DB {
    // 连接 PostgreSQL
    dsn := "postgres://user:pass@localhost:5432/database?sslmode=disable"
    sqldb := sql.OpenDB(pgdriver.NewConnector(pgdriver.WithDSN(dsn)))

    // 创建 Bun DB
    db := bun.NewDB(sqldb, pgdialect.New())

    // 添加 OpenTelemetry 钩子
    db.AddQueryHook(bunotel.NewQueryHook(
        bunotel.WithDBName("mydb"),
        bunotel.WithFormattedQueries(true),  // 格式化 SQL 用于调试
        bunotel.WithAttributes(
            semconv.DBSystemPostgreSQL,
        ),
    ))

    return db
}

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 初始化数据库
    db := initDB()
    defer db.Close()

    ctx := context.Background()

    // 创建表
    _, err = db.NewCreateTable().
        Model((*User)(nil)).
        IfNotExists().
        Exec(ctx)
    if err != nil {
        log.Fatal(err)
    }

    // 插入用户
    user := &User{
        Username: "john",
        Email:    "john@example.com",
        Age:      30,
    }

    _, err = db.NewInsert().
        Model(user).
        Exec(ctx)
    if err != nil {
        log.Fatal(err)
    }

    log.Printf("Created user: %+v\n", user)

    // 查询用户
    var users []User
    err = db.NewSelect().
        Model(&users).
        Where("age > ?", 18).
        Order("created_at DESC").
        Scan(ctx)
    if err != nil {
        log.Fatal(err)
    }

    log.Printf("Found %d users\n", len(users))
}
```

---

## 3. 完整集成示例

### 3.1 完整的 Repository 模式

```go
package repository

import (
    "context"
    "fmt"
    "time"

    "github.com/uptrace/bun"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// User 模型
type User struct {
    bun.BaseModel `bun:"table:users,alias:u"`

    ID        int64     `bun:"id,pk,autoincrement"`
    Username  string    `bun:"username,notnull"`
    Email     string    `bun:"email,notnull,unique"`
    Age       int       `bun:"age"`
    Status    string    `bun:"status,default:'active'"`
    CreatedAt time.Time `bun:"created_at,notnull,default:current_timestamp"`
    UpdatedAt time.Time `bun:"updated_at,notnull,default:current_timestamp"`
    
    // 关联
    Posts []Post `bun:"rel:has-many,join:id=user_id"`
}

// Post 模型
type Post struct {
    bun.BaseModel `bun:"table:posts,alias:p"`

    ID        int64     `bun:"id,pk,autoincrement"`
    UserID    int64     `bun:"user_id,notnull"`
    Title     string    `bun:"title,notnull"`
    Content   string    `bun:"content"`
    Published bool      `bun:"published,default:false"`
    CreatedAt time.Time `bun:"created_at,notnull,default:current_timestamp"`
    UpdatedAt time.Time `bun:"updated_at,notnull,default:current_timestamp"`
    
    // 关联
    User *User `bun:"rel:belongs-to,join:user_id=id"`
}

// UserRepository 用户仓库
type UserRepository struct {
    db     *bun.DB
    tracer trace.Tracer
}

func NewUserRepository(db *bun.DB) *UserRepository {
    return &UserRepository{
        db:     db,
        tracer: otel.Tracer("user-repository"),
    }
}

// Create 创建用户
func (r *UserRepository) Create(ctx context.Context, user *User) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Create",
        trace.WithAttributes(
            attribute.String("user.username", user.Username),
            attribute.String("user.email", user.Email),
        ),
    )
    defer span.End()

    _, err := r.db.NewInsert().
        Model(user).
        Exec(ctx)

    if err != nil {
        span.RecordError(err)
        return fmt.Errorf("failed to create user: %w", err)
    }

    span.SetAttributes(attribute.Int64("user.id", user.ID))
    return nil
}

// FindByID 根据ID查询
func (r *UserRepository) FindByID(ctx context.Context, id int64) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.FindByID",
        trace.WithAttributes(
            attribute.Int64("user.id", id),
        ),
    )
    defer span.End()

    user := new(User)
    err := r.db.NewSelect().
        Model(user).
        Where("id = ?", id).
        Scan(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, fmt.Errorf("failed to find user: %w", err)
    }

    return user, nil
}

// FindByEmail 根据邮箱查询
func (r *UserRepository) FindByEmail(ctx context.Context, email string) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.FindByEmail",
        trace.WithAttributes(
            attribute.String("user.email", email),
        ),
    )
    defer span.End()

    user := new(User)
    err := r.db.NewSelect().
        Model(user).
        Where("email = ?", email).
        Scan(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, fmt.Errorf("failed to find user by email: %w", err)
    }

    return user, nil
}

// List 列出用户（分页）
func (r *UserRepository) List(ctx context.Context, limit, offset int) ([]*User, int, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.List",
        trace.WithAttributes(
            attribute.Int("limit", limit),
            attribute.Int("offset", offset),
        ),
    )
    defer span.End()

    var users []*User
    
    // 查询总数
    count, err := r.db.NewSelect().
        Model(&users).
        Count(ctx)
    if err != nil {
        span.RecordError(err)
        return nil, 0, fmt.Errorf("failed to count users: %w", err)
    }

    // 查询数据
    err = r.db.NewSelect().
        Model(&users).
        Order("created_at DESC").
        Limit(limit).
        Offset(offset).
        Scan(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, 0, fmt.Errorf("failed to list users: %w", err)
    }

    span.SetAttributes(
        attribute.Int("users.count", len(users)),
        attribute.Int("users.total", count),
    )

    return users, count, nil
}

// Update 更新用户
func (r *UserRepository) Update(ctx context.Context, user *User) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Update",
        trace.WithAttributes(
            attribute.Int64("user.id", user.ID),
        ),
    )
    defer span.End()

    user.UpdatedAt = time.Now()

    result, err := r.db.NewUpdate().
        Model(user).
        WherePK().
        Exec(ctx)

    if err != nil {
        span.RecordError(err)
        return fmt.Errorf("failed to update user: %w", err)
    }

    rowsAffected, _ := result.RowsAffected()
    span.SetAttributes(attribute.Int64("rows.affected", rowsAffected))

    return nil
}

// Delete 删除用户
func (r *UserRepository) Delete(ctx context.Context, id int64) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Delete",
        trace.WithAttributes(
            attribute.Int64("user.id", id),
        ),
    )
    defer span.End()

    result, err := r.db.NewDelete().
        Model((*User)(nil)).
        Where("id = ?", id).
        Exec(ctx)

    if err != nil {
        span.RecordError(err)
        return fmt.Errorf("failed to delete user: %w", err)
    }

    rowsAffected, _ := result.RowsAffected()
    span.SetAttributes(attribute.Int64("rows.affected", rowsAffected))

    return nil
}

// FindWithPosts 查询用户及其文章（关联查询）
func (r *UserRepository) FindWithPosts(ctx context.Context, userID int64) (*User, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.FindWithPosts",
        trace.WithAttributes(
            attribute.Int64("user.id", userID),
        ),
    )
    defer span.End()

    user := new(User)
    err := r.db.NewSelect().
        Model(user).
        Relation("Posts").
        Where("u.id = ?", userID).
        Scan(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, fmt.Errorf("failed to find user with posts: %w", err)
    }

    span.SetAttributes(attribute.Int("posts.count", len(user.Posts)))

    return user, nil
}

// BatchCreate 批量创建
func (r *UserRepository) BatchCreate(ctx context.Context, users []*User) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.BatchCreate",
        trace.WithAttributes(
            attribute.Int("users.count", len(users)),
        ),
    )
    defer span.End()

    _, err := r.db.NewInsert().
        Model(&users).
        Exec(ctx)

    if err != nil {
        span.RecordError(err)
        return fmt.Errorf("failed to batch create users: %w", err)
    }

    return nil
}

// SearchByUsername 按用户名搜索
func (r *UserRepository) SearchByUsername(ctx context.Context, query string, limit int) ([]*User, error) {
    ctx, span := r.tracer.Start(ctx, "UserRepository.SearchByUsername",
        trace.WithAttributes(
            attribute.String("search.query", query),
            attribute.Int("limit", limit),
        ),
    )
    defer span.End()

    var users []*User
    err := r.db.NewSelect().
        Model(&users).
        Where("username ILIKE ?", "%"+query+"%").
        Limit(limit).
        Scan(ctx)

    if err != nil {
        span.RecordError(err)
        return nil, fmt.Errorf("failed to search users: %w", err)
    }

    span.SetAttributes(attribute.Int("users.found", len(users)))

    return users, nil
}
```

### 3.2 事务处理

```go
package service

import (
    "context"
    "database/sql"
    "fmt"

    "github.com/uptrace/bun"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// UserService 用户服务
type UserService struct {
    db         *bun.DB
    userRepo   *UserRepository
    postRepo   *PostRepository
    tracer     trace.Tracer
}

func NewUserService(db *bun.DB) *UserService {
    return &UserService{
        db:       db,
        userRepo: NewUserRepository(db),
        postRepo: NewPostRepository(db),
        tracer:   otel.Tracer("user-service"),
    }
}

// CreateUserWithPost 创建用户并发布文章（事务）
func (s *UserService) CreateUserWithPost(ctx context.Context, user *User, post *Post) error {
    ctx, span := s.tracer.Start(ctx, "UserService.CreateUserWithPost",
        trace.WithAttributes(
            attribute.String("user.username", user.Username),
            attribute.String("post.title", post.Title),
        ),
    )
    defer span.End()

    // 开启事务
    err := s.db.RunInTx(ctx, &sql.TxOptions{}, func(ctx context.Context, tx bun.Tx) error {
        // 创建用户
        if err := s.userRepo.Create(ctx, user); err != nil {
            return fmt.Errorf("failed to create user: %w", err)
        }

        // 设置文章的用户ID
        post.UserID = user.ID

        // 创建文章
        if err := s.postRepo.Create(ctx, post); err != nil {
            return fmt.Errorf("failed to create post: %w", err)
        }

        return nil
    })

    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(
        attribute.Int64("user.id", user.ID),
        attribute.Int64("post.id", post.ID),
    )

    return nil
}

// TransferPosts 转移文章（从一个用户到另一个用户）
func (s *UserService) TransferPosts(ctx context.Context, fromUserID, toUserID int64) error {
    ctx, span := s.tracer.Start(ctx, "UserService.TransferPosts",
        trace.WithAttributes(
            attribute.Int64("from.user.id", fromUserID),
            attribute.Int64("to.user.id", toUserID),
        ),
    )
    defer span.End()

    err := s.db.RunInTx(ctx, &sql.TxOptions{}, func(ctx context.Context, tx bun.Tx) error {
        // 验证目标用户存在
        _, err := s.userRepo.FindByID(ctx, toUserID)
        if err != nil {
            return fmt.Errorf("target user not found: %w", err)
        }

        // 更新所有文章的所有者
        result, err := tx.NewUpdate().
            Model((*Post)(nil)).
            Set("user_id = ?", toUserID).
            Set("updated_at = ?", time.Now()).
            Where("user_id = ?", fromUserID).
            Exec(ctx)

        if err != nil {
            return fmt.Errorf("failed to transfer posts: %w", err)
        }

        rowsAffected, _ := result.RowsAffected()
        span.SetAttributes(attribute.Int64("posts.transferred", rowsAffected))

        return nil
    })

    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}
```

---

## 4. 高级特性

### 4.1 复杂查询

```go
package query

import (
    "context"
    "github.com/uptrace/bun"
)

// 子查询
func SubqueryExample(ctx context.Context, db *bun.DB) ([]*User, error) {
    // 查询发布过文章的用户
    subquery := db.NewSelect().
        Model((*Post)(nil)).
        Column("user_id").
        Where("published = ?", true).
        Group("user_id")

    var users []*User
    err := db.NewSelect().
        Model(&users).
        Where("id IN (?)", subquery).
        Scan(ctx)

    return users, err
}

// 联表查询
func JoinExample(ctx context.Context, db *bun.DB) ([]*User, error) {
    var users []*User
    err := db.NewSelect().
        Model(&users).
        ColumnExpr("u.*").
        ColumnExpr("COUNT(p.id) AS post_count").
        Join("LEFT JOIN posts AS p ON p.user_id = u.id").
        Group("u.id").
        Having("COUNT(p.id) > ?", 5).
        Scan(ctx)

    return users, err
}

// CTE (Common Table Expression)
func CTEExample(ctx context.Context, db *bun.DB) ([]*User, error) {
    var users []*User
    err := db.NewSelect().
        With("active_users", db.NewSelect().
            Model((*User)(nil)).
            Where("status = ?", "active")).
        Model(&users).
        TableExpr("active_users AS u").
        Scan(ctx)

    return users, err
}

// 聚合查询
func AggregateExample(ctx context.Context, db *bun.DB) (map[string]interface{}, error) {
    var result struct {
        TotalUsers  int     `bun:"total_users"`
        AvgAge      float64 `bun:"avg_age"`
        MaxAge      int     `bun:"max_age"`
        MinAge      int     `bun:"min_age"`
    }

    err := db.NewSelect().
        Model((*User)(nil)).
        ColumnExpr("COUNT(*) AS total_users").
        ColumnExpr("AVG(age) AS avg_age").
        ColumnExpr("MAX(age) AS max_age").
        ColumnExpr("MIN(age) AS min_age").
        Scan(ctx, &result)

    if err != nil {
        return nil, err
    }

    return map[string]interface{}{
        "total_users": result.TotalUsers,
        "avg_age":     result.AvgAge,
        "max_age":     result.MaxAge,
        "min_age":     result.MinAge,
    }, nil
}
```

### 4.2 软删除

```go
package models

import (
    "context"
    "time"

    "github.com/uptrace/bun"
)

// User 带软删除
type User struct {
    bun.BaseModel `bun:"table:users,alias:u"`

    ID        int64      `bun:"id,pk,autoincrement"`
    Username  string     `bun:"username,notnull"`
    Email     string     `bun:"email,notnull,unique"`
    DeletedAt *time.Time `bun:"deleted_at,soft_delete,nullzero"`
}

// SoftDelete 软删除
func (r *UserRepository) SoftDelete(ctx context.Context, id int64) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.SoftDelete")
    defer span.End()

    now := time.Now()
    _, err := r.db.NewUpdate().
        Model((*User)(nil)).
        Set("deleted_at = ?", now).
        Where("id = ?", id).
        Where("deleted_at IS NULL").
        Exec(ctx)

    return err
}

// Restore 恢复软删除
func (r *UserRepository) Restore(ctx context.Context, id int64) error {
    ctx, span := r.tracer.Start(ctx, "UserRepository.Restore")
    defer span.End()

    _, err := r.db.NewUpdate().
        Model((*User)(nil)).
        Set("deleted_at = NULL").
        Where("id = ?", id).
        Exec(ctx)

    return err
}

// FindIncludingDeleted 查询包括已删除的记录
func (r *UserRepository) FindIncludingDeleted(ctx context.Context, id int64) (*User, error) {
    user := new(User)
    err := r.db.NewSelect().
        Model(user).
        Where("id = ?", id).
        WhereAllWithDeleted().
        Scan(ctx)

    return user, err
}
```

---

## 5. 性能优化

### 5.1 连接池配置

```go
package database

import (
    "database/sql"
    "time"

    "github.com/uptrace/bun"
    "github.com/uptrace/bun/dialect/pgdialect"
    "github.com/uptrace/bun/driver/pgdriver"
)

func NewOptimizedDB(dsn string) *bun.DB {
    connector := pgdriver.NewConnector(
        pgdriver.WithDSN(dsn),
        pgdriver.WithTimeout(5*time.Second),
        pgdriver.WithDialTimeout(5*time.Second),
        pgdriver.WithReadTimeout(10*time.Second),
        pgdriver.WithWriteTimeout(10*time.Second),
    )

    sqldb := sql.OpenDB(connector)

    // 连接池配置
    sqldb.SetMaxOpenConns(25)                 // 最大打开连接数
    sqldb.SetMaxIdleConns(10)                 // 最大空闲连接数
    sqldb.SetConnMaxLifetime(5 * time.Minute) // 连接最大生命周期
    sqldb.SetConnMaxIdleTime(10 * time.Minute)// 空闲连接最大生命周期

    db := bun.NewDB(sqldb, pgdialect.New())

    // 添加查询钩子
    db.AddQueryHook(bunotel.NewQueryHook())

    return db
}
```

### 5.2 批量操作

```go
// 批量插入
func BatchInsertExample(ctx context.Context, db *bun.DB, users []*User) error {
    // 方式1: 简单批量插入
    _, err := db.NewInsert().
        Model(&users).
        Exec(ctx)

    return err
}

// 批量更新
func BatchUpdateExample(ctx context.Context, db *bun.DB, users []*User) error {
    _, err := db.NewUpdate().
        Model(&users).
        Bulk().
        Exec(ctx)

    return err
}

// 分块处理大批量数据
func ChunkedBatchInsert(ctx context.Context, db *bun.DB, users []*User, chunkSize int) error {
    for i := 0; i < len(users); i += chunkSize {
        end := i + chunkSize
        if end > len(users) {
            end = len(users)
        }

        chunk := users[i:end]
        _, err := db.NewInsert().
            Model(&chunk).
            Exec(ctx)

        if err != nil {
            return err
        }
    }

    return nil
}
```

### 5.3 查询优化

```go
// 选择特定列
func SelectSpecificColumns(ctx context.Context, db *bun.DB) ([]*User, error) {
    var users []*User
    err := db.NewSelect().
        Model(&users).
        Column("id", "username", "email").  // 只查询需要的列
        Scan(ctx)

    return users, err
}

// 使用索引
func UseIndex(ctx context.Context, db *bun.DB) ([]*User, error) {
    var users []*User
    err := db.NewSelect().
        Model(&users).
        ForceIndex("idx_username").  // 强制使用索引
        Where("username LIKE ?", "john%").
        Scan(ctx)

    return users, err
}

// 预加载关联
func EagerLoading(ctx context.Context, db *bun.DB) ([]*User, error) {
    var users []*User
    err := db.NewSelect().
        Model(&users).
        Relation("Posts").  // 预加载文章
        Scan(ctx)

    return users, err
}
```

---

## 6. 生产部署

### 6.1 数据库迁移

```go
package migrations

import (
    "context"
    "fmt"

    "github.com/uptrace/bun"
    "github.com/uptrace/bun/migrate"
)

var Migrations = migrate.NewMigrations()

func init() {
    // 注册迁移
    Migrations.MustRegister(func(ctx context.Context, db *bun.DB) error {
        // 创建用户表
        _, err := db.ExecContext(ctx, `
            CREATE TABLE IF NOT EXISTS users (
                id BIGSERIAL PRIMARY KEY,
                username VARCHAR(255) NOT NULL,
                email VARCHAR(255) NOT NULL UNIQUE,
                age INTEGER,
                status VARCHAR(50) DEFAULT 'active',
                created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                deleted_at TIMESTAMP
            )
        `)
        return err
    }, func(ctx context.Context, db *bun.DB) error {
        // 回滚：删除用户表
        _, err := db.ExecContext(ctx, `DROP TABLE IF EXISTS users`)
        return err
    })

    Migrations.MustRegister(func(ctx context.Context, db *bun.DB) error {
        // 创建文章表
        _, err := db.ExecContext(ctx, `
            CREATE TABLE IF NOT EXISTS posts (
                id BIGSERIAL PRIMARY KEY,
                user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                title VARCHAR(500) NOT NULL,
                content TEXT,
                published BOOLEAN DEFAULT FALSE,
                created_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP
            )
        `)
        return err
    }, func(ctx context.Context, db *bun.DB) error {
        _, err := db.ExecContext(ctx, `DROP TABLE IF EXISTS posts`)
        return err
    })

    // 添加索引
    Migrations.MustRegister(func(ctx context.Context, db *bun.DB) error {
        _, err := db.ExecContext(ctx, `
            CREATE INDEX IF NOT EXISTS idx_users_username ON users(username);
            CREATE INDEX IF NOT EXISTS idx_users_email ON users(email);
            CREATE INDEX IF NOT EXISTS idx_posts_user_id ON posts(user_id);
            CREATE INDEX IF NOT EXISTS idx_posts_published ON posts(published);
        `)
        return err
    }, func(ctx context.Context, db *bun.DB) error {
        _, err := db.ExecContext(ctx, `
            DROP INDEX IF EXISTS idx_users_username;
            DROP INDEX IF EXISTS idx_users_email;
            DROP INDEX IF EXISTS idx_posts_user_id;
            DROP INDEX IF EXISTS idx_posts_published;
        `)
        return err
    })
}

// RunMigrations 执行迁移
func RunMigrations(ctx context.Context, db *bun.DB) error {
    migrator := migrate.NewMigrator(db, Migrations)

    // 初始化迁移表
    if err := migrator.Init(ctx); err != nil {
        return fmt.Errorf("failed to init migrator: %w", err)
    }

    // 执行迁移
    group, err := migrator.Migrate(ctx)
    if err != nil {
        return fmt.Errorf("failed to migrate: %w", err)
    }

    if group.IsZero() {
        fmt.Println("No new migrations to run")
    } else {
        fmt.Printf("Migrated to %s\n", group)
    }

    return nil
}
```

### 6.2 健康检查

```go
package health

import (
    "context"
    "time"

    "github.com/uptrace/bun"
)

// CheckDatabase 数据库健康检查
func CheckDatabase(ctx context.Context, db *bun.DB) error {
    ctx, cancel := context.WithTimeout(ctx, 2*time.Second)
    defer cancel()

    // 执行简单查询
    var result int
    err := db.NewSelect().
        ColumnExpr("1").
        Scan(ctx, &result)

    return err
}

// GetDatabaseStats 获取数据库统计信息
func GetDatabaseStats(db *bun.DB) map[string]interface{} {
    stats := db.DB.Stats()

    return map[string]interface{}{
        "max_open_connections": stats.MaxOpenConnections,
        "open_connections":     stats.OpenConnections,
        "in_use":               stats.InUse,
        "idle":                 stats.Idle,
        "wait_count":           stats.WaitCount,
        "wait_duration":        stats.WaitDuration.Seconds(),
        "max_idle_closed":      stats.MaxIdleClosed,
        "max_idle_time_closed": stats.MaxIdleTimeClosed,
        "max_lifetime_closed":  stats.MaxLifetimeClosed,
    }
}
```

---

## 7. 最佳实践

### 7.1 性能优化清单

```text
✅ 连接池:
  - MaxOpenConns: 25-100
  - MaxIdleConns: 10-25
  - ConnMaxLifetime: 5min
  - ConnMaxIdleTime: 10min

✅ 查询优化:
  - 只查询需要的列
  - 使用适当的索引
  - 批量操作使用 Bulk()
  - 避免 N+1 查询

✅ 事务:
  - 保持事务简短
  - 使用适当的隔离级别
  - 正确处理错误和回滚

✅ 缓存:
  - 缓存频繁查询的数据
  - 使用Redis等外部缓存
  - 设置合理的过期时间
```

### 7.2 安全建议

```text
✅ SQL 注入防护:
  - 始终使用参数化查询
  - 不要拼接SQL字符串
  - 验证所有输入

✅ 连接安全:
  - 使用 TLS/SSL 连接
  - 限制数据库权限
  - 不在代码中硬编码密码

✅ 数据保护:
  - 敏感字段加密
  - 实现审计日志
  - 定期备份
```

---

**参考资源**：

- [Bun官方文档](https://bun.uptrace.dev/)
- [Bun GitHub](https://github.com/uptrace/bun)
- [PostgreSQL文档](https://www.postgresql.org/docs/)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

---

**下一步**：

- 实现数据库分片
- 添加读写分离
- 实现缓存策略
- 优化复杂查询


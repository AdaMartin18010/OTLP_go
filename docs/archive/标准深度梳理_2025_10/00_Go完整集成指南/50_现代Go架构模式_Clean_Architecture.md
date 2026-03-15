# 50. 现代 Go 架构模式 - Clean Architecture

## 📚 目录

- [1. Clean Architecture 概述](#1-clean-architecture-概述)
- [2. 分层架构设计](#2-分层架构设计)
- [3. 依赖注入模式](#3-依赖注入模式)
- [4. Repository 模式](#4-repository-模式)
- [5. Use Case 模式](#5-use-case-模式)
- [6. Domain-Driven Design](#6-domain-driven-design)
- [7. CQRS 模式](#7-cqrs-模式)
- [8. 完整实战案例](#8-完整实战案例)
- [9. 总结](#9-总结)

---

## 1. Clean Architecture 概述

### 1.1 什么是 Clean Architecture

Clean Architecture（整洁架构）是由 Robert C. Martin（Uncle Bob）提出的软件架构模式，核心思想是：

- **依赖规则**: 源码依赖只能指向内层
- **独立性**: 业务规则不依赖外部框架
- **可测试性**: 业务逻辑可以独立测试
- **灵活性**: 易于替换外部依赖

### 1.2 架构分层

```text
┌─────────────────────────────────────────────┐
│          Frameworks & Drivers              │  ← 最外层
│  (HTTP, gRPC, Database, External Services) │
├─────────────────────────────────────────────┤
│        Interface Adapters                  │
│    (Controllers, Presenters, Gateways)     │
├─────────────────────────────────────────────┤
│         Application Business Rules         │
│           (Use Cases)                      │
├─────────────────────────────────────────────┤
│      Enterprise Business Rules             │  ← 最内层
│           (Entities, Domain)               │
└─────────────────────────────────────────────┘
```

---

## 2. 分层架构设计

### 2.1 项目结构

```text
project/
├── cmd/
│   └── server/
│       └── main.go                 # 应用入口
├── internal/
│   ├── domain/                     # 领域层（最内层）
│   │   ├── entity/
│   │   │   └── user.go
│   │   ├── repository/
│   │   │   └── user_repository.go  # 接口定义
│   │   └── value/
│   │       └── email.go
│   │
│   ├── usecase/                    # 用例层
│   │   ├── user/
│   │   │   ├── create_user.go
│   │   │   ├── get_user.go
│   │   │   └── list_users.go
│   │   └── interface.go            # 用例接口
│   │
│   ├── adapter/                    # 适配器层
│   │   ├── controller/
│   │   │   └── user_controller.go
│   │   ├── presenter/
│   │   │   └── user_presenter.go
│   │   └── repository/
│   │       └── postgres/
│   │           └── user_repository.go  # 实现
│   │
│   └── infrastructure/             # 基础设施层（最外层）
│       ├── config/
│       │   └── config.go
│       ├── database/
│       │   └── postgres.go
│       ├── http/
│       │   └── server.go
│       └── telemetry/
│           └── otlp.go
│
├── pkg/                            # 公共包
│   ├── logger/
│   ├── errors/
│   └── validation/
│
└── go.mod
```

### 2.2 依赖版本

```go
// go.mod
module github.com/yourorg/clean-arch-service

go 1.25.1

require (
    // 路由
    github.com/go-chi/chi/v5 v5.1.0
    
    // 数据库
    gorm.io/gorm v1.25.12
    gorm.io/driver/postgres v1.5.11
    
    // OTLP
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.32.0
    
    // 依赖注入
    go.uber.org/fx v1.23.0
    
    // 配置
    github.com/spf13/viper v1.19.0
    
    // 验证
    github.com/go-playground/validator/v10 v10.23.0
    
    // UUID
    github.com/google/uuid v1.6.0
)
```

---

## 3. 依赖注入模式

### 3.1 使用 Uber Fx

```go
// cmd/server/main.go
package main

import (
    "context"
    "log"
    
    "go.uber.org/fx"
    "go.uber.org/fx/fxevent"
    "go.uber.org/zap"
    
    "github.com/yourorg/clean-arch-service/internal/adapter/controller"
    "github.com/yourorg/clean-arch-service/internal/adapter/repository/postgres"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/config"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/database"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/http"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/telemetry"
    "github.com/yourorg/clean-arch-service/internal/usecase/user"
)

func main() {
    app := fx.New(
        // 提供日志
        fx.Provide(NewLogger),
        
        // 提供配置
        fx.Provide(config.New),
        
        // 提供数据库连接
        fx.Provide(database.NewPostgresDB),
        
        // 提供 OTLP
        fx.Provide(telemetry.NewTracerProvider),
        fx.Provide(telemetry.NewTracer),
        
        // 提供 Repository
        fx.Provide(postgres.NewUserRepository),
        
        // 提供 Use Case
        fx.Provide(user.NewCreateUserUseCase),
        fx.Provide(user.NewGetUserUseCase),
        fx.Provide(user.NewListUsersUseCase),
        
        // 提供 Controller
        fx.Provide(controller.NewUserController),
        
        // 提供 HTTP 服务器
        fx.Provide(http.NewServer),
        
        // 启动服务器
        fx.Invoke(func(server *http.Server) {
            // 服务器将在 fx 管理的生命周期中启动
        }),
        
        // 配置日志
        fx.WithLogger(func(log *zap.Logger) fxevent.Logger {
            return &fxevent.ZapLogger{Logger: log}
        }),
    )
    
    app.Run()
}

// NewLogger 创建日志器
func NewLogger() (*zap.Logger, error) {
    return zap.NewProduction()
}
```

### 3.2 手动依赖注入

```go
// cmd/server/main.go (手动 DI)
package main

import (
    "context"
    "log"
    
    "github.com/yourorg/clean-arch-service/internal/adapter/controller"
    "github.com/yourorg/clean-arch-service/internal/adapter/repository/postgres"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/config"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/database"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/http"
    "github.com/yourorg/clean-arch-service/internal/infrastructure/telemetry"
    "github.com/yourorg/clean-arch-service/internal/usecase/user"
)

func main() {
    ctx := context.Background()
    
    // 1. 加载配置
    cfg, err := config.New()
    if err != nil {
        log.Fatal(err)
    }
    
    // 2. 初始化 OTLP
    tp, err := telemetry.NewTracerProvider(ctx, cfg)
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(ctx)
    
    tracer := telemetry.NewTracer(tp)
    
    // 3. 初始化数据库
    db, err := database.NewPostgresDB(cfg)
    if err != nil {
        log.Fatal(err)
    }
    
    // 4. 初始化 Repository
    userRepo := postgres.NewUserRepository(db, tracer)
    
    // 5. 初始化 Use Case
    createUserUC := user.NewCreateUserUseCase(userRepo, tracer)
    getUserUC := user.NewGetUserUseCase(userRepo, tracer)
    listUsersUC := user.NewListUsersUseCase(userRepo, tracer)
    
    // 6. 初始化 Controller
    userController := controller.NewUserController(
        createUserUC,
        getUserUC,
        listUsersUC,
        tracer,
    )
    
    // 7. 启动 HTTP 服务器
    server := http.NewServer(cfg, userController, tracer)
    
    if err := server.Run(); err != nil {
        log.Fatal(err)
    }
}
```

---

## 4. Repository 模式

### 4.1 Domain 层接口定义

```go
// internal/domain/repository/user_repository.go
package repository

import (
    "context"
    
    "github.com/google/uuid"
    "github.com/yourorg/clean-arch-service/internal/domain/entity"
)

// UserRepository 用户仓储接口（在 Domain 层定义）
type UserRepository interface {
    // Create 创建用户
    Create(ctx context.Context, user *entity.User) error
    
    // GetByID 根据 ID 获取用户
    GetByID(ctx context.Context, id uuid.UUID) (*entity.User, error)
    
    // GetByEmail 根据邮箱获取用户
    GetByEmail(ctx context.Context, email string) (*entity.User, error)
    
    // List 列出用户
    List(ctx context.Context, limit, offset int) ([]*entity.User, error)
    
    // Update 更新用户
    Update(ctx context.Context, user *entity.User) error
    
    // Delete 删除用户
    Delete(ctx context.Context, id uuid.UUID) error
}
```

### 4.2 Adapter 层实现

```go
// internal/adapter/repository/postgres/user_repository.go
package postgres

import (
    "context"
    "errors"
    
    "github.com/google/uuid"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
    "gorm.io/gorm"
    
    "github.com/yourorg/clean-arch-service/internal/domain/entity"
    "github.com/yourorg/clean-arch-service/internal/domain/repository"
)

// userRepository 用户仓储实现
type userRepository struct {
    db     *gorm.DB
    tracer trace.Tracer
}

// NewUserRepository 创建用户仓储
func NewUserRepository(db *gorm.DB, tracer trace.Tracer) repository.UserRepository {
    return &userRepository{
        db:     db,
        tracer: tracer,
    }
}

// Create 创建用户
func (r *userRepository) Create(ctx context.Context, user *entity.User) error {
    ctx, span := r.tracer.Start(ctx, "repository.user.create",
        trace.WithAttributes(
            attribute.String("user.email", user.Email),
        ),
    )
    defer span.End()
    
    // 转换为数据库模型
    dbUser := &UserModel{
        ID:        user.ID,
        Email:     user.Email,
        Username:  user.Username,
        Password:  user.Password,
        CreatedAt: user.CreatedAt,
        UpdatedAt: user.UpdatedAt,
    }
    
    if err := r.db.WithContext(ctx).Create(dbUser).Error; err != nil {
        span.RecordError(err)
        return err
    }
    
    return nil
}

// GetByID 根据 ID 获取用户
func (r *userRepository) GetByID(ctx context.Context, id uuid.UUID) (*entity.User, error) {
    ctx, span := r.tracer.Start(ctx, "repository.user.get_by_id",
        trace.WithAttributes(
            attribute.String("user.id", id.String()),
        ),
    )
    defer span.End()
    
    var dbUser UserModel
    if err := r.db.WithContext(ctx).Where("id = ?", id).First(&dbUser).Error; err != nil {
        if errors.Is(err, gorm.ErrRecordNotFound) {
            return nil, entity.ErrUserNotFound
        }
        span.RecordError(err)
        return nil, err
    }
    
    // 转换为领域实体
    return &entity.User{
        ID:        dbUser.ID,
        Email:     dbUser.Email,
        Username:  dbUser.Username,
        Password:  dbUser.Password,
        CreatedAt: dbUser.CreatedAt,
        UpdatedAt: dbUser.UpdatedAt,
    }, nil
}

// List 列出用户
func (r *userRepository) List(ctx context.Context, limit, offset int) ([]*entity.User, error) {
    ctx, span := r.tracer.Start(ctx, "repository.user.list",
        trace.WithAttributes(
            attribute.Int("limit", limit),
            attribute.Int("offset", offset),
        ),
    )
    defer span.End()
    
    var dbUsers []UserModel
    if err := r.db.WithContext(ctx).
        Limit(limit).
        Offset(offset).
        Order("created_at DESC").
        Find(&dbUsers).Error; err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    users := make([]*entity.User, len(dbUsers))
    for i, dbUser := range dbUsers {
        users[i] = &entity.User{
            ID:        dbUser.ID,
            Email:     dbUser.Email,
            Username:  dbUser.Username,
            CreatedAt: dbUser.CreatedAt,
            UpdatedAt: dbUser.UpdatedAt,
        }
    }
    
    return users, nil
}

// UserModel 数据库模型
type UserModel struct {
    ID        uuid.UUID `gorm:"type:uuid;primary_key"`
    Email     string    `gorm:"uniqueIndex;not null"`
    Username  string    `gorm:"uniqueIndex;not null"`
    Password  string    `gorm:"not null"`
    CreatedAt time.Time
    UpdatedAt time.Time
}

func (UserModel) TableName() string {
    return "users"
}
```

---

## 5. Use Case 模式

### 5.1 Use Case 定义

```go
// internal/usecase/user/create_user.go
package user

import (
    "context"
    "time"
    
    "github.com/google/uuid"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    "golang.org/x/crypto/bcrypt"
    
    "github.com/yourorg/clean-arch-service/internal/domain/entity"
    "github.com/yourorg/clean-arch-service/internal/domain/repository"
)

// CreateUserUseCase 创建用户用例
type CreateUserUseCase struct {
    userRepo repository.UserRepository
    tracer   trace.Tracer
}

// NewCreateUserUseCase 创建用例
func NewCreateUserUseCase(
    userRepo repository.UserRepository,
    tracer trace.Tracer,
) *CreateUserUseCase {
    return &CreateUserUseCase{
        userRepo: userRepo,
        tracer:   tracer,
    }
}

// CreateUserInput 输入
type CreateUserInput struct {
    Email    string
    Username string
    Password string
}

// CreateUserOutput 输出
type CreateUserOutput struct {
    ID        uuid.UUID
    Email     string
    Username  string
    CreatedAt time.Time
}

// Execute 执行用例
func (uc *CreateUserUseCase) Execute(ctx context.Context, input *CreateUserInput) (*CreateUserOutput, error) {
    ctx, span := uc.tracer.Start(ctx, "usecase.user.create",
        trace.WithAttributes(
            attribute.String("user.email", input.Email),
            attribute.String("user.username", input.Username),
        ),
    )
    defer span.End()
    
    // 1. 验证输入
    if err := uc.validateInput(input); err != nil {
        span.SetStatus(codes.Error, "validation failed")
        span.RecordError(err)
        return nil, err
    }
    
    // 2. 检查邮箱是否已存在
    existing, err := uc.userRepo.GetByEmail(ctx, input.Email)
    if err != nil && err != entity.ErrUserNotFound {
        span.RecordError(err)
        return nil, err
    }
    if existing != nil {
        return nil, entity.ErrEmailAlreadyExists
    }
    
    // 3. 加密密码
    hashedPassword, err := bcrypt.GenerateFromPassword([]byte(input.Password), bcrypt.DefaultCost)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    // 4. 创建用户实体
    user := &entity.User{
        ID:        uuid.New(),
        Email:     input.Email,
        Username:  input.Username,
        Password:  string(hashedPassword),
        CreatedAt: time.Now(),
        UpdatedAt: time.Now(),
    }
    
    // 5. 保存到数据库
    if err := uc.userRepo.Create(ctx, user); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "user created successfully")
    
    // 6. 返回输出
    return &CreateUserOutput{
        ID:        user.ID,
        Email:     user.Email,
        Username:  user.Username,
        CreatedAt: user.CreatedAt,
    }, nil
}

// validateInput 验证输入
func (uc *CreateUserUseCase) validateInput(input *CreateUserInput) error {
    if input.Email == "" {
        return entity.ErrInvalidEmail
    }
    if input.Username == "" {
        return entity.ErrInvalidUsername
    }
    if len(input.Password) < 8 {
        return entity.ErrPasswordTooShort
    }
    return nil
}
```

### 5.2 获取用户用例

```go
// internal/usecase/user/get_user.go
package user

import (
    "context"
    
    "github.com/google/uuid"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
    
    "github.com/yourorg/clean-arch-service/internal/domain/entity"
    "github.com/yourorg/clean-arch-service/internal/domain/repository"
)

// GetUserUseCase 获取用户用例
type GetUserUseCase struct {
    userRepo repository.UserRepository
    tracer   trace.Tracer
}

// NewGetUserUseCase 创建用例
func NewGetUserUseCase(
    userRepo repository.UserRepository,
    tracer trace.Tracer,
) *GetUserUseCase {
    return &GetUserUseCase{
        userRepo: userRepo,
        tracer:   tracer,
    }
}

// GetUserInput 输入
type GetUserInput struct {
    ID uuid.UUID
}

// GetUserOutput 输出
type GetUserOutput struct {
    ID       uuid.UUID
    Email    string
    Username string
}

// Execute 执行用例
func (uc *GetUserUseCase) Execute(ctx context.Context, input *GetUserInput) (*GetUserOutput, error) {
    ctx, span := uc.tracer.Start(ctx, "usecase.user.get",
        trace.WithAttributes(
            attribute.String("user.id", input.ID.String()),
        ),
    )
    defer span.End()
    
    user, err := uc.userRepo.GetByID(ctx, input.ID)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    return &GetUserOutput{
        ID:       user.ID,
        Email:    user.Email,
        Username: user.Username,
    }, nil
}
```

---

## 6. Domain-Driven Design

### 6.1 Entity 定义

```go
// internal/domain/entity/user.go
package entity

import (
    "errors"
    "time"
    
    "github.com/google/uuid"
)

// User 用户实体
type User struct {
    ID        uuid.UUID
    Email     string
    Username  string
    Password  string // 已加密
    CreatedAt time.Time
    UpdatedAt time.Time
}

// Validate 验证用户实体
func (u *User) Validate() error {
    if u.Email == "" {
        return ErrInvalidEmail
    }
    if u.Username == "" {
        return ErrInvalidUsername
    }
    return nil
}

// UpdateEmail 更新邮箱
func (u *User) UpdateEmail(email string) error {
    if email == "" {
        return ErrInvalidEmail
    }
    u.Email = email
    u.UpdatedAt = time.Now()
    return nil
}

// 领域错误
var (
    ErrUserNotFound        = errors.New("user not found")
    ErrInvalidEmail        = errors.New("invalid email")
    ErrInvalidUsername     = errors.New("invalid username")
    ErrPasswordTooShort    = errors.New("password too short")
    ErrEmailAlreadyExists  = errors.New("email already exists")
)
```

### 6.2 Value Object

```go
// internal/domain/value/email.go
package value

import (
    "errors"
    "regexp"
)

// Email 邮箱值对象
type Email struct {
    value string
}

var emailRegex = regexp.MustCompile(`^[a-z0-9._%+\-]+@[a-z0-9.\-]+\.[a-z]{2,4}$`)

// NewEmail 创建邮箱值对象
func NewEmail(email string) (*Email, error) {
    if !emailRegex.MatchString(email) {
        return nil, errors.New("invalid email format")
    }
    
    return &Email{value: email}, nil
}

// String 获取字符串值
func (e *Email) String() string {
    return e.value
}

// Equals 比较两个邮箱
func (e *Email) Equals(other *Email) bool {
    return e.value == other.value
}
```

---

## 7. CQRS 模式

### 7.1 命令（Command）

```go
// internal/usecase/user/command/create_user_command.go
package command

import (
    "context"
    
    "github.com/google/uuid"
    "go.opentelemetry.io/otel/trace"
    
    "github.com/yourorg/clean-arch-service/internal/domain/entity"
    "github.com/yourorg/clean-arch-service/internal/domain/repository"
)

// CreateUserCommand 创建用户命令
type CreateUserCommand struct {
    Email    string
    Username string
    Password string
}

// CreateUserCommandHandler 命令处理器
type CreateUserCommandHandler struct {
    userRepo repository.UserRepository
    tracer   trace.Tracer
}

// NewCreateUserCommandHandler 创建命令处理器
func NewCreateUserCommandHandler(
    userRepo repository.UserRepository,
    tracer trace.Tracer,
) *CreateUserCommandHandler {
    return &CreateUserCommandHandler{
        userRepo: userRepo,
        tracer:   tracer,
    }
}

// Handle 处理命令
func (h *CreateUserCommandHandler) Handle(ctx context.Context, cmd *CreateUserCommand) (uuid.UUID, error) {
    ctx, span := h.tracer.Start(ctx, "command.create_user")
    defer span.End()
    
    // 业务逻辑（写操作）
    user := &entity.User{
        ID:       uuid.New(),
        Email:    cmd.Email,
        Username: cmd.Username,
        Password: cmd.Password, // 应该已加密
    }
    
    if err := h.userRepo.Create(ctx, user); err != nil {
        span.RecordError(err)
        return uuid.Nil, err
    }
    
    return user.ID, nil
}
```

### 7.2 查询（Query）

```go
// internal/usecase/user/query/get_user_query.go
package query

import (
    "context"
    
    "github.com/google/uuid"
    "go.opentelemetry.io/otel/trace"
    
    "github.com/yourorg/clean-arch-service/internal/domain/repository"
)

// GetUserQuery 获取用户查询
type GetUserQuery struct {
    ID uuid.UUID
}

// UserDTO 用户 DTO
type UserDTO struct {
    ID       uuid.UUID `json:"id"`
    Email    string    `json:"email"`
    Username string    `json:"username"`
}

// GetUserQueryHandler 查询处理器
type GetUserQueryHandler struct {
    userRepo repository.UserRepository
    tracer   trace.Tracer
}

// NewGetUserQueryHandler 创建查询处理器
func NewGetUserQueryHandler(
    userRepo repository.UserRepository,
    tracer trace.Tracer,
) *GetUserQueryHandler {
    return &GetUserQueryHandler{
        userRepo: userRepo,
        tracer:   tracer,
    }
}

// Handle 处理查询
func (h *GetUserQueryHandler) Handle(ctx context.Context, query *GetUserQuery) (*UserDTO, error) {
    ctx, span := h.tracer.Start(ctx, "query.get_user")
    defer span.End()
    
    // 读取操作
    user, err := h.userRepo.GetByID(ctx, query.ID)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    return &UserDTO{
        ID:       user.ID,
        Email:    user.Email,
        Username: user.Username,
    }, nil
}
```

---

## 8. 完整实战案例

### 8.1 Controller 实现

```go
// internal/adapter/controller/user_controller.go
package controller

import (
    "encoding/json"
    "net/http"
    
    "github.com/go-chi/chi/v5"
    "github.com/google/uuid"
    "go.opentelemetry.io/otel/trace"
    
    "github.com/yourorg/clean-arch-service/internal/usecase/user"
)

// UserController 用户控制器
type UserController struct {
    createUserUC *user.CreateUserUseCase
    getUserUC    *user.GetUserUseCase
    listUsersUC  *user.ListUsersUseCase
    tracer       trace.Tracer
}

// NewUserController 创建控制器
func NewUserController(
    createUserUC *user.CreateUserUseCase,
    getUserUC *user.GetUserUseCase,
    listUsersUC *user.ListUsersUseCase,
    tracer trace.Tracer,
) *UserController {
    return &UserController{
        createUserUC: createUserUC,
        getUserUC:    getUserUC,
        listUsersUC:  listUsersUC,
        tracer:       tracer,
    }
}

// RegisterRoutes 注册路由
func (c *UserController) RegisterRoutes(r chi.Router) {
    r.Post("/users", c.CreateUser)
    r.Get("/users/{id}", c.GetUser)
    r.Get("/users", c.ListUsers)
}

// CreateUser 创建用户
func (c *UserController) CreateUser(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    ctx, span := c.tracer.Start(ctx, "controller.create_user")
    defer span.End()
    
    var req struct {
        Email    string `json:"email"`
        Username string `json:"username"`
        Password string `json:"password"`
    }
    
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        span.RecordError(err)
        http.Error(w, "Invalid request body", http.StatusBadRequest)
        return
    }
    
    output, err := c.createUserUC.Execute(ctx, &user.CreateUserInput{
        Email:    req.Email,
        Username: req.Username,
        Password: req.Password,
    })
    
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    w.Header().Set("Content-Type", "application/json")
    w.WriteHeader(http.StatusCreated)
    json.NewEncoder(w).Encode(output)
}

// GetUser 获取用户
func (c *UserController) GetUser(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    ctx, span := c.tracer.Start(ctx, "controller.get_user")
    defer span.End()
    
    idStr := chi.URLParam(r, "id")
    id, err := uuid.Parse(idStr)
    if err != nil {
        span.RecordError(err)
        http.Error(w, "Invalid user ID", http.StatusBadRequest)
        return
    }
    
    output, err := c.getUserUC.Execute(ctx, &user.GetUserInput{ID: id})
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusNotFound)
        return
    }
    
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(output)
}
```

---

## 9. 总结

### 核心优势

✅ **关注点分离** - 清晰的层次边界  
✅ **依赖倒置** - 业务规则不依赖外部  
✅ **可测试性** - 每层可独立测试  
✅ **灵活性** - 易于替换实现  
✅ **可维护性** - 结构清晰，易于理解

### 最佳实践

1. ✅ 严格遵守依赖规则
2. ✅ Domain 层只包含业务逻辑
3. ✅ Use Case 层编排业务流程
4. ✅ Repository 只定义接口
5. ✅ Controller 只处理 HTTP
6. ✅ 使用依赖注入
7. ✅ 集成 OTLP 追踪
8. ✅ 编写单元测试

### 相关文档

- [49_Chi框架深度集成与最佳实践](./49_Chi框架深度集成与最佳实践.md)
- [35_Go生产级部署模式与反模式](./35_Go生产级部署模式与反模式.md)
- [38_Go测试与可观测性最佳实践](./38_Go测试与可观测性最佳实践.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**Go 版本**: 1.25.1

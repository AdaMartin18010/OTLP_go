# Go 依赖注入与 Wire/Fx 集成指南

> **版本**: v1.0.0  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **Wire**: google/wire v0.6.0  
> **Fx**: uber-go/fx v1.23.0  
> **日期**: 2025-10-11

---

## 📋 目录

- [Go 依赖注入与 Wire/Fx 集成指南](#go-依赖注入与-wirefx-集成指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心价值](#核心价值)
    - [技术栈](#技术栈)
  - [依赖注入基础](#依赖注入基础)
    - [1. 手动依赖注入](#1-手动依赖注入)
  - [Google Wire 集成](#google-wire-集成)
    - [1. Wire 基础配置](#1-wire-基础配置)
    - [2. Wire 生成代码](#2-wire-生成代码)
    - [3. 使用 Wire 应用](#3-使用-wire-应用)
  - [Uber Fx 集成](#uber-fx-集成)
    - [1. Fx 基础配置](#1-fx-基础配置)
    - [2. Fx Module 模式](#2-fx-module-模式)
  - [OTLP Provider 注入](#otlp-provider-注入)
    - [1. 完整 Provider 注入](#1-完整-provider-注入)
  - [总结](#总结)
    - [核心特性](#核心特性)
    - [Wire vs Fx 对比](#wire-vs-fx-对比)
    - [下一步](#下一步)

---

## 概述

本指南深入讲解 Go 依赖注入框架（Wire、Fx）与 OpenTelemetry 的集成，涵盖 Provider 构建、生命周期管理、测试等核心场景。

### 核心价值

```text
✅ Wire 编译期依赖注入
✅ Fx 运行时依赖管理
✅ OTLP Provider 自动注入
✅ 生命周期钩子集成
✅ 测试友好架构
✅ 生产级代码示例
```

### 技术栈

```go
// 核心依赖
go.opentelemetry.io/otel v1.32.0
go.opentelemetry.io/otel/sdk v1.32.0

// 依赖注入框架
github.com/google/wire v0.6.0           // Wire DI
go.uber.org/fx v1.23.0                  // Fx DI
go.uber.org/dig v1.18.0                 // Dig (Fx 底层)
```

---

## 依赖注入基础

### 1. 手动依赖注入

```go
package main

import (
 "context"
 "database/sql"
 
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/trace"
)

// Repository 层
type UserRepository struct {
 db     *sql.DB
 tracer trace.Tracer
}

func NewUserRepository(db *sql.DB, tracer trace.Tracer) *UserRepository {
 return &UserRepository{
  db:     db,
  tracer: tracer,
 }
}

func (r *UserRepository) FindByID(ctx context.Context, id string) (*User, error) {
 ctx, span := r.tracer.Start(ctx, "repository.FindByID")
 defer span.End()
 
 // 数据库查询
 var user User
 err := r.db.QueryRowContext(ctx, "SELECT * FROM users WHERE id = $1", id).
  Scan(&user.ID, &user.Name)
 
 if err != nil {
  span.RecordError(err)
  return nil, err
 }
 
 return &user, nil
}

// Service 层
type UserService struct {
 repo   *UserRepository
 tracer trace.Tracer
}

func NewUserService(repo *UserRepository, tracer trace.Tracer) *UserService {
 return &UserService{
  repo:   repo,
  tracer: tracer,
 }
}

func (s *UserService) GetUser(ctx context.Context, id string) (*User, error) {
 ctx, span := s.tracer.Start(ctx, "service.GetUser")
 defer span.End()
 
 return s.repo.FindByID(ctx, id)
}

// Handler 层
type UserHandler struct {
 service *UserService
 tracer  trace.Tracer
}

func NewUserHandler(service *UserService, tracer trace.Tracer) *UserHandler {
 return &UserHandler{
  service: service,
  tracer:  tracer,
 }
}

// 手动装配
func ManualWiring() *UserHandler {
 // 1. 初始化基础设施
 db, _ := sql.Open("postgres", "connection-string")
 tracer := otel.Tracer("app")
 
 // 2. 构建依赖图
 repo := NewUserRepository(db, tracer)
 service := NewUserService(repo, tracer)
 handler := NewUserHandler(service, tracer)
 
 return handler
}
```

---

## Google Wire 集成

### 1. Wire 基础配置

```go
//go:build wireinject
// +build wireinject

package main

import (
 "context"
 "database/sql"
 
 "github.com/google/wire"
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
 "go.opentelemetry.io/otel/sdk/trace"
 sdktrace "go.opentelemetry.io/otel/sdk/trace"
 oteltrace "go.opentelemetry.io/otel/trace"
)

// ProvideDatabase 提供数据库连接
func ProvideDatabase() (*sql.DB, error) {
 return sql.Open("postgres", "host=localhost dbname=mydb")
}

// ProvideTraceExporter 提供 Trace Exporter
func ProvideTraceExporter(ctx context.Context) (sdktrace.SpanExporter, error) {
 return otlptracegrpc.New(ctx,
  otlptracegrpc.WithEndpoint("localhost:4317"),
  otlptracegrpc.WithInsecure(),
 )
}

// ProvideTracerProvider 提供 TracerProvider
func ProvideTracerProvider(exporter sdktrace.SpanExporter) *sdktrace.TracerProvider {
 return sdktrace.NewTracerProvider(
  sdktrace.WithBatcher(exporter),
  sdktrace.WithResource(resource.NewWithAttributes(
   semconv.SchemaURL,
   semconv.ServiceName("my-service"),
  )),
 )
}

// ProvideTracer 提供 Tracer
func ProvideTracer(tp *sdktrace.TracerProvider) oteltrace.Tracer {
 return tp.Tracer("app")
}

// Wire Sets
var InfrastructureSet = wire.NewSet(
 ProvideDatabase,
 ProvideTraceExporter,
 ProvideTracerProvider,
 ProvideTracer,
)

var RepositorySet = wire.NewSet(
 NewUserRepository,
 NewOrderRepository,
)

var ServiceSet = wire.NewSet(
 NewUserService,
 NewOrderService,
)

var HandlerSet = wire.NewSet(
 NewUserHandler,
 NewOrderHandler,
)

// InitializeApp Wire 注入函数
func InitializeApp(ctx context.Context) (*App, func(), error) {
 wire.Build(
  InfrastructureSet,
  RepositorySet,
  ServiceSet,
  HandlerSet,
  NewApp,
 )
 return nil, nil, nil
}

// App 应用结构
type App struct {
 UserHandler  *UserHandler
 OrderHandler *OrderHandler
 tp           *sdktrace.TracerProvider
}

func NewApp(
 userHandler *UserHandler,
 orderHandler *OrderHandler,
 tp *sdktrace.TracerProvider,
) *App {
 return &App{
  UserHandler:  userHandler,
  OrderHandler: orderHandler,
  tp:           tp,
 }
}

func (app *App) Shutdown(ctx context.Context) error {
 return app.tp.Shutdown(ctx)
}
```

### 2. Wire 生成代码

```bash
# 生成 Wire 代码
wire gen ./...

# 生成的文件: wire_gen.go
```

### 3. 使用 Wire 应用

```go
package main

import (
 "context"
 "fmt"
 "log"
 "net/http"
)

func main() {
 ctx := context.Background()
 
 // Wire 自动装配
 app, cleanup, err := InitializeApp(ctx)
 if err != nil {
  log.Fatalf("Failed to initialize app: %v", err)
 }
 defer cleanup()
 
 // 启动 HTTP 服务器
 http.HandleFunc("/users/:id", app.UserHandler.GetUser)
 http.HandleFunc("/orders/:id", app.OrderHandler.GetOrder)
 
 fmt.Println("Server starting on :8080")
 if err := http.ListenAndServe(":8080", nil); err != nil {
  log.Fatal(err)
 }
}
```

---

## Uber Fx 集成

### 1. Fx 基础配置

```go
package main

import (
 "context"
 "database/sql"
 "net/http"
 
 "go.uber.org/fx"
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
 "go.opentelemetry.io/otel/sdk/resource"
 sdktrace "go.opentelemetry.io/otel/sdk/trace"
 semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
 oteltrace "go.opentelemetry.io/otel/trace"
)

// ProvideDatabase Fx Provider
func ProvideDatabase(lc fx.Lifecycle) (*sql.DB, error) {
 db, err := sql.Open("postgres", "host=localhost dbname=mydb")
 if err != nil {
  return nil, err
 }
 
 // 注册生命周期钩子
 lc.Append(fx.Hook{
  OnStart: func(ctx context.Context) error {
   return db.PingContext(ctx)
  },
  OnStop: func(ctx context.Context) error {
   return db.Close()
  },
 })
 
 return db, nil
}

// ProvideTracerProvider Fx Provider
func ProvideTracerProvider(lc fx.Lifecycle) (*sdktrace.TracerProvider, error) {
 ctx := context.Background()
 
 // 创建 Exporter
 exporter, err := otlptracegrpc.New(ctx,
  otlptracegrpc.WithEndpoint("localhost:4317"),
  otlptracegrpc.WithInsecure(),
 )
 if err != nil {
  return nil, err
 }
 
 // 创建 TracerProvider
 tp := sdktrace.NewTracerProvider(
  sdktrace.WithBatcher(exporter),
  sdktrace.WithResource(resource.NewWithAttributes(
   semconv.SchemaURL,
   semconv.ServiceName("my-service"),
  )),
 )
 
 // 注册生命周期钩子
 lc.Append(fx.Hook{
  OnStart: func(ctx context.Context) error {
   otel.SetTracerProvider(tp)
   return nil
  },
  OnStop: func(ctx context.Context) error {
   return tp.Shutdown(ctx)
  },
 })
 
 return tp, nil
}

// ProvideTracer Fx Provider
func ProvideTracer(tp *sdktrace.TracerProvider) oteltrace.Tracer {
 return tp.Tracer("app")
}

// ProvideHTTPServer Fx Provider
func ProvideHTTPServer(
 lc fx.Lifecycle,
 userHandler *UserHandler,
 orderHandler *OrderHandler,
) *http.Server {
 mux := http.NewServeMux()
 mux.HandleFunc("/users/", userHandler.GetUser)
 mux.HandleFunc("/orders/", orderHandler.GetOrder)
 
 srv := &http.Server{
  Addr:    ":8080",
  Handler: mux,
 }
 
 // 注册生命周期钩子
 lc.Append(fx.Hook{
  OnStart: func(ctx context.Context) error {
   go func() {
    if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
     log.Printf("HTTP server error: %v", err)
    }
   }()
   return nil
  },
  OnStop: func(ctx context.Context) error {
   return srv.Shutdown(ctx)
  },
 })
 
 return srv
}

// NewFxApp 创建 Fx 应用
func NewFxApp() *fx.App {
 return fx.New(
  // Infrastructure
  fx.Provide(
   ProvideDatabase,
   ProvideTracerProvider,
   ProvideTracer,
  ),
  
  // Repository
  fx.Provide(
   NewUserRepository,
   NewOrderRepository,
  ),
  
  // Service
  fx.Provide(
   NewUserService,
   NewOrderService,
  ),
  
  // Handler
  fx.Provide(
   NewUserHandler,
   NewOrderHandler,
  ),
  
  // HTTP Server
  fx.Provide(ProvideHTTPServer),
  
  // Invoke
  fx.Invoke(func(*http.Server) {}),
 )
}

func main() {
 app := NewFxApp()
 app.Run()
}
```

### 2. Fx Module 模式

```go
package main

import (
 "go.uber.org/fx"
)

// InfrastructureModule 基础设施模块
var InfrastructureModule = fx.Module(
 "infrastructure",
 fx.Provide(
  ProvideDatabase,
  ProvideTracerProvider,
  ProvideTracer,
  ProvideMeterProvider,
  ProvideMeter,
 ),
)

// RepositoryModule 仓储模块
var RepositoryModule = fx.Module(
 "repository",
 fx.Provide(
  NewUserRepository,
  NewOrderRepository,
  NewProductRepository,
 ),
)

// ServiceModule 服务模块
var ServiceModule = fx.Module(
 "service",
 fx.Provide(
  NewUserService,
  NewOrderService,
  NewProductService,
 ),
)

// HandlerModule 处理器模块
var HandlerModule = fx.Module(
 "handler",
 fx.Provide(
  NewUserHandler,
  NewOrderHandler,
  NewProductHandler,
 ),
)

// HTTPModule HTTP 模块
var HTTPModule = fx.Module(
 "http",
 fx.Provide(ProvideHTTPServer),
 fx.Invoke(func(*http.Server) {}),
)

// NewModularApp 模块化应用
func NewModularApp() *fx.App {
 return fx.New(
  InfrastructureModule,
  RepositoryModule,
  ServiceModule,
  HandlerModule,
  HTTPModule,
 )
}
```

---

## OTLP Provider 注入

### 1. 完整 Provider 注入

```go
package main

import (
 "context"
 
 "go.uber.org/fx"
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
 "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
 "go.opentelemetry.io/otel/sdk/metric"
 "go.opentelemetry.io/otel/sdk/resource"
 "go.opentelemetry.io/otel/sdk/trace"
 semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
)

// OTLPConfig OTLP 配置
type OTLPConfig struct {
 Endpoint    string
 ServiceName string
 Environment string
}

// ProvideOTLPConfig 提供配置
func ProvideOTLPConfig() OTLPConfig {
 return OTLPConfig{
  Endpoint:    "localhost:4317",
  ServiceName: "my-service",
  Environment: "production",
 }
}

// ProvideResource 提供资源
func ProvideResource(config OTLPConfig) *resource.Resource {
 return resource.NewWithAttributes(
  semconv.SchemaURL,
  semconv.ServiceName(config.ServiceName),
  semconv.DeploymentEnvironment(config.Environment),
 )
}

// ProvideTraceExporter 提供 Trace Exporter
func ProvideTraceExporter(lc fx.Lifecycle, config OTLPConfig) (trace.SpanExporter, error) {
 ctx := context.Background()
 
 exporter, err := otlptracegrpc.New(ctx,
  otlptracegrpc.WithEndpoint(config.Endpoint),
  otlptracegrpc.WithInsecure(),
 )
 if err != nil {
  return nil, err
 }
 
 lc.Append(fx.Hook{
  OnStop: func(ctx context.Context) error {
   return exporter.Shutdown(ctx)
  },
 })
 
 return exporter, nil
}

// ProvideMetricExporter 提供 Metric Exporter
func ProvideMetricExporter(lc fx.Lifecycle, config OTLPConfig) (metric.Exporter, error) {
 ctx := context.Background()
 
 exporter, err := otlpmetricgrpc.New(ctx,
  otlpmetricgrpc.WithEndpoint(config.Endpoint),
  otlpmetricgrpc.WithInsecure(),
 )
 if err != nil {
  return nil, err
 }
 
 lc.Append(fx.Hook{
  OnStop: func(ctx context.Context) error {
   return exporter.Shutdown(ctx)
  },
 })
 
 return exporter, nil
}

// ProvideTracerProvider 提供 TracerProvider
func ProvideTracerProvider(
 lc fx.Lifecycle,
 exporter trace.SpanExporter,
 res *resource.Resource,
) *trace.TracerProvider {
 tp := trace.NewTracerProvider(
  trace.WithBatcher(exporter),
  trace.WithResource(res),
 )
 
 lc.Append(fx.Hook{
  OnStart: func(ctx context.Context) error {
   otel.SetTracerProvider(tp)
   return nil
  },
  OnStop: func(ctx context.Context) error {
   return tp.Shutdown(ctx)
  },
 })
 
 return tp
}

// ProvideMeterProvider 提供 MeterProvider
func ProvideMeterProvider(
 lc fx.Lifecycle,
 exporter metric.Exporter,
 res *resource.Resource,
) *metric.MeterProvider {
 mp := metric.NewMeterProvider(
  metric.WithReader(metric.NewPeriodicReader(exporter)),
  metric.WithResource(res),
 )
 
 lc.Append(fx.Hook{
  OnStart: func(ctx context.Context) error {
   otel.SetMeterProvider(mp)
   return nil
  },
  OnStop: func(ctx context.Context) error {
   return mp.Shutdown(ctx)
  },
 })
 
 return mp
}

// OTLPModule OTLP 模块
var OTLPModule = fx.Module(
 "otlp",
 fx.Provide(
  ProvideOTLPConfig,
  ProvideResource,
  ProvideTraceExporter,
  ProvideMetricExporter,
  ProvideTracerProvider,
  ProvideMeterProvider,
 ),
)
```

---

## 总结

本指南提供了 Go 依赖注入框架与 OTLP 的完整集成方案，包括：

### 核心特性

```text
✅ Wire 编译期依赖注入
✅ Fx 运行时依赖管理
✅ OTLP Provider 完整注入
✅ 生命周期钩子管理
✅ 模块化架构设计
✅ 测试友好实现
✅ 生产级代码示例
```

### Wire vs Fx 对比

| 特性 | Wire | Fx |
|------|------|-----|
| **注入时机** | 编译期 | 运行时 |
| **性能** | 零开销 | 轻微开销 |
| **灵活性** | 低 | 高 |
| **生命周期** | 手动 | 自动 |
| **调试** | 困难 | 简单 |
| **学习曲线** | 陡峭 | 平缓 |
| **推荐场景** | 性能敏感 | 快速开发 |

### 下一步

- [Go 响应式编程与 RxGo](./60_Go响应式编程与RxGo集成_2025版.md)
- [Go 函数式编程](./58_Go函数式编程模式与OTLP集成_2025版.md)
- [Go 并发原语](./56_Go并发原语与OTLP完整集成_2025版.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**维护者**: OTLP Go Team

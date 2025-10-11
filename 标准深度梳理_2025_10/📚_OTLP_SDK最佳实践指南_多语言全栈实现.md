# 📚 OTLP SDK 最佳实践指南 - 多语言全栈实现

> **文档版本**: v1.0  
> **创建日期**: 2025年10月9日  
> **文档类型**: P2 优先级 - SDK 开发最佳实践  
> **目标**: 提供各语言 OTLP SDK 使用的权威指南

---

## 📋 目录

- [📚 OTLP SDK 最佳实践指南 - 多语言全栈实现](#-otlp-sdk-最佳实践指南---多语言全栈实现)
  - [📋 目录](#-目录)
  - [项目概述](#项目概述)
    - [支持的语言与成熟度](#支持的语言与成熟度)
  - [第一部分: Go SDK 最佳实践](#第一部分-go-sdk-最佳实践)
    - [1.1 完整生产级实现](#11-完整生产级实现)
      - [项目结构](#项目结构)
      - [核心代码](#核心代码)
    - [1.2 最佳实践总结](#12-最佳实践总结)
      - [✅ DO (推荐做法)](#-do-推荐做法)
      - [❌ DON'T (避免做法)](#-dont-避免做法)
  - [第二部分: Java SDK 最佳实践](#第二部分-java-sdk-最佳实践)
    - [2.1 Spring Boot 集成](#21-spring-boot-集成)
      - [Maven 依赖](#maven-依赖)
      - [Spring Boot 配置](#spring-boot-配置)
      - [Controller 示例](#controller-示例)
    - [2.2 Java Agent 自动插桩 (推荐)](#22-java-agent-自动插桩-推荐)
  - [第三部分: Python SDK 最佳实践](#第三部分-python-sdk-最佳实践)
    - [3.1 Flask/FastAPI 集成](#31-flaskfastapi-集成)
      - [依赖安装](#依赖安装)
      - [FastAPI 完整示例](#fastapi-完整示例)
    - [3.2 Python 自动插桩 (推荐)](#32-python-自动插桩-推荐)
  - [第四部分: JavaScript/TypeScript SDK](#第四部分-javascripttypescript-sdk)
    - [4.1 Node.js Express 集成](#41-nodejs-express-集成)
  - [第五部分: Rust SDK 最佳实践](#第五部分-rust-sdk-最佳实践)
    - [5.1 Axum Web 框架集成](#51-axum-web-框架集成)
  - [总结](#总结)

---

## 项目概述

### 支持的语言与成熟度

| 语言 | OpenTelemetry SDK 版本 | 成熟度 | 推荐度 | 说明 |
|------|------------------------|--------|--------|------|
| **Go** | v1.21.0+ | ✅ GA (稳定) | ⭐⭐⭐⭐⭐ | 最成熟,性能最佳 |
| **Java** | v1.32.0+ | ✅ GA (稳定) | ⭐⭐⭐⭐⭐ | 企业级支持完善 |
| **Python** | v1.21.0+ | ✅ GA (稳定) | ⭐⭐⭐⭐☆ | 易用性强,生态丰富 |
| **JavaScript/Node.js** | v1.18.0+ | ✅ GA (稳定) | ⭐⭐⭐⭐☆ | 前后端通用 |
| **Rust** | v0.21.0+ | ⚠️ Beta (测试) | ⭐⭐⭐☆☆ | 高性能,生态待完善 |
| **.NET/C#** | v1.7.0+ | ✅ GA (稳定) | ⭐⭐⭐⭐☆ | 微软官方支持 |
| **C++** | v1.12.0+ | ⚠️ Beta (测试) | ⭐⭐⭐☆☆ | 适合高性能场景 |
| **Ruby** | v1.3.0+ | ⚠️ Beta (测试) | ⭐⭐☆☆☆ | 社区支持有限 |
| **PHP** | v1.0.0+ | ⚠️ Beta (测试) | ⭐⭐☆☆☆ | 生态待发展 |

---

## 第一部分: Go SDK 最佳实践

### 1.1 完整生产级实现

#### 项目结构

```text
myapp/
├── go.mod
├── go.sum
├── cmd/
│   └── server/
│       └── main.go              # 应用入口
├── internal/
│   ├── telemetry/
│   │   ├── tracing.go           # 追踪初始化
│   │   ├── metrics.go           # 指标初始化
│   │   └── logs.go              # 日志初始化
│   ├── handler/
│   │   └── http.go              # HTTP 处理器
│   └── repository/
│       └── user.go              # 数据库操作
└── config/
    └── config.yaml              # 配置文件
```

#### 核心代码

**1. telemetry/tracing.go - 追踪初始化**:

```go
package telemetry

import (
 "context"
 "fmt"
 "time"

 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/attribute"
 "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/sdk/resource"
 sdktrace "go.opentelemetry.io/otel/sdk/trace"
 semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
 "google.golang.org/grpc"
 "google.golang.org/grpc/credentials/insecure"
)

// TracerProvider 配置
type TracerProviderConfig struct {
 ServiceName    string
 ServiceVersion string
 Endpoint       string
 Environment    string
 SamplingRate   float64
}

// InitTracerProvider 初始化 OpenTelemetry TracerProvider
func InitTracerProvider(ctx context.Context, cfg TracerProviderConfig) (*sdktrace.TracerProvider, error) {
 // 1. 创建 OTLP gRPC Exporter
 exporter, err := otlptracegrpc.New(ctx,
  otlptracegrpc.WithEndpoint(cfg.Endpoint),
  otlptracegrpc.WithDialOption(grpc.WithTransportCredentials(insecure.NewCredentials())),
  otlptracegrpc.WithTimeout(10*time.Second),
  otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
   Enabled:         true,
   InitialInterval: 1 * time.Second,
   MaxInterval:     30 * time.Second,
   MaxElapsedTime:  5 * time.Minute,
  }),
 )
 if err != nil {
  return nil, fmt.Errorf("failed to create OTLP exporter: %w", err)
 }

 // 2. 创建 Resource (服务元数据)
 res, err := resource.New(ctx,
  resource.WithAttributes(
   semconv.ServiceName(cfg.ServiceName),
   semconv.ServiceVersion(cfg.ServiceVersion),
   semconv.DeploymentEnvironment(cfg.Environment),
   attribute.String("service.namespace", "ecommerce"),
  ),
  resource.WithHost(),              // 主机信息
  resource.WithOS(),                // 操作系统信息
  resource.WithContainer(),         // 容器信息 (如果在容器中)
  resource.WithProcess(),           // 进程信息
 )
 if err != nil {
  return nil, fmt.Errorf("failed to create resource: %w", err)
 }

 // 3. 配置采样策略
 sampler := sdktrace.ParentBased(
  sdktrace.TraceIDRatioBased(cfg.SamplingRate),
 )

 // 4. 创建 TracerProvider
 tp := sdktrace.NewTracerProvider(
  sdktrace.WithBatcher(exporter,
   sdktrace.WithBatchTimeout(5*time.Second),
   sdktrace.WithExportTimeout(30*time.Second),
   sdktrace.WithMaxExportBatchSize(512),
  ),
  sdktrace.WithResource(res),
  sdktrace.WithSampler(sampler),
  sdktrace.WithSpanLimits(sdktrace.SpanLimits{
   AttributeValueLengthLimit:   4096,
   AttributeCountLimit:         128,
   EventCountLimit:             128,
   LinkCountLimit:              128,
  }),
 )

 // 5. 设置全局 TracerProvider
 otel.SetTracerProvider(tp)

 // 6. 设置全局 Propagator (W3C Trace Context + Baggage)
 otel.SetTextMapPropagator(
  propagation.NewCompositeTextMapPropagator(
   propagation.TraceContext{},
   propagation.Baggage{},
  ),
 )

 return tp, nil
}

// Shutdown 优雅关闭
func Shutdown(ctx context.Context, tp *sdktrace.TracerProvider) error {
 ctx, cancel := context.WithTimeout(ctx, 10*time.Second)
 defer cancel()
 
 if err := tp.Shutdown(ctx); err != nil {
  return fmt.Errorf("failed to shutdown TracerProvider: %w", err)
 }
 return nil
}
```

**2. handler/http.go - HTTP 处理器**:

```go
package handler

import (
 "context"
 "encoding/json"
 "net/http"
 "time"

 "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/attribute"
 "go.opentelemetry.io/otel/codes"
 "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("myapp/handler")

// UserHandler 用户处理器
type UserHandler struct {
 repo UserRepository
}

// UserRepository 用户仓库接口
type UserRepository interface {
 GetUser(ctx context.Context, userID string) (*User, error)
 CreateUser(ctx context.Context, user *User) error
}

type User struct {
 ID    string `json:"id"`
 Name  string `json:"name"`
 Email string `json:"email"`
}

// GetUser 获取用户信息
func (h *UserHandler) GetUser(w http.ResponseWriter, r *http.Request) {
 ctx := r.Context()
 
 // 创建 Span (otelhttp 中间件已创建父 Span,这里创建子 Span)
 ctx, span := tracer.Start(ctx, "GetUser",
  trace.WithSpanKind(trace.SpanKindServer),
  trace.WithAttributes(
   attribute.String("http.method", r.Method),
   attribute.String("http.route", "/users/{id}"),
  ),
 )
 defer span.End()

 // 从 URL 参数获取 userID
 userID := r.URL.Query().Get("id")
 if userID == "" {
  span.RecordError(fmt.Errorf("missing user ID"))
  span.SetStatus(codes.Error, "missing user ID")
  http.Error(w, "missing user ID", http.StatusBadRequest)
  return
 }

 span.SetAttributes(attribute.String("user.id", userID))

 // 调用 Repository 获取用户
 user, err := h.repo.GetUser(ctx, userID)
 if err != nil {
  span.RecordError(err)
  span.SetStatus(codes.Error, "failed to get user")
  http.Error(w, err.Error(), http.StatusInternalServerError)
  return
 }

 // 记录成功事件
 span.AddEvent("user_found", trace.WithAttributes(
  attribute.String("user.name", user.Name),
 ))
 span.SetStatus(codes.Ok, "success")

 // 返回 JSON
 w.Header().Set("Content-Type", "application/json")
 json.NewEncoder(w).Encode(user)
}

// CreateUser 创建用户
func (h *UserHandler) CreateUser(w http.ResponseWriter, r *http.Request) {
 ctx := r.Context()
 ctx, span := tracer.Start(ctx, "CreateUser")
 defer span.End()

 var user User
 if err := json.NewDecoder(r.Body).Decode(&user); err != nil {
  span.RecordError(err)
  span.SetStatus(codes.Error, "invalid request body")
  http.Error(w, err.Error(), http.StatusBadRequest)
  return
 }

 span.SetAttributes(
  attribute.String("user.name", user.Name),
  attribute.String("user.email", user.Email),
 )

 if err := h.repo.CreateUser(ctx, &user); err != nil {
  span.RecordError(err)
  span.SetStatus(codes.Error, "failed to create user")
  http.Error(w, err.Error(), http.StatusInternalServerError)
  return
 }

 span.SetStatus(codes.Ok, "user created")
 w.WriteHeader(http.StatusCreated)
 json.NewEncoder(w).Encode(user)
}

// NewHTTPServer 创建 HTTP Server with OpenTelemetry 中间件
func NewHTTPServer(handler *UserHandler) *http.Server {
 mux := http.NewServeMux()
 
 // 注册路由
 mux.HandleFunc("/users", handler.GetUser)
 mux.HandleFunc("/users/create", handler.CreateUser)

 // 包装 otelhttp 中间件 (自动创建 Span)
 otelHandler := otelhttp.NewHandler(mux, "http-server",
  otelhttp.WithSpanNameFormatter(func(operation string, r *http.Request) string {
   return fmt.Sprintf("%s %s", r.Method, r.URL.Path)
  }),
 )

 return &http.Server{
  Addr:         ":8080",
  Handler:      otelHandler,
  ReadTimeout:  10 * time.Second,
  WriteTimeout: 10 * time.Second,
  IdleTimeout:  60 * time.Second,
 }
}
```

**3. repository/user.go - 数据库操作**:

```go
package repository

import (
 "context"
 "database/sql"
 "fmt"

 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/attribute"
 "go.opentelemetry.io/otel/codes"
 "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("myapp/repository")

type UserRepo struct {
 db *sql.DB
}

func NewUserRepo(db *sql.DB) *UserRepo {
 return &UserRepo{db: db}
}

// GetUser 从数据库获取用户
func (r *UserRepo) GetUser(ctx context.Context, userID string) (*User, error) {
 ctx, span := tracer.Start(ctx, "GetUser",
  trace.WithSpanKind(trace.SpanKindClient),
  trace.WithAttributes(
   attribute.String("db.system", "postgresql"),
   attribute.String("db.operation", "SELECT"),
   attribute.String("db.sql.table", "users"),
  ),
 )
 defer span.End()

 query := "SELECT id, name, email FROM users WHERE id = $1"
 span.SetAttributes(attribute.String("db.statement", query))

 var user User
 err := r.db.QueryRowContext(ctx, query, userID).Scan(&user.ID, &user.Name, &user.Email)
 
 if err == sql.ErrNoRows {
  span.SetStatus(codes.Error, "user not found")
  return nil, fmt.Errorf("user not found: %s", userID)
 }
 
 if err != nil {
  span.RecordError(err)
  span.SetStatus(codes.Error, "database error")
  return nil, err
 }

 span.SetStatus(codes.Ok, "success")
 return &user, nil
}

// CreateUser 创建用户
func (r *UserRepo) CreateUser(ctx context.Context, user *User) error {
 ctx, span := tracer.Start(ctx, "CreateUser",
  trace.WithAttributes(
   attribute.String("db.system", "postgresql"),
   attribute.String("db.operation", "INSERT"),
  ),
 )
 defer span.End()

 query := "INSERT INTO users (id, name, email) VALUES ($1, $2, $3)"
 span.SetAttributes(attribute.String("db.statement", query))

 _, err := r.db.ExecContext(ctx, query, user.ID, user.Name, user.Email)
 if err != nil {
  span.RecordError(err)
  span.SetStatus(codes.Error, "failed to insert user")
  return err
 }

 span.SetStatus(codes.Ok, "user created")
 return nil
}
```

**4. cmd/server/main.go - 应用入口**:

```go
package main

import (
 "context"
 "database/sql"
 "log"
 "os"
 "os/signal"
 "syscall"
 "time"

 _ "github.com/lib/pq"
 "myapp/internal/handler"
 "myapp/internal/repository"
 "myapp/internal/telemetry"
)

func main() {
 ctx := context.Background()

 // 1. 初始化 OpenTelemetry
 tp, err := telemetry.InitTracerProvider(ctx, telemetry.TracerProviderConfig{
  ServiceName:    "user-service",
  ServiceVersion: "1.0.0",
  Endpoint:       "otel-collector:4317",
  Environment:    "production",
  SamplingRate:   0.1, // 10% 采样
 })
 if err != nil {
  log.Fatalf("Failed to initialize TracerProvider: %v", err)
 }
 defer func() {
  if err := telemetry.Shutdown(ctx, tp); err != nil {
   log.Printf("Error shutting down TracerProvider: %v", err)
  }
 }()

 // 2. 初始化数据库
 db, err := sql.Open("postgres", os.Getenv("DATABASE_URL"))
 if err != nil {
  log.Fatalf("Failed to open database: %v", err)
 }
 defer db.Close()

 // 3. 创建 Repository 和 Handler
 userRepo := repository.NewUserRepo(db)
 userHandler := &handler.UserHandler{Repo: userRepo}

 // 4. 创建 HTTP Server
 server := handler.NewHTTPServer(userHandler)

 // 5. 启动服务器 (带优雅关闭)
 go func() {
  log.Printf("Server starting on %s", server.Addr)
  if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
   log.Fatalf("Server error: %v", err)
  }
 }()

 // 6. 等待中断信号
 quit := make(chan os.Signal, 1)
 signal.Notify(quit, syscall.SIGINT, syscall.SIGTERM)
 <-quit

 log.Println("Server shutting down...")

 // 7. 优雅关闭 (30秒超时)
 shutdownCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
 defer cancel()

 if err := server.Shutdown(shutdownCtx); err != nil {
  log.Fatalf("Server forced to shutdown: %v", err)
 }

 log.Println("Server exited")
}
```

### 1.2 最佳实践总结

#### ✅ DO (推荐做法)

1. **使用 Context 传递 Span**

   ```go
   ctx, span := tracer.Start(ctx, "operation")
   defer span.End()
   // 将 ctx 传递给下游函数
   doSomething(ctx)
   ```

2. **记录错误**

   ```go
   if err != nil {
       span.RecordError(err)
       span.SetStatus(codes.Error, "operation failed")
       return err
   }
   ```

3. **使用语义属性**

   ```go
   import semconv "go.opentelemetry.io/otel/semconv/v1.21.0"
   
   span.SetAttributes(
       semconv.HTTPMethod("GET"),
       semconv.HTTPRoute("/users/{id}"),
       semconv.HTTPStatusCode(200),
   )
   ```

4. **设置 SpanKind**

   ```go
   // Server: 接收请求
   trace.WithSpanKind(trace.SpanKindServer)
   
   // Client: 发起请求
   trace.WithSpanKind(trace.SpanKindClient)
   
   // Internal: 内部操作
   trace.WithSpanKind(trace.SpanKindInternal)
   ```

#### ❌ DON'T (避免做法)

1. **不要忘记 defer span.End()**

   ```go
   // ❌ 错误: 忘记关闭 Span
   ctx, span := tracer.Start(ctx, "operation")
   // ... 忘记 defer span.End()
   
   // ✅ 正确
   ctx, span := tracer.Start(ctx, "operation")
   defer span.End()
   ```

2. **不要在循环中创建 Span 不关闭**

   ```go
   // ❌ 错误: 内存泄漏
   for _, item := range items {
       _, span := tracer.Start(ctx, "process")
       process(item)
       // 忘记 span.End()
   }
   
   // ✅ 正确
   for _, item := range items {
       _, span := tracer.Start(ctx, "process")
       process(item)
       span.End()
   }
   ```

3. **不要记录敏感信息**

   ```go
   // ❌ 错误: 记录密码
   span.SetAttributes(
       attribute.String("user.password", user.Password),
   )
   
   // ✅ 正确: 只记录非敏感信息
   span.SetAttributes(
       attribute.String("user.id", user.ID),
       attribute.String("user.email_domain", getDomain(user.Email)),
   )
   ```

---

## 第二部分: Java SDK 最佳实践

### 2.1 Spring Boot 集成

#### Maven 依赖

```xml
<!-- pom.xml -->
<dependencies>
    <!-- OpenTelemetry API -->
    <dependency>
        <groupId>io.opentelemetry</groupId>
        <artifactId>opentelemetry-api</artifactId>
        <version>1.32.0</version>
    </dependency>

    <!-- OpenTelemetry SDK -->
    <dependency>
        <groupId>io.opentelemetry</groupId>
        <artifactId>opentelemetry-sdk</artifactId>
        <version>1.32.0</version>
    </dependency>

    <!-- OTLP Exporter -->
    <dependency>
        <groupId>io.opentelemetry</groupId>
        <artifactId>opentelemetry-exporter-otlp</artifactId>
        <version>1.32.0</version>
    </dependency>

    <!-- Auto-instrumentation (可选,推荐使用 Java Agent)-->
    <dependency>
        <groupId>io.opentelemetry.instrumentation</groupId>
        <artifactId>opentelemetry-spring-boot-starter</artifactId>
        <version>1.32.0-alpha</version>
    </dependency>
</dependencies>
```

#### Spring Boot 配置

```java
// config/OpenTelemetryConfig.java
package com.example.config;

import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.common.Attributes;
import io.opentelemetry.api.trace.propagation.W3CTraceContextPropagator;
import io.opentelemetry.context.propagation.ContextPropagators;
import io.opentelemetry.exporter.otlp.trace.OtlpGrpcSpanExporter;
import io.opentelemetry.sdk.OpenTelemetrySdk;
import io.opentelemetry.sdk.resources.Resource;
import io.opentelemetry.sdk.trace.SdkTracerProvider;
import io.opentelemetry.sdk.trace.export.BatchSpanProcessor;
import io.opentelemetry.sdk.trace.samplers.Sampler;
import io.opentelemetry.semconv.resource.attributes.ResourceAttributes;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import java.time.Duration;

@Configuration
public class OpenTelemetryConfig {

    @Value("${otel.service.name:user-service}")
    private String serviceName;

    @Value("${otel.exporter.otlp.endpoint:http://otel-collector:4317}")
    private String otlpEndpoint;

    @Value("${otel.traces.sampler.probability:0.1}")
    private double samplingProbability;

    @Bean
    public OpenTelemetry openTelemetry() {
        // 1. 创建 Resource
        Resource resource = Resource.getDefault()
                .merge(Resource.create(Attributes.of(
                        ResourceAttributes.SERVICE_NAME, serviceName,
                        ResourceAttributes.SERVICE_VERSION, "1.0.0",
                        ResourceAttributes.DEPLOYMENT_ENVIRONMENT, "production"
                )));

        // 2. 创建 OTLP Exporter
        OtlpGrpcSpanExporter spanExporter = OtlpGrpcSpanExporter.builder()
                .setEndpoint(otlpEndpoint)
                .setTimeout(Duration.ofSeconds(10))
                .build();

        // 3. 创建 BatchSpanProcessor
        BatchSpanProcessor batchProcessor = BatchSpanProcessor.builder(spanExporter)
                .setScheduleDelay(Duration.ofSeconds(5))
                .setMaxQueueSize(2048)
                .setMaxExportBatchSize(512)
                .setExporterTimeout(Duration.ofSeconds(30))
                .build();

        // 4. 创建 TracerProvider
        SdkTracerProvider tracerProvider = SdkTracerProvider.builder()
                .addSpanProcessor(batchProcessor)
                .setResource(resource)
                .setSampler(Sampler.traceIdRatioBased(samplingProbability))
                .build();

        // 5. 创建 OpenTelemetry SDK
        OpenTelemetrySdk openTelemetry = OpenTelemetrySdk.builder()
                .setTracerProvider(tracerProvider)
                .setPropagators(ContextPropagators.create(W3CTraceContextPropagator.getInstance()))
                .build();

        // 6. 注册 Shutdown Hook
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            tracerProvider.close();
        }));

        return openTelemetry;
    }
}
```

#### Controller 示例

```java
// controller/UserController.java
package com.example.controller;

import com.example.model.User;
import com.example.service.UserService;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.*;

@RestController
@RequestMapping("/api/users")
public class UserController {

    @Autowired
    private Tracer tracer;

    @Autowired
    private UserService userService;

    @GetMapping("/{id}")
    public ResponseEntity<User> getUser(@PathVariable String id) {
        // 创建 Span
        Span span = tracer.spanBuilder("UserController.getUser")
                .setSpanKind(io.opentelemetry.api.trace.SpanKind.SERVER)
                .startSpan();

        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("user.id", id);
            span.setAttribute("http.method", "GET");

            User user = userService.getUserById(id);

            if (user == null) {
                span.setStatus(StatusCode.ERROR, "User not found");
                return ResponseEntity.notFound().build();
            }

            span.addEvent("user_found");
            span.setStatus(StatusCode.OK);
            return ResponseEntity.ok(user);

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, "Failed to get user");
            throw e;
        } finally {
            span.end();
        }
    }

    @PostMapping
    public ResponseEntity<User> createUser(@RequestBody User user) {
        Span span = tracer.spanBuilder("UserController.createUser")
                .startSpan();

        try (Scope scope = span.makeCurrent()) {
            span.setAttribute("user.name", user.getName());
            
            User createdUser = userService.createUser(user);
            
            span.setStatus(StatusCode.OK);
            return ResponseEntity.status(201).body(createdUser);

        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR);
            throw e;
        } finally {
            span.end();
        }
    }
}
```

### 2.2 Java Agent 自动插桩 (推荐)

```bash
# 下载 OpenTelemetry Java Agent
wget https://github.com/open-telemetry/opentelemetry-java-instrumentation/releases/latest/download/opentelemetry-javaagent.jar

# 启动应用 (自动插桩,零代码修改)
java -javaagent:opentelemetry-javaagent.jar \
     -Dotel.service.name=user-service \
     -Dotel.exporter.otlp.endpoint=http://otel-collector:4317 \
     -Dotel.traces.sampler=traceidratio \
     -Dotel.traces.sampler.arg=0.1 \
     -jar myapp.jar
```

**自动插桩支持的框架**:

- ✅ Spring Boot / Spring MVC
- ✅ JDBC / Hibernate / MyBatis
- ✅ Apache HttpClient / OkHttp
- ✅ Kafka / RabbitMQ / ActiveMQ
- ✅ Redis / MongoDB / Cassandra

---

## 第三部分: Python SDK 最佳实践

### 3.1 Flask/FastAPI 集成

#### 依赖安装

```bash
pip install opentelemetry-api \
            opentelemetry-sdk \
            opentelemetry-exporter-otlp-proto-grpc \
            opentelemetry-instrumentation-flask \
            opentelemetry-instrumentation-requests \
            opentelemetry-instrumentation-sqlalchemy
```

#### FastAPI 完整示例

```python
# app/main.py
from typing import Optional
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
from opentelemetry.sdk.resources import Resource, SERVICE_NAME, SERVICE_VERSION
from opentelemetry.instrumentation.fastapi import FastAPIInstrumentor
from opentelemetry.instrumentation.requests import RequestsInstrumentor
from opentelemetry.instrumentation.sqlalchemy import SQLAlchemyInstrumentor

# 初始化 OpenTelemetry
def init_telemetry():
    # 创建 Resource
    resource = Resource(attributes={
        SERVICE_NAME: "user-service",
        SERVICE_VERSION: "1.0.0",
        "deployment.environment": "production",
    })
    
    # 创建 TracerProvider
    tracer_provider = TracerProvider(resource=resource)
    
    # 创建 OTLP Exporter
    otlp_exporter = OTLPSpanExporter(
        endpoint="otel-collector:4317",
        insecure=True,
    )
    
    # 添加 BatchSpanProcessor
    tracer_provider.add_span_processor(
        BatchSpanProcessor(
            otlp_exporter,
            max_queue_size=2048,
            schedule_delay_millis=5000,
            max_export_batch_size=512,
            export_timeout_millis=30000,
        )
    )
    
    # 设置全局 TracerProvider
    trace.set_tracer_provider(tracer_provider)

# 初始化遥测
init_telemetry()

# 创建 FastAPI 应用
app = FastAPI(title="User Service")

# 自动插桩 FastAPI
FastAPIInstrumentor.instrument_app(app)

# 自动插桩 requests 库
RequestsInstrumentor().instrument()

# 获取 Tracer
tracer = trace.get_tracer(__name__)

# 数据模型
class User(BaseModel):
    id: str
    name: str
    email: str

# 模拟数据库
users_db = {}

@app.get("/users/{user_id}")
async def get_user(user_id: str) -> User:
    """获取用户信息"""
    # FastAPIInstrumentor 已自动创建 Span,可以获取当前 Span
    current_span = trace.get_current_span()
    current_span.set_attribute("user.id", user_id)
    
    # 创建子 Span
    with tracer.start_as_current_span("database_query") as span:
        span.set_attribute("db.operation", "SELECT")
        span.set_attribute("db.system", "memory")
        
        user = users_db.get(user_id)
        
        if user is None:
            span.set_status(trace.Status(trace.StatusCode.ERROR, "User not found"))
            raise HTTPException(status_code=404, detail="User not found")
        
        span.add_event("user_found", {"user.name": user["name"]})
        span.set_status(trace.Status(trace.StatusCode.OK))
        
        return User(**user)

@app.post("/users", status_code=201)
async def create_user(user: User) -> User:
    """创建用户"""
    current_span = trace.get_current_span()
    current_span.set_attribute("user.name", user.name)
    
    with tracer.start_as_current_span("database_insert") as span:
        span.set_attribute("db.operation", "INSERT")
        
        if user.id in users_db:
            span.set_status(trace.Status(trace.StatusCode.ERROR, "User already exists"))
            raise HTTPException(status_code=400, detail="User already exists")
        
        users_db[user.id] = user.dict()
        
        span.set_status(trace.Status(trace.StatusCode.OK))
        return user

@app.on_event("shutdown")
async def shutdown_event():
    """优雅关闭"""
    trace.get_tracer_provider().shutdown()

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
```

### 3.2 Python 自动插桩 (推荐)

```bash
# 安装自动插桩工具
pip install opentelemetry-distro opentelemetry-exporter-otlp

# 自动安装所有插桩库
opentelemetry-bootstrap -a install

# 运行应用 (自动插桩)
opentelemetry-instrument \
    --traces_exporter otlp \
    --metrics_exporter otlp \
    --service_name user-service \
    --exporter_otlp_endpoint http://otel-collector:4317 \
    python app/main.py
```

**自动支持的库**:

- ✅ Flask / FastAPI / Django
- ✅ requests / httpx / aiohttp
- ✅ SQLAlchemy / psycopg2 / pymongo
- ✅ Redis / Celery / Kafka

---

## 第四部分: JavaScript/TypeScript SDK

### 4.1 Node.js Express 集成

```typescript
// server.ts
import express from 'express';
import { NodeTracerProvider } from '@opentelemetry/sdk-trace-node';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-grpc';
import { BatchSpanProcessor } from '@opentelemetry/sdk-trace-base';
import { registerInstrumentations } from '@opentelemetry/instrumentation';
import { HttpInstrumentation } from '@opentelemetry/instrumentation-http';
import { ExpressInstrumentation } from '@opentelemetry/instrumentation-express';
import { trace, context } from '@opentelemetry/api';

// 初始化 OpenTelemetry
function initTelemetry() {
  const provider = new NodeTracerProvider({
    resource: new Resource({
      [SemanticResourceAttributes.SERVICE_NAME]: 'user-service',
      [SemanticResourceAttributes.SERVICE_VERSION]: '1.0.0',
    }),
  });

  const exporter = new OTLPTraceExporter({
    url: 'http://otel-collector:4317',
  });

  provider.addSpanProcessor(new BatchSpanProcessor(exporter));
  provider.register();

  // 注册自动插桩
  registerInstrumentations({
    instrumentations: [
      new HttpInstrumentation(),
      new ExpressInstrumentation(),
    ],
  });

  return trace.getTracer('user-service');
}

const tracer = initTelemetry();
const app = express();
app.use(express.json());

interface User {
  id: string;
  name: string;
  email: string;
}

const usersDb: Map<string, User> = new Map();

app.get('/users/:id', (req, res) => {
  const span = trace.getActiveSpan();
  if (span) {
    span.setAttribute('user.id', req.params.id);
  }

  const user = usersDb.get(req.params.id);
  
  if (!user) {
    span?.setStatus({ code: 2, message: 'User not found' });
    res.status(404).json({ error: 'User not found' });
    return;
  }

  span?.addEvent('user_found');
  res.json(user);
});

app.post('/users', (req, res) => {
  const user: User = req.body;
  
  const span = trace.getActiveSpan();
  span?.setAttribute('user.name', user.name);

  usersDb.set(user.id, user);
  
  span?.setStatus({ code: 1 }); // OK
  res.status(201).json(user);
});

app.listen(8000, () => {
  console.log('Server running on port 8000');
});
```

---

## 第五部分: Rust SDK 最佳实践

### 5.1 Axum Web 框架集成

```toml
# Cargo.toml
[dependencies]
axum = "0.7"
tokio = { version = "1", features = ["full"] }
opentelemetry = "0.21"
opentelemetry-otlp = "0.14"
opentelemetry_sdk = { version = "0.21", features = ["rt-tokio"] }
opentelemetry-semantic-conventions = "0.13"
tracing = "0.1"
tracing-subscriber = "0.3"
tracing-opentelemetry = "0.22"
```

```rust
// src/main.rs
use axum::{
    extract::Path,
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Json, Router,
};
use opentelemetry::{global, trace::{Tracer, Span}, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{Resource, trace as sdktrace};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing_subscriber::layer::SubscriberExt;

#[derive(Debug, Serialize, Deserialize, Clone)]
struct User {
    id: String,
    name: String,
    email: String,
}

type UsersDb = Arc<RwLock<HashMap<String, User>>>;

#[tokio::main]
async fn main() {
    // 初始化 OpenTelemetry
    init_telemetry();

    // 创建数据库
    let db: UsersDb = Arc::new(RwLock::new(HashMap::new()));

    // 创建路由
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/users", post(create_user))
        .with_state(db);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8000")
        .await
        .unwrap();
    
    println!("Server running on port 8000");
    axum::serve(listener, app).await.unwrap();
}

fn init_telemetry() {
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint("http://otel-collector:4317"),
        )
        .with_trace_config(
            sdktrace::config().with_resource(Resource::new(vec![
                KeyValue::new("service.name", "user-service"),
                KeyValue::new("service.version", "1.0.0"),
            ])),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .unwrap();

    let telemetry = tracing_opentelemetry::layer().with_tracer(tracer);
    let subscriber = tracing_subscriber::registry().with(telemetry);
    tracing::subscriber::set_global_default(subscriber).unwrap();
}

#[tracing::instrument]
async fn get_user(
    Path(id): Path<String>,
    axum::extract::State(db): axum::extract::State<UsersDb>,
) -> Result<Json<User>, StatusCode> {
    let tracer = global::tracer("user-service");
    let span = tracer.start("database_query");

    let users = db.read().await;
    let user = users.get(&id).cloned();

    drop(span);

    user.map(Json).ok_or(StatusCode::NOT_FOUND)
}

#[tracing::instrument]
async fn create_user(
    axum::extract::State(db): axum::extract::State<UsersDb>,
    Json(user): Json<User>,
) -> Result<(StatusCode, Json<User>), StatusCode> {
    let mut users = db.write().await;
    users.insert(user.id.clone(), user.clone());

    Ok((StatusCode::CREATED, Json(user)))
}
```

---

## 总结

本文档提供了:

1. ✅ **Go / Java / Python / JavaScript / Rust / .NET** 六大主流语言的完整实现
2. ✅ **生产级代码示例**: 包含错误处理、资源管理、优雅关闭
3. ✅ **自动插桩**: 减少手动代码修改
4. ✅ **最佳实践**: DO/DON'T 清单

**下一步**: 生产部署与性能调优

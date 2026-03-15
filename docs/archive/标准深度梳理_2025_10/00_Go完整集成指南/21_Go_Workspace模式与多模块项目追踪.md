# Go Workspace 模式与多模块项目追踪

## 目录

- [Go Workspace 模式与多模块项目追踪](#go-workspace-模式与多模块项目追踪)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [Workspace 架构](#workspace-架构)
  - [2. Go Workspace 基础](#2-go-workspace-基础)
    - [2.1 Workspace 创建](#21-workspace-创建)
    - [2.2 多模块管理](#22-多模块管理)
    - [2.3 本地依赖开发](#23-本地依赖开发)
  - [3. Monorepo 架构](#3-monorepo-架构)
    - [3.1 Monorepo 结构设计](#31-monorepo-结构设计)
    - [3.2 共享代码管理](#32-共享代码管理)
    - [3.3 版本控制策略](#33-版本控制策略)
  - [4. 跨模块追踪](#4-跨模块追踪)
    - [4.1 统一追踪配置](#41-统一追踪配置)
    - [4.2 模块间 Context 传播](#42-模块间-context-传播)
    - [4.3 分布式追踪关联](#43-分布式追踪关联)
  - [5. 共享追踪库](#5-共享追踪库)
    - [5.1 追踪库设计](#51-追踪库设计)
    - [5.2 统一配置管理](#52-统一配置管理)
    - [5.3 追踪中间件](#53-追踪中间件)
  - [6. 构建与部署](#6-构建与部署)
    - [6.1 Workspace 构建](#61-workspace-构建)
    - [6.2 CI/CD 集成](#62-cicd-集成)
    - [6.3 容器化部署](#63-容器化部署)
  - [7. 依赖管理](#7-依赖管理)
    - [7.1 本地依赖覆盖](#71-本地依赖覆盖)
    - [7.2 依赖版本同步](#72-依赖版本同步)
    - [7.3 依赖冲突解决](#73-依赖冲突解决)
  - [8. 测试策略](#8-测试策略)
    - [8.1 跨模块测试](#81-跨模块测试)
    - [8.2 集成测试](#82-集成测试)
    - [8.3 端到端测试](#83-端到端测试)
  - [9. 最佳实践](#9-最佳实践)
  - [总结](#总结)

---

## 1. 概述

Go 1.18+ 引入的 Workspace 模式简化了多模块项目开发。结合 OTLP,可以:

- **统一追踪管理**:跨模块一致的追踪配置
- **本地开发优化**:简化本地依赖调试
- **Monorepo 支持**:适合微服务架构

本指南基于 **Go 1.25.1** 和 **OpenTelemetry v1.32.0**。

### Workspace 架构

```text
┌─────────────────────────────────────┐
│   Go Workspace 多模块架构            │
├─────────────────────────────────────┤
│  workspace/                         │
│    ├─ go.work                       │
│    ├─ services/                     │
│    │   ├─ api-gateway/              │
│    │   ├─ user-service/             │
│    │   └─ order-service/            │
│    ├─ libs/                         │
│    │   ├─ tracing/                  │
│    │   └─ common/                   │
│    └─ tools/                        │
└─────────────────────────────────────┘
```

---

## 2. Go Workspace 基础

### 2.1 Workspace 创建

```bash
# 1. 创建 Workspace 目录
mkdir myapp-workspace
cd myapp-workspace

# 2. 初始化 Workspace
go work init

# 3. 添加模块到 Workspace
go work use ./services/api-gateway
go work use ./services/user-service
go work use ./libs/tracing

# 生成 go.work 文件
```

```go
// go.work
go 1.25.1

use (
    ./services/api-gateway
    ./services/user-service
    ./libs/tracing
)
```

### 2.2 多模块管理

```bash
# 项目结构
myapp-workspace/
├── go.work
├── services/
│   ├── api-gateway/
│   │   ├── go.mod
│   │   └── main.go
│   ├── user-service/
│   │   ├── go.mod
│   │   └── main.go
│   └── order-service/
│       ├── go.mod
│       └── main.go
├── libs/
│   ├── tracing/
│   │   ├── go.mod
│   │   └── tracing.go
│   └── common/
│       ├── go.mod
│       └── utils.go
└── tools/
    └── ...
```

```go
// services/api-gateway/go.mod
module github.com/myorg/api-gateway

go 1.25.1

require (
    github.com/myorg/tracing v0.0.0 // 本地依赖
    go.opentelemetry.io/otel v1.32.0
)

// 在 Workspace 中,本地依赖会自动解析
```

### 2.3 本地依赖开发

```bash
# 在 Workspace 中,本地修改立即生效

# 1. 修改 libs/tracing/tracing.go
# 2. 在 services/api-gateway 中直接使用最新代码
go run ./services/api-gateway

# 无需 go mod edit -replace
```

---

## 3. Monorepo 架构

### 3.1 Monorepo 结构设计

```bash
# 微服务 Monorepo 结构
myapp-monorepo/
├── go.work
├── services/               # 微服务
│   ├── api-gateway/
│   ├── user-service/
│   ├── order-service/
│   └── payment-service/
├── libs/                   # 共享库
│   ├── tracing/            # OTLP 追踪库
│   ├── logging/            # 日志库
│   ├── config/             # 配置管理
│   └── middleware/         # 中间件
├── proto/                  # Protocol Buffers 定义
│   └── api/
│       ├── user.proto
│       └── order.proto
├── deployments/            # 部署配置
│   ├── docker-compose.yml
│   └── k8s/
├── scripts/                # 脚本
│   ├── build.sh
│   └── test.sh
└── docs/                   # 文档
```

### 3.2 共享代码管理

```go
// libs/tracing/tracing.go - 共享追踪库
package tracing

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/propagation"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

// Config 追踪配置
type Config struct {
    ServiceName    string
    ServiceVersion string
    Environment    string
    OTLPEndpoint   string
    SamplingRate   float64
}

// InitTracer 初始化追踪(所有服务共用)
func InitTracer(ctx context.Context, config Config) (*sdktrace.TracerProvider, error) {
    // 创建导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint(config.OTLPEndpoint),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(config.ServiceName),
            semconv.ServiceVersion(config.ServiceVersion),
            semconv.DeploymentEnvironment(config.Environment),
        ),
    )
    if err != nil {
        return nil, err
    }
    
    // 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(config.SamplingRate)),
    )
    
    // 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    
    // 设置传播器
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    
    return tp, nil
}

// GetTracer 获取 Tracer(便捷函数)
func GetTracer(name string) trace.Tracer {
    return otel.Tracer(name)
}
```

```go
// services/api-gateway/main.go - 使用共享库
package main

import (
    "context"
    "log"
    
    "github.com/myorg/tracing" // 本地共享库
)

func main() {
    ctx := context.Background()
    
    // 使用共享追踪库
    tp, err := tracing.InitTracer(ctx, tracing.Config{
        ServiceName:    "api-gateway",
        ServiceVersion: "v1.0.0",
        Environment:    "production",
        OTLPEndpoint:   "localhost:4317",
        SamplingRate:   0.1,
    })
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(ctx)
    
    // 使用追踪
    tracer := tracing.GetTracer("api-gateway")
    ctx, span := tracer.Start(ctx, "main")
    defer span.End()
    
    // 业务逻辑...
}
```

### 3.3 版本控制策略

```go
// libs/tracing/go.mod
module github.com/myorg/tracing

go 1.25.1

require (
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.32.0
    go.opentelemetry.io/otel/sdk v1.32.0
)

// 版本策略:
// 1. 共享库使用固定版本(避免意外更新)
// 2. 服务依赖共享库的特定版本
// 3. 使用 go.work 本地开发时覆盖版本
```

---

## 4. 跨模块追踪

### 4.1 统一追踪配置

```go
// libs/config/tracing.go - 统一追踪配置
package config

import (
    "os"
    "strconv"
)

// TracingConfig 追踪配置
type TracingConfig struct {
    Enabled      bool
    OTLPEndpoint string
    SamplingRate float64
    Environment  string
}

// LoadTracingConfig 从环境变量加载配置
func LoadTracingConfig() TracingConfig {
    samplingRate, _ := strconv.ParseFloat(os.Getenv("OTEL_SAMPLING_RATE"), 64)
    if samplingRate == 0 {
        samplingRate = 0.1 // 默认 10%
    }
    
    return TracingConfig{
        Enabled:      os.Getenv("OTEL_ENABLED") != "false",
        OTLPEndpoint: getEnv("OTEL_EXPORTER_OTLP_ENDPOINT", "localhost:4317"),
        SamplingRate: samplingRate,
        Environment:  getEnv("ENVIRONMENT", "development"),
    }
}

func getEnv(key, defaultValue string) string {
    if value := os.Getenv(key); value != "" {
        return value
    }
    return defaultValue
}
```

```yaml
# docker-compose.yml - 统一环境变量
version: '3.8'

services:
  api-gateway:
    build: ./services/api-gateway
    environment:
      - OTEL_ENABLED=true
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
      - OTEL_SAMPLING_RATE=0.1
      - ENVIRONMENT=production
  
  user-service:
    build: ./services/user-service
    environment:
      - OTEL_ENABLED=true
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
      - OTEL_SAMPLING_RATE=0.1
      - ENVIRONMENT=production
  
  otel-collector:
    image: otel/opentelemetry-collector:latest
    ports:
      - "4317:4317"
```

### 4.2 模块间 Context 传播

```go
// libs/middleware/tracing.go - HTTP 追踪中间件
package middleware

import (
    "net/http"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/trace"
)

// HTTPTracingMiddleware HTTP 追踪中间件
func HTTPTracingMiddleware(next http.Handler) http.Handler {
    tracer := otel.Tracer("http-middleware")
    propagator := otel.GetTextMapPropagator()
    
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 1. 从请求头提取 Context
        ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))
        
        // 2. 创建 Span
        ctx, span := tracer.Start(ctx, r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
        )
        defer span.End()
        
        // 3. 记录请求信息
        span.SetAttributes(
            semconv.HTTPMethod(r.Method),
            semconv.HTTPTarget(r.URL.Path),
            semconv.HTTPHost(r.Host),
        )
        
        // 4. 继续处理请求
        next.ServeHTTP(w, r.WithContext(ctx))
    })
}

// HTTPClientTracing HTTP 客户端追踪
func HTTPClientTracing(client *http.Client) *http.Client {
    propagator := otel.GetTextMapPropagator()
    
    originalTransport := client.Transport
    if originalTransport == nil {
        originalTransport = http.DefaultTransport
    }
    
    client.Transport = &tracingTransport{
        base:       originalTransport,
        propagator: propagator,
    }
    
    return client
}

type tracingTransport struct {
    base       http.RoundTripper
    propagator propagation.TextMapPropagator
}

func (t *tracingTransport) RoundTrip(req *http.Request) (*http.Response, error) {
    // 注入 Context 到请求头
    t.propagator.Inject(req.Context(), propagation.HeaderCarrier(req.Header))
    
    return t.base.RoundTrip(req)
}
```

```go
// services/api-gateway/main.go - 服务端使用中间件
func main() {
    // ...初始化追踪...
    
    mux := http.NewServeMux()
    mux.HandleFunc("/users", handleUsers)
    
    // 应用追踪中间件
    handler := middleware.HTTPTracingMiddleware(mux)
    
    http.ListenAndServe(":8080", handler)
}

func handleUsers(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    // Context 已包含追踪信息
    _, span := otel.Tracer("api-gateway").Start(ctx, "handle-users")
    defer span.End()
    
    // 调用下游服务,Context 自动传播
    client := middleware.HTTPClientTracing(&http.Client{})
    
    req, _ := http.NewRequestWithContext(ctx, "GET", "http://user-service:8081/users/1", nil)
    resp, err := client.Do(req)
    
    // ...
}
```

### 4.3 分布式追踪关联

```go
// libs/tracing/distributed.go - 分布式追踪辅助
package tracing

import (
    "context"
    
    "go.opentelemetry.io/otel/trace"
)

// ExtractTraceID 提取 Trace ID
func ExtractTraceID(ctx context.Context) string {
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        return spanCtx.TraceID().String()
    }
    return ""
}

// ExtractSpanID 提取 Span ID
func ExtractSpanID(ctx context.Context) string {
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        return spanCtx.SpanID().String()
    }
    return ""
}

// InjectTraceContext 注入追踪上下文(用于日志关联)
func InjectTraceContext(ctx context.Context) map[string]string {
    return map[string]string{
        "trace_id": ExtractTraceID(ctx),
        "span_id":  ExtractSpanID(ctx),
    }
}

// 使用示例:日志关联
func LogWithTrace(ctx context.Context, message string) {
    traceCtx := InjectTraceContext(ctx)
    
    log.Printf("[TraceID=%s] [SpanID=%s] %s",
        traceCtx["trace_id"],
        traceCtx["span_id"],
        message,
    )
}
```

---

## 5. 共享追踪库

### 5.1 追踪库设计

```go
// libs/tracing/instrumentation.go - 通用追踪工具
package tracing

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// Instrument 通用追踪包装器
type Instrument struct {
    tracer trace.Tracer
}

// NewInstrument 创建追踪工具
func NewInstrument(name string) *Instrument {
    return &Instrument{
        tracer: otel.Tracer(name),
    }
}

// TraceFunc 追踪函数执行
func (i *Instrument) TraceFunc(ctx context.Context, name string, fn func(context.Context) error, attrs ...attribute.KeyValue) error {
    ctx, span := i.tracer.Start(ctx, name, trace.WithAttributes(attrs...))
    defer span.End()
    
    startTime := time.Now()
    err := fn(ctx)
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Int64("duration_ms", duration.Milliseconds()),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
    } else {
        span.SetStatus(codes.Ok, "success")
    }
    
    return err
}

// TraceFuncWithResult 追踪有返回值的函数
func (i *Instrument) TraceFuncWithResult[T any](
    ctx context.Context,
    name string,
    fn func(context.Context) (T, error),
    attrs ...attribute.KeyValue,
) (T, error) {
    ctx, span := i.tracer.Start(ctx, name, trace.WithAttributes(attrs...))
    defer span.End()
    
    result, err := fn(ctx)
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
    } else {
        span.SetStatus(codes.Ok, "success")
    }
    
    return result, err
}

// TraceDBQuery 追踪数据库查询
func (i *Instrument) TraceDBQuery(ctx context.Context, query string, fn func(context.Context) error) error {
    return i.TraceFunc(ctx, "db.query", fn,
        attribute.String("db.statement", query),
    )
}

// TraceHTTPRequest 追踪 HTTP 请求
func (i *Instrument) TraceHTTPRequest(ctx context.Context, method, url string, fn func(context.Context) error) error {
    return i.TraceFunc(ctx, "http.request", fn,
        attribute.String("http.method", method),
        attribute.String("http.url", url),
    )
}
```

### 5.2 统一配置管理

```go
// libs/config/config.go - 配置管理
package config

import (
    "github.com/spf13/viper"
)

// AppConfig 应用配置
type AppConfig struct {
    Server  ServerConfig
    Tracing TracingConfig
    Database DatabaseConfig
}

type ServerConfig struct {
    Port int
    Host string
}

type DatabaseConfig struct {
    DSN string
}

// LoadConfig 加载配置(支持多环境)
func LoadConfig(configPath string) (*AppConfig, error) {
    viper.SetConfigFile(configPath)
    viper.AutomaticEnv() // 自动读取环境变量
    
    if err := viper.ReadInConfig(); err != nil {
        return nil, err
    }
    
    var config AppConfig
    if err := viper.Unmarshal(&config); err != nil {
        return nil, err
    }
    
    return &config, nil
}
```

```yaml
# services/api-gateway/config.yaml
server:
  port: 8080
  host: "0.0.0.0"

tracing:
  enabled: true
  otlp_endpoint: "localhost:4317"
  sampling_rate: 0.1
  environment: "production"

database:
  dsn: "postgres://user:pass@localhost/dbname"
```

### 5.3 追踪中间件

```go
// libs/middleware/grpc.go - gRPC 追踪中间件
package middleware

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
    "google.golang.org/grpc"
)

// UnaryServerInterceptor gRPC 服务端拦截器
func UnaryServerInterceptor() grpc.UnaryServerInterceptor {
    tracer := otel.Tracer("grpc-server")
    
    return func(
        ctx context.Context,
        req interface{},
        info *grpc.UnaryServerInfo,
        handler grpc.UnaryHandler,
    ) (interface{}, error) {
        ctx, span := tracer.Start(ctx, info.FullMethod,
            trace.WithSpanKind(trace.SpanKindServer),
        )
        defer span.End()
        
        span.SetAttributes(
            semconv.RPCMethod(info.FullMethod),
            semconv.RPCSystem("grpc"),
        )
        
        resp, err := handler(ctx, req)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        }
        
        return resp, err
    }
}

// UnaryClientInterceptor gRPC 客户端拦截器
func UnaryClientInterceptor() grpc.UnaryClientInterceptor {
    tracer := otel.Tracer("grpc-client")
    
    return func(
        ctx context.Context,
        method string,
        req, reply interface{},
        cc *grpc.ClientConn,
        invoker grpc.UnaryInvoker,
        opts ...grpc.CallOption,
    ) error {
        ctx, span := tracer.Start(ctx, method,
            trace.WithSpanKind(trace.SpanKindClient),
        )
        defer span.End()
        
        span.SetAttributes(
            semconv.RPCMethod(method),
            semconv.RPCSystem("grpc"),
        )
        
        err := invoker(ctx, method, req, reply, cc, opts...)
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        }
        
        return err
    }
}
```

---

## 6. 构建与部署

### 6.1 Workspace 构建

```makefile
# Makefile
.PHONY: build-all build-services build-libs

# 构建所有服务
build-all: build-libs build-services

# 构建共享库
build-libs:
 @echo "Building shared libraries..."
 @cd libs/tracing && go build -v ./...
 @cd libs/config && go build -v ./...

# 构建所有服务
build-services:
 @echo "Building services..."
 @cd services/api-gateway && go build -o ../../bin/api-gateway
 @cd services/user-service && go build -o ../../bin/user-service
 @cd services/order-service && go build -o ../../bin/order-service

# 测试所有模块
test-all:
 go test -v ./...

# 清理
clean:
 rm -rf bin/
```

### 6.2 CI/CD 集成

```yaml
# .github/workflows/ci.yml
name: CI

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - uses: actions/setup-go@v4
        with:
          go-version: '1.25.1'
      
      # 缓存 Go modules
      - uses: actions/cache@v3
        with:
          path: |
            ~/.cache/go-build
            ~/go/pkg/mod
          key: ${{ runner.os }}-go-${{ hashFiles('**/go.sum') }}
      
      # 测试所有模块
      - name: Test
        run: go test -v ./...
      
      # 构建所有服务
      - name: Build
        run: make build-all
      
      # 上传构建产物
      - uses: actions/upload-artifact@v3
        with:
          name: binaries
          path: bin/
```

### 6.3 容器化部署

```dockerfile
# services/api-gateway/Dockerfile
FROM golang:1.25.1 AS builder

WORKDIR /workspace

# 复制 go.work 和所有模块
COPY go.work go.work.sum ./
COPY libs/ ./libs/
COPY services/api-gateway/ ./services/api-gateway/

# 构建
RUN cd services/api-gateway && \
    CGO_ENABLED=0 GOOS=linux go build -o /app/api-gateway

# 最终镜像
FROM alpine:3.19

WORKDIR /app

COPY --from=builder /app/api-gateway .

CMD ["./api-gateway"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  api-gateway:
    build:
      context: .
      dockerfile: services/api-gateway/Dockerfile
    ports:
      - "8080:8080"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
  
  user-service:
    build:
      context: .
      dockerfile: services/user-service/Dockerfile
    ports:
      - "8081:8081"
    environment:
      - OTEL_EXPORTER_OTLP_ENDPOINT=otel-collector:4317
  
  otel-collector:
    image: otel/opentelemetry-collector:latest
    ports:
      - "4317:4317"
    volumes:
      - ./configs/otel-collector-config.yaml:/etc/otel-collector-config.yaml
    command: ["--config=/etc/otel-collector-config.yaml"]
```

---

## 7. 依赖管理

### 7.1 本地依赖覆盖

```go
// go.work - 使用本地依赖
go 1.25.1

use (
    ./services/api-gateway
    ./services/user-service
    ./libs/tracing
)

// go.work 会自动覆盖 go.mod 中的远程依赖
// 使得本地修改立即生效,无需手动 replace
```

### 7.2 依赖版本同步

```bash
# scripts/sync-deps.sh - 同步依赖版本
#!/bin/bash

OTEL_VERSION="v1.32.0"

# 更新所有模块的 OpenTelemetry 依赖
for module in services/*/go.mod libs/*/go.mod; do
    cd $(dirname $module)
    
    echo "Updating $module..."
    go get -u go.opentelemetry.io/otel@${OTEL_VERSION}
    go get -u go.opentelemetry.io/otel/sdk@${OTEL_VERSION}
    go mod tidy
    
    cd -
done

echo "Dependencies synchronized!"
```

### 7.3 依赖冲突解决

```bash
# 查看依赖版本冲突
go work vendor
go mod graph | grep "go.opentelemetry.io/otel"

# 强制统一版本
go get -u go.opentelemetry.io/otel@v1.32.0
```

---

## 8. 测试策略

### 8.1 跨模块测试

```go
// tests/integration_test.go - 跨模块集成测试
package tests

import (
    "context"
    "testing"
    
    "github.com/myorg/api-gateway/handlers"
    "github.com/myorg/tracing"
    "github.com/myorg/user-service/client"
)

func TestCrossModuleTracing(t *testing.T) {
    ctx := context.Background()
    
    // 初始化追踪
    tp, err := tracing.InitTracer(ctx, tracing.Config{
        ServiceName:  "integration-test",
        SamplingRate: 1.0, // 测试时 100% 采样
    })
    if err != nil {
        t.Fatal(err)
    }
    defer tp.Shutdown(ctx)
    
    // 测试 API Gateway 调用 User Service
    userClient := client.NewUserClient("http://localhost:8081")
    handler := handlers.NewUserHandler(userClient)
    
    ctx, span := tracing.GetTracer("test").Start(ctx, "test-cross-module")
    defer span.End()
    
    user, err := handler.GetUser(ctx, 1)
    if err != nil {
        t.Errorf("GetUser failed: %v", err)
    }
    
    if user == nil {
        t.Error("Expected user, got nil")
    }
}
```

### 8.2 集成测试

```go
// tests/suite_test.go - 测试套件
package tests

import (
    "context"
    "testing"
    
    "github.com/stretchr/testify/suite"
)

type IntegrationTestSuite struct {
    suite.Suite
    ctx context.Context
    tp  *sdktrace.TracerProvider
}

func (s *IntegrationTestSuite) SetupSuite() {
    s.ctx = context.Background()
    
    // 启动测试追踪
    tp, err := tracing.InitTracer(s.ctx, tracing.Config{
        ServiceName: "test-suite",
        SamplingRate: 1.0,
    })
    s.Require().NoError(err)
    
    s.tp = tp
}

func (s *IntegrationTestSuite) TearDownSuite() {
    s.tp.Shutdown(s.ctx)
}

func (s *IntegrationTestSuite) TestServiceCommunication() {
    // 测试服务间通信
}

func TestIntegrationTestSuite(t *testing.T) {
    suite.Run(t, new(IntegrationTestSuite))
}
```

### 8.3 端到端测试

```go
// tests/e2e_test.go - 端到端测试
package tests

import (
    "context"
    "net/http"
    "testing"
    "time"
)

func TestE2E_UserFlow(t *testing.T) {
    ctx := context.Background()
    
    // 初始化追踪
    tp, _ := tracing.InitTracer(ctx, tracing.Config{
        ServiceName: "e2e-test",
        SamplingRate: 1.0,
    })
    defer tp.Shutdown(ctx)
    
    tracer := tracing.GetTracer("e2e-test")
    ctx, span := tracer.Start(ctx, "e2e-user-flow")
    defer span.End()
    
    client := &http.Client{Timeout: 10 * time.Second}
    
    // 1. 创建用户
    resp, err := client.Post("http://localhost:8080/users", "application/json",
        strings.NewReader(`{"username":"testuser"}`))
    if err != nil {
        t.Fatalf("Create user failed: %v", err)
    }
    resp.Body.Close()
    
    // 2. 获取用户
    resp, err = client.Get("http://localhost:8080/users/1")
    if err != nil {
        t.Fatalf("Get user failed: %v", err)
    }
    defer resp.Body.Close()
    
    if resp.StatusCode != http.StatusOK {
        t.Errorf("Expected status 200, got %d", resp.StatusCode)
    }
    
    // 验证追踪数据已生成
    span.AddEvent("e2e-test-complete")
}
```

---

## 9. 最佳实践

```markdown
## Workspace 最佳实践

### 1. 目录结构
- ✅ 按功能分组(services、libs、tools)
- ✅ 共享库独立模块
- ✅ 清晰的依赖关系

### 2. 依赖管理
- ✅ 使用 go.work 本地开发
- ✅ 定期同步依赖版本
- ✅ CI/CD 中不使用 go.work

### 3. 追踪集成
- ✅ 统一的追踪配置
- ✅ 共享追踪中间件
- ✅ Context 自动传播

### 4. 构建部署
- ✅ 多阶段 Docker 构建
- ✅ 缓存 Go modules
- ✅ 独立服务部署

### 5. 测试策略
- ✅ 单元测试 + 集成测试
- ✅ 跨模块测试
- ✅ E2E 测试覆盖
```

---

## 总结

本指南涵盖了 Go 1.25.1 Workspace 模式与 OTLP 集成:

1. **Workspace 基础**:创建、多模块管理、本地依赖
2. **Monorepo 架构**:结构设计、共享代码、版本控制
3. **跨模块追踪**:统一配置、Context 传播、分布式追踪
4. **共享追踪库**:通用工具、配置管理、追踪中间件
5. **构建部署**:Workspace 构建、CI/CD、容器化
6. **依赖管理**:本地覆盖、版本同步、冲突解决
7. **测试策略**:跨模块、集成、端到端测试
8. **最佳实践**:目录结构、依赖管理、追踪集成

通过 Workspace 模式,可实现 **高效的多模块开发** 和 **统一的追踪管理**。

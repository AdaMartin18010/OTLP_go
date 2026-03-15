# Go 编译优化与 OTLP 集成

## 目录

- [Go 编译优化与 OTLP 集成](#go-编译优化与-otlp-集成)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [编译优化架构](#编译优化架构)
  - [2. Build Tags 条件编译](#2-build-tags-条件编译)
    - [2.1 基础 Build Tags](#21-基础-build-tags)
    - [2.2 环境相关编译](#22-环境相关编译)
    - [2.3 追踪级别控制](#23-追踪级别控制)
  - [3. 编译时优化](#3-编译时优化)
    - [3.1 内联优化](#31-内联优化)
    - [3.2 逃逸分析](#32-逃逸分析)
    - [3.3 编译标志优化](#33-编译标志优化)
  - [4. PGO 性能引导优化](#4-pgo-性能引导优化)
    - [4.1 PGO 基础](#41-pgo-基础)
    - [4.2 Profile 收集](#42-profile-收集)
    - [4.3 PGO 与 OTLP 结合](#43-pgo-与-otlp-结合)
  - [5. 链接器优化](#5-链接器优化)
    - [5.1 符号表压缩](#51-符号表压缩)
    - [5.2 二进制大小优化](#52-二进制大小优化)
    - [5.3 动态链接与静态链接](#53-动态链接与静态链接)
  - [6. Go Module 优化](#6-go-module-优化)
    - [6.1 依赖管理](#61-依赖管理)
    - [6.2 Vendor 模式](#62-vendor-模式)
    - [6.3 Module 缓存优化](#63-module-缓存优化)
  - [7. 构建系统集成](#7-构建系统集成)
    - [7.1 Makefile 集成](#71-makefile-集成)
    - [7.2 CI/CD 构建优化](#72-cicd-构建优化)
    - [7.3 多平台交叉编译](#73-多平台交叉编译)
  - [8. 编译追踪](#8-编译追踪)
    - [8.1 编译时间追踪](#81-编译时间追踪)
    - [8.2 编译依赖分析](#82-编译依赖分析)
    - [8.3 增量编译优化](#83-增量编译优化)
  - [9. 生产部署优化](#9-生产部署优化)
  - [总结](#总结)

---

## 1. 概述

Go 编译优化对于生产环境性能至关重要。结合 OTLP,可以:

- **条件编译追踪**:根据环境启用/禁用追踪
- **性能优化**:通过 PGO 优化热路径
- **二进制优化**:减小部署包大小

本指南基于 **Go 1.25.1** 和 **OpenTelemetry v1.32.0**。

### 编译优化架构

```text
┌─────────────────────────────────────┐
│   Go 编译优化与 OTLP 集成            │
├─────────────────────────────────────┤
│  Build Tags  → 条件追踪              │
│  PGO         → 热路径优化            │
│  Linker      → 二进制优化            │
│  Modules     → 依赖管理              │
│  CI/CD       → 自动化构建追踪        │
└─────────────────────────────────────┘
```

---

## 2. Build Tags 条件编译

### 2.1 基础 Build Tags

```go
// tracer_dev.go
//go:build dev
// +build dev

package myapp

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// 开发环境:使用 stdout 导出器
func InitTracer() (*sdktrace.TracerProvider, error) {
    exporter, err := stdouttrace.New(stdouttrace.WithPrettyPrint())
    if err != nil {
        return nil, err
    }
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithSampler(sdktrace.AlwaysSample()), // 100% 采样
    )
    
    otel.SetTracerProvider(tp)
    
    return tp, nil
}
```

```go
// tracer_prod.go
//go:build !dev
// +build !dev

package myapp

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// 生产环境:使用 OTLP gRPC 导出器
func InitTracer() (*sdktrace.TracerProvider, error) {
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("otel-collector:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithSampler(sdktrace.TraceIDRatioBased(0.1)), // 10% 采样
    )
    
    otel.SetTracerProvider(tp)
    
    return tp, nil
}
```

```bash
# 开发环境编译
go build -tags dev -o myapp-dev

# 生产环境编译
go build -o myapp-prod
```

### 2.2 环境相关编译

```go
// config_local.go
//go:build local
// +build local

package config

const (
    TracingEnabled = true
    SamplingRate   = 1.0 // 100%
    ExporterType   = "stdout"
    LogLevel       = "debug"
)
```

```go
// config_staging.go
//go:build staging
// +build staging

package config

const (
    TracingEnabled = true
    SamplingRate   = 0.5 // 50%
    ExporterType   = "otlp"
    LogLevel       = "info"
)
```

```go
// config_production.go
//go:build production
// +build production

package config

const (
    TracingEnabled = true
    SamplingRate   = 0.1 // 10%
    ExporterType   = "otlp"
    LogLevel       = "warn"
)
```

### 2.3 追踪级别控制

```go
// tracing_noop.go
//go:build !tracing
// +build !tracing

package myapp

import (
    "context"
    
    "go.opentelemetry.io/otel/trace"
    "go.opentelemetry.io/otel/trace/noop"
)

// 禁用追踪:使用 NoOp Tracer(零开销)
func GetTracer(name string) trace.Tracer {
    return noop.NewTracerProvider().Tracer(name)
}

func TraceOperation(ctx context.Context, name string, fn func(context.Context) error) error {
    // 直接执行,无追踪
    return fn(ctx)
}
```

```go
// tracing_enabled.go
//go:build tracing
// +build tracing

package myapp

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// 启用追踪:使用真实 Tracer
func GetTracer(name string) trace.Tracer {
    return otel.Tracer(name)
}

func TraceOperation(ctx context.Context, name string, fn func(context.Context) error) error {
    ctx, span := GetTracer("myapp").Start(ctx, name)
    defer span.End()
    
    err := fn(ctx)
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
    }
    
    return err
}
```

```bash
# 启用追踪
go build -tags tracing -o myapp

# 禁用追踪(零开销)
go build -o myapp-no-trace
```

---

## 3. 编译时优化

### 3.1 内联优化

```go
// 使用 //go:inline 指令(Go 1.25.1 实验性)
//go:inline
func fastAdd(a, b int) int {
    return a + b
}

// 使用 //go:noinline 禁止内联(用于性能分析)
//go:noinline
func slowAdd(a, b int) int {
    return a + b
}

// 查看内联决策
// go build -gcflags="-m -m" main.go
```

```go
// OTLP 追踪中的内联优化
package tracing

import (
    "go.opentelemetry.io/otel/attribute"
)

// 内联友好:简单函数,编译器自动内联
func addAttribute(key string, value int) attribute.KeyValue {
    return attribute.Int(key, value)
}

// 热路径优化:使用内联减少函数调用开销
func recordEvent(span trace.Span, name string, attrs ...attribute.KeyValue) {
    // 编译器会尝试内联此函数
    span.AddEvent(name, trace.WithAttributes(attrs...))
}
```

### 3.2 逃逸分析

```go
// 逃逸分析示例
package optimization

import (
    "go.opentelemetry.io/otel/attribute"
)

// ❌ 逃逸到堆:返回指针
func createAttributesHeap() *[]attribute.KeyValue {
    attrs := []attribute.KeyValue{
        attribute.String("key1", "value1"),
        attribute.Int("key2", 42),
    }
    return &attrs // 逃逸到堆
}

// ✅ 栈上分配:返回值
func createAttributesStack() []attribute.KeyValue {
    attrs := []attribute.KeyValue{
        attribute.String("key1", "value1"),
        attribute.Int("key2", 42),
    }
    return attrs // 栈上分配
}

// ✅ 预分配容量,减少扩容逃逸
func createAttributesPrealloc(count int) []attribute.KeyValue {
    attrs := make([]attribute.KeyValue, 0, count) // 预分配
    
    for i := 0; i < count; i++ {
        attrs = append(attrs, attribute.Int("key", i))
    }
    
    return attrs
}

// 查看逃逸分析
// go build -gcflags="-m" optimization.go
```

### 3.3 编译标志优化

```go
// Makefile
.PHONY: build-dev build-prod

# 开发构建:包含调试信息
build-dev:
 go build -gcflags="all=-N -l" \
  -ldflags="-X main.Version=dev -X main.BuildTime=$(shell date -u +%Y-%m-%dT%H:%M:%SZ)" \
  -o bin/myapp-dev

# 生产构建:优化 + 压缩
build-prod:
 go build -trimpath \
  -ldflags="-s -w -X main.Version=$(VERSION) -X main.BuildTime=$(shell date -u +%Y-%m-%dT%H:%M:%SZ)" \
  -o bin/myapp

# PGO 优化构建
build-pgo:
 go build -pgo=cpu.pprof -o bin/myapp-pgo

# 说明:
# -gcflags="all=-N -l" : 禁用优化和内联(调试用)
# -trimpath          : 移除文件系统路径
# -ldflags="-s -w"   : 去除符号表和调试信息
# -pgo               : 启用 PGO 优化
```

---

## 4. PGO 性能引导优化

### 4.1 PGO 基础

```go
// PGO (Profile-Guided Optimization) 是 Go 1.20+ 的特性
// 通过运行时 Profile 优化编译

// 1. 收集 CPU Profile
// go run -pprof=cpu myapp

// 2. 使用 Profile 优化编译
// go build -pgo=cpu.pprof -o myapp-optimized
```

### 4.2 Profile 收集

```go
package main

import (
    "context"
    "os"
    "runtime/pprof"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// ProfiledApp 支持 PGO 的应用
type ProfiledApp struct {
    tracer     trace.Tracer
    cpuProfile *os.File
}

func NewProfiledApp() *ProfiledApp {
    return &ProfiledApp{
        tracer: otel.Tracer("profiled-app"),
    }
}

// StartProfiling 开始性能分析
func (pa *ProfiledApp) StartProfiling(filename string) error {
    f, err := os.Create(filename)
    if err != nil {
        return err
    }
    
    pa.cpuProfile = f
    
    if err := pprof.StartCPUProfile(f); err != nil {
        return err
    }
    
    return nil
}

// StopProfiling 停止性能分析
func (pa *ProfiledApp) StopProfiling() {
    pprof.StopCPUProfile()
    
    if pa.cpuProfile != nil {
        pa.cpuProfile.Close()
    }
}

// RunWithProfiling 运行应用并收集 Profile
func (pa *ProfiledApp) RunWithProfiling(ctx context.Context, duration time.Duration) error {
    ctx, span := pa.tracer.Start(ctx, "run-with-profiling")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int64("profiling.duration_sec", int64(duration.Seconds())),
    )
    
    // 开始 Profiling
    if err := pa.StartProfiling("cpu.pprof"); err != nil {
        span.RecordError(err)
        return err
    }
    defer pa.StopProfiling()
    
    // 运行应用负载(模拟)
    for start := time.Now(); time.Since(start) < duration; {
        // 模拟热路径操作
        pa.hotPath(ctx)
    }
    
    span.AddEvent("profiling-complete")
    
    return nil
}

// hotPath 热路径函数(PGO 会优化)
func (pa *ProfiledApp) hotPath(ctx context.Context) {
    ctx, span := pa.tracer.Start(ctx, "hot-path")
    defer span.End()
    
    // 模拟计算密集型操作
    sum := 0
    for i := 0; i < 10000; i++ {
        sum += i
    }
    
    span.SetAttributes(attribute.Int("result", sum))
}

// 使用示例
func main() {
    app := NewProfiledApp()
    
    ctx := context.Background()
    
    // 运行 30 秒收集 Profile
    if err := app.RunWithProfiling(ctx, 30*time.Second); err != nil {
        panic(err)
    }
    
    // Profile 已保存到 cpu.pprof
    // 使用 go build -pgo=cpu.pprof 重新编译优化
}
```

### 4.3 PGO 与 OTLP 结合

```go
// PGOTracer PGO 追踪器
type PGOTracer struct {
    tracer trace.Tracer
    meter  metric.Meter
    
    // Metrics
    hotPathCounter metric.Int64Counter
}

func NewPGOTracer() (*PGOTracer, error) {
    meter := otel.Meter("pgo-tracer")
    
    hotPathCounter, err := meter.Int64Counter(
        "pgo.hot_path_calls",
        metric.WithDescription("Number of hot path invocations"),
    )
    if err != nil {
        return nil, err
    }
    
    return &PGOTracer{
        tracer:         otel.Tracer("pgo-tracer"),
        meter:          meter,
        hotPathCounter: hotPathCounter,
    }, nil
}

// TraceHotPath 追踪热路径
func (pt *PGOTracer) TraceHotPath(ctx context.Context, name string, fn func() error) error {
    ctx, span := pt.tracer.Start(ctx, "hot-path."+name)
    defer span.End()
    
    // 记录调用次数
    pt.hotPathCounter.Add(ctx, 1, metric.WithAttributes(
        attribute.String("hot_path.name", name),
    ))
    
    // 标记为热路径(供 PGO 识别)
    span.SetAttributes(
        attribute.Bool("hot_path", true),
    )
    
    startTime := time.Now()
    err := fn()
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Float64("hot_path.duration_ms", float64(duration.Microseconds())/1000),
    )
    
    if err != nil {
        span.RecordError(err)
    }
    
    return err
}

// AnalyzeHotPaths 分析热路径
func (pt *PGOTracer) AnalyzeHotPaths(ctx context.Context) {
    ctx, span := pt.tracer.Start(ctx, "analyze-hot-paths")
    defer span.End()
    
    // 通过追踪数据识别热路径
    // 可以与 Profile 数据结合,优化编译
    
    span.AddEvent("hot-path-analysis-complete")
}
```

---

## 5. 链接器优化

### 5.1 符号表压缩

```bash
# 去除符号表和调试信息
go build -ldflags="-s -w" -o myapp

# -s: 去除符号表
# -w: 去除 DWARF 调试信息

# 对比二进制大小
ls -lh myapp*
# myapp-debug:    15MB (包含调试信息)
# myapp-stripped: 10MB (去除调试信息)
```

### 5.2 二进制大小优化

```go
// Makefile
.PHONY: build-minimal

build-minimal:
 # 1. 禁用 CGO(减少依赖)
 CGO_ENABLED=0 \
 # 2. 移除路径信息
 go build -trimpath \
 # 3. 去除调试信息
 -ldflags="-s -w" \
 # 4. 使用 UPX 压缩(可选)
 -o bin/myapp && \
 upx --best --lzma bin/myapp
```

```go
// 减少依赖导入
package minimal

// ❌ 导入整个包
import "go.opentelemetry.io/otel/sdk/trace"

// ✅ 仅导入需要的类型
import (
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/trace"
)

// 使用接口而非具体类型,减少依赖
type Tracer interface {
    Start(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span)
}
```

### 5.3 动态链接与静态链接

```bash
# 静态链接(默认,适合容器部署)
CGO_ENABLED=0 go build -o myapp-static

# 动态链接(较小,但需要运行时依赖)
CGO_ENABLED=1 go build -o myapp-dynamic

# 查看链接依赖
ldd myapp-static  # not a dynamic executable
ldd myapp-dynamic # libc.so.6 => /lib/x86_64-linux-gnu/libc.so.6
```

---

## 6. Go Module 优化

### 6.1 依赖管理

```go
// go.mod
module github.com/myorg/myapp

go 1.25.1

require (
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.32.0
    go.opentelemetry.io/otel/sdk v1.32.0
)

// 使用 replace 指向本地版本(开发用)
replace go.opentelemetry.io/otel => ../otel-go
```

```bash
# 清理未使用的依赖
go mod tidy

# 更新依赖到最新版本
go get -u go.opentelemetry.io/otel@latest

# 查看依赖树
go mod graph

# 查看为什么需要某个依赖
go mod why go.opentelemetry.io/otel/sdk
```

### 6.2 Vendor 模式

```bash
# 创建 vendor 目录
go mod vendor

# 使用 vendor 编译(离线构建)
go build -mod=vendor -o myapp

# 验证 vendor 同步
go mod verify
```

```go
// Makefile
.PHONY: vendor-sync

vendor-sync:
 go mod tidy
 go mod vendor
 go mod verify
```

### 6.3 Module 缓存优化

```bash
# 查看 Module 缓存
go env GOMODCACHE
# /home/user/go/pkg/mod

# 清理缓存
go clean -modcache

# CI/CD 缓存优化
# .github/workflows/build.yml
```

```yaml
# GitHub Actions 示例
name: Build

on: [push]

jobs:
  build:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v3
      
      # 缓存 Go Module
      - uses: actions/cache@v3
        with:
          path: ~/go/pkg/mod
          key: ${{ runner.os }}-go-${{ hashFiles('**/go.sum') }}
          restore-keys: |
            ${{ runner.os }}-go-
      
      - name: Build
        run: go build -v ./...
```

---

## 7. 构建系统集成

### 7.1 Makefile 集成

```makefile
# Makefile
.PHONY: all build clean test

# 变量
VERSION ?= $(shell git describe --tags --always --dirty)
BUILD_TIME := $(shell date -u +%Y-%m-%dT%H:%M:%SZ)
LDFLAGS := -X main.Version=$(VERSION) -X main.BuildTime=$(BUILD_TIME)

# 默认目标
all: test build

# 构建
build:
 @echo "Building version $(VERSION)..."
 go build -ldflags="$(LDFLAGS)" -o bin/myapp

# 开发构建(带调试)
build-debug:
 go build -gcflags="all=-N -l" -ldflags="$(LDFLAGS)" -o bin/myapp-debug

# 生产构建(优化)
build-prod:
 CGO_ENABLED=0 go build -trimpath \
  -ldflags="-s -w $(LDFLAGS)" \
  -o bin/myapp-prod

# PGO 优化构建
build-pgo: profile
 go build -pgo=cpu.pprof -ldflags="$(LDFLAGS)" -o bin/myapp-pgo

# 收集 Profile
profile:
 @echo "Collecting CPU profile..."
 go test -cpuprofile=cpu.pprof -bench=. ./...

# 测试
test:
 go test -v -cover ./...

# 清理
clean:
 rm -rf bin/ cpu.pprof

# 查看构建信息
info:
 @echo "Version: $(VERSION)"
 @echo "Build Time: $(BUILD_TIME)"
```

### 7.2 CI/CD 构建优化

```yaml
# .gitlab-ci.yml
stages:
  - test
  - build
  - deploy

variables:
  GOCACHE: $CI_PROJECT_DIR/.gocache
  GOMODCACHE: $CI_PROJECT_DIR/.gomodcache

# 缓存依赖
cache:
  paths:
    - .gocache
    - .gomodcache

# 测试
test:
  stage: test
  image: golang:1.25.1
  script:
    - go test -v -cover ./...
  only:
    - merge_requests
    - main

# 构建
build:
  stage: build
  image: golang:1.25.1
  script:
    - make build-prod
    - ls -lh bin/myapp-prod
  artifacts:
    paths:
      - bin/myapp-prod
  only:
    - tags

# 部署
deploy:
  stage: deploy
  script:
    - docker build -t myapp:$CI_COMMIT_TAG .
    - docker push myapp:$CI_COMMIT_TAG
  only:
    - tags
```

### 7.3 多平台交叉编译

```makefile
# 多平台编译
.PHONY: build-all

PLATFORMS := linux/amd64 linux/arm64 darwin/amd64 darwin/arm64 windows/amd64

build-all: $(PLATFORMS)

$(PLATFORMS):
 @echo "Building for $@..."
 @mkdir -p bin/$@
 GOOS=$(word 1,$(subst /, ,$@)) GOARCH=$(word 2,$(subst /, ,$@)) \
 go build -ldflags="$(LDFLAGS)" \
 -o bin/$@/myapp$(if $(findstring windows,$@),.exe,)

# 使用
# make build-all
# 输出:
# bin/linux/amd64/myapp
# bin/linux/arm64/myapp
# bin/darwin/amd64/myapp
# bin/darwin/arm64/myapp
# bin/windows/amd64/myapp.exe
```

---

## 8. 编译追踪

### 8.1 编译时间追踪

```go
// BuildTracer 编译追踪器
type BuildTracer struct {
    tracer trace.Tracer
}

func NewBuildTracer() *BuildTracer {
    return &BuildTracer{
        tracer: otel.Tracer("build-tracer"),
    }
}

// TraceBuild 追踪编译过程
func (bt *BuildTracer) TraceBuild(ctx context.Context, buildCmd string) error {
    ctx, span := bt.tracer.Start(ctx, "go-build")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("build.command", buildCmd),
    )
    
    startTime := time.Now()
    
    // 执行编译
    cmd := exec.CommandContext(ctx, "sh", "-c", buildCmd)
    output, err := cmd.CombinedOutput()
    
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Float64("build.duration_sec", duration.Seconds()),
        attribute.Int("build.output_size", len(output)),
    )
    
    if err != nil {
        span.RecordError(err)
        span.SetAttributes(attribute.String("build.output", string(output)))
        return err
    }
    
    span.SetStatus(codes.Ok, "build successful")
    
    return nil
}

// 使用示例
func main() {
    tracer := NewBuildTracer()
    
    ctx := context.Background()
    
    // 追踪编译
    err := tracer.TraceBuild(ctx, "go build -o myapp")
    if err != nil {
        fmt.Printf("Build failed: %v\n", err)
    }
}
```

### 8.2 编译依赖分析

```go
// DependencyAnalyzer 依赖分析器
type DependencyAnalyzer struct {
    tracer trace.Tracer
}

func NewDependencyAnalyzer() *DependencyAnalyzer {
    return &DependencyAnalyzer{
        tracer: otel.Tracer("dependency-analyzer"),
    }
}

// AnalyzeDependencies 分析依赖
func (da *DependencyAnalyzer) AnalyzeDependencies(ctx context.Context) error {
    ctx, span := da.tracer.Start(ctx, "analyze-dependencies")
    defer span.End()
    
    // 执行 go mod graph
    cmd := exec.CommandContext(ctx, "go", "mod", "graph")
    output, err := cmd.Output()
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    // 解析依赖图
    lines := strings.Split(string(output), "\n")
    
    span.SetAttributes(
        attribute.Int("dependencies.total_edges", len(lines)),
    )
    
    // 统计依赖
    deps := make(map[string]int)
    for _, line := range lines {
        parts := strings.Fields(line)
        if len(parts) == 2 {
            deps[parts[1]]++
        }
    }
    
    span.SetAttributes(
        attribute.Int("dependencies.unique_count", len(deps)),
    )
    
    // 记录前 10 个依赖
    type depCount struct {
        name  string
        count int
    }
    
    var topDeps []depCount
    for name, count := range deps {
        topDeps = append(topDeps, depCount{name, count})
    }
    
    sort.Slice(topDeps, func(i, j int) bool {
        return topDeps[i].count > topDeps[j].count
    })
    
    for i, dep := range topDeps {
        if i >= 10 {
            break
        }
        
        span.AddEvent("top-dependency", trace.WithAttributes(
            attribute.Int("rank", i+1),
            attribute.String("name", dep.name),
            attribute.Int("usage_count", dep.count),
        ))
    }
    
    return nil
}
```

### 8.3 增量编译优化

```bash
# 启用增量编译缓存
export GOCACHE=$(pwd)/.gocache

# 查看缓存统计
go clean -cache -n

# 并行编译
go build -p 8  # 使用 8 个并行任务
```

---

## 9. 生产部署优化

```dockerfile
# Dockerfile - 多阶段构建
FROM golang:1.25.1 AS builder

WORKDIR /app

# 复制依赖文件
COPY go.mod go.sum ./
RUN go mod download

# 复制源代码
COPY . .

# 编译优化版本
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 \
    go build -trimpath \
    -ldflags="-s -w -X main.Version=${VERSION}" \
    -o myapp

# 最终镜像:使用 scratch 或 alpine
FROM alpine:3.19

# 安装 CA 证书(HTTPS 需要)
RUN apk --no-cache add ca-certificates

WORKDIR /app

# 复制编译后的二进制
COPY --from=builder /app/myapp .

# 运行
CMD ["./myapp"]
```

```bash
# 构建 Docker 镜像
docker build --build-arg VERSION=v1.0.0 -t myapp:v1.0.0 .

# 查看镜像大小
docker images myapp
# REPOSITORY   TAG       SIZE
# myapp        v1.0.0    15MB  (使用 alpine)
# myapp-scratch v1.0.0   10MB  (使用 scratch)
```

---

## 总结

本指南涵盖了 Go 1.25.1 编译优化与 OTLP 集成:

1. **Build Tags**:条件编译、环境配置、追踪级别控制
2. **编译优化**:内联、逃逸分析、编译标志
3. **PGO**:Profile 收集、性能引导优化、热路径优化
4. **链接器**:符号表压缩、二进制优化、链接模式
5. **Go Module**:依赖管理、Vendor 模式、缓存优化
6. **构建系统**:Makefile、CI/CD、交叉编译
7. **编译追踪**:时间追踪、依赖分析、增量编译
8. **生产部署**:Docker 多阶段构建、镜像优化

通过编译优化,可实现 **更小的二进制**、**更快的执行速度** 和 **更低的资源消耗**。

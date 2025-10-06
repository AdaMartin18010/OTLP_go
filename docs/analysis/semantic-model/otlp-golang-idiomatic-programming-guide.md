# OTLP Golang 编程惯用法与规范指南

**版本**: 1.0.0  
**日期**: 2025-10-06  
**状态**: ✅ 完整

---

## 目录

- [OTLP Golang 编程惯用法与规范指南](#otlp-golang-编程惯用法与规范指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是惯用法 (Idioms)](#11-什么是惯用法-idioms)
    - [1.2 为什么需要惯用法](#12-为什么需要惯用法)
  - [2. 核心惯用法](#2-核心惯用法)
    - [2.1 Tracer 初始化惯用法](#21-tracer-初始化惯用法)
      - [惯用法 1: 使用全局 TracerProvider](#惯用法-1-使用全局-tracerprovider)
      - [惯用法 2: 使用 sync.Once 确保单次初始化](#惯用法-2-使用-synconce-确保单次初始化)
    - [2.2 Span 生命周期惯用法](#22-span-生命周期惯用法)
      - [惯用法 3: 始终使用 defer span.End()](#惯用法-3-始终使用-defer-spanend)
      - [惯用法 4: 使用命名返回值记录错误](#惯用法-4-使用命名返回值记录错误)
    - [2.3 Context 传播惯用法](#23-context-传播惯用法)
      - [惯用法 5: Context 作为第一个参数](#惯用法-5-context-作为第一个参数)
      - [惯用法 6: 不要在结构体中存储 Context](#惯用法-6-不要在结构体中存储-context)
    - [2.4 错误处理惯用法](#24-错误处理惯用法)
      - [惯用法 7: 记录错误到 Span](#惯用法-7-记录错误到-span)
      - [惯用法 8: 使用 errors.Is 和 errors.As](#惯用法-8-使用-errorsis-和-errorsas)
    - [2.5 属性设置惯用法](#25-属性设置惯用法)
      - [惯用法 9: 使用语义约定](#惯用法-9-使用语义约定)
      - [惯用法 10: 批量设置属性](#惯用法-10-批量设置属性)
  - [3. 高级惯用法](#3-高级惯用法)
    - [3.1 Span 链接惯用法](#31-span-链接惯用法)
      - [惯用法 11: 链接相关的 Span](#惯用法-11-链接相关的-span)
    - [3.2 Span 事件惯用法](#32-span-事件惯用法)
      - [惯用法 12: 记录重要事件](#惯用法-12-记录重要事件)
    - [3.3 批量操作惯用法](#33-批量操作惯用法)
      - [惯用法 13: 使用 SpanContext 传播](#惯用法-13-使用-spancontext-传播)
    - [3.4 采样决策惯用法](#34-采样决策惯用法)
      - [惯用法 14: 基于条件的采样](#惯用法-14-基于条件的采样)
  - [4. 性能优化惯用法](#4-性能优化惯用法)
    - [4.1 对象池化惯用法](#41-对象池化惯用法)
      - [惯用法 15: 使用 sync.Pool 复用对象](#惯用法-15-使用-syncpool-复用对象)
    - [4.2 零分配惯用法](#42-零分配惯用法)
      - [惯用法 16: 避免不必要的分配](#惯用法-16-避免不必要的分配)
    - [4.3 批处理惯用法](#43-批处理惯用法)
      - [惯用法 17: 批量导出 Span](#惯用法-17-批量导出-span)
  - [5. 并发编程惯用法](#5-并发编程惯用法)
    - [5.1 Goroutine 安全惯用法](#51-goroutine-安全惯用法)
      - [惯用法 18: 使用 Mutex 保护共享状态](#惯用法-18-使用-mutex-保护共享状态)
    - [5.2 Channel 使用惯用法](#52-channel-使用惯用法)
      - [惯用法 19: 使用 Channel 传递 Span](#惯用法-19-使用-channel-传递-span)
    - [5.3 同步原语惯用法](#53-同步原语惯用法)
      - [惯用法 20: 使用 WaitGroup 等待完成](#惯用法-20-使用-waitgroup-等待完成)
  - [6. 测试惯用法](#6-测试惯用法)
    - [6.1 单元测试惯用法](#61-单元测试惯用法)
      - [惯用法 21: 使用 InMemoryExporter 测试](#惯用法-21-使用-inmemoryexporter-测试)
    - [6.2 集成测试惯用法](#62-集成测试惯用法)
      - [惯用法 22: 使用测试容器](#惯用法-22-使用测试容器)
    - [6.3 基准测试惯用法](#63-基准测试惯用法)
      - [惯用法 23: 基准测试 Span 创建](#惯用法-23-基准测试-span-创建)
  - [7. 反模式与陷阱](#7-反模式与陷阱)
    - [7.1 常见反模式](#71-常见反模式)
      - [反模式 1: 忘记调用 span.End()](#反模式-1-忘记调用-spanend)
      - [反模式 2: 过度使用 Span](#反模式-2-过度使用-span)
    - [7.2 性能陷阱](#72-性能陷阱)
      - [陷阱 1: 在循环中创建 Span](#陷阱-1-在循环中创建-span)
    - [7.3 并发陷阱](#73-并发陷阱)
      - [陷阱 2: 共享 Span 跨 Goroutine](#陷阱-2-共享-span-跨-goroutine)
  - [8. 代码风格规范](#8-代码风格规范)
    - [8.1 命名规范](#81-命名规范)
      - [规范 1: Span 名称命名](#规范-1-span-名称命名)
    - [8.2 注释规范](#82-注释规范)
      - [规范 2: 添加有意义的注释](#规范-2-添加有意义的注释)
    - [8.3 错误处理规范](#83-错误处理规范)
      - [规范 3: 一致的错误处理](#规范-3-一致的错误处理)
  - [9. 参考文献](#9-参考文献)

---

## 1. 概述

### 1.1 什么是惯用法 (Idioms)

**惯用法**是指在特定编程语言和领域中,被广泛接受和使用的编程模式和实践。对于 OTLP Golang 编程:

- **语言惯用法**: 符合 Go 语言习惯的代码风格
- **领域惯用法**: 符合 OpenTelemetry 最佳实践的使用模式
- **性能惯用法**: 高效的资源使用和优化技巧

### 1.2 为什么需要惯用法

1. **可读性**: 代码更容易被其他开发者理解
2. **可维护性**: 遵循统一的模式,降低维护成本
3. **性能**: 避免常见的性能陷阱
4. **正确性**: 减少错误和 bug
5. **团队协作**: 统一的代码风格提高协作效率

---

## 2. 核心惯用法

### 2.1 Tracer 初始化惯用法

#### 惯用法 1: 使用全局 TracerProvider

**✅ 推荐写法**:

```go
package main

import (
    "context"
    "log"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
)

// 初始化函数
func initTracer() func() {
    ctx := context.Background()
    
    // 1. 创建 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("my-service"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        log.Fatalf("failed to create resource: %v", err)
    }
    
    // 2. 创建 Exporter
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatalf("failed to create exporter: %v", err)
    }
    
    // 3. 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithResource(res),
        trace.WithBatcher(exporter),
    )
    
    // 4. 设置全局 TracerProvider
    otel.SetTracerProvider(tp)
    
    // 5. 返回清理函数
    return func() {
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("failed to shutdown tracer: %v", err)
        }
    }
}

func main() {
    // 初始化并获取清理函数
    cleanup := initTracer()
    defer cleanup()
    
    // 使用全局 Tracer
    tracer := otel.Tracer("my-component")
    
    ctx, span := tracer.Start(context.Background(), "main")
    defer span.End()
    
    // 业务逻辑
}
```

**❌ 不推荐写法**:

```go
// 不推荐: 每次都创建新的 TracerProvider
func doWork() {
    tp := trace.NewTracerProvider(...) // 错误: 资源泄漏
    tracer := tp.Tracer("component")
    // ...
    // 忘记调用 tp.Shutdown()
}

// 不推荐: 传递 TracerProvider
func doWork(tp *trace.TracerProvider) {
    tracer := tp.Tracer("component")
    // ...
}
```

#### 惯用法 2: 使用 sync.Once 确保单次初始化

**✅ 推荐写法**:

```go
var (
    tracerProvider *trace.TracerProvider
    tracerOnce     sync.Once
)

func getTracerProvider() *trace.TracerProvider {
    tracerOnce.Do(func() {
        // 初始化逻辑
        tracerProvider = initTracerProvider()
    })
    return tracerProvider
}

func initTracerProvider() *trace.TracerProvider {
    // 创建 TracerProvider
    // ...
    return tp
}
```

### 2.2 Span 生命周期惯用法

#### 惯用法 3: 始终使用 defer span.End()

**✅ 推荐写法**:

```go
func processRequest(ctx context.Context, req *Request) error {
    ctx, span := tracer.Start(ctx, "processRequest")
    defer span.End() // 确保 Span 总是被结束
    
    // 业务逻辑
    if err := validate(req); err != nil {
        return err // Span 会被自动结束
    }
    
    result, err := process(ctx, req)
    if err != nil {
        return err // Span 会被自动结束
    }
    
    return save(ctx, result) // Span 会被自动结束
}
```

**❌ 不推荐写法**:

```go
// 不推荐: 手动调用 span.End()
func processRequest(ctx context.Context, req *Request) error {
    ctx, span := tracer.Start(ctx, "processRequest")
    
    if err := validate(req); err != nil {
        span.End() // 容易忘记
        return err
    }
    
    result, err := process(ctx, req)
    if err != nil {
        span.End() // 重复代码
        return err
    }
    
    err = save(ctx, result)
    span.End() // 容易忘记
    return err
}
```

#### 惯用法 4: 使用命名返回值记录错误

**✅ 推荐写法**:

```go
func processRequest(ctx context.Context, req *Request) (err error) {
    ctx, span := tracer.Start(ctx, "processRequest")
    defer func() {
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        }
        span.End()
    }()
    
    // 业务逻辑
    return doWork(ctx, req)
}
```

### 2.3 Context 传播惯用法

#### 惯用法 5: Context 作为第一个参数

**✅ 推荐写法**:

```go
// 正确: Context 作为第一个参数
func fetchUser(ctx context.Context, userID string) (*User, error) {
    ctx, span := tracer.Start(ctx, "fetchUser")
    defer span.End()
    
    span.SetAttributes(attribute.String("user.id", userID))
    
    // 查询数据库
    return db.Query(ctx, "SELECT * FROM users WHERE id = ?", userID)
}

// 调用时传递 Context
func handleRequest(ctx context.Context, req *Request) {
    user, err := fetchUser(ctx, req.UserID)
    // ...
}
```

**❌ 不推荐写法**:

```go
// 错误: Context 不是第一个参数
func fetchUser(userID string, ctx context.Context) (*User, error) {
    // ...
}

// 错误: 没有 Context 参数
func fetchUser(userID string) (*User, error) {
    // 无法传播追踪上下文
    // ...
}
```

#### 惯用法 6: 不要在结构体中存储 Context

**✅ 推荐写法**:

```go
type UserService struct {
    db     *sql.DB
    tracer trace.Tracer
}

func (s *UserService) GetUser(ctx context.Context, userID string) (*User, error) {
    ctx, span := s.tracer.Start(ctx, "GetUser")
    defer span.End()
    
    // 使用参数中的 Context
    return s.db.QueryContext(ctx, "SELECT * FROM users WHERE id = ?", userID)
}
```

**❌ 不推荐写法**:

```go
// 错误: 在结构体中存储 Context
type UserService struct {
    ctx    context.Context // 不要这样做!
    db     *sql.DB
    tracer trace.Tracer
}

func (s *UserService) GetUser(userID string) (*User, error) {
    // 使用结构体中的 Context (错误)
    return s.db.QueryContext(s.ctx, "SELECT * FROM users WHERE id = ?", userID)
}
```

### 2.4 错误处理惯用法

#### 惯用法 7: 记录错误到 Span

**✅ 推荐写法**:

```go
func processOrder(ctx context.Context, order *Order) (err error) {
    ctx, span := tracer.Start(ctx, "processOrder")
    defer func() {
        if err != nil {
            // 记录错误
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            
            // 添加错误相关属性
            span.SetAttributes(
                attribute.String("error.type", fmt.Sprintf("%T", err)),
                attribute.Bool("order.failed", true),
            )
        }
        span.End()
    }()
    
    // 业务逻辑
    if err := validateOrder(order); err != nil {
        return fmt.Errorf("validation failed: %w", err)
    }
    
    return saveOrder(ctx, order)
}
```

#### 惯用法 8: 使用 errors.Is 和 errors.As

**✅ 推荐写法**:

```go
func handleError(ctx context.Context, err error) {
    ctx, span := tracer.Start(ctx, "handleError")
    defer span.End()
    
    // 使用 errors.Is 检查错误类型
    if errors.Is(err, sql.ErrNoRows) {
        span.SetAttributes(attribute.String("error.kind", "not_found"))
        return
    }
    
    // 使用 errors.As 提取错误
    var netErr *net.OpError
    if errors.As(err, &netErr) {
        span.SetAttributes(
            attribute.String("error.kind", "network"),
            attribute.String("error.op", netErr.Op),
        )
        return
    }
    
    span.RecordError(err)
}
```

### 2.5 属性设置惯用法

#### 惯用法 9: 使用语义约定

**✅ 推荐写法**:

```go
import (
    "go.opentelemetry.io/otel/attribute"
    semconv "go.opentelemetry.io/otel/semconv/v1.17.0"
)

func handleHTTPRequest(ctx context.Context, req *http.Request) {
    ctx, span := tracer.Start(ctx, "handleHTTPRequest")
    defer span.End()
    
    // 使用语义约定常量
    span.SetAttributes(
        semconv.HTTPMethod(req.Method),
        semconv.HTTPTarget(req.URL.Path),
        semconv.HTTPScheme(req.URL.Scheme),
        semconv.HTTPUserAgent(req.UserAgent()),
    )
    
    // 业务逻辑
}
```

**❌ 不推荐写法**:

```go
// 不推荐: 硬编码属性名
func handleHTTPRequest(ctx context.Context, req *http.Request) {
    ctx, span := tracer.Start(ctx, "handleHTTPRequest")
    defer span.End()
    
    // 硬编码属性名 (容易拼写错误)
    span.SetAttributes(
        attribute.String("http.method", req.Method),
        attribute.String("http.target", req.URL.Path),
        attribute.String("http.scheme", req.URL.Scheme),
    )
}
```

#### 惯用法 10: 批量设置属性

**✅ 推荐写法**:

```go
func processUser(ctx context.Context, user *User) {
    ctx, span := tracer.Start(ctx, "processUser")
    defer span.End()
    
    // 批量设置属性 (一次调用)
    span.SetAttributes(
        attribute.String("user.id", user.ID),
        attribute.String("user.name", user.Name),
        attribute.String("user.email", user.Email),
        attribute.Int("user.age", user.Age),
        attribute.Bool("user.premium", user.IsPremium),
    )
}
```

**❌ 不推荐写法**:

```go
// 不推荐: 多次调用 SetAttributes
func processUser(ctx context.Context, user *User) {
    ctx, span := tracer.Start(ctx, "processUser")
    defer span.End()
    
    // 多次调用 (性能较差)
    span.SetAttributes(attribute.String("user.id", user.ID))
    span.SetAttributes(attribute.String("user.name", user.Name))
    span.SetAttributes(attribute.String("user.email", user.Email))
    span.SetAttributes(attribute.Int("user.age", user.Age))
    span.SetAttributes(attribute.Bool("user.premium", user.IsPremium))
}
```

---

## 3. 高级惯用法

### 3.1 Span 链接惯用法

#### 惯用法 11: 链接相关的 Span

**✅ 推荐写法**:

```go
func processBatch(ctx context.Context, items []Item) error {
    ctx, span := tracer.Start(ctx, "processBatch")
    defer span.End()
    
    // 收集所有子 Span 的 SpanContext
    var links []trace.Link
    
    for _, item := range items {
        itemCtx, itemSpan := tracer.Start(ctx, "processItem")
        
        // 添加链接
        links = append(links, trace.Link{
            SpanContext: itemSpan.SpanContext(),
            Attributes: []attribute.KeyValue{
                attribute.String("item.id", item.ID),
            },
        })
        
        processItem(itemCtx, item)
        itemSpan.End()
    }
    
    // 创建汇总 Span 并链接所有子 Span
    _, summarySpan := tracer.Start(ctx, "batchSummary",
        trace.WithLinks(links...),
    )
    defer summarySpan.End()
    
    summarySpan.SetAttributes(
        attribute.Int("batch.size", len(items)),
        attribute.Int("batch.links", len(links)),
    )
    
    return nil
}
```

### 3.2 Span 事件惯用法

#### 惯用法 12: 记录重要事件

**✅ 推荐写法**:

```go
func processPayment(ctx context.Context, payment *Payment) error {
    ctx, span := tracer.Start(ctx, "processPayment")
    defer span.End()
    
    // 记录开始事件
    span.AddEvent("payment.started",
        trace.WithAttributes(
            attribute.String("payment.id", payment.ID),
            attribute.Float64("payment.amount", payment.Amount),
        ),
    )
    
    // 验证支付
    if err := validatePayment(payment); err != nil {
        span.AddEvent("payment.validation_failed",
            trace.WithAttributes(
                attribute.String("error", err.Error()),
            ),
        )
        return err
    }
    
    span.AddEvent("payment.validated")
    
    // 处理支付
    if err := chargeCard(ctx, payment); err != nil {
        span.AddEvent("payment.charge_failed",
            trace.WithAttributes(
                attribute.String("error", err.Error()),
            ),
        )
        return err
    }
    
    span.AddEvent("payment.completed",
        trace.WithAttributes(
            attribute.String("transaction.id", payment.TransactionID),
        ),
    )
    
    return nil
}
```

### 3.3 批量操作惯用法

#### 惯用法 13: 使用 SpanContext 传播

**✅ 推荐写法**:

```go
func processBatchAsync(ctx context.Context, items []Item) error {
    ctx, span := tracer.Start(ctx, "processBatchAsync")
    defer span.End()
    
    // 提取 SpanContext 用于异步操作
    spanCtx := span.SpanContext()
    
    var wg sync.WaitGroup
    errCh := make(chan error, len(items))
    
    for _, item := range items {
        wg.Add(1)
        go func(item Item) {
            defer wg.Done()
            
            // 使用 SpanContext 创建新的 Context
            itemCtx := trace.ContextWithSpanContext(context.Background(), spanCtx)
            
            // 创建子 Span
            itemCtx, itemSpan := tracer.Start(itemCtx, "processItem")
            defer itemSpan.End()
            
            if err := processItem(itemCtx, item); err != nil {
                errCh <- err
            }
        }(item)
    }
    
    wg.Wait()
    close(errCh)
    
    // 收集错误
    for err := range errCh {
        span.RecordError(err)
    }
    
    return nil
}
```

### 3.4 采样决策惯用法

#### 惯用法 14: 基于条件的采样

**✅ 推荐写法**:

```go
// 自定义采样器
type ConditionalSampler struct {
    defaultSampler trace.Sampler
    highPriority   trace.Sampler
}

func (s *ConditionalSampler) ShouldSample(p trace.SamplingParameters) trace.SamplingResult {
    // 检查是否为高优先级请求
    for _, attr := range p.Attributes {
        if attr.Key == "priority" && attr.Value.AsString() == "high" {
            return s.highPriority.ShouldSample(p)
        }
    }
    
    return s.defaultSampler.ShouldSample(p)
}

func (s *ConditionalSampler) Description() string {
    return "ConditionalSampler"
}

// 使用自定义采样器
func initTracerWithSampler() *trace.TracerProvider {
    sampler := &ConditionalSampler{
        defaultSampler: trace.TraceIDRatioBased(0.1), // 10% 采样
        highPriority:   trace.AlwaysSample(),         // 100% 采样
    }
    
    return trace.NewTracerProvider(
        trace.WithSampler(sampler),
    )
}
```

---

## 4. 性能优化惯用法

### 4.1 对象池化惯用法

#### 惯用法 15: 使用 sync.Pool 复用对象

**✅ 推荐写法**:

```go
// Span 池
var spanPool = sync.Pool{
    New: func() interface{} {
        return &spanData{
            attributes: make([]attribute.KeyValue, 0, 16),
        }
    },
}

type spanData struct {
    attributes []attribute.KeyValue
}

func getSpanData() *spanData {
    return spanPool.Get().(*spanData)
}

func putSpanData(sd *spanData) {
    // 重置状态
    sd.attributes = sd.attributes[:0]
    spanPool.Put(sd)
}

// 使用示例
func processWithPool(ctx context.Context) {
    sd := getSpanData()
    defer putSpanData(sd)
    
    // 使用 spanData
    sd.attributes = append(sd.attributes,
        attribute.String("key", "value"),
    )
}
```

### 4.2 零分配惯用法

#### 惯用法 16: 避免不必要的分配

**✅ 推荐写法**:

```go
// 预分配 slice
func processItems(ctx context.Context, items []Item) {
    ctx, span := tracer.Start(ctx, "processItems")
    defer span.End()
    
    // 预分配足够的容量
    results := make([]Result, 0, len(items))
    
    for _, item := range items {
        result := processItem(ctx, item)
        results = append(results, result)
    }
}

// 复用 buffer
var bufferPool = sync.Pool{
    New: func() interface{} {
        return new(bytes.Buffer)
    },
}

func formatSpan(span trace.Span) string {
    buf := bufferPool.Get().(*bytes.Buffer)
    defer func() {
        buf.Reset()
        bufferPool.Put(buf)
    }()
    
    // 使用 buffer
    fmt.Fprintf(buf, "span: %s", span.SpanContext().SpanID())
    return buf.String()
}
```

### 4.3 批处理惯用法

#### 惯用法 17: 批量导出 Span

**✅ 推荐写法**:

```go
type BatchProcessor struct {
    exporter trace.SpanExporter
    batch    []trace.ReadOnlySpan
    batchMu  sync.Mutex
    timer    *time.Timer
    
    maxBatchSize int
    timeout      time.Duration
}

func (p *BatchProcessor) OnEnd(span trace.ReadOnlySpan) {
    p.batchMu.Lock()
    defer p.batchMu.Unlock()
    
    p.batch = append(p.batch, span)
    
    // 达到批次大小,立即导出
    if len(p.batch) >= p.maxBatchSize {
        p.flush()
        return
    }
    
    // 启动定时器
    if p.timer == nil {
        p.timer = time.AfterFunc(p.timeout, func() {
            p.batchMu.Lock()
            defer p.batchMu.Unlock()
            p.flush()
        })
    }
}

func (p *BatchProcessor) flush() {
    if len(p.batch) == 0 {
        return
    }
    
    // 导出批次
    if err := p.exporter.ExportSpans(context.Background(), p.batch); err != nil {
        log.Printf("failed to export spans: %v", err)
    }
    
    // 重置批次
    p.batch = p.batch[:0]
    
    // 停止定时器
    if p.timer != nil {
        p.timer.Stop()
        p.timer = nil
    }
}
```

---

## 5. 并发编程惯用法

### 5.1 Goroutine 安全惯用法

#### 惯用法 18: 使用 Mutex 保护共享状态

**✅ 推荐写法**:

```go
type SafeSpanCollector struct {
    mu    sync.RWMutex
    spans []trace.ReadOnlySpan
}

func (c *SafeSpanCollector) Add(span trace.ReadOnlySpan) {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    c.spans = append(c.spans, span)
}

func (c *SafeSpanCollector) GetAll() []trace.ReadOnlySpan {
    c.mu.RLock()
    defer c.mu.RUnlock()
    
    // 返回副本
    result := make([]trace.ReadOnlySpan, len(c.spans))
    copy(result, c.spans)
    return result
}
```

### 5.2 Channel 使用惯用法

#### 惯用法 19: 使用 Channel 传递 Span

**✅ 推荐写法**:

```go
func processSpansAsync(ctx context.Context, spans <-chan trace.ReadOnlySpan) {
    ctx, span := tracer.Start(ctx, "processSpansAsync")
    defer span.End()
    
    for {
        select {
        case s, ok := <-spans:
            if !ok {
                // Channel 已关闭
                return
            }
            processSpan(ctx, s)
            
        case <-ctx.Done():
            // Context 取消
            span.RecordError(ctx.Err())
            return
        }
    }
}

// 使用示例
func main() {
    spanCh := make(chan trace.ReadOnlySpan, 100)
    
    // 启动处理 goroutine
    go processSpansAsync(context.Background(), spanCh)
    
    // 发送 spans
    for _, span := range spans {
        spanCh <- span
    }
    
    // 关闭 channel
    close(spanCh)
}
```

### 5.3 同步原语惯用法

#### 惯用法 20: 使用 WaitGroup 等待完成

**✅ 推荐写法**:

```go
func processParallel(ctx context.Context, items []Item) error {
    ctx, span := tracer.Start(ctx, "processParallel")
    defer span.End()
    
    var wg sync.WaitGroup
    errCh := make(chan error, len(items))
    
    for _, item := range items {
        wg.Add(1)
        go func(item Item) {
            defer wg.Done()
            
            itemCtx, itemSpan := tracer.Start(ctx, "processItem")
            defer itemSpan.End()
            
            if err := processItem(itemCtx, item); err != nil {
                errCh <- err
            }
        }(item)
    }
    
    // 等待所有 goroutine 完成
    wg.Wait()
    close(errCh)
    
    // 收集错误
    var errs []error
    for err := range errCh {
        errs = append(errs, err)
    }
    
    if len(errs) > 0 {
        span.RecordError(errs[0])
        return errs[0]
    }
    
    return nil
}
```

---

## 6. 测试惯用法

### 6.1 单元测试惯用法

#### 惯用法 21: 使用 InMemoryExporter 测试

**✅ 推荐写法**:

```go
func TestProcessRequest(t *testing.T) {
    // 创建内存导出器
    exporter := tracetest.NewInMemoryExporter()
    
    // 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithSyncer(exporter),
    )
    
    // 使用 TracerProvider
    tracer := tp.Tracer("test")
    
    ctx, span := tracer.Start(context.Background(), "test")
    span.SetAttributes(attribute.String("key", "value"))
    span.End()
    
    // 验证导出的 Span
    spans := exporter.GetSpans()
    require.Len(t, spans, 1)
    
    assert.Equal(t, "test", spans[0].Name())
    assert.Equal(t, "value", spans[0].Attributes()[0].Value.AsString())
}
```

### 6.2 集成测试惯用法

#### 惯用法 22: 使用测试容器

**✅ 推荐写法**:

```go
func TestWithCollector(t *testing.T) {
    // 启动 OTLP Collector 容器
    ctx := context.Background()
    req := testcontainers.ContainerRequest{
        Image:        "otel/opentelemetry-collector:latest",
        ExposedPorts: []string{"4317/tcp"},
        WaitingFor:   wait.ForListeningPort("4317/tcp"),
    }
    
    container, err := testcontainers.GenericContainer(ctx, testcontainers.GenericContainerRequest{
        ContainerRequest: req,
        Started:          true,
    })
    require.NoError(t, err)
    defer container.Terminate(ctx)
    
    // 获取端口
    endpoint, err := container.Endpoint(ctx, "")
    require.NoError(t, err)
    
    // 创建 Exporter
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint(endpoint),
        otlptracegrpc.WithInsecure(),
    )
    require.NoError(t, err)
    
    // 运行测试
    // ...
}
```

### 6.3 基准测试惯用法

#### 惯用法 23: 基准测试 Span 创建

**✅ 推荐写法**:

```go
func BenchmarkSpanCreation(b *testing.B) {
    // 创建 TracerProvider
    tp := trace.NewTracerProvider()
    tracer := tp.Tracer("benchmark")
    
    ctx := context.Background()
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        _, span := tracer.Start(ctx, "operation")
        span.End()
    }
}

func BenchmarkSpanWithAttributes(b *testing.B) {
    tp := trace.NewTracerProvider()
    tracer := tp.Tracer("benchmark")
    
    ctx := context.Background()
    attrs := []attribute.KeyValue{
        attribute.String("key1", "value1"),
        attribute.String("key2", "value2"),
        attribute.Int("key3", 123),
    }
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        _, span := tracer.Start(ctx, "operation")
        span.SetAttributes(attrs...)
        span.End()
    }
}
```

---

## 7. 反模式与陷阱

### 7.1 常见反模式

#### 反模式 1: 忘记调用 span.End()

**❌ 错误示例**:

```go
func badExample(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "operation")
    
    // 业务逻辑
    doWork(ctx)
    
    // 忘记调用 span.End() - 内存泄漏!
}
```

**✅ 正确示例**:

```go
func goodExample(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End() // 使用 defer 确保调用
    
    // 业务逻辑
    doWork(ctx)
}
```

#### 反模式 2: 过度使用 Span

**❌ 错误示例**:

```go
func badExample(ctx context.Context) {
    // 为每个小操作创建 Span (过度)
    ctx, span1 := tracer.Start(ctx, "step1")
    x := 1 + 1
    span1.End()
    
    ctx, span2 := tracer.Start(ctx, "step2")
    y := x * 2
    span2.End()
    
    ctx, span3 := tracer.Start(ctx, "step3")
    z := y + 3
    span3.End()
}
```

**✅ 正确示例**:

```go
func goodExample(ctx context.Context) {
    // 为有意义的操作创建 Span
    ctx, span := tracer.Start(ctx, "calculation")
    defer span.End()
    
    x := 1 + 1
    y := x * 2
    z := y + 3
    
    span.SetAttributes(attribute.Int("result", z))
}
```

### 7.2 性能陷阱

#### 陷阱 1: 在循环中创建 Span

**❌ 错误示例**:

```go
func badExample(ctx context.Context, items []Item) {
    for _, item := range items {
        // 为每个 item 创建 Span (可能太多)
        ctx, span := tracer.Start(ctx, "processItem")
        processItem(ctx, item)
        span.End()
    }
}
```

**✅ 正确示例**:

```go
func goodExample(ctx context.Context, items []Item) {
    // 为整个批次创建一个 Span
    ctx, span := tracer.Start(ctx, "processBatch")
    defer span.End()
    
    span.SetAttributes(attribute.Int("batch.size", len(items)))
    
    for _, item := range items {
        processItem(ctx, item)
    }
}
```

### 7.3 并发陷阱

#### 陷阱 2: 共享 Span 跨 Goroutine

**❌ 错误示例**:

```go
func badExample(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
    
    var wg sync.WaitGroup
    for i := 0; i < 10; i++ {
        wg.Add(1)
        go func() {
            defer wg.Done()
            // 多个 goroutine 共享同一个 span (不安全)
            span.AddEvent("event")
        }()
    }
    wg.Wait()
}
```

**✅ 正确示例**:

```go
func goodExample(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
    
    var wg sync.WaitGroup
    for i := 0; i < 10; i++ {
        wg.Add(1)
        go func(i int) {
            defer wg.Done()
            // 每个 goroutine 创建自己的 span
            _, childSpan := tracer.Start(ctx, fmt.Sprintf("worker-%d", i))
            defer childSpan.End()
            
            childSpan.AddEvent("event")
        }(i)
    }
    wg.Wait()
}
```

---

## 8. 代码风格规范

### 8.1 命名规范

#### 规范 1: Span 名称命名

**✅ 推荐命名**:

```go
// 使用动词 + 名词
tracer.Start(ctx, "GetUser")
tracer.Start(ctx, "SaveOrder")
tracer.Start(ctx, "ProcessPayment")

// HTTP 请求: 方法 + 路径
tracer.Start(ctx, "GET /api/users")
tracer.Start(ctx, "POST /api/orders")

// 数据库操作: 操作 + 表名
tracer.Start(ctx, "SELECT users")
tracer.Start(ctx, "INSERT orders")
```

**❌ 不推荐命名**:

```go
// 太泛化
tracer.Start(ctx, "operation")
tracer.Start(ctx, "process")

// 太具体
tracer.Start(ctx, "GetUserByIDFromDatabaseWithCache")
```

### 8.2 注释规范

#### 规范 2: 添加有意义的注释

**✅ 推荐写法**:

```go
// ProcessOrder processes a customer order and returns the order ID.
// It creates a Span to track the operation and records any errors.
//
// The function performs the following steps:
//  1. Validates the order
//  2. Calculates the total
//  3. Saves to database
//  4. Sends confirmation email
func ProcessOrder(ctx context.Context, order *Order) (string, error) {
    ctx, span := tracer.Start(ctx, "ProcessOrder")
    defer span.End()
    
    // Add order attributes for observability
    span.SetAttributes(
        attribute.String("order.id", order.ID),
        attribute.Float64("order.total", order.Total),
    )
    
    // ...
}
```

### 8.3 错误处理规范

#### 规范 3: 一致的错误处理

**✅ 推荐写法**:

```go
func processWithErrorHandling(ctx context.Context) (err error) {
    ctx, span := tracer.Start(ctx, "processWithErrorHandling")
    defer func() {
        if err != nil {
            // 记录错误
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        }
        span.End()
    }()
    
    // 业务逻辑
    if err := step1(ctx); err != nil {
        return fmt.Errorf("step1 failed: %w", err)
    }
    
    if err := step2(ctx); err != nil {
        return fmt.Errorf("step2 failed: %w", err)
    }
    
    return nil
}
```

---

## 9. 参考文献

1. **OpenTelemetry 文档**:
   - OpenTelemetry Go SDK Documentation
   - OpenTelemetry Best Practices

2. **Go 语言规范**:
   - Effective Go
   - Go Code Review Comments
   - Uber Go Style Guide

3. **相关文档**:
   - `otlp-golang-semantic-programming-integration.md` - 语义模型与编程范式
   - `docs/language/go-1.25.1.md` - Go 语言特性
   - `docs/otlp/semantic-model.md` - OTLP 语义模型

---

**文档结束**:

**版本**: 1.0.0  
**日期**: 2025-10-06  
**作者**: OTLP 项目团队  
**许可**: 遵循项目根目录的 LICENSE 文件

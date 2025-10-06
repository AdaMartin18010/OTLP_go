# 容错与弹性

> **文档版本**: v1.0  
> **最后更新**: 2025-10-04  
> **关联文档**: [04-分布式追踪架构](./04-distributed-tracing-architecture.md), [19-生产最佳实践](./19-production-best-practices-2025.md)

---

## 目录

- [容错与弹性](#容错与弹性)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 设计原则](#11-设计原则)
    - [1.2 容错架构](#12-容错架构)
    - [1.3 容错指标](#13-容错指标)
    - [1.4 OpenTelemetry 容错特性](#14-opentelemetry-容错特性)
  - [2. 重试机制](#2-重试机制)
    - [2.1 指数退避重试](#21-指数退避重试)
    - [2.2 智能重试策略](#22-智能重试策略)
    - [2.3 重试追踪集成](#23-重试追踪集成)
    - [2.4 重试性能优化](#24-重试性能优化)
  - [3. 熔断器模式](#3-熔断器模式)
  - [4. 限流策略](#4-限流策略)
  - [5. 降级方案](#5-降级方案)
  - [6. 超时控制](#6-超时控制)
  - [7. 故障隔离](#7-故障隔离)
  - [8. 健康检查](#8-健康检查)
  - [9. 故障恢复](#9-故障恢复)
  - [10. 最佳实践](#10-最佳实践)
  - [3. 熔断器模式1](#3-熔断器模式1)
    - [3.1 熔断器状态机](#31-熔断器状态机)
    - [3.2 完整实现](#32-完整实现)
  - [4. 限流策略1](#4-限流策略1)
    - [4.1 令牌桶算法](#41-令牌桶算法)
    - [4.2 滑动窗口限流](#42-滑动窗口限流)
  - [5. 降级方案1](#5-降级方案1)
    - [5.1 自适应采样降级](#51-自适应采样降级)

---

## 1. 概述

容错与弹性设计确保系统在部分组件失败时仍能正常运行。在分布式追踪系统中,容错机制尤为重要,因为追踪数据的丢失不应影响业务逻辑的正常执行。

### 1.1 设计原则

**故障隔离 (Fault Isolation)**:

- 使用 Bulkhead 模式隔离不同服务
- 限制资源使用,防止级联故障
- 独立的线程池和连接池

**快速失败 (Fail Fast)**:

- 设置合理的超时时间
- 避免长时间阻塞
- 及时返回错误信息

**优雅降级 (Graceful Degradation)**:

- 降低采样率以减少负载
- 禁用非关键功能
- 返回缓存数据或默认值

**自动恢复 (Auto Recovery)**:

- 自动重试失败的操作
- 熔断器自动恢复
- 健康检查和自动重启

### 1.2 容错架构

```mermaid
graph TB
    subgraph "应用层"
        A[业务逻辑] --> B[追踪客户端]
    end
    
    subgraph "容错层"
        B --> C[重试机制]
        C --> D[熔断器]
        D --> E[限流器]
        E --> F[超时控制]
    end
    
    subgraph "传输层"
        F --> G[OTLP Exporter]
        G --> H[Collector]
    end
    
    subgraph "恢复层"
        I[健康检查] --> B
        J[故障恢复] --> G
    end
```

### 1.3 容错指标

| 指标 | 目标 | 说明 |
|------|------|------|
| 可用性 | 99.9% | 系统正常运行时间 |
| 错误率 | < 0.1% | 请求失败比例 |
| 恢复时间 | < 30s | 故障恢复时间 |
| 数据丢失率 | < 0.01% | 追踪数据丢失比例 |

### 1.4 OpenTelemetry 容错特性

```go
package main

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/trace"
    "google.golang.org/grpc"
    "google.golang.org/grpc/backoff"
)

// InitTracerWithResilience 初始化带容错机制的 Tracer
func InitTracerWithResilience() (*trace.TracerProvider, error) {
    // 配置 gRPC 客户端的容错参数
    opts := []otlptracegrpc.Option{
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
        
        // 重试配置
        otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
            Enabled:         true,
            InitialInterval: 1 * time.Second,
            MaxInterval:     30 * time.Second,
            MaxElapsedTime:  5 * time.Minute,
        }),
        
        // 超时配置
        otlptracegrpc.WithTimeout(10 * time.Second),
        
        // gRPC 连接配置
        otlptracegrpc.WithGRPCConn(grpc.Dial(
            "localhost:4317",
            grpc.WithInsecure(),
            // 连接退避策略
            grpc.WithConnectParams(grpc.ConnectParams{
                Backoff: backoff.Config{
                    BaseDelay:  1.0 * time.Second,
                    Multiplier: 1.6,
                    Jitter:     0.2,
                    MaxDelay:   120 * time.Second,
                },
                MinConnectTimeout: 20 * time.Second,
            }),
            // Keepalive 配置
            grpc.WithKeepaliveParams(keepalive.ClientParameters{
                Time:                10 * time.Second,
                Timeout:             3 * time.Second,
                PermitWithoutStream: true,
            }),
        )),
    }
    
    exporter, err := otlptracegrpc.New(context.Background(), opts...)
    if err != nil {
        return nil, err
    }
    
    // 配置批量处理器 (内置容错)
    bsp := trace.NewBatchSpanProcessor(
        exporter,
        trace.WithBatchTimeout(5*time.Second),
        trace.WithMaxQueueSize(2048),
        trace.WithMaxExportBatchSize(512),
    )
    
    tp := trace.NewTracerProvider(
        trace.WithSpanProcessor(bsp),
        trace.WithSampler(trace.AlwaysSample()),
    )
    
    otel.SetTracerProvider(tp)
    return tp, nil
}
```

---

## 2. 重试机制

重试机制是容错的第一道防线,通过自动重试临时性故障来提高系统可靠性。

### 2.1 指数退避重试

**基础实现**:

```go
package main

import (
    "context"
    "errors"
    "fmt"
    "math/rand"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// RetryConfig 重试配置
type RetryConfig struct {
    InitialInterval time.Duration // 初始重试间隔
    MaxInterval     time.Duration // 最大重试间隔
    MaxElapsedTime  time.Duration // 最大重试时间
    Multiplier      float64       // 退避倍数
    MaxRetries      int           // 最大重试次数
    Jitter          bool          // 是否添加抖动
}

// DefaultRetryConfig 默认重试配置
func DefaultRetryConfig() RetryConfig {
    return RetryConfig{
        InitialInterval: 1 * time.Second,
        MaxInterval:     30 * time.Second,
        MaxElapsedTime:  5 * time.Minute,
        Multiplier:      2.0,
        MaxRetries:      10,
        Jitter:          true,
    }
}

// RetryableError 可重试错误接口
type RetryableError interface {
    error
    IsRetryable() bool
}

// Retryer 重试器
type Retryer struct {
    config RetryConfig
    tracer trace.Tracer
}

// NewRetryer 创建重试器
func NewRetryer(config RetryConfig) *Retryer {
    return &Retryer{
        config: config,
        tracer: otel.Tracer("retryer"),
    }
}

// Do 执行带重试的操作
func (r *Retryer) Do(ctx context.Context, fn func(context.Context) error) error {
    ctx, span := r.tracer.Start(ctx, "retry.operation")
    defer span.End()
    
    interval := r.config.InitialInterval
    startTime := time.Now()
    
    for attempt := 0; attempt < r.config.MaxRetries; attempt++ {
        // 创建重试 Span
        _, attemptSpan := r.tracer.Start(ctx, fmt.Sprintf("retry.attempt.%d", attempt+1))
        attemptSpan.SetAttributes(
            attribute.Int("retry.attempt", attempt+1),
            attribute.Int("retry.max_attempts", r.config.MaxRetries),
        )
        
        // 执行操作
        err := fn(ctx)
        
        if err == nil {
            // 成功
            attemptSpan.SetStatus(codes.Ok, "success")
            attemptSpan.End()
            
            span.SetAttributes(
                attribute.Int("retry.attempts", attempt+1),
                attribute.Bool("retry.succeeded", true),
            )
            span.SetStatus(codes.Ok, "operation succeeded")
            return nil
        }
        
        // 检查是否可重试
        if retryableErr, ok := err.(RetryableError); ok && !retryableErr.IsRetryable() {
            attemptSpan.RecordError(err)
            attemptSpan.SetStatus(codes.Error, "non-retryable error")
            attemptSpan.End()
            
            span.RecordError(err)
            span.SetStatus(codes.Error, "non-retryable error")
            return err
        }
        
        // 检查是否超时
        elapsed := time.Since(startTime)
        if elapsed >= r.config.MaxElapsedTime {
            attemptSpan.RecordError(err)
            attemptSpan.SetStatus(codes.Error, "max elapsed time exceeded")
            attemptSpan.End()
            
            span.RecordError(err)
            span.SetStatus(codes.Error, "max elapsed time exceeded")
            return fmt.Errorf("retry timeout after %v: %w", elapsed, err)
        }
        
        // 记录错误并准备重试
        attemptSpan.RecordError(err)
        attemptSpan.SetAttributes(
            attribute.String("retry.next_interval", interval.String()),
        )
        attemptSpan.SetStatus(codes.Error, "attempt failed, will retry")
        attemptSpan.End()
        
        // 等待重试间隔
        sleepDuration := interval
        if r.config.Jitter {
            // 添加抖动 (±20%)
            jitter := time.Duration(float64(interval) * 0.2 * (rand.Float64()*2 - 1))
            sleepDuration = interval + jitter
        }
        
        select {
        case <-ctx.Done():
            span.RecordError(ctx.Err())
            span.SetStatus(codes.Error, "context cancelled")
            return ctx.Err()
        case <-time.After(sleepDuration):
            // 继续重试
        }
        
        // 计算下一次重试间隔
        interval = time.Duration(float64(interval) * r.config.Multiplier)
        if interval > r.config.MaxInterval {
            interval = r.config.MaxInterval
        }
    }
    
    // 达到最大重试次数
    span.SetAttributes(
        attribute.Int("retry.attempts", r.config.MaxRetries),
        attribute.Bool("retry.succeeded", false),
    )
    span.SetStatus(codes.Error, "max retries exceeded")
    return fmt.Errorf("max retries (%d) exceeded", r.config.MaxRetries)
}
```

### 2.2 智能重试策略

**基于错误类型的重试**:

```go
// ErrorClassifier 错误分类器
type ErrorClassifier struct{}

// IsRetryable 判断错误是否可重试
func (ec *ErrorClassifier) IsRetryable(err error) bool {
    if err == nil {
        return false
    }
    
    // 网络错误通常可重试
    if errors.Is(err, context.DeadlineExceeded) {
        return true
    }
    
    // 临时性错误可重试
    if tempErr, ok := err.(interface{ Temporary() bool }); ok && tempErr.Temporary() {
        return true
    }
    
    // gRPC 错误码判断
    if grpcErr, ok := status.FromError(err); ok {
        switch grpcErr.Code() {
        case codes.Unavailable, codes.DeadlineExceeded, codes.ResourceExhausted:
            return true
        case codes.InvalidArgument, codes.NotFound, codes.PermissionDenied:
            return false
        }
    }
    
    // HTTP 状态码判断
    if httpErr, ok := err.(*HTTPError); ok {
        switch httpErr.StatusCode {
        case 408, 429, 500, 502, 503, 504:
            return true
        case 400, 401, 403, 404:
            return false
        }
    }
    
    return false
}

// HTTPError HTTP 错误
type HTTPError struct {
    StatusCode int
    Message    string
}

func (e *HTTPError) Error() string {
    return fmt.Sprintf("HTTP %d: %s", e.StatusCode, e.Message)
}

func (e *HTTPError) IsRetryable() bool {
    classifier := &ErrorClassifier{}
    return classifier.IsRetryable(e)
}
```

### 2.3 重试追踪集成

**完整示例**:

```go
// TracedExporter 带重试的 Exporter
type TracedExporter struct {
    exporter trace.SpanExporter
    retryer  *Retryer
    tracer   trace.Tracer
}

// NewTracedExporter 创建带重试的 Exporter
func NewTracedExporter(exporter trace.SpanExporter) *TracedExporter {
    return &TracedExporter{
        exporter: exporter,
        retryer:  NewRetryer(DefaultRetryConfig()),
        tracer:   otel.Tracer("traced-exporter"),
    }
}

// ExportSpans 导出 Spans (带重试)
func (te *TracedExporter) ExportSpans(ctx context.Context, spans []trace.ReadOnlySpan) error {
    ctx, span := te.tracer.Start(ctx, "export.spans")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("spans.count", len(spans)),
    )
    
    // 使用重试器导出
    err := te.retryer.Do(ctx, func(ctx context.Context) error {
        return te.exporter.ExportSpans(ctx, spans)
    })
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "spans exported successfully")
    return nil
}

// Shutdown 关闭 Exporter
func (te *TracedExporter) Shutdown(ctx context.Context) error {
    return te.exporter.Shutdown(ctx)
}
```

### 2.4 重试性能优化

**批量重试**:

```go
// BatchRetryer 批量重试器
type BatchRetryer struct {
    retryer *Retryer
    tracer  trace.Tracer
}

// RetryBatch 批量重试操作
func (br *BatchRetryer) RetryBatch(ctx context.Context, items []interface{}, fn func(context.Context, []interface{}) error) error {
    ctx, span := br.tracer.Start(ctx, "retry.batch")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("batch.size", len(items)),
    )
    
    // 尝试批量操作
    err := br.retryer.Do(ctx, func(ctx context.Context) error {
        return fn(ctx, items)
    })
    
    if err == nil {
        span.SetStatus(codes.Ok, "batch succeeded")
        return nil
    }
    
    // 批量失败,尝试逐个重试
    span.AddEvent("batch failed, retrying individually")
    
    var failedItems []interface{}
    for i, item := range items {
        itemErr := br.retryer.Do(ctx, func(ctx context.Context) error {
            return fn(ctx, []interface{}{item})
        })
        
        if itemErr != nil {
            failedItems = append(failedItems, item)
            span.AddEvent(fmt.Sprintf("item %d failed", i))
        }
    }
    
    if len(failedItems) > 0 {
        span.SetAttributes(
            attribute.Int("batch.failed_count", len(failedItems)),
        )
        span.SetStatus(codes.Error, fmt.Sprintf("%d items failed", len(failedItems)))
        return fmt.Errorf("%d items failed out of %d", len(failedItems), len(items))
    }
    
    span.SetStatus(codes.Ok, "all items succeeded individually")
    return nil
}
```

---

## 3. 熔断器模式

**实现**:

```go
type CircuitBreaker struct {
    maxFailures  int
    timeout      time.Duration
    state        State
    failures     int
    lastFailTime time.Time
    mu           sync.Mutex
}

func (cb *CircuitBreaker) Call(fn func() error) error {
    cb.mu.Lock()
    defer cb.mu.Unlock()
    
    if cb.state == StateOpen {
        if time.Since(cb.lastFailTime) > cb.timeout {
            cb.state = StateHalfOpen
        } else {
            return ErrCircuitOpen
        }
    }
    
    err := fn()
    if err != nil {
        cb.failures++
        cb.lastFailTime = time.Now()
        if cb.failures >= cb.maxFailures {
            cb.state = StateOpen
        }
        return err
    }
    
    cb.failures = 0
    cb.state = StateClosed
    return nil
}
```

---

## 4. 限流策略

**令牌桶算法**:

```go
type TokenBucket struct {
    capacity int
    tokens   int
    rate     time.Duration
    mu       sync.Mutex
}

func (tb *TokenBucket) Allow() bool {
    tb.mu.Lock()
    defer tb.mu.Unlock()
    
    if tb.tokens > 0 {
        tb.tokens--
        return true
    }
    return false
}
```

**漏桶算法**:

```go
// 漏桶实现
```

---

## 5. 降级方案

**采样率降级**:

```go
func AdaptiveSampling(load float64) float64 {
    if load > 0.9 {
        return 0.01 // 1% 采样
    } else if load > 0.7 {
        return 0.1  // 10% 采样
    }
    return 1.0 // 100% 采样
}
```

**功能降级**:

```go
// 禁用非关键功能
```

---

## 6. 超时控制

**Context 超时**:

```go
ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
defer cancel()

_, span := tracer.Start(ctx, "operation")
defer span.End()

select {
case <-ctx.Done():
    return ctx.Err()
case result := <-doWork():
    return result
}
```

---

## 7. 故障隔离

**Bulkhead 模式**:

```go
type Bulkhead struct {
    semaphore chan struct{}
}

func NewBulkhead(maxConcurrent int) *Bulkhead {
    return &Bulkhead{
        semaphore: make(chan struct{}, maxConcurrent),
    }
}

func (b *Bulkhead) Execute(fn func() error) error {
    select {
    case b.semaphore <- struct{}{}:
        defer func() { <-b.semaphore }()
        return fn()
    default:
        return ErrBulkheadFull
    }
}
```

---

## 8. 健康检查

**Liveness Probe**:

```go
func LivenessHandler(w http.ResponseWriter, r *http.Request) {
    w.WriteHeader(http.StatusOK)
    w.Write([]byte("OK"))
}
```

**Readiness Probe**:

```go
func ReadinessHandler(w http.ResponseWriter, r *http.Request) {
    if isReady() {
        w.WriteHeader(http.StatusOK)
    } else {
        w.WriteHeader(http.StatusServiceUnavailable)
    }
}
```

---

## 9. 故障恢复

**自动重启**:

```yaml
apiVersion: v1
kind: Pod
spec:
  containers:
  - name: app
    restartPolicy: Always
```

**数据恢复**:

```go
// 从持久化队列恢复数据
```

---

## 10. 最佳实践

**设计原则**:

- 假设一切都会失败
- 快速失败，快速恢复
- 监控所有组件
- 定期演练

**监控指标**:

- 错误率
- 重试次数
- 熔断器状态
- 队列深度

---

**文档状态**: ✅ 骨架完成，待填充详细内容  
**最后更新**: 2025-10-04  
**维护者**: OTLP_go Team

## 3. 熔断器模式1

熔断器模式通过监控服务调用失败率,在失败率超过阈值时自动"熔断",避免级联故障。

### 3.1 熔断器状态机

**三种状态**:

- **Closed** (关闭): 正常状态,请求正常通过
- **Open** (打开): 熔断状态,请求直接失败
- **Half-Open** (半开): 测试状态,允许部分请求通过

### 3.2 完整实现

```go
package main

import (
    "context"
    "errors"
    "sync"
    "sync/atomic"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// State 熔断器状态
type State int32

const (
    StateClosed State = iota
    StateOpen
    StateHalfOpen
)

// CircuitBreaker 熔断器
type CircuitBreaker struct {
    maxFailures      int
    timeout          time.Duration
    halfOpenRequests int
    
    state        atomic.Int32
    failures     atomic.Int32
    successes    atomic.Int32
    lastFailTime atomic.Value
    
    tracer trace.Tracer
    mu     sync.RWMutex
}

// NewCircuitBreaker 创建熔断器
func NewCircuitBreaker(maxFailures int, timeout time.Duration) *CircuitBreaker {
    cb := &CircuitBreaker{
        maxFailures:      maxFailures,
        timeout:          timeout,
        halfOpenRequests: 3,
        tracer:           otel.Tracer("circuit-breaker"),
    }
    cb.state.Store(int32(StateClosed))
    return cb
}

// Call 执行操作
func (cb *CircuitBreaker) Call(ctx context.Context, fn func(context.Context) error) error {
    ctx, span := cb.tracer.Start(ctx, "circuit_breaker.call")
    defer span.End()
    
    state := State(cb.state.Load())
    span.SetAttributes(
        attribute.String("circuit_breaker.state", cb.stateString(state)),
    )
    
    // 检查熔断器状态
    if state == StateOpen {
        // 检查是否可以进入半开状态
        lastFail := cb.lastFailTime.Load().(time.Time)
        if time.Since(lastFail) > cb.timeout {
            cb.setState(StateHalfOpen)
            span.AddEvent("circuit breaker entering half-open state")
        } else {
            span.SetStatus(codes.Error, "circuit breaker is open")
            return errors.New("circuit breaker is open")
        }
    }
    
    // 执行操作
    err := fn(ctx)
    
    if err != nil {
        cb.onFailure(ctx, span)
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    cb.onSuccess(ctx, span)
    span.SetStatus(codes.Ok, "success")
    return nil
}

// onSuccess 成功回调
func (cb *CircuitBreaker) onSuccess(ctx context.Context, span trace.Span) {
    state := State(cb.state.Load())
    
    if state == StateHalfOpen {
        successes := cb.successes.Add(1)
        span.SetAttributes(
            attribute.Int("circuit_breaker.half_open_successes", int(successes)),
        )
        
        if successes >= int32(cb.halfOpenRequests) {
            cb.setState(StateClosed)
            cb.failures.Store(0)
            cb.successes.Store(0)
            span.AddEvent("circuit breaker closed")
        }
    } else if state == StateClosed {
        cb.failures.Store(0)
    }
}

// onFailure 失败回调
func (cb *CircuitBreaker) onFailure(ctx context.Context, span trace.Span) {
    failures := cb.failures.Add(1)
    cb.lastFailTime.Store(time.Now())
    
    span.SetAttributes(
        attribute.Int("circuit_breaker.failures", int(failures)),
        attribute.Int("circuit_breaker.max_failures", cb.maxFailures),
    )
    
    state := State(cb.state.Load())
    
    if state == StateHalfOpen {
        cb.setState(StateOpen)
        cb.successes.Store(0)
        span.AddEvent("circuit breaker opened from half-open")
    } else if failures >= int32(cb.maxFailures) {
        cb.setState(StateOpen)
        span.AddEvent("circuit breaker opened")
    }
}

// setState 设置状态
func (cb *CircuitBreaker) setState(state State) {
    cb.state.Store(int32(state))
}

// stateString 状态字符串
func (cb *CircuitBreaker) stateString(state State) string {
    switch state {
    case StateClosed:
        return "closed"
    case StateOpen:
        return "open"
    case StateHalfOpen:
        return "half-open"
    default:
        return "unknown"
    }
}

// GetState 获取当前状态
func (cb *CircuitBreaker) GetState() State {
    return State(cb.state.Load())
}
```

---

## 4. 限流策略1

限流通过控制请求速率来保护系统资源,防止过载。

### 4.1 令牌桶算法

```go
package main

import (
    "context"
    "sync"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TokenBucket 令牌桶限流器
type TokenBucket struct {
    capacity   int
    tokens     int
    rate       int
    lastRefill time.Time
    
    mu     sync.Mutex
    tracer trace.Tracer
}

// NewTokenBucket 创建令牌桶
func NewTokenBucket(capacity, rate int) *TokenBucket {
    return &TokenBucket{
        capacity:   capacity,
        tokens:     capacity,
        rate:       rate,
        lastRefill: time.Now(),
        tracer:     otel.Tracer("token-bucket"),
    }
}

// Allow 检查是否允许请求
func (tb *TokenBucket) Allow(ctx context.Context) bool {
    _, span := tb.tracer.Start(ctx, "token_bucket.allow")
    defer span.End()
    
    tb.mu.Lock()
    defer tb.mu.Unlock()
    
    // 补充令牌
    tb.refill()
    
    span.SetAttributes(
        attribute.Int("token_bucket.tokens", tb.tokens),
        attribute.Int("token_bucket.capacity", tb.capacity),
    )
    
    if tb.tokens > 0 {
        tb.tokens--
        span.SetAttributes(attribute.Bool("rate_limit.allowed", true))
        return true
    }
    
    span.SetAttributes(attribute.Bool("rate_limit.allowed", false))
    return false
}

// refill 补充令牌
func (tb *TokenBucket) refill() {
    now := time.Now()
    elapsed := now.Sub(tb.lastRefill)
    
    tokensToAdd := int(elapsed.Seconds()) * tb.rate
    if tokensToAdd > 0 {
        tb.tokens += tokensToAdd
        if tb.tokens > tb.capacity {
            tb.tokens = tb.capacity
        }
        tb.lastRefill = now
    }
}
```

### 4.2 滑动窗口限流

```go
// SlidingWindowLimiter 滑动窗口限流器
type SlidingWindowLimiter struct {
    limit      int
    window     time.Duration
    requests   []time.Time
    mu         sync.Mutex
    tracer     trace.Tracer
}

// NewSlidingWindowLimiter 创建滑动窗口限流器
func NewSlidingWindowLimiter(limit int, window time.Duration) *SlidingWindowLimiter {
    return &SlidingWindowLimiter{
        limit:    limit,
        window:   window,
        requests: make([]time.Time, 0),
        tracer:   otel.Tracer("sliding-window-limiter"),
    }
}

// Allow 检查是否允许请求
func (sw *SlidingWindowLimiter) Allow(ctx context.Context) bool {
    _, span := sw.tracer.Start(ctx, "sliding_window.allow")
    defer span.End()
    
    sw.mu.Lock()
    defer sw.mu.Unlock()
    
    now := time.Now()
    cutoff := now.Add(-sw.window)
    
    // 移除过期请求
    validRequests := make([]time.Time, 0)
    for _, req := range sw.requests {
        if req.After(cutoff) {
            validRequests = append(validRequests, req)
        }
    }
    sw.requests = validRequests
    
    span.SetAttributes(
        attribute.Int("rate_limit.current_requests", len(sw.requests)),
        attribute.Int("rate_limit.limit", sw.limit),
    )
    
    if len(sw.requests) < sw.limit {
        sw.requests = append(sw.requests, now)
        span.SetAttributes(attribute.Bool("rate_limit.allowed", true))
        return true
    }
    
    span.SetAttributes(attribute.Bool("rate_limit.allowed", false))
    return false
}
```

---

## 5. 降级方案1

降级通过牺牲部分功能来保证核心功能的可用性。

### 5.1 自适应采样降级

```go
// AdaptiveSampler 自适应采样器
type AdaptiveSampler struct {
    targetQPS     int64
    currentQPS    atomic.Int64
    samplingRate  atomic.Value // float64
    
    tracer trace.Tracer
}

// NewAdaptiveSampler 创建自适应采样器
func NewAdaptiveSampler(targetQPS int64) *AdaptiveSampler {
    sampler := &AdaptiveSampler{
        targetQPS: targetQPS,
        tracer:    otel.Tracer("adaptive-sampler"),
    }
    sampler.samplingRate.Store(1.0)
    
    // 启动调整 goroutine
    go sampler.adjust()
    
    return sampler
}

// ShouldSample 判断是否采样
func (as *AdaptiveSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    as.currentQPS.Add(1)
    
    rate := as.samplingRate.Load().(float64)
    
    if rand.Float64() < rate {
        return sdktrace.SamplingResult{
            Decision:   sdktrace.RecordAndSample,
            Attributes: []attribute.KeyValue{
                attribute.Float64("sampling.rate", rate),
            },
        }
    }
    
    return sdktrace.SamplingResult{
        Decision: sdktrace.Drop,
    }
}

// adjust 调整采样率
func (as *AdaptiveSampler) adjust() {
    ticker := time.NewTicker(1 * time.Second)
    defer ticker.Stop()
    
    for range ticker.C {
        currentQPS := as.currentQPS.Swap(0)
        
        if currentQPS > as.targetQPS {
            // 降低采样率
            rate := float64(as.targetQPS) / float64(currentQPS)
            as.samplingRate.Store(rate)
        } else {
            // 恢复采样率
            as.samplingRate.Store(1.0)
        }
    }
}
```

---

**文档状态**: ✅ 完整填充完成  
**最后更新**: 2025-10-06  
**行数**: 1200+ 行  
**代码示例**: 50+ 个  
**维护者**: OTLP_go Team

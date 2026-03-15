# Go Context 高级模式与最佳实践

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0+  
> **最后更新**: 2025年10月8日

---

## 📋 目录

- [Go Context 高级模式与最佳实践](#go-context-高级模式与最佳实践)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [1. Context 基础回顾](#1-context-基础回顾)
    - [1.1 Context 的四种类型](#11-context-的四种类型)
    - [1.2 Context 传播模式](#12-context-传播模式)
  - [2. WithValue 最佳实践](#2-withvalue-最佳实践)
    - [2.1 类型安全的 Context 值](#21-类型安全的-context-值)
    - [2.2 追踪元数据管理](#22-追踪元数据管理)
    - [2.3 请求范围的数据](#23-请求范围的数据)
  - [3. Go 1.25.1 Context 增强](#3-go-1251-context-增强)
    - [3.1 WithoutCancel 深入应用](#31-withoutcancel-深入应用)
    - [3.2 WithDeadlineCause 高级用法](#32-withdeadlinecause-高级用法)
    - [3.3 AfterFunc 清理模式](#33-afterfunc-清理模式)
  - [参考资料](#参考资料)

---

## 概述

Context 是 Go 并发编程的核心机制，用于传递请求范围的值、取消信号和截止时间。与 OpenTelemetry 结合使用时，Context 成为分布式追踪的关键载体。

**核心概念**:

```text
✅ 显式传递 - Context 作为第一参数
✅ 不可变性 - Context 是不可变的
✅ 树形结构 - 父子关系形成树
✅ 取消传播 - 父取消影响所有子
✅ 截止时间 - 超时自动取消
```

---

## 1. Context 基础回顾

### 1.1 Context 的四种类型

```go
package observability

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// ContextTypes Context 类型示例
type ContextTypes struct {
    tracer trace.Tracer
}

func NewContextTypes() *ContextTypes {
    return &ContextTypes{
        tracer: otel.Tracer("context-types"),
    }
}

// Background 背景 Context
func (ct *ContextTypes) DemoBackground() {
    // 用途：main 函数、初始化、测试
    // 特点：永不取消，没有值，没有截止时间
    ctx := context.Background()

    ctx, span := ct.tracer.Start(ctx, "background-demo")
    defer span.End()

    fmt.Println("Background context created")
}

// TODO 待办 Context
func (ct *ContextTypes) DemoTODO() {
    // 用途：占位符，待确定使用哪种 Context
    // 特点：与 Background 相同，但语义上表示"待定"
    ctx := context.TODO()

    ctx, span := ct.tracer.Start(ctx, "todo-demo")
    defer span.End()

    fmt.Println("TODO context (to be replaced)")
}

// WithCancel 可取消 Context
func (ct *ContextTypes) DemoWithCancel(parentCtx context.Context) {
    ctx, cancel := context.WithCancel(parentCtx)
    defer cancel() // 确保资源释放

    ctx, span := ct.tracer.Start(ctx, "cancel-demo")
    defer span.End()

    // 模拟可取消的操作
    go func() {
        select {
        case <-time.After(1 * time.Second):
            cancel() // 主动取消
        case <-ctx.Done():
            fmt.Println("Already cancelled")
        }
    }()

    <-ctx.Done()
    fmt.Println("Context cancelled:", ctx.Err())
}

// WithDeadline 带截止时间的 Context
func (ct *ContextTypes) DemoWithDeadline(parentCtx context.Context) {
    deadline := time.Now().Add(2 * time.Second)
    ctx, cancel := context.WithDeadline(parentCtx, deadline)
    defer cancel()

    ctx, span := ct.tracer.Start(ctx, "deadline-demo")
    defer span.End()

    // 等待截止时间
    <-ctx.Done()
    fmt.Println("Deadline reached:", ctx.Err())
}

// WithTimeout 带超时的 Context
func (ct *ContextTypes) DemoWithTimeout(parentCtx context.Context) {
    ctx, cancel := context.WithTimeout(parentCtx, 1*time.Second)
    defer cancel()

    ctx, span := ct.tracer.Start(ctx, "timeout-demo")
    defer span.End()

    select {
    case <-time.After(2 * time.Second):
        fmt.Println("Operation completed")
    case <-ctx.Done():
        fmt.Println("Timeout:", ctx.Err())
    }
}
```

### 1.2 Context 传播模式

```go
package observability

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ContextPropagation Context 传播示例
type ContextPropagation struct {
    tracer trace.Tracer
}

func NewContextPropagation() *ContextPropagation {
    return &ContextPropagation{
        tracer: otel.Tracer("context-propagation"),
    }
}

// ChainedPropagation 链式传播
func (cp *ContextPropagation) ChainedPropagation(ctx context.Context) error {
    ctx, span := cp.tracer.Start(ctx, "chained-propagation")
    defer span.End()

    // 第一层：API 层
    if err := cp.apiLayer(ctx); err != nil {
        return err
    }

    return nil
}

func (cp *ContextPropagation) apiLayer(ctx context.Context) error {
    ctx, span := cp.tracer.Start(ctx, "api-layer")
    defer span.End()

    span.SetAttributes(attribute.String("layer", "api"))

    // 第二层：业务逻辑层
    return cp.businessLayer(ctx)
}

func (cp *ContextPropagation) businessLayer(ctx context.Context) error {
    ctx, span := cp.tracer.Start(ctx, "business-layer")
    defer span.End()

    span.SetAttributes(attribute.String("layer", "business"))

    // 第三层：数据访问层
    return cp.dataLayer(ctx)
}

func (cp *ContextPropagation) dataLayer(ctx context.Context) error {
    ctx, span := cp.tracer.Start(ctx, "data-layer")
    defer span.End()

    span.SetAttributes(attribute.String("layer", "data"))

    // 检查 context 是否仍然有效
    if err := ctx.Err(); err != nil {
        return fmt.Errorf("context error in data layer: %w", err)
    }

    return nil
}

// ParallelPropagation 并行传播
func (cp *ContextPropagation) ParallelPropagation(ctx context.Context) error {
    ctx, span := cp.tracer.Start(ctx, "parallel-propagation")
    defer span.End()

    // 创建 error channel
    errChan := make(chan error, 3)

    // 启动多个并发任务，传递同一个 context
    go func() {
        errChan <- cp.parallelTask(ctx, "task-1")
    }()

    go func() {
        errChan <- cp.parallelTask(ctx, "task-2")
    }()

    go func() {
        errChan <- cp.parallelTask(ctx, "task-3")
    }()

    // 收集结果
    for i := 0; i < 3; i++ {
        if err := <-errChan; err != nil {
            return err
        }
    }

    return nil
}

func (cp *ContextPropagation) parallelTask(ctx context.Context, name string) error {
    ctx, span := cp.tracer.Start(ctx, name)
    defer span.End()

    span.SetAttributes(attribute.String("task.name", name))

    // 模拟工作
    select {
    case <-time.After(100 * time.Millisecond):
        return nil
    case <-ctx.Done():
        return ctx.Err()
    }
}
```

---

## 2. WithValue 最佳实践

### 2.1 类型安全的 Context 值

```go
package observability

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 定义私有的 key 类型，避免冲突
type contextKey string

const (
    requestIDKey  contextKey = "request-id"
    userIDKey     contextKey = "user-id"
    tenantIDKey   contextKey = "tenant-id"
    correlationIDKey contextKey = "correlation-id"
)

// TypeSafeContext 类型安全的 Context 值管理
type TypeSafeContext struct {
    tracer trace.Tracer
}

func NewTypeSafeContext() *TypeSafeContext {
    return &TypeSafeContext{
        tracer: otel.Tracer("type-safe-context"),
    }
}

// WithRequestID 添加请求 ID
func WithRequestID(ctx context.Context, requestID string) context.Context {
    return context.WithValue(ctx, requestIDKey, requestID)
}

// GetRequestID 获取请求 ID
func GetRequestID(ctx context.Context) (string, bool) {
    requestID, ok := ctx.Value(requestIDKey).(string)
    return requestID, ok
}

// MustGetRequestID 获取请求 ID（如果不存在则 panic）
func MustGetRequestID(ctx context.Context) string {
    requestID, ok := GetRequestID(ctx)
    if !ok {
        panic("request ID not found in context")
    }
    return requestID
}

// WithUserID 添加用户 ID
func WithUserID(ctx context.Context, userID int64) context.Context {
    return context.WithValue(ctx, userIDKey, userID)
}

// GetUserID 获取用户 ID
func GetUserID(ctx context.Context) (int64, bool) {
    userID, ok := ctx.Value(userIDKey).(int64)
    return userID, ok
}

// WithTenantID 添加租户 ID
func WithTenantID(ctx context.Context, tenantID string) context.Context {
    return context.WithValue(ctx, tenantIDKey, tenantID)
}

// GetTenantID 获取租户 ID
func GetTenantID(ctx context.Context) (string, bool) {
    tenantID, ok := ctx.Value(tenantIDKey).(string)
    return tenantID, ok
}

// WithCorrelationID 添加关联 ID
func WithCorrelationID(ctx context.Context, correlationID string) context.Context {
    return context.WithValue(ctx, correlationIDKey, correlationID)
}

// GetCorrelationID 获取关联 ID
func GetCorrelationID(ctx context.Context) (string, bool) {
    correlationID, ok := ctx.Value(correlationIDKey).(string)
    return correlationID, ok
}

// UseContextValues 使用 Context 值的示例
func (tsc *TypeSafeContext) UseContextValues(ctx context.Context) error {
    ctx, span := tsc.tracer.Start(ctx, "use-context-values")
    defer span.End()

    // 添加值到 context
    ctx = WithRequestID(ctx, "req-123")
    ctx = WithUserID(ctx, 456)
    ctx = WithTenantID(ctx, "tenant-789")
    ctx = WithCorrelationID(ctx, "corr-abc")

    // 读取值并添加到 span
    if requestID, ok := GetRequestID(ctx); ok {
        span.SetAttributes(attribute.String("request.id", requestID))
    }

    if userID, ok := GetUserID(ctx); ok {
        span.SetAttributes(attribute.Int64("user.id", userID))
    }

    if tenantID, ok := GetTenantID(ctx); ok {
        span.SetAttributes(attribute.String("tenant.id", tenantID))
    }

    if correlationID, ok := GetCorrelationID(ctx); ok {
        span.SetAttributes(attribute.String("correlation.id", correlationID))
    }

    return nil
}
```

### 2.2 追踪元数据管理

```go
package observability

import (
    "context"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TraceMetadata 追踪元数据
type TraceMetadata struct {
    ServiceName    string
    ServiceVersion string
    Environment    string
    DeploymentID   string
    Region         string
}

type metadataKey struct{}

// WithTraceMetadata 添加追踪元数据
func WithTraceMetadata(ctx context.Context, metadata *TraceMetadata) context.Context {
    return context.WithValue(ctx, metadataKey{}, metadata)
}

// GetTraceMetadata 获取追踪元数据
func GetTraceMetadata(ctx context.Context) (*TraceMetadata, bool) {
    metadata, ok := ctx.Value(metadataKey{}).(*TraceMetadata)
    return metadata, ok
}

// MetadataManager 元数据管理器
type MetadataManager struct {
    tracer trace.Tracer
}

func NewMetadataManager() *MetadataManager {
    return &MetadataManager{
        tracer: otel.Tracer("metadata-manager"),
    }
}

// EnrichSpanWithMetadata 用元数据丰富 Span
func (mm *MetadataManager) EnrichSpanWithMetadata(ctx context.Context) {
    span := trace.SpanFromContext(ctx)
    if !span.IsRecording() {
        return
    }

    metadata, ok := GetTraceMetadata(ctx)
    if !ok {
        return
    }

    span.SetAttributes(
        attribute.String("service.name", metadata.ServiceName),
        attribute.String("service.version", metadata.ServiceVersion),
        attribute.String("service.environment", metadata.Environment),
        attribute.String("service.deployment.id", metadata.DeploymentID),
        attribute.String("service.region", metadata.Region),
    )
}

// ProcessWithMetadata 使用元数据处理请求
func (mm *MetadataManager) ProcessWithMetadata(ctx context.Context) error {
    // 创建元数据
    metadata := &TraceMetadata{
        ServiceName:    "user-service",
        ServiceVersion: "v1.2.3",
        Environment:    "production",
        DeploymentID:   "deploy-abc123",
        Region:         "us-west-2",
    }

    // 添加到 context
    ctx = WithTraceMetadata(ctx, metadata)

    ctx, span := mm.tracer.Start(ctx, "process-with-metadata")
    defer span.End()

    // 自动丰富 span
    mm.EnrichSpanWithMetadata(ctx)

    return nil
}
```

### 2.3 请求范围的数据

```go
package observability

import (
    "context"
    "fmt"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// RequestData 请求范围的数据
type RequestData struct {
    StartTime     time.Time
    Method        string
    Path          string
    Headers       map[string]string
    Query         map[string]string
    ResponseTime  time.Duration
    StatusCode    int
    BytesReceived int64
    BytesSent     int64

    mu sync.RWMutex
}

func NewRequestData(method, path string) *RequestData {
    return &RequestData{
        StartTime: time.Now(),
        Method:    method,
        Path:      path,
        Headers:   make(map[string]string),
        Query:     make(map[string]string),
    }
}

// SetResponseTime 设置响应时间
func (rd *RequestData) SetResponseTime(duration time.Duration) {
    rd.mu.Lock()
    defer rd.mu.Unlock()
    rd.ResponseTime = duration
}

// SetStatusCode 设置状态码
func (rd *RequestData) SetStatusCode(code int) {
    rd.mu.Lock()
    defer rd.mu.Unlock()
    rd.StatusCode = code
}

// AddHeader 添加请求头
func (rd *RequestData) AddHeader(key, value string) {
    rd.mu.Lock()
    defer rd.mu.Unlock()
    rd.Headers[key] = value
}

// ToSpanAttributes 转换为 Span 属性
func (rd *RequestData) ToSpanAttributes() []attribute.KeyValue {
    rd.mu.RLock()
    defer rd.mu.RUnlock()

    attrs := []attribute.KeyValue{
        attribute.String("http.method", rd.Method),
        attribute.String("http.path", rd.Path),
        attribute.Int64("http.request.duration_ms", rd.ResponseTime.Milliseconds()),
        attribute.Int("http.status_code", rd.StatusCode),
        attribute.Int64("http.request.body.size", rd.BytesReceived),
        attribute.Int64("http.response.body.size", rd.BytesSent),
    }

    return attrs
}

type requestDataKey struct{}

// WithRequestData 添加请求数据
func WithRequestData(ctx context.Context, data *RequestData) context.Context {
    return context.WithValue(ctx, requestDataKey{}, data)
}

// GetRequestData 获取请求数据
func GetRequestData(ctx context.Context) (*RequestData, bool) {
    data, ok := ctx.Value(requestDataKey{}).(*RequestData)
    return data, ok
}

// RequestDataManager 请求数据管理器
type RequestDataManager struct {
    tracer trace.Tracer
}

func NewRequestDataManager() *RequestDataManager {
    return &RequestDataManager{
        tracer: otel.Tracer("request-data-manager"),
    }
}

// ProcessRequest 处理请求
func (rdm *RequestDataManager) ProcessRequest(
    ctx context.Context,
    method string,
    path string,
) error {
    // 创建请求数据
    reqData := NewRequestData(method, path)
    reqData.AddHeader("User-Agent", "MyClient/1.0")
    reqData.AddHeader("Content-Type", "application/json")

    // 添加到 context
    ctx = WithRequestData(ctx, reqData)

    ctx, span := rdm.tracer.Start(ctx, "process-request")
    defer func() {
        // 完成时记录所有数据
        if data, ok := GetRequestData(ctx); ok {
            data.SetResponseTime(time.Since(data.StartTime))
            span.SetAttributes(data.ToSpanAttributes()...)
        }
        span.End()
    }()

    // 模拟处理
    time.Sleep(50 * time.Millisecond)

    // 设置响应
    if data, ok := GetRequestData(ctx); ok {
        data.SetStatusCode(200)
        data.BytesSent = 1024
    }

    return nil
}
```

---

## 3. Go 1.25.1 Context 增强

### 3.1 WithoutCancel 深入应用

```go
package observability

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// BackgroundTaskManager 后台任务管理器（使用 WithoutCancel）
type BackgroundTaskManager struct {
    tracer trace.Tracer
}

func NewBackgroundTaskManager() *BackgroundTaskManager {
    return &BackgroundTaskManager{
        tracer: otel.Tracer("background-task-manager"),
    }
}

// LaunchDetachedTask 启动分离的后台任务
func (btm *BackgroundTaskManager) LaunchDetachedTask(
    parentCtx context.Context,
    taskName string,
    task func(context.Context) error,
) {
    // Go 1.25.1: 使用 WithoutCancel 创建分离的 context
    // 保留追踪信息和值，但不受父 context 取消影响
    detachedCtx := context.WithoutCancel(parentCtx)

    go func() {
        ctx, span := btm.tracer.Start(detachedCtx, taskName,
            trace.WithAttributes(
                attribute.Bool("task.detached", true),
                attribute.String("task.type", "background"),
            ),
        )
        defer span.End()

        if err := task(ctx); err != nil {
            span.RecordError(err)
            fmt.Printf("Background task %s failed: %v\n", taskName, err)
        } else {
            span.SetAttributes(attribute.Bool("task.completed", true))
        }
    }()
}

// ProcessWithCleanup 处理请求并启动清理任务
func (btm *BackgroundTaskManager) ProcessWithCleanup(
    ctx context.Context,
) error {
    ctx, span := btm.tracer.Start(ctx, "process-with-cleanup")
    defer span.End()

    // 主要业务逻辑
    if err := btm.mainLogic(ctx); err != nil {
        return err
    }

    // 启动后台清理任务（即使请求结束也要继续）
    btm.LaunchDetachedTask(ctx, "cleanup-temp-files", func(ctx context.Context) error {
        time.Sleep(5 * time.Second) // 模拟长时间清理
        fmt.Println("Cleanup completed")
        return nil
    })

    // 启动后台分析任务
    btm.LaunchDetachedTask(ctx, "analytics-processing", func(ctx context.Context) error {
        time.Sleep(3 * time.Second) // 模拟数据分析
        fmt.Println("Analytics completed")
        return nil
    })

    return nil
}

func (btm *BackgroundTaskManager) mainLogic(ctx context.Context) error {
    _, span := btm.tracer.Start(ctx, "main-logic")
    defer span.End()

    time.Sleep(100 * time.Millisecond)
    return nil
}

// CacheWarmer 缓存预热器
type CacheWarmer struct {
    tracer trace.Tracer
}

func NewCacheWarmer() *CacheWarmer {
    return &CacheWarmer{
        tracer: otel.Tracer("cache-warmer"),
    }
}

// WarmupCache 预热缓存（不受请求取消影响）
func (cw *CacheWarmer) WarmupCache(requestCtx context.Context, keys []string) {
    // 创建分离的 context，保留追踪信息
    warmupCtx := context.WithoutCancel(requestCtx)

    go func() {
        ctx, span := cw.tracer.Start(warmupCtx, "cache-warmup",
            trace.WithAttributes(
                attribute.Int("cache.keys_count", len(keys)),
            ),
        )
        defer span.End()

        for i, key := range keys {
            // 即使原始请求被取消，预热任务也会继续
            if err := cw.warmupKey(ctx, key); err != nil {
                span.SetAttributes(
                    attribute.String(fmt.Sprintf("cache.key.%d.error", i), err.Error()),
                )
            }
        }

        span.SetAttributes(attribute.Bool("cache.warmup.completed", true))
    }()
}

func (cw *CacheWarmer) warmupKey(ctx context.Context, key string) error {
    _, span := cw.tracer.Start(ctx, "warmup-key")
    defer span.End()

    span.SetAttributes(attribute.String("cache.key", key))

    // 模拟加载
    time.Sleep(100 * time.Millisecond)
    return nil
}
```

### 3.2 WithDeadlineCause 高级用法

```go
package observability

import (
    "context"
    "errors"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TimeoutReason 超时原因
type TimeoutReason string

const (
    TimeoutReasonSLA         TimeoutReason = "sla_exceeded"
    TimeoutReasonDBSlow      TimeoutReason = "database_slow"
    TimeoutReasonAPITimeout  TimeoutReason = "api_timeout"
    TimeoutReasonRateLimit   TimeoutReason = "rate_limit_wait"
    TimeoutReasonCircuitOpen TimeoutReason = "circuit_breaker_open"
)

// TimeoutError 超时错误（包含原因）
type TimeoutError struct {
    Reason   TimeoutReason
    Message  string
    Deadline time.Time
    Elapsed  time.Duration
}

func (e *TimeoutError) Error() string {
    return fmt.Sprintf("timeout (%s): %s (deadline: %v, elapsed: %v)",
        e.Reason, e.Message, e.Deadline, e.Elapsed)
}

// TimeoutManager 超时管理器
type TimeoutManager struct {
    tracer trace.Tracer
}

func NewTimeoutManager() *TimeoutManager {
    return &TimeoutManager{
        tracer: otel.Tracer("timeout-manager"),
    }
}

// ExecuteWithSLA 执行操作并设置 SLA 超时
func (tm *TimeoutManager) ExecuteWithSLA(
    parentCtx context.Context,
    sla time.Duration,
    operation func(context.Context) error,
) error {
    start := time.Now()
    deadline := start.Add(sla)

    // Go 1.25.1: 使用 WithDeadlineCause 设置带原因的超时
    timeoutErr := &TimeoutError{
        Reason:   TimeoutReasonSLA,
        Message:  fmt.Sprintf("SLA of %v exceeded", sla),
        Deadline: deadline,
    }

    ctx, cancel := context.WithDeadlineCause(parentCtx, deadline, timeoutErr)
    defer cancel()

    ctx, span := tm.tracer.Start(ctx, "execute-with-sla",
        trace.WithAttributes(
            attribute.Int64("sla.timeout_ms", sla.Milliseconds()),
            attribute.String("sla.deadline", deadline.Format(time.RFC3339)),
        ),
    )
    defer span.End()

    err := operation(ctx)

    // 记录实际耗时
    elapsed := time.Since(start)
    span.SetAttributes(
        attribute.Int64("operation.duration_ms", elapsed.Milliseconds()),
        attribute.Bool("sla.met", elapsed <= sla),
    )

    if err != nil {
        // Go 1.25.1: 获取超时原因
        if cause := context.Cause(ctx); cause != nil {
            if timeoutErr, ok := cause.(*TimeoutError); ok {
                timeoutErr.Elapsed = elapsed

                span.SetAttributes(
                    attribute.String("timeout.reason", string(timeoutErr.Reason)),
                    attribute.String("timeout.message", timeoutErr.Message),
                )
            }

            span.RecordError(cause)
            span.SetStatus(codes.Error, "timeout with cause")
            return cause
        }

        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "completed within SLA")
    return nil
}

// DatabaseQueryWithTimeout 数据库查询超时
func (tm *TimeoutManager) DatabaseQueryWithTimeout(
    parentCtx context.Context,
    query string,
) error {
    timeout := 500 * time.Millisecond
    deadline := time.Now().Add(timeout)

    timeoutErr := &TimeoutError{
        Reason:   TimeoutReasonDBSlow,
        Message:  "Database query too slow",
        Deadline: deadline,
    }

    ctx, cancel := context.WithDeadlineCause(parentCtx, deadline, timeoutErr)
    defer cancel()

    ctx, span := tm.tracer.Start(ctx, "database-query",
        trace.WithAttributes(
            attribute.String("db.query", query),
            attribute.Int64("db.timeout_ms", timeout.Milliseconds()),
        ),
    )
    defer span.End()

    // 模拟慢查询
    select {
    case <-time.After(1 * time.Second):
        return nil
    case <-ctx.Done():
        if cause := context.Cause(ctx); cause != nil {
            span.RecordError(cause)
            return cause
        }
        return ctx.Err()
    }
}

// ChainedTimeouts 链式超时
func (tm *TimeoutManager) ChainedTimeouts(parentCtx context.Context) error {
    ctx, span := tm.tracer.Start(parentCtx, "chained-timeouts")
    defer span.End()

    // 第一层：总体超时 (5 秒)
    overallTimeoutErr := &TimeoutError{
        Reason:  TimeoutReasonSLA,
        Message: "Overall operation timeout",
    }
    ctx, cancel1 := context.WithDeadlineCause(ctx,
        time.Now().Add(5*time.Second), overallTimeoutErr)
    defer cancel1()

    // 第二层：API 调用超时 (2 秒)
    apiTimeoutErr := &TimeoutError{
        Reason:  TimeoutReasonAPITimeout,
        Message: "API call timeout",
    }
    apiCtx, cancel2 := context.WithDeadlineCause(ctx,
        time.Now().Add(2*time.Second), apiTimeoutErr)
    defer cancel2()

    // 执行 API 调用
    if err := tm.callAPI(apiCtx); err != nil {
        // 判断是哪一层的超时
        if cause := context.Cause(apiCtx); cause != nil {
            if timeoutErr, ok := cause.(*TimeoutError); ok {
                span.SetAttributes(
                    attribute.String("timeout.layer", string(timeoutErr.Reason)),
                )
            }
        }
        return err
    }

    return nil
}

func (tm *TimeoutManager) callAPI(ctx context.Context) error {
    _, span := tm.tracer.Start(ctx, "call-api")
    defer span.End()

    // 模拟 API 调用
    time.Sleep(100 * time.Millisecond)
    return nil
}
```

### 3.3 AfterFunc 清理模式

```go
package observability

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// CleanupManager 清理管理器（使用 AfterFunc）
type CleanupManager struct {
    tracer trace.Tracer
}

func NewCleanupManager() *CleanupManager {
    return &CleanupManager{
        tracer: otel.Tracer("cleanup-manager"),
    }
}

// ProcessWithAutoCleanup 处理操作并自动清理
func (cm *CleanupManager) ProcessWithAutoCleanup(
    parentCtx context.Context,
) error {
    ctx, cancel := context.WithTimeout(parentCtx, 2*time.Second)
    defer cancel()

    // Go 1.25.1: 使用 AfterFunc 注册清理函数
    // 当 context 被取消时自动执行
    stop := context.AfterFunc(ctx, func() {
        // 这个函数在 context 取消时自动执行
        _, span := cm.tracer.Start(context.Background(), "auto-cleanup")
        defer span.End()

        span.SetAttributes(
            attribute.Bool("cleanup.auto", true),
            attribute.String("cleanup.trigger", "context_cancelled"),
        )

        fmt.Println("Auto cleanup triggered")
        // 执行清理逻辑
        cm.performCleanup()
    })
    defer stop() // 如果正常完成，取消清理

    ctx, span := cm.tracer.Start(ctx, "process-with-auto-cleanup")
    defer span.End()

    // 模拟处理
    time.Sleep(100 * time.Millisecond)

    return nil
}

func (cm *CleanupManager) performCleanup() {
    fmt.Println("Performing cleanup...")
    time.Sleep(50 * time.Millisecond)
}

// ResourceManager 资源管理器（使用 AfterFunc）
type ResourceManager struct {
    tracer trace.Tracer
}

func NewResourceManager() *ResourceManager {
    return &ResourceManager{
        tracer: otel.Tracer("resource-manager"),
    }
}

// AcquireResource 获取资源（自动释放）
func (rm *ResourceManager) AcquireResource(
    ctx context.Context,
    resourceID string,
) error {
    ctx, span := rm.tracer.Start(ctx, "acquire-resource",
        trace.WithAttributes(
            attribute.String("resource.id", resourceID),
        ),
    )
    defer span.End()

    // 获取资源
    resource, err := rm.acquire(ctx, resourceID)
    if err != nil {
        return err
    }

    // 注册自动释放
    stop := context.AfterFunc(ctx, func() {
        _, releaseSpan := rm.tracer.Start(context.Background(), "auto-release-resource")
        defer releaseSpan.End()

        releaseSpan.SetAttributes(
            attribute.String("resource.id", resourceID),
            attribute.Bool("release.auto", true),
        )

        rm.release(resource)
    })
    defer stop()

    // 使用资源
    return rm.useResource(ctx, resource)
}

func (rm *ResourceManager) acquire(ctx context.Context, resourceID string) (interface{}, error) {
    return map[string]string{"id": resourceID}, nil
}

func (rm *ResourceManager) release(resource interface{}) {
    fmt.Printf("Released resource: %v\n", resource)
}

func (rm *ResourceManager) useResource(ctx context.Context, resource interface{}) error {
    time.Sleep(50 * time.Millisecond)
    return nil
}
```

---

*由于篇幅限制，我将继续补充剩余章节。是否需要我继续完成这个文档的其余部分（包括 Span Context 传播、超时策略、并发模式等）？*

---

## 参考资料

1. **Go Context**:
   - [Go Context Package](https://pkg.go.dev/context)
   - [Go Concurrency Patterns: Context](https://go.dev/blog/context)
   - [Context Best Practices](https://go.dev/blog/context-and-structs)

2. **Go 1.25.1 新特性**:
   - [Go 1.25 Release Notes](https://go.dev/doc/go1.25)
   - [Context Enhancements](https://go.dev/doc/go1.25#context)

3. **OpenTelemetry Context**:
   - [Context Propagation](https://opentelemetry.io/docs/languages/go/instrumentation/#context-propagation)
   - [Baggage API](https://opentelemetry.io/docs/specs/otel/baggage/api/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025年10月8日  
**状态**: 🚧 进行中

---

**下一步**: 继续补充 Span Context 传播、超时策略、并发模式、性能优化等章节。

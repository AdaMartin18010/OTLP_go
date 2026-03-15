# Context 管理

## 📋 目录

- [Context 管理](#context-管理)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Context 传播](#context-传播)
    - [1. Span Context 传播](#1-span-context-传播)
    - [2. Baggage 传播](#2-baggage-传播)
  - [Go 1.25.1 Context 特性](#go-1251-context-特性)
    - [1. WithoutCancel](#1-withoutcancel)
    - [2. AfterFunc](#2-afterfunc)
    - [3. WithDeadlineCause](#3-withdeadlinecause)
  - [Context 生命周期](#context-生命周期)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

**Context** 是 OpenTelemetry 中传播追踪信息（Trace、Baggage）的核心机制。

```text
Context
    ├─ Span (TraceID, SpanID)
    ├─ Baggage (key-value pairs)
    └─ 其他元数据
```

---

## Context 传播

### 1. Span Context 传播

```go
import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

func handleRequest(ctx context.Context) {
    // 从 Context 获取 Tracer
    tracer := otel.Tracer("myapp")
    
    // 创建 Span (自动继承父 Span)
    ctx, span := tracer.Start(ctx, "handleRequest")
    defer span.End()
    
    // 传播 Context 到下游
    processData(ctx)
}

func processData(ctx context.Context) {
    // 从 Context 获取当前 Span
    span := trace.SpanFromContext(ctx)
    span.AddEvent("processing data")
    
    // 创建子 Span
    ctx, childSpan := otel.Tracer("myapp").Start(ctx, "processData")
    defer childSpan.End()
    
    // 继续传播
    saveToDatabase(ctx)
}
```

### 2. Baggage 传播

```go
import "go.opentelemetry.io/otel/baggage"

func handleRequest(ctx context.Context) {
    // 添加 Baggage
    member, _ := baggage.NewMember("user.id", "12345")
    bag, _ := baggage.New(member)
    ctx = baggage.ContextWithBaggage(ctx, bag)
    
    // 传播到下游
    processData(ctx)
}

func processData(ctx context.Context) {
    // 从 Context 获取 Baggage
    bag := baggage.FromContext(ctx)
    userID := bag.Member("user.id").Value()
    
    log.Printf("Processing for user: %s", userID)
}
```

---

## Go 1.25.1 Context 特性

### 1. WithoutCancel

创建不受父 Context 取消影响的子 Context：

```go
func handleRequest(ctx context.Context) {
    // 主请求 Context (可能被取消)
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    // 创建独立 Context 用于后台任务
    backgroundCtx := context.WithoutCancel(ctx)
    
    // 后台任务不受主请求取消影响
    go func() {
        ctx, span := otel.Tracer("myapp").Start(backgroundCtx, "background")
        defer span.End()
        
        // 长时间运行的任务
        time.Sleep(10*time.Second)
        saveMetrics(ctx)
    }()
    
    // 主请求处理
    return processRequest(ctx)
}
```

### 2. AfterFunc

在 Context 取消后执行清理函数：

```go
func handleRequest(ctx context.Context) {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    // 注册取消后的清理函数
    stop := context.AfterFunc(ctx, func() {
        log.Println("Request cancelled, cleaning up...")
        
        // 导出剩余的 Span
        if err := tracer.ForceFlush(context.Background()); err != nil {
            log.Printf("Failed to flush: %v", err)
        }
    })
    defer stop()
    
    // 处理请求
    return processRequest(ctx)
}
```

### 3. WithDeadlineCause

设置带原因的截止时间：

```go
import "errors"

var ErrSlowQuery = errors.New("database query too slow")

func queryDatabase(ctx context.Context) error {
    // 设置 5 秒超时，并附带原因
    ctx, cancel := context.WithDeadlineCause(
        ctx,
        time.Now().Add(5*time.Second),
        ErrSlowQuery,
    )
    defer cancel()
    
    ctx, span := otel.Tracer("myapp").Start(ctx, "database.query")
    defer span.End()
    
    // 执行查询
    if err := db.QueryContext(ctx, "SELECT ..."); err != nil {
        // 检查是否超时
        if ctx.Err() != nil {
            // 获取超时原因
            cause := context.Cause(ctx)
            span.RecordError(cause)
            span.SetStatus(codes.Error, cause.Error())
            return cause
        }
        return err
    }
    
    return nil
}
```

---

## Context 生命周期

```go
func handleHTTPRequest(w http.ResponseWriter, r *http.Request) {
    // 1. 从 HTTP 请求提取 Context
    ctx := r.Context()
    
    // 2. 创建 Span
    ctx, span := otel.Tracer("myapp").Start(ctx, "http.request")
    defer span.End()
    
    // 3. 添加 Baggage
    member, _ := baggage.NewMember("request.id", generateRequestID())
    bag, _ := baggage.New(member)
    ctx = baggage.ContextWithBaggage(ctx, bag)
    
    // 4. 传播到业务逻辑
    result, err := businessLogic(ctx)
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    // 5. 返回响应
    json.NewEncoder(w).Encode(result)
}

func businessLogic(ctx context.Context) (interface{}, error) {
    // Context 自动包含 Span 和 Baggage
    ctx, span := otel.Tracer("myapp").Start(ctx, "businessLogic")
    defer span.End()
    
    // 传播到数据库层
    return fetchFromDatabase(ctx)
}

func fetchFromDatabase(ctx context.Context) (interface{}, error) {
    // 继续传播
    ctx, span := otel.Tracer("myapp").Start(ctx, "database.fetch")
    defer span.End()
    
    // 从 Context 获取 Baggage
    bag := baggage.FromContext(ctx)
    requestID := bag.Member("request.id").Value()
    
    span.SetAttributes(attribute.String("request.id", requestID))
    
    // 执行数据库查询
    return db.QueryContext(ctx, "SELECT ...")
}
```

---

## 最佳实践

```go
// ✅ 正确: 始终传播 Context
func processRequest(ctx context.Context) {
    ctx, span := otel.Tracer("myapp").Start(ctx, "process")
    defer span.End()
    
    doWork(ctx) // 传播 Context
}

// ❌ 错误: 不传播 Context
func processRequest(ctx context.Context) {
    ctx, span := otel.Tracer("myapp").Start(ctx, "process")
    defer span.End()
    
    doWork(context.Background()) // 丢失追踪信息
}

// ✅ 正确: 使用 Context 超时
func callExternalAPI(ctx context.Context) error {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    ctx, span := otel.Tracer("myapp").Start(ctx, "external.api")
    defer span.End()
    
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    resp, err := http.DefaultClient.Do(req)
    return err
}

// ✅ 正确: 后台任务使用 WithoutCancel
func handleRequest(ctx context.Context) {
    // 处理请求
    ctx, span := otel.Tracer("myapp").Start(ctx, "request")
    defer span.End()
    
    // 异步日志聚合（不受请求取消影响）
    go func() {
        bgCtx := context.WithoutCancel(ctx)
        aggregateLogs(bgCtx)
    }()
}

// ✅ 正确: 使用 AfterFunc 清理资源
func processWithCleanup(ctx context.Context) {
    resource := acquireResource()
    
    stop := context.AfterFunc(ctx, func() {
        resource.Close()
    })
    defer stop()
    
    // 处理逻辑
}
```

---

## 常见问题

**Q1: 为什么不能存储 Context？**

```go
// ❌ 错误: 存储 Context
type Handler struct {
    ctx context.Context // 不要这样做
}

// ✅ 正确: 通过参数传递
type Handler struct {}

func (h *Handler) Handle(ctx context.Context) {
    // 使用参数传递的 Context
}
```

**Q2: 如何在 goroutine 中传播 Context？**

```go
// ✅ 正确: 传递 Context 或使用 WithoutCancel
func handleRequest(ctx context.Context) {
    // 方案 1: 传递完整 Context (goroutine 会被取消)
    go func(ctx context.Context) {
        processData(ctx)
    }(ctx)
    
    // 方案 2: 使用 WithoutCancel (goroutine 不被取消)
    go func() {
        bgCtx := context.WithoutCancel(ctx)
        processData(bgCtx)
    }()
}
```

**Q3: Context 超时后如何处理 Span？**

```go
func handleTimeout(ctx context.Context) {
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    ctx, span := otel.Tracer("myapp").Start(ctx, "operation")
    defer span.End()
    
    if err := longRunningOperation(ctx); err != nil {
        if ctx.Err() == context.DeadlineExceeded {
            span.SetStatus(codes.Error, "timeout")
            span.RecordError(ctx.Err())
        }
        return err
    }
}
```

---

## 参考资源

- [Go Context Package](https://pkg.go.dev/context)
- [OpenTelemetry Context](https://opentelemetry.io/docs/specs/otel/context/)
- [02_Propagators.md](./02_Propagators.md)

---

**🎉 完成！Context 管理知识掌握！**

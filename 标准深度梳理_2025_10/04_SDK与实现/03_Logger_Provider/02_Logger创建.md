# Logger 创建

## 📋 目录

- [Logger 创建](#logger-创建)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Logger](#什么是-logger)
    - [创建流程](#创建流程)
  - [基本创建](#基本创建)
    - [1. 从全局 LoggerProvider 创建](#1-从全局-loggerprovider-创建)
    - [2. 从自定义 LoggerProvider 创建](#2-从自定义-loggerprovider-创建)
    - [3. 带选项创建](#3-带选项创建)
  - [slog 集成](#slog-集成)
    - [1. 基本集成](#1-基本集成)
    - [2. 结构化日志](#2-结构化日志)
    - [3. Context 传播](#3-context-传播)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. Logger 管理](#1-logger-管理)
    - [2. 模块级 Logger](#2-模块级-logger)
    - [3. Logger 包装](#3-logger-包装)
  - [日志级别](#日志级别)
    - [1. 级别配置](#1-级别配置)
    - [2. 动态级别](#2-动态级别)
    - [3. 级别过滤](#3-级别过滤)
  - [性能优化](#性能优化)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 Logger

**Logger** 是 OpenTelemetry Logs 中用于记录日志的工具。在 Go 中，通常通过 `slog` 与 OpenTelemetry 集成。

```text
LoggerProvider (全局)
    ↓
Logger (per InstrumentationScope)
    ↓
LogRecord (日志记录)
    ↓
Processor → Exporter → Backend
```

### 创建流程

```text
1. 应用启动时设置 LoggerProvider
2. 创建 slog Handler (otelslog)
3. 设置为默认 slog logger
4. 使用 slog 记录日志
5. 应用关闭时清理 LoggerProvider
```

---

## 基本创建

### 1. 从全局 LoggerProvider 创建

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/log"
)

func main() {
    // 从全局 LoggerProvider 获取 Logger
    logger := otel.GetLoggerProvider().Logger("myapp")
    
    // 使用 Logger
    logger.Emit(context.Background(), log.Record{
        Body:            log.StringValue("Application started"),
        SeverityNumber:  log.SeverityInfo,
        SeverityText:    "INFO",
    })
}
```

### 2. 从自定义 LoggerProvider 创建

```go
package main

import (
    "go.opentelemetry.io/otel/sdk/log"
)

func main() {
    // 创建自定义 LoggerProvider
    lp := log.NewLoggerProvider()
    
    // 从自定义 LoggerProvider 获取 Logger
    logger := lp.Logger("myapp")
    
    // 使用 Logger
    logger.Emit(context.Background(), log.Record{
        Body: log.StringValue("message"),
    })
}
```

### 3. 带选项创建

```go
package main

import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/log"
)

func main() {
    // 带选项创建 Logger
    logger := otel.GetLoggerProvider().Logger(
        "myapp",
        log.WithInstrumentationVersion("1.0.0"),
        log.WithSchemaURL("https://opentelemetry.io/schemas/1.21.0"),
    )
}
```

---

## slog 集成

### 1. 基本集成

```go
package main

import (
    "log/slog"
    "go.opentelemetry.io/contrib/bridges/otelslog"
    "go.opentelemetry.io/otel"
)

func main() {
    // 获取 LoggerProvider
    lp := otel.GetLoggerProvider()
    
    // 创建 slog Handler
    handler := otelslog.NewHandler("myapp",
        otelslog.WithLoggerProvider(lp),
    )
    
    // 设置为默认 logger
    logger := slog.New(handler)
    slog.SetDefault(logger)
    
    // 使用 slog
    slog.Info("Application started")
    slog.Error("Failed to connect", "error", err)
}
```

### 2. 结构化日志

```go
package main

import (
    "log/slog"
)

func main() {
    // 基本日志
    slog.Info("User logged in",
        "user_id", "12345",
        "username", "john",
        "ip", "192.168.1.1",
    )
    
    // 嵌套属性
    slog.Info("Request processed",
        slog.Group("http",
            "method", "GET",
            "path", "/api/users",
            "status", 200,
        ),
        slog.Group("timing",
            "duration_ms", 45,
            "db_ms", 23,
        ),
    )
    
    // 使用 With 添加共享属性
    logger := slog.With("service", "api", "version", "1.0.0")
    logger.Info("Service started")
    logger.Error("Service error", "error", err)
}
```

### 3. Context 传播

```go
package main

import (
    "context"
    "log/slog"
    "go.opentelemetry.io/otel/trace"
)

func processRequest(ctx context.Context) {
    // 从 Context 获取 Span
    span := trace.SpanFromContext(ctx)
    spanContext := span.SpanContext()
    
    // 日志中包含 Trace ID 和 Span ID
    slog.InfoContext(ctx, "Processing request",
        "trace_id", spanContext.TraceID().String(),
        "span_id", spanContext.SpanID().String(),
        "user_id", "12345",
    )
    
    // otelslog 自动注入 Trace Context
    // 如果使用 otelslog.NewHandler，无需手动添加
}

// 自动注入示例
func automaticTraceContext(ctx context.Context) {
    // otelslog Handler 自动从 Context 提取 Trace 信息
    slog.InfoContext(ctx, "Request completed",
        "duration_ms", 100,
    )
    // 导出的日志会自动包含 trace_id 和 span_id
}
```

---

## Go 1.25.1 实现

### 1. Logger 管理

```go
package logging

import (
    "log/slog"
    "sync"
)

var (
    defaultLogger *slog.Logger
    loggerOnce    sync.Once
)

// GetLogger 获取默认 Logger
func GetLogger() *slog.Logger {
    loggerOnce.Do(func() {
        handler := otelslog.NewHandler("myapp")
        defaultLogger = slog.New(handler)
    })
    return defaultLogger
}

// SetLogger 设置默认 Logger
func SetLogger(logger *slog.Logger) {
    slog.SetDefault(logger)
}

// 使用示例
func main() {
    logger := GetLogger()
    logger.Info("Application started")
}
```

### 2. 模块级 Logger

```go
package api

import (
    "log/slog"
    "go.opentelemetry.io/contrib/bridges/otelslog"
)

// 模块级 Logger
var logger *slog.Logger

func init() {
    handler := otelslog.NewHandler("myapp/api")
    logger = slog.New(handler)
}

func HandleRequest(ctx context.Context) {
    logger.InfoContext(ctx, "Handling request",
        "path", "/api/users",
        "method", "GET",
    )
    
    // 业务逻辑
    result, err := processRequest(ctx)
    if err != nil {
        logger.ErrorContext(ctx, "Failed to process request",
            "error", err,
        )
        return
    }
    
    logger.InfoContext(ctx, "Request completed",
        "result_count", len(result),
    )
}
```

### 3. Logger 包装

```go
package logging

import (
    "log/slog"
    "context"
)

// AppLogger 应用 Logger 包装
type AppLogger struct {
    logger *slog.Logger
}

// NewAppLogger 创建 AppLogger
func NewAppLogger(name string) *AppLogger {
    handler := otelslog.NewHandler(name)
    return &AppLogger{
        logger: slog.New(handler),
    }
}

// WithFields 添加字段
func (l *AppLogger) WithFields(fields map[string]interface{}) *AppLogger {
    args := make([]any, 0, len(fields)*2)
    for k, v := range fields {
        args = append(args, k, v)
    }
    return &AppLogger{
        logger: l.logger.With(args...),
    }
}

// Info 记录 Info 日志
func (l *AppLogger) Info(ctx context.Context, msg string, fields map[string]interface{}) {
    args := fieldsToArgs(fields)
    l.logger.InfoContext(ctx, msg, args...)
}

// Error 记录 Error 日志
func (l *AppLogger) Error(ctx context.Context, msg string, err error, fields map[string]interface{}) {
    args := fieldsToArgs(fields)
    args = append(args, "error", err)
    l.logger.ErrorContext(ctx, msg, args...)
}

// Warn 记录 Warn 日志
func (l *AppLogger) Warn(ctx context.Context, msg string, fields map[string]interface{}) {
    args := fieldsToArgs(fields)
    l.logger.WarnContext(ctx, msg, args...)
}

// Debug 记录 Debug 日志
func (l *AppLogger) Debug(ctx context.Context, msg string, fields map[string]interface{}) {
    args := fieldsToArgs(fields)
    l.logger.DebugContext(ctx, msg, args...)
}

func fieldsToArgs(fields map[string]interface{}) []any {
    args := make([]any, 0, len(fields)*2)
    for k, v := range fields {
        args = append(args, k, v)
    }
    return args
}

// 使用示例
func main() {
    logger := NewAppLogger("myapp")
    
    // 添加共享字段
    logger = logger.WithFields(map[string]interface{}{
        "service": "api",
        "version": "1.0.0",
    })
    
    ctx := context.Background()
    logger.Info(ctx, "Service started", map[string]interface{}{
        "port": 8080,
    })
    
    logger.Error(ctx, "Database error", err, map[string]interface{}{
        "query": "SELECT * FROM users",
    })
}
```

---

## 日志级别

### 1. 级别配置

```go
package main

import (
    "log/slog"
    "os"
)

func setupLogger() *slog.Logger {
    // 配置日志级别
    var level slog.Level
    switch os.Getenv("LOG_LEVEL") {
    case "DEBUG":
        level = slog.LevelDebug
    case "INFO":
        level = slog.LevelInfo
    case "WARN":
        level = slog.LevelWarn
    case "ERROR":
        level = slog.LevelError
    default:
        level = slog.LevelInfo
    }
    
    // 创建带级别的 Handler
    handler := otelslog.NewHandler("myapp")
    
    // 包装 LevelHandler
    levelHandler := slog.NewLevelHandler(level, handler)
    
    return slog.New(levelHandler)
}

// 使用示例
func main() {
    logger := setupLogger()
    slog.SetDefault(logger)
    
    // 根据配置的级别过滤
    slog.Debug("Debug message")   // 可能不输出
    slog.Info("Info message")     // 输出
    slog.Warn("Warning message")  // 输出
    slog.Error("Error message")   // 输出
}
```

### 2. 动态级别

```go
package logging

import (
    "log/slog"
    "sync/atomic"
)

// DynamicLevelHandler 动态级别 Handler
type DynamicLevelHandler struct {
    level   atomic.Value // slog.Level
    handler slog.Handler
}

func NewDynamicLevelHandler(initialLevel slog.Level, handler slog.Handler) *DynamicLevelHandler {
    h := &DynamicLevelHandler{
        handler: handler,
    }
    h.level.Store(initialLevel)
    return h
}

// SetLevel 设置日志级别
func (h *DynamicLevelHandler) SetLevel(level slog.Level) {
    h.level.Store(level)
}

// GetLevel 获取当前级别
func (h *DynamicLevelHandler) GetLevel() slog.Level {
    return h.level.Load().(slog.Level)
}

// Enabled 判断是否启用
func (h *DynamicLevelHandler) Enabled(ctx context.Context, level slog.Level) bool {
    return level >= h.GetLevel()
}

// Handle 处理日志
func (h *DynamicLevelHandler) Handle(ctx context.Context, r slog.Record) error {
    if !h.Enabled(ctx, r.Level) {
        return nil
    }
    return h.handler.Handle(ctx, r)
}

// WithAttrs 添加属性
func (h *DynamicLevelHandler) WithAttrs(attrs []slog.Attr) slog.Handler {
    return &DynamicLevelHandler{
        level:   h.level,
        handler: h.handler.WithAttrs(attrs),
    }
}

// WithGroup 添加组
func (h *DynamicLevelHandler) WithGroup(name string) slog.Handler {
    return &DynamicLevelHandler{
        level:   h.level,
        handler: h.handler.WithGroup(name),
    }
}

// 使用示例
var dynamicHandler *DynamicLevelHandler

func init() {
    baseHandler := otelslog.NewHandler("myapp")
    dynamicHandler = NewDynamicLevelHandler(slog.LevelInfo, baseHandler)
    slog.SetDefault(slog.New(dynamicHandler))
}

// HTTP 端点动态调整级别
func handleSetLogLevel(w http.ResponseWriter, r *http.Request) {
    levelStr := r.URL.Query().Get("level")
    
    var level slog.Level
    switch levelStr {
    case "DEBUG":
        level = slog.LevelDebug
    case "INFO":
        level = slog.LevelInfo
    case "WARN":
        level = slog.LevelWarn
    case "ERROR":
        level = slog.LevelError
    default:
        http.Error(w, "Invalid level", http.StatusBadRequest)
        return
    }
    
    dynamicHandler.SetLevel(level)
    fmt.Fprintf(w, "Log level set to %s", levelStr)
}
```

### 3. 级别过滤

```go
// 根据模块设置不同级别
func setupModularLogger() {
    // API 模块: INFO
    apiHandler := otelslog.NewHandler("myapp/api")
    apiLogger := slog.New(slog.NewLevelHandler(slog.LevelInfo, apiHandler))
    
    // Database 模块: DEBUG
    dbHandler := otelslog.NewHandler("myapp/database")
    dbLogger := slog.New(slog.NewLevelHandler(slog.LevelDebug, dbHandler))
    
    // 使用
    apiLogger.Info("API request")
    dbLogger.Debug("SQL query", "query", "SELECT *")
}
```

---

## 性能优化

```go
// 1. 延迟字段计算
slog.Info("User info",
    slog.Any("user", func() interface{} {
        // 仅在日志级别启用时计算
        return expensiveUserComputation()
    }),
)

// 2. 使用 With 缓存共享字段
var logger = slog.With(
    "service", "api",
    "version", "1.0.0",
)

func handler(ctx context.Context) {
    // 复用 logger，避免重复添加字段
    logger.InfoContext(ctx, "Request")
}

// 3. 避免不必要的字符串格式化
// ❌ 错误
slog.Info(fmt.Sprintf("User %s logged in", userID))

// ✅ 正确
slog.Info("User logged in", "user_id", userID)

// 4. 使用 LogValuer 接口
type User struct {
    ID   string
    Name string
}

func (u User) LogValue() slog.Value {
    return slog.GroupValue(
        slog.String("id", u.ID),
        slog.String("name", u.Name),
    )
}

// 使用
user := User{ID: "123", Name: "John"}
slog.Info("User action", "user", user)

// 5. 条件日志
if slog.Default().Enabled(ctx, slog.LevelDebug) {
    // 仅在 Debug 级别启用时执行
    data := expensiveComputation()
    slog.Debug("Debug info", "data", data)
}
```

---

## 最佳实践

```go
// ✅ 正确: 使用 Context 传播 Trace
func handler(ctx context.Context) {
    slog.InfoContext(ctx, "Processing request")
    // Trace ID 自动注入
}

// ❌ 错误: 不使用 Context
func handler(ctx context.Context) {
    slog.Info("Processing request") // 丢失 Trace 信息
}

// ✅ 正确: 结构化字段
slog.Info("User action",
    "user_id", "123",
    "action", "login",
    "ip", "192.168.1.1",
)

// ❌ 错误: 字符串拼接
slog.Info("User 123 performed login from 192.168.1.1")

// ✅ 正确: 使用适当的级别
slog.Debug("Detailed debug info")
slog.Info("Normal operation")
slog.Warn("Warning condition")
slog.Error("Error occurred", "error", err)

// ✅ 正确: 包含错误信息
if err != nil {
    slog.Error("Failed to save user",
        "error", err,
        "user_id", userID,
    )
}

// ❌ 错误: 丢失错误详情
if err != nil {
    slog.Error("Failed to save user")
}
```

---

## 常见问题

**Q1: 如何在日志中包含 Trace ID？**

```go
// 方案 1: 使用 otelslog (自动)
handler := otelslog.NewHandler("myapp")
slog.SetDefault(slog.New(handler))

func handler(ctx context.Context) {
    // 自动包含 trace_id 和 span_id
    slog.InfoContext(ctx, "Processing")
}

// 方案 2: 手动添加
func handler(ctx context.Context) {
    span := trace.SpanFromContext(ctx)
    sc := span.SpanContext()
    
    slog.InfoContext(ctx, "Processing",
        "trace_id", sc.TraceID().String(),
        "span_id", sc.SpanID().String(),
    )
}
```

**Q2: 如何设置不同模块的日志级别？**

```go
// 为每个模块创建独立 logger
apiLogger := slog.New(slog.NewLevelHandler(
    slog.LevelInfo,
    otelslog.NewHandler("myapp/api"),
))

dbLogger := slog.New(slog.NewLevelHandler(
    slog.LevelDebug,
    otelslog.NewHandler("myapp/database"),
))
```

**Q3: slog 与传统 log 包的区别？**

```text
slog (推荐):
✅ 结构化日志
✅ 高性能
✅ 原生支持级别
✅ OpenTelemetry 集成

log (传统):
❌ 非结构化
❌ 性能较差
❌ 无级别支持
❌ 难以集成

推荐:
- 新项目: slog
- 旧项目: 逐步迁移到 slog
```

---

## 参考资源

- [Go slog Package](https://pkg.go.dev/log/slog)
- [OpenTelemetry slog Bridge](https://pkg.go.dev/go.opentelemetry.io/contrib/bridges/otelslog)
- [01_Provider配置.md](./01_Provider配置.md)
- [03_处理器.md](./03_处理器.md)

---

**🎉 恭喜！你已经掌握了 Logger 创建和 slog 集成！**

现在你可以：

- ✅ 创建和配置 Logger
- ✅ 集成 Go slog
- ✅ 实现结构化日志
- ✅ 配置日志级别
- ✅ 优化日志性能

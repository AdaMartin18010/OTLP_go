# Grafana Loki 与 OTLP 完整集成指南（Go 1.25.1 - 2025版）

> **文档版本**: v1.0.0  
> **更新日期**: 2025-10-12  
> **Go 版本**: 1.25.1+  
> **Loki 版本**: 2.9.0+  
> **技术深度**: ⭐⭐⭐⭐⭐

---

## 📋 目录

- [Grafana Loki 与 OTLP 完整集成指南（Go 1.25.1 - 2025版）](#grafana-loki-与-otlp-完整集成指南go-1251---2025版)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [什么是 Grafana Loki？](#什么是-grafana-loki)
    - [核心特性](#核心特性)
    - [与其他方案对比](#与其他方案对比)
  - [Grafana Loki 概述](#grafana-loki-概述)
    - [架构设计](#架构设计)
    - [数据模型](#数据模型)
  - [完整集成示例](#完整集成示例)
    - [1. 基础配置](#1-基础配置)
      - [go.mod 依赖](#gomod-依赖)
    - [2. Loki Go Client](#2-loki-go-client)
    - [3. 结构化日志集成](#3-结构化日志集成)
    - [4. HTTP 请求日志中间件](#4-http-请求日志中间件)
    - [5. 追踪上下文集成](#5-追踪上下文集成)
  - [高级特性](#高级特性)
    - [1. LogQL 查询语言](#1-logql-查询语言)
      - [Go 中使用 LogQL](#go-中使用-logql)
    - [2. 日志管道处理](#2-日志管道处理)
    - [3. 日志聚合统计](#3-日志聚合统计)
  - [性能优化](#性能优化)
    - [1. 批处理优化](#1-批处理优化)
    - [2. 压缩优化](#2-压缩优化)
    - [3. 标签优化](#3-标签优化)
  - [生产部署](#生产部署)
    - [1. Docker Compose 部署](#1-docker-compose-部署)
      - [Loki 配置](#loki-配置)
      - [Promtail 配置](#promtail-配置)
    - [2. Kubernetes 部署](#2-kubernetes-部署)
  - [最佳实践](#最佳实践)
    - [1. 标签设计](#1-标签设计)
    - [2. 日志结构化](#2-日志结构化)
    - [3. 保留策略](#3-保留策略)
  - [故障排查](#故障排查)
    - [常见问题](#常见问题)
  - [总结](#总结)

---

## 简介

### 什么是 Grafana Loki？

**Grafana Loki** 是一个水平可扩展、高可用的多租户日志聚合系统，受 Prometheus 启发。
它不索引日志内容，只索引标签，使其成本效益极高。

### 核心特性

```text
✅ 核心优势:
  - 成本极低 (无全文索引)
  - 云原生设计
  - 与 Grafana 深度集成
  - 支持 LogQL 查询语言
  - 水平可扩展

✅ 性能指标:
  - 摄入速率: 100GB+/day per instance
  - 查询延迟: <1s (标签查询)
  - 存储成本: ~$0.02/GB/月
  - 压缩比: 10:1

✅ 集成能力:
  - Promtail (官方采集器)
  - Fluentd/Fluent Bit
  - Logstash
  - OTLP logs (实验性)
  - Docker/Kubernetes 原生

✅ 部署模式:
  - 单机版 (monolithic)
  - 微服务模式 (distributor/ingester/querier)
  - 简单可扩展模式 (SSD)
```

### 与其他方案对比

| 特性 | Loki | Elasticsearch | Splunk | CloudWatch |
|------|------|---------------|--------|------------|
| 成本 | 极低 | 高 | 极高 | 高 |
| 索引方式 | 仅标签 | 全文索引 | 全文索引 | 部分索引 |
| 查询能力 | LogQL | DSL | SPL | CloudWatch Logs Insights |
| 扩展性 | 优秀 | 优秀 | 优秀 | 优秀 |
| 运维复杂度 | 低 | 高 | 中 | 低 |
| Grafana集成 | 原生 | 插件 | 插件 | 插件 |

---

## Grafana Loki 概述

### 架构设计

```text
┌─────────────────────────────────────────────────────────┐
│                    Loki 架构                            │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐               │
│  │ Promtail │  │ Fluentd  │  │  App Log │               │
│  │  Agent   │  │  Plugin  │  │  Client  │               │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘               │
│       │             │             │                     │
│       └─────────────┼─────────────┘                     │
│                     │                                   │
│            ┌────────▼────────┐                          │
│            │   Distributor   │  (负载均衡/限流)          │
│            └────────┬────────┘                          │
│                     │                                   │
│       ┌─────────────┼─────────────┐                     │
│       │             │             │                     │
│  ┌────▼────┐  ┌────▼────┐  ┌────▼────┐                  │
│  │Ingester │  │Ingester │  │Ingester │  (缓冲/压缩)      │
│  │ Node 1  │  │ Node 2  │  │ Node 3  │                  │
│  └────┬────┘  └────┬────┘  └────┬────┘                  │
│       │             │             │                     │
│       └─────────────┼─────────────┘                     │
│                     │                                   │
│            ┌────────▼────────┐                          │
│            │ Object Storage  │  (S3/GCS/Azure)          │
│            └────────┬────────┘                          │
│                     │                                   │
│            ┌────────▼────────┐                          │
│            │  Query Frontend │  (查询调度)               │
│            └────────┬────────┘                          │
│                     │                                   │
│            ┌────────▼────────┐                          │
│            │     Querier     │  (日志检索)               │
│            └────────┬────────┘                          │
│                     │                                   │
│            ┌────────▼────────┐                          │
│            │     Grafana     │                          │
│            └─────────────────┘                          │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 数据模型

Loki 使用标签+时间戳+日志行的模型：

```text
{job="api-server", env="prod", level="error"} 2025-01-15T10:30:45Z Error: database connection failed
```

---

## 完整集成示例

### 1. 基础配置

#### go.mod 依赖

```go
module github.com/example/loki-integration

go 1.25.1

require (
    github.com/grafana/loki/pkg/push v0.0.0-20240115000000-000000000000
    github.com/prometheus/client_golang v1.18.0
    github.com/prometheus/common v0.45.0
    go.opentelemetry.io/otel v1.24.0
    go.opentelemetry.io/otel/exporters/otlp/otlplog v0.0.0-20240115000000-000000000000
    go.opentelemetry.io/otel/sdk/log v0.0.0-20240115000000-000000000000
    go.uber.org/zap v1.26.0
)
```

### 2. Loki Go Client

```go
package loki

import (
    "bytes"
    "context"
    "encoding/json"
    "fmt"
    "io"
    "net/http"
    "time"

    "github.com/prometheus/common/model"
)

// LokiClient Loki 客户端
type LokiClient struct {
    url    string
    client *http.Client
    labels model.LabelSet
}

// NewLokiClient 创建 Loki 客户端
func NewLokiClient(url string, labels model.LabelSet) *LokiClient {
    return &LokiClient{
        url:    url,
        client: &http.Client{Timeout: 10 * time.Second},
        labels: labels,
    }
}

// PushRequest Loki push 请求
type PushRequest struct {
    Streams []Stream `json:"streams"`
}

// Stream 日志流
type Stream struct {
    Stream map[string]string `json:"stream"`
    Values [][]string        `json:"values"`
}

// SendLog 发送日志
func (c *LokiClient) SendLog(ctx context.Context, line string, labels map[string]string) error {
    // 合并默认标签和自定义标签
    streamLabels := make(map[string]string)
    for k, v := range c.labels {
        streamLabels[string(k)] = string(v)
    }
    for k, v := range labels {
        streamLabels[k] = v
    }

    // 构建 push 请求
    timestamp := fmt.Sprintf("%d", time.Now().UnixNano())
    req := PushRequest{
        Streams: []Stream{
            {
                Stream: streamLabels,
                Values: [][]string{
                    {timestamp, line},
                },
            },
        },
    }

    // 序列化
    body, err := json.Marshal(req)
    if err != nil {
        return fmt.Errorf("failed to marshal request: %w", err)
    }

    // 发送请求
    pushURL := fmt.Sprintf("%s/loki/api/v1/push", c.url)
    httpReq, err := http.NewRequestWithContext(ctx, "POST", pushURL, bytes.NewReader(body))
    if err != nil {
        return fmt.Errorf("failed to create request: %w", err)
    }
    httpReq.Header.Set("Content-Type", "application/json")

    resp, err := c.client.Do(httpReq)
    if err != nil {
        return fmt.Errorf("failed to send request: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusNoContent && resp.StatusCode != http.StatusOK {
        body, _ := io.ReadAll(resp.Body)
        return fmt.Errorf("unexpected status code: %d, body: %s", resp.StatusCode, string(body))
    }

    return nil
}

// BatchSendLogs 批量发送日志
func (c *LokiClient) BatchSendLogs(ctx context.Context, logs []LogEntry) error {
    if len(logs) == 0 {
        return nil
    }

    // 按标签分组
    streamMap := make(map[string]*Stream)
    
    for _, log := range logs {
        // 合并标签
        streamLabels := make(map[string]string)
        for k, v := range c.labels {
            streamLabels[string(k)] = string(v)
        }
        for k, v := range log.Labels {
            streamLabels[k] = v
        }

        // 计算 stream key
        streamKey := labelsKey(streamLabels)
        
        if _, exists := streamMap[streamKey]; !exists {
            streamMap[streamKey] = &Stream{
                Stream: streamLabels,
                Values: [][]string{},
            }
        }

        timestamp := fmt.Sprintf("%d", log.Timestamp.UnixNano())
        streamMap[streamKey].Values = append(streamMap[streamKey].Values, []string{timestamp, log.Line})
    }

    // 构建请求
    streams := make([]Stream, 0, len(streamMap))
    for _, stream := range streamMap {
        streams = append(streams, *stream)
    }

    req := PushRequest{Streams: streams}
    body, err := json.Marshal(req)
    if err != nil {
        return fmt.Errorf("failed to marshal request: %w", err)
    }

    // 发送请求
    pushURL := fmt.Sprintf("%s/loki/api/v1/push", c.url)
    httpReq, err := http.NewRequestWithContext(ctx, "POST", pushURL, bytes.NewReader(body))
    if err != nil {
        return fmt.Errorf("failed to create request: %w", err)
    }
    httpReq.Header.Set("Content-Type", "application/json")

    resp, err := c.client.Do(httpReq)
    if err != nil {
        return fmt.Errorf("failed to send request: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusNoContent && resp.StatusCode != http.StatusOK {
        respBody, _ := io.ReadAll(resp.Body)
        return fmt.Errorf("unexpected status code: %d, body: %s", resp.StatusCode, string(respBody))
    }

    return nil
}

// LogEntry 日志条目
type LogEntry struct {
    Timestamp time.Time
    Line      string
    Labels    map[string]string
}

// labelsKey 生成标签键
func labelsKey(labels map[string]string) string {
    var buf bytes.Buffer
    for k, v := range labels {
        buf.WriteString(k)
        buf.WriteString("=")
        buf.WriteString(v)
        buf.WriteString(",")
    }
    return buf.String()
}
```

### 3. 结构化日志集成

```go
package loki

import (
    "context"
    "encoding/json"
    "fmt"
    "sync"
    "time"

    "github.com/prometheus/common/model"
    "go.uber.org/zap"
    "go.uber.org/zap/zapcore"
)

// LokiWriter Loki 日志写入器
type LokiWriter struct {
    client     *LokiClient
    buffer     []LogEntry
    bufferSize int
    mu         sync.Mutex
    flushTimer *time.Timer
    done       chan struct{}
}

// NewLokiWriter 创建 Loki 写入器
func NewLokiWriter(lokiURL string, labels model.LabelSet, bufferSize int, flushInterval time.Duration) *LokiWriter {
    writer := &LokiWriter{
        client:     NewLokiClient(lokiURL, labels),
        buffer:     make([]LogEntry, 0, bufferSize),
        bufferSize: bufferSize,
        done:       make(chan struct{}),
    }

    // 定期刷新
    writer.flushTimer = time.AfterFunc(flushInterval, func() {
        writer.Flush(context.Background())
        writer.flushTimer.Reset(flushInterval)
    })

    return writer
}

// Write 实现 io.Writer 接口
func (w *LokiWriter) Write(p []byte) (n int, err error) {
    w.mu.Lock()
    defer w.mu.Unlock()

    // 解析日志行
    var logData map[string]interface{}
    if err := json.Unmarshal(p, &logData); err != nil {
        // 如果不是 JSON，直接使用原始文本
        w.buffer = append(w.buffer, LogEntry{
            Timestamp: time.Now(),
            Line:      string(p),
            Labels:    map[string]string{},
        })
    } else {
        // 提取标签
        labels := extractLabels(logData)
        w.buffer = append(w.buffer, LogEntry{
            Timestamp: time.Now(),
            Line:      string(p),
            Labels:    labels,
        })
    }

    // 如果缓冲区满，触发刷新
    if len(w.buffer) >= w.bufferSize {
        go w.Flush(context.Background())
    }

    return len(p), nil
}

// Flush 刷新缓冲区
func (w *LokiWriter) Flush(ctx context.Context) error {
    w.mu.Lock()
    if len(w.buffer) == 0 {
        w.mu.Unlock()
        return nil
    }

    logs := make([]LogEntry, len(w.buffer))
    copy(logs, w.buffer)
    w.buffer = w.buffer[:0]
    w.mu.Unlock()

    return w.client.BatchSendLogs(ctx, logs)
}

// Close 关闭写入器
func (w *LokiWriter) Close() error {
    close(w.done)
    if w.flushTimer != nil {
        w.flushTimer.Stop()
    }
    return w.Flush(context.Background())
}

// extractLabels 从日志数据中提取标签
func extractLabels(logData map[string]interface{}) map[string]string {
    labels := make(map[string]string)
    
    // 提取常见字段作为标签
    if level, ok := logData["level"].(string); ok {
        labels["level"] = level
    }
    if service, ok := logData["service"].(string); ok {
        labels["service"] = service
    }
    if env, ok := logData["env"].(string); ok {
        labels["env"] = env
    }
    
    return labels
}

// NewZapLogger 创建带 Loki 后端的 Zap Logger
func NewZapLogger(lokiURL string, labels model.LabelSet) (*zap.Logger, error) {
    // 创建 Loki 写入器
    lokiWriter := NewLokiWriter(lokiURL, labels, 100, 5*time.Second)

    // 创建编码器配置
    encoderConfig := zapcore.EncoderConfig{
        TimeKey:        "ts",
        LevelKey:       "level",
        NameKey:        "logger",
        CallerKey:      "caller",
        FunctionKey:    zapcore.OmitKey,
        MessageKey:     "msg",
        StacktraceKey:  "stacktrace",
        LineEnding:     zapcore.DefaultLineEnding,
        EncodeLevel:    zapcore.LowercaseLevelEncoder,
        EncodeTime:     zapcore.ISO8601TimeEncoder,
        EncodeDuration: zapcore.SecondsDurationEncoder,
        EncodeCaller:   zapcore.ShortCallerEncoder,
    }

    // 创建 JSON 编码器
    encoder := zapcore.NewJSONEncoder(encoderConfig)

    // 创建 core (多输出)
    core := zapcore.NewTee(
        zapcore.NewCore(encoder, zapcore.AddSync(lokiWriter), zapcore.DebugLevel), // Loki
        zapcore.NewCore(encoder, zapcore.AddSync(zapcore.Lock(zapcore.AddSync(zapcore.Lock(zapcore.Lock(zapcore.Lock(zapcore.AddSync(nil)))))))), // Stdout (简化)
    )

    return zap.New(core, zap.AddCaller(), zap.AddStacktrace(zapcore.ErrorLevel)), nil
}

// 使用示例
func ExampleLokiZapLogger() {
    labels := model.LabelSet{
        "app":     "my-service",
        "env":     "production",
        "version": "1.0.0",
    }

    logger, err := NewZapLogger("http://localhost:3100", labels)
    if err != nil {
        panic(err)
    }
    defer logger.Sync()

    // 使用 logger
    logger.Info("Application started",
        zap.String("user_id", "123"),
        zap.Int("port", 8080),
    )

    logger.Error("Database connection failed",
        zap.String("database", "postgres"),
        zap.Error(fmt.Errorf("connection timeout")),
    )
}
```

### 4. HTTP 请求日志中间件

```go
package loki

import (
    "context"
    "net/http"
    "time"

    "github.com/prometheus/common/model"
    "go.uber.org/zap"
)

// HTTPLoggingMiddleware HTTP 日志中间件
type HTTPLoggingMiddleware struct {
    logger *zap.Logger
    client *LokiClient
}

// NewHTTPLoggingMiddleware 创建 HTTP 日志中间件
func NewHTTPLoggingMiddleware(lokiURL string, labels model.LabelSet) (*HTTPLoggingMiddleware, error) {
    logger, err := NewZapLogger(lokiURL, labels)
    if err != nil {
        return nil, err
    }

    return &HTTPLoggingMiddleware{
        logger: logger,
        client: NewLokiClient(lokiURL, labels),
    }, nil
}

// Middleware 中间件函数
func (m *HTTPLoggingMiddleware) Middleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()

        // 包装 ResponseWriter
        ww := &responseWriter{ResponseWriter: w, statusCode: http.StatusOK}

        // 调用下一个处理器
        next.ServeHTTP(ww, r)

        // 记录日志
        duration := time.Since(start)
        
        m.logger.Info("HTTP request",
            zap.String("method", r.Method),
            zap.String("path", r.URL.Path),
            zap.String("remote_addr", r.RemoteAddr),
            zap.Int("status_code", ww.statusCode),
            zap.Duration("duration", duration),
            zap.Int64("response_size", ww.size),
            zap.String("user_agent", r.UserAgent()),
        )

        // 错误请求发送到 Loki
        if ww.statusCode >= 400 {
            labels := map[string]string{
                "level":  "error",
                "method": r.Method,
                "path":   r.URL.Path,
                "status": fmt.Sprintf("%d", ww.statusCode),
            }

            logLine := fmt.Sprintf("%s %s %d %v", r.Method, r.URL.Path, ww.statusCode, duration)
            m.client.SendLog(context.Background(), logLine, labels)
        }
    })
}

type responseWriter struct {
    http.ResponseWriter
    statusCode int
    size       int64
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    size, err := rw.ResponseWriter.Write(b)
    rw.size += int64(size)
    return size, err
}
```

### 5. 追踪上下文集成

```go
package loki

import (
    "context"
    "fmt"

    "go.opentelemetry.io/otel/trace"
    "go.uber.org/zap"
    "go.uber.org/zap/zapcore"
)

// TraceContextHook 追踪上下文钩子
type TraceContextHook struct{}

// TraceContextField 追踪上下文字段
func TraceContextField(ctx context.Context) []zapcore.Field {
    span := trace.SpanFromContext(ctx)
    if !span.SpanContext().IsValid() {
        return nil
    }

    sc := span.SpanContext()
    return []zapcore.Field{
        zap.String("trace_id", sc.TraceID().String()),
        zap.String("span_id", sc.SpanID().String()),
        zap.Bool("trace_sampled", sc.TraceFlags().IsSampled()),
    }
}

// LogWithTrace 带追踪上下文的日志
func LogWithTrace(ctx context.Context, logger *zap.Logger, level zapcore.Level, msg string, fields ...zapcore.Field) {
    // 添加追踪字段
    traceFields := TraceContextField(ctx)
    allFields := append(traceFields, fields...)

    // 根据级别记录日志
    switch level {
    case zapcore.DebugLevel:
        logger.Debug(msg, allFields...)
    case zapcore.InfoLevel:
        logger.Info(msg, allFields...)
    case zapcore.WarnLevel:
        logger.Warn(msg, allFields...)
    case zapcore.ErrorLevel:
        logger.Error(msg, allFields...)
    case zapcore.DPanicLevel:
        logger.DPanic(msg, allFields...)
    case zapcore.PanicLevel:
        logger.Panic(msg, allFields...)
    case zapcore.FatalLevel:
        logger.Fatal(msg, allFields...)
    }
}

// 使用示例
func ExampleTraceContext(ctx context.Context) {
    labels := model.LabelSet{
        "app": "demo",
    }

    logger, _ := NewZapLogger("http://localhost:3100", labels)
    
    // 带追踪上下文的日志
    LogWithTrace(ctx, logger, zapcore.InfoLevel, "Processing request",
        zap.String("user_id", "123"),
        zap.String("action", "create_order"),
    )
}
```

---

## 高级特性

### 1. LogQL 查询语言

LogQL 是 Loki 的查询语言，类似 PromQL。

```logql
# 1. 基础查询 - 查询特定标签的日志
{job="api-server", env="prod"}

# 2. 正则过滤 - 包含 "error"
{job="api-server"} |= "error"

# 3. 正则排除 - 不包含 "debug"
{job="api-server"} != "debug"

# 4. 正则表达式匹配
{job="api-server"} |~ "error|failed|exception"

# 5. JSON 解析
{job="api-server"} | json | level="error"

# 6. Pattern 解析
{job="api-server"} | pattern `<method> <path> <status>`

# 7. 日志频率统计
rate({job="api-server"}[5m])

# 8. 错误率统计
sum(rate({job="api-server", level="error"}[5m])) / sum(rate({job="api-server"}[5m]))

# 9. 按标签聚合
sum(rate({job="api-server"}[5m])) by (env)

# 10. Top N 错误
topk(10, sum(rate({level="error"}[1h])) by (service))

# 11. 指标查询 - 计算字节数
sum(rate({job="api-server"} | json | __error__="" | unwrap bytes [5m])) by (env)

# 12. 组合查询 - 慢请求且有错误
{job="api-server"} | json | duration > 1000 and level="error"
```

#### Go 中使用 LogQL

```go
package loki

import (
    "context"
    "encoding/json"
    "fmt"
    "io"
    "net/http"
    "net/url"
    "time"
)

// LokiQuerier Loki 查询客户端
type LokiQuerier struct {
    baseURL string
    client  *http.Client
}

// NewLokiQuerier 创建查询客户端
func NewLokiQuerier(baseURL string) *LokiQuerier {
    return &LokiQuerier{
        baseURL: baseURL,
        client:  &http.Client{Timeout: 30 * time.Second},
    }
}

// QueryResult 查询结果
type QueryResult struct {
    Status string `json:"status"`
    Data   struct {
        ResultType string `json:"resultType"`
        Result     []struct {
            Stream map[string]string `json:"stream"`
            Values [][]string        `json:"values"`
        } `json:"result"`
    } `json:"data"`
}

// Query 执行 LogQL 查询
func (q *LokiQuerier) Query(ctx context.Context, query string, limit int, start, end time.Time) (*QueryResult, error) {
    params := url.Values{}
    params.Add("query", query)
    params.Add("limit", fmt.Sprintf("%d", limit))
    if !start.IsZero() {
        params.Add("start", fmt.Sprintf("%d", start.UnixNano()))
    }
    if !end.IsZero() {
        params.Add("end", fmt.Sprintf("%d", end.UnixNano()))
    }

    queryURL := fmt.Sprintf("%s/loki/api/v1/query_range?%s", q.baseURL, params.Encode())
    
    req, err := http.NewRequestWithContext(ctx, "GET", queryURL, nil)
    if err != nil {
        return nil, err
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()

    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return nil, err
    }

    var result QueryResult
    if err := json.Unmarshal(body, &result); err != nil {
        return nil, err
    }

    return &result, nil
}

// QueryLabels 查询标签值
func (q *LokiQuerier) QueryLabels(ctx context.Context, labelName string) ([]string, error) {
    labelsURL := fmt.Sprintf("%s/loki/api/v1/label/%s/values", q.baseURL, labelName)
    
    req, err := http.NewRequestWithContext(ctx, "GET", labelsURL, nil)
    if err != nil {
        return nil, err
    }

    resp, err := q.client.Do(req)
    if err != nil {
        return nil, err
    }
    defer resp.Body.Close()

    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return nil, err
    }

    var result struct {
        Status string   `json:"status"`
        Data   []string `json:"data"`
    }

    if err := json.Unmarshal(body, &result); err != nil {
        return nil, err
    }

    return result.Data, nil
}

// 使用示例
func ExampleLogQL() {
    querier := NewLokiQuerier("http://localhost:3100")
    ctx := context.Background()

    // 查询错误日志
    result, err := querier.Query(ctx,
        `{job="api-server", level="error"}`,
        100,
        time.Now().Add(-1*time.Hour),
        time.Now(),
    )
    if err != nil {
        fmt.Printf("Query failed: %v\n", err)
        return
    }

    fmt.Printf("Found %d log streams\n", len(result.Data.Result))
    for _, stream := range result.Data.Result {
        fmt.Printf("Stream: %v, Entries: %d\n", stream.Stream, len(stream.Values))
    }

    // 查询标签值
    labels, err := querier.QueryLabels(ctx, "level")
    if err != nil {
        fmt.Printf("Failed to query labels: %v\n", err)
        return
    }

    fmt.Printf("Available log levels: %v\n", labels)
}
```

### 2. 日志管道处理

```go
package loki

import (
    "encoding/json"
    "regexp"
    "strings"
)

// LogPipeline 日志管道
type LogPipeline struct {
    filters []LogFilter
}

// LogFilter 日志过滤器
type LogFilter func(line string) (string, bool)

// NewLogPipeline 创建日志管道
func NewLogPipeline() *LogPipeline {
    return &LogPipeline{
        filters: []LogFilter{},
    }
}

// AddFilter 添加过滤器
func (p *LogPipeline) AddFilter(filter LogFilter) *LogPipeline {
    p.filters = append(p.filters, filter)
    return p
}

// Process 处理日志行
func (p *LogPipeline) Process(line string) (string, bool) {
    for _, filter := range p.filters {
        var keep bool
        line, keep = filter(line)
        if !keep {
            return "", false
        }
    }
    return line, true
}

// 常用过滤器

// RegexFilter 正则过滤器
func RegexFilter(pattern string, match bool) LogFilter {
    re := regexp.MustCompile(pattern)
    return func(line string) (string, bool) {
        matched := re.MatchString(line)
        if match {
            return line, matched
        }
        return line, !matched
    }
}

// JSONExtractor JSON 提取器
func JSONExtractor(fields []string) LogFilter {
    return func(line string) (string, bool) {
        var data map[string]interface{}
        if err := json.Unmarshal([]byte(line), &data); err != nil {
            return line, true // 不是 JSON，保持原样
        }

        extracted := make(map[string]interface{})
        for _, field := range fields {
            if val, ok := data[field]; ok {
                extracted[field] = val
            }
        }

        result, _ := json.Marshal(extracted)
        return string(result), true
    }
}

// SensitiveDataMasker 敏感数据脱敏
func SensitiveDataMasker() LogFilter {
    patterns := map[string]*regexp.Regexp{
        "email":      regexp.MustCompile(`\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b`),
        "phone":      regexp.MustCompile(`\b\d{3}[-.]?\d{3}[-.]?\d{4}\b`),
        "credit_card": regexp.MustCompile(`\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b`),
        "ssn":        regexp.MustCompile(`\b\d{3}-\d{2}-\d{4}\b`),
    }

    return func(line string) (string, bool) {
        result := line
        for _, re := range patterns {
            result = re.ReplaceAllString(result, "***REDACTED***")
        }
        return result, true
    }
}

// LevelFilter 日志级别过滤器
func LevelFilter(minLevel string) LogFilter {
    levels := map[string]int{
        "debug": 0,
        "info":  1,
        "warn":  2,
        "error": 3,
        "fatal": 4,
    }

    minLevelInt := levels[strings.ToLower(minLevel)]

    return func(line string) (string, bool) {
        var data map[string]interface{}
        if err := json.Unmarshal([]byte(line), &data); err != nil {
            return line, true
        }

        level, ok := data["level"].(string)
        if !ok {
            return line, true
        }

        levelInt := levels[strings.ToLower(level)]
        return line, levelInt >= minLevelInt
    }
}

// 使用示例
func ExampleLogPipeline() {
    pipeline := NewLogPipeline().
        AddFilter(RegexFilter("error|fatal", true)).      // 只保留包含 error 或 fatal 的行
        AddFilter(SensitiveDataMasker()).                  // 脱敏
        AddFilter(JSONExtractor([]string{"level", "msg", "ts"})) // 提取字段

    logs := []string{
        `{"level":"info","msg":"User logged in","email":"user@example.com"}`,
        `{"level":"error","msg":"Payment failed","card":"1234-5678-9012-3456"}`,
        `{"level":"debug","msg":"Debug info"}`,
    }

    for _, log := range logs {
        processed, keep := pipeline.Process(log)
        if keep {
            fmt.Println("Processed:", processed)
        } else {
            fmt.Println("Filtered out:", log)
        }
    }
}
```

### 3. 日志聚合统计

```go
package loki

import (
    "context"
    "fmt"
    "sync"
    "time"
)

// LogAggregator 日志聚合器
type LogAggregator struct {
    stats map[string]*LogStats
    mu    sync.RWMutex
}

// LogStats 日志统计
type LogStats struct {
    Count    int64
    Errors   int64
    Warnings int64
    LastSeen time.Time
}

// NewLogAggregator 创建日志聚合器
func NewLogAggregator() *LogAggregator {
    return &LogAggregator{
        stats: make(map[string]*LogStats),
    }
}

// Record 记录日志
func (a *LogAggregator) Record(service, level string) {
    a.mu.Lock()
    defer a.mu.Unlock()

    if _, exists := a.stats[service]; !exists {
        a.stats[service] = &LogStats{}
    }

    stats := a.stats[service]
    stats.Count++
    stats.LastSeen = time.Now()

    switch level {
    case "error":
        stats.Errors++
    case "warn":
        stats.Warnings++
    }
}

// GetStats 获取统计信息
func (a *LogAggregator) GetStats(service string) *LogStats {
    a.mu.RLock()
    defer a.mu.RUnlock()

    if stats, exists := a.stats[service]; exists {
        return stats
    }
    return &LogStats{}
}

// GetAllStats 获取所有统计信息
func (a *LogAggregator) GetAllStats() map[string]*LogStats {
    a.mu.RLock()
    defer a.mu.RUnlock()

    result := make(map[string]*LogStats)
    for k, v := range a.stats {
        result[k] = v
    }
    return result
}

// ReportMetrics 报告度量到 Loki
func (a *LogAggregator) ReportMetrics(ctx context.Context, client *LokiClient) error {
    stats := a.GetAllStats()

    for service, stat := range stats {
        logLine := fmt.Sprintf("service=%s count=%d errors=%d warnings=%d",
            service, stat.Count, stat.Errors, stat.Warnings)

        labels := map[string]string{
            "service": service,
            "type":    "metrics",
        }

        if err := client.SendLog(ctx, logLine, labels); err != nil {
            return err
        }
    }

    return nil
}
```

---

## 性能优化

### 1. 批处理优化

```go
package loki

import (
    "context"
    "sync"
    "time"
)

// BatchLogger 批处理日志记录器
type BatchLogger struct {
    client        *LokiClient
    buffer        []LogEntry
    batchSize     int
    flushInterval time.Duration
    mu            sync.Mutex
    done          chan struct{}
}

// NewBatchLogger 创建批处理日志记录器
func NewBatchLogger(client *LokiClient, batchSize int, flushInterval time.Duration) *BatchLogger {
    bl := &BatchLogger{
        client:        client,
        buffer:        make([]LogEntry, 0, batchSize),
        batchSize:     batchSize,
        flushInterval: flushInterval,
        done:          make(chan struct{}),
    }

    go bl.periodicFlush()
    return bl
}

// Log 记录日志
func (bl *BatchLogger) Log(line string, labels map[string]string) {
    bl.mu.Lock()
    defer bl.mu.Unlock()

    bl.buffer = append(bl.buffer, LogEntry{
        Timestamp: time.Now(),
        Line:      line,
        Labels:    labels,
    })

    if len(bl.buffer) >= bl.batchSize {
        go bl.flush()
    }
}

// flush 刷新缓冲区
func (bl *BatchLogger) flush() {
    bl.mu.Lock()
    if len(bl.buffer) == 0 {
        bl.mu.Unlock()
        return
    }

    logs := make([]LogEntry, len(bl.buffer))
    copy(logs, bl.buffer)
    bl.buffer = bl.buffer[:0]
    bl.mu.Unlock()

    ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
    defer cancel()

    if err := bl.client.BatchSendLogs(ctx, logs); err != nil {
        // 错误处理 (重试/记录到本地等)
        fmt.Printf("Failed to flush logs: %v\n", err)
    }
}

// periodicFlush 定期刷新
func (bl *BatchLogger) periodicFlush() {
    ticker := time.NewTicker(bl.flushInterval)
    defer ticker.Stop()

    for {
        select {
        case <-ticker.C:
            bl.flush()
        case <-bl.done:
            bl.flush()
            return
        }
    }
}

// Close 关闭记录器
func (bl *BatchLogger) Close() {
    close(bl.done)
    bl.flush()
}
```

### 2. 压缩优化

```go
package loki

import (
    "bytes"
    "compress/gzip"
    "context"
    "fmt"
    "io"
    "net/http"
)

// CompressedLokiClient 压缩的 Loki 客户端
type CompressedLokiClient struct {
    *LokiClient
}

// NewCompressedLokiClient 创建压缩客户端
func NewCompressedLokiClient(url string, labels model.LabelSet) *CompressedLokiClient {
    return &CompressedLokiClient{
        LokiClient: NewLokiClient(url, labels),
    }
}

// BatchSendLogsCompressed 批量发送压缩日志
func (c *CompressedLokiClient) BatchSendLogsCompressed(ctx context.Context, logs []LogEntry) error {
    if len(logs) == 0 {
        return nil
    }

    // 构建请求体
    req := c.buildPushRequest(logs)
    body, err := json.Marshal(req)
    if err != nil {
        return fmt.Errorf("failed to marshal request: %w", err)
    }

    // 压缩
    var compressed bytes.Buffer
    gz := gzip.NewWriter(&compressed)
    if _, err := gz.Write(body); err != nil {
        return fmt.Errorf("failed to compress: %w", err)
    }
    if err := gz.Close(); err != nil {
        return fmt.Errorf("failed to close gzip writer: %w", err)
    }

    // 发送请求
    pushURL := fmt.Sprintf("%s/loki/api/v1/push", c.url)
    httpReq, err := http.NewRequestWithContext(ctx, "POST", pushURL, &compressed)
    if err != nil {
        return fmt.Errorf("failed to create request: %w", err)
    }
    httpReq.Header.Set("Content-Type", "application/json")
    httpReq.Header.Set("Content-Encoding", "gzip")

    resp, err := c.client.Do(httpReq)
    if err != nil {
        return fmt.Errorf("failed to send request: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode != http.StatusNoContent && resp.StatusCode != http.StatusOK {
        respBody, _ := io.ReadAll(resp.Body)
        return fmt.Errorf("unexpected status code: %d, body: %s", resp.StatusCode, string(respBody))
    }

    return nil
}

func (c *CompressedLokiClient) buildPushRequest(logs []LogEntry) PushRequest {
    // 实现略...
    return PushRequest{}
}
```

### 3. 标签优化

```go
package loki

// LabelOptimizer 标签优化器
type LabelOptimizer struct {
    maxLabels      int
    allowedLabels  map[string]struct{}
    labelCache     map[string]map[string]string
}

// NewLabelOptimizer 创建标签优化器
func NewLabelOptimizer(maxLabels int, allowedLabels []string) *LabelOptimizer {
    allowed := make(map[string]struct{})
    for _, label := range allowedLabels {
        allowed[label] = struct{}{}
    }

    return &LabelOptimizer{
        maxLabels:     maxLabels,
        allowedLabels: allowed,
        labelCache:    make(map[string]map[string]string),
    }
}

// OptimizeLabels 优化标签
func (lo *LabelOptimizer) OptimizeLabels(labels map[string]string) map[string]string {
    optimized := make(map[string]string)
    count := 0

    for k, v := range labels {
        // 检查是否在允许列表中
        if _, allowed := lo.allowedLabels[k]; !allowed {
            continue
        }

        // 检查数量限制
        if count >= lo.maxLabels {
            break
        }

        optimized[k] = v
        count++
    }

    return optimized
}
```

---

## 生产部署

### 1. Docker Compose 部署

```yaml
# docker-compose.yml
version: '3.8'

services:
  loki:
    image: grafana/loki:2.9.0
    container_name: loki
    command: -config.file=/etc/loki/loki-config.yaml
    volumes:
      - ./loki-config.yaml:/etc/loki/loki-config.yaml
      - loki-data:/loki
    ports:
      - "3100:3100"
    networks:
      - logging
    restart: unless-stopped

  promtail:
    image: grafana/promtail:2.9.0
    container_name: promtail
    command: -config.file=/etc/promtail/promtail-config.yaml
    volumes:
      - ./promtail-config.yaml:/etc/promtail/promtail-config.yaml
      - /var/log:/var/log:ro
      - /var/lib/docker/containers:/var/lib/docker/containers:ro
    networks:
      - logging
    depends_on:
      - loki
    restart: unless-stopped

  grafana:
    image: grafana/grafana:latest
    container_name: grafana
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml
    ports:
      - "3000:3000"
    networks:
      - logging
    depends_on:
      - loki
    restart: unless-stopped

volumes:
  loki-data:
  grafana-data:

networks:
  logging:
    driver: bridge
```

#### Loki 配置

```yaml
# loki-config.yaml
auth_enabled: false

server:
  http_listen_port: 3100
  grpc_listen_port: 9096
  log_level: info

common:
  path_prefix: /loki
  storage:
    filesystem:
      chunks_directory: /loki/chunks
      rules_directory: /loki/rules
  replication_factor: 1
  ring:
    kvstore:
      store: inmemory

schema_config:
  configs:
    - from: 2020-10-24
      store: boltdb-shipper
      object_store: filesystem
      schema: v11
      index:
        prefix: index_
        period: 24h

storage_config:
  boltdb_shipper:
    active_index_directory: /loki/boltdb-shipper-active
    cache_location: /loki/boltdb-shipper-cache
    cache_ttl: 24h
    shared_store: filesystem
  filesystem:
    directory: /loki/chunks

compactor:
  working_directory: /loki/boltdb-shipper-compactor
  shared_store: filesystem

limits_config:
  reject_old_samples: true
  reject_old_samples_max_age: 168h
  ingestion_rate_mb: 10
  ingestion_burst_size_mb: 20
  max_query_series: 1000
  max_query_parallelism: 32

chunk_store_config:
  max_look_back_period: 0s

table_manager:
  retention_deletes_enabled: true
  retention_period: 720h  # 30 days

ruler:
  alertmanager_url: http://alertmanager:9093
```

#### Promtail 配置

```yaml
# promtail-config.yaml
server:
  http_listen_port: 9080
  grpc_listen_port: 0

positions:
  filename: /tmp/positions.yaml

clients:
  - url: http://loki:3100/loki/api/v1/push

scrape_configs:
  # Docker 容器日志
  - job_name: docker
    docker_sd_configs:
      - host: unix:///var/run/docker.sock
        refresh_interval: 5s
    relabel_configs:
      - source_labels: ['__meta_docker_container_name']
        regex: '/(.*)'
        target_label: 'container'
      - source_labels: ['__meta_docker_container_log_stream']
        target_label: 'stream'
      - source_labels: ['__meta_docker_container_label_com_docker_compose_project']
        target_label: 'project'
      - source_labels: ['__meta_docker_container_label_com_docker_compose_service']
        target_label: 'service'

  # 系统日志
  - job_name: system
    static_configs:
      - targets:
          - localhost
        labels:
          job: varlogs
          __path__: /var/log/*log
```

### 2. Kubernetes 部署

```yaml
# loki-deployment.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: loki-config
  namespace: logging
data:
  loki.yaml: |
    auth_enabled: false
    server:
      http_listen_port: 3100
    
    ingester:
      lifecycler:
        ring:
          kvstore:
            store: memberlist
          replication_factor: 1
      chunk_idle_period: 30m
      chunk_block_size: 262144
      chunk_retain_period: 1m
      max_transfer_retries: 0
    
    schema_config:
      configs:
        - from: 2020-10-24
          store: boltdb-shipper
          object_store: s3
          schema: v11
          index:
            prefix: index_
            period: 24h
    
    storage_config:
      boltdb_shipper:
        active_index_directory: /data/loki/boltdb-shipper-active
        cache_location: /data/loki/boltdb-shipper-cache
        shared_store: s3
      aws:
        s3: s3://us-east-1/my-loki-bucket
        s3forcepathstyle: true
    
    limits_config:
      ingestion_rate_mb: 10
      ingestion_burst_size_mb: 20

---
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: loki
  namespace: logging
spec:
  serviceName: loki
  replicas: 3
  selector:
    matchLabels:
      app: loki
  template:
    metadata:
      labels:
        app: loki
    spec:
      containers:
      - name: loki
        image: grafana/loki:2.9.0
        args:
          - -config.file=/etc/loki/loki.yaml
        ports:
        - containerPort: 3100
          name: http
        - containerPort: 9096
          name: grpc
        volumeMounts:
        - name: config
          mountPath: /etc/loki
        - name: storage
          mountPath: /data
        resources:
          requests:
            cpu: 500m
            memory: 1Gi
          limits:
            cpu: 1000m
            memory: 2Gi
      volumes:
      - name: config
        configMap:
          name: loki-config
  volumeClaimTemplates:
  - metadata:
      name: storage
    spec:
      accessModes: ["ReadWriteOnce"]
      resources:
        requests:
          storage: 10Gi

---
apiVersion: v1
kind: Service
metadata:
  name: loki
  namespace: logging
spec:
  selector:
    app: loki
  ports:
  - name: http
    port: 3100
    targetPort: 3100
  - name: grpc
    port: 9096
    targetPort: 9096
  type: ClusterIP
```

---

## 最佳实践

### 1. 标签设计

```text
✅ 好的标签设计:
  - 低基数标签: service, environment, level
  - 静态标签: 不频繁变化的值
  - 有意义的标签: 便于过滤和聚合

❌ 避免的标签:
  - 高基数标签: user_id, request_id, trace_id
  - 动态标签: 频繁变化的值
  - 无意义标签: random_value

推荐标签集:
  - job/service: 服务名称
  - env: 环境 (dev/staging/prod)
  - level: 日志级别 (debug/info/warn/error)
  - region: 地理区域
  - namespace: K8s 命名空间
```

### 2. 日志结构化

```json
{
  "ts": "2025-01-15T10:30:45Z",
  "level": "error",
  "service": "api-server",
  "msg": "Database connection failed",
  "error": "connection timeout",
  "duration_ms": 5000,
  "trace_id": "abc123",
  "span_id": "def456"
}
```

### 3. 保留策略

```yaml
limits_config:
  # 7天内的日志
  reject_old_samples: true
  reject_old_samples_max_age: 168h

table_manager:
  # 保留30天
  retention_deletes_enabled: true
  retention_period: 720h
```

---

## 故障排查

### 常见问题

```text
问题 1: 日志未显示
排查:
  1. 检查 Loki 服务状态
  2. 检查客户端连接
  3. 验证标签配置
  4. 查看 Loki 日志

问题 2: 查询慢
排查:
  1. 减小时间范围
  2. 添加标签过滤
  3. 使用索引标签
  4. 增加查询并发度

问题 3: 磁盘空间不足
排查:
  1. 检查保留期设置
  2. 启用压缩
  3. 清理旧数据
  4. 增加存储空间
```

---

## 总结

```text
✅ Loki 优势:
  - 成本极低 (仅索引标签)
  - 云原生设计
  - 与 Grafana 深度集成
  - LogQL 强大查询语言

✅ 集成步骤:
  1. 创建 Loki 客户端
  2. 配置日志记录器
  3. 设计标签策略
  4. 部署 Loki 服务
  5. 配置 Grafana

✅ 最佳实践:
  - 低基数标签设计
  - 结构化日志格式
  - 批处理优化
  - 合理保留策略
```

---

**更新时间**: 2025-10-12  
**文档版本**: v1.0.0  
**维护团队**: OTLP Go Integration Team

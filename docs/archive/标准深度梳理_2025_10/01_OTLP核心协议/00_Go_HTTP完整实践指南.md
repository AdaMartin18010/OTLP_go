# Go HTTP OTLP 完整实践指南

> **Go 版本**: 1.25.1  
> **OpenTelemetry Go SDK**: v1.24.0+  
> **最后更新**: 2025年10月8日

---

## 目录

- [Go HTTP OTLP 完整实践指南](#go-http-otlp-完整实践指南)
  - [目录](#目录)
  - [1. Go net/http OTLP 集成](#1-go-nethttp-otlp-集成)
    - [1.1 依赖管理](#11-依赖管理)
    - [1.2 初始化配置](#12-初始化配置)
  - [2. 生产级 HTTP 客户端](#2-生产级-http-客户端)
    - [2.1 完整的 HTTP 客户端实现](#21-完整的-http-客户端实现)
    - [2.2 重试机制](#22-重试机制)
  - [3. HTTP 服务器实现](#3-http-服务器实现)
    - [3.1 完整的 HTTP 服务器](#31-完整的-http-服务器)
  - [4. 压缩与性能优化](#4-压缩与性能优化)
    - [4.1 智能压缩](#41-智能压缩)
    - [4.2 连接池优化](#42-连接池优化)
  - [5. 认证与安全](#5-认证与安全)
    - [5.1 认证实现](#51-认证实现)
  - [6. 错误处理与重试](#6-错误处理与重试)
  - [7. 测试与基准测试](#7-测试与基准测试)
    - [7.1 单元测试](#71-单元测试)
    - [7.2 基准测试](#72-基准测试)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 配置建议](#81-配置建议)
    - [8.2 完整示例](#82-完整示例)
  - [总结](#总结)

---

## 1. Go net/http OTLP 集成

### 1.1 依赖管理

```go
module github.com/example/otlp-http-go

go 1.25.1

require (
    go.opentelemetry.io/otel v1.24.0
    go.opentelemetry.io/otel/sdk v1.24.0
    go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp v1.24.0
    go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetrichttp v1.24.0
    go.opentelemetry.io/proto/otlp v1.1.0
    google.golang.org/protobuf v1.32.0
)
```

### 1.2 初始化配置

```go
package otelhttp

import (
    "context"
    "crypto/tls"
    "fmt"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracehttp"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// HTTPTracerConfig HTTP 追踪器配置
type HTTPTracerConfig struct {
    ServiceName    string
    ServiceVersion string
    Environment    string
    
    // HTTP 配置
    Endpoint     string // 例如: https://collector.example.com:4318
    URLPath      string // 默认: /v1/traces
    Insecure     bool
    
    // TLS 配置
    TLSConfig *tls.Config
    
    // 认证
    Headers map[string]string
    
    // 性能配置
    Compression    string        // "gzip" 或 ""
    Timeout        time.Duration
    MaxIdleConns   int
    IdleConnTimeout time.Duration
    
    // 采样
    SampleRate float64
    
    // 批处理
    MaxExportBatchSize int
    BatchTimeout       time.Duration
    MaxQueueSize       int
}

// DefaultHTTPConfig 默认 HTTP 配置
func DefaultHTTPConfig() *HTTPTracerConfig {
    return &HTTPTracerConfig{
        Endpoint:           "http://localhost:4318",
        URLPath:            "/v1/traces",
        Insecure:           false,
        Compression:        "gzip",
        Timeout:            30 * time.Second,
        MaxIdleConns:       100,
        IdleConnTimeout:    90 * time.Second,
        SampleRate:         1.0,
        MaxExportBatchSize: 512,
        BatchTimeout:       5 * time.Second,
        MaxQueueSize:       2048,
        Headers:            make(map[string]string),
    }
}

// InitHTTPTracer 初始化 HTTP 追踪器
func InitHTTPTracer(ctx context.Context, cfg *HTTPTracerConfig) (*sdktrace.TracerProvider, error) {
    // 1. 创建 Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName(cfg.ServiceName),
            semconv.ServiceVersion(cfg.ServiceVersion),
            semconv.DeploymentEnvironment(cfg.Environment),
        ),
        resource.WithFromEnv(),
        resource.WithProcess(),
        resource.WithOS(),
        resource.WithContainer(),
        resource.WithHost(),
        resource.WithTelemetrySDK(),
    )
    if err != nil {
        return nil, fmt.Errorf("创建 Resource 失败: %w", err)
    }

    // 2. 配置 HTTP 客户端
    httpClient := &http.Client{
        Timeout: cfg.Timeout,
        Transport: &http.Transport{
            MaxIdleConns:        cfg.MaxIdleConns,
            MaxIdleConnsPerHost: 10,
            IdleConnTimeout:     cfg.IdleConnTimeout,
            TLSClientConfig:     cfg.TLSConfig,
            DisableKeepAlives:   false,
            DisableCompression:  false,
        },
    }

    // 3. 配置 OTLP HTTP 选项
    opts := []otlptracehttp.Option{
        otlptracehttp.WithEndpoint(cfg.Endpoint),
        otlptracehttp.WithURLPath(cfg.URLPath),
        otlptracehttp.WithHTTPClient(httpClient),
        otlptracehttp.WithTimeout(cfg.Timeout),
        otlptracehttp.WithRetry(otlptracehttp.RetryConfig{
            Enabled:         true,
            InitialInterval: 1 * time.Second,
            MaxInterval:     30 * time.Second,
            MaxElapsedTime:  5 * time.Minute,
        }),
    }

    // 4. Insecure 模式
    if cfg.Insecure {
        opts = append(opts, otlptracehttp.WithInsecure())
    }

    // 5. 压缩
    if cfg.Compression == "gzip" {
        opts = append(opts, otlptracehttp.WithCompression(otlptracehttp.GzipCompression))
    }

    // 6. 自定义头部
    if len(cfg.Headers) > 0 {
        opts = append(opts, otlptracehttp.WithHeaders(cfg.Headers))
    }

    // 7. 创建 Exporter
    exporter, err := otlptracehttp.New(ctx, opts...)
    if err != nil {
        return nil, fmt.Errorf("创建 HTTP Exporter 失败: %w", err)
    }

    // 8. 创建 Sampler
    sampler := sdktrace.ParentBased(
        sdktrace.TraceIDRatioBased(cfg.SampleRate),
    )

    // 9. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(cfg.BatchTimeout),
            sdktrace.WithMaxExportBatchSize(cfg.MaxExportBatchSize),
            sdktrace.WithMaxQueueSize(cfg.MaxQueueSize),
        ),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sampler),
    )

    // 10. 设置全局 Provider
    otel.SetTracerProvider(tp)
    
    // 11. 设置 Propagator
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )

    return tp, nil
}
```

---

## 2. 生产级 HTTP 客户端

### 2.1 完整的 HTTP 客户端实现

```go
package httpclient

import (
    "bytes"
    "compress/gzip"
    "context"
    "crypto/tls"
    "fmt"
    "io"
    "net/http"
    "time"

    tracepb "go.opentelemetry.io/proto/otlp/collector/trace/v1"
    "google.golang.org/protobuf/proto"
)

// OTLPHTTPClient OTLP HTTP 客户端
type OTLPHTTPClient struct {
    httpClient  *http.Client
    endpoint    string
    headers     map[string]string
    compression bool
    timeout     time.Duration
}

// ClientConfig 客户端配置
type ClientConfig struct {
    Endpoint        string
    Headers         map[string]string
    Compression     bool
    Timeout         time.Duration
    MaxIdleConns    int
    IdleConnTimeout time.Duration
    TLSConfig       *tls.Config
}

// NewOTLPHTTPClient 创建 HTTP 客户端
func NewOTLPHTTPClient(cfg *ClientConfig) *OTLPHTTPClient {
    if cfg.Timeout == 0 {
        cfg.Timeout = 30 * time.Second
    }

    transport := &http.Transport{
        MaxIdleConns:        cfg.MaxIdleConns,
        MaxIdleConnsPerHost: 10,
        IdleConnTimeout:     cfg.IdleConnTimeout,
        TLSClientConfig:     cfg.TLSConfig,
        DisableKeepAlives:   false,
        ForceAttemptHTTP2:   true,
    }

    return &OTLPHTTPClient{
        httpClient: &http.Client{
            Transport: transport,
            Timeout:   cfg.Timeout,
        },
        endpoint:    cfg.Endpoint + "/v1/traces",
        headers:     cfg.Headers,
        compression: cfg.Compression,
        timeout:     cfg.Timeout,
    }
}

// ExportTraces 导出追踪数据
func (c *OTLPHTTPClient) ExportTraces(ctx context.Context, req *tracepb.ExportTraceServiceRequest) error {
    // 1. 序列化
    data, err := proto.Marshal(req)
    if err != nil {
        return fmt.Errorf("序列化失败: %w", err)
    }

    // 2. 压缩
    if c.compression {
        data, err = c.compress(data)
        if err != nil {
            return fmt.Errorf("压缩失败: %w", err)
        }
    }

    // 3. 创建 HTTP 请求
    httpReq, err := http.NewRequestWithContext(ctx, "POST", c.endpoint, bytes.NewReader(data))
    if err != nil {
        return fmt.Errorf("创建请求失败: %w", err)
    }

    // 4. 设置头部
    httpReq.Header.Set("Content-Type", "application/x-protobuf")
    httpReq.Header.Set("User-Agent", "otlp-http-go/1.0")
    
    if c.compression {
        httpReq.Header.Set("Content-Encoding", "gzip")
    }

    for k, v := range c.headers {
        httpReq.Header.Set(k, v)
    }

    // 5. 发送请求
    httpResp, err := c.httpClient.Do(httpReq)
    if err != nil {
        return fmt.Errorf("HTTP 请求失败: %w", err)
    }
    defer httpResp.Body.Close()

    // 6. 检查状态码
    if httpResp.StatusCode >= 200 && httpResp.StatusCode < 300 {
        return c.checkPartialSuccess(httpResp)
    }

    // 7. 处理错误
    body, _ := io.ReadAll(httpResp.Body)
    return fmt.Errorf("HTTP %d: %s", httpResp.StatusCode, string(body))
}

// compress 压缩数据
func (c *OTLPHTTPClient) compress(data []byte) ([]byte, error) {
    if len(data) < 1024 {
        return data, nil // 太小不压缩
    }

    var buf bytes.Buffer
    gw := gzip.NewWriter(&buf)

    if _, err := gw.Write(data); err != nil {
        return nil, err
    }

    if err := gw.Close(); err != nil {
        return nil, err
    }

    return buf.Bytes(), nil
}

// checkPartialSuccess 检查部分成功
func (c *OTLPHTTPClient) checkPartialSuccess(resp *http.Response) error {
    if resp.ContentLength == 0 {
        return nil
    }

    body, err := io.ReadAll(resp.Body)
    if err != nil {
        return err
    }

    var exportResp tracepb.ExportTraceServiceResponse
    if err := proto.Unmarshal(body, &exportResp); err != nil {
        return err
    }

    if ps := exportResp.PartialSuccess; ps != nil && ps.RejectedSpans > 0 {
        return fmt.Errorf("部分失败: %d spans 被拒绝: %s", 
            ps.RejectedSpans, ps.ErrorMessage)
    }

    return nil
}

// Close 关闭客户端
func (c *OTLPHTTPClient) Close() error {
    c.httpClient.CloseIdleConnections()
    return nil
}
```

### 2.2 重试机制

```go
package httpclient

import (
    "context"
    "errors"
    "fmt"
    "math"
    "math/rand"
    "net/http"
    "time"

    tracepb "go.opentelemetry.io/proto/otlp/collector/trace/v1"
)

// RetryableHTTPClient 带重试的 HTTP 客户端
type RetryableHTTPClient struct {
    client      *OTLPHTTPClient
    maxRetries  int
    initialWait time.Duration
    maxWait     time.Duration
}

// NewRetryableHTTPClient 创建带重试的客户端
func NewRetryableHTTPClient(client *OTLPHTTPClient, maxRetries int) *RetryableHTTPClient {
    return &RetryableHTTPClient{
        client:      client,
        maxRetries:  maxRetries,
        initialWait: 1 * time.Second,
        maxWait:     120 * time.Second,
    }
}

// ExportTracesWithRetry 带重试的导出
func (r *RetryableHTTPClient) ExportTracesWithRetry(
    ctx context.Context,
    req *tracepb.ExportTraceServiceRequest,
) error {
    var lastErr error

    for attempt := 0; attempt < r.maxRetries; attempt++ {
        err := r.client.ExportTraces(ctx, req)
        if err == nil {
            return nil
        }

        lastErr = err

        // 判断是否可重试
        if !r.isRetryable(err) {
            return err
        }

        // 最后一次尝试
        if attempt == r.maxRetries-1 {
            break
        }

        // 计算退避时间
        waitTime := r.calculateBackoff(attempt)

        // 等待重试
        select {
        case <-ctx.Done():
            return ctx.Err()
        case <-time.After(waitTime):
            // 继续重试
        }
    }

    return fmt.Errorf("最大重试次数 %d 已达到: %w", r.maxRetries, lastErr)
}

// isRetryable 判断错误是否可重试
func (r *RetryableHTTPClient) isRetryable(err error) bool {
    if err == nil {
        return false
    }

    // 检查 HTTP 状态码
    var httpErr *HTTPError
    if errors.As(err, &httpErr) {
        statusCode := httpErr.StatusCode
        return statusCode == http.StatusTooManyRequests ||
            statusCode == http.StatusRequestTimeout ||
            statusCode >= 500
    }

    // 其他错误可重试
    return true
}

// calculateBackoff 计算退避时间
func (r *RetryableHTTPClient) calculateBackoff(attempt int) time.Duration {
    backoff := float64(r.initialWait) * math.Pow(2.0, float64(attempt))
    
    if backoff > float64(r.maxWait) {
        backoff = float64(r.maxWait)
    }

    // 添加抖动 ±25%
    jitter := backoff * 0.25 * (2*rand.Float64() - 1)
    backoff += jitter

    return time.Duration(backoff)
}

// HTTPError HTTP 错误
type HTTPError struct {
    StatusCode int
    Body       string
}

func (e *HTTPError) Error() string {
    return fmt.Sprintf("HTTP %d: %s", e.StatusCode, e.Body)
}
```

---

## 3. HTTP 服务器实现

### 3.1 完整的 HTTP 服务器

```go
package httpserver

import (
    "compress/gzip"
    "context"
    "encoding/json"
    "fmt"
    "io"
    "log"
    "net/http"
    "strings"
    "time"

    tracepb "go.opentelemetry.io/proto/otlp/collector/trace/v1"
    "google.golang.org/protobuf/proto"
)

// HTTPServer OTLP HTTP 服务器
type HTTPServer struct {
    server  *http.Server
    handler TraceHandler
}

// TraceHandler 追踪处理器接口
type TraceHandler interface {
    HandleTraces(ctx context.Context, req *tracepb.ExportTraceServiceRequest) error
}

// ServerConfig 服务器配置
type ServerConfig struct {
    Port            int
    ReadTimeout     time.Duration
    WriteTimeout    time.Duration
    IdleTimeout     time.Duration
    MaxHeaderBytes  int
    EnableCORS      bool
    AllowedOrigins  []string
}

// DefaultServerConfig 默认服务器配置
func DefaultServerConfig() *ServerConfig {
    return &ServerConfig{
        Port:           4318,
        ReadTimeout:    30 * time.Second,
        WriteTimeout:   30 * time.Second,
        IdleTimeout:    120 * time.Second,
        MaxHeaderBytes: 1 << 20, // 1MB
        EnableCORS:     false,
    }
}

// NewHTTPServer 创建 HTTP 服务器
func NewHTTPServer(cfg *ServerConfig, handler TraceHandler) *HTTPServer {
    mux := http.NewServeMux()

    s := &HTTPServer{
        handler: handler,
    }

    // 注册端点
    mux.HandleFunc("/v1/traces", s.handleTraces)
    mux.HandleFunc("/v1/metrics", s.handleMetrics)
    mux.HandleFunc("/v1/logs", s.handleLogs)
    mux.HandleFunc("/health", s.handleHealth)

    // 应用中间件
    var finalHandler http.Handler = mux
    finalHandler = s.loggingMiddleware(finalHandler)
    
    if cfg.EnableCORS {
        finalHandler = s.corsMiddleware(finalHandler, cfg.AllowedOrigins)
    }

    s.server = &http.Server{
        Addr:           fmt.Sprintf(":%d", cfg.Port),
        Handler:        finalHandler,
        ReadTimeout:    cfg.ReadTimeout,
        WriteTimeout:   cfg.WriteTimeout,
        IdleTimeout:    cfg.IdleTimeout,
        MaxHeaderBytes: cfg.MaxHeaderBytes,
    }

    return s
}

// handleTraces 处理追踪请求
func (s *HTTPServer) handleTraces(w http.ResponseWriter, r *http.Request) {
    // 1. 检查方法
    if r.Method != http.MethodPost {
        http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
        return
    }

    // 2. 检查 Content-Type
    contentType := r.Header.Get("Content-Type")
    if !strings.Contains(contentType, "application/x-protobuf") &&
        !strings.Contains(contentType, "application/json") {
        http.Error(w, "Unsupported media type", http.StatusUnsupportedMediaType)
        return
    }

    // 3. 读取请求体
    body := r.Body
    if r.Header.Get("Content-Encoding") == "gzip" {
        gr, err := gzip.NewReader(r.Body)
        if err != nil {
            http.Error(w, "Invalid gzip", http.StatusBadRequest)
            return
        }
        defer gr.Close()
        body = gr
    }

    data, err := io.ReadAll(body)
    if err != nil {
        http.Error(w, "Read error", http.StatusBadRequest)
        return
    }

    // 4. 解析请求
    var req tracepb.ExportTraceServiceRequest
    
    if strings.Contains(contentType, "application/json") {
        // JSON 格式
        if err := json.Unmarshal(data, &req); err != nil {
            http.Error(w, "Invalid JSON", http.StatusBadRequest)
            return
        }
    } else {
        // Protobuf 格式
        if err := proto.Unmarshal(data, &req); err != nil {
            http.Error(w, "Invalid protobuf", http.StatusBadRequest)
            return
        }
    }

    // 5. 验证请求
    if err := s.validateRequest(&req); err != nil {
        http.Error(w, err.Error(), http.StatusBadRequest)
        return
    }

    // 6. 处理数据
    ctx, cancel := context.WithTimeout(r.Context(), 30*time.Second)
    defer cancel()

    if err := s.handler.HandleTraces(ctx, &req); err != nil {
        log.Printf("处理失败: %v", err)
        http.Error(w, "Internal server error", http.StatusInternalServerError)
        return
    }

    // 7. 返回成功
    w.Header().Set("Content-Type", "application/x-protobuf")
    w.WriteHeader(http.StatusOK)
}

// validateRequest 验证请求
func (s *HTTPServer) validateRequest(req *tracepb.ExportTraceServiceRequest) error {
    if len(req.ResourceSpans) == 0 {
        return fmt.Errorf("resource_spans 不能为空")
    }

    for i, rs := range req.ResourceSpans {
        if rs.Resource == nil {
            return fmt.Errorf("resource_spans[%d].resource 不能为空", i)
        }
        
        for j, ss := range rs.ScopeSpans {
            if len(ss.Spans) == 0 {
                return fmt.Errorf("resource_spans[%d].scope_spans[%d].spans 不能为空", i, j)
            }
        }
    }

    return nil
}

// handleMetrics 处理指标请求
func (s *HTTPServer) handleMetrics(w http.ResponseWriter, r *http.Request) {
    // 类似 handleTraces
    http.Error(w, "Not implemented", http.StatusNotImplemented)
}

// handleLogs 处理日志请求
func (s *HTTPServer) handleLogs(w http.ResponseWriter, r *http.Request) {
    // 类似 handleTraces
    http.Error(w, "Not implemented", http.StatusNotImplemented)
}

// handleHealth 健康检查
func (s *HTTPServer) handleHealth(w http.ResponseWriter, r *http.Request) {
    w.WriteHeader(http.StatusOK)
    w.Write([]byte("OK"))
}

// loggingMiddleware 日志中间件
func (s *HTTPServer) loggingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        
        // 使用 ResponseWriter wrapper 记录状态码
        rw := &responseWriter{ResponseWriter: w, statusCode: http.StatusOK}
        
        next.ServeHTTP(rw, r)
        
        duration := time.Since(start)
        log.Printf("%s %s %d %v", r.Method, r.URL.Path, rw.statusCode, duration)
    })
}

// corsMiddleware CORS 中间件
func (s *HTTPServer) corsMiddleware(next http.Handler, allowedOrigins []string) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        origin := r.Header.Get("Origin")
        
        // 检查 origin 是否允许
        allowed := false
        for _, o := range allowedOrigins {
            if o == "*" || o == origin {
                allowed = true
                break
            }
        }

        if allowed {
            w.Header().Set("Access-Control-Allow-Origin", origin)
            w.Header().Set("Access-Control-Allow-Methods", "POST, OPTIONS")
            w.Header().Set("Access-Control-Allow-Headers", 
                "Content-Type, Content-Encoding, Authorization")
            w.Header().Set("Access-Control-Max-Age", "86400")
        }

        if r.Method == http.MethodOptions {
            w.WriteHeader(http.StatusNoContent)
            return
        }

        next.ServeHTTP(w, r)
    })
}

// Start 启动服务器
func (s *HTTPServer) Start() error {
    log.Printf("HTTP 服务器监听 %s", s.server.Addr)
    return s.server.ListenAndServe()
}

// Shutdown 优雅关闭
func (s *HTTPServer) Shutdown(ctx context.Context) error {
    log.Println("正在关闭 HTTP 服务器...")
    return s.server.Shutdown(ctx)
}

// responseWriter HTTP 响应写入器包装
type responseWriter struct {
    http.ResponseWriter
    statusCode int
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}
```

---

## 4. 压缩与性能优化

### 4.1 智能压缩

```go
package compression

import (
    "bytes"
    "compress/gzip"
    "fmt"
    "io"
)

// Compressor 压缩器接口
type Compressor interface {
    Compress(data []byte) ([]byte, error)
    Decompress(data []byte) ([]byte, error)
}

// GzipCompressor Gzip 压缩器
type GzipCompressor struct {
    level     int
    threshold int // 压缩阈值
}

// NewGzipCompressor 创建 Gzip 压缩器
func NewGzipCompressor(level, threshold int) *GzipCompressor {
    return &GzipCompressor{
        level:     level,
        threshold: threshold,
    }
}

// Compress 压缩数据
func (c *GzipCompressor) Compress(data []byte) ([]byte, error) {
    // 小于阈值不压缩
    if len(data) < c.threshold {
        return data, nil
    }

    var buf bytes.Buffer
    gw, err := gzip.NewWriterLevel(&buf, c.level)
    if err != nil {
        return nil, err
    }

    if _, err := gw.Write(data); err != nil {
        return nil, err
    }

    if err := gw.Close(); err != nil {
        return nil, err
    }

    compressed := buf.Bytes()

    // 如果压缩后更大，返回原数据
    if len(compressed) >= len(data) {
        return data, nil
    }

    return compressed, nil
}

// Decompress 解压数据
func (c *GzipCompressor) Decompress(data []byte) ([]byte, error) {
    gr, err := gzip.NewReader(bytes.NewReader(data))
    if err != nil {
        return nil, err
    }
    defer gr.Close()

    return io.ReadAll(gr)
}

// CompressWithLevel 使用指定级别压缩
func CompressWithLevel(data []byte, level int) ([]byte, error) {
    compressor := NewGzipCompressor(level, 1024)
    return compressor.Compress(data)
}
```

### 4.2 连接池优化

```go
package pooling

import (
    "crypto/tls"
    "net"
    "net/http"
    "time"
)

// OptimizedHTTPClient 优化的 HTTP 客户端
func OptimizedHTTPClient(cfg *ClientOptimizationConfig) *http.Client {
    dialer := &net.Dialer{
        Timeout:   30 * time.Second,
        KeepAlive: 30 * time.Second,
    }

    transport := &http.Transport{
        DialContext:           dialer.DialContext,
        ForceAttemptHTTP2:     true,
        MaxIdleConns:          cfg.MaxIdleConns,
        MaxIdleConnsPerHost:   cfg.MaxIdleConnsPerHost,
        MaxConnsPerHost:       cfg.MaxConnsPerHost,
        IdleConnTimeout:       cfg.IdleConnTimeout,
        TLSHandshakeTimeout:   10 * time.Second,
        ExpectContinueTimeout: 1 * time.Second,
        ResponseHeaderTimeout: 30 * time.Second,
        DisableKeepAlives:     false,
        DisableCompression:    false,
    }

    // TLS 配置
    if cfg.TLSConfig != nil {
        transport.TLSClientConfig = cfg.TLSConfig
    } else {
        transport.TLSClientConfig = &tls.Config{
            MinVersion: tls.VersionTLS12,
            CipherSuites: []uint16{
                tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
                tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
            },
        }
    }

    return &http.Client{
        Transport: transport,
        Timeout:   cfg.Timeout,
    }
}

// ClientOptimizationConfig 客户端优化配置
type ClientOptimizationConfig struct {
    MaxIdleConns        int
    MaxIdleConnsPerHost int
    MaxConnsPerHost     int
    IdleConnTimeout     time.Duration
    Timeout             time.Duration
    TLSConfig           *tls.Config
}

// DefaultOptimizationConfig 默认优化配置
func DefaultOptimizationConfig() *ClientOptimizationConfig {
    return &ClientOptimizationConfig{
        MaxIdleConns:        100,
        MaxIdleConnsPerHost: 10,
        MaxConnsPerHost:     20,
        IdleConnTimeout:     90 * time.Second,
        Timeout:             30 * time.Second,
    }
}
```

---

## 5. 认证与安全

### 5.1 认证实现

```go
package auth

import (
    "crypto/tls"
    "crypto/x509"
    "fmt"
    "net/http"
    "os"
)

// AuthConfig 认证配置
type AuthConfig struct {
    Type       string // "bearer", "apikey", "basic", "mtls"
    Token      string
    APIKey     string
    Username   string
    Password   string
    CertPath   string
    KeyPath    string
    CAPath     string
}

// SetupAuth 设置认证
func SetupAuth(client *http.Client, cfg *AuthConfig) error {
    switch cfg.Type {
    case "bearer":
        return setupBearerAuth(client, cfg.Token)
    case "apikey":
        return setupAPIKeyAuth(client, cfg.APIKey)
    case "basic":
        return setupBasicAuth(client, cfg.Username, cfg.Password)
    case "mtls":
        return setupMTLS(client, cfg.CertPath, cfg.KeyPath, cfg.CAPath)
    default:
        return fmt.Errorf("不支持的认证类型: %s", cfg.Type)
    }
}

// setupBearerAuth 设置 Bearer Token 认证
func setupBearerAuth(client *http.Client, token string) error {
    // 通过请求拦截器添加 Authorization 头部
    transport := client.Transport
    if transport == nil {
        transport = http.DefaultTransport
    }

    client.Transport = &bearerAuthTransport{
        token:     token,
        transport: transport,
    }

    return nil
}

// bearerAuthTransport Bearer 认证 Transport
type bearerAuthTransport struct {
    token     string
    transport http.RoundTripper
}

func (t *bearerAuthTransport) RoundTrip(req *http.Request) (*http.Response, error) {
    req.Header.Set("Authorization", "Bearer "+t.token)
    return t.transport.RoundTrip(req)
}

// setupAPIKeyAuth 设置 API Key 认证
func setupAPIKeyAuth(client *http.Client, apiKey string) error {
    transport := client.Transport
    if transport == nil {
        transport = http.DefaultTransport
    }

    client.Transport = &apiKeyAuthTransport{
        apiKey:    apiKey,
        transport: transport,
    }

    return nil
}

// apiKeyAuthTransport API Key 认证 Transport
type apiKeyAuthTransport struct {
    apiKey    string
    transport http.RoundTripper
}

func (t *apiKeyAuthTransport) RoundTrip(req *http.Request) (*http.Response, error) {
    req.Header.Set("X-API-Key", t.apiKey)
    return t.transport.RoundTrip(req)
}

// setupBasicAuth 设置 Basic 认证
func setupBasicAuth(client *http.Client, username, password string) error {
    transport := client.Transport
    if transport == nil {
        transport = http.DefaultTransport
    }

    client.Transport = &basicAuthTransport{
        username:  username,
        password:  password,
        transport: transport,
    }

    return nil
}

// basicAuthTransport Basic 认证 Transport
type basicAuthTransport struct {
    username  string
    password  string
    transport http.RoundTripper
}

func (t *basicAuthTransport) RoundTrip(req *http.Request) (*http.Response, error) {
    req.SetBasicAuth(t.username, t.password)
    return t.transport.RoundTrip(req)
}

// setupMTLS 设置 mTLS
func setupMTLS(client *http.Client, certPath, keyPath, caPath string) error {
    // 加载客户端证书
    cert, err := tls.LoadX509KeyPair(certPath, keyPath)
    if err != nil {
        return fmt.Errorf("加载客户端证书失败: %w", err)
    }

    // 加载 CA 证书
    caCert, err := os.ReadFile(caPath)
    if err != nil {
        return fmt.Errorf("读取 CA 证书失败: %w", err)
    }

    caCertPool := x509.NewCertPool()
    if !caCertPool.AppendCertsFromPEM(caCert) {
        return fmt.Errorf("添加 CA 证书失败")
    }

    // 配置 TLS
    tlsConfig := &tls.Config{
        Certificates: []tls.Certificate{cert},
        RootCAs:      caCertPool,
        MinVersion:   tls.VersionTLS12,
    }

    transport := client.Transport
    if transport == nil {
        transport = http.DefaultTransport
    }

    if httpTransport, ok := transport.(*http.Transport); ok {
        httpTransport.TLSClientConfig = tlsConfig
    }

    return nil
}
```

---

## 6. 错误处理与重试

*（已在第 2.2 节展示）*-

---

## 7. 测试与基准测试

### 7.1 单元测试

```go
package httpclient

import (
    "context"
    "net/http"
    "net/http/httptest"
    "testing"
    "time"

    tracepb "go.opentelemetry.io/proto/otlp/collector/trace/v1"
    "google.golang.org/protobuf/proto"
)

// TestExportTraces 测试导出
func TestExportTraces(t *testing.T) {
    // 创建测试服务器
    server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        if r.URL.Path != "/v1/traces" {
            t.Errorf("错误的路径: %s", r.URL.Path)
        }

        if r.Method != http.MethodPost {
            t.Errorf("错误的方法: %s", r.Method)
        }

        w.WriteHeader(http.StatusOK)
    }))
    defer server.Close()

    // 创建客户端
    client := NewOTLPHTTPClient(&ClientConfig{
        Endpoint:    server.URL,
        Compression: false,
        Timeout:     5 * time.Second,
    })

    // 测试导出
    req := &tracepb.ExportTraceServiceRequest{
        ResourceSpans: []*tracepb.ResourceSpans{
            // ... 填充测试数据
        },
    }

    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()

    err := client.ExportTraces(ctx, req)
    if err != nil {
        t.Fatalf("导出失败: %v", err)
    }
}

// TestRetry 测试重试
func TestRetry(t *testing.T) {
    attempts := 0
    server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        attempts++
        
        if attempts < 3 {
            w.WriteHeader(http.StatusServiceUnavailable)
            return
        }

        w.WriteHeader(http.StatusOK)
    }))
    defer server.Close()

    client := NewOTLPHTTPClient(&ClientConfig{
        Endpoint:    server.URL,
        Compression: false,
        Timeout:     5 * time.Second,
    })

    retryClient := NewRetryableHTTPClient(client, 5)

    req := &tracepb.ExportTraceServiceRequest{}

    err := retryClient.ExportTracesWithRetry(context.Background(), req)
    if err != nil {
        t.Fatalf("重试失败: %v", err)
    }

    if attempts != 3 {
        t.Errorf("预期 3 次尝试,实际 %d 次", attempts)
    }
}
```

### 7.2 基准测试

```go
package httpclient

import (
    "context"
    "net/http/httptest"
    "testing"

    tracepb "go.opentelemetry.io/proto/otlp/collector/trace/v1"
)

// BenchmarkExportTraces 基准测试导出
func BenchmarkExportTraces(b *testing.B) {
    server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        w.WriteHeader(http.StatusOK)
    }))
    defer server.Close()

    client := NewOTLPHTTPClient(&ClientConfig{
        Endpoint:    server.URL,
        Compression: false,
    })

    req := &tracepb.ExportTraceServiceRequest{
        ResourceSpans: generateTestSpans(100),
    }

    b.ResetTimer()

    for i := 0; i < b.N; i++ {
        err := client.ExportTraces(context.Background(), req)
        if err != nil {
            b.Fatalf("导出失败: %v", err)
        }
    }
}

// BenchmarkExportTracesWithCompression 基准测试压缩导出
func BenchmarkExportTracesWithCompression(b *testing.B) {
    server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        w.WriteHeader(http.StatusOK)
    }))
    defer server.Close()

    client := NewOTLPHTTPClient(&ClientConfig{
        Endpoint:    server.URL,
        Compression: true,
    })

    req := &tracepb.ExportTraceServiceRequest{
        ResourceSpans: generateTestSpans(100),
    }

    b.ResetTimer()

    for i := 0; i < b.N; i++ {
        err := client.ExportTraces(context.Background(), req)
        if err != nil {
            b.Fatalf("导出失败: %v", err)
        }
    }
}
```

---

## 8. 最佳实践

### 8.1 配置建议

```go
// 生产环境推荐配置
cfg := &HTTPTracerConfig{
    ServiceName:    "my-service",
    ServiceVersion: "1.0.0",
    Environment:    "production",
    
    // HTTPS 端点
    Endpoint:    "https://collector.example.com:4318",
    Insecure:    false,
    
    // 启用压缩
    Compression: "gzip",
    
    // 超时设置
    Timeout:         30 * time.Second,
    IdleConnTimeout: 90 * time.Second,
    
    // 连接池
    MaxIdleConns: 100,
    
    // 采样
    SampleRate: 0.1, // 10% 采样
    
    // 批处理
    MaxExportBatchSize: 512,
    BatchTimeout:       5 * time.Second,
    MaxQueueSize:       2048,
    
    // 认证
    Headers: map[string]string{
        "Authorization": "Bearer " + token,
        "X-Custom-Header": "value",
    },
}
```

### 8.2 完整示例

```go
package main

import (
    "context"
    "log"
    "os"
    "os/signal"
    "syscall"
    "time"

    "go.opentelemetry.io/otel"
)

func main() {
    ctx := context.Background()

    // 配置
    cfg := otelhttp.DefaultHTTPConfig()
    cfg.ServiceName = "my-service"
    cfg.ServiceVersion = "1.0.0"
    cfg.Environment = "production"
    cfg.Endpoint = "https://collector.example.com:4318"

    // 初始化
    tp, err := otelhttp.InitHTTPTracer(ctx, cfg)
    if err != nil {
        log.Fatal(err)
    }

    // 优雅关闭
    sigCh := make(chan os.Signal, 1)
    signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)

    go func() {
        <-sigCh
        log.Println("正在关闭...")

        shutdownCtx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
        defer cancel()

        if err := tp.Shutdown(shutdownCtx); err != nil {
            log.Printf("关闭失败: %v", err)
        }

        os.Exit(0)
    }()

    // 使用追踪器
    tracer := otel.Tracer("my-app")
    ctx, span := tracer.Start(ctx, "main-operation")
    defer span.End()

    // 业务逻辑
    doWork(ctx)

    log.Println("应用运行中...")
    select {}
}
```

---

## 总结

本文档提供了 Go 1.25.1 环境下 OTLP HTTP 集成的完整实践，包括：

1. ✅ **完整的客户端实现** - 支持 Protobuf/JSON、压缩、重试
2. ✅ **生产级服务器** - CORS、认证、中间件、优雅关闭
3. ✅ **性能优化** - 连接池、智能压缩、批处理
4. ✅ **安全实现** - Bearer Token、API Key、Basic Auth、mTLS
5. ✅ **测试覆盖** - 单元测试、基准测试

**相关文档**：

- [03_传输层_HTTP.md](./03_传输层_HTTP.md) - HTTP 协议详解
- [00_Go_gRPC完整实践指南.md](./00_Go_gRPC完整实践指南.md) - gRPC 实践指南
- [Go_1.25.1_完整集成指南.md](../00_Go完整集成指南/01_Go_1.25.1_完整集成指南.md) - SDK 集成指南

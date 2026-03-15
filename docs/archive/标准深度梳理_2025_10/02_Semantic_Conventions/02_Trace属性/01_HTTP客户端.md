# HTTP 客户端追踪属性完整指南

> **文档版本**: v2.0.0  
> **最后更新**: 2025-10-09  
> **OpenTelemetry 版本**: v1.32.0  
> **Go 版本**: 1.25.1

## 目录

- [HTTP 客户端追踪属性完整指南](#http-客户端追踪属性完整指南)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 HTTP 客户端语义约定](#11-http-客户端语义约定)
    - [1.2 与服务器端的区别](#12-与服务器端的区别)
  - [2. 核心属性](#2-核心属性)
    - [2.1 请求属性](#21-请求属性)
      - [2.1.1 必需属性](#211-必需属性)
      - [2.1.2 推荐属性](#212-推荐属性)
    - [2.2 响应属性](#22-响应属性)
    - [2.3 网络属性](#23-网络属性)
  - [3. HTTP/1.1 追踪](#3-http11-追踪)
    - [3.1 基础实现](#31-基础实现)
    - [3.2 连接复用](#32-连接复用)
  - [4. HTTP/2 追踪](#4-http2-追踪)
    - [4.1 多路复用](#41-多路复用)
    - [4.2 服务器推送](#42-服务器推送)
  - [5. HTTP/3 追踪](#5-http3-追踪)
    - [5.1 QUIC 集成](#51-quic-集成)
    - [5.2 0-RTT 处理](#52-0-rtt-处理)
  - [6. 高级模式](#6-高级模式)
    - [6.1 重试与重定向](#61-重试与重定向)
    - [6.2 超时与取消](#62-超时与取消)
    - [6.3 请求体追踪](#63-请求体追踪)
  - [7. Go 完整实现](#7-go-完整实现)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 命名规范](#81-命名规范)
    - [8.2 敏感信息处理](#82-敏感信息处理)
    - [8.3 采样策略](#83-采样策略)
  - [9. 性能优化](#9-性能优化)
    - [9.1 连接池配置](#91-连接池配置)
    - [9.2 批量追踪](#92-批量追踪)
  - [10. 故障排查](#10-故障排查)
    - [10.1 常见问题](#101-常见问题)
    - [10.2 调试技巧](#102-调试技巧)
  - [总结](#总结)

---

## 1. 概述

### 1.1 HTTP 客户端语义约定

HTTP 客户端追踪记录从**客户端视角**发起的 HTTP 请求。

**关键特征**:

- **Span Kind**: `SPAN_KIND_CLIENT`
- **命名规范**: `{http.request.method} {http.route}` 或 `{http.request.method}`
- **父 Span**: 通常是业务逻辑 Span
- **子 Span**: 可能包含 DNS 解析、TCP 连接、TLS 握手

### 1.2 与服务器端的区别

| 维度 | 客户端 | 服务器端 |
|------|--------|----------|
| **Span Kind** | `CLIENT` | `SERVER` |
| **命名** | `GET` / `POST {path}` | `GET /api/users` |
| **关注点** | 请求发起、重试、超时 | 请求处理、路由、业务逻辑 |
| **网络属性** | `server.address`, `server.port` | `client.address`, `client.port` |

---

## 2. 核心属性

### 2.1 请求属性

#### 2.1.1 必需属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `http.request.method` | string | `GET`, `POST` | HTTP 方法 |
| `server.address` | string | `api.example.com` | 目标服务器地址 |
| `url.full` | string | `https://api.example.com/users?page=1` | 完整 URL |

#### 2.1.2 推荐属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `server.port` | int | `443` | 目标端口 |
| `url.scheme` | string | `https` | URL 协议 |
| `url.path` | string | `/api/users` | URL 路径 |
| `url.query` | string | `page=1&limit=10` | 查询参数 |
| `http.request.header.<key>` | string[] | `["application/json"]` | 请求头 |
| `http.request.body.size` | int | `1024` | 请求体大小 (字节) |

### 2.2 响应属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `http.response.status_code` | int | `200`, `404` | HTTP 状态码 |
| `http.response.header.<key>` | string[] | `["gzip"]` | 响应头 |
| `http.response.body.size` | int | `2048` | 响应体大小 (字节) |

### 2.3 网络属性

| 属性 | 类型 | 示例 | 描述 |
|------|------|------|------|
| `network.protocol.name` | string | `http` | 协议名称 |
| `network.protocol.version` | string | `1.1`, `2`, `3` | 协议版本 |
| `network.peer.address` | string | `93.184.216.34` | 对端 IP 地址 |
| `network.peer.port` | int | `443` | 对端端口 |

---

## 3. HTTP/1.1 追踪

### 3.1 基础实现

```go
package httptracing

import (
    "context"
    "fmt"
    "io"
    "net/http"
    "net/http/httptrace"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

// TracedHTTPClient 包装 http.Client 并提供自动追踪
type TracedHTTPClient struct {
    client     *http.Client
    tracer     trace.Tracer
    propagator propagation.TextMapPropagator
}

// NewTracedHTTPClient 创建带追踪的 HTTP 客户端
func NewTracedHTTPClient(client *http.Client) *TracedHTTPClient {
    if client == nil {
        client = http.DefaultClient
    }

    return &TracedHTTPClient{
        client:     client,
        tracer:     otel.Tracer("http-client"),
        propagator: otel.GetTextMapPropagator(),
    }
}

// Do 执行 HTTP 请求并自动添加追踪
func (c *TracedHTTPClient) Do(ctx context.Context, req *http.Request) (*http.Response, error) {
    // 创建客户端 Span
    spanName := req.Method
    if req.URL.Path != "" {
        spanName = fmt.Sprintf("%s %s", req.Method, req.URL.Path)
    }

    ctx, span := c.tracer.Start(ctx, spanName,
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.HTTPRequestMethodKey.String(req.Method),
            semconv.URLFull(req.URL.String()),
            semconv.URLScheme(req.URL.Scheme),
            semconv.URLPath(req.URL.Path),
            semconv.ServerAddress(req.URL.Hostname()),
        ),
    )
    defer span.End()

    // 添加端口 (如果不是默认端口)
    if port := req.URL.Port(); port != "" {
        span.SetAttributes(semconv.ServerPort(mustParsePort(port)))
    }

    // 添加查询参数 (可选,注意敏感信息)
    if req.URL.RawQuery != "" {
        span.SetAttributes(semconv.URLQuery(req.URL.RawQuery))
    }

    // 注入追踪上下文到 HTTP 头
    req = req.Clone(ctx)
    c.propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))

    // 添加请求头追踪 (选择性)
    recordRequestHeaders(span, req.Header)

    // 执行请求
    resp, err := c.client.Do(req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    // 记录响应属性
    span.SetAttributes(
        semconv.HTTPResponseStatusCode(resp.StatusCode),
    )

    // HTTP 状态码映射到 Span 状态
    if resp.StatusCode >= 400 {
        span.SetStatus(codes.Error, http.StatusText(resp.StatusCode))
    } else {
        span.SetStatus(codes.Ok, "")
    }

    // 记录响应头 (选择性)
    recordResponseHeaders(span, resp.Header)

    return resp, nil
}

// recordRequestHeaders 记录重要的请求头
func recordRequestHeaders(span trace.Span, headers http.Header) {
    importantHeaders := []string{"Content-Type", "User-Agent", "Accept"}
    for _, key := range importantHeaders {
        if values := headers.Values(key); len(values) > 0 {
            span.SetAttributes(
                attribute.StringSlice(fmt.Sprintf("http.request.header.%s", key), values),
            )
        }
    }
}

// recordResponseHeaders 记录重要的响应头
func recordResponseHeaders(span trace.Span, headers http.Header) {
    importantHeaders := []string{"Content-Type", "Content-Encoding", "Cache-Control"}
    for _, key := range importantHeaders {
        if values := headers.Values(key); len(values) > 0 {
            span.SetAttributes(
                attribute.StringSlice(fmt.Sprintf("http.response.header.%s", key), values),
            )
        }
    }
}

func mustParsePort(port string) int {
    var p int
    fmt.Sscanf(port, "%d", &p)
    return p
}
```

### 3.2 连接复用

追踪连接池和复用:

```go
// TracedTransport 包装 http.RoundTripper 并追踪连接细节
type TracedTransport struct {
    base   http.RoundTripper
    tracer trace.Tracer
}

func NewTracedTransport(base http.RoundTripper) *TracedTransport {
    if base == nil {
        base = http.DefaultTransport
    }
    return &TracedTransport{
        base:   base,
        tracer: otel.Tracer("http-transport"),
    }
}

func (t *TracedTransport) RoundTrip(req *http.Request) (*http.Response, error) {
    ctx := req.Context()
    span := trace.SpanFromContext(ctx)

    // 使用 httptrace 追踪底层连接事件
    trace := &httptrace.ClientTrace{
        GetConn: func(hostPort string) {
            span.AddEvent("GetConn", trace.WithAttributes(
                attribute.String("host_port", hostPort),
            ))
        },
        GotConn: func(info httptrace.GotConnInfo) {
            span.AddEvent("GotConn", trace.WithAttributes(
                attribute.Bool("reused", info.Reused),
                attribute.Bool("was_idle", info.WasIdle),
                attribute.String("idle_time", info.IdleTime.String()),
            ))
        },
        DNSStart: func(info httptrace.DNSStartInfo) {
            span.AddEvent("DNSStart", trace.WithAttributes(
                attribute.String("host", info.Host),
            ))
        },
        DNSDone: func(info httptrace.DNSDoneInfo) {
            span.AddEvent("DNSDone", trace.WithAttributes(
                attribute.Int("addr_count", len(info.Addrs)),
            ))
            if info.Err != nil {
                span.RecordError(info.Err)
            }
        },
        ConnectStart: func(network, addr string) {
            span.AddEvent("ConnectStart", trace.WithAttributes(
                attribute.String("network", network),
                attribute.String("addr", addr),
            ))
        },
        ConnectDone: func(network, addr string, err error) {
            span.AddEvent("ConnectDone", trace.WithAttributes(
                attribute.String("network", network),
                attribute.String("addr", addr),
            ))
            if err != nil {
                span.RecordError(err)
            }
        },
        TLSHandshakeStart: func() {
            span.AddEvent("TLSHandshakeStart")
        },
        TLSHandshakeDone: func(state tls.ConnectionState, err error) {
            span.AddEvent("TLSHandshakeDone", trace.WithAttributes(
                attribute.String("tls_version", tlsVersionName(state.Version)),
                attribute.String("cipher_suite", tls.CipherSuiteName(state.CipherSuite)),
                attribute.Bool("resumed", state.DidResume),
            ))
            if err != nil {
                span.RecordError(err)
            }
        },
        WroteRequest: func(info httptrace.WroteRequestInfo) {
            if info.Err != nil {
                span.RecordError(info.Err)
            }
        },
        GotFirstResponseByte: func() {
            span.AddEvent("GotFirstResponseByte")
        },
    }

    req = req.WithContext(httptrace.WithClientTrace(ctx, trace))
    return t.base.RoundTrip(req)
}

func tlsVersionName(version uint16) string {
    switch version {
    case tls.VersionTLS10:
        return "TLS 1.0"
    case tls.VersionTLS11:
        return "TLS 1.1"
    case tls.VersionTLS12:
        return "TLS 1.2"
    case tls.VersionTLS13:
        return "TLS 1.3"
    default:
        return fmt.Sprintf("unknown (0x%04x)", version)
    }
}
```

---

## 4. HTTP/2 追踪

### 4.1 多路复用

HTTP/2 的多路复用特性需要特殊处理:

```go
// HTTP2Client 提供 HTTP/2 特定的追踪
type HTTP2Client struct {
    *TracedHTTPClient
}

func NewHTTP2Client() *HTTP2Client {
    transport := &http2.Transport{
        // 允许 HTTP/2
        AllowHTTP: true,
    }

    client := &http.Client{
        Transport: NewTracedTransport(transport),
    }

    return &HTTP2Client{
        TracedHTTPClient: NewTracedHTTPClient(client),
    }
}

func (c *HTTP2Client) Do(ctx context.Context, req *http.Request) (*http.Response, error) {
    span := trace.SpanFromContext(ctx)
    
    // 标记为 HTTP/2
    span.SetAttributes(
        semconv.NetworkProtocolName("http"),
        semconv.NetworkProtocolVersion("2"),
    )

    return c.TracedHTTPClient.Do(ctx, req)
}
```

### 4.2 服务器推送

追踪 HTTP/2 服务器推送:

```go
// HTTP2PushHandler 处理服务器推送
type HTTP2PushHandler struct {
    tracer trace.Tracer
}

func NewHTTP2PushHandler() *HTTP2PushHandler {
    return &HTTP2PushHandler{
        tracer: otel.Tracer("http2-push"),
    }
}

func (h *HTTP2PushHandler) HandlePush(ctx context.Context, pushRequest *http.Request) {
    ctx, span := h.tracer.Start(ctx, "HTTP/2 Server Push",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.HTTPRequestMethodKey.String(pushRequest.Method),
            semconv.URLFull(pushRequest.URL.String()),
            attribute.Bool("http.server_push", true),
        ),
    )
    defer span.End()

    // 处理推送的资源
    // ...
}
```

---

## 5. HTTP/3 追踪

### 5.1 QUIC 集成

HTTP/3 基于 QUIC 协议:

```go
import (
    "github.com/quic-go/quic-go"
    "github.com/quic-go/quic-go/http3"
)

// HTTP3Client 提供 HTTP/3 (QUIC) 追踪
type HTTP3Client struct {
    *TracedHTTPClient
}

func NewHTTP3Client() *HTTP3Client {
    roundTripper := &http3.RoundTripper{
        TLSClientConfig: &tls.Config{
            // TLS 配置
        },
    }

    client := &http.Client{
        Transport: NewTracedTransport(roundTripper),
    }

    return &HTTP3Client{
        TracedHTTPClient: NewTracedHTTPClient(client),
    }
}

func (c *HTTP3Client) Do(ctx context.Context, req *http.Request) (*http.Response, error) {
    span := trace.SpanFromContext(ctx)
    
    // 标记为 HTTP/3
    span.SetAttributes(
        semconv.NetworkProtocolName("http"),
        semconv.NetworkProtocolVersion("3"),
        attribute.String("network.transport", "quic"),
    )

    return c.TracedHTTPClient.Do(ctx, req)
}
```

### 5.2 0-RTT 处理

追踪 0-RTT 连接:

```go
// TracedQUICTransport 追踪 QUIC 特定事件
type TracedQUICTransport struct {
    base   *http3.RoundTripper
    tracer trace.Tracer
}

func (t *TracedQUICTransport) RoundTrip(req *http.Request) (*http.Response, error) {
    ctx := req.Context()
    span := trace.SpanFromContext(ctx)

    // QUIC 特定属性
    span.AddEvent("QUIC Connection Start")

    resp, err := t.base.RoundTrip(req)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    // 检查是否使用了 0-RTT
    if resp.TLS != nil && resp.TLS.DidResume {
        span.SetAttributes(attribute.Bool("quic.zero_rtt", true))
    }

    return resp, nil
}
```

---

## 6. 高级模式

### 6.1 重试与重定向

追踪 HTTP 重试和重定向:

```go
// RetryableClient 支持重试的 HTTP 客户端
type RetryableClient struct {
    client     *TracedHTTPClient
    maxRetries int
    tracer     trace.Tracer
}

func NewRetryableClient(maxRetries int) *RetryableClient {
    return &RetryableClient{
        client:     NewTracedHTTPClient(nil),
        maxRetries: maxRetries,
        tracer:     otel.Tracer("http-retry"),
    }
}

func (c *RetryableClient) DoWithRetry(ctx context.Context, req *http.Request) (*http.Response, error) {
    ctx, span := c.tracer.Start(ctx, "HTTP Request with Retry",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()

    var lastErr error
    for attempt := 0; attempt <= c.maxRetries; attempt++ {
        if attempt > 0 {
            span.AddEvent("Retry Attempt", trace.WithAttributes(
                attribute.Int("attempt", attempt),
            ))
            
            // 指数退避
            backoff := time.Duration(1<<uint(attempt-1)) * time.Second
            select {
            case <-time.After(backoff):
            case <-ctx.Done():
                return nil, ctx.Err()
            }
        }

        resp, err := c.client.Do(ctx, req)
        if err == nil && resp.StatusCode < 500 {
            span.SetAttributes(attribute.Int("http.retry.count", attempt))
            return resp, nil
        }

        lastErr = err
        if err != nil {
            span.AddEvent("Request Failed", trace.WithAttributes(
                attribute.String("error", err.Error()),
            ))
        } else {
            span.AddEvent("Server Error", trace.WithAttributes(
                attribute.Int("status_code", resp.StatusCode),
            ))
            resp.Body.Close()
        }
    }

    span.RecordError(lastErr)
    span.SetStatus(codes.Error, "Max retries exceeded")
    return nil, fmt.Errorf("max retries exceeded: %w", lastErr)
}
```

### 6.2 超时与取消

结合 Context 追踪超时:

```go
func DoWithTimeout(ctx context.Context, client *TracedHTTPClient, req *http.Request, timeout time.Duration) (*http.Response, error) {
    ctx, cancel := context.WithTimeout(ctx, timeout)
    defer cancel()

    span := trace.SpanFromContext(ctx)
    span.SetAttributes(attribute.String("http.timeout", timeout.String()))

    resp, err := client.Do(ctx, req)
    if err != nil {
        if ctx.Err() == context.DeadlineExceeded {
            span.AddEvent("Request Timeout", trace.WithAttributes(
                attribute.String("timeout", timeout.String()),
            ))
        }
    }

    return resp, err
}
```

### 6.3 请求体追踪

追踪请求和响应体大小:

```go
// CountingReader 包装 io.Reader 并计数
type CountingReader struct {
    reader io.Reader
    count  int64
}

func (r *CountingReader) Read(p []byte) (n int, err error) {
    n, err = r.reader.Read(p)
    r.count += int64(n)
    return
}

// WrapRequestBody 包装请求体以追踪大小
func WrapRequestBody(req *http.Request, span trace.Span) {
    if req.Body == nil {
        return
    }

    counter := &CountingReader{reader: req.Body}
    req.Body = io.NopCloser(counter)

    // 在请求完成后记录大小
    req = req.WithContext(context.WithValue(req.Context(), "bodyCounter", counter))
}

// RecordBodySize 记录请求体大小
func RecordBodySize(ctx context.Context, span trace.Span) {
    if counter, ok := ctx.Value("bodyCounter").(*CountingReader); ok {
        span.SetAttributes(attribute.Int64("http.request.body.size", counter.count))
    }
}
```

---

## 7. Go 完整实现

完整的生产级客户端:

```go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func initTracer() (*sdktrace.TracerProvider, error) {
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    resource := resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.ServiceName("http-client-example"),
        semconv.ServiceVersion("1.0.0"),
    )

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(resource),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

func main() {
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 创建带追踪的客户端
    client := NewRetryableClient(3)

    // 发起请求
    ctx := context.Background()
    req, err := http.NewRequestWithContext(ctx, "GET", "https://api.github.com/users/octocat", nil)
    if err != nil {
        log.Fatal(err)
    }

    req.Header.Set("User-Agent", "OpenTelemetry-Go-Client/1.0")

    resp, err := client.DoWithRetry(ctx, req)
    if err != nil {
        log.Fatal(err)
    }
    defer resp.Body.Close()

    fmt.Printf("Status: %d\n", resp.StatusCode)
}
```

---

## 8. 最佳实践

### 8.1 命名规范

- **简洁**: 使用 `GET`, `POST` 而非完整 URL
- **有路由时**: `POST /api/users`
- **无路由时**: `POST` (仅方法名)

### 8.2 敏感信息处理

```go
// SanitizeURL 清理 URL 中的敏感信息
func SanitizeURL(urlStr string) string {
    u, err := url.Parse(urlStr)
    if err != nil {
        return urlStr
    }

    // 移除密码
    if u.User != nil {
        u.User = url.UserPassword(u.User.Username(), "***")
    }

    // 清理查询参数
    query := u.Query()
    sensitiveParams := []string{"password", "token", "api_key"}
    for _, param := range sensitiveParams {
        if query.Has(param) {
            query.Set(param, "***")
        }
    }
    u.RawQuery = query.Encode()

    return u.String()
}
```

### 8.3 采样策略

```go
// AdaptiveSampler 基于响应时间的自适应采样
type AdaptiveSampler struct {
    threshold time.Duration
}

func (s *AdaptiveSampler) ShouldSample(duration time.Duration) bool {
    // 慢请求始终采样
    if duration > s.threshold {
        return true
    }
    // 快请求按比例采样
    return rand.Float64() < 0.1
}
```

---

## 9. 性能优化

### 9.1 连接池配置

```go
func NewOptimizedHTTPClient() *http.Client {
    transport := &http.Transport{
        MaxIdleConns:        100,
        MaxIdleConnsPerHost: 10,
        IdleConnTimeout:     90 * time.Second,
        DisableKeepAlives:   false,
    }

    return &http.Client{
        Transport: NewTracedTransport(transport),
        Timeout:   30 * time.Second,
    }
}
```

### 9.2 批量追踪

对于高频请求,使用批处理:

```go
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter,
        sdktrace.WithMaxExportBatchSize(512),
        sdktrace.WithBatchTimeout(5*time.Second),
    ),
)
```

---

## 10. 故障排查

### 10.1 常见问题

**问题 1**: Span 未创建父子关系

```go
// ❌ 错误
req, _ := http.NewRequest("GET", url, nil)
resp, _ := client.Do(req)

// ✅ 正确
req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
resp, _ := client.Do(req)
```

**问题 2**: 上下文未传播

```go
// ✅ 确保注入追踪上下文
otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
```

### 10.2 调试技巧

```go
// 启用详细日志
import "go.opentelemetry.io/otel/sdk/trace"

tp := sdktrace.NewTracerProvider(
    sdktrace.WithSpanProcessor(
        &loggingSpanProcessor{},
    ),
)

type loggingSpanProcessor struct{}

func (p *loggingSpanProcessor) OnStart(ctx context.Context, s sdktrace.ReadWriteSpan) {
    log.Printf("Span started: %s", s.Name())
}

func (p *loggingSpanProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
    log.Printf("Span ended: %s (duration: %v)", s.Name(), s.EndTime().Sub(s.StartTime()))
}

func (p *loggingSpanProcessor) Shutdown(ctx context.Context) error { return nil }
func (p *loggingSpanProcessor) ForceFlush(ctx context.Context) error { return nil }
```

---

## 总结

本文档详细介绍了 HTTP 客户端的 OpenTelemetry 追踪:

1. ✅ **核心属性**: `http.request.method`, `server.address`, `http.response.status_code`
2. ✅ **协议支持**: HTTP/1.1, HTTP/2, HTTP/3
3. ✅ **高级模式**: 重试、超时、连接复用
4. ✅ **Go 实现**: 完整的生产级示例
5. ✅ **最佳实践**: 命名、敏感信息、性能优化

**下一步**: 参见 `02_HTTP服务器.md` 了解服务器端追踪。

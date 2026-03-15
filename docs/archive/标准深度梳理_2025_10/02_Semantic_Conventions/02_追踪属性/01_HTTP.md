# HTTP语义约定详解

> **Semantic Conventions版本**: v1.27.0  
> **稳定性**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [HTTP语义约定详解](#http语义约定详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 适用范围](#11-适用范围)
    - [1.2 HTTP版本支持](#12-http版本支持)
  - [2. 通用属性](#2-通用属性)
    - [2.1 网络属性](#21-网络属性)
    - [2.2 URL属性](#22-url属性)
  - [3. HTTP客户端属性](#3-http客户端属性)
    - [3.1 必需属性](#31-必需属性)
    - [3.2 推荐属性](#32-推荐属性)
    - [3.3 条件必需属性](#33-条件必需属性)
  - [4. HTTP服务器属性](#4-http服务器属性)
    - [4.1 必需属性](#41-必需属性)
    - [4.2 推荐属性](#42-推荐属性)
    - [4.3 路由属性](#43-路由属性)
  - [5. HTTP头部捕获](#5-http头部捕获)
    - [5.1 请求头](#51-请求头)
    - [5.2 响应头](#52-响应头)
    - [5.3 敏感头部处理](#53-敏感头部处理)
  - [6. HTTP状态码映射](#6-http状态码映射)
    - [6.1 Span状态映射](#61-span状态映射)
    - [6.2 错误分类](#62-错误分类)
  - [7. HTTP指标](#7-http指标)
    - [7.1 客户端指标](#71-客户端指标)
    - [7.2 服务器指标](#72-服务器指标)
  - [8. 实现示例](#8-实现示例)
    - [8.1 HTTP客户端 (Go)](#81-http客户端-go)
    - [8.2 HTTP服务器 (Go)](#82-http服务器-go)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 参考资源](#10-参考资源)

## 1. 概述

### 1.1 适用范围

**HTTP语义约定适用于**：

```text
1. HTTP客户端
   - 发起HTTP请求
   - Span kind: CLIENT

2. HTTP服务器
   - 处理HTTP请求
   - Span kind: SERVER

3. HTTP代理
   - 转发HTTP请求
   - 可能是CLIENT或SERVER

4. 所有HTTP版本
   - HTTP/0.9, HTTP/1.0, HTTP/1.1
   - HTTP/2
   - HTTP/3 (QUIC)
```

### 1.2 HTTP版本支持

**版本特定考虑**：

```text
HTTP/1.1:
- 标准请求/响应
- 支持持久连接
- 明确的头部

HTTP/2:
- 多路复用
- 服务器推送
- 头部压缩 (HPACK)

HTTP/3:
- 基于QUIC
- 改进的性能
- 内置加密
```

---

## 2. 通用属性

### 2.1 网络属性

**网络层属性**：

| 属性名 | 类型 | 必需性 | 描述 | 示例 |
|--------|------|--------|------|------|
| `network.protocol.name` | string | 推荐 | 协议名称 | `http` |
| `network.protocol.version` | string | 推荐 | 协议版本 | `1.1`, `2`, `3` |
| `network.transport` | string | 可选 | 传输层协议 | `tcp`, `udp` |
| `network.type` | string | 可选 | 网络类型 | `ipv4`, `ipv6` |

**示例**：

```text
HTTP/1.1 over TCP:
network.protocol.name: "http"
network.protocol.version: "1.1"
network.transport: "tcp"

HTTP/2:
network.protocol.name: "http"
network.protocol.version: "2"

HTTP/3 (QUIC):
network.protocol.name: "http"
network.protocol.version: "3"
network.transport: "udp"
```

### 2.2 URL属性

**URL相关属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `url.full` | string | 完整URL | `https://example.com/path?q=1` |
| `url.scheme` | string | URL scheme | `http`, `https` |
| `url.path` | string | URL路径 | `/api/users` |
| `url.query` | string | 查询字符串 | `q=search&limit=10` |
| `url.fragment` | string | URL片段 | `section-1` |

**URL组成示例**：

```text
完整URL:
https://example.com:8080/api/users/123?active=true#profile

分解:
url.scheme:   https
server.address: example.com
server.port:  8080
url.path:     /api/users/123
url.query:    active=true
url.fragment: profile
```

---

## 3. HTTP客户端属性

### 3.1 必需属性

**HTTP客户端必需属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `http.request.method` | string | HTTP方法 | `GET`, `POST` |
| `server.address` | string | 服务器地址 | `example.com` |
| `url.full` | string | 完整请求URL | `https://example.com/api` |

**http.request.method 枚举值**：

```text
标准方法:
- GET
- POST
- PUT
- DELETE
- HEAD
- OPTIONS
- PATCH
- TRACE
- CONNECT

特殊处理:
- 标准方法: 使用大写
- 自定义方法: 原样记录
- 未知方法: 使用 "_OTHER"
```

### 3.2 推荐属性

**HTTP客户端推荐属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `http.response.status_code` | int | HTTP状态码 | `200`, `404` |
| `http.request.body.size` | int | 请求体大小(字节) | `1024` |
| `http.response.body.size` | int | 响应体大小(字节) | `2048` |
| `server.port` | int | 服务器端口 | `443`, `8080` |
| `network.protocol.version` | string | HTTP版本 | `1.1`, `2` |

**大小计算说明**：

```text
http.request.body.size:
- Content-Length头部的值
- 或实际传输的字节数
- 不包括HTTP头部

http.response.body.size:
- Content-Length头部的值
- 或实际接收的字节数
- 不包括HTTP头部
```

### 3.3 条件必需属性

**条件必需属性**：

| 属性名 | 类型 | 条件 | 示例 |
|--------|------|------|------|
| `error.type` | string | 请求失败时 | `timeout`, `connection_error` |
| `http.resend_count` | int | 发生重试时 | `0`, `1`, `2` |

**error.type 值**：

```text
网络错误:
- connection_error
- timeout
- name_resolution_error

HTTP错误 (4xx/5xx):
- 使用状态码: "400", "404", "500"

TLS错误:
- certificate_verify_failed
- ssl_handshake_timeout

其他:
- canceled (用户取消)
- _OTHER (未知错误)
```

---

## 4. HTTP服务器属性

### 4.1 必需属性

**HTTP服务器必需属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `http.request.method` | string | HTTP方法 | `GET`, `POST` |
| `url.path` | string | 请求路径 | `/api/users/123` |
| `url.scheme` | string | URL scheme | `http`, `https` |

**路径规范化**：

```text
原始请求: /api/users/../admin
规范化: /api/admin

原始请求: /path//to///resource
规范化: /path/to/resource

保留:
- 查询参数: 记录在url.query
- 片段: 通常不发送到服务器
```

### 4.2 推荐属性

**HTTP服务器推荐属性**：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `http.response.status_code` | int | HTTP状态码 | `200`, `404` |
| `http.route` | string | 路由模式 | `/api/users/{id}` |
| `server.address` | string | 服务器地址 | `example.com` |
| `server.port` | int | 服务器端口 | `80`, `443` |
| `client.address` | string | 客户端IP | `192.168.1.100` |
| `client.port` | int | 客户端端口 | `54321` |
| `user_agent.original` | string | User-Agent | `Mozilla/5.0...` |

**client.address 提取规则**：

```text
优先级:
1. X-Forwarded-For (第一个IP)
2. X-Real-IP
3. TCP连接的remote address

示例:
X-Forwarded-For: 203.0.113.1, 192.168.1.1
client.address: 203.0.113.1 (客户端真实IP)

直接连接:
remote_addr: 192.168.1.100
client.address: 192.168.1.100
```

### 4.3 路由属性

**http.route 定义**：

```text
http.route: 路由模板/模式

示例:
实际请求: GET /api/users/123
http.route: /api/users/{id}

实际请求: GET /api/products/456/reviews/789
http.route: /api/products/{productId}/reviews/{reviewId}

实际请求: GET /static/images/logo.png
http.route: /static/*  (通配符路由)

用途:
1. 性能聚合
   - 按路由模式分组
   - 计算p50/p95/p99延迟
   
2. 避免高基数
   - 使用模式而非具体值
   - 防止指标爆炸

3. 监控告警
   - 按路由设置阈值
   - 识别慢路由
```

---

## 5. HTTP头部捕获

### 5.1 请求头

**`http.request.header.<key>`**：

```text
格式: http.request.header.<normalized-key>

归一化规则:
- 转换为小写
- 连字符转为下划线
- 前缀: http.request.header.

示例:
Content-Type → http.request.header.content_type
User-Agent → http.request.header.user_agent
X-Request-ID → http.request.header.x_request_id

类型: string[]
原因: HTTP头部可以有多个值

示例值:
http.request.header.accept: ["application/json", "text/html"]
http.request.header.content_type: ["application/json; charset=utf-8"]
```

### 5.2 响应头

**`http.response.header.<key>`**：

```text
格式: http.response.header.<normalized-key>

示例:
Content-Type → http.response.header.content_type
Set-Cookie → http.response.header.set_cookie
X-RateLimit-Remaining → http.response.header.x_ratelimit_remaining

示例值:
http.response.header.content_type: ["application/json"]
http.response.header.content_length: ["1024"]
http.response.header.set_cookie: ["session=abc123; Path=/; HttpOnly"]
```

### 5.3 敏感头部处理

**敏感头部清单**：

```text
禁止捕获:
❌ Authorization
❌ Proxy-Authorization
❌ Cookie
❌ Set-Cookie

谨慎捕获 (脱敏):
⚠️ X-API-Key (仅前4位: "abcd****")
⚠️ X-Auth-Token (完全省略或哈希)

安全捕获:
✅ Content-Type
✅ Content-Length
✅ User-Agent
✅ Accept
✅ X-Request-ID
✅ X-Correlation-ID

配置示例:
allowed_request_headers:
  - content-type
  - accept
  - user-agent
  - x-request-id

blocked_request_headers:
  - authorization
  - cookie
  - x-api-key
```

---

## 6. HTTP状态码映射

### 6.1 Span状态映射

**HTTP状态码 → Span Status**：

```text
状态码映射规则:

1xx (信息性):
→ UNSET (继续处理)

2xx (成功):
→ OK
示例: 200, 201, 204

3xx (重定向):
→ OK (通常是成功)
示例: 301, 302, 304

4xx (客户端错误):
→ ERROR
示例: 400, 401, 403, 404, 429
特殊: 某些业务可能视404为OK

5xx (服务器错误):
→ ERROR
示例: 500, 502, 503, 504

特殊处理:
- 408 Request Timeout → ERROR
- 499 Client Closed Request → ERROR
```

**详细映射表**：

| HTTP状态码 | Span Status | Status Message |
|-----------|-------------|----------------|
| 100-199 | UNSET | - |
| 200-299 | OK | - |
| 300-399 | OK | - |
| 400 | ERROR | "Bad Request" |
| 401 | ERROR | "Unauthorized" |
| 403 | ERROR | "Forbidden" |
| 404 | ERROR | "Not Found" |
| 408 | ERROR | "Request Timeout" |
| 429 | ERROR | "Too Many Requests" |
| 500 | ERROR | "Internal Server Error" |
| 502 | ERROR | "Bad Gateway" |
| 503 | ERROR | "Service Unavailable" |
| 504 | ERROR | "Gateway Timeout" |

### 6.2 错误分类

**按状态码分类错误**：

```text
客户端错误 (4xx):
400: 请求格式错误
401: 缺少认证
403: 权限不足
404: 资源不存在
409: 冲突 (如: 重复创建)
422: 验证失败 (不可处理的实体)
429: 限流

服务器错误 (5xx):
500: 内部错误
502: 上游服务错误
503: 服务不可用 (过载/维护)
504: 上游超时

网络错误:
- 连接超时
- DNS解析失败
- 连接重置
```

---

## 7. HTTP指标

### 7.1 客户端指标

**推荐的HTTP客户端指标**：

```text
http.client.request.duration (Histogram):
- 描述: HTTP请求持续时间
- 单位: 秒 (s)
- 维度:
  * http.request.method
  * http.response.status_code
  * server.address
  * server.port
  * error.type

http.client.request.body.size (Histogram):
- 描述: HTTP请求体大小
- 单位: 字节 (By)
- 维度:
  * http.request.method
  * http.response.status_code
  * server.address

http.client.response.body.size (Histogram):
- 描述: HTTP响应体大小
- 单位: 字节 (By)
- 维度同上
```

### 7.2 服务器指标

**推荐的HTTP服务器指标**：

```text
http.server.request.duration (Histogram):
- 描述: HTTP请求处理时间
- 单位: 秒 (s)
- 维度:
  * http.request.method
  * http.response.status_code
  * http.route  (重要!)
  * url.scheme

http.server.active_requests (UpDownCounter):
- 描述: 并发请求数
- 单位: {request}
- 维度:
  * http.request.method
  * server.address
  * url.scheme

http.server.request.body.size (Histogram):
- 描述: 请求体大小
- 单位: 字节 (By)

http.server.response.body.size (Histogram):
- 描述: 响应体大小
- 单位: 字节 (By)
```

---

## 8. 实现示例

### 8.1 HTTP客户端 (Go)

**完整示例**：

```go
package main

import (
    "context"
    "fmt"
    "net/http"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

type TracedHTTPClient struct {
    client *http.Client
    tracer trace.Tracer
}

func NewTracedHTTPClient() *TracedHTTPClient {
    return &TracedHTTPClient{
        client: &http.Client{},
        tracer: otel.Tracer("http-client"),
    }
}

func (c *TracedHTTPClient) Do(ctx context.Context, req *http.Request) (*http.Response, error) {
    // 创建客户端span
    ctx, span := c.tracer.Start(ctx, fmt.Sprintf("HTTP %s", req.Method),
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            // 必需属性
            semconv.HTTPRequestMethodKey.String(req.Method),
            semconv.ServerAddress(req.URL.Hostname()),
            semconv.URLFull(req.URL.String()),
            
            // 推荐属性
            semconv.ServerPort(getPort(req.URL)),
            semconv.URLScheme(req.URL.Scheme),
            semconv.URLPath(req.URL.Path),
            semconv.NetworkProtocolName("http"),
            semconv.NetworkProtocolVersion(getHTTPVersion(req)),
        ),
    )
    defer span.End()
    
    // 注入追踪上下文
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    // 发送请求
    resp, err := c.client.Do(req.WithContext(ctx))
    
    if err != nil {
        // 记录错误
        span.SetStatus(codes.Error, err.Error())
        span.SetAttributes(
            semconv.ErrorType(classifyError(err)),
        )
        return nil, err
    }
    
    // 记录响应属性
    span.SetAttributes(
        semconv.HTTPResponseStatusCode(resp.StatusCode),
        semconv.HTTPResponseBodySize(int(resp.ContentLength)),
    )
    
    // 设置Span状态
    if resp.StatusCode >= 400 {
        span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", resp.StatusCode))
        span.SetAttributes(
            semconv.ErrorType(fmt.Sprintf("%d", resp.StatusCode)),
        )
    } else {
        span.SetStatus(codes.Ok, "")
    }
    
    return resp, nil
}

func getPort(url *url.URL) int {
    if url.Port() != "" {
        port, _ := strconv.Atoi(url.Port())
        return port
    }
    if url.Scheme == "https" {
        return 443
    }
    return 80
}

func classifyError(err error) string {
    switch {
    case errors.Is(err, context.DeadlineExceeded):
        return "timeout"
    case errors.Is(err, context.Canceled):
        return "canceled"
    default:
        return "connection_error"
    }
}
```

### 8.2 HTTP服务器 (Go)

**完整示例**：

```go
package main

import (
    "net/http"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func TracingMiddleware(next http.Handler) http.Handler {
    tracer := otel.Tracer("http-server")
    
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 提取上游SpanContext
        ctx := otel.GetTextMapPropagator().Extract(r.Context(), 
            propagation.HeaderCarrier(r.Header))
        
        // 创建服务器span
        ctx, span := tracer.Start(ctx, fmt.Sprintf("%s %s", r.Method, r.URL.Path),
            trace.WithSpanKind(trace.SpanKindServer),
            trace.WithAttributes(
                // 必需属性
                semconv.HTTPRequestMethodKey.String(r.Method),
                semconv.URLPath(r.URL.Path),
                semconv.URLScheme(getScheme(r)),
                
                // 推荐属性
                semconv.HTTPRoute(getRoute(r)),
                semconv.ServerAddress(r.Host),
                semconv.ServerPort(getServerPort(r)),
                semconv.ClientAddress(getClientIP(r)),
                semconv.UserAgentOriginal(r.UserAgent()),
                semconv.NetworkProtocolVersion(getHTTPProtoVersion(r)),
            ),
        )
        defer span.End()
        
        // 包装ResponseWriter以捕获状态码
        wrapped := &responseWriter{
            ResponseWriter: w,
            statusCode:     200,
        }
        
        // 处理请求
        next.ServeHTTP(wrapped, r.WithContext(ctx))
        
        // 记录响应属性
        span.SetAttributes(
            semconv.HTTPResponseStatusCode(wrapped.statusCode),
        )
        
        // 设置Span状态
        if wrapped.statusCode >= 400 {
            span.SetStatus(codes.Error, http.StatusText(wrapped.statusCode))
        } else {
            span.SetStatus(codes.Ok, "")
        }
    })
}

type responseWriter struct {
    http.ResponseWriter
    statusCode int
    written    bool
}

func (rw *responseWriter) WriteHeader(statusCode int) {
    if !rw.written {
        rw.statusCode = statusCode
        rw.written = true
        rw.ResponseWriter.WriteHeader(statusCode)
    }
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    if !rw.written {
        rw.WriteHeader(200)
    }
    return rw.ResponseWriter.Write(b)
}

func getScheme(r *http.Request) string {
    if r.TLS != nil {
        return "https"
    }
    if scheme := r.Header.Get("X-Forwarded-Proto"); scheme != "" {
        return scheme
    }
    return "http"
}

func getClientIP(r *http.Request) string {
    // 优先X-Forwarded-For
    if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
        // 取第一个IP
        if idx := strings.Index(xff, ","); idx != -1 {
            return strings.TrimSpace(xff[:idx])
        }
        return xff
    }
    
    // 次选X-Real-IP
    if xri := r.Header.Get("X-Real-IP"); xri != "" {
        return xri
    }
    
    // 最后使用RemoteAddr
    host, _, _ := net.SplitHostPort(r.RemoteAddr)
    return host
}

func getRoute(r *http.Request) string {
    // 从路由器获取路由模式
    // 这里需要根据实际使用的路由框架实现
    // 示例: 使用gorilla/mux
    // route := mux.CurrentRoute(r)
    // if route != nil {
    //     if pathTemplate, err := route.GetPathTemplate(); err == nil {
    //         return pathTemplate
    //     }
    // }
    return "" // 如果无法确定,返回空
}
```

---

## 9. 最佳实践

```text
1. 属性选择
   ✅ 优先使用标准属性
   ✅ http.route非常重要 (避免高基数)
   ✅ 记录http.response.status_code

2. 敏感信息
   ❌ 不要捕获Authorization头
   ❌ 不要捕获Cookie
   ❌ 不要在URL中记录密码
   ✅ 脱敏查询参数 (如: token)

3. 性能
   ✅ 使用http.route分组
   ✅ 避免在span name中使用ID
   ❌ 不要捕获所有头部

4. 错误处理
   ✅ 4xx/5xx设置Span状态为ERROR
   ✅ 记录error.type
   ✅ 网络错误也设置ERROR

5. 指标
   ✅ 使用http.server.request.duration
   ✅ 按http.route分组
   ✅ 监控p95/p99延迟
```

---

## 10. 参考资源

- **Semantic Conventions (HTTP)**: <https://opentelemetry.io/docs/specs/semconv/http/http-spans/>
- **HTTP Metrics**: <https://opentelemetry.io/docs/specs/semconv/http/http-metrics/>
- **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**下一步**: [02_gRPC.md](./02_gRPC.md)

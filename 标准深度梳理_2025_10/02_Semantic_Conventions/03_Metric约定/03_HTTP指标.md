# HTTP 指标（HTTP Metrics）

## 目录

- [HTTP 指标（HTTP Metrics）](#http-指标http-metrics)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. HTTP 服务器指标](#2-http-服务器指标)
    - [2.1 请求速率](#21-请求速率)
    - [2.2 请求延迟](#22-请求延迟)
    - [2.3 请求大小](#23-请求大小)
    - [2.4 响应大小](#24-响应大小)
    - [2.5 活跃连接数](#25-活跃连接数)
  - [3. HTTP 客户端指标](#3-http-客户端指标)
    - [3.1 客户端请求速率](#31-客户端请求速率)
    - [3.2 客户端延迟](#32-客户端延迟)
    - [3.3 连接池指标](#33-连接池指标)
  - [4. Go 实现](#4-go-实现)
    - [4.1 标准库集成](#41-标准库集成)
    - [4.2 框架集成](#42-框架集成)
    - [4.3 中间件模式](#43-中间件模式)
  - [5. 完整示例](#5-完整示例)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 基数控制](#61-基数控制)
    - [6.2 错误分类](#62-错误分类)
    - [6.3 采样策略](#63-采样策略)
    - [6.4 告警配置](#64-告警配置)
  - [7. 常见问题](#7-常见问题)
  - [总结](#总结)

---

## 1. 概述

HTTP 指标是应用性能监控的核心，遵循 [OpenTelemetry HTTP Metrics Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/http/http-metrics/)。

**关键指标**：
- 📊 **请求速率**：QPS/RPS
- ⏱️ **延迟分布**：P50/P90/P99
- 🚨 **错误率**：4xx/5xx 比例
- 📈 **吞吐量**：请求/响应大小

---

## 2. HTTP 服务器指标

### 2.1 请求速率

**指标名称**：`http.server.request.duration`

**描述**：HTTP 请求处理时间

**单位**：`s`

**指标类型**：Histogram

**必需属性**：
- `http.request.method`：HTTP 方法（如 `GET`, `POST`）
- `http.response.status_code`：状态码（如 `200`, `404`, `500`）
- `url.scheme`：协议（`http` / `https`）
- `network.protocol.version`：HTTP 版本（`1.1`, `2`, `3`）

**可选属性**：
- `http.route`：路由模板（如 `/users/{id}`）
- `server.address`：服务器地址
- `server.port`：服务器端口

**推荐桶边界**：
```go
[]float64{
    0.005,  // 5 ms
    0.01,   // 10 ms
    0.025,  // 25 ms
    0.05,   // 50 ms
    0.1,    // 100 ms
    0.25,   // 250 ms
    0.5,    // 500 ms
    1.0,    // 1 s
    2.5,    // 2.5 s
    5.0,    // 5 s
    10.0,   // 10 s
}
```

### 2.2 请求延迟

**指标名称**：`http.server.active_requests`

**描述**：当前活跃的 HTTP 请求数

**单位**：`{request}`

**指标类型**：UpDownCounter

**必需属性**：
- `http.request.method`
- `url.scheme`

### 2.3 请求大小

**指标名称**：`http.server.request.body.size`

**描述**：HTTP 请求体大小

**单位**：`By`

**指标类型**：Histogram

**必需属性**：同请求速率

### 2.4 响应大小

**指标名称**：`http.server.response.body.size`

**描述**：HTTP 响应体大小

**单位**：`By`

**指标类型**：Histogram

**必需属性**：同请求速率

### 2.5 活跃连接数

**指标名称**：`http.server.connection.duration`

**描述**：HTTP 连接持续时间

**单位**：`s`

**指标类型**：Histogram

---

## 3. HTTP 客户端指标

### 3.1 客户端请求速率

**指标名称**：`http.client.request.duration`

**描述**：HTTP 客户端请求时间（包括网络延迟）

**单位**：`s`

**指标类型**：Histogram

**必需属性**：
- `http.request.method`
- `http.response.status_code`
- `url.scheme`
- `network.protocol.version`
- `server.address`：目标服务器
- `server.port`

### 3.2 客户端延迟

**指标名称**：`http.client.request.body.size` / `http.client.response.body.size`

**描述**：客户端请求/响应大小

**单位**：`By`

**指标类型**：Histogram

### 3.3 连接池指标

**指标名称**：`http.client.connection.duration`

**描述**：连接持续时间

**单位**：`s`

**指标类型**：Histogram

**指标名称**：`http.client.open_connections`

**描述**：打开的连接数

**单位**：`{connection}`

**指标类型**：UpDownCounter

**必需属性**：
- `http.connection.state`：`active` / `idle`
- `server.address`
- `server.port`

---

## 4. Go 实现

### 4.1 标准库集成

```go
package httpmetrics

import (
    "fmt"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

// ServerMetrics HTTP 服务器指标
type ServerMetrics struct {
    meter           metric.Meter
    requestDuration metric.Float64Histogram
    activeRequests  metric.Int64UpDownCounter
    requestSize     metric.Float64Histogram
    responseSize    metric.Float64Histogram
}

// NewServerMetrics 创建服务器指标
func NewServerMetrics() (*ServerMetrics, error) {
    meter := otel.Meter("http.server")
    
    sm := &ServerMetrics{
        meter: meter,
    }
    
    var err error
    
    sm.requestDuration, err = meter.Float64Histogram(
        "http.server.request.duration",
        metric.WithDescription("HTTP server request duration"),
        metric.WithUnit("s"),
        metric.WithExplicitBucketBoundaries(
            0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0,
        ),
    )
    if err != nil {
        return nil, err
    }
    
    sm.activeRequests, err = meter.Int64UpDownCounter(
        "http.server.active_requests",
        metric.WithDescription("Active HTTP requests"),
        metric.WithUnit("{request}"),
    )
    if err != nil {
        return nil, err
    }
    
    sm.requestSize, err = meter.Float64Histogram(
        "http.server.request.body.size",
        metric.WithDescription("HTTP request body size"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }
    
    sm.responseSize, err = meter.Float64Histogram(
        "http.server.response.body.size",
        metric.WithDescription("HTTP response body size"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }
    
    return sm, nil
}

// Middleware HTTP 指标中间件
func (sm *ServerMetrics) Middleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        
        // 增加活跃请求数
        attrs := []attribute.KeyValue{
            attribute.String("http.request.method", r.Method),
            attribute.String("url.scheme", schemeFromRequest(r)),
        }
        sm.activeRequests.Add(r.Context(), 1, metric.WithAttributes(attrs...))
        defer sm.activeRequests.Add(r.Context(), -1, metric.WithAttributes(attrs...))
        
        // 包装 ResponseWriter 以捕获状态码和响应大小
        rw := &responseWriter{
            ResponseWriter: w,
            statusCode:     http.StatusOK,
        }
        
        // 处理请求
        next.ServeHTTP(rw, r)
        
        // 记录指标
        duration := time.Since(start).Seconds()
        
        fullAttrs := append(attrs,
            attribute.Int("http.response.status_code", rw.statusCode),
            attribute.String("network.protocol.version", protocolVersion(r)),
        )
        
        sm.requestDuration.Record(r.Context(), duration, metric.WithAttributes(fullAttrs...))
        
        if r.ContentLength > 0 {
            sm.requestSize.Record(r.Context(), float64(r.ContentLength), metric.WithAttributes(fullAttrs...))
        }
        
        if rw.bytesWritten > 0 {
            sm.responseSize.Record(r.Context(), float64(rw.bytesWritten), metric.WithAttributes(fullAttrs...))
        }
    })
}

// responseWriter 包装 http.ResponseWriter
type responseWriter struct {
    http.ResponseWriter
    statusCode   int
    bytesWritten int
}

func (rw *responseWriter) WriteHeader(statusCode int) {
    rw.statusCode = statusCode
    rw.ResponseWriter.WriteHeader(statusCode)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    n, err := rw.ResponseWriter.Write(b)
    rw.bytesWritten += n
    return n, err
}

func schemeFromRequest(r *http.Request) string {
    if r.TLS != nil {
        return "https"
    }
    return "http"
}

func protocolVersion(r *http.Request) string {
    switch r.ProtoMajor {
    case 1:
        return "1.1"
    case 2:
        return "2"
    case 3:
        return "3"
    default:
        return r.Proto
    }
}
```

### 4.2 框架集成

**Gin 框架**：
```go
package ginmetrics

import (
    "time"

    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

func MetricsMiddleware(metrics *ServerMetrics) gin.HandlerFunc {
    return func(c *gin.Context) {
        start := time.Now()
        
        attrs := []attribute.KeyValue{
            attribute.String("http.request.method", c.Request.Method),
            attribute.String("url.scheme", c.Request.URL.Scheme),
        }
        metrics.activeRequests.Add(c.Request.Context(), 1, metric.WithAttributes(attrs...))
        defer metrics.activeRequests.Add(c.Request.Context(), -1, metric.WithAttributes(attrs...))
        
        c.Next()
        
        duration := time.Since(start).Seconds()
        
        fullAttrs := append(attrs,
            attribute.Int("http.response.status_code", c.Writer.Status()),
            attribute.String("http.route", c.FullPath()),
        )
        
        metrics.requestDuration.Record(c.Request.Context(), duration, metric.WithAttributes(fullAttrs...))
    }
}
```

**Echo 框架**：
```go
package echometrics

import (
    "time"

    "github.com/labstack/echo/v4"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
)

func MetricsMiddleware(metrics *ServerMetrics) echo.MiddlewareFunc {
    return func(next echo.HandlerFunc) echo.HandlerFunc {
        return func(c echo.Context) error {
            start := time.Now()
            
            attrs := []attribute.KeyValue{
                attribute.String("http.request.method", c.Request().Method),
            }
            metrics.activeRequests.Add(c.Request().Context(), 1, metric.WithAttributes(attrs...))
            defer metrics.activeRequests.Add(c.Request().Context(), -1, metric.WithAttributes(attrs...))
            
            err := next(c)
            
            duration := time.Since(start).Seconds()
            statusCode := c.Response().Status
            
            fullAttrs := append(attrs,
                attribute.Int("http.response.status_code", statusCode),
                attribute.String("http.route", c.Path()),
            )
            
            metrics.requestDuration.Record(c.Request().Context(), duration, metric.WithAttributes(fullAttrs...))
            
            return err
        }
    }
}
```

### 4.3 中间件模式

**路由级指标**：
```go
func RouteMetrics(route string, metrics *ServerMetrics) func(http.Handler) http.Handler {
    return func(next http.Handler) http.Handler {
        return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
            start := time.Now()
            
            rw := &responseWriter{ResponseWriter: w, statusCode: 200}
            next.ServeHTTP(rw, r)
            
            attrs := []attribute.KeyValue{
                attribute.String("http.request.method", r.Method),
                attribute.Int("http.response.status_code", rw.statusCode),
                attribute.String("http.route", route),
            }
            
            metrics.requestDuration.Record(r.Context(), time.Since(start).Seconds(),
                metric.WithAttributes(attrs...))
        })
    }
}
```

---

## 5. 完整示例

```go
package main

import (
    "context"
    "log"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func main() {
    ctx := context.Background()
    
    // 初始化 OpenTelemetry
    res, _ := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("http-server"),
        ),
    )
    
    exporter, _ := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithInsecure(),
        otlpmetricgrpc.WithEndpoint("localhost:4317"),
    )
    
    provider := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(metric.NewPeriodicReader(exporter,
            metric.WithInterval(10*time.Second),
        )),
    )
    defer provider.Shutdown(ctx)
    otel.SetMeterProvider(provider)
    
    // 创建指标
    metrics, _ := NewServerMetrics()
    
    // 设置路由
    mux := http.NewServeMux()
    
    mux.Handle("/", metrics.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        w.Write([]byte("Hello, World!"))
    })))
    
    mux.Handle("/slow", metrics.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        time.Sleep(100 * time.Millisecond)
        w.Write([]byte("Slow response"))
    })))
    
    mux.Handle("/error", metrics.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        http.Error(w, "Internal Server Error", http.StatusInternalServerError)
    })))
    
    // 启动服务器
    log.Println("服务器启动在 :8080")
    log.Fatal(http.ListenAndServe(":8080", mux))
}
```

---

## 6. 最佳实践

### 6.1 基数控制

**问题**：高基数属性（如 `url.path`）会导致指标爆炸。

**解决方案**：
```go
// ❌ 不要使用原始路径
attribute.String("url.path", r.URL.Path)  // /users/12345, /users/67890, ...

// ✅ 使用路由模板
attribute.String("http.route", "/users/{id}")
```

### 6.2 错误分类

```go
func statusCategory(code int) string {
    switch {
    case code >= 200 && code < 300:
        return "2xx"
    case code >= 300 && code < 400:
        return "3xx"
    case code >= 400 && code < 500:
        return "4xx"
    case code >= 500:
        return "5xx"
    default:
        return "unknown"
    }
}
```

### 6.3 采样策略

对于高流量服务，使用采样：
```go
import "math/rand"

func shouldSample(rate float64) bool {
    return rand.Float64() < rate
}

if shouldSample(0.1) { // 10% 采样
    metrics.requestDuration.Record(ctx, duration, ...)
}
```

### 6.4 告警配置

**Prometheus 告警规则**：
```yaml
groups:
  - name: http_alerts
    rules:
      - alert: HighHTTPErrorRate
        expr: |
          sum(rate(http_server_request_duration_count{http_response_status_code=~"5.."}[5m])) /
          sum(rate(http_server_request_duration_count[5m])) > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "HTTP 5xx 错误率过高"
      
      - alert: HighHTTPLatency
        expr: histogram_quantile(0.99, rate(http_server_request_duration_bucket[5m])) > 1
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "HTTP P99 延迟过高"
```

---

## 7. 常见问题

**Q1: 为什么使用 Histogram 而不是 Counter？**

A: Histogram 可以计算百分位数（P50/P90/P99），Counter 只能计算速率。

**Q2: 如何选择桶边界？**

A: 根据业务 SLA 选择。例如，如果 SLA 要求 P99 < 100ms，应包含 0.05, 0.1, 0.15 等边界。

**Q3: 如何避免指标基数爆炸？**

A:
- 使用路由模板而非原始路径
- 对状态码分组（`2xx`, `4xx`, `5xx`）
- 限制自定义标签的取值范围

**Q4: 如何监控 HTTP/2 和 HTTP/3？**

A: 使用 `network.protocol.version` 属性区分协议版本，并监控特定的 HTTP/2 和 HTTP/3 指标（如流数量）。

---

## 总结

本文档详细介绍了 OpenTelemetry HTTP 指标的语义约定和 Go 1.25.1 实现方案，涵盖：

✅ **服务器指标**：请求速率、延迟、大小、活跃请求  
✅ **客户端指标**：请求时间、连接池  
✅ **Go 实现**：标准库、框架（Gin/Echo）、中间件  
✅ **完整示例**：生产级 HTTP 服务器  
✅ **最佳实践**：基数控制、错误分类、采样、告警  

**下一步**：
- 📖 阅读《数据库指标》学习数据库监控
- 📖 阅读《自定义指标》学习业务指标
- 🔗 参考 [OpenTelemetry HTTP Metrics](https://opentelemetry.io/docs/specs/semconv/http/http-metrics/)


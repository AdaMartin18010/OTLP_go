# Prometheus 高级集成与 OTLP 完整集成（2025版）

> **Prometheus 版本**: v2.48+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Prometheus 高级集成与 OTLP 完整集成（2025版）](#prometheus-高级集成与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Prometheus 概述](#1-prometheus-概述)
    - [1.1 为什么选择 Prometheus](#11-为什么选择-prometheus)
    - [1.2 与其他监控系统对比](#12-与其他监控系统对比)
    - [1.3 核心指标类型](#13-核心指标类型)
  - [2. 快速开始](#2-快速开始)
    - [2.1 Docker 部署 Prometheus](#21-docker-部署-prometheus)
    - [2.2 Go 依赖安装](#22-go-依赖安装)
    - [2.3 基础配置](#23-基础配置)
  - [3. OTLP 完整集成](#3-otlp-完整集成)
    - [3.1 OTLP Prometheus Exporter](#31-otlp-prometheus-exporter)
    - [3.2 自定义 Prometheus Registry](#32-自定义-prometheus-registry)
  - [4. 高级特性](#4-高级特性)
    - [4.1 自定义 Histogram Buckets](#41-自定义-histogram-buckets)
    - [4.2 Summary vs Histogram](#42-summary-vs-histogram)
    - [4.3 中间件集成](#43-中间件集成)
  - [5. 完整示例](#5-完整示例)
    - [5.1 Web 服务监控](#51-web-服务监控)
  - [6. 性能优化](#6-性能优化)
    - [6.1 减少标签基数](#61-减少标签基数)
    - [6.2 使用 Exemplars](#62-使用-exemplars)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 命名规范](#71-命名规范)
    - [7.2 PromQL 查询示例](#72-promql-查询示例)
  - [8. 总结](#8-总结)
    - [8.1 优势与劣势](#81-优势与劣势)

---

## 1. Prometheus 概述

### 1.1 为什么选择 Prometheus

**Prometheus** 是云原生时代最流行的监控系统，CNCF 毕业项目。

```text
✅ 核心优势:
  - 多维数据模型 - 强大的标签系统
  - 灵活查询 - PromQL 查询语言
  - 无依赖 - 单体架构，易部署
  - 高效存储 - 时序数据库优化
  - 主动拉取 - Pull 模型，服务发现
  - 告警系统 - Alertmanager 集成
  - 可视化 - Grafana 完美集成

📊 使用统计:
  - GitHub Stars: 55,000+
  - 生产使用: 数万家公司
  - CNCF: 毕业项目
  - 社区: 极其活跃
```

### 1.2 与其他监控系统对比

```text
┌──────────────┬─────────┬──────────┬──────────┬────────────┐
│   系统       │  性能   │ 查询能力 │ 易用性   │ 推荐指数   │
├──────────────┼─────────┼──────────┼──────────┼────────────┤
│ Prometheus   │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐⭐  │
│ InfluxDB     │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐   │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐   │
│ Datadog      │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐⭐  │ ⭐⭐⭐⭐⭐  │  ⭐⭐⭐⭐⭐  │
│ VictoriaM    │  ⭐⭐⭐⭐⭐ │ ⭐⭐⭐⭐   │ ⭐⭐⭐⭐   │  ⭐⭐⭐⭐   │
│ OpenMetrics  │  ⭐⭐⭐⭐  │ ⭐⭐⭐    │ ⭐⭐⭐    │  ⭐⭐⭐    │
└──────────────┴─────────┴──────────┴──────────┴────────────┘

特点:
  - Prometheus: 云原生标准，PromQL 强大
  - InfluxDB: 通用时序数据库
  - Datadog: 商业 SaaS，功能最全
  - VictoriaMetrics: Prometheus 增强版
```

### 1.3 核心指标类型

```go
// Prometheus 四种指标类型
type MetricTypes struct {
    // Counter - 计数器（只增不减）
    Counter prometheus.Counter
    
    // Gauge - 仪表盘（可增可减）
    Gauge prometheus.Gauge
    
    // Histogram - 直方图（分布统计）
    Histogram prometheus.Histogram
    
    // Summary - 摘要（分位数）
    Summary prometheus.Summary
}

// 使用场景
scenarios := map[string]string{
    "Counter":   "请求总数、错误总数、任务完成数",
    "Gauge":     "当前并发数、内存使用、队列长度",
    "Histogram": "请求延迟分布、响应大小分布",
    "Summary":   "请求延迟分位数（P50/P95/P99）",
}
```

---

## 2. 快速开始

### 2.1 Docker 部署 Prometheus

```bash
# 创建配置文件
cat > prometheus.yml <<EOF
global:
  scrape_interval: 15s
  evaluation_interval: 15s

scrape_configs:
  - job_name: 'go-app'
    static_configs:
      - targets: ['host.docker.internal:8080']
        labels:
          environment: 'development'
          service: 'my-service'
EOF

# 启动 Prometheus
docker run -d \
  --name prometheus \
  -p 9090:9090 \
  -v $(pwd)/prometheus.yml:/etc/prometheus/prometheus.yml \
  prom/prometheus:v2.48.0

# 访问 UI: http://localhost:9090
```

### 2.2 Go 依赖安装

```bash
# Prometheus Go 客户端
go get github.com/prometheus/client_golang/prometheus@v1.19.0
go get github.com/prometheus/client_golang/prometheus/promhttp

# OTLP 依赖
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/exporters/prometheus@v0.47.0
go get go.opentelemetry.io/otel/sdk/metric@v1.32.0
```

### 2.3 基础配置

```go
package main

import (
    "log"
    "net/http"
    
    "github.com/prometheus/client_golang/prometheus"
    "github.com/prometheus/client_golang/prometheus/promhttp"
)

func main() {
    // 创建指标
    requestCounter := prometheus.NewCounterVec(
        prometheus.CounterOpts{
            Name: "http_requests_total",
            Help: "Total HTTP requests",
        },
        []string{"method", "endpoint", "status"},
    )
    
    // 注册指标
    prometheus.MustRegister(requestCounter)
    
    // 暴露 /metrics 端点
    http.Handle("/metrics", promhttp.Handler())
    
    // 业务路由
    http.HandleFunc("/api", func(w http.ResponseWriter, r *http.Request) {
        requestCounter.WithLabelValues(r.Method, "/api", "200").Inc()
        w.Write([]byte("Hello"))
    })
    
    log.Println("Starting server on :8080")
    http.ListenAndServe(":8080", nil)
}
```

---

## 3. OTLP 完整集成

### 3.1 OTLP Prometheus Exporter

```go
package main

import (
    "context"
    "log"
    "net/http"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/prometheus"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func main() {
    ctx := context.Background()
    
    // 创建 Prometheus Exporter
    exporter, err := prometheus.New()
    if err != nil {
        log.Fatal(err)
    }
    
    // 创建 MeterProvider
    provider := metric.NewMeterProvider(
        metric.WithReader(exporter),
        metric.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceName("my-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
        )),
    )
    
    otel.SetMeterProvider(provider)
    
    // 创建 Meter
    meter := provider.Meter("my-service")
    
    // 创建指标
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Total HTTP requests"),
    )
    
    requestDuration, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    
    activeConnections, _ := meter.Int64UpDownCounter(
        "http.server.active_connections",
        metric.WithDescription("Active HTTP connections"),
    )
    
    // 暴露 metrics 端点
    http.Handle("/metrics", exporter)
    
    // 业务路由
    http.HandleFunc("/api", func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        
        // 增加活跃连接
        activeConnections.Add(ctx, 1)
        defer activeConnections.Add(ctx, -1)
        
        // 业务逻辑
        time.Sleep(100 * time.Millisecond)
        
        // 记录指标
        duration := time.Since(start).Milliseconds()
        requestCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("method", r.Method),
                attribute.String("endpoint", "/api"),
                attribute.Int("status", 200),
            ),
        )
        requestDuration.Record(ctx, float64(duration),
            metric.WithAttributes(
                attribute.String("method", r.Method),
                attribute.String("endpoint", "/api"),
            ),
        )
        
        w.Write([]byte("OK"))
    })
    
    log.Println("Starting server on :8080")
    http.ListenAndServe(":8080", nil)
}
```

### 3.2 自定义 Prometheus Registry

```go
package metrics

import (
    "github.com/prometheus/client_golang/prometheus"
    "github.com/prometheus/client_golang/prometheus/collectors"
)

// MetricsCollector 自定义指标收集器
type MetricsCollector struct {
    registry *prometheus.Registry
    
    // HTTP 指标
    httpRequestsTotal     *prometheus.CounterVec
    httpRequestDuration   *prometheus.HistogramVec
    httpRequestSize       *prometheus.HistogramVec
    httpResponseSize      *prometheus.HistogramVec
    httpActiveConnections prometheus.Gauge
    
    // 业务指标
    businessMetrics *prometheus.CounterVec
    
    // 系统指标
    goroutines prometheus.Gauge
    memAlloc   prometheus.Gauge
}

func NewMetricsCollector() *MetricsCollector {
    reg := prometheus.NewRegistry()
    
    // 注册默认收集器
    reg.MustRegister(collectors.NewGoCollector())
    reg.MustRegister(collectors.NewProcessCollector(collectors.ProcessCollectorOpts{}))
    
    mc := &MetricsCollector{
        registry: reg,
        
        // HTTP 指标
        httpRequestsTotal: prometheus.NewCounterVec(
            prometheus.CounterOpts{
                Name: "http_requests_total",
                Help: "Total number of HTTP requests",
            },
            []string{"method", "endpoint", "status"},
        ),
        
        httpRequestDuration: prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name:    "http_request_duration_seconds",
                Help:    "HTTP request latencies in seconds",
                Buckets: prometheus.DefBuckets, // 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10
            },
            []string{"method", "endpoint"},
        ),
        
        httpRequestSize: prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name:    "http_request_size_bytes",
                Help:    "HTTP request size in bytes",
                Buckets: prometheus.ExponentialBuckets(100, 10, 8), // 100, 1000, 10000, ...
            },
            []string{"method", "endpoint"},
        ),
        
        httpResponseSize: prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name:    "http_response_size_bytes",
                Help:    "HTTP response size in bytes",
                Buckets: prometheus.ExponentialBuckets(100, 10, 8),
            },
            []string{"method", "endpoint"},
        ),
        
        httpActiveConnections: prometheus.NewGauge(
            prometheus.GaugeOpts{
                Name: "http_active_connections",
                Help: "Number of active HTTP connections",
            },
        ),
        
        // 业务指标
        businessMetrics: prometheus.NewCounterVec(
            prometheus.CounterOpts{
                Name: "business_operations_total",
                Help: "Total business operations",
            },
            []string{"operation", "status"},
        ),
        
        // 系统指标
        goroutines: prometheus.NewGauge(
            prometheus.GaugeOpts{
                Name: "goroutines_count",
                Help: "Number of goroutines",
            },
        ),
        
        memAlloc: prometheus.NewGauge(
            prometheus.GaugeOpts{
                Name: "memory_alloc_bytes",
                Help: "Allocated memory in bytes",
            },
        ),
    }
    
    // 注册所有指标
    reg.MustRegister(
        mc.httpRequestsTotal,
        mc.httpRequestDuration,
        mc.httpRequestSize,
        mc.httpResponseSize,
        mc.httpActiveConnections,
        mc.businessMetrics,
        mc.goroutines,
        mc.memAlloc,
    )
    
    return mc
}

func (mc *MetricsCollector) Registry() *prometheus.Registry {
    return mc.registry
}

// RecordHTTPRequest 记录 HTTP 请求
func (mc *MetricsCollector) RecordHTTPRequest(method, endpoint, status string, duration float64, reqSize, respSize int64) {
    mc.httpRequestsTotal.WithLabelValues(method, endpoint, status).Inc()
    mc.httpRequestDuration.WithLabelValues(method, endpoint).Observe(duration)
    mc.httpRequestSize.WithLabelValues(method, endpoint).Observe(float64(reqSize))
    mc.httpResponseSize.WithLabelValues(method, endpoint).Observe(float64(respSize))
}

// IncrementActiveConnections 增加活跃连接
func (mc *MetricsCollector) IncrementActiveConnections() {
    mc.httpActiveConnections.Inc()
}

// DecrementActiveConnections 减少活跃连接
func (mc *MetricsCollector) DecrementActiveConnections() {
    mc.httpActiveConnections.Dec()
}

// RecordBusinessOperation 记录业务操作
func (mc *MetricsCollector) RecordBusinessOperation(operation, status string) {
    mc.businessMetrics.WithLabelValues(operation, status).Inc()
}

// UpdateSystemMetrics 更新系统指标
func (mc *MetricsCollector) UpdateSystemMetrics() {
    var m runtime.MemStats
    runtime.ReadMemStats(&m)
    
    mc.goroutines.Set(float64(runtime.NumGoroutine()))
    mc.memAlloc.Set(float64(m.Alloc))
}
```

---

## 4. 高级特性

### 4.1 自定义 Histogram Buckets

```go
// 为不同场景定义不同的 buckets

// API 延迟 (ms)
apiLatencyBuckets := []float64{
    1, 2, 5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000, 10000,
}

// 数据库查询延迟 (ms)
dbLatencyBuckets := []float64{
    0.1, 0.5, 1, 2, 5, 10, 25, 50, 100, 250, 500, 1000,
}

// 文件大小 (bytes)
fileSizeBuckets := prometheus.ExponentialBuckets(
    1024,      // 起始值 1KB
    2,         // 倍数
    10,        // 桶数量
) // 1KB, 2KB, 4KB, 8KB, 16KB, 32KB, 64KB, 128KB, 256KB, 512KB

// 队列长度
queueLengthBuckets := prometheus.LinearBuckets(
    0,    // 起始值
    10,   // 步长
    20,   // 桶数量
) // 0, 10, 20, 30, ..., 190

// 使用示例
requestLatency := prometheus.NewHistogramVec(
    prometheus.HistogramOpts{
        Name:    "http_request_duration_ms",
        Help:    "HTTP request latency in milliseconds",
        Buckets: apiLatencyBuckets,
    },
    []string{"method", "endpoint"},
)
```

### 4.2 Summary vs Histogram

```go
// Summary - 客户端计算分位数
requestLatencySummary := prometheus.NewSummaryVec(
    prometheus.SummaryOpts{
        Name:       "http_request_duration_summary_seconds",
        Help:       "HTTP request latencies (summary)",
        Objectives: map[float64]float64{
            0.5:  0.05,  // P50，误差 ±5%
            0.9:  0.01,  // P90，误差 ±1%
            0.95: 0.005, // P95，误差 ±0.5%
            0.99: 0.001, // P99，误差 ±0.1%
        },
        MaxAge: 10 * time.Minute,
    },
    []string{"method", "endpoint"},
)

// Histogram - 服务端聚合
requestLatencyHistogram := prometheus.NewHistogramVec(
    prometheus.HistogramOpts{
        Name:    "http_request_duration_histogram_seconds",
        Help:    "HTTP request latencies (histogram)",
        Buckets: apiLatencyBuckets,
    },
    []string{"method", "endpoint"},
)

// 对比:
comparison := `
┌────────────┬──────────────┬──────────────────┐
│   特性     │   Summary    │   Histogram      │
├────────────┼──────────────┼──────────────────┤
│ 计算位置   │  客户端      │  服务端(Prom)    │
│ 聚合能力   │  不支持      │  支持            │
│ 精度       │  高(精确)    │  近似(桶)        │
│ 性能开销   │  高          │  低              │
│ 推荐场景   │  单实例监控  │  多实例聚合      │
└────────────┴──────────────┴──────────────────┘
`
```

### 4.3 中间件集成

```go
package middleware

import (
    "net/http"
    "strconv"
    "time"
    
    "github.com/prometheus/client_golang/prometheus"
)

type PrometheusMiddleware struct {
    requestsTotal   *prometheus.CounterVec
    requestDuration *prometheus.HistogramVec
    requestSize     *prometheus.HistogramVec
    responseSize    *prometheus.HistogramVec
    inFlightGauge   prometheus.Gauge
}

func NewPrometheusMiddleware(reg *prometheus.Registry) *PrometheusMiddleware {
    pm := &PrometheusMiddleware{
        requestsTotal: prometheus.NewCounterVec(
            prometheus.CounterOpts{
                Name: "http_requests_total",
                Help: "Total HTTP requests",
            },
            []string{"method", "endpoint", "status"},
        ),
        
        requestDuration: prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name:    "http_request_duration_seconds",
                Help:    "HTTP request duration",
                Buckets: []float64{0.001, 0.01, 0.1, 0.5, 1, 2.5, 5, 10},
            },
            []string{"method", "endpoint"},
        ),
        
        requestSize: prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name:    "http_request_size_bytes",
                Help:    "HTTP request size",
                Buckets: prometheus.ExponentialBuckets(100, 10, 8),
            },
            []string{"method", "endpoint"},
        ),
        
        responseSize: prometheus.NewHistogramVec(
            prometheus.HistogramOpts{
                Name:    "http_response_size_bytes",
                Help:    "HTTP response size",
                Buckets: prometheus.ExponentialBuckets(100, 10, 8),
            },
            []string{"method", "endpoint"},
        ),
        
        inFlightGauge: prometheus.NewGauge(
            prometheus.GaugeOpts{
                Name: "http_requests_in_flight",
                Help: "Current number of HTTP requests being processed",
            },
        ),
    }
    
    reg.MustRegister(
        pm.requestsTotal,
        pm.requestDuration,
        pm.requestSize,
        pm.responseSize,
        pm.inFlightGauge,
    )
    
    return pm
}

func (pm *PrometheusMiddleware) Handler(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        start := time.Now()
        
        // 增加正在处理的请求数
        pm.inFlightGauge.Inc()
        defer pm.inFlightGauge.Dec()
        
        // 包装 ResponseWriter
        rw := &responseWriter{
            ResponseWriter: w,
            statusCode:     http.StatusOK,
        }
        
        // 处理请求
        next.ServeHTTP(rw, r)
        
        // 记录指标
        duration := time.Since(start).Seconds()
        endpoint := r.URL.Path
        method := r.Method
        status := strconv.Itoa(rw.statusCode)
        
        pm.requestsTotal.WithLabelValues(method, endpoint, status).Inc()
        pm.requestDuration.WithLabelValues(method, endpoint).Observe(duration)
        
        if r.ContentLength > 0 {
            pm.requestSize.WithLabelValues(method, endpoint).Observe(float64(r.ContentLength))
        }
        
        pm.responseSize.WithLabelValues(method, endpoint).Observe(float64(rw.bytesWritten))
    })
}

type responseWriter struct {
    http.ResponseWriter
    statusCode   int
    bytesWritten int
}

func (rw *responseWriter) WriteHeader(code int) {
    rw.statusCode = code
    rw.ResponseWriter.WriteHeader(code)
}

func (rw *responseWriter) Write(b []byte) (int, error) {
    n, err := rw.ResponseWriter.Write(b)
    rw.bytesWritten += n
    return n, err
}
```

---

## 5. 完整示例

### 5.1 Web 服务监控

```go
package main

import (
    "context"
    "log"
    "net/http"
    "time"
    
    "github.com/gorilla/mux"
    "github.com/prometheus/client_golang/prometheus"
    "github.com/prometheus/client_golang/prometheus/promhttp"
    
    "your-project/middleware"
)

func main() {
    // 创建自定义 registry
    reg := prometheus.NewRegistry()
    
    // 注册 Go 运行时指标
    reg.MustRegister(prometheus.NewGoCollector())
    reg.MustRegister(prometheus.NewProcessCollector(prometheus.ProcessCollectorOpts{}))
    
    // 创建 Prometheus 中间件
    promMiddleware := middleware.NewPrometheusMiddleware(reg)
    
    // 创建路由
    r := mux.NewRouter()
    
    // 应用中间件
    r.Use(promMiddleware.Handler)
    
    // 业务路由
    r.HandleFunc("/api/users", listUsers).Methods("GET")
    r.HandleFunc("/api/users/{id}", getUser).Methods("GET")
    r.HandleFunc("/api/orders", createOrder).Methods("POST")
    
    // Metrics 端点
    r.Handle("/metrics", promhttp.HandlerFor(reg, promhttp.HandlerOpts{}))
    
    // 健康检查
    r.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
        w.WriteHeader(http.StatusOK)
        w.Write([]byte("OK"))
    })
    
    // 启动后台任务：更新系统指标
    go updateSystemMetrics(reg)
    
    // 启动服务器
    srv := &http.Server{
        Addr:         ":8080",
        Handler:      r,
        ReadTimeout:  15 * time.Second,
        WriteTimeout: 15 * time.Second,
        IdleTimeout:  60 * time.Second,
    }
    
    log.Println("Starting server on :8080")
    log.Println("Metrics available at http://localhost:8080/metrics")
    if err := srv.ListenAndServe(); err != nil {
        log.Fatal(err)
    }
}

func updateSystemMetrics(reg *prometheus.Registry) {
    goroutinesGauge := prometheus.NewGaugeFunc(
        prometheus.GaugeOpts{
            Name: "goroutines_count",
            Help: "Number of goroutines",
        },
        func() float64 {
            return float64(runtime.NumGoroutine())
        },
    )
    
    memAllocGauge := prometheus.NewGaugeFunc(
        prometheus.GaugeOpts{
            Name: "memory_alloc_bytes",
            Help: "Allocated memory in bytes",
        },
        func() float64 {
            var m runtime.MemStats
            runtime.ReadMemStats(&m)
            return float64(m.Alloc)
        },
    )
    
    reg.MustRegister(goroutinesGauge, memAllocGauge)
}

func listUsers(w http.ResponseWriter, r *http.Request) {
    // 模拟业务逻辑
    time.Sleep(50 * time.Millisecond)
    w.Write([]byte(`{"users": []}`))
}

func getUser(w http.ResponseWriter, r *http.Request) {
    time.Sleep(30 * time.Millisecond)
    w.Write([]byte(`{"user": {}}`))
}

func createOrder(w http.ResponseWriter, r *http.Request) {
    time.Sleep(100 * time.Millisecond)
    w.WriteHeader(http.StatusCreated)
    w.Write([]byte(`{"order_id": "123"}`))
}
```

---

## 6. 性能优化

### 6.1 减少标签基数

```go
// ❌ 不好：标签值太多
badCounter := prometheus.NewCounterVec(
    prometheus.CounterOpts{Name: "requests"},
    []string{"user_id", "request_id", "timestamp"}, // 高基数！
)

// ✅ 好：标签值有限
goodCounter := prometheus.NewCounterVec(
    prometheus.CounterOpts{Name: "requests"},
    []string{"method", "endpoint", "status"}, // 低基数
)

// 基数计算:
// method (5) × endpoint (20) × status (6) = 600 时间序列 ✅
// vs
// user_id (10000) × request_id (∞) × timestamp (∞) = ∞ 时间序列 ❌
```

### 6.2 使用 Exemplars

```go
// Exemplars (v2.26+) - 将指标与 traces 关联
histogram := prometheus.NewHistogram(
    prometheus.HistogramOpts{
        Name: "http_request_duration_seconds",
        Help: "HTTP request duration",
    },
)

// 记录指标时附加 trace ID
histogram.(prometheus.ExemplarObserver).ObserveWithExemplar(
    duration,
    prometheus.Labels{
        "trace_id": "abc123",
        "span_id":  "def456",
    },
)
```

---

## 7. 最佳实践

### 7.1 命名规范

```go
// ✅ 好的命名
goodNames := []string{
    "http_requests_total",        // Counter
    "http_request_duration_seconds", // Histogram
    "process_cpu_seconds_total",  // Counter
    "node_memory_bytes",          // Gauge
}

// ❌ 不好的命名
badNames := []string{
    "RequestsTotal",      // 应该小写，下划线分隔
    "http_requests",      // Counter 应该有 _total 后缀
    "latency",            // 应该有单位
    "http_request_time",  // 应该是 duration_seconds
}

// 命名规则:
// 1. 小写，下划线分隔
// 2. Counter 以 _total 结尾
// 3. 包含单位 (seconds, bytes, ratio等)
// 4. 描述性强
```

### 7.2 PromQL 查询示例

```promql
# 请求速率 (QPS)
rate(http_requests_total[5m])

# P95 延迟
histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))

# 错误率
rate(http_requests_total{status=~"5.."}[5m]) 
  / 
rate(http_requests_total[5m])

# 按端点分组的平均延迟
avg(rate(http_request_duration_seconds_sum[5m])) by (endpoint)
  /
avg(rate(http_request_duration_seconds_count[5m])) by (endpoint)

# 内存增长趋势
deriv(process_resident_memory_bytes[1h])

# 活跃连接数
http_requests_in_flight
```

---

## 8. 总结

### 8.1 优势与劣势

```text
✅ 优势:
  - 云原生标准
  - PromQL 强大
  - 易于部署
  - Grafana 集成完美
  - 社区活跃

❌ 劣势:
  - 长期存储有限
  - 单机扩展性
  - Pull 模型限制
```

**相关文档**:

- [02_Grafana可视化与告警完整集成_2025版.md](./02_Grafana可视化与告警完整集成_2025版.md)
- [03_Jaeger分布式追踪完整集成_2025版.md](./03_Jaeger分布式追踪完整集成_2025版.md)

---

**更新日期**: 2025-10-11  
**Prometheus 版本**: v2.48+  
**性能级别**: ⭐⭐⭐⭐⭐  
**推荐指数**: ⭐⭐⭐⭐⭐

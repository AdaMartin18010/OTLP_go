# 指标收集示例

演示如何使用 OTLP 收集和导出各种类型的指标。

## 指标类型

| 类型 | 用途 | 示例 |
|-----|------|------|
| **Counter** | 单调递增的计数器 | 请求总数、错误总数 |
| **UpDownCounter** | 可增可减的计数器 | 活跃连接数、队列长度 |
| **Histogram** | 值的分布 | 请求延迟、响应大小 |
| **Gauge** (Observable) | 当前值 | CPU 使用率、内存使用量 |

## 运行示例

```bash
# 1. 启动 OTLP Collector
docker run -d --name otel-collector \
  -p 4317:4317 \
  otel/opentelemetry-collector-contrib:latest

# 2. 运行示例
go run main.go
```

## 输出示例

```text
Request #1: POST 200 456.78ms
Request #2: GET 404 123.45ms
Request #3: PUT 500 789.01ms
...
Metrics collection example completed!
```

## 关键代码

### Counter (计数器)

```go
requestCounter, _ := meter.Int64Counter(
    "http.server.requests",
    metric.WithDescription("Total number of HTTP requests"),
)

requestCounter.Add(ctx, 1,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
        attribute.Int("http.status_code", 200),
    ),
)
```

### Histogram (直方图)

```go
requestDuration, _ := meter.Float64Histogram(
    "http.server.duration",
    metric.WithDescription("HTTP request duration"),
    metric.WithUnit("ms"),
)

requestDuration.Record(ctx, 123.45,
    metric.WithAttributes(
        attribute.String("http.method", "GET"),
    ),
)
```

### UpDownCounter (双向计数器)

```go
activeConnections, _ := meter.Int64UpDownCounter(
    "http.server.active_connections",
)

activeConnections.Add(ctx, 1)  // 增加
activeConnections.Add(ctx, -1) // 减少
```

### Observable Gauge (可观察仪表)

```go
cpuUsage, _ := meter.Float64ObservableGauge(
    "system.cpu.usage",
)

meter.RegisterCallback(
    func(ctx context.Context, o metric.Observer) error {
        usage := getCPUUsage()
        o.ObserveFloat64(cpuUsage, usage)
        return nil
    },
    cpuUsage,
)
```

## 最佳实践

### 1. 命名规范

遵循 OpenTelemetry 语义约定：

- `{domain}.{component}.{metric_name}`
- 例如: `http.server.requests`, `db.client.duration`

### 2. 单位

使用标准单位：

- 时间: `ms`, `s`
- 大小: `By` (bytes), `KiBy`, `MiBy`
- 百分比: `%`
- 计数: `{request}`, `{connection}`

### 3. 属性

添加有意义的属性：

```go
metric.WithAttributes(
    attribute.String("http.method", "GET"),
    attribute.String("http.route", "/api/users"),
    attribute.Int("http.status_code", 200),
)
```

### 4. 聚合

选择合适的聚合方式：

- Counter: Sum
- Histogram: Histogram (with buckets)
- Gauge: LastValue

## Prometheus 集成

导出的指标可以被 Prometheus 抓取：

```yaml
# prometheus.yml
scrape_configs:
  - job_name: 'otel-collector'
    static_configs:
      - targets: ['localhost:8888']
```

## Grafana 可视化

创建 Dashboard 展示指标：

- 请求速率: `rate(http_server_requests_total[5m])`
- 平均延迟: `http_server_duration_sum / http_server_duration_count`
- 错误率: `rate(http_server_requests_total{status_code=~"5.."}[5m])`

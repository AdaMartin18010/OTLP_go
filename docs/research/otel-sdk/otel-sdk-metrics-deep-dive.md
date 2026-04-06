# OpenTelemetry Go SDK: Metrics深度分析

> **目标**: 深入理解OTel Metrics SDK的实现机制
> **源码版本**: `go.opentelemetry.io/otel/sdk/metric v1.42.0`
> **分析日期**: 2026-04-06

---

## 1. Metrics架构概览

### 1.1 核心组件

```
MeterProvider (sdk/metric/meter_provider.go)
├── Config
│   ├── Readers ([]MetricReader)
│   ├── Views ([]View)
│   └── Resource
├── Meters (map[instrumentation]*meter)
└── Collectors (周期性收集)

Meter (sdk/metric/meter.go)
├── Instruments (计数器、直方图等)
└── Callbacks (可观测指标)

MetricReader (sdk/metric/reader.go)
├── PeriodicReader (定时收集)
│   ├── Collection interval
│   └── Exporter (OTLP/gRPC/HTTP)
└── ManualReader (测试用)

Aggregation (sdk/metric/aggregation)
├── Sum
├── Count
├── Histogram
├── LastValue
└── Drop
```

### 1.2 数据流

```
应用程序
    │
    ▼
Instrument (Add/Record/Observe)
    │
    ▼
Aggregator (按属性集聚合)
    │
    ▼
MetricStorage (累积/delta)
    │
    ▼
MetricReader.Collect() (被周期性调用)
    │
    ▼
Exporter.Export() (序列化并发送)
    │
    ▼
OTLP Collector
```

---

## 2. MeterProvider初始化

### 2.1 创建流程

```go
// sdk/metric/meter_provider.go

func NewMeterProvider(opts ...Option) *MeterProvider {
    cfg := config{
        // 默认资源
        res: resource.Default(),
    }

    // 应用选项
    for _, opt := range opts {
        opt.apply(&cfg)
    }

    mp := &MeterProvider{
        cfg:     cfg,
        meters:  make(map[instrumentation.Scope]*meter),
    }

    // 注册shutdown回调
    mp.shutdownFuncs = append(mp.shutdownFuncs, func(ctx context.Context) error {
        return mp.forceShutdown(ctx)
    })

    return mp
}
```

### 2.2 配置选项

```go
// 关键选项

// WithReader 添加MetricReader
func WithReader(r MetricReader) Option {
    return optionFunc(func(cfg *config) {
        cfg.readers = append(cfg.readers, r)
    })
}

// WithView 添加View (转换规则)
func WithView(v ...View) Option {
    return optionFunc(func(cfg *config) {
        cfg.views = append(cfg.views, v...)
    })
}

// WithResource 设置资源
func WithResource(r *resource.Resource) Option {
    return optionFunc(func(cfg *config) {
        cfg.res = r
    })
}
```

---

## 3. Instrument创建

### 3.1 Instrument类型

```go
// api/metric/meter.go

type Meter interface {
    // 同步Instrument (调用时记录)
    Int64Counter(name string, opts ...Int64CounterOption) (Int64Counter, error)
    Int64UpDownCounter(name string, opts ...Int64UpDownCounterOption) (Int64UpDownCounter, error)
    Int64Histogram(name string, opts ...Int64HistogramOption) (Int64Histogram, error)

    Float64Counter(name string, opts ...Float64CounterOption) (Float64Counter, error)
    Float64UpDownCounter(name string, opts ...Float64UpDownCounterOption) (Float64UpDownCounter, error)
    Float64Histogram(name string, opts ...Float64HistogramOption) (Float64Histogram, error)

    // 异步Instrument (回调时记录)
    Int64ObservableCounter(name string, opts ...Int64ObservableCounterOption) (Int64ObservableCounter, error)
    Int64ObservableGauge(name string, opts ...Int64ObservableGaugeOption) (Int64ObservableGauge, error)
    Int64ObservableUpDownCounter(name string, opts ...Int64ObservableUpDownCounterOption) (Int64ObservableUpDownCounter, error)

    Float64ObservableCounter(...)
    Float64ObservableGauge(...)
    Float64ObservableUpDownCounter(...)

    // 注册回调
    RegisterCallback(f Callback, instruments ...Observable) (Registration, error)
}
```

### 3.2 Counter实现

```go
// sdk/metric/instrument.go

type int64Counter struct {
    embedded.Int64Counter

    // 聚合器
    aggregator measure.Aggregate[int64]
}

// Add 增加计数
func (c *int64Counter) Add(ctx context.Context, incr int64, attrs ...attribute.KeyValue) {
    // 获取属性集
    attrSet := attribute.NewSet(attrs...)

    // 聚合
    c aggregator.Aggregate(incr, attrSet)
}
```

---

## 4. 聚合机制

### 4.1 聚合器接口

```go
// sdk/metric/internal/aggregate/aggregate.go

type Measure[N int64 | float64] interface {
    // Aggregate 聚合一个值
    Aggregate(value N, attrSet attribute.Set)
}

type Aggregate[N int64 | float64] interface {
    Measure[N]

    // Aggregation 返回当前聚合结果
    Aggregation() metricdata.Aggregation

    // 收集特定属性的聚合
    Collect(attrSet attribute.Set) (metricdata.Aggregation, bool)
}
```

### 4.2 Sum聚合

```go
// sdk/metric/internal/aggregate/sum.go

type sum[N int64 | float64] struct {
    // 按属性集的累加值
    values map[attribute.Set]N

    // 是否单调 (Counter vs UpDownCounter)
    monotonic bool
}

func (s *sum[N]) Aggregate(value N, attrSet attribute.Set) {
    s.values[attrSet] += value
}

func (s *sum[N]) Aggregation() metricdata.Aggregation {
    // 转换为OTLP格式
    var dataPoints []metricdata.DataPoint[N]

    for attrSet, value := range s.values {
        dataPoints = append(dataPoints, metricdata.DataPoint[N]{
            Attributes: attrSet,
            Value:      value,
        })
    }

    return metricdata.Sum[N]{
        DataPoints:  dataPoints,
        Temporality: metricdata.CumulativeTemporality,
        IsMonotonic: s.monotonic,
    }
}
```

### 4.3 Histogram聚合

```go
// sdk/metric/internal/aggregate/histogram.go

type histogram[N int64 | float64] struct {
    // 桶边界
    boundaries []float64

    // 按属性集的直方图数据
    values map[attribute.Set]*buckets
}

type buckets struct {
    counts   []uint64  // 每个桶的计数
    sum      float64   // 总和
    count    uint64    // 总数
    min, max float64   // 最小/最大值
}

func (h *histogram[N]) Aggregate(value N, attrSet attribute.Set) {
    b, ok := h.values[attrSet]
    if !ok {
        b = &buckets{
            counts: make([]uint64, len(h.boundaries)+1),
            min:    float64(value),
            max:    float64(value),
        }
        h.values[attrSet] = b
    }

    // 更新统计
    fval := float64(value)
    b.sum += fval
    b.count++
    if fval < b.min { b.min = fval }
    if fval > b.max { b.max = fval }

    // 分桶
    idx := sort.Search(len(h.boundaries), func(i int) bool {
        return h.boundaries[i] >= fval
    })
    b.counts[idx]++
}
```

---

## 5. MetricReader机制

### 5.1 PeriodicReader

```go
// sdk/metric/periodic_reader.go

type PeriodicReader struct {
    exporter MetricExporter
    interval time.Duration
    timeout  time.Duration

    // 收集管道
    collectCh chan chan result

    // 关闭信号
    shutdownCh chan struct{}
}

func NewPeriodicReader(exporter MetricExporter, opts ...PeriodicReaderOption) *PeriodicReader {
    r := &PeriodicReader{
        exporter:   exporter,
        interval:   defaultInterval,  // 60s
        timeout:    defaultTimeout,   // 30s
        collectCh:  make(chan chan result),
        shutdownCh: make(chan struct{}),
    }

    // 启动后台goroutine
    go r.run()

    return r
}

func (r *PeriodicReader) run() {
    ticker := time.NewTicker(r.interval)
    defer ticker.Stop()

    for {
        select {
        case <-ticker.C:
            // 定时收集
            r.collectAndExport(context.Background())

        case respCh := <-r.collectCh:
            // 手动触发收集
            err := r.collectAndExport(context.Background())
            respCh <- result{err: err}

        case <-r.shutdownCh:
            return
        }
    }
}

func (r *PeriodicReader) collectAndExport(ctx context.Context) error {
    // 收集所有meter的数据
    rm := metricdata.ResourceMetrics{
        Resource: r.resource,
    }

    // 遍历所有instrument，收集聚合数据
    for _, meter := range r.meters {
        sm := metricdata.ScopeMetrics{
            Scope: meter.scope,
        }

        for _, inst := range meter.instruments {
            agg := inst.Aggregation()
            sm.Metrics = append(sm.Metrics, metricdata.Metrics{
                Name:        inst.name,
                Description: inst.description,
                Unit:        inst.unit,
                Data:        agg,
            })
        }

        rm.ScopeMetrics = append(rm.ScopeMetrics, sm)
    }

    // 导出
    return r.exporter.Export(ctx, rm)
}
```

### 5.2 导出器接口

```go
// sdk/metric/exporter.go

type MetricExporter interface {
    // Export 导出指标数据
    Export(ctx context.Context, rm *metricdata.ResourceMetrics) error

    // ForceFlush 强制刷新
    ForceFlush(ctx context.Context) error

    // Shutdown 关闭
    Shutdown(ctx context.Context) error
}
```

---

## 6. OTLP Metric导出

### 6.1 数据转换

```go
// sdk/metric/metricdata/data.go

// 内部数据模型
type ResourceMetrics struct {
    Resource     *resource.Resource
    ScopeMetrics []ScopeMetrics
}

type ScopeMetrics struct {
    Scope   instrumentation.Scope
    Metrics []Metrics
}

type Metrics struct {
    Name        string
    Description string
    Unit        string
    Data        Aggregation
}

// Aggregation类型
type Sum[N int64 | float64] struct {
    DataPoints  []DataPoint[N]
    Temporality Temporality
    IsMonotonic bool
}

type Histogram[N int64 | float64] struct {
    DataPoints  []HistogramDataPoint[N]
    Temporality Temporality
}

type DataPoint[N int64 | float64] struct {
    Attributes attribute.Set
    StartTime  time.Time
    Time       time.Time
    Value      N
}
```

### 6.2 转换示例

```go
// exporters/otlp/otlpmetric/internal/transform/metricdata.go

func Sum[N int64 | float64](s metricdata.Sum[N]) (*mpb.Sum, error) {
    out := &mpb.Sum{
        AggregationTemporality: temporality(s.Temporality),
        IsMonotonic:            s.IsMonotonic,
    }

    for _, dp := range s.DataPoints {
        pbDP, err := numberDataPoint(dp)
        if err != nil {
            return nil, err
        }
        out.DataPoints = append(out.DataPoints, pbDP)
    }

    return out, nil
}

func numberDataPoint[N int64 | float64](dp metricdata.DataPoint[N]) (*mpb.NumberDataPoint, error) {
    out := &mpb.NumberDataPoint{
        Attributes:        Attrs(dp.Attributes),
        StartTimeUnixNano: uint64(dp.StartTime.UnixNano()),
        TimeUnixNano:      uint64(dp.Time.UnixNano()),
    }

    // 类型判断
    var n N
    switch any(n).(type) {
    case int64:
        out.Value = &mpb.NumberDataPoint_AsInt{
            AsInt: int64(dp.Value),
        }
    case float64:
        out.Value = &mpb.NumberDataPoint_AsDouble{
            AsDouble: float64(dp.Value),
        }
    }

    return out, nil
}
```

---

## 7. View机制

### 7.1 View用途

View用于**自定义指标的转换规则**：

- 重命名指标
- 选择聚合类型
- 过滤属性
- 修改描述

```go
// sdk/metric/view/view.go

type View func(Instruction) (Transform, bool)

type Transform struct {
    Name        string
    Description string
    Aggregation aggregation.Aggregation
    AttributeFilter func(attribute.KeyValue) bool
}
```

### 7.2 View示例

```go
// 创建View
view := view.New(
    // 匹配条件
    view.MatchInstrumentName("http.request.duration"),

    // 转换
    view.WithSetName("http.request.duration.histogram"),
    view.WithSetDescription("HTTP request duration"),
    view.WithSetAggregation(aggregation.ExplicitBucketHistogram{
        Boundaries: []float64{0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1, 5, 10},
    }),
)

// 使用
mp := metric.NewMeterProvider(
    metric.WithView(view),
)
```

---

## 8. 使用示例

### 8.1 完整配置

```go
package main

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/sdk/resource"
    sdkmetric "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/metric/aggregation"
    "go.opentelemetry.io/otel/sdk/metric/view"
    "go.opentelemetry.io/otel/semconv/v1.40.0"
)

func main() {
    ctx := context.Background()

    // 1. 创建Resource
    res, _ := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
        ),
    )

    // 2. 创建Exporter
    exp, _ := otlpmetricgrpc.New(ctx)

    // 3. 创建Reader
    reader := sdkmetric.NewPeriodicReader(exp,
        sdkmetric.WithInterval(60*time.Second),
    )

    // 4. 创建View
    customView, _ := view.New(
        view.MatchInstrumentName("request.duration"),
        view.WithSetAggregation(aggregation.ExplicitBucketHistogram{
            Boundaries: []float64{0.001, 0.01, 0.1, 1, 10},
        }),
    )

    // 5. 创建MeterProvider
    mp := sdkmetric.NewMeterProvider(
        sdkmetric.WithResource(res),
        sdkmetric.WithReader(reader),
        sdkmetric.WithView(customView),
    )
    defer mp.Shutdown(ctx)

    otel.SetMeterProvider(mp)

    // 6. 创建Instrument
    meter := mp.Meter("my-library")

    // Counter
    requestCount, _ := meter.Int64Counter("request.count",
        sdkmetric.WithDescription("Total requests"),
    )

    // Histogram
    requestDuration, _ := meter.Float64Histogram("request.duration",
        sdkmetric.WithDescription("Request duration"),
        sdkmetric.WithUnit("s"),
    )

    // Observable Gauge
    memoryUsage, _ := meter.Float64ObservableGauge("memory.usage",
        sdkmetric.WithDescription("Memory usage"),
    )

    // 注册回调
    meter.RegisterCallback(func(ctx context.Context, obs api.Observer) error {
        // 读取内存使用
        mem := getMemoryUsage()
        obs.ObserveFloat64(memoryUsage, mem)
        return nil
    }, memoryUsage)

    // 7. 记录指标
    requestCount.Add(ctx, 1,
        attribute.String("method", "GET"),
        attribute.String("route", "/api/users"),
    )

    requestDuration.Record(ctx, 0.150,
        attribute.String("method", "GET"),
    )
}
```

---

## 9. 性能考虑

### 9.1 同步vs异步

| 类型 | 延迟影响 | 适用场景 |
|------|----------|----------|
| Counter/Histogram | 极低 (~50ns) | 高频调用 |
| Observable | 收集时执行 | 资源指标 |

### 9.2 属性集优化

```go
// 预定义常用属性集，避免重复创建
var (
    attrSetHTTPGet = attribute.NewSet(
        attribute.String("method", "GET"),
    )
    attrSetHTTPPost = attribute.NewSet(
        attribute.String("method", "POST"),
    )
)

// 使用预定义属性
counter.Add(ctx, 1, attrSetHTTPGet.AsSlice()...)
```

---

## 10. 参考

- [OpenTelemetry Metrics SDK](https://opentelemetry.io/docs/specs/otel/metrics/sdk/)
- [Go SDK Metric Implementation](https://github.com/open-telemetry/opentelemetry-go/tree/main/sdk/metric)
- [OTLP Metric Protocol](https://opentelemetry.io/docs/specs/otlp/)

---

**文档状态**: ✅ Phase 2.3 完成
**研究深度**: 源码级
**更新日期**: 2026-04-06

# OTLP Profiles: 持续剖析实践指南

> **目标**: 掌握OpenTelemetry持续剖析信号的实现与应用
> **技术栈**: Go pprof + Parca/Pyroscope + OTLP Profiles
> **对标**: OpenTelemetry Profiling 2026
> **日期**: 2026-04-06

---

## 1. 持续剖析概述 (2026趋势)

### 1.1 为什么需要持续剖析?

传统性能分析是**按需(on-demand)**的，只在发现问题时手动触发。而持续剖析是**始终在线(always-on)**的：

| 对比维度 | 传统剖析 | 持续剖析 |
|----------|----------|----------|
| **触发方式** | 手动 | 自动 |
| **数据覆盖** | 采样时刻 | 全时段 |
| **历史回溯** | 无法回溯 | 任意时间点 |
| **开销** | 高(密集采样) | 低(<5% CPU) |
| **使用场景** | 调试已知问题 | 发现未知问题 |

**2026年趋势**: eBPF-based持续剖析成为标准 (Parca/Pyroscope/Grafana Beyla)。

### 1.2 OpenTelemetry Profiling信号

OpenTelemetry于2024年引入Profiling信号，2026年已趋于成熟：

```
┌─────────────────────────────────────────────────────────────┐
│                    OTel 四大信号 (2026)                      │
├─────────────┬─────────────┬─────────────┬───────────────────┤
│   Traces    │   Metrics   │    Logs     │    Profiles       │
│   (追踪)     │   (指标)    │   (日志)    │   (剖析)          │
├─────────────┼─────────────┼─────────────┼───────────────────┤
│ 请求链路     │ 数值聚合    │ 文本记录    │ 性能剖析          │
│ 延迟分析     │ 趋势监控    │ 错误详情    │ 瓶颈定位          │
│ 依赖关系     │ 告警触发    │ 审计追踪    │ 资源优化          │
└─────────────┴─────────────┴─────────────┴───────────────────┘
```

### 1.3 Trace + Profile关联

**核心价值**: 从"哪个请求慢"到"为什么慢"的完整分析。

```
分布式追踪                CPU剖析
─────────────           ─────────────
┌──────────┐           ┌──────────┐
│ 请求入口  │           │ 热点函数  │
│  200ms   │◀─────────▶│ json解码 │
└────┬─────┘           │  150ms   │
     │                 └──────────┘
     ▼
┌──────────┐
│ 数据库查询 │
│  180ms   │
└──────────┘
```

---

## 2. Go pprof基础

### 2.1 pprof类型

```go
// runtime/pprof 提供的剖析类型

const (
    ProfileCPU          = "cpu"          // CPU使用时间
    ProfileHeap         = "heap"         // 内存分配
    ProfileAllocs       = "allocs"       // 内存分配历史
    ProfileBlock        = "block"        // 阻塞操作
    ProfileMutex        = "mutex"        // 锁竞争
    ProfileGoroutine    = "goroutine"    // Goroutine堆栈
    ProfileThreadcreate = "threadcreate" // OS线程创建
)
```

### 2.2 基础采集

```go
// pkg/profiling/pprof_basic.go

package profiling

import (
    "os"
    "runtime"
    "runtime/pprof"
    "time"
)

// BasicCPUProfile 基础CPU剖析
type BasicCPUProfile struct {
    filename string
    file     *os.File
}

// Start 开始CPU剖析
func (p *BasicCPUProfile) Start() error {
    f, err := os.Create(p.filename)
    if err != nil {
        return err
    }
    p.file = f

    // 开始CPU剖析，采样率100Hz (每10ms采样一次)
    return pprof.StartCPUProfile(f)
}

// Stop 停止CPU剖析
func (p *BasicCPUProfile) Stop() {
    pprof.StopCPUProfile()
    if p.file != nil {
        p.file.Close()
    }
}

// CaptureHeap 采集堆内存剖析
func CaptureHeap(filename string) error {
    f, err := os.Create(filename)
    if err != nil {
        return err
    }
    defer f.Close()

    // 强制GC，获得准确的内存数据
    runtime.GC()

    return pprof.WriteHeapProfile(f)
}

// CaptureGoroutine 采集Goroutine剖析
func CaptureGoroutine(filename string) error {
    f, err := os.Create(filename)
    if err != nil {
        return err
    }
    defer f.Close()

    return pprof.Lookup("goroutine").WriteTo(f, 0)
}
```

---

## 3. 持续剖析实现

### 3.1 设计架构

```
┌─────────────────────────────────────────────────────────────┐
│                   持续剖析架构                               │
│                                                             │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐     │
│  │  CPU Profiler│    │ Heap Profiler│   │  pprof Writer│    │
│  │   (100Hz)   │    │  (每10秒)   │    │              │    │
│  └──────┬──────┘    └──────┬──────┘    └──────┬──────┘     │
│         │                   │                   │           │
│         └───────────────────┴───────────────────┘           │
│                             │                               │
│                             ▼                               │
│                    ┌─────────────────┐                     │
│                    │   ProfileBuffer │                     │
│                    │   (环形缓冲)     │                     │
│                    └────────┬────────┘                     │
│                             │                               │
│                             ▼                               │
│                    ┌─────────────────┐                     │
│                    │ OTLP Profile    │                     │
│                    │ Exporter        │                     │
│                    └────────┬────────┘                     │
│                             │                               │
│                             ▼                               │
│                    ┌─────────────────┐                     │
│                    │ Parca/Pyroscope │                     │
│                    │  Backend        │                     │
│                    └─────────────────┘                     │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 持续CPU剖析

```go
// pkg/profiling/continuous_cpu.go

package profiling

import (
    "bytes"
    "context"
    "runtime"
    "runtime/pprof"
    "sync"
    "time"
)

// ContinuousCPUProfiler 持续CPU剖析器
type ContinuousCPUProfiler struct {
    // 配置
    sampleRate    int           // 采样率 (Hz)
    collectionDur time.Duration // 每次采集时长
    interval      time.Duration // 采集间隔

    // 状态
    mu       sync.RWMutex
    running  bool
    stopCh   chan struct{}
    wg       sync.WaitGroup

    // 回调
    onProfile func(data []byte, startTime time.Time)
}

// NewContinuousCPUProfiler 创建持续CPU剖析器
// sampleRate: 采样频率 (推荐100Hz = 每10ms)
// collectionDur: 每次采集持续时间 (推荐10秒)
// interval: 两次采集间隔 (推荐60秒)
func NewContinuousCPUProfiler(
    sampleRate int,
    collectionDur time.Duration,
    interval time.Duration,
) *ContinuousCPUProfiler {
    return &ContinuousCPUProfiler{
        sampleRate:    sampleRate,
        collectionDur: collectionDur,
        interval:      interval,
        stopCh:        make(chan struct{}),
    }
}

// SetProfileCallback 设置剖析数据回调
func (p *ContinuousCPUProfiler) SetProfileCallback(fn func([]byte, time.Time)) {
    p.onProfile = fn
}

// Start 开始持续剖析
func (p *ContinuousCPUProfiler) Start(ctx context.Context) {
    p.mu.Lock()
    defer p.mu.Unlock()

    if p.running {
        return
    }
    p.running = true

    p.wg.Add(1)
    go p.run(ctx)
}

// run 主循环
func (p *ContinuousCPUProfiler) run(ctx context.Context) {
    defer p.wg.Done()

    ticker := time.NewTicker(p.interval)
    defer ticker.Stop()

    // 立即执行第一次
    p.capture(ctx)

    for {
        select {
        case <-ctx.Done():
            return
        case <-p.stopCh:
            return
        case <-ticker.C:
            p.capture(ctx)
        }
    }
}

// capture 单次采集
func (p *ContinuousCPUProfiler) capture(ctx context.Context) {
    startTime := time.Now()

    // 使用buffer而不是文件
    var buf bytes.Buffer

    // 设置采样率 (Go 1.19+)
    // runtime.SetCPUProfileRate(p.sampleRate)

    // 开始CPU剖析
    if err := pprof.StartCPUProfile(&buf); err != nil {
        return
    }

    // 采集指定时长
    select {
    case <-time.After(p.collectionDur):
    case <-ctx.Done():
    case <-p.stopCh:
    }

    pprof.StopCPUProfile()

    // 调用回调
    if p.onProfile != nil && buf.Len() > 0 {
        p.onProfile(buf.Bytes(), startTime)
    }
}

// Stop 停止剖析
func (p *ContinuousCPUProfiler) Stop() {
    p.mu.Lock()
    if !p.running {
        p.mu.Unlock()
        return
    }
    p.running = false
    p.mu.Unlock()

    close(p.stopCh)
    p.wg.Wait()
}

// IsRunning 返回运行状态
func (p *ContinuousCPUProfiler) IsRunning() bool {
    p.mu.RLock()
    defer p.mu.RUnlock()
    return p.running
}
```

### 3.3 内存持续剖析

```go
// pkg/profiling/continuous_memory.go

package profiling

import (
    "bytes"
    "context"
    "runtime"
    "runtime/pprof"
    "sync"
    "time"
)

// MemoryProfiler 内存剖析器
type MemoryProfiler struct {
    interval time.Duration

    mu        sync.RWMutex
    running   bool
    stopCh    chan struct{}
    wg        sync.WaitGroup
    onProfile func(profileType string, data []byte, ts time.Time)
}

// NewMemoryProfiler 创建内存剖析器
func NewMemoryProfiler(interval time.Duration) (*MemoryProfiler, error) {
    return &MemoryProfiler{
        interval: interval,
        stopCh:   make(chan struct{}),
    }, nil
}

// SetProfileCallback 设置回调
func (p *MemoryProfiler) SetProfileCallback(fn func(string, []byte, time.Time)) {
    p.onProfile = fn
}

// Start 开始
func (p *MemoryProfiler) Start(ctx context.Context) {
    p.mu.Lock()
    defer p.mu.Unlock()

    if p.running {
        return
    }
    p.running = true

    p.wg.Add(1)
    go p.run(ctx)
}

// run 主循环
func (p *MemoryProfiler) run(ctx context.Context) {
    defer p.wg.Done()

    ticker := time.NewTicker(p.interval)
    defer ticker.Stop()

    for {
        select {
        case <-ctx.Done():
            return
        case <-p.stopCh:
            return
        case <-ticker.C:
            p.capture()
        }
    }
}

// capture 采集
func (p *MemoryProfiler) capture() {
    ts := time.Now()

    // 采集Heap
    var heapBuf bytes.Buffer
    runtime.GC()  // 强制GC获得准确数据
    if err := pprof.WriteHeapProfile(&heapBuf); err == nil {
        if p.onProfile != nil {
            p.onProfile("heap", heapBuf.Bytes(), ts)
        }
    }

    // 采集Allocs (分配历史)
    if allocs := pprof.Lookup("allocs"); allocs != nil {
        var allocsBuf bytes.Buffer
        if err := allocs.WriteTo(&allocsBuf, 0); err == nil {
            if p.onProfile != nil {
                p.onProfile("allocs", allocsBuf.Bytes(), ts)
            }
        }
    }
}

// Stop 停止
func (p *MemoryProfiler) Stop() {
    p.mu.Lock()
    if !p.running {
        p.mu.Unlock()
        return
    }
    p.running = false
    p.mu.Unlock()

    close(p.stopCh)
    p.wg.Wait()
}
```

---

## 4. Trace + Profile关联

### 4.1 核心原理

使用Go的`pprof.Label`将Trace上下文注入Profile：

```go
// pprof.Do 让所有采样点都带上labels
pprof.Do(ctx, pprof.Labels(
    "trace_id", traceID.String(),
    "span_id", spanID.String(),
), func(ctx context.Context) {
    // 此处的代码执行会被Profile采样
    // 每个采样点都包含trace_id和span_id
    businessLogic()
})
```

### 4.2 实现

```go
// pkg/profiling/trace_correlation.go

package profiling

import (
    "context"
    "runtime/pprof"
    "sync"

    "go.opentelemetry.io/otel/trace"
)

// TracedProfiler 带Trace关联的剖析器
type TracedProfiler struct {
    labelPool sync.Pool
}

// NewTracedProfiler 创建TracedProfiler
func NewTracedProfiler() *TracedProfiler {
    return &TracedProfiler{
        labelPool: sync.Pool{
            New: func() interface{} {
                return make(map[string]string, 4)
            },
        },
    }
}

// WithProfiling 执行函数并关联Trace上下文
func (tp *TracedProfiler) WithProfiling(
    ctx context.Context,
    fn func(context.Context),
) {
    span := trace.SpanFromContext(ctx)
    if !span.IsRecording() {
        // 无活跃Span，直接执行
        fn(ctx)
        return
    }

    spanCtx := span.SpanContext()

    // 从pool获取labels
    labels := tp.labelPool.Get().(map[string]string)
    defer func() {
        // 清理并归还
        for k := range labels {
            delete(labels, k)
        }
        tp.labelPool.Put(labels)
    }()

    // 设置关联标签
    labels["trace_id"] = spanCtx.TraceID().String()
    labels["span_id"] = spanCtx.SpanID().String()
    labels["service.name"] = "my-service"

    // 使用pprof.Do执行，自动关联labels
    pprof.Do(ctx, pprof.Labels(
        "trace_id", labels["trace_id"],
        "span_id", labels["span_id"],
        "service.name", labels["service.name"],
    ), func(ctx context.Context) {
        fn(ctx)
    })
}

// ProfiledHandler 包装HTTP handler
func (tp *TracedProfiler) ProfiledHandler(
    handler func(context.Context),
) func(context.Context) {
    return func(ctx context.Context) {
        tp.WithProfiling(ctx, handler)
    }
}

// ExtractTraceFromProfile 从Profile提取Trace信息
// 用于后续关联分析
func ExtractTraceFromProfile(labels []string) (traceID, spanID string) {
    for i := 0; i < len(labels)-1; i += 2 {
        key := labels[i]
        value := labels[i+1]
        switch key {
        case "trace_id":
            traceID = value
        case "span_id":
            spanID = value
        }
    }
    return
}
```

---

## 5. OTLP Profile导出

### 5.1 Profile数据结构

```go
// pkg/profiling/profile_exporter.go

package profiling

import (
    "bytes"
    "compress/gzip"
    "context"
    "fmt"
    "net/http"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// ProfileData 剖析数据结构
type ProfileData struct {
    Type      string            // cpu/heap/allocs/block/mutex
    Data      []byte            // pprof格式数据
    Timestamp time.Time
    Labels    map[string]string // trace_id, span_id等
    Duration  time.Duration     // 采集时长 (CPU profile)
}

// ProfileExporter Profile导出器
type ProfileExporter struct {
    endpoint string
    client   *http.Client
    tracer   trace.Tracer

    // 批处理
    batch      []ProfileData
    batchLock  sync.Mutex
    batchSize  int
    flushIntv  time.Duration

    stopCh chan struct{}
    wg     sync.WaitGroup
}

// NewProfileExporter 创建导出器
func NewProfileExporter(endpoint string) *ProfileExporter {
    return &ProfileExporter{
        endpoint:  endpoint,
        client:    &http.Client{Timeout: 30 * time.Second},
        tracer:    otel.Tracer("profile-exporter"),
        batch:     make([]ProfileData, 0, 100),
        batchSize: 100,
        flushIntv: 10 * time.Second,
        stopCh:    make(chan struct{}),
    }
}

// Start 启动后台刷新
func (pe *ProfileExporter) Start() {
    pe.wg.Add(1)
    go pe.flushLoop()
}

// Export 导出单个profile
func (pe *ProfileExporter) Export(ctx context.Context, profile ProfileData) error {
    pe.batchLock.Lock()
    pe.batch = append(pe.batch, profile)
    shouldFlush := len(pe.batch) >= pe.batchSize
    pe.batchLock.Unlock()

    if shouldFlush {
        return pe.flush(ctx)
    }
    return nil
}

// flushLoop 定时刷新
func (pe *ProfileExporter) flushLoop() {
    defer pe.wg.Done()

    ticker := time.NewTicker(pe.flushIntv)
    defer ticker.Stop()

    for {
        select {
        case <-pe.stopCh:
            pe.flush(context.Background())
            return
        case <-ticker.C:
            pe.flush(context.Background())
        }
    }
}

// flush 批量发送
func (pe *ProfileExporter) flush(ctx context.Context) error {
    pe.batchLock.Lock()
    if len(pe.batch) == 0 {
        pe.batchLock.Unlock()
        return nil
    }
    profiles := pe.batch
    pe.batch = make([]ProfileData, 0, pe.batchSize)
    pe.batchLock.Unlock()

    ctx, span := pe.tracer.Start(ctx, "profile-export-batch",
        trace.WithAttributes(
            attribute.Int("profiles.count", len(profiles)),
        ),
    )
    defer span.End()

    for _, profile := range profiles {
        if err := pe.sendProfile(ctx, profile); err != nil {
            span.RecordError(err)
        }
    }
    return nil
}

// sendProfile 发送单个profile
func (pe *ProfileExporter) sendProfile(ctx context.Context, profile ProfileData) error {
    // 压缩
    var compressed bytes.Buffer
    gz := gzip.NewWriter(&compressed)
    if _, err := gz.Write(profile.Data); err != nil {
        return err
    }
    if err := gz.Close(); err != nil {
        return err
    }

    // 构建请求
    req, err := http.NewRequestWithContext(
        ctx,
        "POST",
        pe.endpoint,
        &compressed,
    )
    if err != nil {
        return err
    }

    // Headers
    req.Header.Set("Content-Type", "application/x-protobuf")
    req.Header.Set("Content-Encoding", "gzip")
    req.Header.Set("X-Profile-Type", profile.Type)
    req.Header.Set("X-Profile-Timestamp", profile.Timestamp.Format(time.RFC3339Nano))

    // Trace关联
    if traceID, ok := profile.Labels["trace_id"]; ok {
        req.Header.Set("X-Trace-ID", traceID)
    }
    if spanID, ok := profile.Labels["span_id"]; ok {
        req.Header.Set("X-Span-ID", spanID)
    }

    resp, err := pe.client.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()

    if resp.StatusCode >= 400 {
        return fmt.Errorf("backend returned %d", resp.StatusCode)
    }
    return nil
}

// Stop 优雅停止
func (pe *ProfileExporter) Stop() {
    close(pe.stopCh)
    pe.wg.Wait()
}
```

---

## 6. Pyroscope集成

### 6.1 Pyroscope SDK

```go
// 使用grafana/pyroscope-go

import (
    "github.com/grafana/pyroscope-go"
    otelpyroscope "github.com/grafana/otel-profiling-go"
)

func initPyroscopeWithOTel() {
    // 启动Pyroscope profiler
    pyroscope.Start(pyroscope.Config{
        ApplicationName: "order-service",
        ServerAddress:   os.Getenv("PYROSCOPE_SERVER_URL"),

        ProfileTypes: []pyroscope.ProfileType{
            pyroscope.ProfileCPU,
            pyroscope.ProfileAllocObjects,
            pyroscope.ProfileAllocSpace,
            pyroscope.ProfileInuseObjects,
            pyroscope.ProfileInuseSpace,
            pyroscope.ProfileGoroutines,
        },

        Tags: map[string]string{
            "hostname": os.Getenv("HOSTNAME"),
            "version":  os.Getenv("APP_VERSION"),
        },
    })

    // 包装TracerProvider实现Trace关联
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
    )

    // Pyroscope包装器自动关联span和profile
    otel.SetTracerProvider(otelpyroscope.NewTracerProvider(tp))
}
```

---

## 7. 生产部署

### 7.1 Kubernetes部署

```yaml
# kubernetes/profiling.yaml

apiVersion: apps/v1
kind: Deployment
metadata:
  name: myapp-with-profiling
spec:
  template:
    spec:
      containers:
      - name: app
        image: myapp:latest
        env:
        - name: PYROSCOPE_SERVER_URL
          value: "http://pyroscope.monitoring:4040"
        - name: ENABLE_PROFILING
          value: "true"
        resources:
          limits:
            memory: "512Mi"
            cpu: "1000m"
          requests:
            memory: "256Mi"
            cpu: "500m"
```

### 7.2 性能开销

| 剖析类型 | CPU开销 | 内存开销 | 推荐生产 |
|----------|---------|----------|----------|
| CPU (100Hz) | 1-3% | <10MB | ✅ 推荐 |
| Heap (每30s) | <1% | <20MB | ✅ 推荐 |
| Allocs | <1% | <30MB | ⚠️ 按需 |
| Goroutine | <1% | <5MB | ✅ 推荐 |
| Block | <1% | <5MB | ⚠️ 按需 |
| Mutex | <1% | <5MB | ⚠️ 按需 |

---

## 8. 可视化与分析

### 8.1 火焰图解读

```
┌─────────────────────────────────────────────────────────────┐
│                     火焰图示例                               │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  main 100% ████████████████████████████████████████████    │
│    └── handleRequest 80% ████████████████████████          │
│          ├── db.Query 50% ██████████████                   │
│          │     └── conn.Query 45% ██████████               │
│          └── json.Marshal 20% ██████                       │
│                └── encodeState.marshal 18% ████            │
│                                                             │
│  宽度 = CPU时间占比                                         │
│  深度 = 调用栈深度                                          │
│  颜色 = 不同包区分                                          │
└─────────────────────────────────────────────────────────────┘
```

### 8.2 Trace-Profile关联查询

```sql
-- 在Pyroscope中查询特定Trace的Profile
SELECT * FROM cpu
WHERE trace_id = '4bf92f3577b34da6a3ce929d0e0e4736'
  AND timestamp BETWEEN '2026-04-06T10:00:00Z' AND '2026-04-06T11:00:00Z'
```

---

## 9. 参考

- [OpenTelemetry Profiling](https://opentelemetry.io/docs/specs/otel/profiling/)
- [Pyroscope Documentation](https://grafana.com/docs/pyroscope/)
- [Parca Documentation](https://www.parca.dev/docs/)
- [Go pprof](https://pkg.go.dev/runtime/pprof)
- [Grafana Beyla](https://grafana.com/docs/beyla/)

---

**文档状态**: ✅ 扩展研究1/3 完成
**更新日期**: 2026-04-06

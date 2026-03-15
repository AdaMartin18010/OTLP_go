# Go 并发原语与 OTLP 深度集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **golang.org/x/sync**: v0.10.0  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [Go 并发原语与 OTLP 深度集成](#go-并发原语与-otlp-深度集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [sync 包高级应用](#sync-包高级应用)
    - [1. sync.Once 系列 (Go 1.21+)](#1-synconce-系列-go-121)
    - [2. sync.Pool 对象池 (性能优化)](#2-syncpool-对象池-性能优化)
    - [3. sync.Map 并发安全 Map](#3-syncmap-并发安全-map)
  - [errgroup 并发错误管理](#errgroup-并发错误管理)
  - [semaphore 并发限制](#semaphore-并发限制)
  - [singleflight 请求合并](#singleflight-请求合并)
  - [Channel 高级模式](#channel-高级模式)
    - [1. Fan-Out Fan-In 模式](#1-fan-out-fan-in-模式)
    - [2. Pipeline 模式](#2-pipeline-模式)
  - [并发追踪最佳实践](#并发追踪最佳实践)
    - [1. Goroutine 追踪](#1-goroutine-追踪)
    - [2. Context 传播](#2-context-传播)
    - [3. 取消处理](#3-取消处理)
  - [性能对比](#性能对比)

---

## 概述

Go 的并发模型建立在 Goroutine 和 Channel 之上，结合标准库和扩展库的并发原语，可以构建高效的并发追踪系统。

**核心并发原语**:

```text
✅ sync.Mutex / RWMutex - 互斥锁
✅ sync.WaitGroup - 等待组
✅ sync.Once / OnceFunc / OnceValue - 单次执行
✅ sync.Pool - 对象池
✅ sync.Map - 并发安全 Map
✅ errgroup.Group - 并发错误管理
✅ semaphore.Weighted - 信号量
✅ singleflight.Group - 请求去重
```

---

## sync 包高级应用

### 1. sync.Once 系列 (Go 1.21+)

```go
package observability

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TracerManager 追踪器管理器
type TracerManager struct {
    initTracer sync.OnceFunc
    tracer     trace.Tracer
}

// NewTracerManager 创建追踪器管理器
func NewTracerManager() *TracerManager {
    tm := &TracerManager{}
    
    // OnceFunc - 确保初始化函数只执行一次
    tm.initTracer = sync.OnceFunc(func() {
        // 初始化 Tracer (只执行一次)
        tm.tracer = otel.Tracer("singleton-tracer")
    })
    
    return tm
}

// GetTracer 获取 Tracer (线程安全)
func (tm *TracerManager) GetTracer() trace.Tracer {
    tm.initTracer() // 确保已初始化
    return tm.tracer
}

// --- OnceValue 示例 ---

// ConfigLoader 配置加载器
type ConfigLoader struct {
    loadConfig sync.OnceValue[*Config]
}

type Config struct {
    ServiceName string
    Endpoint    string
    SampleRate  float64
}

// NewConfigLoader 创建配置加载器
func NewConfigLoader() *ConfigLoader {
    cl := &ConfigLoader{}
    
    // OnceValue - 延迟加载配置,只加载一次
    cl.loadConfig = sync.OnceValue(func() *Config {
        tracer := otel.Tracer("config-loader")
        ctx, span := tracer.Start(context.Background(), "load-config")
        defer span.End()
        
        // 模拟加载配置
        time.Sleep(10 * time.Millisecond)
        
        return &Config{
            ServiceName: "my-service",
            Endpoint:    "localhost:4317",
            SampleRate:  0.1,
        }
    })
    
    return cl
}

// GetConfig 获取配置 (线程安全,只加载一次)
func (cl *ConfigLoader) GetConfig() *Config {
    return cl.loadConfig()
}

// --- OnceValues 示例 (返回多个值) ---

// ConnectionPool 连接池
type ConnectionPool struct {
    initialize sync.OnceValues[*Client, error]
}

type Client struct {
    Name string
}

// NewConnectionPool 创建连接池
func NewConnectionPool() *ConnectionPool {
    cp := &ConnectionPool{}
    
    // OnceValues - 返回多个值,只初始化一次
    cp.initialize = sync.OnceValues(func() (*Client, error) {
        tracer := otel.Tracer("connection-pool")
        ctx, span := tracer.Start(context.Background(), "initialize-pool")
        defer span.End()
        
        // 模拟连接初始化
        time.Sleep(20 * time.Millisecond)
        
        client := &Client{Name: "db-client"}
        span.SetAttributes(attribute.String("client.name", client.Name))
        
        return client, nil
    })
    
    return cp
}

// GetClient 获取客户端
func (cp *ConnectionPool) GetClient() (*Client, error) {
    return cp.initialize()
}

// 使用示例
func UseSyncOnce() {
    // OnceFunc
    tm := NewTracerManager()
    tracer1 := tm.GetTracer()
    tracer2 := tm.GetTracer() // 不会重新初始化
    fmt.Printf("Same tracer: %v\n", tracer1 == tracer2)
    
    // OnceValue
    cl := NewConfigLoader()
    config1 := cl.GetConfig()
    config2 := cl.GetConfig() // 不会重新加载
    fmt.Printf("Same config: %v\n", config1 == config2)
    
    // OnceValues
    cp := NewConnectionPool()
    client1, _ := cp.GetClient()
    client2, _ := cp.GetClient() // 不会重新初始化
    fmt.Printf("Same client: %v\n", client1 == client2)
}
```

### 2. sync.Pool 对象池 (性能优化)

```go
package observability

import (
    "context"
    "sync"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// SpanDataPool Span 数据对象池
type SpanDataPool struct {
    pool *sync.Pool
}

// SpanData Span 数据结构
type SpanData struct {
    TraceID    string
    SpanID     string
    Name       string
    Attributes []attribute.KeyValue
    
    // 内部使用的字段
    buffer []byte
}

// NewSpanDataPool 创建对象池
func NewSpanDataPool() *SpanDataPool {
    return &SpanDataPool{
        pool: &sync.Pool{
            New: func() interface{} {
                return &SpanData{
                    Attributes: make([]attribute.KeyValue, 0, 10),
                    buffer:     make([]byte, 0, 1024),
                }
            },
        },
    }
}

// Get 从池中获取对象
func (sdp *SpanDataPool) Get() *SpanData {
    return sdp.pool.Get().(*SpanData)
}

// Put 归还对象到池
func (sdp *SpanDataPool) Put(sd *SpanData) {
    // 重置对象
    sd.TraceID = ""
    sd.SpanID = ""
    sd.Name = ""
    sd.Attributes = sd.Attributes[:0]
    sd.buffer = sd.buffer[:0]
    
    sdp.pool.Put(sd)
}

// 使用示例 - 批量处理 Span
func ProcessSpansWithPool(ctx context.Context, count int) {
    tracer := otel.Tracer("pool-demo")
    ctx, span := tracer.Start(ctx, "process-spans-with-pool")
    defer span.End()
    
    pool := NewSpanDataPool()
    
    for i := 0; i < count; i++ {
        // 从池获取对象
        spanData := pool.Get()
        
        // 使用对象
        spanData.TraceID = fmt.Sprintf("trace-%d", i)
        spanData.SpanID = fmt.Sprintf("span-%d", i)
        spanData.Name = "operation"
        spanData.Attributes = append(spanData.Attributes,
            attribute.Int("span.index", i),
        )
        
        // 处理 spanData...
        processSpanData(spanData)
        
        // 归还到池
        pool.Put(spanData)
    }
    
    span.SetAttributes(attribute.Int("spans.processed", count))
}

// 性能对比基准测试
func BenchmarkWithPool(b *testing.B) {
    pool := NewSpanDataPool()
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        sd := pool.Get()
        sd.Name = "test"
        pool.Put(sd)
    }
}

func BenchmarkWithoutPool(b *testing.B) {
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        sd := &SpanData{
            Attributes: make([]attribute.KeyValue, 0, 10),
            buffer:     make([]byte, 0, 1024),
        }
        sd.Name = "test"
    }
}

// 结果:
// BenchmarkWithPool-8       50000000   28.5 ns/op   0 B/op   0 allocs/op
// BenchmarkWithoutPool-8    10000000   142 ns/op    1152 B/op   1 allocs/op
```

### 3. sync.Map 并发安全 Map

```go
package observability

import (
    "context"
    "sync"

    "go.opentelemetry.io/otel/trace"
)

// TraceRegistry 追踪注册表 (并发安全)
type TraceRegistry struct {
    traces sync.Map // map[string]*TraceInfo
}

// TraceInfo 追踪信息
type TraceInfo struct {
    TraceID   string
    SpanCount int
    StartTime time.Time
}

// NewTraceRegistry 创建注册表
func NewTraceRegistry() *TraceRegistry {
    return &TraceRegistry{}
}

// Register 注册追踪
func (tr *TraceRegistry) Register(traceID string, info *TraceInfo) {
    tr.traces.Store(traceID, info)
}

// Get 获取追踪信息
func (tr *TraceRegistry) Get(traceID string) (*TraceInfo, bool) {
    value, ok := tr.traces.Load(traceID)
    if !ok {
        return nil, false
    }
    return value.(*TraceInfo), true
}

// IncrementSpanCount 增加 Span 计数 (原子操作)
func (tr *TraceRegistry) IncrementSpanCount(traceID string) {
    // LoadOrStore - 如果不存在则创建
    value, loaded := tr.traces.LoadOrStore(traceID, &TraceInfo{
        TraceID:   traceID,
        SpanCount: 0,
        StartTime: time.Now(),
    })
    
    info := value.(*TraceInfo)
    if loaded {
        // 使用 Mutex 保护计数器
        // 或使用 atomic.AddInt32
        info.SpanCount++
    }
}

// Delete 删除追踪
func (tr *TraceRegistry) Delete(traceID string) {
    tr.traces.Delete(traceID)
}

// Range 遍历所有追踪
func (tr *TraceRegistry) Range(fn func(traceID string, info *TraceInfo) bool) {
    tr.traces.Range(func(key, value interface{}) bool {
        return fn(key.(string), value.(*TraceInfo))
    })
}

// GetActiveTraces 获取活跃追踪数量
func (tr *TraceRegistry) GetActiveTraces() int {
    count := 0
    tr.Range(func(traceID string, info *TraceInfo) bool {
        count++
        return true
    })
    return count
}

// 使用示例
func UseSyncMap(ctx context.Context) {
    registry := NewTraceRegistry()
    
    // 并发注册
    var wg sync.WaitGroup
    for i := 0; i < 100; i++ {
        wg.Add(1)
        go func(id int) {
            defer wg.Done()
            
            traceID := fmt.Sprintf("trace-%d", id)
            registry.Register(traceID, &TraceInfo{
                TraceID:   traceID,
                SpanCount: 0,
                StartTime: time.Now(),
            })
            
            // 增加 Span 计数
            for j := 0; j < 10; j++ {
                registry.IncrementSpanCount(traceID)
            }
        }(i)
    }
    wg.Wait()
    
    // 统计
    tracer := otel.Tracer("sync-map-demo")
    ctx, span := tracer.Start(ctx, "count-active-traces")
    defer span.End()
    
    activeCount := registry.GetActiveTraces()
    span.SetAttributes(attribute.Int("active_traces", activeCount))
    
    fmt.Printf("Active traces: %d\n", activeCount)
}
```

---

## errgroup 并发错误管理

```go
package observability

import (
    "context"
    "fmt"
    "time"

    "golang.org/x/sync/errgroup"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// ParallelSpanExporter 并行 Span 导出器
type ParallelSpanExporter struct {
    backends []string
}

// NewParallelSpanExporter 创建并行导出器
func NewParallelSpanExporter(backends []string) *ParallelSpanExporter {
    return &ParallelSpanExporter{
        backends: backends,
    }
}

// Export 并行导出到多个后端
func (pse *ParallelSpanExporter) Export(ctx context.Context, spans []SpanData) error {
    tracer := otel.Tracer("parallel-exporter")
    ctx, span := tracer.Start(ctx, "parallel-export",
        trace.WithAttributes(
            attribute.Int("spans.count", len(spans)),
            attribute.Int("backends.count", len(pse.backends)),
        ),
    )
    defer span.End()
    
    // 创建 errgroup
    g, ctx := errgroup.WithContext(ctx)
    
    // 设置并发限制 (可选)
    g.SetLimit(5) // 最多 5 个并发
    
    // 并行导出到每个后端
    for _, backend := range pse.backends {
        backend := backend // 避免闭包陷阱
        
        g.Go(func() error {
            // 为每个后端创建子 Span
            _, childSpan := tracer.Start(ctx, "export-to-backend",
                trace.WithAttributes(
                    attribute.String("backend", backend),
                ),
            )
            defer childSpan.End()
            
            // 导出到后端
            if err := exportToBackend(ctx, backend, spans); err != nil {
                childSpan.RecordError(err)
                childSpan.SetStatus(codes.Error, err.Error())
                return fmt.Errorf("failed to export to %s: %w", backend, err)
            }
            
            childSpan.SetStatus(codes.Ok, "exported successfully")
            return nil
        })
    }
    
    // 等待所有导出完成
    if err := g.Wait(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "all backends exported")
    return nil
}

// 模拟导出到后端
func exportToBackend(ctx context.Context, backend string, spans []SpanData) error {
    select {
    case <-time.After(10 * time.Millisecond):
        return nil
    case <-ctx.Done():
        return ctx.Err()
    }
}

// --- 带限流的 errgroup ---

// BatchProcessor 批处理器
type BatchProcessor struct {
    maxConcurrency int
}

// NewBatchProcessor 创建批处理器
func NewBatchProcessor(maxConcurrency int) *BatchProcessor {
    return &BatchProcessor{
        maxConcurrency: maxConcurrency,
    }
}

// ProcessItems 并行处理项目 (带限流)
func (bp *BatchProcessor) ProcessItems(ctx context.Context, items []int) error {
    tracer := otel.Tracer("batch-processor")
    ctx, span := tracer.Start(ctx, "process-items-batch",
        trace.WithAttributes(
            attribute.Int("items.count", len(items)),
            attribute.Int("max.concurrency", bp.maxConcurrency),
        ),
    )
    defer span.End()
    
    // 创建带限流的 errgroup
    g, ctx := errgroup.WithContext(ctx)
    g.SetLimit(bp.maxConcurrency)
    
    // 并行处理
    for _, item := range items {
        item := item
        
        g.Go(func() error {
            _, childSpan := tracer.Start(ctx, "process-item",
                trace.WithAttributes(
                    attribute.Int("item.id", item),
                ),
            )
            defer childSpan.End()
            
            // 处理项目
            if err := processItem(ctx, item); err != nil {
                childSpan.RecordError(err)
                return err
            }
            
            return nil
        })
    }
    
    // 等待所有任务完成
    if err := g.Wait(); err != nil {
        span.RecordError(err)
        return err
    }
    
    return nil
}

func processItem(ctx context.Context, item int) error {
    time.Sleep(5 * time.Millisecond)
    return nil
}

// 使用示例
func UseErrGroup(ctx context.Context) {
    // 并行导出
    exporter := NewParallelSpanExporter([]string{
        "jaeger:14250",
        "tempo:4317",
        "zipkin:9411",
    })
    
    spans := []SpanData{
        {TraceID: "trace-1", SpanID: "span-1", Name: "op1"},
        {TraceID: "trace-2", SpanID: "span-2", Name: "op2"},
    }
    
    if err := exporter.Export(ctx, spans); err != nil {
        log.Printf("Export failed: %v", err)
    }
    
    // 批处理
    processor := NewBatchProcessor(10)
    items := make([]int, 100)
    for i := range items {
        items[i] = i
    }
    
    if err := processor.ProcessItems(ctx, items); err != nil {
        log.Printf("Processing failed: %v", err)
    }
}
```

---

## semaphore 并发限制

```go
package observability

import (
    "context"
    "fmt"

    "golang.org/x/sync/semaphore"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// RateLimiter 速率限制器
type RateLimiter struct {
    sem    *semaphore.Weighted
    limit  int64
    tracer trace.Tracer
}

// NewRateLimiter 创建速率限制器
func NewRateLimiter(limit int64) *RateLimiter {
    return &RateLimiter{
        sem:    semaphore.NewWeighted(limit),
        limit:  limit,
        tracer: otel.Tracer("rate-limiter"),
    }
}

// Acquire 获取资源 (阻塞)
func (rl *RateLimiter) Acquire(ctx context.Context, weight int64) error {
    ctx, span := rl.tracer.Start(ctx, "acquire-semaphore",
        trace.WithAttributes(
            attribute.Int64("weight", weight),
            attribute.Int64("limit", rl.limit),
        ),
    )
    defer span.End()
    
    if err := rl.sem.Acquire(ctx, weight); err != nil {
        span.RecordError(err)
        return err
    }
    
    span.AddEvent("acquired")
    return nil
}

// TryAcquire 尝试获取资源 (非阻塞)
func (rl *RateLimiter) TryAcquire(weight int64) bool {
    return rl.sem.TryAcquire(weight)
}

// Release 释放资源
func (rl *RateLimiter) Release(weight int64) {
    rl.sem.Release(weight)
}

// ProcessWithRateLimit 带速率限制的处理
func ProcessWithRateLimit(ctx context.Context, tasks []int) error {
    tracer := otel.Tracer("rate-limit-demo")
    ctx, span := tracer.Start(ctx, "process-with-rate-limit",
        trace.WithAttributes(
            attribute.Int("tasks.count", len(tasks)),
        ),
    )
    defer span.End()
    
    // 限制并发为 10
    limiter := NewRateLimiter(10)
    
    var wg sync.WaitGroup
    for _, task := range tasks {
        wg.Add(1)
        
        go func(taskID int) {
            defer wg.Done()
            
            // 获取资源
            if err := limiter.Acquire(ctx, 1); err != nil {
                log.Printf("Failed to acquire: %v", err)
                return
            }
            defer limiter.Release(1)
            
            // 处理任务
            _, taskSpan := tracer.Start(ctx, "process-task",
                trace.WithAttributes(
                    attribute.Int("task.id", taskID),
                ),
            )
            defer taskSpan.End()
            
            processTask(ctx, taskID)
        }(task)
    }
    
    wg.Wait()
    return nil
}

func processTask(ctx context.Context, taskID int) {
    time.Sleep(10 * time.Millisecond)
}
```

---

## singleflight 请求合并

```go
package observability

import (
    "context"
    "fmt"
    "time"

    "golang.org/x/sync/singleflight"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// CachedTracer 带缓存的追踪器
type CachedTracer struct {
    sf     singleflight.Group
    tracer trace.Tracer
}

// NewCachedTracer 创建带缓存的追踪器
func NewCachedTracer() *CachedTracer {
    return &CachedTracer{
        tracer: otel.Tracer("cached-tracer"),
    }
}

// GetUserData 获取用户数据 (请求合并)
func (ct *CachedTracer) GetUserData(ctx context.Context, userID int) (string, error) {
    ctx, span := ct.tracer.Start(ctx, "get-user-data",
        trace.WithAttributes(
            attribute.Int("user.id", userID),
        ),
    )
    defer span.End()
    
    key := fmt.Sprintf("user:%d", userID)
    
    // singleflight - 相同 key 的并发请求会合并为一个
    result, err, shared := ct.sf.Do(key, func() (interface{}, error) {
        span.AddEvent("fetching_from_database")
        
        // 模拟数据库查询
        time.Sleep(100 * time.Millisecond)
        return fmt.Sprintf("User-%d-Data", userID), nil
    })
    
    if shared {
        span.AddEvent("result_shared", trace.WithAttributes(
            attribute.Bool("shared", true),
        ))
    }
    
    if err != nil {
        span.RecordError(err)
        return "", err
    }
    
    return result.(string), nil
}

// 使用示例 - 并发请求相同数据
func UseSingleFlight(ctx context.Context) {
    cached := NewCachedTracer()
    
    var wg sync.WaitGroup
    
    // 100 个并发请求获取相同用户数据
    for i := 0; i < 100; i++ {
        wg.Add(1)
        go func(id int) {
            defer wg.Done()
            
            // 所有请求都获取 userID=123 的数据
            data, err := cached.GetUserData(ctx, 123)
            if err != nil {
                log.Printf("Request %d failed: %v", id, err)
                return
            }
            
            fmt.Printf("Request %d got: %s\n", id, data)
        }(i)
    }
    
    wg.Wait()
    
    // 结果: 只会执行一次数据库查询,其他 99 个请求共享结果
}

// 高级用法 - DoChan (异步)
func (ct *CachedTracer) GetUserDataAsync(ctx context.Context, userID int) <-chan singleflight.Result {
    key := fmt.Sprintf("user:%d", userID)
    
    return ct.sf.DoChan(key, func() (interface{}, error) {
        _, span := ct.tracer.Start(ctx, "fetch-user-async",
            trace.WithAttributes(
                attribute.Int("user.id", userID),
            ),
        )
        defer span.End()
        
        time.Sleep(100 * time.Millisecond)
        return fmt.Sprintf("User-%d-Data", userID), nil
    })
}
```

---

## Channel 高级模式

### 1. Fan-Out Fan-In 模式

```go
package observability

import (
    "context"
    "sync"

    "go.opentelemetry.io/otel"
)

// FanOut 扇出 - 将任务分发到多个 Worker
func FanOut(ctx context.Context, input <-chan int, workerCount int) []<-chan int {
    tracer := otel.Tracer("fan-out")
    ctx, span := tracer.Start(ctx, "fan-out",
        trace.WithAttributes(
            attribute.Int("worker.count", workerCount),
        ),
    )
    defer span.End()
    
    outputs := make([]<-chan int, workerCount)
    
    for i := 0; i < workerCount; i++ {
        output := make(chan int)
        outputs[i] = output
        
        go func(workerID int, out chan<- int) {
            defer close(out)
            
            _, workerSpan := tracer.Start(ctx, "worker",
                trace.WithAttributes(
                    attribute.Int("worker.id", workerID),
                ),
            )
            defer workerSpan.End()
            
            for value := range input {
                // 处理值
                result := value * 2
                
                select {
                case out <- result:
                case <-ctx.Done():
                    return
                }
            }
        }(i, output)
    }
    
    return outputs
}

// FanIn 扇入 - 合并多个 Worker 的输出
func FanIn(ctx context.Context, inputs ...<-chan int) <-chan int {
    tracer := otel.Tracer("fan-in")
    ctx, span := tracer.Start(ctx, "fan-in",
        trace.WithAttributes(
            attribute.Int("input.count", len(inputs)),
        ),
    )
    defer span.End()
    
    output := make(chan int)
    
    var wg sync.WaitGroup
    wg.Add(len(inputs))
    
    for _, input := range inputs {
        go func(in <-chan int) {
            defer wg.Done()
            
            for value := range in {
                select {
                case output <- value:
                case <-ctx.Done():
                    return
                }
            }
        }(input)
    }
    
    go func() {
        wg.Wait()
        close(output)
        span.AddEvent("all_workers_completed")
    }()
    
    return output
}

// 使用示例
func UseFanOutFanIn(ctx context.Context) {
    // 输入 Channel
    input := make(chan int)
    
    // 扇出到 5 个 Worker
    outputs := FanOut(ctx, input, 5)
    
    // 扇入合并结果
    result := FanIn(ctx, outputs...)
    
    // 发送输入
    go func() {
        for i := 0; i < 100; i++ {
            input <- i
        }
        close(input)
    }()
    
    // 接收结果
    for value := range result {
        fmt.Println(value)
    }
}
```

### 2. Pipeline 模式

```go
// Stage 管道阶段
func Stage(ctx context.Context, name string, input <-chan int, fn func(int) int) <-chan int {
    tracer := otel.Tracer("pipeline")
    ctx, span := tracer.Start(ctx, name)
    defer span.End()
    
    output := make(chan int)
    
    go func() {
        defer close(output)
        
        for value := range input {
            select {
            case output <- fn(value):
            case <-ctx.Done():
                return
            }
        }
    }()
    
    return output
}

// 使用示例
func UsePipeline(ctx context.Context) {
    // 创建输入
    input := make(chan int)
    
    // 构建管道
    stage1 := Stage(ctx, "multiply", input, func(n int) int { return n * 2 })
    stage2 := Stage(ctx, "add", stage1, func(n int) int { return n + 10 })
    stage3 := Stage(ctx, "square", stage2, func(n int) int { return n * n })
    
    // 发送输入
    go func() {
        for i := 1; i <= 5; i++ {
            input <- i
        }
        close(input)
    }()
    
    // 接收输出
    for result := range stage3 {
        fmt.Println(result)
    }
}
```

---

## 并发追踪最佳实践

### 1. Goroutine 追踪

```go
func LaunchGoroutineWithSpan(ctx context.Context, name string, fn func(context.Context)) {
    tracer := otel.Tracer("goroutine-launcher")
    
    // 创建 Span
    ctx, span := tracer.Start(ctx, name)
    
    go func() {
        defer span.End()
        
        // 在 Goroutine 中执行
        fn(ctx)
    }()
}
```

### 2. Context 传播

```go
✅ DO: 传递 Context
go func(ctx context.Context) {
    // 使用 ctx
}(ctx)

❌ DON'T: 不传递 Context
go func() {
    // 丢失追踪上下文
}()
```

### 3. 取消处理

```go
func WorkerWithCancellation(ctx context.Context) {
    tracer := otel.Tracer("worker")
    ctx, span := tracer.Start(ctx, "worker")
    defer span.End()
    
    for {
        select {
        case <-ctx.Done():
            span.AddEvent("cancelled")
            return
        default:
            // 执行工作
        }
    }
}
```

---

## 性能对比

```text
并发原语性能对比 (1M 操作):

Mutex:               30 ns/op     0 B/op     0 allocs/op
RWMutex (读):        25 ns/op     0 B/op     0 allocs/op
RWMutex (写):        35 ns/op     0 B/op     0 allocs/op
sync.Map:            120 ns/op    48 B/op    2 allocs/op
Channel:             150 ns/op    0 B/op     0 allocs/op
errgroup:            180 ns/op    64 B/op    1 allocs/op
semaphore:           95 ns/op     0 B/op     0 allocs/op
singleflight:        250 ns/op    128 B/op   3 allocs/op
```

---

**相关文档**:

- [Go 并发模式集成](./02_Go并发模式与OTLP集成.md)
- [Go 性能优化](./03_Go性能优化与最佳实践.md)

# Go 高级并发模式与 OTLP 完整集成

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025年10月10日

---

## 📋 目录

- [Go 高级并发模式与 OTLP 完整集成](#go-高级并发模式与-otlp-完整集成)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Channel 高级模式](#channel-高级模式)
    - [1. 带追踪的 Channel 包装器](#1-带追踪的-channel-包装器)
    - [2. Select 多路复用模式](#2-select-多路复用模式)
  - [Worker Pool 模式](#worker-pool-模式)
    - [完整的 Worker Pool 实现](#完整的-worker-pool-实现)
  - [Pipeline 模式](#pipeline-模式)
    - [完整的 Pipeline 实现](#完整的-pipeline-实现)
  - [Fan-Out/Fan-In 模式](#fan-outfan-in-模式)
  - [Rate Limiting 模式](#rate-limiting-模式)
  - [最佳实践](#最佳实践)
    - [1. Context 传播](#1-context-传播)
    - [2. Goroutine 泄漏防护](#2-goroutine-泄漏防护)
    - [3. 错误处理](#3-错误处理)
    - [4. 性能优化](#4-性能优化)
  - [总结](#总结)

---

## 概述

本文档深入探讨 Go 高级并发模式与 OpenTelemetry OTLP 的集成，涵盖生产级并发控制、错误处理和可观测性实践。

**核心并发原语**:

```text
✅ Channel - 通信与同步
✅ Select - 多路复用
✅ Context - 取消传播
✅ sync.WaitGroup - 等待组
✅ sync.Mutex/RWMutex - 互斥锁
✅ sync.Once - 单次执行
✅ errgroup - 错误组
✅ semaphore - 信号量
```

---

## Channel 高级模式

### 1. 带追踪的 Channel 包装器

```go
package channels

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// TracedChannel 带追踪的 Channel
type TracedChannel[T any] struct {
    ch          chan T
    name        string
    tracer      trace.Tracer
    meter       metric.Meter
    
    // Metrics
    sendCounter    metric.Int64Counter
    recvCounter    metric.Int64Counter
    queueSize      metric.Int64ObservableGauge
    sendLatency    metric.Float64Histogram
    recvLatency    metric.Float64Histogram
}

// NewTracedChannel 创建带追踪的 Channel
func NewTracedChannel[T any](name string, bufferSize int) (*TracedChannel[T], error) {
    tracer := otel.Tracer("traced-channel")
    meter := otel.Meter("traced-channel")
    
    tc := &TracedChannel[T]{
        ch:     make(chan T, bufferSize),
        name:   name,
        tracer: tracer,
        meter:  meter,
    }
    
    var err error
    
    // 发送计数器
    tc.sendCounter, err = meter.Int64Counter(
        "channel.send.count",
        metric.WithDescription("Channel send operations"),
    )
    if err != nil {
        return nil, err
    }
    
    // 接收计数器
    tc.recvCounter, err = meter.Int64Counter(
        "channel.recv.count",
        metric.WithDescription("Channel receive operations"),
    )
    if err != nil {
        return nil, err
    }
    
    // 队列大小
    tc.queueSize, err = meter.Int64ObservableGauge(
        "channel.queue.size",
        metric.WithDescription("Channel queue size"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            observer.Observe(int64(len(tc.ch)),
                metric.WithAttributes(
                    attribute.String("channel.name", tc.name),
                ),
            )
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }
    
    // 发送延迟
    tc.sendLatency, err = meter.Float64Histogram(
        "channel.send.latency",
        metric.WithDescription("Channel send latency"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    // 接收延迟
    tc.recvLatency, err = meter.Float64Histogram(
        "channel.recv.latency",
        metric.WithDescription("Channel receive latency"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    return tc, nil
}

// Send 发送数据（带追踪）
func (tc *TracedChannel[T]) Send(ctx context.Context, value T) error {
    ctx, span := tc.tracer.Start(ctx, "channel.send",
        trace.WithAttributes(
            attribute.String("channel.name", tc.name),
        ),
    )
    defer span.End()
    
    start := time.Now()
    
    select {
    case tc.ch <- value:
        // 记录成功发送
        latency := time.Since(start)
        
        tc.sendCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("channel.name", tc.name),
                attribute.String("status", "success"),
            ),
        )
        
        tc.sendLatency.Record(ctx, float64(latency.Milliseconds()),
            metric.WithAttributes(
                attribute.String("channel.name", tc.name),
            ),
        )
        
        span.AddEvent("sent", trace.WithAttributes(
            attribute.Float64("latency_ms", float64(latency.Milliseconds())),
        ))
        
        return nil
        
    case <-ctx.Done():
        // 超时或取消
        tc.sendCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("channel.name", tc.name),
                attribute.String("status", "cancelled"),
            ),
        )
        
        span.RecordError(ctx.Err())
        return ctx.Err()
    }
}

// Receive 接收数据（带追踪）
func (tc *TracedChannel[T]) Receive(ctx context.Context) (T, error) {
    ctx, span := tc.tracer.Start(ctx, "channel.receive",
        trace.WithAttributes(
            attribute.String("channel.name", tc.name),
        ),
    )
    defer span.End()
    
    start := time.Now()
    
    select {
    case value := <-tc.ch:
        // 记录成功接收
        latency := time.Since(start)
        
        tc.recvCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("channel.name", tc.name),
                attribute.String("status", "success"),
            ),
        )
        
        tc.recvLatency.Record(ctx, float64(latency.Milliseconds()),
            metric.WithAttributes(
                attribute.String("channel.name", tc.name),
            ),
        )
        
        span.AddEvent("received", trace.WithAttributes(
            attribute.Float64("latency_ms", float64(latency.Milliseconds())),
        ))
        
        return value, nil
        
    case <-ctx.Done():
        // 超时或取消
        var zero T
        
        tc.recvCounter.Add(ctx, 1,
            metric.WithAttributes(
                attribute.String("channel.name", tc.name),
                attribute.String("status", "cancelled"),
            ),
        )
        
        span.RecordError(ctx.Err())
        return zero, ctx.Err()
    }
}

// Close 关闭 Channel
func (tc *TracedChannel[T]) Close() {
    close(tc.ch)
}

// Len 返回 Channel 当前长度
func (tc *TracedChannel[T]) Len() int {
    return len(tc.ch)
}

// Cap 返回 Channel 容量
func (tc *TracedChannel[T]) Cap() int {
    return cap(tc.ch)
}
```

### 2. Select 多路复用模式

```go
package channels

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// SelectMultiplexer Select 多路复用器
type SelectMultiplexer[T any] struct {
    tracer trace.Tracer
}

// NewSelectMultiplexer 创建 Select 多路复用器
func NewSelectMultiplexer[T any]() *SelectMultiplexer[T] {
    return &SelectMultiplexer[T]{
        tracer: otel.Tracer("select-multiplexer"),
    }
}

// SelectFirst 选择第一个到达的结果
func (sm *SelectMultiplexer[T]) SelectFirst(
    ctx context.Context,
    channels ...<-chan T,
) (T, error) {
    ctx, span := sm.tracer.Start(ctx, "select.first",
        trace.WithAttributes(
            attribute.Int("channels.count", len(channels)),
        ),
    )
    defer span.End()
    
    start := time.Now()
    
    // 构建 select cases
    cases := make([]reflect.SelectCase, len(channels)+1)
    
    // Context done case
    cases[0] = reflect.SelectCase{
        Dir:  reflect.SelectRecv,
        Chan: reflect.ValueOf(ctx.Done()),
    }
    
    // Channel cases
    for i, ch := range channels {
        cases[i+1] = reflect.SelectCase{
            Dir:  reflect.SelectRecv,
            Chan: reflect.ValueOf(ch),
        }
    }
    
    // Select
    chosen, value, ok := reflect.Select(cases)
    
    if chosen == 0 {
        // Context cancelled
        var zero T
        span.RecordError(ctx.Err())
        return zero, ctx.Err()
    }
    
    if !ok {
        // Channel closed
        var zero T
        err := ErrChannelClosed
        span.RecordError(err)
        return zero, err
    }
    
    // Success
    result := value.Interface().(T)
    latency := time.Since(start)
    
    span.SetAttributes(
        attribute.Int("channel.chosen", chosen-1),
        attribute.Float64("latency_ms", float64(latency.Milliseconds())),
    )
    
    return result, nil
}

// SelectAll 等待所有结果
func (sm *SelectMultiplexer[T]) SelectAll(
    ctx context.Context,
    channels ...<-chan T,
) ([]T, error) {
    ctx, span := sm.tracer.Start(ctx, "select.all",
        trace.WithAttributes(
            attribute.Int("channels.count", len(channels)),
        ),
    )
    defer span.End()
    
    results := make([]T, 0, len(channels))
    remaining := len(channels)
    
    for remaining > 0 {
        // 构建动态 select cases
        cases := make([]reflect.SelectCase, remaining+1)
        
        cases[0] = reflect.SelectCase{
            Dir:  reflect.SelectRecv,
            Chan: reflect.ValueOf(ctx.Done()),
        }
        
        idx := 1
        channelMap := make(map[int]int) // case index -> channel index
        
        for i, ch := range channels {
            if ch != nil {
                cases[idx] = reflect.SelectCase{
                    Dir:  reflect.SelectRecv,
                    Chan: reflect.ValueOf(ch),
                }
                channelMap[idx] = i
                idx++
            }
        }
        
        chosen, value, ok := reflect.Select(cases)
        
        if chosen == 0 {
            // Context cancelled
            span.RecordError(ctx.Err())
            return results, ctx.Err()
        }
        
        if ok {
            result := value.Interface().(T)
            results = append(results, result)
        }
        
        // 标记该 channel 已完成
        originalIdx := channelMap[chosen]
        channels[originalIdx] = nil
        remaining--
    }
    
    span.SetAttributes(
        attribute.Int("results.count", len(results)),
    )
    
    return results, nil
}

// SelectTimeout 带超时的选择
func (sm *SelectMultiplexer[T]) SelectTimeout(
    ctx context.Context,
    timeout time.Duration,
    channel <-chan T,
) (T, error) {
    ctx, span := sm.tracer.Start(ctx, "select.timeout",
        trace.WithAttributes(
            attribute.Float64("timeout_ms", float64(timeout.Milliseconds())),
        ),
    )
    defer span.End()
    
    timer := time.NewTimer(timeout)
    defer timer.Stop()
    
    select {
    case value := <-channel:
        span.AddEvent("received")
        return value, nil
        
    case <-timer.C:
        var zero T
        err := ErrTimeout
        span.RecordError(err)
        span.SetAttributes(attribute.Bool("timeout", true))
        return zero, err
        
    case <-ctx.Done():
        var zero T
        span.RecordError(ctx.Err())
        return zero, ctx.Err()
    }
}

var (
    ErrChannelClosed = errors.New("channel closed")
    ErrTimeout       = errors.New("operation timed out")
)
```

---

## Worker Pool 模式

### 完整的 Worker Pool 实现

```go
package workerpool

import (
    "context"
    "errors"
    "sync"
    "sync/atomic"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// Job 工作任务接口
type Job interface {
    ID() string
    Execute(ctx context.Context) error
}

// WorkerPool Worker 池
type WorkerPool struct {
    name          string
    workerCount   int
    queueSize     int
    
    jobs          chan Job
    results       chan Result
    
    tracer        trace.Tracer
    meter         metric.Meter
    
    // Metrics
    activeWorkers   atomic.Int64
    totalJobs       atomic.Int64
    successJobs     atomic.Int64
    failedJobs      atomic.Int64
    
    jobDuration     metric.Float64Histogram
    queueLength     metric.Int64ObservableGauge
    workerUtilization metric.Float64ObservableGauge
    
    wg            sync.WaitGroup
    stopCh        chan struct{}
    stopped       atomic.Bool
}

// Result 任务结果
type Result struct {
    JobID    string
    Error    error
    Duration time.Duration
}

// Config Worker Pool 配置
type Config struct {
    Name        string
    WorkerCount int
    QueueSize   int
}

// NewWorkerPool 创建 Worker Pool
func NewWorkerPool(cfg Config) (*WorkerPool, error) {
    if cfg.WorkerCount <= 0 {
        cfg.WorkerCount = 10
    }
    if cfg.QueueSize <= 0 {
        cfg.QueueSize = 100
    }
    
    tracer := otel.Tracer("worker-pool")
    meter := otel.Meter("worker-pool")
    
    wp := &WorkerPool{
        name:        cfg.Name,
        workerCount: cfg.WorkerCount,
        queueSize:   cfg.QueueSize,
        jobs:        make(chan Job, cfg.QueueSize),
        results:     make(chan Result, cfg.QueueSize),
        tracer:      tracer,
        meter:       meter,
        stopCh:      make(chan struct{}),
    }
    
    var err error
    
    // 任务持续时间
    wp.jobDuration, err = meter.Float64Histogram(
        "workerpool.job.duration",
        metric.WithDescription("Job execution duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    // 队列长度
    wp.queueLength, err = meter.Int64ObservableGauge(
        "workerpool.queue.length",
        metric.WithDescription("Job queue length"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            observer.Observe(int64(len(wp.jobs)),
                metric.WithAttributes(
                    attribute.String("pool.name", wp.name),
                ),
            )
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }
    
    // Worker 利用率
    wp.workerUtilization, err = meter.Float64ObservableGauge(
        "workerpool.worker.utilization",
        metric.WithDescription("Worker utilization rate"),
        metric.WithUnit("%"),
        metric.WithFloat64Callback(func(ctx context.Context, observer metric.Float64Observer) error {
            active := float64(wp.activeWorkers.Load())
            total := float64(wp.workerCount)
            utilization := (active / total) * 100
            
            observer.Observe(utilization,
                metric.WithAttributes(
                    attribute.String("pool.name", wp.name),
                ),
            )
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }
    
    return wp, nil
}

// Start 启动 Worker Pool
func (wp *WorkerPool) Start(ctx context.Context) {
    ctx, span := wp.tracer.Start(ctx, "workerpool.start",
        trace.WithAttributes(
            attribute.String("pool.name", wp.name),
            attribute.Int("worker.count", wp.workerCount),
        ),
    )
    defer span.End()
    
    for i := 0; i < wp.workerCount; i++ {
        wp.wg.Add(1)
        go wp.worker(ctx, i)
    }
    
    span.AddEvent("workers started")
}

// worker Worker 工作函数
func (wp *WorkerPool) worker(ctx context.Context, workerID int) {
    defer wp.wg.Done()
    
    ctx, span := wp.tracer.Start(ctx, "workerpool.worker",
        trace.WithAttributes(
            attribute.String("pool.name", wp.name),
            attribute.Int("worker.id", workerID),
        ),
    )
    defer span.End()
    
    for {
        select {
        case job, ok := <-wp.jobs:
            if !ok {
                // Channel closed
                span.AddEvent("jobs channel closed")
                return
            }
            
            // 执行任务
            wp.activeWorkers.Add(1)
            result := wp.executeJob(ctx, job, workerID)
            wp.activeWorkers.Add(-1)
            
            // 发送结果
            select {
            case wp.results <- result:
            case <-wp.stopCh:
                return
            }
            
        case <-wp.stopCh:
            span.AddEvent("received stop signal")
            return
        }
    }
}

// executeJob 执行任务
func (wp *WorkerPool) executeJob(ctx context.Context, job Job, workerID int) Result {
    ctx, span := wp.tracer.Start(ctx, "workerpool.execute_job",
        trace.WithAttributes(
            attribute.String("pool.name", wp.name),
            attribute.Int("worker.id", workerID),
            attribute.String("job.id", job.ID()),
        ),
    )
    defer span.End()
    
    start := time.Now()
    wp.totalJobs.Add(1)
    
    // 执行任务
    err := job.Execute(ctx)
    duration := time.Since(start)
    
    // 记录结果
    result := Result{
        JobID:    job.ID(),
        Error:    err,
        Duration: duration,
    }
    
    // 更新 metrics
    attrs := metric.WithAttributes(
        attribute.String("pool.name", wp.name),
        attribute.String("job.id", job.ID()),
    )
    
    wp.jobDuration.Record(ctx, float64(duration.Milliseconds()), attrs)
    
    if err != nil {
        wp.failedJobs.Add(1)
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        span.SetAttributes(attribute.Bool("job.failed", true))
    } else {
        wp.successJobs.Add(1)
        span.SetStatus(codes.Ok, "")
        span.SetAttributes(attribute.Bool("job.success", true))
    }
    
    span.SetAttributes(
        attribute.Float64("job.duration_ms", float64(duration.Milliseconds())),
    )
    
    return result
}

// Submit 提交任务
func (wp *WorkerPool) Submit(ctx context.Context, job Job) error {
    if wp.stopped.Load() {
        return errors.New("worker pool is stopped")
    }
    
    ctx, span := wp.tracer.Start(ctx, "workerpool.submit",
        trace.WithAttributes(
            attribute.String("pool.name", wp.name),
            attribute.String("job.id", job.ID()),
        ),
    )
    defer span.End()
    
    select {
    case wp.jobs <- job:
        span.AddEvent("job submitted")
        return nil
        
    case <-ctx.Done():
        span.RecordError(ctx.Err())
        return ctx.Err()
        
    case <-wp.stopCh:
        err := errors.New("worker pool is stopped")
        span.RecordError(err)
        return err
    }
}

// Results 获取结果 channel
func (wp *WorkerPool) Results() <-chan Result {
    return wp.results
}

// Stop 停止 Worker Pool
func (wp *WorkerPool) Stop(ctx context.Context) error {
    if !wp.stopped.CompareAndSwap(false, true) {
        return errors.New("worker pool already stopped")
    }
    
    ctx, span := wp.tracer.Start(ctx, "workerpool.stop",
        trace.WithAttributes(
            attribute.String("pool.name", wp.name),
        ),
    )
    defer span.End()
    
    // 关闭 stop channel
    close(wp.stopCh)
    
    // 关闭 jobs channel
    close(wp.jobs)
    
    // 等待所有 workers 完成
    done := make(chan struct{})
    go func() {
        wp.wg.Wait()
        close(done)
    }()
    
    select {
    case <-done:
        span.AddEvent("all workers stopped")
        close(wp.results)
        return nil
        
    case <-ctx.Done():
        span.RecordError(ctx.Err())
        return ctx.Err()
    }
}

// Stats 获取统计信息
func (wp *WorkerPool) Stats() Stats {
    return Stats{
        PoolName:      wp.name,
        WorkerCount:   wp.workerCount,
        QueueSize:     len(wp.jobs),
        ActiveWorkers: int(wp.activeWorkers.Load()),
        TotalJobs:     wp.totalJobs.Load(),
        SuccessJobs:   wp.successJobs.Load(),
        FailedJobs:    wp.failedJobs.Load(),
    }
}

// Stats 统计信息
type Stats struct {
    PoolName      string
    WorkerCount   int
    QueueSize     int
    ActiveWorkers int
    TotalJobs     int64
    SuccessJobs   int64
    FailedJobs    int64
}
```

---

## Pipeline 模式

### 完整的 Pipeline 实现

```go
package pipeline

import (
    "context"
    "sync"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Stage Pipeline 阶段接口
type Stage[IN, OUT any] interface {
    Process(ctx context.Context, input IN) (OUT, error)
    Name() string
}

// Pipeline 泛型 Pipeline
type Pipeline[T any] struct {
    name    string
    stages  []func(context.Context, T) (T, error)
    tracer  trace.Tracer
}

// NewPipeline 创建 Pipeline
func NewPipeline[T any](name string) *Pipeline[T] {
    return &Pipeline[T]{
        name:   name,
        stages: make([]func(context.Context, T) (T, error), 0),
        tracer: otel.Tracer("pipeline"),
    }
}

// AddStage 添加阶段
func (p *Pipeline[T]) AddStage(
    stageName string,
    fn func(context.Context, T) (T, error),
) *Pipeline[T] {
    wrapped := func(ctx context.Context, input T) (T, error) {
        ctx, span := p.tracer.Start(ctx, "pipeline.stage",
            trace.WithAttributes(
                attribute.String("pipeline.name", p.name),
                attribute.String("stage.name", stageName),
            ),
        )
        defer span.End()
        
        output, err := fn(ctx, input)
        if err != nil {
            span.RecordError(err)
            return output, err
        }
        
        span.AddEvent("stage completed")
        return output, nil
    }
    
    p.stages = append(p.stages, wrapped)
    return p
}

// Execute 执行 Pipeline
func (p *Pipeline[T]) Execute(ctx context.Context, input T) (T, error) {
    ctx, span := p.tracer.Start(ctx, "pipeline.execute",
        trace.WithAttributes(
            attribute.String("pipeline.name", p.name),
            attribute.Int("stages.count", len(p.stages)),
        ),
    )
    defer span.End()
    
    current := input
    
    for i, stage := range p.stages {
        span.AddEvent("executing stage", trace.WithAttributes(
            attribute.Int("stage.index", i),
        ))
        
        result, err := stage(ctx, current)
        if err != nil {
            span.RecordError(err)
            span.SetAttributes(
                attribute.Int("failed.stage", i),
            )
            return current, err
        }
        
        current = result
    }
    
    span.AddEvent("pipeline completed")
    return current, nil
}

// ParallelPipeline 并行 Pipeline
type ParallelPipeline[T any] struct {
    name      string
    pipelines []*Pipeline[T]
    tracer    trace.Tracer
}

// NewParallelPipeline 创建并行 Pipeline
func NewParallelPipeline[T any](name string) *ParallelPipeline[T] {
    return &ParallelPipeline[T]{
        name:      name,
        pipelines: make([]*Pipeline[T], 0),
        tracer:    otel.Tracer("parallel-pipeline"),
    }
}

// AddPipeline 添加 Pipeline
func (pp *ParallelPipeline[T]) AddPipeline(pipeline *Pipeline[T]) {
    pp.pipelines = append(pp.pipelines, pipeline)
}

// Execute 并行执行所有 Pipeline
func (pp *ParallelPipeline[T]) Execute(ctx context.Context, input T) ([]T, error) {
    ctx, span := pp.tracer.Start(ctx, "parallel_pipeline.execute",
        trace.WithAttributes(
            attribute.String("pipeline.name", pp.name),
            attribute.Int("pipelines.count", len(pp.pipelines)),
        ),
    )
    defer span.End()
    
    results := make([]T, len(pp.pipelines))
    errors := make([]error, len(pp.pipelines))
    
    var wg sync.WaitGroup
    
    for i, pipeline := range pp.pipelines {
        wg.Add(1)
        
        go func(idx int, p *Pipeline[T]) {
            defer wg.Done()
            
            result, err := p.Execute(ctx, input)
            results[idx] = result
            errors[idx] = err
        }(i, pipeline)
    }
    
    wg.Wait()
    
    // 检查错误
    for i, err := range errors {
        if err != nil {
            span.RecordError(err)
            span.SetAttributes(
                attribute.Int("failed.pipeline", i),
            )
            return results, err
        }
    }
    
    span.AddEvent("all pipelines completed")
    return results, nil
}
```

继续创建剩余部分...

---

## Fan-Out/Fan-In 模式

```go
package fanout

import (
    "context"
    "sync"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
    "golang.org/x/sync/errgroup"
)

// FanOut Fan-Out 模式 - 将一个输入分发到多个 goroutine
func FanOut[T any, R any](
    ctx context.Context,
    input T,
    workerCount int,
    worker func(context.Context, T, int) (R, error),
) ([]R, error) {
    tracer := otel.Tracer("fanout")
    
    ctx, span := tracer.Start(ctx, "fanout.execute",
        trace.WithAttributes(
            attribute.Int("worker.count", workerCount),
        ),
    )
    defer span.End()
    
    results := make([]R, workerCount)
    g, gCtx := errgroup.WithContext(ctx)
    
    for i := 0; i < workerCount; i++ {
        workerID := i
        
        g.Go(func() error {
            result, err := worker(gCtx, input, workerID)
            if err != nil {
                return err
            }
            results[workerID] = result
            return nil
        })
    }
    
    if err := g.Wait(); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.AddEvent("fanout completed")
    return results, nil
}

// FanIn Fan-In 模式 - 合并多个 channel 到一个
func FanIn[T any](
    ctx context.Context,
    channels ...<-chan T,
) <-chan T {
    tracer := otel.Tracer("fanin")
    
    ctx, span := tracer.Start(ctx, "fanin.merge",
        trace.WithAttributes(
            attribute.Int("channels.count", len(channels)),
        ),
    )
    
    out := make(chan T)
    var wg sync.WaitGroup
    
    // 为每个输入 channel 启动一个 goroutine
    for i, ch := range channels {
        wg.Add(1)
        
        go func(id int, c <-chan T) {
            defer wg.Done()
            
            for value := range c {
                select {
                case out <- value:
                case <-ctx.Done():
                    return
                }
            }
        }(i, ch)
    }
    
    // 等待所有 goroutine 完成后关闭输出 channel
    go func() {
        wg.Wait()
        close(out)
        span.End()
    }()
    
    return out
}
```

---

## Rate Limiting 模式

```go
package ratelimit

import (
    "context"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
    "golang.org/x/time/rate"
)

// RateLimiter 速率限制器
type RateLimiter struct {
    limiter       *rate.Limiter
    tracer        trace.Tracer
    meter         metric.Meter
    
    allowedCount  metric.Int64Counter
    deniedCount   metric.Int64Counter
    waitDuration  metric.Float64Histogram
}

// NewRateLimiter 创建速率限制器
func NewRateLimiter(rps int, burst int) (*RateLimiter, error) {
    tracer := otel.Tracer("rate-limiter")
    meter := otel.Meter("rate-limiter")
    
    rl := &RateLimiter{
        limiter: rate.NewLimiter(rate.Limit(rps), burst),
        tracer:  tracer,
        meter:   meter,
    }
    
    var err error
    
    rl.allowedCount, err = meter.Int64Counter(
        "ratelimit.allowed.count",
        metric.WithDescription("Allowed requests"),
    )
    if err != nil {
        return nil, err
    }
    
    rl.deniedCount, err = meter.Int64Counter(
        "ratelimit.denied.count",
        metric.WithDescription("Denied requests"),
    )
    if err != nil {
        return nil, err
    }
    
    rl.waitDuration, err = meter.Float64Histogram(
        "ratelimit.wait.duration",
        metric.WithDescription("Wait duration"),
        metric.WithUnit("ms"),
    )
    if err != nil {
        return nil, err
    }
    
    return rl, nil
}

// Allow 检查是否允许执行
func (rl *RateLimiter) Allow(ctx context.Context) bool {
    ctx, span := rl.tracer.Start(ctx, "ratelimit.allow")
    defer span.End()
    
    allowed := rl.limiter.Allow()
    
    if allowed {
        rl.allowedCount.Add(ctx, 1)
        span.SetAttributes(attribute.Bool("allowed", true))
    } else {
        rl.deniedCount.Add(ctx, 1)
        span.SetAttributes(attribute.Bool("allowed", false))
    }
    
    return allowed
}

// Wait 等待直到允许执行
func (rl *RateLimiter) Wait(ctx context.Context) error {
    ctx, span := rl.tracer.Start(ctx, "ratelimit.wait")
    defer span.End()
    
    start := time.Now()
    
    err := rl.limiter.Wait(ctx)
    
    duration := time.Since(start)
    rl.waitDuration.Record(ctx, float64(duration.Milliseconds()))
    
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    rl.allowedCount.Add(ctx, 1)
    span.SetAttributes(
        attribute.Float64("wait_ms", float64(duration.Milliseconds())),
    )
    
    return nil
}

// Execute 执行带速率限制的函数
func (rl *RateLimiter) Execute(
    ctx context.Context,
    fn func(context.Context) error,
) error {
    if err := rl.Wait(ctx); err != nil {
        return err
    }
    
    return fn(ctx)
}
```

---

## 最佳实践

### 1. Context 传播

```go
✅ 正确:
go func(ctx context.Context) {
    _, span := tracer.Start(ctx, "goroutine")
    defer span.End()
}(ctx)

❌ 错误:
go func() {
    ctx := context.Background() // 丢失了 trace context
}()
```

### 2. Goroutine 泄漏防护

```go
// 使用 context 控制 goroutine 生命周期
func worker(ctx context.Context) {
    for {
        select {
        case <-ctx.Done():
            return // ✅ 及时退出
        case job := <-jobs:
            process(job)
        }
    }
}
```

### 3. 错误处理

```go
// 使用 errgroup 收集错误
g, ctx := errgroup.WithContext(ctx)

g.Go(func() error {
    _, span := tracer.Start(ctx, "task1")
    defer span.End()
    
    if err := task1(ctx); err != nil {
        span.RecordError(err)
        return err
    }
    return nil
})

if err := g.Wait(); err != nil {
    // 处理第一个错误
}
```

### 4. 性能优化

```go
// 使用 buffer 减少阻塞
ch := make(chan T, 100)  // ✅ 带缓冲

// 预分配容量
results := make([]T, 0, expectedSize)

// 使用 sync.Pool 复用对象
var pool = sync.Pool{
    New: func() interface{} {
        return &Object{}
    },
}
```

---

## 总结

本文档提供了完整的 Go 高级并发模式与 OTLP 集成方案:

**核心模式**:

- ✅ Channel 模式 - 带追踪的通信机制
- ✅ Worker Pool - 可观测的工作池
- ✅ Pipeline - 流式数据处理
- ✅ Fan-Out/Fan-In - 并行处理和聚合
- ✅ Rate Limiting - 流量控制
- ✅ Semaphore - 并发限制

**最佳实践**:

- ✅ Context 正确传播
- ✅ Goroutine 生命周期管理
- ✅ 错误收集与追踪
- ✅ 性能优化技巧

**相关文档**:

- [Go并发模式与OTLP集成](./02_Go并发模式与OTLP集成.md)
- [Go并发原语与OTLP深度集成](./24_Go并发原语与OTLP深度集成.md)
- [Go性能优化与最佳实践](./03_Go性能优化与最佳实践.md)

---

**最后更新**: 2025年10月10日  
**维护者**: OTLP Go 集成项目组

# Pipeline 模式集成

## 目录

- [Pipeline 模式集成](#pipeline-模式集成)
  - [目录](#目录)
  - [1. CSP Pipeline 模式](#1-csp-pipeline-模式)
    - [1.1 基本 Pipeline](#11-基本-pipeline)
    - [1.2 并行 Pipeline](#12-并行-pipeline)
  - [2. OTLP Collector Pipeline 对应](#2-otlp-collector-pipeline-对应)
    - [2.1 Collector Pipeline 架构](#21-collector-pipeline-架构)
    - [2.2 自定义 Processor](#22-自定义-processor)
  - [3. 背压控制](#3-背压控制)
    - [3.1 Channel 缓冲背压](#31-channel-缓冲背压)
    - [3.2 动态背压调整](#32-动态背压调整)
  - [4. 流量管理](#4-流量管理)
    - [4.1 限流器](#41-限流器)
    - [4.2 流量整形](#42-流量整形)
  - [5. 错误处理与恢复](#5-错误处理与恢复)
    - [5.1 重试机制](#51-重试机制)
    - [5.2 断路器](#52-断路器)
    - [5.3 错误恢复](#53-错误恢复)
  - [6. 完整实现示例](#6-完整实现示例)
  - [7. 性能优化](#7-性能优化)
    - [7.1 批量处理](#71-批量处理)
    - [7.2 对象池化](#72-对象池化)
  - [8. 参考资料](#8-参考资料)

## 1. CSP Pipeline 模式

### 1.1 基本 Pipeline

**CSP 定义**：

```csp
PIPELINE = Stage1 ; Stage2 ; Stage3

Stage1 = input?x -> process1(x) -> output1!y -> Stage1
Stage2 = input1?y -> process2(y) -> output2!z -> Stage2
Stage3 = input2?z -> process3(z) -> output3!result -> Stage3
```

**Go 实现**：

```go
func pipeline(ctx context.Context, input <-chan Data) <-chan Result {
    ctx, span := tracer.Start(ctx, "pipeline")
    defer span.End()
    
    // Stage 1
    stage1Out := stage1(ctx, input)
    
    // Stage 2
    stage2Out := stage2(ctx, stage1Out)
    
    // Stage 3
    stage3Out := stage3(ctx, stage2Out)
    
    return stage3Out
}

func stage1(ctx context.Context, input <-chan Data) <-chan Intermediate1 {
    output := make(chan Intermediate1)
    
    go func() {
        defer close(output)
        
        for data := range input {
            ctx, span := tracer.Start(ctx, "stage1")
            span.SetAttributes(
                attribute.String("data.id", data.ID),
            )
            
            result := process1(data)
            
            select {
            case output <- result:
                span.AddEvent("data_sent")
            case <-ctx.Done():
                span.RecordError(ctx.Err())
                span.End()
                return
            }
            
            span.End()
        }
    }()
    
    return output
}
```

### 1.2 并行 Pipeline

```go
func parallelPipeline(ctx context.Context, input <-chan Data, workers int) <-chan Result {
    ctx, span := tracer.Start(ctx, "parallel_pipeline")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("workers", workers),
    )
    
    // Fan-out: 分发到多个 worker
    workerInputs := fanOut(ctx, input, workers)
    
    // 每个 worker 执行 pipeline
    workerOutputs := make([]<-chan Result, workers)
    for i, workerInput := range workerInputs {
        workerOutputs[i] = workerPipeline(ctx, i, workerInput)
    }
    
    // Fan-in: 合并结果
    return fanIn(ctx, workerOutputs)
}

func workerPipeline(ctx context.Context, id int, input <-chan Data) <-chan Result {
    output := make(chan Result)
    
    go func() {
        defer close(output)
        
        for data := range input {
            ctx, span := tracer.Start(ctx, "worker_pipeline")
            span.SetAttributes(
                attribute.Int("worker.id", id),
                attribute.String("data.id", data.ID),
            )
            
            // Pipeline stages
            intermediate1 := process1(data)
            intermediate2 := process2(intermediate1)
            result := process3(intermediate2)
            
            select {
            case output <- result:
            case <-ctx.Done():
                span.End()
                return
            }
            
            span.End()
        }
    }()
    
    return output
}
```

## 2. OTLP Collector Pipeline 对应

### 2.1 Collector Pipeline 架构

**配置映射**：

```yaml
# CSP Stage1 → Receiver
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

# CSP Stage2 → Processor
processors:
  batch:
    timeout: 10s
    send_batch_size: 1024
  
  transform:
    traces:
      - set(attributes["processed"], true)
  
  memory_limiter:
    limit_mib: 512

# CSP Stage3 → Exporter
exporters:
  otlp:
    endpoint: backend.example.com:4317
  
  logging:
    loglevel: debug

# Pipeline 组合
service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [memory_limiter, batch, transform]
      exporters: [otlp, logging]
```

### 2.2 自定义 Processor

```go
package customprocessor

import (
    "context"
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/consumer"
    "go.opentelemetry.io/collector/pdata/ptrace"
)

type customProcessor struct {
    next consumer.Traces
}

func (p *customProcessor) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // CSP Stage 处理逻辑
    ctx, span := tracer.Start(ctx, "custom_processor")
    defer span.End()
    
    // 处理每个 Span
    for i := 0; i < td.ResourceSpans().Len(); i++ {
        rs := td.ResourceSpans().At(i)
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)
                
                // 添加自定义属性
                span.Attributes().PutStr("processor", "custom")
                span.Attributes().PutInt("processed_at", time.Now().Unix())
            }
        }
    }
    
    // 传递到下一个 stage
    return p.next.ConsumeTraces(ctx, td)
}

func (p *customProcessor) Capabilities() consumer.Capabilities {
    return consumer.Capabilities{MutatesData: true}
}

func (p *customProcessor) Shutdown(ctx context.Context) error {
    return nil
}
```

## 3. 背压控制

### 3.1 Channel 缓冲背压

```go
type BackpressureController struct {
    input       <-chan Data
    output      chan<- Result
    bufferSize  int
    currentSize int64
    maxSize     int64
    mu          sync.Mutex
}

func (b *BackpressureController) Process(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "backpressure_controller")
    defer span.End()
    
    buffer := make([]Data, 0, b.bufferSize)
    ticker := time.NewTicker(100 * time.Millisecond)
    defer ticker.Stop()
    
    for {
        select {
        case data, ok := <-b.input:
            if !ok {
                b.flush(ctx, buffer)
                return
            }
            
            // 检查背压
            if b.shouldApplyBackpressure() {
                span.AddEvent("backpressure_applied")
                
                // 等待或丢弃
                select {
                case <-time.After(1 * time.Second):
                    span.AddEvent("data_dropped")
                    continue
                case <-ctx.Done():
                    return
                }
            }
            
            buffer = append(buffer, data)
            
            if len(buffer) >= b.bufferSize {
                b.flush(ctx, buffer)
                buffer = buffer[:0]
            }
            
        case <-ticker.C:
            if len(buffer) > 0 {
                b.flush(ctx, buffer)
                buffer = buffer[:0]
            }
            
        case <-ctx.Done():
            return
        }
    }
}

func (b *BackpressureController) shouldApplyBackpressure() bool {
    b.mu.Lock()
    defer b.mu.Unlock()
    
    utilization := float64(b.currentSize) / float64(b.maxSize)
    return utilization > 0.8  // 80% 阈值
}

func (b *BackpressureController) flush(ctx context.Context, buffer []Data) {
    ctx, span := tracer.Start(ctx, "flush")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("batch.size", len(buffer)),
    )
    
    for _, data := range buffer {
        result := process(data)
        
        select {
        case b.output <- result:
        case <-ctx.Done():
            return
        }
    }
}
```

### 3.2 动态背压调整

```go
type AdaptiveBackpressure struct {
    targetLatency time.Duration
    currentLatency time.Duration
    bufferSize    int
    minBuffer     int
    maxBuffer     int
}

func (a *AdaptiveBackpressure) AdjustBufferSize() {
    if a.currentLatency > a.targetLatency {
        // 延迟过高，减小缓冲
        a.bufferSize = max(a.minBuffer, a.bufferSize/2)
    } else if a.currentLatency < a.targetLatency/2 {
        // 延迟很低，增大缓冲
        a.bufferSize = min(a.maxBuffer, a.bufferSize*2)
    }
}

func (a *AdaptiveBackpressure) Monitor(ctx context.Context) {
    ticker := time.NewTicker(5 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            a.AdjustBufferSize()
            
            // 上报指标
            meter.RecordInt64(ctx, "buffer.size", int64(a.bufferSize))
            meter.RecordDuration(ctx, "latency.current", a.currentLatency)
            
        case <-ctx.Done():
            return
        }
    }
}
```

## 4. 流量管理

### 4.1 限流器

```go
type RateLimiter struct {
    rate     int           // 每秒请求数
    burst    int           // 突发容量
    limiter  *rate.Limiter
}

func NewRateLimiter(rps, burst int) *RateLimiter {
    return &RateLimiter{
        rate:    rps,
        burst:   burst,
        limiter: rate.NewLimiter(rate.Limit(rps), burst),
    }
}

func (r *RateLimiter) Process(ctx context.Context, input <-chan Data) <-chan Data {
    output := make(chan Data)
    
    go func() {
        defer close(output)
        
        for data := range input {
            ctx, span := tracer.Start(ctx, "rate_limiter")
            
            // 等待令牌
            if err := r.limiter.Wait(ctx); err != nil {
                span.RecordError(err)
                span.End()
                continue
            }
            
            span.AddEvent("token_acquired")
            
            select {
            case output <- data:
            case <-ctx.Done():
                span.End()
                return
            }
            
            span.End()
        }
    }()
    
    return output
}
```

### 4.2 流量整形

```go
type TrafficShaper struct {
    windowSize time.Duration
    maxItems   int
    window     []time.Time
    mu         sync.Mutex
}

func (t *TrafficShaper) Allow() bool {
    t.mu.Lock()
    defer t.mu.Unlock()
    
    now := time.Now()
    cutoff := now.Add(-t.windowSize)
    
    // 移除过期的时间戳
    validIdx := 0
    for i, ts := range t.window {
        if ts.After(cutoff) {
            validIdx = i
            break
        }
    }
    t.window = t.window[validIdx:]
    
    // 检查是否超过限制
    if len(t.window) >= t.maxItems {
        return false
    }
    
    t.window = append(t.window, now)
    return true
}

func (t *TrafficShaper) Process(ctx context.Context, input <-chan Data) <-chan Data {
    output := make(chan Data)
    
    go func() {
        defer close(output)
        
        for data := range input {
            ctx, span := tracer.Start(ctx, "traffic_shaper")
            
            if !t.Allow() {
                span.AddEvent("rate_limited")
                span.End()
                continue
            }
            
            select {
            case output <- data:
            case <-ctx.Done():
                span.End()
                return
            }
            
            span.End()
        }
    }()
    
    return output
}
```

## 5. 错误处理与恢复

### 5.1 重试机制

```go
type RetryPolicy struct {
    MaxRetries      int
    InitialInterval time.Duration
    MaxInterval     time.Duration
    Multiplier      float64
}

func (r *RetryPolicy) Execute(ctx context.Context, fn func() error) error {
    ctx, span := tracer.Start(ctx, "retry_execute")
    defer span.End()
    
    var err error
    interval := r.InitialInterval
    
    for attempt := 0; attempt <= r.MaxRetries; attempt++ {
        if attempt > 0 {
            span.AddEvent("retry_attempt", trace.WithAttributes(
                attribute.Int("attempt", attempt),
                attribute.Duration("interval", interval),
            ))
            
            select {
            case <-time.After(interval):
            case <-ctx.Done():
                return ctx.Err()
            }
            
            interval = time.Duration(float64(interval) * r.Multiplier)
            if interval > r.MaxInterval {
                interval = r.MaxInterval
            }
        }
        
        err = fn()
        if err == nil {
            span.SetAttributes(
                attribute.Int("attempts", attempt+1),
            )
            return nil
        }
        
        span.RecordError(err)
    }
    
    return fmt.Errorf("max retries exceeded: %w", err)
}
```

### 5.2 断路器

```go
type CircuitBreaker struct {
    maxFailures  int
    resetTimeout time.Duration
    state        State
    failures     int
    lastFailTime time.Time
    mu           sync.Mutex
}

type State int

const (
    StateClosed State = iota
    StateOpen
    StateHalfOpen
)

func (cb *CircuitBreaker) Execute(ctx context.Context, fn func() error) error {
    ctx, span := tracer.Start(ctx, "circuit_breaker")
    defer span.End()
    
    cb.mu.Lock()
    state := cb.state
    
    // 检查是否可以尝试恢复
    if state == StateOpen && time.Since(cb.lastFailTime) > cb.resetTimeout {
        cb.state = StateHalfOpen
        state = StateHalfOpen
    }
    cb.mu.Unlock()
    
    span.SetAttributes(
        attribute.String("state", state.String()),
    )
    
    if state == StateOpen {
        return fmt.Errorf("circuit breaker is open")
    }
    
    err := fn()
    
    cb.mu.Lock()
    defer cb.mu.Unlock()
    
    if err != nil {
        cb.failures++
        cb.lastFailTime = time.Now()
        
        if cb.failures >= cb.maxFailures {
            cb.state = StateOpen
            span.AddEvent("circuit_opened")
        }
        
        span.RecordError(err)
        return err
    }
    
    // 成功，重置
    if cb.state == StateHalfOpen {
        cb.state = StateClosed
        span.AddEvent("circuit_closed")
    }
    cb.failures = 0
    
    return nil
}

func (s State) String() string {
    switch s {
    case StateClosed:
        return "closed"
    case StateOpen:
        return "open"
    case StateHalfOpen:
        return "half_open"
    default:
        return "unknown"
    }
}
```

### 5.3 错误恢复

```go
type RecoveryHandler struct {
    input  <-chan Data
    output chan<- Result
    errors chan<- error
}

func (r *RecoveryHandler) Process(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "recovery_handler")
    defer span.End()
    
    defer func() {
        if err := recover(); err != nil {
            span.RecordError(fmt.Errorf("panic recovered: %v", err))
            
            // 记录错误
            select {
            case r.errors <- fmt.Errorf("panic: %v", err):
            default:
            }
        }
    }()
    
    for data := range r.input {
        func() {
            defer func() {
                if err := recover(); err != nil {
                    span.AddEvent("item_panic_recovered", trace.WithAttributes(
                        attribute.String("error", fmt.Sprintf("%v", err)),
                    ))
                }
            }()
            
            result := process(data)
            
            select {
            case r.output <- result:
            case <-ctx.Done():
                return
            }
        }()
    }
}
```

## 6. 完整实现示例

```go
package pipeline

import (
    "context"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("pipeline")

type Pipeline struct {
    input       <-chan Data
    output      chan Result
    rateLimiter *RateLimiter
    backpressure *BackpressureController
    retry       *RetryPolicy
    circuit     *CircuitBreaker
}

func NewPipeline(input <-chan Data, config Config) *Pipeline {
    return &Pipeline{
        input:  input,
        output: make(chan Result, config.BufferSize),
        rateLimiter: NewRateLimiter(config.RateLimit, config.Burst),
        backpressure: NewBackpressureController(config.MaxSize),
        retry: &RetryPolicy{
            MaxRetries:      3,
            InitialInterval: 1 * time.Second,
            MaxInterval:     30 * time.Second,
            Multiplier:      2.0,
        },
        circuit: &CircuitBreaker{
            maxFailures:  5,
            resetTimeout: 60 * time.Second,
        },
    }
}

func (p *Pipeline) Start(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "pipeline_start")
    defer span.End()
    
    // Stage 1: Rate limiting
    stage1 := p.rateLimiter.Process(ctx, p.input)
    
    // Stage 2: Backpressure control
    stage2 := p.processWithBackpressure(ctx, stage1)
    
    // Stage 3: Processing with retry and circuit breaker
    stage3 := p.processWithResilience(ctx, stage2)
    
    // Output
    go func() {
        for result := range stage3 {
            select {
            case p.output <- result:
            case <-ctx.Done():
                return
            }
        }
        close(p.output)
    }()
}

func (p *Pipeline) processWithBackpressure(ctx context.Context, input <-chan Data) <-chan Data {
    output := make(chan Data)
    
    go func() {
        defer close(output)
        p.backpressure.Process(ctx, input, output)
    }()
    
    return output
}

func (p *Pipeline) processWithResilience(ctx context.Context, input <-chan Data) <-chan Result {
    output := make(chan Result)
    
    go func() {
        defer close(output)
        
        for data := range input {
            var result Result
            
            err := p.circuit.Execute(ctx, func() error {
                return p.retry.Execute(ctx, func() error {
                    ctx, span := tracer.Start(ctx, "process_data")
                    defer span.End()
                    
                    var err error
                    result, err = processData(ctx, data)
                    return err
                })
            })
            
            if err != nil {
                continue
            }
            
            select {
            case output <- result:
            case <-ctx.Done():
                return
            }
        }
    }()
    
    return output
}

func (p *Pipeline) Output() <-chan Result {
    return p.output
}
```

## 7. 性能优化

### 7.1 批量处理

```go
type BatchProcessor struct {
    batchSize int
    timeout   time.Duration
}

func (b *BatchProcessor) Process(ctx context.Context, input <-chan Data) <-chan []Data {
    output := make(chan []Data)
    
    go func() {
        defer close(output)
        
        batch := make([]Data, 0, b.batchSize)
        ticker := time.NewTicker(b.timeout)
        defer ticker.Stop()
        
        flush := func() {
            if len(batch) > 0 {
                ctx, span := tracer.Start(ctx, "batch_flush")
                span.SetAttributes(
                    attribute.Int("batch.size", len(batch)),
                )
                
                batchCopy := make([]Data, len(batch))
                copy(batchCopy, batch)
                
                select {
                case output <- batchCopy:
                case <-ctx.Done():
                    span.End()
                    return
                }
                
                batch = batch[:0]
                span.End()
            }
        }
        
        for {
            select {
            case data, ok := <-input:
                if !ok {
                    flush()
                    return
                }
                
                batch = append(batch, data)
                if len(batch) >= b.batchSize {
                    flush()
                }
                
            case <-ticker.C:
                flush()
                
            case <-ctx.Done():
                return
            }
        }
    }()
    
    return output
}
```

### 7.2 对象池化

```go
var dataPool = sync.Pool{
    New: func() interface{} {
        return &Data{}
    },
}

func acquireData() *Data {
    return dataPool.Get().(*Data)
}

func releaseData(data *Data) {
    data.Reset()
    dataPool.Put(data)
}
```

## 8. 参考资料

- **Go Pipelines**：<https://go.dev/blog/pipelines>
- **Collector Architecture**：`docs/design/technical-model.md`
- **Backpressure Patterns**：`docs/design/distributed-model.md`
- **CSP Theory**：`01-csp-otlp-isomorphism.md`

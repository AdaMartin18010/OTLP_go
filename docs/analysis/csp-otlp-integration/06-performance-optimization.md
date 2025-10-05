# 性能优化策略

## 目录

- [性能优化策略](#性能优化策略)
  - [目录](#目录)
  - [1. Channel 缓冲与批处理](#1-channel-缓冲与批处理)
    - [1.1 动态缓冲调整](#11-动态缓冲调整)
    - [1.2 智能批处理](#12-智能批处理)
  - [2. Goroutine 池化](#2-goroutine-池化)
    - [2.1 Worker Pool 实现](#21-worker-pool-实现)
    - [2.2 动态 Worker Pool](#22-动态-worker-pool)
  - [3. 内存管理与对象复用](#3-内存管理与对象复用)
    - [3.1 Span 对象池](#31-span-对象池)
    - [3.2 零拷贝序列化](#32-零拷贝序列化)
    - [3.3 内存池管理](#33-内存池管理)
  - [4. OTLP 导出优化](#4-otlp-导出优化)
    - [4.1 批量导出器](#41-批量导出器)
    - [4.2 压缩优化](#42-压缩优化)
  - [5. 采样策略](#5-采样策略)
    - [5.1 自适应采样](#51-自适应采样)
    - [5.2 尾部采样](#52-尾部采样)
  - [6. 零分配优化](#6-零分配优化)
    - [6.1 避免接口转换](#61-避免接口转换)
    - [6.2 字符串优化](#62-字符串优化)
  - [7. 性能基准测试](#7-性能基准测试)
  - [8. 参考资料](#8-参考资料)

## 1. Channel 缓冲与批处理

### 1.1 动态缓冲调整

```go
type AdaptiveBuffer struct {
    ch          chan Data
    targetSize  int
    minSize     int
    maxSize     int
    utilization float64
    mu          sync.RWMutex
}

func NewAdaptiveBuffer(initial, min, max int) *AdaptiveBuffer {
    return &AdaptiveBuffer{
        ch:         make(chan Data, initial),
        targetSize: initial,
        minSize:    min,
        maxSize:    max,
    }
}

func (ab *AdaptiveBuffer) AdjustSize(ctx context.Context) {
    ticker := time.NewTicker(5 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            ab.mu.Lock()
            currentLen := len(ab.ch)
            currentCap := cap(ab.ch)
            ab.utilization = float64(currentLen) / float64(currentCap)
            
            var newSize int
            if ab.utilization > 0.8 {
                // 高利用率，增大缓冲
                newSize = min(ab.maxSize, currentCap*2)
            } else if ab.utilization < 0.2 {
                // 低利用率，减小缓冲
                newSize = max(ab.minSize, currentCap/2)
            } else {
                ab.mu.Unlock()
                continue
            }
            
            if newSize != currentCap {
                ab.resize(newSize)
                
                // 记录指标
                meter.RecordInt64(ctx, "buffer.size", int64(newSize))
                meter.RecordFloat64(ctx, "buffer.utilization", ab.utilization)
            }
            
            ab.mu.Unlock()
            
        case <-ctx.Done():
            return
        }
    }
}

func (ab *AdaptiveBuffer) resize(newSize int) {
    newCh := make(chan Data, newSize)
    
    // 迁移现有数据
    close(ab.ch)
    for data := range ab.ch {
        select {
        case newCh <- data:
        default:
            // 缓冲已满，丢弃
        }
    }
    
    ab.ch = newCh
    ab.targetSize = newSize
}
```

### 1.2 智能批处理

```go
type SmartBatcher struct {
    maxBatchSize int
    maxWaitTime  time.Duration
    input        <-chan Data
    output       chan<- []Data
    
    // 自适应参数
    avgProcessTime time.Duration
    ewma           *EWMA
}

func NewSmartBatcher(input <-chan Data, output chan<- []Data, config BatchConfig) *SmartBatcher {
    return &SmartBatcher{
        maxBatchSize: config.MaxSize,
        maxWaitTime:  config.MaxWait,
        input:        input,
        output:       output,
        ewma:         NewEWMA(0.3), // 指数加权移动平均
    }
}

func (sb *SmartBatcher) Run(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "smart_batcher")
    defer span.End()
    
    batch := make([]Data, 0, sb.maxBatchSize)
    timer := time.NewTimer(sb.maxWaitTime)
    defer timer.Stop()
    
    flush := func() {
        if len(batch) == 0 {
            return
        }
        
        start := time.Now()
        
        batchCopy := make([]Data, len(batch))
        copy(batchCopy, batch)
        
        select {
        case sb.output <- batchCopy:
            // 更新处理时间
            processTime := time.Since(start)
            sb.avgProcessTime = sb.ewma.Update(processTime)
            
            // 动态调整等待时间
            if sb.avgProcessTime > sb.maxWaitTime/2 {
                sb.maxWaitTime = min(sb.maxWaitTime*2, 10*time.Second)
            } else {
                sb.maxWaitTime = max(sb.maxWaitTime/2, 10*time.Millisecond)
            }
            
            span.AddEvent("batch_flushed", trace.WithAttributes(
                attribute.Int("batch.size", len(batch)),
                attribute.Duration("wait.time", sb.maxWaitTime),
            ))
            
        case <-ctx.Done():
            return
        }
        
        batch = batch[:0]
        timer.Reset(sb.maxWaitTime)
    }
    
    for {
        select {
        case data, ok := <-sb.input:
            if !ok {
                flush()
                return
            }
            
            batch = append(batch, data)
            
            // 批次大小达到阈值
            if len(batch) >= sb.maxBatchSize {
                flush()
            }
            
        case <-timer.C:
            // 超时，刷新批次
            flush()
            
        case <-ctx.Done():
            flush()
            return
        }
    }
}

// 指数加权移动平均
type EWMA struct {
    alpha float64
    value time.Duration
}

func NewEWMA(alpha float64) *EWMA {
    return &EWMA{alpha: alpha}
}

func (e *EWMA) Update(newValue time.Duration) time.Duration {
    if e.value == 0 {
        e.value = newValue
    } else {
        e.value = time.Duration(e.alpha*float64(newValue) + (1-e.alpha)*float64(e.value))
    }
    return e.value
}
```

## 2. Goroutine 池化

### 2.1 Worker Pool 实现

```go
type WorkerPool struct {
    workers    int
    taskQueue  chan Task
    resultQueue chan Result
    wg         sync.WaitGroup
    
    // 性能指标
    activeWorkers int64
    totalTasks    int64
    completedTasks int64
}

func NewWorkerPool(workers, queueSize int) *WorkerPool {
    return &WorkerPool{
        workers:     workers,
        taskQueue:   make(chan Task, queueSize),
        resultQueue: make(chan Result, queueSize),
    }
}

func (wp *WorkerPool) Start(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "worker_pool_start")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("workers", wp.workers),
    )
    
    for i := 0; i < wp.workers; i++ {
        wp.wg.Add(1)
        go wp.worker(ctx, i)
    }
    
    // 监控 goroutine
    go wp.monitor(ctx)
}

func (wp *WorkerPool) worker(ctx context.Context, id int) {
    defer wp.wg.Done()
    
    for {
        select {
        case task, ok := <-wp.taskQueue:
            if !ok {
                return
            }
            
            atomic.AddInt64(&wp.activeWorkers, 1)
            
            ctx, span := tracer.Start(ctx, "worker_process")
            span.SetAttributes(
                attribute.Int("worker.id", id),
                attribute.String("task.id", task.ID),
            )
            
            start := time.Now()
            result := task.Execute(ctx)
            duration := time.Since(start)
            
            span.SetAttributes(
                attribute.Duration("task.duration", duration),
            )
            span.End()
            
            atomic.AddInt64(&wp.activeWorkers, -1)
            atomic.AddInt64(&wp.completedTasks, 1)
            
            select {
            case wp.resultQueue <- result:
            case <-ctx.Done():
                return
            }
            
        case <-ctx.Done():
            return
        }
    }
}

func (wp *WorkerPool) monitor(ctx context.Context) {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            active := atomic.LoadInt64(&wp.activeWorkers)
            completed := atomic.LoadInt64(&wp.completedTasks)
            queueLen := len(wp.taskQueue)
            
            // 上报指标
            meter.RecordInt64(ctx, "worker.active", active)
            meter.RecordInt64(ctx, "worker.completed", completed)
            meter.RecordInt64(ctx, "worker.queue.length", int64(queueLen))
            
            // 动态调整（如果需要）
            utilization := float64(active) / float64(wp.workers)
            if utilization > 0.9 && queueLen > wp.workers*2 {
                // 考虑增加 worker（需要实现动态扩展）
            }
            
        case <-ctx.Done():
            return
        }
    }
}

func (wp *WorkerPool) Submit(task Task) error {
    atomic.AddInt64(&wp.totalTasks, 1)
    
    select {
    case wp.taskQueue <- task:
        return nil
    default:
        return errors.New("task queue full")
    }
}

func (wp *WorkerPool) Stop() {
    close(wp.taskQueue)
    wp.wg.Wait()
    close(wp.resultQueue)
}
```

### 2.2 动态 Worker Pool

```go
type DynamicWorkerPool struct {
    minWorkers int
    maxWorkers int
    currentWorkers int
    taskQueue  chan Task
    workerChan chan struct{}
    mu         sync.Mutex
}

func (dwp *DynamicWorkerPool) ScaleUp(ctx context.Context) {
    dwp.mu.Lock()
    defer dwp.mu.Unlock()
    
    if dwp.currentWorkers >= dwp.maxWorkers {
        return
    }
    
    // 启动新 worker
    go dwp.worker(ctx, dwp.currentWorkers)
    dwp.currentWorkers++
    
    meter.RecordInt64(ctx, "worker.scaled_up", int64(dwp.currentWorkers))
}

func (dwp *DynamicWorkerPool) ScaleDown(ctx context.Context) {
    dwp.mu.Lock()
    defer dwp.mu.Unlock()
    
    if dwp.currentWorkers <= dwp.minWorkers {
        return
    }
    
    // 发送停止信号
    select {
    case dwp.workerChan <- struct{}{}:
        dwp.currentWorkers--
        meter.RecordInt64(ctx, "worker.scaled_down", int64(dwp.currentWorkers))
    default:
    }
}
```

## 3. 内存管理与对象复用

### 3.1 Span 对象池

```go
type SpanPool struct {
    pool sync.Pool
}

func NewSpanPool() *SpanPool {
    return &SpanPool{
        pool: sync.Pool{
            New: func() interface{} {
                return &Span{
                    Attributes: make(map[string]interface{}, 16),
                    Events:     make([]Event, 0, 8),
                }
            },
        },
    }
}

func (sp *SpanPool) Get() *Span {
    return sp.pool.Get().(*Span)
}

func (sp *SpanPool) Put(span *Span) {
    // 重置 Span
    span.Reset()
    sp.pool.Put(span)
}

type Span struct {
    TraceID    [16]byte
    SpanID     [8]byte
    Name       string
    StartTime  time.Time
    EndTime    time.Time
    Attributes map[string]interface{}
    Events     []Event
}

func (s *Span) Reset() {
    s.Name = ""
    s.StartTime = time.Time{}
    s.EndTime = time.Time{}
    
    // 清空 map 但保留容量
    for k := range s.Attributes {
        delete(s.Attributes, k)
    }
    
    // 清空 slice 但保留容量
    s.Events = s.Events[:0]
}
```

### 3.2 零拷贝序列化

```go
type ZeroCopySerializer struct {
    buffer *bytes.Buffer
    writer *bufio.Writer
}

func NewZeroCopySerializer() *ZeroCopySerializer {
    buf := bytes.NewBuffer(make([]byte, 0, 4096))
    return &ZeroCopySerializer{
        buffer: buf,
        writer: bufio.NewWriter(buf),
    }
}

func (zcs *ZeroCopySerializer) SerializeSpan(span *Span) ([]byte, error) {
    zcs.buffer.Reset()
    zcs.writer.Reset(zcs.buffer)
    
    // 使用 protobuf 或其他高效序列化
    // 直接写入 buffer，避免中间分配
    
    if err := zcs.writer.Flush(); err != nil {
        return nil, err
    }
    
    // 返回底层字节切片（不复制）
    return zcs.buffer.Bytes(), nil
}
```

### 3.3 内存池管理

```go
type MemoryPool struct {
    pools map[int]*sync.Pool
}

func NewMemoryPool() *MemoryPool {
    mp := &MemoryPool{
        pools: make(map[int]*sync.Pool),
    }
    
    // 预定义常用大小的池
    sizes := []int{64, 128, 256, 512, 1024, 2048, 4096, 8192}
    for _, size := range sizes {
        size := size // 捕获循环变量
        mp.pools[size] = &sync.Pool{
            New: func() interface{} {
                return make([]byte, size)
            },
        }
    }
    
    return mp
}

func (mp *MemoryPool) Get(size int) []byte {
    // 找到最接近的池大小
    poolSize := mp.nearestPoolSize(size)
    
    if pool, ok := mp.pools[poolSize]; ok {
        buf := pool.Get().([]byte)
        return buf[:size]
    }
    
    // 没有合适的池，直接分配
    return make([]byte, size)
}

func (mp *MemoryPool) Put(buf []byte) {
    size := cap(buf)
    poolSize := mp.nearestPoolSize(size)
    
    if pool, ok := mp.pools[poolSize]; ok {
        pool.Put(buf[:cap(buf)])
    }
}

func (mp *MemoryPool) nearestPoolSize(size int) int {
    for _, poolSize := range []int{64, 128, 256, 512, 1024, 2048, 4096, 8192} {
        if size <= poolSize {
            return poolSize
        }
    }
    return 8192
}
```

## 4. OTLP 导出优化

### 4.1 批量导出器

```go
type BatchExporter struct {
    exporter     otlptrace.Client
    batchSize    int
    timeout      time.Duration
    queue        chan ptrace.Traces
    buffer       []ptrace.Traces
    mu           sync.Mutex
}

func NewBatchExporter(exporter otlptrace.Client, config ExportConfig) *BatchExporter {
    return &BatchExporter{
        exporter:  exporter,
        batchSize: config.BatchSize,
        timeout:   config.Timeout,
        queue:     make(chan ptrace.Traces, config.QueueSize),
        buffer:    make([]ptrace.Traces, 0, config.BatchSize),
    }
}

func (be *BatchExporter) Start(ctx context.Context) {
    ticker := time.NewTicker(be.timeout)
    defer ticker.Stop()
    
    for {
        select {
        case traces := <-be.queue:
            be.mu.Lock()
            be.buffer = append(be.buffer, traces)
            
            if len(be.buffer) >= be.batchSize {
                be.flush(ctx)
            }
            be.mu.Unlock()
            
        case <-ticker.C:
            be.mu.Lock()
            be.flush(ctx)
            be.mu.Unlock()
            
        case <-ctx.Done():
            be.mu.Lock()
            be.flush(ctx)
            be.mu.Unlock()
            return
        }
    }
}

func (be *BatchExporter) flush(ctx context.Context) {
    if len(be.buffer) == 0 {
        return
    }
    
    ctx, span := tracer.Start(ctx, "batch_export")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("batch.size", len(be.buffer)),
    )
    
    // 合并所有 traces
    merged := ptrace.NewTraces()
    for _, traces := range be.buffer {
        traces.ResourceSpans().MoveAndAppendTo(merged.ResourceSpans())
    }
    
    // 导出
    start := time.Now()
    if err := be.exporter.UploadTraces(ctx, merged); err != nil {
        span.RecordError(err)
    } else {
        duration := time.Since(start)
        span.SetAttributes(
            attribute.Duration("export.duration", duration),
        )
    }
    
    be.buffer = be.buffer[:0]
}
```

### 4.2 压缩优化

```go
type CompressedExporter struct {
    exporter     otlptrace.Client
    compression  Compression
}

type Compression int

const (
    NoCompression Compression = iota
    GzipCompression
    ZstdCompression
)

func (ce *CompressedExporter) Export(ctx context.Context, traces ptrace.Traces) error {
    ctx, span := tracer.Start(ctx, "compressed_export")
    defer span.End()
    
    // 序列化
    marshaler := &ptrace.ProtoMarshaler{}
    data, err := marshaler.MarshalTraces(traces)
    if err != nil {
        return err
    }
    
    originalSize := len(data)
    span.SetAttributes(
        attribute.Int("data.original_size", originalSize),
    )
    
    // 压缩
    compressed, err := ce.compress(data)
    if err != nil {
        return err
    }
    
    compressedSize := len(compressed)
    ratio := float64(compressedSize) / float64(originalSize)
    
    span.SetAttributes(
        attribute.Int("data.compressed_size", compressedSize),
        attribute.Float64("compression.ratio", ratio),
    )
    
    // 导出压缩数据
    return ce.exporter.UploadTraces(ctx, traces)
}

func (ce *CompressedExporter) compress(data []byte) ([]byte, error) {
    switch ce.compression {
    case GzipCompression:
        return ce.gzipCompress(data)
    case ZstdCompression:
        return ce.zstdCompress(data)
    default:
        return data, nil
    }
}

func (ce *CompressedExporter) gzipCompress(data []byte) ([]byte, error) {
    var buf bytes.Buffer
    writer := gzip.NewWriter(&buf)
    
    if _, err := writer.Write(data); err != nil {
        return nil, err
    }
    
    if err := writer.Close(); err != nil {
        return nil, err
    }
    
    return buf.Bytes(), nil
}
```

## 5. 采样策略

### 5.1 自适应采样

```go
type AdaptiveSampler struct {
    targetRate    float64
    currentRate   float64
    windowSize    time.Duration
    requestCount  int64
    sampledCount  int64
    lastAdjust    time.Time
    mu            sync.RWMutex
}

func NewAdaptiveSampler(targetRate float64) *AdaptiveSampler {
    return &AdaptiveSampler{
        targetRate:  targetRate,
        currentRate: targetRate,
        windowSize:  60 * time.Second,
        lastAdjust:  time.Now(),
    }
}

func (as *AdaptiveSampler) ShouldSample(ctx context.Context, traceID trace.TraceID) bool {
    atomic.AddInt64(&as.requestCount, 1)
    
    // 检查是否需要调整采样率
    if time.Since(as.lastAdjust) > as.windowSize {
        as.adjustRate()
    }
    
    // 基于 TraceID 的确定性采样
    threshold := uint64(as.currentRate * float64(math.MaxUint64))
    traceIDUint := binary.BigEndian.Uint64(traceID[:8])
    
    shouldSample := traceIDUint < threshold
    
    if shouldSample {
        atomic.AddInt64(&as.sampledCount, 1)
    }
    
    return shouldSample
}

func (as *AdaptiveSampler) adjustRate() {
    as.mu.Lock()
    defer as.mu.Unlock()
    
    requests := atomic.LoadInt64(&as.requestCount)
    sampled := atomic.LoadInt64(&as.sampledCount)
    
    if requests == 0 {
        return
    }
    
    actualRate := float64(sampled) / float64(requests)
    
    // 调整采样率
    if actualRate > as.targetRate*1.1 {
        // 实际采样率过高，降低
        as.currentRate *= 0.9
    } else if actualRate < as.targetRate*0.9 {
        // 实际采样率过低，提高
        as.currentRate *= 1.1
    }
    
    // 限制范围
    as.currentRate = math.Max(0.01, math.Min(1.0, as.currentRate))
    
    // 重置计数器
    atomic.StoreInt64(&as.requestCount, 0)
    atomic.StoreInt64(&as.sampledCount, 0)
    as.lastAdjust = time.Now()
    
    // 上报指标
    meter.RecordFloat64(context.Background(), "sampler.rate", as.currentRate)
}
```

### 5.2 尾部采样

```go
type TailSampler struct {
    traces    map[trace.TraceID]*TraceDecision
    decisions chan TraceDecision
    timeout   time.Duration
    mu        sync.RWMutex
}

type TraceDecision struct {
    TraceID     trace.TraceID
    Spans       []ptrace.Span
    ShouldKeep  bool
    HasError    bool
    Duration    time.Duration
}

func (ts *TailSampler) AddSpan(span ptrace.Span) {
    traceID := span.TraceID()
    
    ts.mu.Lock()
    decision, exists := ts.traces[traceID]
    if !exists {
        decision = &TraceDecision{
            TraceID: traceID,
            Spans:   make([]ptrace.Span, 0, 10),
        }
        ts.traces[traceID] = decision
    }
    
    decision.Spans = append(decision.Spans, span)
    
    // 检查错误
    if span.Status().Code() == ptrace.StatusCodeError {
        decision.HasError = true
    }
    
    ts.mu.Unlock()
    
    // 启动超时定时器
    go ts.scheduleDecision(traceID)
}

func (ts *TailSampler) scheduleDecision(traceID trace.TraceID) {
    time.Sleep(ts.timeout)
    
    ts.mu.Lock()
    decision, exists := ts.traces[traceID]
    if !exists {
        ts.mu.Unlock()
        return
    }
    
    delete(ts.traces, traceID)
    ts.mu.Unlock()
    
    // 做出采样决策
    decision.ShouldKeep = ts.makeDecision(decision)
    
    ts.decisions <- *decision
}

func (ts *TailSampler) makeDecision(decision *TraceDecision) bool {
    // 规则 1: 有错误的 trace 全部保留
    if decision.HasError {
        return true
    }
    
    // 规则 2: 慢 trace 保留
    if decision.Duration > 1*time.Second {
        return true
    }
    
    // 规则 3: 其他按比例采样
    return rand.Float64() < 0.1
}
```

## 6. 零分配优化

### 6.1 避免接口转换

```go
// 不好的实现（有分配）
func processAttributes(attrs map[string]interface{}) {
    for k, v := range attrs {
        switch v.(type) {  // 接口转换，可能分配
        case string:
            // ...
        case int:
            // ...
        }
    }
}

// 好的实现（零分配）
type AttributeValue struct {
    Type  AttributeType
    Str   string
    Int   int64
    Float float64
    Bool  bool
}

type AttributeType int

const (
    StringType AttributeType = iota
    IntType
    FloatType
    BoolType
)

func processAttributesOptimized(attrs map[string]AttributeValue) {
    for k, v := range attrs {
        switch v.Type {  // 无分配
        case StringType:
            // 使用 v.Str
        case IntType:
            // 使用 v.Int
        }
    }
}
```

### 6.2 字符串优化

```go
// 避免字符串拼接分配
type StringBuilder struct {
    buf []byte
}

func (sb *StringBuilder) Append(s string) {
    sb.buf = append(sb.buf, s...)
}

func (sb *StringBuilder) String() string {
    return string(sb.buf)  // 只有一次分配
}

// 使用 unsafe 零拷贝转换（谨慎使用）
func bytesToString(b []byte) string {
    return *(*string)(unsafe.Pointer(&b))
}

func stringToBytes(s string) []byte {
    return *(*[]byte)(unsafe.Pointer(&s))
}
```

## 7. 性能基准测试

```go
func BenchmarkSpanCreation(b *testing.B) {
    tracer := otel.Tracer("benchmark")
    ctx := context.Background()
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        _, span := tracer.Start(ctx, "test")
        span.End()
    }
}

func BenchmarkSpanWithPool(b *testing.B) {
    pool := NewSpanPool()
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        span := pool.Get()
        // 使用 span...
        pool.Put(span)
    }
}

func BenchmarkBatchExport(b *testing.B) {
    exporter := NewBatchExporter(nil, ExportConfig{
        BatchSize: 100,
        Timeout:   1 * time.Second,
    })
    
    traces := generateTestTraces(100)
    
    b.ResetTimer()
    b.ReportAllocs()
    
    for i := 0; i < b.N; i++ {
        exporter.Export(context.Background(), traces)
    }
}
```

## 8. 参考资料

- **Go Performance**：<https://go.dev/doc/diagnostics>
- **OTLP Optimization**：`docs/implementation/PHASE3_OPTIMIZATION_SUMMARY.md`
- **Benchmarks**：`benchmarks/README.md`
- **Memory Management**：`02-golang-csp-implementation.md`

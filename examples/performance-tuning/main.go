package main

import (
	"context"
	"fmt"
	"log"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	"go.opentelemetry.io/otel/trace"
)

// ============================
// 1. 高性能 Span 池
// ============================

// PooledSpan 可池化的 Span 包装器
type PooledSpan struct {
	ctx       context.Context
	span      trace.Span
	attrs     [32]attribute.KeyValue // 栈上数组,避免堆分配
	attrCount int
	released  bool
}

var spanPool = sync.Pool{
	New: func() interface{} {
		return &PooledSpan{}
	},
}

// AcquireSpan 从池中获取 Span
func AcquireSpan(tracer trace.Tracer, ctx context.Context, name string) *PooledSpan {
	ps := spanPool.Get().(*PooledSpan)
	ps.ctx, ps.span = tracer.Start(ctx, name)
	ps.attrCount = 0
	ps.released = false
	return ps
}

// SetAttribute 添加属性(零分配)
func (ps *PooledSpan) SetAttribute(kv attribute.KeyValue) {
	if ps.attrCount < len(ps.attrs) {
		ps.attrs[ps.attrCount] = kv
		ps.attrCount++
	}
}

// Release 释放 Span 回池
func (ps *PooledSpan) Release() {
	if ps.released {
		return
	}

	// 批量设置属性
	if ps.attrCount > 0 {
		ps.span.SetAttributes(ps.attrs[:ps.attrCount]...)
	}

	ps.span.End()
	ps.ctx = nil
	ps.span = nil
	ps.attrCount = 0
	ps.released = true

	spanPool.Put(ps)
}

// ============================
// 2. 批量导出优化
// ============================

// BatchExporter 批量导出器
type BatchExporter struct {
	mu         sync.Mutex
	buffer     []sdktrace.ReadOnlySpan
	batchSize  int
	flushTimer *time.Timer
	stopCh     chan struct{}
	exported   int64
}

// NewBatchExporter 创建批量导出器
func NewBatchExporter(batchSize int, flushInterval time.Duration) *BatchExporter {
	be := &BatchExporter{
		buffer:    make([]sdktrace.ReadOnlySpan, 0, batchSize),
		batchSize: batchSize,
		stopCh:    make(chan struct{}),
	}

	// 定时刷新
	be.flushTimer = time.AfterFunc(flushInterval, func() {
		be.FlushIfNeeded()
		be.flushTimer.Reset(flushInterval)
	})

	return be
}

// ExportSpans 导出 Span
func (be *BatchExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
	be.mu.Lock()
	defer be.mu.Unlock()

	be.buffer = append(be.buffer, spans...)

	if len(be.buffer) >= be.batchSize {
		return be.flush()
	}

	return nil
}

// flush 刷新缓冲区
func (be *BatchExporter) flush() error {
	if len(be.buffer) == 0 {
		return nil
	}

	count := len(be.buffer)
	atomic.AddInt64(&be.exported, int64(count))

	log.Printf("📤 Batch export: %d spans (total: %d)", count, atomic.LoadInt64(&be.exported))

	// 清空缓冲区(保留容量)
	be.buffer = be.buffer[:0]

	return nil
}

// FlushIfNeeded 如果需要则刷新
func (be *BatchExporter) FlushIfNeeded() {
	be.mu.Lock()
	defer be.mu.Unlock()

	if len(be.buffer) > 0 {
		be.flush()
	}
}

// Shutdown 关闭导出器
func (be *BatchExporter) Shutdown(ctx context.Context) error {
	be.flushTimer.Stop()
	close(be.stopCh)

	be.mu.Lock()
	defer be.mu.Unlock()

	return be.flush()
}

// ============================
// 3. 无锁计数器
// ============================

// LockFreeCounter 无锁计数器
type LockFreeCounter struct {
	count int64
}

// Inc 增加计数
func (c *LockFreeCounter) Inc() {
	atomic.AddInt64(&c.count, 1)
}

// Get 获取计数
func (c *LockFreeCounter) Get() int64 {
	return atomic.LoadInt64(&c.count)
}

// ============================
// 4. 并行处理优化
// ============================

// WorkerPool Worker 池
type WorkerPool struct {
	workers   int
	taskQueue chan func()
	wg        sync.WaitGroup
	stopCh    chan struct{}
	processed int64
}

// NewWorkerPool 创建 Worker 池
func NewWorkerPool(workers int, queueSize int) *WorkerPool {
	wp := &WorkerPool{
		workers:   workers,
		taskQueue: make(chan func(), queueSize),
		stopCh:    make(chan struct{}),
	}

	// 启动 workers
	for i := range workers {
		wp.wg.Add(1)
		go wp.worker(i)
	}

	return wp
}

// worker 工作协程
func (wp *WorkerPool) worker(id int) {
	defer wp.wg.Done()

	for {
		select {
		case task := <-wp.taskQueue:
			task()
			atomic.AddInt64(&wp.processed, 1)
		case <-wp.stopCh:
			return
		}
	}
}

// Submit 提交任务
func (wp *WorkerPool) Submit(task func()) {
	select {
	case wp.taskQueue <- task:
	case <-wp.stopCh:
	}
}

// Stop 停止 Worker 池
func (wp *WorkerPool) Stop() {
	close(wp.stopCh)
	wp.wg.Wait()
	close(wp.taskQueue)
	log.Printf("✅ Worker pool stopped, processed %d tasks", atomic.LoadInt64(&wp.processed))
}

// ============================
// 5. 内存预分配优化
// ============================

// PreallocatedBuffer 预分配缓冲区
type PreallocatedBuffer struct {
	data []byte
	pos  int
}

// NewPreallocatedBuffer 创建预分配缓冲区
func NewPreallocatedBuffer(size int) *PreallocatedBuffer {
	return &PreallocatedBuffer{
		data: make([]byte, 0, size),
		pos:  0,
	}
}

// Write 写入数据
func (pb *PreallocatedBuffer) Write(p []byte) (n int, err error) {
	pb.data = append(pb.data, p...)
	pb.pos += len(p)
	return len(p), nil
}

// Reset 重置缓冲区
func (pb *PreallocatedBuffer) Reset() {
	pb.data = pb.data[:0]
	pb.pos = 0
}

// ============================
// 6. 缓存优化
// ============================

// AttributeCache 属性缓存
type AttributeCache struct {
	cache sync.Map // 使用 sync.Map 提供无锁读取
}

// NewAttributeCache 创建属性缓存
func NewAttributeCache() *AttributeCache {
	return &AttributeCache{}
}

// Get 获取属性
func (ac *AttributeCache) Get(key string) ([]attribute.KeyValue, bool) {
	val, ok := ac.cache.Load(key)
	if !ok {
		return nil, false
	}
	return val.([]attribute.KeyValue), true
}

// Set 设置属性
func (ac *AttributeCache) Set(key string, attrs []attribute.KeyValue) {
	ac.cache.Store(key, attrs)
}

// ============================
// 演示函数
// ============================

// demonstrateSpanPool 演示 Span 池
func demonstrateSpanPool(tracer trace.Tracer) {
	log.Println("\n--- Span Pool Demo ---")

	ctx := context.Background()
	var m1, m2 runtime.MemStats

	// 不使用池
	runtime.ReadMemStats(&m1)
	start := time.Now()

	for i := range 10000 {
		_, span := tracer.Start(ctx, fmt.Sprintf("operation-%d", i))
		span.SetAttributes(
			attribute.String("type", "test"),
			attribute.Int("iteration", i),
		)
		span.End()
	}

	withoutPoolDuration := time.Since(start)
	runtime.ReadMemStats(&m2)
	allocWithoutPool := m2.TotalAlloc - m1.TotalAlloc

	// 使用池
	runtime.ReadMemStats(&m1)
	start = time.Now()

	for i := range 10000 {
		ps := AcquireSpan(tracer, ctx, fmt.Sprintf("pooled-operation-%d", i))
		ps.SetAttribute(attribute.String("type", "test"))
		ps.SetAttribute(attribute.Int("iteration", i))
		ps.Release()
	}

	withPoolDuration := time.Since(start)
	runtime.ReadMemStats(&m2)
	allocWithPool := m2.TotalAlloc - m1.TotalAlloc

	log.Printf("📊 Without Pool: %v, Alloc: %d bytes", withoutPoolDuration, allocWithoutPool)
	log.Printf("📊 With Pool:    %v, Alloc: %d bytes", withPoolDuration, allocWithPool)
	log.Printf("🚀 Improvement:  %.2fx faster, %.2fx less allocation\n",
		float64(withoutPoolDuration)/float64(withPoolDuration),
		float64(allocWithoutPool)/float64(allocWithPool+1))
}

// demonstrateWorkerPool 演示 Worker 池
func demonstrateWorkerPool(tracer trace.Tracer) {
	log.Println("\n--- Worker Pool Demo ---")

	ctx := context.Background()
	pool := NewWorkerPool(4, 100)
	defer pool.Stop()

	var counter LockFreeCounter

	// 提交任务
	start := time.Now()
	for i := range 1000 {
		taskID := i
		pool.Submit(func() {
			ps := AcquireSpan(tracer, ctx, fmt.Sprintf("worker-task-%d", taskID))
			ps.SetAttribute(attribute.String("worker", "pool"))
			ps.SetAttribute(attribute.Int("task_id", taskID))

			// 模拟工作
			time.Sleep(time.Microsecond * 100)

			ps.Release()
			counter.Inc()
		})
	}

	// 等待完成
	for counter.Get() < 1000 {
		time.Sleep(time.Millisecond * 10)
	}

	duration := time.Since(start)
	log.Printf("📊 Processed %d tasks in %v", counter.Get(), duration)
	log.Printf("📊 Throughput: %.0f tasks/sec\n", float64(counter.Get())/duration.Seconds())
}

// demonstrateAttributeCache 演示属性缓存
func demonstrateAttributeCache(tracer trace.Tracer) {
	log.Println("\n--- Attribute Cache Demo ---")

	ctx := context.Background()
	cache := NewAttributeCache()

	// 预先缓存常用属性
	commonAttrs := []attribute.KeyValue{
		attribute.String("service", "api"),
		attribute.String("environment", "production"),
		attribute.String("version", "1.0.0"),
	}
	cache.Set("common", commonAttrs)

	// 使用缓存
	start := time.Now()
	for i := range 1000 {
		ps := AcquireSpan(tracer, ctx, fmt.Sprintf("cached-operation-%d", i))

		// 从缓存获取属性
		if attrs, ok := cache.Get("common"); ok {
			for _, attr := range attrs {
				ps.SetAttribute(attr)
			}
		}

		ps.SetAttribute(attribute.Int("iteration", i))
		ps.Release()
	}
	duration := time.Since(start)

	log.Printf("📊 Processed 1000 operations with cache in %v\n", duration)
}

// demonstrateBatchExport 演示批量导出
func demonstrateBatchExport(tracer trace.Tracer) {
	log.Println("\n--- Batch Export Demo ---")

	ctx := context.Background()

	// 生成大量 Span
	start := time.Now()
	for i := range 5000 {
		ps := AcquireSpan(tracer, ctx, fmt.Sprintf("batch-operation-%d", i))
		ps.SetAttribute(attribute.String("type", "batch"))
		ps.SetAttribute(attribute.Int("id", i))
		ps.Release()
	}
	duration := time.Since(start)

	log.Printf("📊 Generated 5000 spans in %v", duration)
	log.Printf("📊 Rate: %.0f spans/sec\n", 5000.0/duration.Seconds())
}

// demonstrateMemoryEfficiency 演示内存效率
func demonstrateMemoryEfficiency(tracer trace.Tracer) {
	log.Println("\n--- Memory Efficiency Demo ---")

	ctx := context.Background()

	// 获取初始内存状态
	runtime.GC()
	var m1 runtime.MemStats
	runtime.ReadMemStats(&m1)

	// 执行大量操作
	for i := range 10000 {
		ps := AcquireSpan(tracer, ctx, "memory-test")
		ps.SetAttribute(attribute.String("test", "memory"))
		ps.SetAttribute(attribute.Int("id", i))
		ps.Release()
	}

	// 获取最终内存状态
	runtime.GC()
	var m2 runtime.MemStats
	runtime.ReadMemStats(&m2)

	log.Printf("📊 Memory Stats:")
	log.Printf("   Alloc:      %d MB", (m2.Alloc-m1.Alloc)/1024/1024)
	log.Printf("   TotalAlloc: %d MB", (m2.TotalAlloc-m1.TotalAlloc)/1024/1024)
	log.Printf("   NumGC:      %d", m2.NumGC-m1.NumGC)
	log.Println()
}

// ============================
// Main
// ============================

func main() {
	// 设置 GOMAXPROCS
	runtime.GOMAXPROCS(runtime.NumCPU())

	log.Println("\n" + strings.Repeat("=", 80))
	log.Println("🚀 Performance Tuning Demo")
	log.Println(strings.Repeat("=", 80) + "\n")

	// 初始化 TracerProvider
	_, err := stdouttrace.New(
		stdouttrace.WithPrettyPrint(),
		stdouttrace.WithoutTimestamps(), // 减少输出噪音
	)
	if err != nil {
		log.Fatalf("Failed to create exporter: %v", err)
	}

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("performance-tuning-demo"),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	// 使用批量导出器
	batchExporter := NewBatchExporter(100, time.Second)

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithSpanProcessor(sdktrace.NewBatchSpanProcessor(batchExporter)),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(sdktrace.AlwaysSample()),
	)
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Fatalf("Failed to shutdown tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)
	tracer := tp.Tracer("performance-tuning")

	// 演示1: Span 池
	demonstrateSpanPool(tracer)

	// 演示2: Worker 池
	demonstrateWorkerPool(tracer)

	// 演示3: 属性缓存
	demonstrateAttributeCache(tracer)

	// 演示4: 批量导出
	demonstrateBatchExport(tracer)

	// 演示5: 内存效率
	demonstrateMemoryEfficiency(tracer)

	// 等待批量导出完成
	time.Sleep(time.Second * 2)

	log.Println(strings.Repeat("=", 80))
	log.Println("✅ All demos completed successfully")
	log.Println(strings.Repeat("=", 80))

	// 打印最终统计
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	log.Printf("\n📊 Final Memory Stats:")
	log.Printf("   Alloc:      %d MB", m.Alloc/1024/1024)
	log.Printf("   TotalAlloc: %d MB", m.TotalAlloc/1024/1024)
	log.Printf("   Sys:        %d MB", m.Sys/1024/1024)
	log.Printf("   NumGC:      %d", m.NumGC)
	log.Printf("   Goroutines: %d", runtime.NumGoroutine())
}

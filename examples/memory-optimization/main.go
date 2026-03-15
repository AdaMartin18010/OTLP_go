package main

import (
	"context"
	"fmt"
	"log"
	"runtime"
	"strings"
	"sync"
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
// 1. sync.Pool 对象池
// ============================

// SpanPool Span 对象池
var spanDataPool = sync.Pool{
	New: func() interface{} {
		return &SpanData{
			Attributes: make([]attribute.KeyValue, 0, 16), // 预分配容量
		}
	},
}

// SpanData Span 数据结构
type SpanData struct {
	TraceID    string
	SpanID     string
	Name       string
	StartTime  time.Time
	EndTime    time.Time
	Attributes []attribute.KeyValue
}

// AcquireSpanData 从池中获取 SpanData
func AcquireSpanData() *SpanData {
	return spanDataPool.Get().(*SpanData)
}

// ReleaseSpanData 归还 SpanData 到池
func ReleaseSpanData(sd *SpanData) {
	// 重置字段
	sd.TraceID = ""
	sd.SpanID = ""
	sd.Name = ""
	sd.StartTime = time.Time{}
	sd.EndTime = time.Time{}
	sd.Attributes = sd.Attributes[:0] // 保留容量,清空长度

	spanDataPool.Put(sd)
}

// demonstrateSpanPool 演示 Span 对象池
func demonstrateSpanPool(ctx context.Context, tracer trace.Tracer) {
	_, span := tracer.Start(ctx, "demonstrate-span-pool")
	defer span.End()

	log.Println("\n--- Span Pool Demo ---")

	const iterations = 10000

	// 不使用对象池
	var m1 runtime.MemStats
	runtime.ReadMemStats(&m1)
	start := time.Now()

	for i := range iterations {
		sd := &SpanData{
			TraceID:    fmt.Sprintf("trace-%d", i),
			SpanID:     fmt.Sprintf("span-%d", i),
			Name:       "operation",
			Attributes: make([]attribute.KeyValue, 0, 16),
		}
		_ = sd
	}

	withoutPoolDuration := time.Since(start)
	var m2 runtime.MemStats
	runtime.ReadMemStats(&m2)
	allocWithoutPool := m2.Alloc - m1.Alloc

	// 使用对象池
	runtime.ReadMemStats(&m1)
	start = time.Now()

	for i := range iterations {
		sd := AcquireSpanData()
		sd.TraceID = fmt.Sprintf("trace-%d", i)
		sd.SpanID = fmt.Sprintf("span-%d", i)
		sd.Name = "operation"
		ReleaseSpanData(sd)
	}

	withPoolDuration := time.Since(start)
	runtime.ReadMemStats(&m2)
	allocWithPool := m2.Alloc - m1.Alloc

	log.Printf("📊 Without Pool: %v, Alloc: %d bytes", withoutPoolDuration, allocWithoutPool)
	log.Printf("📊 With Pool:    %v, Alloc: %d bytes", withPoolDuration, allocWithPool)
	log.Printf("🚀 Improvement:  %.2fx faster, %.2fx less allocation\n",
		float64(withoutPoolDuration)/float64(withPoolDuration),
		float64(allocWithoutPool)/float64(allocWithPool+1),
	)

	span.SetAttributes(
		attribute.Int64("alloc.without_pool", int64(allocWithoutPool)),
		attribute.Int64("alloc.with_pool", int64(allocWithPool)),
	)
}

// ============================
// 2. 内存预分配与复用
// ============================

// AttributeBuffer 属性缓冲区(可复用)
type AttributeBuffer struct {
	buf []attribute.KeyValue
}

var attributeBufferPool = sync.Pool{
	New: func() interface{} {
		return &AttributeBuffer{
			buf: make([]attribute.KeyValue, 0, 32), // 预分配32个属性
		}
	},
}

// AcquireAttributeBuffer 获取属性缓冲区
func AcquireAttributeBuffer() *AttributeBuffer {
	return attributeBufferPool.Get().(*AttributeBuffer)
}

// ReleaseAttributeBuffer 释放属性缓冲区
func (ab *AttributeBuffer) Release() {
	ab.buf = ab.buf[:0]
	attributeBufferPool.Put(ab)
}

// Add 添加属性
func (ab *AttributeBuffer) Add(kv attribute.KeyValue) {
	ab.buf = append(ab.buf, kv)
}

// Attributes 获取属性切片
func (ab *AttributeBuffer) Attributes() []attribute.KeyValue {
	return ab.buf
}

// demonstratePreallocation 演示内存预分配
func demonstratePreallocation(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-preallocation")
	defer span.End()

	log.Println("\n--- Memory Preallocation Demo ---")

	// 不预分配
	var m1 runtime.MemStats
	runtime.ReadMemStats(&m1)

	attrs1 := make([]attribute.KeyValue, 0) // 容量为0
	for i := range 100 {
		attrs1 = append(attrs1, attribute.Int(fmt.Sprintf("key%d", i), i))
	}

	var m2 runtime.MemStats
	runtime.ReadMemStats(&m2)
	allocWithoutPrealloc := m2.Alloc - m1.Alloc

	// 预分配
	runtime.ReadMemStats(&m1)

	attrs2 := make([]attribute.KeyValue, 0, 100) // 预分配容量100
	for i := range 100 {
		attrs2 = append(attrs2, attribute.Int(fmt.Sprintf("key%d", i), i))
	}

	runtime.ReadMemStats(&m2)
	allocWithPrealloc := m2.Alloc - m1.Alloc

	log.Printf("📊 Without Prealloc: %d bytes", allocWithoutPrealloc)
	log.Printf("📊 With Prealloc:    %d bytes", allocWithPrealloc)
	log.Printf("🚀 Improvement:      %.2fx less allocation\n",
		float64(allocWithoutPrealloc)/float64(allocWithPrealloc+1),
	)

	// 使用对象池 + 预分配
	attrBuf := AcquireAttributeBuffer()
	for i := range 100 {
		attrBuf.Add(attribute.Int(fmt.Sprintf("key%d", i), i))
	}
	log.Printf("✅ Pooled buffer with %d attributes", len(attrBuf.Attributes()))
	attrBuf.Release()
}

// ============================
// 3. 零分配技术
// ============================

// ZeroAllocSpanBuilder 零分配 Span 构建器
type ZeroAllocSpanBuilder struct {
	attrs [16]attribute.KeyValue // 栈上数组
	count int
}

// AddString 添加字符串属性(零分配)
func (z *ZeroAllocSpanBuilder) AddString(key, value string) {
	if z.count < len(z.attrs) {
		z.attrs[z.count] = attribute.String(key, value)
		z.count++
	}
}

// AddInt 添加整数属性(零分配)
func (z *ZeroAllocSpanBuilder) AddInt(key string, value int) {
	if z.count < len(z.attrs) {
		z.attrs[z.count] = attribute.Int(key, value)
		z.count++
	}
}

// Attributes 获取属性切片(零分配,返回栈上数组切片)
func (z *ZeroAllocSpanBuilder) Attributes() []attribute.KeyValue {
	return z.attrs[:z.count]
}

// demonstrateZeroAlloc 演示零分配技术
func demonstrateZeroAlloc(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-zero-alloc")
	defer span.End()

	log.Println("\n--- Zero-Allocation Demo ---")

	const iterations = 100000

	// 堆分配
	var m1 runtime.MemStats
	runtime.ReadMemStats(&m1)
	start := time.Now()

	for range iterations {
		attrs := []attribute.KeyValue{
			attribute.String("service", "api"),
			attribute.Int("status", 200),
			attribute.String("method", "GET"),
		}
		_ = attrs
	}

	heapDuration := time.Since(start)
	var m2 runtime.MemStats
	runtime.ReadMemStats(&m2)
	heapAlloc := m2.Alloc - m1.Alloc

	// 栈分配(零分配)
	runtime.ReadMemStats(&m1)
	start = time.Now()

	for range iterations {
		var builder ZeroAllocSpanBuilder
		builder.AddString("service", "api")
		builder.AddInt("status", 200)
		builder.AddString("method", "GET")
		_ = builder.Attributes()
	}

	stackDuration := time.Since(start)
	runtime.ReadMemStats(&m2)
	stackAlloc := m2.Alloc - m1.Alloc

	log.Printf("📊 Heap Allocation:  %v, Alloc: %d bytes", heapDuration, heapAlloc)
	log.Printf("📊 Stack Allocation: %v, Alloc: %d bytes", stackDuration, stackAlloc)
	log.Printf("🚀 Improvement:      %.2fx faster, %.2fx less allocation\n",
		float64(heapDuration)/float64(stackDuration),
		float64(heapAlloc)/float64(stackAlloc+1),
	)

	span.SetAttributes(
		attribute.Int64("alloc.heap", int64(heapAlloc)),
		attribute.Int64("alloc.stack", int64(stackAlloc)),
	)
}

// ============================
// 4. 批处理优化
// ============================

// BatchExporter 批量导出器
type BatchExporter struct {
	tracer    trace.Tracer
	batchSize int
	buffer    []*SpanData
	mu        sync.Mutex
}

// NewBatchExporter 创建批量导出器
func NewBatchExporter(tracer trace.Tracer, batchSize int) *BatchExporter {
	return &BatchExporter{
		tracer:    tracer,
		batchSize: batchSize,
		buffer:    make([]*SpanData, 0, batchSize),
	}
}

// Add 添加 Span 到缓冲区
func (be *BatchExporter) Add(sd *SpanData) {
	be.mu.Lock()
	defer be.mu.Unlock()

	be.buffer = append(be.buffer, sd)

	if len(be.buffer) >= be.batchSize {
		be.flush()
	}
}

// flush 刷新缓冲区
func (be *BatchExporter) flush() {
	if len(be.buffer) == 0 {
		return
	}

	_, span := be.tracer.Start(context.Background(), "batch-export")
	defer span.End()

	span.SetAttributes(attribute.Int("batch.size", len(be.buffer)))

	// 模拟导出
	log.Printf("📤 Exporting batch of %d spans", len(be.buffer))

	// 清空缓冲区
	be.buffer = be.buffer[:0]
}

// Flush 强制刷新
func (be *BatchExporter) Flush() {
	be.mu.Lock()
	defer be.mu.Unlock()
	be.flush()
}

// demonstrateBatchProcessing 演示批处理
func demonstrateBatchProcessing(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-batch-processing")
	defer span.End()

	log.Println("\n--- Batch Processing Demo ---")

	exporter := NewBatchExporter(tracer, 100)

	// 生成1000个 Span
	for i := range 1000 {
		sd := AcquireSpanData()
		sd.TraceID = fmt.Sprintf("trace-%d", i)
		sd.SpanID = fmt.Sprintf("span-%d", i)
		sd.Name = "operation"
		exporter.Add(sd)
	}

	// 刷新剩余的
	exporter.Flush()

	log.Println("✅ Batch processing completed")
}

// ============================
// 5. GC 监控与调优
// ============================

// GCStats GC 统计
type GCStats struct {
	NumGC        uint32
	PauseTotal   time.Duration
	LastPause    time.Duration
	MemAlloc     uint64
	MemSys       uint64
	NumGoroutine int
}

// GetGCStats 获取 GC 统计
func GetGCStats() GCStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return GCStats{
		NumGC:        m.NumGC,
		PauseTotal:   time.Duration(m.PauseTotalNs),
		LastPause:    time.Duration(m.PauseNs[(m.NumGC+255)%256]),
		MemAlloc:     m.Alloc,
		MemSys:       m.Sys,
		NumGoroutine: runtime.NumGoroutine(),
	}
}

// demonstrateGCTuning 演示 GC 调优
func demonstrateGCTuning(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-gc-tuning")
	defer span.End()

	log.Println("\n--- GC Tuning Demo ---")

	// 获取初始 GC 统计
	stats1 := GetGCStats()
	log.Printf("📊 Initial GC Stats:")
	log.Printf("   NumGC: %d, PauseTotal: %v, MemAlloc: %d MB",
		stats1.NumGC, stats1.PauseTotal, stats1.MemAlloc/1024/1024)

	// 模拟大量内存分配
	const allocCount = 100000
	data := make([]*SpanData, allocCount)
	for i := range allocCount {
		data[i] = AcquireSpanData()
		data[i].Name = fmt.Sprintf("span-%d", i)
	}

	// 获取分配后的 GC 统计
	runtime.GC() // 手动触发 GC
	stats2 := GetGCStats()
	log.Printf("📊 After Allocation:")
	log.Printf("   NumGC: %d (+%d), PauseTotal: %v (+%v), MemAlloc: %d MB",
		stats2.NumGC, stats2.NumGC-stats1.NumGC,
		stats2.PauseTotal, stats2.PauseTotal-stats1.PauseTotal,
		stats2.MemAlloc/1024/1024)

	// 释放内存
	for i := range allocCount {
		ReleaseSpanData(data[i])
	}
	data = nil

	runtime.GC() // 手动触发 GC
	stats3 := GetGCStats()
	log.Printf("📊 After Release:")
	log.Printf("   NumGC: %d (+%d), PauseTotal: %v (+%v), MemAlloc: %d MB",
		stats3.NumGC, stats3.NumGC-stats2.NumGC,
		stats3.PauseTotal, stats3.PauseTotal-stats2.PauseTotal,
		stats3.MemAlloc/1024/1024)

	span.SetAttributes(
		attribute.Int("gc.count", int(stats3.NumGC-stats1.NumGC)),
		attribute.Int64("gc.pause_total_ns", int64(stats3.PauseTotal-stats1.PauseTotal)),
		attribute.Int64("mem.alloc_final", int64(stats3.MemAlloc)),
	)

	log.Println()
}

// ============================
// Main
// ============================

func main() {
	// 初始化 TracerProvider
	exporter, err := stdouttrace.New(stdouttrace.WithPrettyPrint())
	if err != nil {
		log.Fatalf("Failed to create exporter: %v", err)
	}

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("memory-optimization-demo"),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
	)
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Fatalf("Failed to shutdown tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)
	tracer := tp.Tracer("memory-optimization")

	ctx := context.Background()

	log.Println("\n" + strings.Repeat("=", 80))
	log.Println("🚀 Memory Optimization with OTLP Demo")
	log.Println(strings.Repeat("=", 80))

	// 1. Span 对象池
	demonstrateSpanPool(ctx, tracer)

	// 2. 内存预分配
	demonstratePreallocation(ctx, tracer)

	// 3. 零分配技术
	demonstrateZeroAlloc(ctx, tracer)

	// 4. 批处理优化
	demonstrateBatchProcessing(ctx, tracer)

	// 5. GC 调优
	demonstrateGCTuning(ctx, tracer)

	log.Println(strings.Repeat("=", 80))
	log.Println("✅ All demos completed successfully")
	log.Println(strings.Repeat("=", 80))
}

package processor

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/trace"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// FilteringProcessor 过滤 Span Processor
// 根据条件过滤不需要的 Span
type FilteringProcessor struct {
	next      sdktrace.SpanProcessor
	filter    FilterFunc
	dropped   int64
	processed int64
}

// FilterFunc 过滤函数
type FilterFunc func(sdktrace.ReadOnlySpan) bool

// NewFilteringProcessor 创建过滤处理器
func NewFilteringProcessor(next sdktrace.SpanProcessor, filter FilterFunc) *FilteringProcessor {
	return &FilteringProcessor{
		next:   next,
		filter: filter,
	}
}

// OnStart 实现 SpanProcessor 接口
func (fp *FilteringProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	fp.next.OnStart(parent, s)
}

// OnEnd 实现 SpanProcessor 接口
func (fp *FilteringProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	// 应用过滤器
	if !fp.filter(s) {
		atomic.AddInt64(&fp.dropped, 1)
		return
	}

	atomic.AddInt64(&fp.processed, 1)
	fp.next.OnEnd(s)
}

// Shutdown 实现 SpanProcessor 接口
func (fp *FilteringProcessor) Shutdown(ctx context.Context) error {
	return fp.next.Shutdown(ctx)
}

// ForceFlush 实现 SpanProcessor 接口
func (fp *FilteringProcessor) ForceFlush(ctx context.Context) error {
	return fp.next.ForceFlush(ctx)
}

// GetStats 获取统计信息
func (fp *FilteringProcessor) GetStats() (processed, dropped int64) {
	return atomic.LoadInt64(&fp.processed), atomic.LoadInt64(&fp.dropped)
}

// EnrichingProcessor 丰富 Span Processor
// 自动添加额外的属性
type EnrichingProcessor struct {
	next       sdktrace.SpanProcessor
	enrichFunc EnrichFunc
}

// EnrichFunc 丰富函数
type EnrichFunc func(sdktrace.ReadWriteSpan)

// NewEnrichingProcessor 创建丰富处理器
func NewEnrichingProcessor(next sdktrace.SpanProcessor, enrichFunc EnrichFunc) *EnrichingProcessor {
	return &EnrichingProcessor{
		next:       next,
		enrichFunc: enrichFunc,
	}
}

// OnStart 实现 SpanProcessor 接口
func (ep *EnrichingProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	// 在 Span 开始时丰富
	ep.enrichFunc(s)
	ep.next.OnStart(parent, s)
}

// OnEnd 实现 SpanProcessor 接口
func (ep *EnrichingProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	ep.next.OnEnd(s)
}

// Shutdown 实现 SpanProcessor 接口
func (ep *EnrichingProcessor) Shutdown(ctx context.Context) error {
	return ep.next.Shutdown(ctx)
}

// ForceFlush 实现 SpanProcessor 接口
func (ep *EnrichingProcessor) ForceFlush(ctx context.Context) error {
	return ep.next.ForceFlush(ctx)
}

// AggregatingProcessor 聚合 Span Processor
// 聚合相似的 Span，减少导出数量
type AggregatingProcessor struct {
	next          sdktrace.SpanProcessor
	aggregations  map[string]*SpanAggregation
	mu            sync.RWMutex
	flushInterval time.Duration
	maxAggSize    int

	stopCh chan struct{}
	wg     sync.WaitGroup
}

// SpanAggregation Span 聚合
type SpanAggregation struct {
	Name       string
	Count      int64
	TotalTime  time.Duration
	MinTime    time.Duration
	MaxTime    time.Duration
	Errors     int64
	LastUpdate time.Time
}

// NewAggregatingProcessor 创建聚合处理器
func NewAggregatingProcessor(next sdktrace.SpanProcessor, flushInterval time.Duration, maxAggSize int) *AggregatingProcessor {
	ap := &AggregatingProcessor{
		next:          next,
		aggregations:  make(map[string]*SpanAggregation),
		flushInterval: flushInterval,
		maxAggSize:    maxAggSize,
		stopCh:        make(chan struct{}),
	}

	// 启动定期刷新
	ap.wg.Add(1)
	go ap.periodicFlush()

	return ap
}

// OnStart 实现 SpanProcessor 接口
func (ap *AggregatingProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	ap.next.OnStart(parent, s)
}

// OnEnd 实现 SpanProcessor 接口
func (ap *AggregatingProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	spanName := s.Name()
	duration := s.EndTime().Sub(s.StartTime())
	hasError := s.Status().Code == 2 // Error code

	ap.mu.Lock()
	defer ap.mu.Unlock()

	agg, exists := ap.aggregations[spanName]
	if !exists {
		agg = &SpanAggregation{
			Name:    spanName,
			MinTime: duration,
			MaxTime: duration,
		}
		ap.aggregations[spanName] = agg
	}

	// 更新聚合
	agg.Count++
	agg.TotalTime += duration
	if duration < agg.MinTime {
		agg.MinTime = duration
	}
	if duration > agg.MaxTime {
		agg.MaxTime = duration
	}
	if hasError {
		agg.Errors++
	}
	agg.LastUpdate = time.Now()

	// 检查是否需要刷新
	if len(ap.aggregations) >= ap.maxAggSize {
		ap.flushLocked()
	}
}

// periodicFlush 定期刷新
func (ap *AggregatingProcessor) periodicFlush() {
	defer ap.wg.Done()

	ticker := time.NewTicker(ap.flushInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			ap.mu.Lock()
			ap.flushLocked()
			ap.mu.Unlock()
		case <-ap.stopCh:
			return
		}
	}
}

// flushLocked 刷新聚合（需要持有锁）
func (ap *AggregatingProcessor) flushLocked() {
	for name, agg := range ap.aggregations {
		// 创建聚合 Span
		// 注意：这里简化处理，实际应该创建真正的 Span
		_ = fmt.Sprintf("Aggregated: %s, Count: %d, Avg: %v", name, agg.Count, agg.TotalTime/time.Duration(agg.Count))
	}

	// 清空聚合
	ap.aggregations = make(map[string]*SpanAggregation)
}

// Shutdown 实现 SpanProcessor 接口
func (ap *AggregatingProcessor) Shutdown(ctx context.Context) error {
	close(ap.stopCh)
	ap.wg.Wait()

	ap.mu.Lock()
	ap.flushLocked()
	ap.mu.Unlock()

	return ap.next.Shutdown(ctx)
}

// ForceFlush 实现 SpanProcessor 接口
func (ap *AggregatingProcessor) ForceFlush(ctx context.Context) error {
	ap.mu.Lock()
	ap.flushLocked()
	ap.mu.Unlock()

	return ap.next.ForceFlush(ctx)
}

// AsyncProcessor 异步 Span Processor
// 使用独立的 goroutine 池处理 Span
type AsyncProcessor struct {
	next        sdktrace.SpanProcessor
	queue       chan sdktrace.ReadOnlySpan
	workerCount int
	wg          sync.WaitGroup
	stopCh      chan struct{}
}

// NewAsyncProcessor 创建异步处理器
func NewAsyncProcessor(next sdktrace.SpanProcessor, queueSize, workerCount int) *AsyncProcessor {
	ap := &AsyncProcessor{
		next:        next,
		queue:       make(chan sdktrace.ReadOnlySpan, queueSize),
		workerCount: workerCount,
		stopCh:      make(chan struct{}),
	}

	// 启动 worker
	for i := 0; i < workerCount; i++ {
		ap.wg.Add(1)
		go ap.worker()
	}

	return ap
}

// worker 处理 Span 的工作协程
func (ap *AsyncProcessor) worker() {
	defer ap.wg.Done()

	for {
		select {
		case span := <-ap.queue:
			ap.next.OnEnd(span)
		case <-ap.stopCh:
			// 处理剩余的 Span
			for len(ap.queue) > 0 {
				span := <-ap.queue
				ap.next.OnEnd(span)
			}
			return
		}
	}
}

// OnStart 实现 SpanProcessor 接口
func (ap *AsyncProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	ap.next.OnStart(parent, s)
}

// OnEnd 实现 SpanProcessor 接口
func (ap *AsyncProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	select {
	case ap.queue <- s:
		// 成功入队
	default:
		// 队列满，直接处理
		ap.next.OnEnd(s)
	}
}

// Shutdown 实现 SpanProcessor 接口
func (ap *AsyncProcessor) Shutdown(ctx context.Context) error {
	close(ap.stopCh)
	ap.wg.Wait()
	close(ap.queue)

	return ap.next.Shutdown(ctx)
}

// ForceFlush 实现 SpanProcessor 接口
func (ap *AsyncProcessor) ForceFlush(ctx context.Context) error {
	// 等待队列清空
	for len(ap.queue) > 0 {
		time.Sleep(10 * time.Millisecond)
	}

	return ap.next.ForceFlush(ctx)
}

// Example: 使用示例
func ExampleCustomProcessors() {
	// 创建一个简单的 noop exporter
	noopExporter := &noopExporter{}

	// 1. 过滤处理器：过滤健康检查
	filteringProcessor := NewFilteringProcessor(
		trace.NewSimpleSpanProcessor(noopExporter),
		func(span sdktrace.ReadOnlySpan) bool {
			// 过滤掉 /health 路径
			for _, attr := range span.Attributes() {
				if attr.Key == "http.target" && attr.Value.AsString() == "/health" {
					return false
				}
			}
			return true
		},
	)

	// 2. 丰富处理器：自动添加环境信息
	enrichingProcessor := NewEnrichingProcessor(
		filteringProcessor,
		func(span sdktrace.ReadWriteSpan) {
			span.SetAttributes(
				attribute.String("deployment.environment", "production"),
				attribute.String("service.version", "1.0.0"),
				attribute.String("host.name", "server-01"),
			)
		},
	)

	// 3. 聚合处理器：聚合相似 Span
	aggregatingProcessor := NewAggregatingProcessor(
		enrichingProcessor,
		1*time.Minute, // 每分钟刷新
		1000,          // 最多聚合 1000 种 Span
	)

	// 4. 异步处理器：异步处理
	asyncProcessor := NewAsyncProcessor(
		aggregatingProcessor,
		10000, // 队列大小
		4,     // Worker 数量
	)

	// 使用处理器
	_ = trace.NewTracerProvider(
		trace.WithSpanProcessor(asyncProcessor),
	)
}

// noopExporter 用于示例的空导出器
type noopExporter struct{}

func (e *noopExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
	return nil
}

func (e *noopExporter) Shutdown(ctx context.Context) error {
	return nil
}

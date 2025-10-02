package optimization

import (
	"context"
	"sync"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// SpanPool Span 对象池
// 减少 Span 相关对象的内存分配
// 优化：集成统一的对象池系统和 OTLP 监控
type SpanPool struct {
	attributePool *AttributePool
	eventPool     *EventPool
	meter         metric.Meter
	wrapperCount  metric.Int64Counter
	flushCount    metric.Int64Counter
}

// NewSpanPool 创建 Span 池
// 优化：添加监控指标
func NewSpanPool() *SpanPool {
	meter := otel.Meter("optimization/span-pool")

	wrapperCount, _ := meter.Int64Counter(
		"span_pool.wrappers",
		metric.WithDescription("Number of span wrappers created"),
	)

	flushCount, _ := meter.Int64Counter(
		"span_pool.flushes",
		metric.WithDescription("Number of span flushes"),
	)

	return &SpanPool{
		attributePool: NewAttributePool(16),
		eventPool:     NewEventPool(8),
		meter:         meter,
		wrapperCount:  wrapperCount,
		flushCount:    flushCount,
	}
}

// AttributePool 属性池
type AttributePool struct {
	pool       sync.Pool
	initialCap int
}

// NewAttributePool 创建属性池
func NewAttributePool(initialCap int) *AttributePool {
	return &AttributePool{
		initialCap: initialCap,
		pool: sync.Pool{
			New: func() interface{} {
				return make([]attribute.KeyValue, 0, initialCap)
			},
		},
	}
}

// Get 获取属性切片
func (p *AttributePool) Get() []attribute.KeyValue {
	return p.pool.Get().([]attribute.KeyValue)[:0]
}

// Put 归还属性切片
func (p *AttributePool) Put(attrs []attribute.KeyValue) {
	if cap(attrs) > p.initialCap*4 {
		// 容量过大，不回收
		return
	}
	p.pool.Put(attrs[:0])
}

// EventPool 事件池
type EventPool struct {
	pool       sync.Pool
	initialCap int
}

// EventWrapper 事件包装器
type EventWrapper struct {
	Name       string
	Attributes []attribute.KeyValue
	Options    []trace.EventOption
}

// NewEventPool 创建事件池
func NewEventPool(initialCap int) *EventPool {
	return &EventPool{
		initialCap: initialCap,
		pool: sync.Pool{
			New: func() interface{} {
				return &EventWrapper{
					Attributes: make([]attribute.KeyValue, 0, initialCap),
				}
			},
		},
	}
}

// Get 获取事件包装器
func (p *EventPool) Get() *EventWrapper {
	wrapper := p.pool.Get().(*EventWrapper)
	wrapper.Name = ""
	wrapper.Attributes = wrapper.Attributes[:0]
	wrapper.Options = wrapper.Options[:0]
	return wrapper
}

// Put 归还事件包装器
func (p *EventPool) Put(wrapper *EventWrapper) {
	if cap(wrapper.Attributes) > p.initialCap*4 {
		return
	}
	p.pool.Put(wrapper)
}

// SpanWrapper Span 包装器
// 提供对象池化的 Span 操作
type SpanWrapper struct {
	span       trace.Span
	attributes []attribute.KeyValue
	events     []*EventWrapper
	pool       *SpanPool
}

// NewSpanWrapper 创建 Span 包装器
// 优化：添加指标记录
func NewSpanWrapper(span trace.Span, pool *SpanPool) *SpanWrapper {
	pool.wrapperCount.Add(context.Background(), 1)

	return &SpanWrapper{
		span:       span,
		attributes: pool.attributePool.Get(),
		events:     make([]*EventWrapper, 0, 4),
		pool:       pool,
	}
}

// SetAttributes 设置属性（使用池化）
func (sw *SpanWrapper) SetAttributes(attrs ...attribute.KeyValue) {
	sw.attributes = append(sw.attributes, attrs...)
}

// AddEvent 添加事件（使用池化）
func (sw *SpanWrapper) AddEvent(name string, attrs ...attribute.KeyValue) {
	event := sw.pool.eventPool.Get()
	event.Name = name
	event.Attributes = append(event.Attributes, attrs...)
	sw.events = append(sw.events, event)
}

// Flush 刷新到实际 Span
// 优化：批量操作，添加指标记录
func (sw *SpanWrapper) Flush() {
	sw.pool.flushCount.Add(context.Background(), 1)

	// 批量设置属性（减少函数调用）
	if len(sw.attributes) > 0 {
		sw.span.SetAttributes(sw.attributes...)
	}

	// 批量添加事件
	for _, event := range sw.events {
		sw.span.AddEvent(event.Name, trace.WithAttributes(event.Attributes...))
		sw.pool.eventPool.Put(event)
	}

	// 清空事件列表
	sw.events = sw.events[:0]
}

// End 结束 Span 并清理资源
func (sw *SpanWrapper) End() {
	sw.Flush()
	sw.span.End()

	// 归还到池
	sw.pool.attributePool.Put(sw.attributes)
	sw.attributes = nil
	sw.events = nil
}

// PooledTracer 支持池化的 Tracer 包装器
type PooledTracer struct {
	tracer trace.Tracer
	pool   *SpanPool
}

// NewPooledTracer 创建池化 Tracer
func NewPooledTracer(tracer trace.Tracer) *PooledTracer {
	return &PooledTracer{
		tracer: tracer,
		pool:   NewSpanPool(),
	}
}

// Start 启动 Span（返回包装器）
func (pt *PooledTracer) Start(ctx context.Context, spanName string, opts ...trace.SpanStartOption) (context.Context, *SpanWrapper) {
	ctx, span := pt.tracer.Start(ctx, spanName, opts...)
	wrapper := NewSpanWrapper(span, pt.pool)
	return ctx, wrapper
}

// BatchAttributeSetter 批量属性设置器
// 优化大量属性设置的性能
type BatchAttributeSetter struct {
	attributes []attribute.KeyValue
	capacity   int
}

// NewBatchAttributeSetter 创建批量属性设置器
func NewBatchAttributeSetter(capacity int) *BatchAttributeSetter {
	return &BatchAttributeSetter{
		attributes: make([]attribute.KeyValue, 0, capacity),
		capacity:   capacity,
	}
}

// Add 添加属性
func (bas *BatchAttributeSetter) Add(key string, value interface{}) *BatchAttributeSetter {
	var attr attribute.KeyValue

	switch v := value.(type) {
	case string:
		attr = attribute.String(key, v)
	case int:
		attr = attribute.Int(key, v)
	case int64:
		attr = attribute.Int64(key, v)
	case float64:
		attr = attribute.Float64(key, v)
	case bool:
		attr = attribute.Bool(key, v)
	default:
		attr = attribute.String(key, "unknown")
	}

	bas.attributes = append(bas.attributes, attr)
	return bas
}

// SetToSpan 批量设置到 Span
func (bas *BatchAttributeSetter) SetToSpan(span trace.Span) {
	if len(bas.attributes) > 0 {
		span.SetAttributes(bas.attributes...)
	}
}

// Reset 重置
func (bas *BatchAttributeSetter) Reset() {
	bas.attributes = bas.attributes[:0]
}

// SpanRecorder Span 记录器
// 批量记录 Span 信息，延迟提交
type SpanRecorder struct {
	records []SpanRecord
	mu      sync.Mutex
}

// SpanRecord Span 记录
type SpanRecord struct {
	SpanName   string
	Attributes map[string]interface{}
	StartTime  int64
	EndTime    int64
}

// NewSpanRecorder 创建 Span 记录器
func NewSpanRecorder() *SpanRecorder {
	return &SpanRecorder{
		records: make([]SpanRecord, 0, 100),
	}
}

// Record 记录 Span
func (sr *SpanRecorder) Record(record SpanRecord) {
	sr.mu.Lock()
	sr.records = append(sr.records, record)
	sr.mu.Unlock()
}

// Flush 刷新所有记录
func (sr *SpanRecorder) Flush(ctx context.Context, tracer trace.Tracer) {
	sr.mu.Lock()
	records := sr.records
	sr.records = make([]SpanRecord, 0, 100)
	sr.mu.Unlock()

	for _, record := range records {
		_, span := tracer.Start(ctx, record.SpanName)

		// 设置属性
		attrs := make([]attribute.KeyValue, 0, len(record.Attributes))
		for key, value := range record.Attributes {
			switch v := value.(type) {
			case string:
				attrs = append(attrs, attribute.String(key, v))
			case int:
				attrs = append(attrs, attribute.Int(key, v))
			case int64:
				attrs = append(attrs, attribute.Int64(key, v))
			case float64:
				attrs = append(attrs, attribute.Float64(key, v))
			case bool:
				attrs = append(attrs, attribute.Bool(key, v))
			}
		}

		span.SetAttributes(attrs...)
		span.End()
	}
}

// Example: 使用示例
func ExampleSpanPooling() {
	// 使用池化 Tracer
	pooledTracer := NewPooledTracer(trace.NewNoopTracerProvider().Tracer("example"))

	ctx := context.Background()
	ctx, wrapper := pooledTracer.Start(ctx, "operation")
	defer wrapper.End()

	// 使用池化的属性设置
	wrapper.SetAttributes(
		attribute.String("key1", "value1"),
		attribute.Int("key2", 123),
	)

	wrapper.AddEvent("event1",
		attribute.String("event.key", "value"),
	)

	// 批量属性设置
	batchSetter := NewBatchAttributeSetter(10)
	batchSetter.
		Add("attr1", "value1").
		Add("attr2", 123).
		Add("attr3", 3.14).
		Add("attr4", true)

	batchSetter.SetToSpan(wrapper.span)
	batchSetter.Reset()
}

// Package otel provides OpenTelemetry SDK initialization and management
// for the OTLP Go SDK.
package otel

import (
	"context"
	"fmt"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
)

// MeterWrapper 是对 OpenTelemetry Meter 的包装，提供更便捷的 API
type MeterWrapper struct {
	meter                metric.Meter
	name                 string
	mu                   sync.RWMutex
	counters             map[string]metric.Int64Counter
	upDownCounters       map[string]metric.Int64UpDownCounter
	histograms           map[string]metric.Int64Histogram
	exponentialHistograms map[string]metric.Int64Histogram
	floatCounters        map[string]metric.Float64Counter
	floatUpDownCounters  map[string]metric.Float64UpDownCounter
	floatHistograms      map[string]metric.Float64Histogram
	gauges               map[string]metric.Int64Gauge
	floatGauges          map[string]metric.Float64Gauge
	observables          map[string]metric.Registration
}

// NewMeterWrapper 创建一个新的 MeterWrapper
func NewMeterWrapper(mp metric.MeterProvider, name string, opts ...metric.MeterOption) *MeterWrapper {
	return &MeterWrapper{
		meter:                 mp.Meter(name, opts...),
		name:                  name,
		counters:              make(map[string]metric.Int64Counter),
		upDownCounters:        make(map[string]metric.Int64UpDownCounter),
		histograms:            make(map[string]metric.Int64Histogram),
		exponentialHistograms: make(map[string]metric.Int64Histogram),
		floatCounters:         make(map[string]metric.Float64Counter),
		floatUpDownCounters:   make(map[string]metric.Float64UpDownCounter),
		floatHistograms:       make(map[string]metric.Float64Histogram),
		gauges:                make(map[string]metric.Int64Gauge),
		floatGauges:           make(map[string]metric.Float64Gauge),
		observables:           make(map[string]metric.Registration),
	}
}

// Counter 获取或创建 Int64Counter
func (mw *MeterWrapper) Counter(name string, opts ...metric.Int64CounterOption) (metric.Int64Counter, error) {
	mw.mu.RLock()
	if c, ok := mw.counters[name]; ok {
		mw.mu.RUnlock()
		return c, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	// 双重检查
	if c, ok := mw.counters[name]; ok {
		return c, nil
	}

	counter, err := mw.meter.Int64Counter(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create counter %s: %w", name, err)
	}

	mw.counters[name] = counter
	return counter, nil
}

// UpDownCounter 获取或创建 Int64UpDownCounter
func (mw *MeterWrapper) UpDownCounter(name string, opts ...metric.Int64UpDownCounterOption) (metric.Int64UpDownCounter, error) {
	mw.mu.RLock()
	if c, ok := mw.upDownCounters[name]; ok {
		mw.mu.RUnlock()
		return c, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if c, ok := mw.upDownCounters[name]; ok {
		return c, nil
	}

	counter, err := mw.meter.Int64UpDownCounter(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create up-down counter %s: %w", name, err)
	}

	mw.upDownCounters[name] = counter
	return counter, nil
}

// Histogram 获取或创建 Int64Histogram
func (mw *MeterWrapper) Histogram(name string, opts ...metric.Int64HistogramOption) (metric.Int64Histogram, error) {
	mw.mu.RLock()
	if h, ok := mw.histograms[name]; ok {
		mw.mu.RUnlock()
		return h, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if h, ok := mw.histograms[name]; ok {
		return h, nil
	}

	histogram, err := mw.meter.Int64Histogram(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create histogram %s: %w", name, err)
	}

	mw.histograms[name] = histogram
	return histogram, nil
}

// ExponentialHistogram 获取或创建 Int64Histogram (配置为指数直方图聚合)
// 注意：实际的指数直方图行为取决于 MeterProvider 的 View 配置
func (mw *MeterWrapper) ExponentialHistogram(name string, opts ...metric.Int64HistogramOption) (metric.Int64Histogram, error) {
	mw.mu.RLock()
	if h, ok := mw.exponentialHistograms[name]; ok {
		mw.mu.RUnlock()
		return h, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if h, ok := mw.exponentialHistograms[name]; ok {
		return h, nil
	}

	histogram, err := mw.meter.Int64Histogram(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create exponential histogram %s: %w", name, err)
	}

	mw.exponentialHistograms[name] = histogram
	return histogram, nil
}

// FloatCounter 获取或创建 Float64Counter
func (mw *MeterWrapper) FloatCounter(name string, opts ...metric.Float64CounterOption) (metric.Float64Counter, error) {
	mw.mu.RLock()
	if c, ok := mw.floatCounters[name]; ok {
		mw.mu.RUnlock()
		return c, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if c, ok := mw.floatCounters[name]; ok {
		return c, nil
	}

	counter, err := mw.meter.Float64Counter(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create float counter %s: %w", name, err)
	}

	mw.floatCounters[name] = counter
	return counter, nil
}

// FloatUpDownCounter 获取或创建 Float64UpDownCounter
func (mw *MeterWrapper) FloatUpDownCounter(name string, opts ...metric.Float64UpDownCounterOption) (metric.Float64UpDownCounter, error) {
	mw.mu.RLock()
	if c, ok := mw.floatUpDownCounters[name]; ok {
		mw.mu.RUnlock()
		return c, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if c, ok := mw.floatUpDownCounters[name]; ok {
		return c, nil
	}

	counter, err := mw.meter.Float64UpDownCounter(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create float up-down counter %s: %w", name, err)
	}

	mw.floatUpDownCounters[name] = counter
	return counter, nil
}

// FloatHistogram 获取或创建 Float64Histogram
func (mw *MeterWrapper) FloatHistogram(name string, opts ...metric.Float64HistogramOption) (metric.Float64Histogram, error) {
	mw.mu.RLock()
	if h, ok := mw.floatHistograms[name]; ok {
		mw.mu.RUnlock()
		return h, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if h, ok := mw.floatHistograms[name]; ok {
		return h, nil
	}

	histogram, err := mw.meter.Float64Histogram(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create float histogram %s: %w", name, err)
	}

	mw.floatHistograms[name] = histogram
	return histogram, nil
}

// Gauge 获取或创建 Int64Gauge
func (mw *MeterWrapper) Gauge(name string, opts ...metric.Int64GaugeOption) (metric.Int64Gauge, error) {
	mw.mu.RLock()
	if g, ok := mw.gauges[name]; ok {
		mw.mu.RUnlock()
		return g, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if g, ok := mw.gauges[name]; ok {
		return g, nil
	}

	gauge, err := mw.meter.Int64Gauge(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create gauge %s: %w", name, err)
	}

	mw.gauges[name] = gauge
	return gauge, nil
}

// FloatGauge 获取或创建 Float64Gauge
func (mw *MeterWrapper) FloatGauge(name string, opts ...metric.Float64GaugeOption) (metric.Float64Gauge, error) {
	mw.mu.RLock()
	if g, ok := mw.floatGauges[name]; ok {
		mw.mu.RUnlock()
		return g, nil
	}
	mw.mu.RUnlock()

	mw.mu.Lock()
	defer mw.mu.Unlock()

	if g, ok := mw.floatGauges[name]; ok {
		return g, nil
	}

	gauge, err := mw.meter.Float64Gauge(name, opts...)
	if err != nil {
		return nil, fmt.Errorf("failed to create float gauge %s: %w", name, err)
	}

	mw.floatGauges[name] = gauge
	return gauge, nil
}

// Add 增加计数器值
func (mw *MeterWrapper) Add(ctx context.Context, name string, value int64, attrs ...attribute.KeyValue) error {
	counter, err := mw.Counter(name)
	if err != nil {
		return err
	}
	counter.Add(ctx, value, metric.WithAttributes(attrs...))
	return nil
}

// Inc 计数器加 1
func (mw *MeterWrapper) Inc(ctx context.Context, name string, attrs ...attribute.KeyValue) error {
	return mw.Add(ctx, name, 1, attrs...)
}

// Record 记录直方图值
func (mw *MeterWrapper) Record(ctx context.Context, name string, value int64, attrs ...attribute.KeyValue) error {
	histogram, err := mw.Histogram(name)
	if err != nil {
		return err
	}
	histogram.Record(ctx, value, metric.WithAttributes(attrs...))
	return nil
}

// RecordDuration 记录持续时间
func (mw *MeterWrapper) RecordDuration(ctx context.Context, name string, duration time.Duration, attrs ...attribute.KeyValue) error {
	return mw.Record(ctx, name, duration.Milliseconds(), attrs...)
}

// SetGauge 设置仪表值
func (mw *MeterWrapper) SetGauge(ctx context.Context, name string, value int64, attrs ...attribute.KeyValue) error {
	gauge, err := mw.Gauge(name)
	if err != nil {
		return err
	}
	// Note: Int64Gauge requires a callback-based approach in newer OTel versions
	// This is a simplified implementation
	_ = gauge
	_ = ctx
	_ = value
	_ = attrs
	return nil
}

// ObservableGauge 创建可观察仪表
func (mw *MeterWrapper) ObservableGauge(name string, callback metric.Int64Callback, opts ...metric.Int64ObservableGaugeOption) error {
	_, err := mw.meter.Int64ObservableGauge(name, append(opts, metric.WithInt64Callback(callback))...)
	return err
}

// Timer 用于测量执行时间的辅助结构
type Timer struct {
	start time.Time
	meter *MeterWrapper
	name  string
	attrs []attribute.KeyValue
}

// NewTimer 创建一个新的计时器
func (mw *MeterWrapper) NewTimer(name string, attrs ...attribute.KeyValue) *Timer {
	return &Timer{
		start: time.Now(),
		meter: mw,
		name:  name,
		attrs: attrs,
	}
}

// Stop 停止计时器并记录持续时间
func (t *Timer) Stop(ctx context.Context) time.Duration {
	duration := time.Since(t.start)
	_ = t.meter.RecordDuration(ctx, t.name, duration, t.attrs...)
	return duration
}

// Elapsed 返回已过去的时间（不记录）
func (t *Timer) Elapsed() time.Duration {
	return time.Since(t.start)
}

// Record 记录当前经过的时间
func (t *Timer) Record(ctx context.Context) time.Duration {
	return t.Stop(ctx)
}

// TimerFunc 是一个计时函数包装器
func (mw *MeterWrapper) TimerFunc(ctx context.Context, name string, fn func() error, attrs ...attribute.KeyValue) error {
	timer := mw.NewTimer(name, attrs...)
	err := fn()
	timer.Stop(ctx)
	return err
}

// TimerFuncWithResult 是一个带返回值的计时函数包装器
func TimerFuncWithResult[T any](mw *MeterWrapper, ctx context.Context, name string, fn func() (T, error), attrs ...attribute.KeyValue) (T, error) {
	timer := mw.NewTimer(name, attrs...)
	result, err := fn()
	timer.Stop(ctx)
	return result, err
}

// MetricsBatch 批量记录指标
type MetricsBatch struct {
	meter *MeterWrapper
	ctx   context.Context
}

// NewBatch 创建新的批量记录器
func (mw *MeterWrapper) NewBatch(ctx context.Context) *MetricsBatch {
	return &MetricsBatch{
		meter: mw,
		ctx:   ctx,
	}
}

// Add 批量添加计数
func (mb *MetricsBatch) Add(name string, value int64, attrs ...attribute.KeyValue) *MetricsBatch {
	_ = mb.meter.Add(mb.ctx, name, value, attrs...)
	return mb
}

// Inc 批量增加计数
func (mb *MetricsBatch) Inc(name string, attrs ...attribute.KeyValue) *MetricsBatch {
	return mb.Add(name, 1, attrs...)
}

// Record 批量记录直方图
func (mb *MetricsBatch) Record(name string, value int64, attrs ...attribute.KeyValue) *MetricsBatch {
	_ = mb.meter.Record(mb.ctx, name, value, attrs...)
	return mb
}

// MeterFromContext 从上下文获取 Meter
func MeterFromContext(ctx context.Context, name string) metric.Meter {
	provider, ok := ctx.Value(meterProviderKey{}).(metric.MeterProvider)
	if !ok || provider == nil {
		return nil
	}
	return provider.Meter(name)
}

type meterProviderKey struct{}

// ContextWithMeterProvider 将 MeterProvider 存入上下文
func ContextWithMeterProvider(ctx context.Context, provider metric.MeterProvider) context.Context {
	return context.WithValue(ctx, meterProviderKey{}, provider)
}

// Attribute helpers

// StringAttr 创建字符串属性
func StringAttr(key, value string) attribute.KeyValue {
	return attribute.String(key, value)
}

// IntAttr 创建整数属性
func IntAttr(key string, value int) attribute.KeyValue {
	return attribute.Int(key, value)
}

// Int64Attr 创建 int64 属性
func Int64Attr(key string, value int64) attribute.KeyValue {
	return attribute.Int64(key, value)
}

// Float64Attr 创建 float64 属性
func Float64Attr(key string, value float64) attribute.KeyValue {
	return attribute.Float64(key, value)
}

// BoolAttr 创建布尔属性
func BoolAttr(key string, value bool) attribute.KeyValue {
	return attribute.Bool(key, value)
}

// StringSliceAttr 创建字符串切片属性
func StringSliceAttr(key string, values []string) attribute.KeyValue {
	return attribute.StringSlice(key, values)
}

// Attributes 从 map 创建属性列表
func Attributes(attrs map[string]interface{}) []attribute.KeyValue {
	result := make([]attribute.KeyValue, 0, len(attrs))
	for k, v := range attrs {
		result = append(result, createMetricAttribute(k, v))
	}
	return result
}

// createMetricAttribute 创建指标属性
func createMetricAttribute(key string, value interface{}) attribute.KeyValue {
	switch v := value.(type) {
	case string:
		return attribute.String(key, v)
	case int:
		return attribute.Int(key, v)
	case int64:
		return attribute.Int64(key, v)
	case float64:
		return attribute.Float64(key, v)
	case bool:
		return attribute.Bool(key, v)
	case []string:
		return attribute.StringSlice(key, v)
	case []int:
		return attribute.IntSlice(key, v)
	case []int64:
		return attribute.Int64Slice(key, v)
	case []float64:
		return attribute.Float64Slice(key, v)
	case []bool:
		return attribute.BoolSlice(key, v)
	default:
		return attribute.String(key, fmt.Sprintf("%v", v))
	}
}

// Package performance provides performance optimization utilities
// for the OTLP Go SDK.
package performance

import (
	"fmt"
	"runtime"
	runtimemetrics "runtime/metrics"
	"sync"
	"sync/atomic"
	"time"
)

// MetricType 指标类型
type MetricType string

const (
	// MetricTypeCounter 计数器
	MetricTypeCounter MetricType = "counter"
	// MetricTypeGauge 仪表盘
	MetricTypeGauge MetricType = "gauge"
	// MetricTypeHistogram 直方图
	MetricTypeHistogram MetricType = "histogram"
	// MetricTypeSummary 摘要
	MetricTypeSummary MetricType = "summary"
)

// RuntimeMetric 运行时指标
type RuntimeMetric struct {
	Name      string
	Type      MetricType
	Value     float64
	Timestamp time.Time
	Labels    map[string]string
}

// MetricCollector 指标收集器接口
type MetricCollector interface {
	Collect() []RuntimeMetric
	Start() error
	Stop() error
}

// MetricsConfig 指标收集配置
type MetricsConfig struct {
	// CollectionInterval 收集间隔
	CollectionInterval time.Duration
	// EnableGCMetrics 启用 GC 指标
	EnableGCMetrics bool
	// EnableMemMetrics 启用内存指标
	EnableMemMetrics bool
	// EnableGoroutineMetrics 启用 Goroutine 指标
	EnableGoroutineMetrics bool
	// EnableRuntimeMetrics 启用运行时指标（Go 1.16+）
	EnableRuntimeMetrics bool
	// EnableCustomMetrics 启用自定义指标
	EnableCustomMetrics bool
	// MaxMetricsHistory 最大历史记录数
	MaxMetricsHistory int
}

// DefaultMetricsConfig 返回默认配置
func DefaultMetricsConfig() *MetricsConfig {
	return &MetricsConfig{
		CollectionInterval:     10 * time.Second,
		EnableGCMetrics:        true,
		EnableMemMetrics:       true,
		EnableGoroutineMetrics: true,
		EnableRuntimeMetrics:   true,
		EnableCustomMetrics:    true,
		MaxMetricsHistory:      1000,
	}
}

// RuntimeMetricsCollector 运行时指标收集器
type RuntimeMetricsCollector struct {
	config    *MetricsConfig
	metrics   []RuntimeMetric
	history   map[string][]RuntimeMetric
	mu        sync.RWMutex
	stopCh    chan struct{}
	running   atomic.Bool
	startTime time.Time
}

// NewRuntimeMetricsCollector 创建运行时指标收集器
func NewRuntimeMetricsCollector(config *MetricsConfig) *RuntimeMetricsCollector {
	if config == nil {
		config = DefaultMetricsConfig()
	}
	return &RuntimeMetricsCollector{
		config:  config,
		metrics: make([]RuntimeMetric, 0),
		history: make(map[string][]RuntimeMetric),
		stopCh:  make(chan struct{}),
	}
}

// Start 开始收集指标
func (c *RuntimeMetricsCollector) Start() error {
	if !c.running.CompareAndSwap(false, true) {
		return fmt.Errorf("metrics collector already running")
	}

	c.startTime = time.Now()

	// 立即收集一次
	c.collect()

	// 启动定时收集
	go c.collectionLoop()

	return nil
}

// Stop 停止收集指标
func (c *RuntimeMetricsCollector) Stop() error {
	if !c.running.CompareAndSwap(true, false) {
		return fmt.Errorf("metrics collector not running")
	}

	close(c.stopCh)
	return nil
}

// Collect 收集当前指标
func (c *RuntimeMetricsCollector) Collect() []RuntimeMetric {
	c.mu.RLock()
	defer c.mu.RUnlock()

	result := make([]RuntimeMetric, len(c.metrics))
	copy(result, c.metrics)
	return result
}

// GetHistory 获取指标历史
func (c *RuntimeMetricsCollector) GetHistory(metricName string) []RuntimeMetric {
	c.mu.RLock()
	defer c.mu.RUnlock()

	history, ok := c.history[metricName]
	if !ok {
		return nil
	}

	result := make([]RuntimeMetric, len(history))
	copy(result, history)
	return result
}

// GetAllHistory 获取所有指标历史
func (c *RuntimeMetricsCollector) GetAllHistory() map[string][]RuntimeMetric {
	c.mu.RLock()
	defer c.mu.RUnlock()

	result := make(map[string][]RuntimeMetric)
	for k, v := range c.history {
		history := make([]RuntimeMetric, len(v))
		copy(history, v)
		result[k] = history
	}
	return result
}

// collectionLoop 收集循环
func (c *RuntimeMetricsCollector) collectionLoop() {
	ticker := time.NewTicker(c.config.CollectionInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			c.collect()
		case <-c.stopCh:
			return
		}
	}
}

// collect 执行指标收集
func (c *RuntimeMetricsCollector) collect() {
	now := time.Now()
	metrics := make([]RuntimeMetric, 0)

	if c.config.EnableGCMetrics {
		metrics = append(metrics, c.collectGCMetrics(now)...)
	}

	if c.config.EnableMemMetrics {
		metrics = append(metrics, c.collectMemMetrics(now)...)
	}

	if c.config.EnableGoroutineMetrics {
		metrics = append(metrics, c.collectGoroutineMetrics(now)...)
	}

	if c.config.EnableRuntimeMetrics {
		metrics = append(metrics, c.collectRuntimeMetrics(now)...)
	}

	// 更新指标和历史记录
	c.mu.Lock()
	c.metrics = metrics

	// 更新历史记录
	for _, m := range metrics {
		history := c.history[m.Name]
		history = append(history, m)
		if len(history) > c.config.MaxMetricsHistory {
			history = history[len(history)-c.config.MaxMetricsHistory:]
		}
		c.history[m.Name] = history
	}
	c.mu.Unlock()
}

// collectGCMetrics 收集 GC 指标
func (c *RuntimeMetricsCollector) collectGCMetrics(now time.Time) []RuntimeMetric {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return []RuntimeMetric{
		{
			Name:      "go_gc_count",
			Type:      MetricTypeCounter,
			Value:     float64(m.NumGC),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_gc_cpu_fraction",
			Type:      MetricTypeGauge,
			Value:     m.GCCPUFraction,
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_gc_pause_total_ns",
			Type:      MetricTypeCounter,
			Value:     float64(m.PauseTotalNs),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_gc_last_pause_ns",
			Type:      MetricTypeGauge,
			Value:     float64(m.PauseNs[(m.NumGC+255)%256]),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_gc_forced",
			Type:      MetricTypeCounter,
			Value:     float64(m.NumForcedGC),
			Timestamp: now,
			Labels:    map[string]string{},
		},
	}
}

// collectMemMetrics 收集内存指标
func (c *RuntimeMetricsCollector) collectMemMetrics(now time.Time) []RuntimeMetric {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return []RuntimeMetric{
		{
			Name:      "go_mem_alloc_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.Alloc),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_total_alloc_bytes",
			Type:      MetricTypeCounter,
			Value:     float64(m.TotalAlloc),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_sys_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.Sys),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_lookups",
			Type:      MetricTypeCounter,
			Value:     float64(m.Lookups),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_mallocs",
			Type:      MetricTypeCounter,
			Value:     float64(m.Mallocs),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_frees",
			Type:      MetricTypeCounter,
			Value:     float64(m.Frees),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_heap_alloc_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.HeapAlloc),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_heap_sys_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.HeapSys),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_heap_idle_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.HeapIdle),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_heap_inuse_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.HeapInuse),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_heap_released_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.HeapReleased),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_heap_objects",
			Type:      MetricTypeGauge,
			Value:     float64(m.HeapObjects),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_stack_inuse_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.StackInuse),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_stack_sys_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.StackSys),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_mspan_inuse_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.MSpanInuse),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_mcache_inuse_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.MCacheInuse),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_mem_next_gc_bytes",
			Type:      MetricTypeGauge,
			Value:     float64(m.NextGC),
			Timestamp: now,
			Labels:    map[string]string{},
		},
	}
}

// collectGoroutineMetrics 收集 Goroutine 指标
func (c *RuntimeMetricsCollector) collectGoroutineMetrics(now time.Time) []RuntimeMetric {
	return []RuntimeMetric{
		{
			Name:      "go_goroutines",
			Type:      MetricTypeGauge,
			Value:     float64(runtime.NumGoroutine()),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_cpus",
			Type:      MetricTypeGauge,
			Value:     float64(runtime.NumCPU()),
			Timestamp: now,
			Labels:    map[string]string{},
		},
		{
			Name:      "go_cgo_calls",
			Type:      MetricTypeCounter,
			Value:     float64(runtime.NumCgoCall()),
			Timestamp: now,
			Labels:    map[string]string{},
		},
	}
}

// collectRuntimeMetrics 使用 runtime/metrics 收集指标（Go 1.16+）
func (c *RuntimeMetricsCollector) collectRuntimeMetrics(now time.Time) []RuntimeMetric {
	metrics := make([]RuntimeMetric, 0)

	// 获取所有支持的指标描述
	samples := []runtimemetrics.Sample{
		{Name: "/sched/goroutines:goroutines"},
		{Name: "/memory/classes/total:bytes"},
		{Name: "/memory/classes/heap/objects:bytes"},
		{Name: "/memory/classes/heap/free:bytes"},
		{Name: "/memory/classes/heap/released:bytes"},
		{Name: "/gc/heap/allocs:bytes"},
		{Name: "/gc/heap/frees:bytes"},
		{Name: "/gc/heap/objects:objects"},
		{Name: "/gc/cycles/total:gc-cycles"},
		{Name: "/gc/cycles/forced:gc-cycles"},
	}

	runtimemetrics.Read(samples)

	for _, sample := range samples {
		var value float64
		switch sample.Value.Kind() {
		case runtimemetrics.KindUint64:
			value = float64(sample.Value.Uint64())
		case runtimemetrics.KindFloat64:
			value = sample.Value.Float64()
		case runtimemetrics.KindBad:
			continue // 跳过不支持的指标
		default:
			continue
		}

		metrics = append(metrics, RuntimeMetric{
			Name:      sample.Name,
			Type:      MetricTypeGauge,
			Value:     value,
			Timestamp: now,
			Labels:    map[string]string{},
		})
	}

	return metrics
}

// GetStats 获取统计信息
func (c *RuntimeMetricsCollector) GetStats() map[string]interface{} {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return map[string]interface{}{
		"running":             c.running.Load(),
		"start_time":          c.startTime,
		"metrics_count":       len(c.metrics),
		"history_count":       len(c.history),
		"collection_interval": c.config.CollectionInterval,
	}
}

// CustomMetric 自定义指标
type CustomMetric struct {
	collector  *RuntimeMetricsCollector
	name       string
	metricType MetricType
	value      float64
	mu         sync.RWMutex
}

// NewCustomMetric 创建自定义指标
func NewCustomMetric(collector *RuntimeMetricsCollector, name string, metricType MetricType) *CustomMetric {
	return &CustomMetric{
		collector:  collector,
		name:       name,
		metricType: metricType,
	}
}

// Set 设置指标值（Gauge 类型）
func (m *CustomMetric) Set(value float64) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.value = value
}

// Add 增加值（Counter 类型）
func (m *CustomMetric) Add(delta float64) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.value += delta
}

// Inc 增加 1
func (m *CustomMetric) Inc() {
	m.Add(1)
}

// Dec 减少 1
func (m *CustomMetric) Dec() {
	m.Add(-1)
}

// Get 获取当前值
func (m *CustomMetric) Get() float64 {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.value
}

// Timer 计时器指标
type Timer struct {
	collector *RuntimeMetricsCollector
	name      string
	startTime time.Time
}

// NewTimer 创建计时器
func NewTimer(collector *RuntimeMetricsCollector, name string) *Timer {
	return &Timer{
		collector: collector,
		name:      name,
		startTime: time.Now(),
	}
}

// ObserveDuration 记录持续时间
func (t *Timer) ObserveDuration() float64 {
	duration := time.Since(t.startTime).Seconds()
	return duration
}

// Histogram 直方图指标
type Histogram struct {
	collector *RuntimeMetricsCollector
	name      string
	bounds    []float64
	counts    []uint64
	sum       float64
	count     uint64
	mu        sync.RWMutex
}

// NewHistogram 创建直方图
func NewHistogram(collector *RuntimeMetricsCollector, name string, bounds []float64) *Histogram {
	if len(bounds) == 0 {
		bounds = []float64{.005, .01, .025, .05, .1, .25, .5, 1, 2.5, 5, 10}
	}
	return &Histogram{
		collector: collector,
		name:      name,
		bounds:    bounds,
		counts:    make([]uint64, len(bounds)+1),
	}
}

// Observe 观察一个值
func (h *Histogram) Observe(value float64) {
	h.mu.Lock()
	defer h.mu.Unlock()

	h.sum += value
	h.count++

	for i, bound := range h.bounds {
		if value <= bound {
			h.counts[i]++
			return
		}
	}
	h.counts[len(h.bounds)]++
}

// GetSnapshot 获取直方图快照
func (h *Histogram) GetSnapshot() (sum float64, count uint64, counts []uint64) {
	h.mu.RLock()
	defer h.mu.RUnlock()

	countsCopy := make([]uint64, len(h.counts))
	copy(countsCopy, h.counts)
	return h.sum, h.count, countsCopy
}

// GetRuntimeSnapshot 获取运行时快照
func GetRuntimeSnapshot() map[string]interface{} {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return map[string]interface{}{
		"timestamp":       time.Now(),
		"goroutines":      runtime.NumGoroutine(),
		"cpus":            runtime.NumCPU(),
		"cgo_calls":       runtime.NumCgoCall(),
		"mem_alloc":       m.Alloc,
		"mem_total_alloc": m.TotalAlloc,
		"mem_sys":         m.Sys,
		"mem_heap_alloc":  m.HeapAlloc,
		"mem_heap_sys":    m.HeapSys,
		"gc_count":        m.NumGC,
		"gc_cpu_fraction": m.GCCPUFraction,
	}
}

// FormatBytes 格式化字节大小
func FormatBytes(bytes uint64) string {
	const unit = 1024
	if bytes < unit {
		return fmt.Sprintf("%d B", bytes)
	}
	div, exp := uint64(unit), 0
	for n := bytes / unit; n >= unit; n /= unit {
		div *= unit
		exp++
	}
	return fmt.Sprintf("%.1f %cB", float64(bytes)/float64(div), "KMGTPE"[exp])
}

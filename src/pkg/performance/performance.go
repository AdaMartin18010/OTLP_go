package performance

import (
	"fmt"
	"runtime"
	"sync"
	"time"
)

// PerformanceMonitor 性能监控器
type PerformanceMonitor struct {
	metrics   map[string]*Metric
	mutex     sync.RWMutex
	startTime time.Time
	interval  time.Duration
	stopCh    chan struct{}
}

// Metric 性能指标
type Metric struct {
	Name        string
	Value       float64
	Count       int64
	Min         float64
	Max         float64
	Sum         float64
	LastUpdated time.Time
	mutex       sync.RWMutex
}

// PerformanceStats 性能统计
type PerformanceStats struct {
	MemoryStats   *MemoryStats       `json:"memory_stats"`
	RuntimeStats  *RuntimeStats      `json:"runtime_stats"`
	CustomMetrics map[string]*Metric `json:"custom_metrics"`
	Uptime        time.Duration      `json:"uptime"`
	LastUpdated   time.Time          `json:"last_updated"`
}

// MemoryStats 内存统计
type MemoryStats struct {
	Alloc         uint64  `json:"alloc"`
	TotalAlloc    uint64  `json:"total_alloc"`
	Sys           uint64  `json:"sys"`
	Lookups       uint64  `json:"lookups"`
	Mallocs       uint64  `json:"mallocs"`
	Frees         uint64  `json:"frees"`
	HeapAlloc     uint64  `json:"heap_alloc"`
	HeapSys       uint64  `json:"heap_sys"`
	HeapIdle      uint64  `json:"heap_idle"`
	HeapInuse     uint64  `json:"heap_inuse"`
	HeapReleased  uint64  `json:"heap_released"`
	HeapObjects   uint64  `json:"heap_objects"`
	StackInuse    uint64  `json:"stack_inuse"`
	StackSys      uint64  `json:"stack_sys"`
	MSpanInuse    uint64  `json:"mspan_inuse"`
	MSpanSys      uint64  `json:"mspan_sys"`
	MCacheInuse   uint64  `json:"mcache_inuse"`
	MCacheSys     uint64  `json:"mcache_sys"`
	BuckHashSys   uint64  `json:"buck_hash_sys"`
	GCSys         uint64  `json:"gc_sys"`
	OtherSys      uint64  `json:"other_sys"`
	NextGC        uint64  `json:"next_gc"`
	LastGC        uint64  `json:"last_gc"`
	PauseTotalNs  uint64  `json:"pause_total_ns"`
	NumGC         uint32  `json:"num_gc"`
	NumForcedGC   uint32  `json:"num_forced_gc"`
	GCCPUFraction float64 `json:"gc_cpu_fraction"`
}

// RuntimeStats 运行时统计
type RuntimeStats struct {
	NumGoroutine int   `json:"num_goroutine"`
	NumCgoCall   int64 `json:"num_cgo_call"`
	NumCPU       int   `json:"num_cpu"`
	GOMAXPROCS   int   `json:"gomaxprocs"`
}

// NewPerformanceMonitor 创建性能监控器
func NewPerformanceMonitor(interval time.Duration) *PerformanceMonitor {
	return &PerformanceMonitor{
		metrics:   make(map[string]*Metric),
		startTime: time.Now(),
		interval:  interval,
		stopCh:    make(chan struct{}),
	}
}

// Start 开始监控
func (pm *PerformanceMonitor) Start() {
	go pm.monitor()
}

// Stop 停止监控
func (pm *PerformanceMonitor) Stop() {
	close(pm.stopCh)
}

// monitor 监控循环
func (pm *PerformanceMonitor) monitor() {
	ticker := time.NewTicker(pm.interval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			pm.collectStats()
		case <-pm.stopCh:
			return
		}
	}
}

// collectStats 收集统计信息
func (pm *PerformanceMonitor) collectStats() {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	// 更新内存指标
	pm.UpdateMetric("memory.alloc", float64(m.Alloc))
	pm.UpdateMetric("memory.total_alloc", float64(m.TotalAlloc))
	pm.UpdateMetric("memory.sys", float64(m.Sys))
	pm.UpdateMetric("memory.heap_alloc", float64(m.HeapAlloc))
	pm.UpdateMetric("memory.heap_sys", float64(m.HeapSys))
	pm.UpdateMetric("memory.heap_objects", float64(m.HeapObjects))
	pm.UpdateMetric("memory.num_gc", float64(m.NumGC))
	pm.UpdateMetric("memory.gc_cpu_fraction", m.GCCPUFraction)

	// 更新运行时指标
	pm.UpdateMetric("runtime.goroutines", float64(runtime.NumGoroutine()))
	pm.UpdateMetric("runtime.cgo_calls", float64(runtime.NumCgoCall()))
}

// UpdateMetric 更新指标
func (pm *PerformanceMonitor) UpdateMetric(name string, value float64) {
	pm.mutex.Lock()
	defer pm.mutex.Unlock()

	metric, exists := pm.metrics[name]
	if !exists {
		metric = &Metric{
			Name:        name,
			Value:       value,
			Count:       1,
			Min:         value,
			Max:         value,
			Sum:         value,
			LastUpdated: time.Now(),
		}
		pm.metrics[name] = metric
		return
	}

	metric.mutex.Lock()
	defer metric.mutex.Unlock()

	metric.Value = value
	metric.Count++
	metric.Sum += value
	metric.LastUpdated = time.Now()

	if value < metric.Min {
		metric.Min = value
	}
	if value > metric.Max {
		metric.Max = value
	}
}

// GetMetric 获取指标
func (pm *PerformanceMonitor) GetMetric(name string) (*Metric, bool) {
	pm.mutex.RLock()
	defer pm.mutex.RUnlock()

	metric, exists := pm.metrics[name]
	if !exists {
		return nil, false
	}

	// 返回副本以避免并发问题
	metric.mutex.RLock()
	defer metric.mutex.RUnlock()

	return &Metric{
		Name:        metric.Name,
		Value:       metric.Value,
		Count:       metric.Count,
		Min:         metric.Min,
		Max:         metric.Max,
		Sum:         metric.Sum,
		LastUpdated: metric.LastUpdated,
	}, true
}

// GetAllMetrics 获取所有指标
func (pm *PerformanceMonitor) GetAllMetrics() map[string]*Metric {
	pm.mutex.RLock()
	defer pm.mutex.RUnlock()

	result := make(map[string]*Metric)
	for name, metric := range pm.metrics {
		metric.mutex.RLock()
		result[name] = &Metric{
			Name:        metric.Name,
			Value:       metric.Value,
			Count:       metric.Count,
			Min:         metric.Min,
			Max:         metric.Max,
			Sum:         metric.Sum,
			LastUpdated: metric.LastUpdated,
		}
		metric.mutex.RUnlock()
	}

	return result
}

// GetStats 获取性能统计
func (pm *PerformanceMonitor) GetStats() *PerformanceStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	memoryStats := &MemoryStats{
		Alloc:         m.Alloc,
		TotalAlloc:    m.TotalAlloc,
		Sys:           m.Sys,
		Lookups:       m.Lookups,
		Mallocs:       m.Mallocs,
		Frees:         m.Frees,
		HeapAlloc:     m.HeapAlloc,
		HeapSys:       m.HeapSys,
		HeapIdle:      m.HeapIdle,
		HeapInuse:     m.HeapInuse,
		HeapReleased:  m.HeapReleased,
		HeapObjects:   m.HeapObjects,
		StackInuse:    m.StackInuse,
		StackSys:      m.StackSys,
		MSpanInuse:    m.MSpanInuse,
		MSpanSys:      m.MSpanSys,
		MCacheInuse:   m.MCacheInuse,
		MCacheSys:     m.MCacheSys,
		BuckHashSys:   m.BuckHashSys,
		GCSys:         m.GCSys,
		OtherSys:      m.OtherSys,
		NextGC:        m.NextGC,
		LastGC:        m.LastGC,
		PauseTotalNs:  m.PauseTotalNs,
		NumGC:         m.NumGC,
		NumForcedGC:   m.NumForcedGC,
		GCCPUFraction: m.GCCPUFraction,
	}

	runtimeStats := &RuntimeStats{
		NumGoroutine: runtime.NumGoroutine(),
		NumCgoCall:   runtime.NumCgoCall(),
		NumCPU:       runtime.NumCPU(),
		GOMAXPROCS:   runtime.GOMAXPROCS(0),
	}

	return &PerformanceStats{
		MemoryStats:   memoryStats,
		RuntimeStats:  runtimeStats,
		CustomMetrics: pm.GetAllMetrics(),
		Uptime:        time.Since(pm.startTime),
		LastUpdated:   time.Now(),
	}
}

// GetAverage 获取平均值
func (m *Metric) GetAverage() float64 {
	if m.Count == 0 {
		return 0
	}
	return m.Sum / float64(m.Count)
}

// String 返回指标的字符串表示
func (m *Metric) String() string {
	return fmt.Sprintf("Metric{Name: %s, Value: %.2f, Count: %d, Min: %.2f, Max: %.2f, Avg: %.2f}",
		m.Name, m.Value, m.Count, m.Min, m.Max, m.GetAverage())
}

// 性能优化工具

// StringPool 字符串池
type StringPool struct {
	pool sync.Pool
}

// NewStringPool 创建字符串池
func NewStringPool() *StringPool {
	return &StringPool{
		pool: sync.Pool{
			New: func() interface{} {
				return &StringBuilder{}
			},
		},
	}
}

// Get 获取StringBuilder
func (sp *StringPool) Get() *StringBuilder {
	return sp.pool.Get().(*StringBuilder)
}

// Put 归还StringBuilder
func (sp *StringPool) Put(sb *StringBuilder) {
	sb.Reset()
	sp.pool.Put(sb)
}

// StringBuilder 优化的字符串构建器
type StringBuilder struct {
	buf []byte
}

// NewStringBuilder 创建StringBuilder
func NewStringBuilder() *StringBuilder {
	return &StringBuilder{
		buf: make([]byte, 0, 256), // 预分配容量
	}
}

// Write 写入字节
func (sb *StringBuilder) Write(p []byte) (n int, err error) {
	sb.buf = append(sb.buf, p...)
	return len(p), nil
}

// WriteString 写入字符串
func (sb *StringBuilder) WriteString(s string) (n int, err error) {
	sb.buf = append(sb.buf, s...)
	return len(s), nil
}

// WriteByte 写入字节
func (sb *StringBuilder) WriteByte(c byte) error {
	sb.buf = append(sb.buf, c)
	return nil
}

// String 返回字符串
func (sb *StringBuilder) String() string {
	return string(sb.buf)
}

// Len 返回长度
func (sb *StringBuilder) Len() int {
	return len(sb.buf)
}

// Cap 返回容量
func (sb *StringBuilder) Cap() int {
	return cap(sb.buf)
}

// Reset 重置
func (sb *StringBuilder) Reset() {
	sb.buf = sb.buf[:0]
}

// Grow 增长容量
func (sb *StringBuilder) Grow(n int) {
	if cap(sb.buf)-len(sb.buf) < n {
		newBuf := make([]byte, len(sb.buf), 2*cap(sb.buf)+n)
		copy(newBuf, sb.buf)
		sb.buf = newBuf
	}
}

// ObjectPool 对象池
type ObjectPool struct {
	pool sync.Pool
}

// NewObjectPool 创建对象池
func NewObjectPool(factory func() interface{}) *ObjectPool {
	return &ObjectPool{
		pool: sync.Pool{
			New: factory,
		},
	}
}

// Get 获取对象
func (op *ObjectPool) Get() interface{} {
	return op.pool.Get()
}

// Put 归还对象
func (op *ObjectPool) Put(obj interface{}) {
	op.pool.Put(obj)
}

// 性能基准测试

// BenchmarkResult 基准测试结果
type BenchmarkResult struct {
	Name            string        `json:"name"`
	Duration        time.Duration `json:"duration"`
	Iterations      int           `json:"iterations"`
	BytesPerOp      int64         `json:"bytes_per_op"`
	AllocsPerOp     int64         `json:"allocs_per_op"`
	MemPerOp        int64         `json:"mem_per_op"`
	NsPerOp         int64         `json:"ns_per_op"`
	MBPerSec        float64       `json:"mb_per_sec"`
	AllocedMBPerSec float64       `json:"alloced_mb_per_sec"`
}

// Benchmark 基准测试
func Benchmark(name string, iterations int, fn func()) *BenchmarkResult {
	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)

	start := time.Now()
	for i := 0; i < iterations; i++ {
		fn()
	}
	duration := time.Since(start)

	runtime.ReadMemStats(&m2)

	result := &BenchmarkResult{
		Name:       name,
		Duration:   duration,
		Iterations: iterations,
		NsPerOp:    int64(duration.Nanoseconds()) / int64(iterations),
	}

	if iterations > 0 {
		result.BytesPerOp = int64(m2.TotalAlloc-m1.TotalAlloc) / int64(iterations)
		result.AllocsPerOp = int64(m2.Mallocs-m1.Mallocs) / int64(iterations)
		result.MemPerOp = int64(m2.TotalAlloc-m1.TotalAlloc) / int64(iterations)
		result.MBPerSec = float64(result.BytesPerOp) / duration.Seconds() / 1024 / 1024
		result.AllocedMBPerSec = float64(result.MemPerOp) / duration.Seconds() / 1024 / 1024
	}

	return result
}

// 性能分析工具

// Profiler 性能分析器
type Profiler struct {
	enabled bool
	mutex   sync.RWMutex
}

// NewProfiler 创建性能分析器
func NewProfiler(enabled bool) *Profiler {
	return &Profiler{
		enabled: enabled,
	}
}

// Profile 性能分析
func (p *Profiler) Profile(name string, fn func()) {
	if !p.enabled {
		fn()
		return
	}

	p.mutex.RLock()
	enabled := p.enabled
	p.mutex.RUnlock()

	if !enabled {
		fn()
		return
	}

	start := time.Now()
	fn()
	duration := time.Since(start)

	// 这里可以添加性能分析逻辑
	// 例如记录到日志、发送到监控系统等
	fmt.Printf("Profile[%s]: %v\n", name, duration)
}

// Enable 启用性能分析
func (p *Profiler) Enable() {
	p.mutex.Lock()
	defer p.mutex.Unlock()
	p.enabled = true
}

// Disable 禁用性能分析
func (p *Profiler) Disable() {
	p.mutex.Lock()
	defer p.mutex.Unlock()
	p.enabled = false
}

// IsEnabled 检查是否启用
func (p *Profiler) IsEnabled() bool {
	p.mutex.RLock()
	defer p.mutex.RUnlock()
	return p.enabled
}

// 内存优化工具

// MemoryOptimizer 内存优化器
type MemoryOptimizer struct {
	threshold uint64
	interval  time.Duration
	stopCh    chan struct{}
}

// NewMemoryOptimizer 创建内存优化器
func NewMemoryOptimizer(threshold uint64, interval time.Duration) *MemoryOptimizer {
	return &MemoryOptimizer{
		threshold: threshold,
		interval:  interval,
		stopCh:    make(chan struct{}),
	}
}

// Start 开始内存优化
func (mo *MemoryOptimizer) Start() {
	go mo.optimize()
}

// Stop 停止内存优化
func (mo *MemoryOptimizer) Stop() {
	close(mo.stopCh)
}

// optimize 内存优化循环
func (mo *MemoryOptimizer) optimize() {
	ticker := time.NewTicker(mo.interval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			mo.checkAndOptimize()
		case <-mo.stopCh:
			return
		}
	}
}

// checkAndOptimize 检查并优化内存
func (mo *MemoryOptimizer) checkAndOptimize() {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	if m.HeapAlloc > mo.threshold {
		runtime.GC()
		fmt.Printf("Memory optimization triggered: HeapAlloc=%d, threshold=%d\n", m.HeapAlloc, mo.threshold)
	}
}

// 全局性能监控器
var globalMonitor *PerformanceMonitor

// InitGlobalMonitor 初始化全局监控器
func InitGlobalMonitor(interval time.Duration) {
	globalMonitor = NewPerformanceMonitor(interval)
	globalMonitor.Start()
}

// GetGlobalMonitor 获取全局监控器
func GetGlobalMonitor() *PerformanceMonitor {
	return globalMonitor
}

// ShutdownGlobalMonitor 关闭全局监控器
func ShutdownGlobalMonitor() {
	if globalMonitor != nil {
		globalMonitor.Stop()
	}
}

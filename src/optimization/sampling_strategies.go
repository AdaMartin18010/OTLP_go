package optimization

import (
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/trace"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	oteltrace "go.opentelemetry.io/otel/trace"
)

// AdaptiveSampler 自适应采样器
// 根据系统负载和错误率动态调整采样率
type AdaptiveSampler struct {
	baseSampler  sdktrace.Sampler
	errorSampler sdktrace.Sampler
	slowSampler  sdktrace.Sampler

	// 配置
	slowThreshold time.Duration
	highLoadQPS   int64

	// 运行时状态
	currentQPS   int64
	errorCount   int64
	requestCount int64
	mu           sync.RWMutex
	currentRate  float64

	// 统计窗口
	windowStart    time.Time
	windowDuration time.Duration
}

// NewAdaptiveSampler 创建自适应采样器
func NewAdaptiveSampler(baseRate float64, slowThreshold time.Duration, highLoadQPS int64) *AdaptiveSampler {
	sampler := &AdaptiveSampler{
		baseSampler:    sdktrace.TraceIDRatioBased(baseRate),
		errorSampler:   sdktrace.AlwaysSample(),
		slowSampler:    sdktrace.AlwaysSample(),
		slowThreshold:  slowThreshold,
		highLoadQPS:    highLoadQPS,
		currentRate:    baseRate,
		windowStart:    time.Now(),
		windowDuration: 10 * time.Second,
	}

	// 启动统计协程
	go sampler.updateStats()

	return sampler
}

// ShouldSample 实现 Sampler 接口
func (s *AdaptiveSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
	atomic.AddInt64(&s.requestCount, 1)

	// 1. 检查是否有错误标记
	for _, attr := range params.Attributes {
		if attr.Key == "error" && attr.Value.AsBool() {
			atomic.AddInt64(&s.errorCount, 1)
			return s.errorSampler.ShouldSample(params)
		}

		// 2. 检查是否为慢请求（通过自定义属性传递）
		if attr.Key == "is_slow" && attr.Value.AsBool() {
			return s.slowSampler.ShouldSample(params)
		}
	}

	// 3. 高负载时降低采样率
	qps := atomic.LoadInt64(&s.currentQPS)
	if qps > s.highLoadQPS {
		// 动态采样率：QPS 越高，采样率越低
		dynamicRate := float64(s.highLoadQPS) / float64(qps)
		if dynamicRate < 0.01 {
			dynamicRate = 0.01 // 最低 1%
		}
		return sdktrace.TraceIDRatioBased(dynamicRate).ShouldSample(params)
	}

	// 4. 正常负载使用基础采样率
	return s.baseSampler.ShouldSample(params)
}

// Description 实现 Sampler 接口
func (s *AdaptiveSampler) Description() string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return fmt.Sprintf("AdaptiveSampler{rate=%.1f%%}", s.currentRate*100)
}

// updateStats 定期更新统计信息
func (s *AdaptiveSampler) updateStats() {
	ticker := time.NewTicker(s.windowDuration)
	defer ticker.Stop()

	for range ticker.C {
		requests := atomic.SwapInt64(&s.requestCount, 0)
		errors := atomic.SwapInt64(&s.errorCount, 0)

		qps := requests / int64(s.windowDuration.Seconds())
		atomic.StoreInt64(&s.currentQPS, qps)

		errorRate := float64(0)
		if requests > 0 {
			errorRate = float64(errors) / float64(requests)
		}

		s.mu.Lock()
		// 根据错误率调整基础采样率
		if errorRate > 0.05 { // 错误率 > 5%
			s.currentRate = 1.0 // 提升到 100%
			s.baseSampler = sdktrace.AlwaysSample()
		} else if errorRate > 0.01 { // 错误率 > 1%
			s.currentRate = 0.5 // 提升到 50%
			s.baseSampler = sdktrace.TraceIDRatioBased(0.5)
		} else {
			s.currentRate = 0.1 // 正常 10%
			s.baseSampler = sdktrace.TraceIDRatioBased(0.1)
		}
		s.mu.Unlock()
	}
}

// GetStats 获取当前统计信息
func (s *AdaptiveSampler) GetStats() SamplerStats {
	s.mu.RLock()
	defer s.mu.RUnlock()

	return SamplerStats{
		CurrentQPS:  atomic.LoadInt64(&s.currentQPS),
		CurrentRate: s.currentRate,
	}
}

// SamplerStats 采样器统计信息
type SamplerStats struct {
	CurrentQPS  int64
	CurrentRate float64
}

// PrioritySampler 优先级采样器
// 根据请求优先级决定采样
type PrioritySampler struct {
	highPrioritySampler   sdktrace.Sampler
	normalPrioritySampler sdktrace.Sampler
	lowPrioritySampler    sdktrace.Sampler
}

// NewPrioritySampler 创建优先级采样器
func NewPrioritySampler() *PrioritySampler {
	return &PrioritySampler{
		highPrioritySampler:   sdktrace.AlwaysSample(),
		normalPrioritySampler: sdktrace.TraceIDRatioBased(0.1),
		lowPrioritySampler:    sdktrace.TraceIDRatioBased(0.01),
	}
}

// ShouldSample 实现 Sampler 接口
func (s *PrioritySampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
	// 检查优先级属性
	for _, attr := range params.Attributes {
		if attr.Key == "priority" {
			switch attr.Value.AsString() {
			case "high", "critical":
				return s.highPrioritySampler.ShouldSample(params)
			case "low":
				return s.lowPrioritySampler.ShouldSample(params)
			}
		}
	}

	// 默认正常优先级
	return s.normalPrioritySampler.ShouldSample(params)
}

// Description 实现 Sampler 接口
func (s *PrioritySampler) Description() string {
	return "PrioritySampler{high=100%, normal=10%, low=1%}"
}

// PathBasedSampler 基于路径的采样器
// 对不同的 API 路径使用不同的采样率
type PathBasedSampler struct {
	rules          map[string]float64
	defaultSampler sdktrace.Sampler
	mu             sync.RWMutex
}

// NewPathBasedSampler 创建基于路径的采样器
func NewPathBasedSampler(defaultRate float64) *PathBasedSampler {
	return &PathBasedSampler{
		rules:          make(map[string]float64),
		defaultSampler: sdktrace.TraceIDRatioBased(defaultRate),
	}
}

// AddRule 添加路径采样规则
func (s *PathBasedSampler) AddRule(path string, rate float64) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.rules[path] = rate
}

// ShouldSample 实现 Sampler 接口
func (s *PathBasedSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
	// 查找路径属性
	for _, attr := range params.Attributes {
		if attr.Key == "http.target" || attr.Key == "http.route" {
			path := attr.Value.AsString()

			s.mu.RLock()
			rate, ok := s.rules[path]
			s.mu.RUnlock()

			if ok {
				return sdktrace.TraceIDRatioBased(rate).ShouldSample(params)
			}
		}
	}

	// 使用默认采样率
	return s.defaultSampler.ShouldSample(params)
}

// Description 实现 Sampler 接口
func (s *PathBasedSampler) Description() string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return fmt.Sprintf("PathBasedSampler{rules=%d}", len(s.rules))
}

// ComposableSampler 可组合采样器
// 允许多个采样器按顺序评估
type ComposableSampler struct {
	samplers []sdktrace.Sampler
}

// NewComposableSampler 创建可组合采样器
func NewComposableSampler(samplers ...sdktrace.Sampler) *ComposableSampler {
	return &ComposableSampler{
		samplers: samplers,
	}
}

// ShouldSample 实现 Sampler 接口
// 任何一个采样器返回 RecordAndSample 就采样
func (s *ComposableSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
	for _, sampler := range s.samplers {
		result := sampler.ShouldSample(params)
		if result.Decision == sdktrace.RecordAndSample {
			return result
		}
	}

	// 所有采样器都不采样
	return sdktrace.SamplingResult{
		Decision:   sdktrace.Drop,
		Attributes: []attribute.KeyValue{},
	}
}

// Description 实现 Sampler 接口
func (s *ComposableSampler) Description() string {
	return fmt.Sprintf("ComposableSampler{count=%d}", len(s.samplers))
}

// TailSamplingSampler 尾部采样器（简化版本）
// 在请求完成后根据结果决定是否采样
type TailSamplingSampler struct {
	buffer      map[oteltrace.TraceID]*traceDecision
	mu          sync.RWMutex
	maxBuffered int
}

type traceDecision struct {
	shouldSample bool
	timestamp    time.Time
}

// NewTailSamplingSampler 创建尾部采样器
func NewTailSamplingSampler(maxBuffered int) *TailSamplingSampler {
	sampler := &TailSamplingSampler{
		buffer:      make(map[oteltrace.TraceID]*traceDecision),
		maxBuffered: maxBuffered,
	}

	// 启动清理协程
	go sampler.cleanup()

	return sampler
}

// ShouldSample 实现 Sampler 接口
func (s *TailSamplingSampler) ShouldSample(params sdktrace.SamplingParameters) sdktrace.SamplingResult {
	s.mu.RLock()
	decision, exists := s.buffer[params.TraceID]
	s.mu.RUnlock()

	if exists && decision.shouldSample {
		return sdktrace.SamplingResult{
			Decision: sdktrace.RecordAndSample,
		}
	}

	// 先记录，稍后决定
	return sdktrace.SamplingResult{
		Decision: sdktrace.RecordOnly,
	}
}

// RecordDecision 记录采样决策（由外部调用）
func (s *TailSamplingSampler) RecordDecision(traceID oteltrace.TraceID, shouldSample bool) {
	s.mu.Lock()
	defer s.mu.Unlock()

	if len(s.buffer) >= s.maxBuffered {
		// 简单的 LRU：删除最老的条目
		var oldestID oteltrace.TraceID
		var oldestTime time.Time

		for id, decision := range s.buffer {
			if oldestTime.IsZero() || decision.timestamp.Before(oldestTime) {
				oldestID = id
				oldestTime = decision.timestamp
			}
		}

		delete(s.buffer, oldestID)
	}

	s.buffer[traceID] = &traceDecision{
		shouldSample: shouldSample,
		timestamp:    time.Now(),
	}
}

// cleanup 定期清理过期的决策
func (s *TailSamplingSampler) cleanup() {
	ticker := time.NewTicker(1 * time.Minute)
	defer ticker.Stop()

	for range ticker.C {
		s.mu.Lock()
		now := time.Now()
		for id, decision := range s.buffer {
			if now.Sub(decision.timestamp) > 5*time.Minute {
				delete(s.buffer, id)
			}
		}
		s.mu.Unlock()
	}
}

// Description 实现 Sampler 接口
func (s *TailSamplingSampler) Description() string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return fmt.Sprintf("TailSamplingSampler{buffered=%d}", len(s.buffer))
}

// Example: 使用示例
func ExampleSamplingStrategies() {
	// 1. 自适应采样器
	adaptiveSampler := NewAdaptiveSampler(
		0.1,                  // 基础采样率 10%
		500*time.Millisecond, // 慢请求阈值
		10000,                // 高负载 QPS 阈值
	)

	_ = trace.NewTracerProvider(
		trace.WithSampler(adaptiveSampler),
	)

	// 2. 优先级采样器
	prioritySampler := NewPrioritySampler()
	_ = trace.NewTracerProvider(
		trace.WithSampler(prioritySampler),
	)

	// 3. 路径采样器
	pathSampler := NewPathBasedSampler(0.1)
	pathSampler.AddRule("/api/critical", 1.0)  // 关键 API 100%
	pathSampler.AddRule("/api/important", 0.5) // 重要 API 50%
	pathSampler.AddRule("/health", 0.01)       // 健康检查 1%

	_ = trace.NewTracerProvider(
		trace.WithSampler(pathSampler),
	)

	// 4. 组合采样器
	composableSampler := NewComposableSampler(
		adaptiveSampler,
		prioritySampler,
		pathSampler,
	)

	_ = trace.NewTracerProvider(
		trace.WithSampler(composableSampler),
	)
}

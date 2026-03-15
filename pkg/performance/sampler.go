// Package performance provides performance optimization utilities
// for the OTLP Go SDK.
package performance

import (
	"math"
	"runtime"
	"sync"
	"sync/atomic"
	"time"
)

// SamplingStrategy 采样策略类型
type SamplingStrategy string

const (
	// SamplingStrategyFixed 固定采样率
	SamplingStrategyFixed SamplingStrategy = "fixed"
	// SamplingStrategyAdaptive 自适应采样
	SamplingStrategyAdaptive SamplingStrategy = "adaptive"
	// SamplingStrategyProbabilistic 概率采样
	SamplingStrategyProbabilistic SamplingStrategy = "probabilistic"
	// SamplingStrategyRateLimiting 速率限制采样
	SamplingStrategyRateLimiting SamplingStrategy = "rate_limiting"
	// SamplingStrategyDynamic 动态采样
	SamplingStrategyDynamic SamplingStrategy = "dynamic"
)

// SamplingConfig 采样配置
type SamplingConfig struct {
	// Strategy 采样策略
	Strategy SamplingStrategy
	// Rate 固定采样率 (0.0 - 1.0)
	Rate float64
	// MaxSamplesPerSecond 每秒最大采样数（速率限制策略）
	MaxSamplesPerSecond int
	// AdaptiveInterval 自适应调整间隔
	AdaptiveInterval time.Duration
	// MinRate 最小采样率
	MinRate float64
	// MaxRate 最大采样率
	MaxRate float64
	// TargetCPU 目标 CPU 使用率 (%)
	TargetCPU float64
	// TargetMemory 目标内存使用率 (%)
	TargetMemory float64
	// WindowSize 滑动窗口大小
	WindowSize int
}

// DefaultSamplingConfig 返回默认采样配置
func DefaultSamplingConfig() *SamplingConfig {
	return &SamplingConfig{
		Strategy:            SamplingStrategyAdaptive,
		Rate:                1.0,
		MaxSamplesPerSecond: 1000,
		AdaptiveInterval:    5 * time.Second,
		MinRate:             0.01,
		MaxRate:             1.0,
		TargetCPU:           70.0,
		TargetMemory:        80.0,
		WindowSize:          10,
	}
}

// SamplingDecision 采样决策
type SamplingDecision int

const (
	// SamplingDecisionDrop 丢弃
	SamplingDecisionDrop SamplingDecision = iota
	// SamplingDecisionSample 采样
	SamplingDecisionSample
)

// SamplingContext 采样上下文
type SamplingContext struct {
	TraceID    string
	SpanID     string
	Operation  string
	StartTime  time.Time
	Attributes map[string]interface{}
}

// Sampler 采样器接口
type Sampler interface {
	ShouldSample(ctx *SamplingContext) SamplingDecision
	GetRate() float64
	UpdateRate(rate float64)
}

// FixedSampler 固定采样率采样器
type FixedSampler struct {
	rate float64
}

// NewFixedSampler 创建固定采样率采样器
func NewFixedSampler(rate float64) *FixedSampler {
	if rate < 0 {
		rate = 0
	}
	if rate > 1 {
		rate = 1
	}
	return &FixedSampler{rate: rate}
}

// ShouldSample 判断是否采样
func (s *FixedSampler) ShouldSample(ctx *SamplingContext) SamplingDecision {
	if s.rate >= 1.0 {
		return SamplingDecisionSample
	}
	if s.rate <= 0 {
		return SamplingDecisionDrop
	}
	// 使用 TraceID 进行确定性采样
	hash := hashTraceID(ctx.TraceID)
	if hash < s.rate {
		return SamplingDecisionSample
	}
	return SamplingDecisionDrop
}

// GetRate 获取当前采样率
func (s *FixedSampler) GetRate() float64 {
	return s.rate
}

// UpdateRate 更新采样率
func (s *FixedSampler) UpdateRate(rate float64) {
	if rate < 0 {
		rate = 0
	}
	if rate > 1 {
		rate = 1
	}
	s.rate = rate
}

// ProbabilisticSampler 概率采样器
type ProbabilisticSampler struct {
	rate uint64
}

// NewProbabilisticSampler 创建概率采样器
func NewProbabilisticSampler(rate float64) *ProbabilisticSampler {
	if rate < 0 {
		rate = 0
	}
	if rate > 1 {
		rate = 1
	}
	return &ProbabilisticSampler{rate: uint64(rate * math.MaxUint64)}
}

// ShouldSample 判断是否采样
func (s *ProbabilisticSampler) ShouldSample(ctx *SamplingContext) SamplingDecision {
	if s.rate >= math.MaxUint64 {
		return SamplingDecisionSample
	}
	if s.rate == 0 {
		return SamplingDecisionDrop
	}
	// 使用随机数
	if randomUint64() < s.rate {
		return SamplingDecisionSample
	}
	return SamplingDecisionDrop
}

// GetRate 获取当前采样率
func (s *ProbabilisticSampler) GetRate() float64 {
	return float64(s.rate) / float64(math.MaxUint64)
}

// UpdateRate 更新采样率
func (s *ProbabilisticSampler) UpdateRate(rate float64) {
	if rate < 0 {
		rate = 0
	}
	if rate > 1 {
		rate = 1
	}
	atomic.StoreUint64(&s.rate, uint64(rate*math.MaxUint64))
}

// RateLimitingSampler 速率限制采样器
type RateLimitingSampler struct {
	maxPerSecond int
	tokens       int
	lastUpdate   time.Time
	mu           sync.Mutex
}

// NewRateLimitingSampler 创建速率限制采样器
func NewRateLimitingSampler(maxPerSecond int) *RateLimitingSampler {
	return &RateLimitingSampler{
		maxPerSecond: maxPerSecond,
		tokens:       maxPerSecond,
		lastUpdate:   time.Now(),
	}
}

// ShouldSample 判断是否采样
func (s *RateLimitingSampler) ShouldSample(ctx *SamplingContext) SamplingDecision {
	s.mu.Lock()
	defer s.mu.Unlock()

	now := time.Now()
	elapsed := now.Sub(s.lastUpdate)
	s.lastUpdate = now

	// 添加令牌
	tokensToAdd := int(elapsed.Seconds() * float64(s.maxPerSecond))
	s.tokens += tokensToAdd
	if s.tokens > s.maxPerSecond {
		s.tokens = s.maxPerSecond
	}

	// 消耗令牌
	if s.tokens > 0 {
		s.tokens--
		return SamplingDecisionSample
	}
	return SamplingDecisionDrop
}

// GetRate 获取当前采样率
func (s *RateLimitingSampler) GetRate() float64 {
	s.mu.Lock()
	defer s.mu.Unlock()
	return float64(s.tokens) / float64(s.maxPerSecond)
}

// UpdateRate 更新采样率
func (s *RateLimitingSampler) UpdateRate(rate float64) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.maxPerSecond = int(rate * 1000)
	s.tokens = s.maxPerSecond
}

// AdaptiveSampler 自适应采样器
type AdaptiveSampler struct {
	config        *SamplingConfig
	currentRate   uint64
	sampleCount   uint64
	decisionCount uint64
	cpuHistory    []float64
	memHistory    []float64
	mu            sync.RWMutex
	stopCh        chan struct{}
	lastGCNum     uint32
}

// NewAdaptiveSampler 创建自适应采样器
func NewAdaptiveSampler(config *SamplingConfig) *AdaptiveSampler {
	if config == nil {
		config = DefaultSamplingConfig()
	}

	sampler := &AdaptiveSampler{
		config:      config,
		currentRate: uint64(config.Rate * math.MaxUint64),
		cpuHistory:  make([]float64, 0, config.WindowSize),
		memHistory:  make([]float64, 0, config.WindowSize),
		stopCh:      make(chan struct{}),
	}

	// 启动自适应调整 goroutine
	go sampler.adaptiveLoop()

	return sampler
}

// ShouldSample 判断是否采样
func (s *AdaptiveSampler) ShouldSample(ctx *SamplingContext) SamplingDecision {
	atomic.AddUint64(&s.decisionCount, 1)

	rate := atomic.LoadUint64(&s.currentRate)
	if rate >= math.MaxUint64 {
		atomic.AddUint64(&s.sampleCount, 1)
		return SamplingDecisionSample
	}
	if rate == 0 {
		return SamplingDecisionDrop
	}

	if randomUint64() < rate {
		atomic.AddUint64(&s.sampleCount, 1)
		return SamplingDecisionSample
	}
	return SamplingDecisionDrop
}

// GetRate 获取当前采样率
func (s *AdaptiveSampler) GetRate() float64 {
	rate := atomic.LoadUint64(&s.currentRate)
	return float64(rate) / float64(math.MaxUint64)
}

// UpdateRate 更新采样率
func (s *AdaptiveSampler) UpdateRate(rate float64) {
	if rate < s.config.MinRate {
		rate = s.config.MinRate
	}
	if rate > s.config.MaxRate {
		rate = s.config.MaxRate
	}
	atomic.StoreUint64(&s.currentRate, uint64(rate*math.MaxUint64))
}

// Stop 停止自适应采样器
func (s *AdaptiveSampler) Stop() {
	close(s.stopCh)
}

// adaptiveLoop 自适应调整循环
func (s *AdaptiveSampler) adaptiveLoop() {
	ticker := time.NewTicker(s.config.AdaptiveInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			s.adjustRate()
		case <-s.stopCh:
			return
		}
	}
}

// adjustRate 调整采样率
func (s *AdaptiveSampler) adjustRate() {
	// 收集系统指标
	cpuUsage := getCPUUsage()
	memUsage := getMemoryUsage()

	s.mu.Lock()
	// 更新历史记录
	s.cpuHistory = append(s.cpuHistory, cpuUsage)
	s.memHistory = append(s.memHistory, memUsage)
	if len(s.cpuHistory) > s.config.WindowSize {
		s.cpuHistory = s.cpuHistory[1:]
	}
	if len(s.memHistory) > s.config.WindowSize {
		s.memHistory = s.memHistory[1:]
	}

	// 计算平均值
	avgCPU := average(s.cpuHistory)
	avgMem := average(s.memHistory)
	s.mu.Unlock()

	// 根据系统负载调整采样率
	currentRate := s.GetRate()
	newRate := currentRate

	if avgCPU > s.config.TargetCPU || avgMem > s.config.TargetMemory {
		// 系统负载高，降低采样率
		newRate = currentRate * 0.9
	} else if avgCPU < s.config.TargetCPU*0.7 && avgMem < s.config.TargetMemory*0.7 {
		// 系统负载低，增加采样率
		newRate = currentRate * 1.1
	}

	s.UpdateRate(newRate)
}

// GetStats 获取采样统计
func (s *AdaptiveSampler) GetStats() map[string]interface{} {
	return map[string]interface{}{
		"current_rate":   s.GetRate(),
		"sample_count":   atomic.LoadUint64(&s.sampleCount),
		"decision_count": atomic.LoadUint64(&s.decisionCount),
	}
}

// DynamicSampler 动态采样器（基于操作类型）
type DynamicSampler struct {
	defaultSampler Sampler
	operationRates map[string]Sampler
	mu             sync.RWMutex
}

// NewDynamicSampler 创建动态采样器
func NewDynamicSampler(defaultSampler Sampler) *DynamicSampler {
	if defaultSampler == nil {
		defaultSampler = NewFixedSampler(1.0)
	}
	return &DynamicSampler{
		defaultSampler: defaultSampler,
		operationRates: make(map[string]Sampler),
	}
}

// SetOperationSampler 为特定操作设置采样器
func (s *DynamicSampler) SetOperationSampler(operation string, sampler Sampler) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.operationRates[operation] = sampler
}

// ShouldSample 判断是否采样
func (s *DynamicSampler) ShouldSample(ctx *SamplingContext) SamplingDecision {
	s.mu.RLock()
	sampler, ok := s.operationRates[ctx.Operation]
	s.mu.RUnlock()

	if ok {
		return sampler.ShouldSample(ctx)
	}
	return s.defaultSampler.ShouldSample(ctx)
}

// GetRate 获取当前采样率
func (s *DynamicSampler) GetRate() float64 {
	return s.defaultSampler.GetRate()
}

// UpdateRate 更新默认采样率
func (s *DynamicSampler) UpdateRate(rate float64) {
	s.defaultSampler.UpdateRate(rate)
}

// SamplerFactory 采样器工厂
type SamplerFactory struct{}

// NewSamplerFactory 创建采样器工厂
func NewSamplerFactory() *SamplerFactory {
	return &SamplerFactory{}
}

// CreateSampler 根据配置创建采样器
func (f *SamplerFactory) CreateSampler(config *SamplingConfig) Sampler {
	switch config.Strategy {
	case SamplingStrategyFixed:
		return NewFixedSampler(config.Rate)
	case SamplingStrategyProbabilistic:
		return NewProbabilisticSampler(config.Rate)
	case SamplingStrategyRateLimiting:
		return NewRateLimitingSampler(config.MaxSamplesPerSecond)
	case SamplingStrategyAdaptive:
		return NewAdaptiveSampler(config)
	case SamplingStrategyDynamic:
		return NewDynamicSampler(NewFixedSampler(config.Rate))
	default:
		return NewFixedSampler(config.Rate)
	}
}

// 辅助函数

// hashTraceID 计算 TraceID 的哈希值
func hashTraceID(traceID string) float64 {
	hash := uint64(0)
	for i := 0; i < len(traceID); i++ {
		hash = hash*31 + uint64(traceID[i])
	}
	return float64(hash) / float64(^uint64(0))
}

// randomUint64 生成随机 uint64
func randomUint64() uint64 {
	return uint64(time.Now().UnixNano())
}

// getCPUUsage 获取 CPU 使用率
func getCPUUsage() float64 {
	// 简化实现，实际应该使用更精确的测量
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return 50.0 // 模拟值
}

// getMemoryUsage 获取内存使用率
func getMemoryUsage() float64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	// 计算内存使用率（简化）
	totalMemory := m.Sys
	if totalMemory == 0 {
		return 0
	}
	return float64(m.Alloc) / float64(totalMemory) * 100
}

// average 计算平均值
func average(values []float64) float64 {
	if len(values) == 0 {
		return 0
	}
	sum := 0.0
	for _, v := range values {
		sum += v
	}
	return sum / float64(len(values))
}

// CompositeSampler 复合采样器（组合多种策略）
type CompositeSampler struct {
	samplers []Sampler
	mode     string // "all" 或 "any"
}

// NewCompositeSampler 创建复合采样器
func NewCompositeSampler(mode string, samplers ...Sampler) *CompositeSampler {
	if mode != "all" && mode != "any" {
		mode = "any"
	}
	return &CompositeSampler{
		samplers: samplers,
		mode:     mode,
	}
}

// ShouldSample 判断是否采样
func (s *CompositeSampler) ShouldSample(ctx *SamplingContext) SamplingDecision {
	if len(s.samplers) == 0 {
		return SamplingDecisionSample
	}

	if s.mode == "all" {
		// 所有采样器都同意才采样
		for _, sampler := range s.samplers {
			if sampler.ShouldSample(ctx) == SamplingDecisionDrop {
				return SamplingDecisionDrop
			}
		}
		return SamplingDecisionSample
	}

	// 任一采样器同意就采样
	for _, sampler := range s.samplers {
		if sampler.ShouldSample(ctx) == SamplingDecisionSample {
			return SamplingDecisionSample
		}
	}
	return SamplingDecisionDrop
}

// GetRate 获取当前采样率
func (s *CompositeSampler) GetRate() float64 {
	if len(s.samplers) == 0 {
		return 1.0
	}
	sum := 0.0
	for _, sampler := range s.samplers {
		sum += sampler.GetRate()
	}
	return sum / float64(len(s.samplers))
}

// UpdateRate 更新采样率
func (s *CompositeSampler) UpdateRate(rate float64) {
	for _, sampler := range s.samplers {
		sampler.UpdateRate(rate)
	}
}

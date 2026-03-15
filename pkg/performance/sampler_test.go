package performance

import (
	"sync"
	"testing"
	"time"
)

func TestDefaultSamplingConfig(t *testing.T) {
	config := DefaultSamplingConfig()
	if config == nil {
		t.Fatal("config should not be nil")
	}
	if config.Strategy != SamplingStrategyAdaptive {
		t.Errorf("Strategy = %v, want %v", config.Strategy, SamplingStrategyAdaptive)
	}
	if config.Rate != 1.0 {
		t.Errorf("Rate = %f, want 1.0", config.Rate)
	}
	if config.MaxSamplesPerSecond != 1000 {
		t.Errorf("MaxSamplesPerSecond = %d, want 1000", config.MaxSamplesPerSecond)
	}
	if config.AdaptiveInterval != 5*time.Second {
		t.Errorf("AdaptiveInterval = %v, want 5s", config.AdaptiveInterval)
	}
	if config.MinRate != 0.01 {
		t.Errorf("MinRate = %f, want 0.01", config.MinRate)
	}
	if config.MaxRate != 1.0 {
		t.Errorf("MaxRate = %f, want 1.0", config.MaxRate)
	}
	if config.TargetCPU != 70.0 {
		t.Errorf("TargetCPU = %f, want 70.0", config.TargetCPU)
	}
	if config.TargetMemory != 80.0 {
		t.Errorf("TargetMemory = %f, want 80.0", config.TargetMemory)
	}
	if config.WindowSize != 10 {
		t.Errorf("WindowSize = %d, want 10", config.WindowSize)
	}
}

func TestNewFixedSampler(t *testing.T) {
	tests := []struct {
		name     string
		rate     float64
		expected float64
	}{
		{"normal rate", 0.5, 0.5},
		{"full rate", 1.0, 1.0},
		{"zero rate", 0.0, 0.0},
		{"negative rate", -0.5, 0.0},
		{"over max rate", 1.5, 1.0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			sampler := NewFixedSampler(tt.rate)
			if sampler == nil {
				t.Fatal("sampler should not be nil")
			}
			if sampler.GetRate() != tt.expected {
				t.Errorf("GetRate() = %f, want %f", sampler.GetRate(), tt.expected)
			}
		})
	}
}

func TestFixedSamplerShouldSample(t *testing.T) {
	tests := []struct {
		name     string
		rate     float64
		expected SamplingDecision
	}{
		{"full sample", 1.0, SamplingDecisionSample},
		{"no sample", 0.0, SamplingDecisionDrop},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			sampler := NewFixedSampler(tt.rate)
			ctx := &SamplingContext{
				TraceID:   "test-trace-id",
				Operation: "test-operation",
			}
			decision := sampler.ShouldSample(ctx)
			if decision != tt.expected {
				t.Errorf("ShouldSample() = %v, want %v", decision, tt.expected)
			}
		})
	}
}

func TestFixedSamplerUpdateRate(t *testing.T) {
	sampler := NewFixedSampler(0.5)
	if sampler.GetRate() != 0.5 {
		t.Errorf("initial rate = %f, want 0.5", sampler.GetRate())
	}

	sampler.UpdateRate(0.8)
	if sampler.GetRate() != 0.8 {
		t.Errorf("updated rate = %f, want 0.8", sampler.GetRate())
	}

	// 测试边界值
	sampler.UpdateRate(-0.1)
	if sampler.GetRate() != 0.0 {
		t.Errorf("negative rate = %f, want 0.0", sampler.GetRate())
	}

	sampler.UpdateRate(1.5)
	if sampler.GetRate() != 1.0 {
		t.Errorf("over max rate = %f, want 1.0", sampler.GetRate())
	}
}

func TestNewProbabilisticSampler(t *testing.T) {
	sampler := NewProbabilisticSampler(0.5)
	if sampler == nil {
		t.Fatal("sampler should not be nil")
	}
	if sampler.GetRate() < 0.49 || sampler.GetRate() > 0.51 {
		t.Errorf("rate = %f, want ~0.5", sampler.GetRate())
	}

	// 测试边界值
	sampler2 := NewProbabilisticSampler(-0.1)
	if sampler2.GetRate() != 0.0 {
		t.Errorf("negative rate = %f, want 0.0", sampler2.GetRate())
	}

	sampler3 := NewProbabilisticSampler(1.5)
	if sampler3.GetRate() != 1.0 {
		t.Errorf("over max rate = %f, want 1.0", sampler3.GetRate())
	}
}

func TestProbabilisticSamplerShouldSample(t *testing.T) {
	sampler := NewProbabilisticSampler(1.0)
	ctx := &SamplingContext{TraceID: "test"}
	if sampler.ShouldSample(ctx) != SamplingDecisionSample {
		t.Error("full rate should sample")
	}

	sampler2 := NewProbabilisticSampler(0.0)
	if sampler2.ShouldSample(ctx) != SamplingDecisionDrop {
		t.Error("zero rate should drop")
	}
}

func TestProbabilisticSamplerUpdateRate(t *testing.T) {
	sampler := NewProbabilisticSampler(0.5)
	sampler.UpdateRate(0.7)
	if sampler.GetRate() < 0.69 || sampler.GetRate() > 0.71 {
		t.Errorf("updated rate = %f, want ~0.7", sampler.GetRate())
	}
}

func TestNewRateLimitingSampler(t *testing.T) {
	sampler := NewRateLimitingSampler(100)
	if sampler == nil {
		t.Fatal("sampler should not be nil")
	}
	if sampler.GetRate() != 1.0 {
		t.Errorf("initial rate = %f, want 1.0", sampler.GetRate())
	}
}

func TestRateLimitingSamplerShouldSample(t *testing.T) {
	sampler := NewRateLimitingSampler(10) // 每秒 10 个
	ctx := &SamplingContext{Operation: "test"}

	// 应该能采样 10 个
	sampleCount := 0
	for i := 0; i < 20; i++ {
		if sampler.ShouldSample(ctx) == SamplingDecisionSample {
			sampleCount++
		}
	}
	if sampleCount < 10 {
		t.Errorf("sampled %d, want >= 10", sampleCount)
	}
}

func TestRateLimitingSamplerUpdateRate(t *testing.T) {
	sampler := NewRateLimitingSampler(100)
	sampler.UpdateRate(0.5)
	if sampler.GetRate() != 0.5 {
		t.Errorf("updated rate = %f, want 0.5", sampler.GetRate())
	}
}

func TestNewAdaptiveSampler(t *testing.T) {
	config := DefaultSamplingConfig()
	sampler := NewAdaptiveSampler(config)
	if sampler == nil {
		t.Fatal("sampler should not be nil")
	}
	defer sampler.Stop()

	if sampler.GetRate() != config.Rate {
		t.Errorf("initial rate = %f, want %f", sampler.GetRate(), config.Rate)
	}
}

func TestAdaptiveSamplerShouldSample(t *testing.T) {
	config := DefaultSamplingConfig()
	sampler := NewAdaptiveSampler(config)
	defer sampler.Stop()

	ctx := &SamplingContext{TraceID: "test"}

	// 全采样
	sampler.UpdateRate(1.0)
	if sampler.ShouldSample(ctx) != SamplingDecisionSample {
		t.Error("full rate should sample")
	}

	// 不采样
	sampler.UpdateRate(0.0)
	if sampler.ShouldSample(ctx) != SamplingDecisionDrop {
		t.Error("zero rate should drop")
	}
}

func TestAdaptiveSamplerUpdateRate(t *testing.T) {
	config := DefaultSamplingConfig()
	sampler := NewAdaptiveSampler(config)
	defer sampler.Stop()

	// 测试 MinRate 限制
	sampler.UpdateRate(0.001)
	if sampler.GetRate() != config.MinRate {
		t.Errorf("min rate = %f, want %f", sampler.GetRate(), config.MinRate)
	}

	// 测试 MaxRate 限制
	sampler.UpdateRate(1.5)
	if sampler.GetRate() != config.MaxRate {
		t.Errorf("max rate = %f, want %f", sampler.GetRate(), config.MaxRate)
	}

	// 测试正常值
	sampler.UpdateRate(0.5)
	if sampler.GetRate() != 0.5 {
		t.Errorf("normal rate = %f, want 0.5", sampler.GetRate())
	}
}

func TestAdaptiveSamplerGetStats(t *testing.T) {
	config := DefaultSamplingConfig()
	sampler := NewAdaptiveSampler(config)
	defer sampler.Stop()

	stats := sampler.GetStats()
	if stats == nil {
		t.Fatal("stats should not be nil")
	}
	if _, ok := stats["current_rate"]; !ok {
		t.Error("should contain current_rate")
	}
	if _, ok := stats["sample_count"]; !ok {
		t.Error("should contain sample_count")
	}
	if _, ok := stats["decision_count"]; !ok {
		t.Error("should contain decision_count")
	}
}

func TestNewDynamicSampler(t *testing.T) {
	defaultSampler := NewFixedSampler(0.5)
	sampler := NewDynamicSampler(defaultSampler)
	if sampler == nil {
		t.Fatal("sampler should not be nil")
	}
	if sampler.GetRate() != 0.5 {
		t.Errorf("rate = %f, want 0.5", sampler.GetRate())
	}
}

func TestDynamicSamplerSetOperationSampler(t *testing.T) {
	defaultSampler := NewFixedSampler(0.5)
	sampler := NewDynamicSampler(defaultSampler)

	// 为特定操作设置采样器
	operationSampler := NewFixedSampler(1.0)
	sampler.SetOperationSampler("critical-op", operationSampler)

	// 特定操作应该全采样
	ctx := &SamplingContext{Operation: "critical-op"}
	if sampler.ShouldSample(ctx) != SamplingDecisionSample {
		t.Error("critical-op should sample")
	}
}

func TestDynamicSamplerUpdateRate(t *testing.T) {
	defaultSampler := NewFixedSampler(0.5)
	sampler := NewDynamicSampler(defaultSampler)

	sampler.UpdateRate(0.8)
	if sampler.GetRate() != 0.8 {
		t.Errorf("updated rate = %f, want 0.8", sampler.GetRate())
	}
}

func TestNewDynamicSamplerWithNil(t *testing.T) {
	sampler := NewDynamicSampler(nil)
	if sampler == nil {
		t.Fatal("sampler should not be nil")
	}
	if sampler.GetRate() != 1.0 {
		t.Errorf("default rate = %f, want 1.0", sampler.GetRate())
	}
}

func TestSamplerFactory(t *testing.T) {
	factory := NewSamplerFactory()
	if factory == nil {
		t.Fatal("factory should not be nil")
	}

	tests := []struct {
		strategy SamplingStrategy
	}{
		{SamplingStrategyFixed},
		{SamplingStrategyProbabilistic},
		{SamplingStrategyRateLimiting},
		{SamplingStrategyDynamic},
		{SamplingStrategy("unknown")}, // 默认
	}

	for _, tt := range tests {
		t.Run(string(tt.strategy), func(t *testing.T) {
			config := &SamplingConfig{
				Strategy:            tt.strategy,
				Rate:                0.5,
				MaxSamplesPerSecond: 100,
			}
			sampler := factory.CreateSampler(config)
			if sampler == nil {
				t.Fatal("sampler should not be nil")
			}
		})
	}
}

func TestSamplerFactoryAdaptive(t *testing.T) {
	factory := NewSamplerFactory()
	config := &SamplingConfig{
		Strategy: SamplingStrategyAdaptive,
		Rate:     0.5,
	}
	sampler := factory.CreateSampler(config)
	if sampler == nil {
		t.Fatal("sampler should not be nil")
	}
	
	// 自适应采样器需要停止
	if adaptiveSampler, ok := sampler.(*AdaptiveSampler); ok {
		adaptiveSampler.Stop()
	}
}

func TestCompositeSampler(t *testing.T) {
	sampler1 := NewFixedSampler(1.0) // 总是采样
	sampler2 := NewFixedSampler(0.0) // 从不采样

	tests := []struct {
		name     string
		mode     string
		expected SamplingDecision
	}{
		{"any mode with one yes", "any", SamplingDecisionSample},
		{"all mode with one no", "all", SamplingDecisionDrop},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			sampler := NewCompositeSampler(tt.mode, sampler1, sampler2)
			ctx := &SamplingContext{TraceID: "test"}
			decision := sampler.ShouldSample(ctx)
			if decision != tt.expected {
				t.Errorf("ShouldSample() = %v, want %v", decision, tt.expected)
			}
		})
	}
}

func TestCompositeSamplerEmpty(t *testing.T) {
	sampler := NewCompositeSampler("any")
	ctx := &SamplingContext{TraceID: "test"}
	decision := sampler.ShouldSample(ctx)
	if decision != SamplingDecisionSample {
		t.Errorf("empty sampler should sample, got %v", decision)
	}
}

func TestCompositeSamplerGetRate(t *testing.T) {
	sampler1 := NewFixedSampler(0.5)
	sampler2 := NewFixedSampler(1.0)
	sampler := NewCompositeSampler("any", sampler1, sampler2)

	rate := sampler.GetRate()
	if rate != 0.75 {
		t.Errorf("rate = %f, want 0.75", rate)
	}
}

func TestCompositeSamplerUpdateRate(t *testing.T) {
	sampler1 := NewFixedSampler(0.5)
	sampler2 := NewFixedSampler(0.5)
	sampler := NewCompositeSampler("any", sampler1, sampler2)

	sampler.UpdateRate(0.8)
	if sampler1.GetRate() != 0.8 {
		t.Errorf("sampler1 rate = %f, want 0.8", sampler1.GetRate())
	}
	if sampler2.GetRate() != 0.8 {
		t.Errorf("sampler2 rate = %f, want 0.8", sampler2.GetRate())
	}
}

func TestSamplingContext(t *testing.T) {
	ctx := &SamplingContext{
		TraceID:    "test-trace-id",
		SpanID:     "test-span-id",
		Operation:  "test-operation",
		StartTime:  time.Now(),
		Attributes: map[string]interface{}{"key": "value"},
	}

	if ctx.TraceID != "test-trace-id" {
		t.Error("TraceID mismatch")
	}
	if ctx.SpanID != "test-span-id" {
		t.Error("SpanID mismatch")
	}
	if ctx.Operation != "test-operation" {
		t.Error("Operation mismatch")
	}
	if ctx.StartTime.IsZero() {
		t.Error("StartTime should not be zero")
	}
	if ctx.Attributes == nil {
		t.Error("Attributes should not be nil")
	}
}

func TestSamplingDecision(t *testing.T) {
	if SamplingDecisionDrop != 0 {
		t.Error("SamplingDecisionDrop should be 0")
	}
	if SamplingDecisionSample != 1 {
		t.Error("SamplingDecisionSample should be 1")
	}
}

func TestSamplerConcurrency(t *testing.T) {
	sampler := NewProbabilisticSampler(0.5)
	ctx := &SamplingContext{TraceID: "test"}

	var wg sync.WaitGroup
	totalCount := 100

	for i := 0; i < totalCount; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = sampler.ShouldSample(ctx)
		}()
	}

	wg.Wait()
}

func TestHashTraceID(t *testing.T) {
	hash1 := hashTraceID("test-id-1")
	hash2 := hashTraceID("test-id-1")
	hash3 := hashTraceID("test-id-2")

	if hash1 != hash2 {
		t.Error("same id should produce same hash")
	}
	if hash1 == hash3 {
		t.Error("different ids should produce different hashes")
	}
	if hash1 < 0 || hash1 >= 1 {
		t.Errorf("hash should be in [0, 1), got %f", hash1)
	}
}

func TestRandomUint64(t *testing.T) {
	r1 := randomUint64()
	r2 := randomUint64()

	// 两次调用应该返回不同的值（概率极低相同）
	if r1 == r2 {
		t.Error("random numbers should be different")
	}
}

func TestAverage(t *testing.T) {
	if average([]float64{}) != 0.0 {
		t.Error("average of empty slice should be 0")
	}
	if average([]float64{5.0}) != 5.0 {
		t.Error("average of single element should be that element")
	}
	if average([]float64{5.0, 6.0}) != 5.5 {
		t.Error("average of [5, 6] should be 5.5")
	}
	if average([]float64{4.0, 5.0, 6.0}) != 5.0 {
		t.Error("average of [4, 5, 6] should be 5.0")
	}
}

func TestGetMemoryUsage(t *testing.T) {
	usage := getMemoryUsage()
	if usage < 0 || usage >= 100 {
		t.Errorf("memory usage should be in [0, 100), got %f", usage)
	}
}

func TestGetCPUUsage(t *testing.T) {
	usage := getCPUUsage()
	if usage != 50.0 {
		t.Errorf("cpu usage = %f, want 50.0", usage)
	}
}

func BenchmarkFixedSampler(b *testing.B) {
	sampler := NewFixedSampler(0.5)
	ctx := &SamplingContext{TraceID: "test"}
	for i := 0; i < b.N; i++ {
		sampler.ShouldSample(ctx)
	}
}

func BenchmarkProbabilisticSampler(b *testing.B) {
	sampler := NewProbabilisticSampler(0.5)
	ctx := &SamplingContext{TraceID: "test"}
	for i := 0; i < b.N; i++ {
		sampler.ShouldSample(ctx)
	}
}

func BenchmarkRateLimitingSampler(b *testing.B) {
	sampler := NewRateLimitingSampler(10000)
	ctx := &SamplingContext{Operation: "test"}
	for i := 0; i < b.N; i++ {
		sampler.ShouldSample(ctx)
	}
}

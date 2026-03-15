// Package performance provides performance optimization utilities
// for the OTLP Go SDK.
package performance

import (
	"fmt"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
)

// OptimizationLevel 优化级别
type OptimizationLevel string

const (
	// OptimizationLevelCritical 严重问题
	OptimizationLevelCritical OptimizationLevel = "critical"
	// OptimizationLevelWarning 警告
	OptimizationLevelWarning OptimizationLevel = "warning"
	// OptimizationLevelInfo 信息
	OptimizationLevelInfo OptimizationLevel = "info"
	// OptimizationLevelSuggestion 建议
	OptimizationLevelSuggestion OptimizationLevel = "suggestion"
)

// OptimizationCategory 优化类别
type OptimizationCategory string

const (
	// OptimizationCategoryMemory 内存优化
	OptimizationCategoryMemory OptimizationCategory = "memory"
	// OptimizationCategoryCPU CPU 优化
	OptimizationCategoryCPU OptimizationCategory = "cpu"
	// OptimizationCategoryGC GC 优化
	OptimizationCategoryGC OptimizationCategory = "gc"
	// OptimizationCategoryGoroutine Goroutine 优化
	OptimizationCategoryGoroutine OptimizationCategory = "goroutine"
	// OptimizationCategoryConfig 配置优化
	OptimizationCategoryConfig OptimizationCategory = "config"
)

// OptimizationSuggestion 优化建议
type OptimizationSuggestion struct {
	ID          string
	Level       OptimizationLevel
	Category    OptimizationCategory
	Title       string
	Description string
	Impact      string
	Solution    string
	Config      map[string]interface{}
}

// OptimizerConfig 优化器配置
type OptimizerConfig struct {
	// EnableAutoOptimize 启用自动优化
	EnableAutoOptimize bool
	// MemoryThresholdMB 内存阈值（MB）
	MemoryThresholdMB float64
	// GoroutineThreshold Goroutine 阈值
	GoroutineThreshold int
	// GCThresholdPercent GC CPU 使用阈值（%）
	GCThresholdPercent float64
	// CheckInterval 检查间隔
	CheckInterval time.Duration
	// MinSuggestions 最小建议数
	MinSuggestions int
	// MaxSuggestions 最大建议数
	MaxSuggestions int
}

// DefaultOptimizerConfig 返回默认配置
func DefaultOptimizerConfig() *OptimizerConfig {
	return &OptimizerConfig{
		EnableAutoOptimize: false,
		MemoryThresholdMB:  512,
		GoroutineThreshold: 10000,
		GCThresholdPercent: 10.0,
		CheckInterval:      30 * time.Second,
		MinSuggestions:     1,
		MaxSuggestions:     20,
	}
}

// PerformanceOptimizer 性能优化器
type PerformanceOptimizer struct {
	config       *OptimizerConfig
	suggestions  []OptimizationSuggestion
	metricsCollector *RuntimeMetricsCollector
	mu           sync.RWMutex
	stopCh       chan struct{}
	running      bool
	lastSnapshot map[string]interface{}
}

// NewPerformanceOptimizer 创建性能优化器
func NewPerformanceOptimizer(config *OptimizerConfig, collector *RuntimeMetricsCollector) *PerformanceOptimizer {
	if config == nil {
		config = DefaultOptimizerConfig()
	}
	return &PerformanceOptimizer{
		config:           config,
		suggestions:      make([]OptimizationSuggestion, 0),
		metricsCollector: collector,
		stopCh:           make(chan struct{}),
		lastSnapshot:     make(map[string]interface{}),
	}
}

// Start 启动优化器
func (o *PerformanceOptimizer) Start() error {
	o.mu.Lock()
	defer o.mu.Unlock()

	if o.running {
		return fmt.Errorf("optimizer already running")
	}

	o.running = true

	// 如果启用了自动优化，启动检查循环
	if o.config.EnableAutoOptimize {
		go o.optimizationLoop()
	}

	// 立即执行一次分析
	go o.Analyze()

	return nil
}

// Stop 停止优化器
func (o *PerformanceOptimizer) Stop() error {
	o.mu.Lock()
	defer o.mu.Unlock()

	if !o.running {
		return fmt.Errorf("optimizer not running")
	}

	o.running = false
	close(o.stopCh)
	return nil
}

// Analyze 分析性能并生成建议
func (o *PerformanceOptimizer) Analyze() []OptimizationSuggestion {
	o.mu.Lock()
	defer o.mu.Unlock()

	suggestions := make([]OptimizationSuggestion, 0)

	// 获取当前运行时快照
	snapshot := GetRuntimeSnapshot()
	o.lastSnapshot = snapshot

	// 内存分析
	suggestions = append(suggestions, o.analyzeMemory(snapshot)...)

	// GC 分析
	suggestions = append(suggestions, o.analyzeGC(snapshot)...)

	// Goroutine 分析
	suggestions = append(suggestions, o.analyzeGoroutines(snapshot)...)

	// 配置分析
	suggestions = append(suggestions, o.analyzeConfig(snapshot)...)

	// 排序：严重问题在前
	sort.Slice(suggestions, func(i, j int) bool {
		levelOrder := map[OptimizationLevel]int{
			OptimizationLevelCritical:   0,
			OptimizationLevelWarning:    1,
			OptimizationLevelInfo:       2,
			OptimizationLevelSuggestion: 3,
		}
		return levelOrder[suggestions[i].Level] < levelOrder[suggestions[j].Level]
	})

	// 限制建议数量
	if len(suggestions) > o.config.MaxSuggestions {
		suggestions = suggestions[:o.config.MaxSuggestions]
	}

	o.suggestions = suggestions
	return suggestions
}

// GetSuggestions 获取所有建议
func (o *PerformanceOptimizer) GetSuggestions() []OptimizationSuggestion {
	o.mu.RLock()
	defer o.mu.RUnlock()

	result := make([]OptimizationSuggestion, len(o.suggestions))
	copy(result, o.suggestions)
	return result
}

// GetSuggestionsByLevel 按级别获取建议
func (o *PerformanceOptimizer) GetSuggestionsByLevel(level OptimizationLevel) []OptimizationSuggestion {
	o.mu.RLock()
	defer o.mu.RUnlock()

	result := make([]OptimizationSuggestion, 0)
	for _, s := range o.suggestions {
		if s.Level == level {
			result = append(result, s)
		}
	}
	return result
}

// GetSuggestionsByCategory 按类别获取建议
func (o *PerformanceOptimizer) GetSuggestionsByCategory(category OptimizationCategory) []OptimizationSuggestion {
	o.mu.RLock()
	defer o.mu.RUnlock()

	result := make([]OptimizationSuggestion, 0)
	for _, s := range o.suggestions {
		if s.Category == category {
			result = append(result, s)
		}
	}
	return result
}

// ClearSuggestions 清除所有建议
func (o *PerformanceOptimizer) ClearSuggestions() {
	o.mu.Lock()
	defer o.mu.Unlock()
	o.suggestions = make([]OptimizationSuggestion, 0)
}

// optimizationLoop 优化检查循环
func (o *PerformanceOptimizer) optimizationLoop() {
	ticker := time.NewTicker(o.config.CheckInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			o.Analyze()
		case <-o.stopCh:
			return
		}
	}
}

// analyzeMemory 分析内存使用
func (o *PerformanceOptimizer) analyzeMemory(snapshot map[string]interface{}) []OptimizationSuggestion {
	suggestions := make([]OptimizationSuggestion, 0)

	memAlloc, ok := snapshot["mem_alloc"].(uint64)
	if !ok {
		return suggestions
	}

	memAllocMB := float64(memAlloc) / 1024 / 1024

	// 检查内存使用是否超过阈值
	if memAllocMB > o.config.MemoryThresholdMB {
		suggestions = append(suggestions, OptimizationSuggestion{
			ID:          "MEM-001",
			Level:       OptimizationLevelCritical,
			Category:    OptimizationCategoryMemory,
			Title:       "内存使用过高",
			Description: fmt.Sprintf("当前内存使用 %.2f MB，超过阈值 %.2f MB", memAllocMB, o.config.MemoryThresholdMB),
			Impact:      "可能导致 OOM 或频繁的 GC，影响应用性能",
			Solution:    "1. 检查内存泄漏\n2. 使用对象池复用对象\n3. 减少不必要的内存分配\n4. 优化数据结构",
			Config: map[string]interface{}{
				"current_memory_mb": memAllocMB,
				"threshold_mb":      o.config.MemoryThresholdMB,
			},
		})
	}

	// 检查堆内存
	heapAlloc, ok := snapshot["mem_heap_alloc"].(uint64)
	if ok {
		heapAllocMB := float64(heapAlloc) / 1024 / 1024
		if heapAllocMB > o.config.MemoryThresholdMB*0.8 {
			suggestions = append(suggestions, OptimizationSuggestion{
				ID:          "MEM-002",
				Level:       OptimizationLevelWarning,
				Category:    OptimizationCategoryMemory,
				Title:       "堆内存使用较高",
				Description: fmt.Sprintf("当前堆内存使用 %.2f MB", heapAllocMB),
				Impact:      "可能导致 GC 压力增加",
				Solution:    "1. 检查对象生命周期\n2. 使用 sync.Pool 复用对象\n3. 预分配切片容量",
				Config: map[string]interface{}{
					"heap_alloc_mb": heapAllocMB,
				},
			})
		}
	}

	return suggestions
}

// analyzeGC 分析 GC 情况
func (o *PerformanceOptimizer) analyzeGC(snapshot map[string]interface{}) []OptimizationSuggestion {
	suggestions := make([]OptimizationSuggestion, 0)

	gcCPUFraction, ok := snapshot["gc_cpu_fraction"].(float64)
	if !ok {
		return suggestions
	}

	gcPercent := gcCPUFraction * 100

	// 检查 GC CPU 使用
	if gcPercent > o.config.GCThresholdPercent {
		suggestions = append(suggestions, OptimizationSuggestion{
			ID:          "GC-001",
			Level:       OptimizationLevelWarning,
			Category:    OptimizationCategoryGC,
			Title:       "GC CPU 使用率过高",
			Description: fmt.Sprintf("GC CPU 使用率为 %.2f%%，超过阈值 %.2f%%", gcPercent, o.config.GCThresholdPercent),
			Impact:      "GC 开销过大，影响应用性能",
			Solution:    "1. 增加 GOGC 值\n2. 减少内存分配\n3. 使用对象池\n4. 优化内存使用模式",
			Config: map[string]interface{}{
				"gc_cpu_percent": gcPercent,
				"threshold":      o.config.GCThresholdPercent,
			},
		})
	}

	gcCount, ok := snapshot["gc_count"].(uint32)
	if ok && gcCount > 100 {
		suggestions = append(suggestions, OptimizationSuggestion{
			ID:          "GC-002",
			Level:       OptimizationLevelInfo,
			Category:    OptimizationCategoryGC,
			Title:       "GC 次数较多",
			Description: fmt.Sprintf("已执行 %d 次 GC", gcCount),
			Impact:      "频繁的 GC 可能影响性能",
			Solution:    "1. 检查内存分配模式\n2. 考虑使用 sync.Pool\n3. 调整 GOGC 值",
			Config: map[string]interface{}{
				"gc_count": gcCount,
			},
		})
	}

	return suggestions
}

// analyzeGoroutines 分析 Goroutine 情况
func (o *PerformanceOptimizer) analyzeGoroutines(snapshot map[string]interface{}) []OptimizationSuggestion {
	suggestions := make([]OptimizationSuggestion, 0)

	goroutines, ok := snapshot["goroutines"].(int)
	if !ok {
		return suggestions
	}

	// 检查 Goroutine 数量
	if goroutines > o.config.GoroutineThreshold {
		suggestions = append(suggestions, OptimizationSuggestion{
			ID:          "GR-001",
			Level:       OptimizationLevelCritical,
			Category:    OptimizationCategoryGoroutine,
			Title:       "Goroutine 数量过多",
			Description: fmt.Sprintf("当前有 %d 个 Goroutine，超过阈值 %d", goroutines, o.config.GoroutineThreshold),
			Impact:      "可能导致内存泄漏或调度开销增加",
			Solution:    "1. 检查 Goroutine 泄漏\n2. 使用 Worker Pool 限制并发\n3. 确保 Goroutine 正确退出",
			Config: map[string]interface{}{
				"goroutine_count": goroutines,
				"threshold":       o.config.GoroutineThreshold,
			},
		})
	} else if goroutines > o.config.GoroutineThreshold/2 {
		suggestions = append(suggestions, OptimizationSuggestion{
			ID:          "GR-002",
			Level:       OptimizationLevelInfo,
			Category:    OptimizationCategoryGoroutine,
			Title:       "Goroutine 数量较多",
			Description: fmt.Sprintf("当前有 %d 个 Goroutine", goroutines),
			Impact:      "可能需要注意 Goroutine 管理",
			Solution:    "1. 监控 Goroutine 增长趋势\n2. 使用 pprof 分析 Goroutine 状态",
			Config: map[string]interface{}{
				"goroutine_count": goroutines,
			},
		})
	}

	return suggestions
}

// analyzeConfig 分析配置
func (o *PerformanceOptimizer) analyzeConfig(snapshot map[string]interface{}) []OptimizationSuggestion {
	suggestions := make([]OptimizationSuggestion, 0)

	// 检查 GOMAXPROCS
	maxProcs := runtime.GOMAXPROCS(0)
	numCPU := runtime.NumCPU()

	if maxProcs < numCPU {
		suggestions = append(suggestions, OptimizationSuggestion{
			ID:          "CFG-001",
			Level:       OptimizationLevelSuggestion,
			Category:    OptimizationCategoryConfig,
			Title:       "GOMAXPROCS 设置可能过低",
			Description: fmt.Sprintf("GOMAXPROCS=%d，但 CPU 核心数为 %d", maxProcs, numCPU),
			Impact:      "可能无法充分利用 CPU 资源",
			Solution:    "考虑将 GOMAXPROCS 设置为 CPU 核心数或更高（如果存在 I/O 等待）",
			Config: map[string]interface{}{
				"gomaxprocs": maxProcs,
				"num_cpu":    numCPU,
			},
		})
	}

	// 检查 GOGC
	gcPercent := "N/A"
	// 使用环境变量检查
	if gogc := osGetenv("GOGC"); gogc != "" {
		gcPercent = gogc
	}

	suggestions = append(suggestions, OptimizationSuggestion{
		ID:          "CFG-002",
		Level:       OptimizationLevelInfo,
		Category:    OptimizationCategoryConfig,
		Title:       "GOGC 配置信息",
		Description: fmt.Sprintf("当前 GOGC=%s", gcPercent),
		Impact:      "GOGC 控制 GC 触发阈值",
		Solution:    "如果 GC 开销过高，可以考虑增加 GOGC 值（如 200 或更高）",
		Config: map[string]interface{}{
			"gogc": gcPercent,
		},
	})

	return suggestions
}

// osGetenv 包装函数，便于测试
var osGetenv = func(key string) string {
	return ""
}

// GenerateReport 生成优化报告
func (o *PerformanceOptimizer) GenerateReport() string {
	o.mu.RLock()
	suggestions := make([]OptimizationSuggestion, len(o.suggestions))
	copy(suggestions, o.suggestions)
	o.mu.RUnlock()

	var sb strings.Builder

	sb.WriteString("=" + strings.Repeat("=", 60) + "\n")
	sb.WriteString("性能优化报告\n")
	sb.WriteString("生成时间: " + time.Now().Format("2006-01-02 15:04:05") + "\n")
	sb.WriteString("=" + strings.Repeat("=", 60) + "\n\n")

	if len(suggestions) == 0 {
		sb.WriteString("✓ 未发现性能问题\n")
		return sb.String()
	}

	// 统计
	criticalCount := 0
	warningCount := 0
	infoCount := 0
	for _, s := range suggestions {
		switch s.Level {
		case OptimizationLevelCritical:
			criticalCount++
		case OptimizationLevelWarning:
			warningCount++
		case OptimizationLevelInfo:
			infoCount++
		}
	}

	sb.WriteString(fmt.Sprintf("发现 %d 个性能问题:\n", len(suggestions)))
	sb.WriteString(fmt.Sprintf("  - 严重: %d\n", criticalCount))
	sb.WriteString(fmt.Sprintf("  - 警告: %d\n", warningCount))
	sb.WriteString(fmt.Sprintf("  - 信息: %d\n\n", infoCount))

	// 详细建议
	for i, s := range suggestions {
		var icon string
		switch s.Level {
		case OptimizationLevelCritical:
			icon = "🔴"
		case OptimizationLevelWarning:
			icon = "🟡"
		case OptimizationLevelInfo:
			icon = "🔵"
		default:
			icon = "🟢"
		}

		sb.WriteString(fmt.Sprintf("%d. %s [%s] %s\n", i+1, icon, s.Level, s.Title))
		sb.WriteString(fmt.Sprintf("   ID: %s | 类别: %s\n", s.ID, s.Category))
		sb.WriteString(fmt.Sprintf("   描述: %s\n", s.Description))
		sb.WriteString(fmt.Sprintf("   影响: %s\n", s.Impact))
		sb.WriteString(fmt.Sprintf("   解决方案:\n%s\n", formatSolution(s.Solution)))
		sb.WriteString("\n")
	}

	return sb.String()
}

// formatSolution 格式化解决方案
func formatSolution(solution string) string {
	lines := strings.Split(solution, "\n")
	var result []string
	for _, line := range lines {
		if strings.TrimSpace(line) != "" {
			result = append(result, "     "+line)
		}
	}
	return strings.Join(result, "\n")
}

// ApplyOptimization 应用优化配置
func (o *PerformanceOptimizer) ApplyOptimization(suggestion OptimizationSuggestion) error {
	switch suggestion.ID {
	case "CFG-001":
		// 调整 GOMAXPROCS
		if numCPU, ok := suggestion.Config["num_cpu"].(int); ok {
			runtime.GOMAXPROCS(numCPU)
		}
	case "GC-001":
		// 建议调整 GOGC，但实际需要用户手动设置环境变量
		return fmt.Errorf("请手动设置 GOGC 环境变量以增加 GC 阈值")
	default:
		return fmt.Errorf("无法自动应用优化建议 %s", suggestion.ID)
	}
	return nil
}

// PerformanceReport 性能报告
type PerformanceReport struct {
	Timestamp    time.Time
	Snapshot     map[string]interface{}
	Suggestions  []OptimizationSuggestion
	Score        float64
	Status       string
}

// CalculateScore 计算性能评分
func (o *PerformanceOptimizer) CalculateScore() float64 {
	o.mu.RLock()
	defer o.mu.RUnlock()

	score := 100.0

	for _, s := range o.suggestions {
		switch s.Level {
		case OptimizationLevelCritical:
			score -= 20
		case OptimizationLevelWarning:
			score -= 10
		case OptimizationLevelInfo:
			score -= 5
		case OptimizationLevelSuggestion:
			score -= 2
		}
	}

	if score < 0 {
		score = 0
	}
	return score
}

// GetStatus 获取性能状态
func (o *PerformanceOptimizer) GetStatus() string {
	score := o.CalculateScore()
	switch {
	case score >= 90:
		return "优秀"
	case score >= 70:
		return "良好"
	case score >= 50:
		return "一般"
	case score >= 30:
		return "较差"
	default:
		return "严重"
	}
}

// GenerateFullReport 生成完整报告
func (o *PerformanceOptimizer) GenerateFullReport() *PerformanceReport {
	return &PerformanceReport{
		Timestamp:   time.Now(),
		Snapshot:    o.lastSnapshot,
		Suggestions: o.GetSuggestions(),
		Score:       o.CalculateScore(),
		Status:      o.GetStatus(),
	}
}

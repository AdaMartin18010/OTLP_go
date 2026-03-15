package performance

import (
	"strings"
	"testing"
	"time"
)

func TestDefaultOptimizerConfig(t *testing.T) {
	config := DefaultOptimizerConfig()
	if config == nil {
		t.Fatal("config should not be nil")
	}
	if config.EnableAutoOptimize {
		t.Error("EnableAutoOptimize should be false")
	}
	if config.MemoryThresholdMB != 512.0 {
		t.Errorf("MemoryThresholdMB = %f, want 512.0", config.MemoryThresholdMB)
	}
	if config.GoroutineThreshold != 10000 {
		t.Errorf("GoroutineThreshold = %d, want 10000", config.GoroutineThreshold)
	}
	if config.GCThresholdPercent != 10.0 {
		t.Errorf("GCThresholdPercent = %f, want 10.0", config.GCThresholdPercent)
	}
	if config.CheckInterval != 30*time.Second {
		t.Errorf("CheckInterval = %v, want 30s", config.CheckInterval)
	}
	if config.MinSuggestions != 1 {
		t.Errorf("MinSuggestions = %d, want 1", config.MinSuggestions)
	}
	if config.MaxSuggestions != 20 {
		t.Errorf("MaxSuggestions = %d, want 20", config.MaxSuggestions)
	}
}

func TestNewPerformanceOptimizer(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	if optimizer == nil {
		t.Fatal("optimizer should not be nil")
	}
	if optimizer.config != config {
		t.Error("config mismatch")
	}
	if optimizer.metricsCollector != collector {
		t.Error("metricsCollector mismatch")
	}
	if optimizer.suggestions == nil {
		t.Error("suggestions should not be nil")
	}
	if optimizer.stopCh == nil {
		t.Error("stopCh should not be nil")
	}
}

func TestNewPerformanceOptimizerWithNilConfig(t *testing.T) {
	collector := NewRuntimeMetricsCollector(nil)
	optimizer := NewPerformanceOptimizer(nil, collector)
	if optimizer == nil {
		t.Fatal("optimizer should not be nil")
	}
	if optimizer.config == nil {
		t.Error("config should not be nil")
	}
}

func TestPerformanceOptimizerStartStop(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 测试启动
	err := optimizer.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	
	// 等待分析完成
	time.Sleep(100 * time.Millisecond)
	
	// 测试重复启动
	err = optimizer.Start()
	if err == nil {
		t.Error("should fail when already running")
	}
	
	// 测试停止
	err = optimizer.Stop()
	if err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
	
	// 测试重复停止
	err = optimizer.Stop()
	if err == nil {
		t.Error("should fail when not running")
	}
}

func TestPerformanceOptimizerAnalyze(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	suggestions := optimizer.Analyze()
	if suggestions == nil {
		t.Fatal("suggestions should not be nil")
	}
	
	// 验证内部状态已更新
	if optimizer.lastSnapshot == nil {
		t.Error("lastSnapshot should not be nil")
	}
}

func TestPerformanceOptimizerGetSuggestions(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 初始为空
	suggestions := optimizer.GetSuggestions()
	if len(suggestions) != 0 {
		t.Errorf("initial suggestions count = %d, want 0", len(suggestions))
	}
	
	// 添加测试建议
	optimizer.suggestions = []OptimizationSuggestion{
		{
			ID:       "TEST-001",
			Level:    OptimizationLevelWarning,
			Category: OptimizationCategoryMemory,
			Title:    "Test Suggestion",
		},
	}
	
	suggestions = optimizer.GetSuggestions()
	if len(suggestions) != 1 {
		t.Errorf("suggestions count = %d, want 1", len(suggestions))
	}
	if suggestions[0].ID != "TEST-001" {
		t.Errorf("ID = %s, want TEST-001", suggestions[0].ID)
	}
}

func TestGetSuggestionsByLevel(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加不同级别的建议
	optimizer.suggestions = []OptimizationSuggestion{
		{
			ID:       "TEST-001",
			Level:    OptimizationLevelCritical,
			Category: OptimizationCategoryMemory,
			Title:    "Critical",
		},
		{
			ID:       "TEST-002",
			Level:    OptimizationLevelWarning,
			Category: OptimizationCategoryCPU,
			Title:    "Warning",
		},
		{
			ID:       "TEST-003",
			Level:    OptimizationLevelCritical,
			Category: OptimizationCategoryGC,
			Title:    "Another Critical",
		},
	}
	
	// 按级别筛选
	critical := optimizer.GetSuggestionsByLevel(OptimizationLevelCritical)
	if len(critical) != 2 {
		t.Errorf("critical count = %d, want 2", len(critical))
	}
	
	warning := optimizer.GetSuggestionsByLevel(OptimizationLevelWarning)
	if len(warning) != 1 {
		t.Errorf("warning count = %d, want 1", len(warning))
	}
	
	info := optimizer.GetSuggestionsByLevel(OptimizationLevelInfo)
	if len(info) != 0 {
		t.Errorf("info count = %d, want 0", len(info))
	}
}

func TestGetSuggestionsByCategory(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加不同类别的建议
	optimizer.suggestions = []OptimizationSuggestion{
		{
			ID:       "TEST-001",
			Level:    OptimizationLevelCritical,
			Category: OptimizationCategoryMemory,
			Title:    "Memory Issue",
		},
		{
			ID:       "TEST-002",
			Level:    OptimizationLevelWarning,
			Category: OptimizationCategoryCPU,
			Title:    "CPU Issue",
		},
		{
			ID:       "TEST-003",
			Level:    OptimizationLevelInfo,
			Category: OptimizationCategoryMemory,
			Title:    "Another Memory Issue",
		},
	}
	
	// 按类别筛选
	memory := optimizer.GetSuggestionsByCategory(OptimizationCategoryMemory)
	if len(memory) != 2 {
		t.Errorf("memory count = %d, want 2", len(memory))
	}
	
	cpu := optimizer.GetSuggestionsByCategory(OptimizationCategoryCPU)
	if len(cpu) != 1 {
		t.Errorf("cpu count = %d, want 1", len(cpu))
	}
	
	gc := optimizer.GetSuggestionsByCategory(OptimizationCategoryGC)
	if len(gc) != 0 {
		t.Errorf("gc count = %d, want 0", len(gc))
	}
}

func TestClearSuggestions(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加建议
	optimizer.suggestions = []OptimizationSuggestion{
		{ID: "TEST-001", Title: "Test"},
	}
	
	// 清除
	optimizer.ClearSuggestions()
	if len(optimizer.suggestions) != 0 {
		t.Errorf("suggestions count = %d, want 0", len(optimizer.suggestions))
	}
}

func TestAnalyzeMemory(t *testing.T) {
	config := &OptimizerConfig{
		MemoryThresholdMB: 1, // 设置很低的阈值以触发建议
	}
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 创建高内存使用场景
	snapshot := map[string]interface{}{
		"mem_alloc":      uint64(100 * 1024 * 1024), // 100 MB
		"mem_heap_alloc": uint64(80 * 1024 * 1024),  // 80 MB
	}
	
	suggestions := optimizer.analyzeMemory(snapshot)
	if len(suggestions) == 0 {
		t.Error("should have memory suggestions")
	}
	
	// 验证有内存相关的建议
	hasMemorySuggestion := false
	for _, s := range suggestions {
		if s.Category == OptimizationCategoryMemory {
			hasMemorySuggestion = true
			break
		}
	}
	if !hasMemorySuggestion {
		t.Error("should have memory category suggestion")
	}
}

func TestAnalyzeGC(t *testing.T) {
	config := &OptimizerConfig{
		GCThresholdPercent: 1, // 设置很低的阈值以触发建议
	}
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 创建高 GC CPU 使用场景
	snapshot := map[string]interface{}{
		"gc_cpu_fraction": 0.15, // 15%
		"gc_count":        uint32(200),
	}
	
	suggestions := optimizer.analyzeGC(snapshot)
	if len(suggestions) == 0 {
		t.Error("should have GC suggestions")
	}
	
	// 验证有 GC 相关的建议
	hasGCSuggestion := false
	for _, s := range suggestions {
		if s.Category == OptimizationCategoryGC {
			hasGCSuggestion = true
			break
		}
	}
	if !hasGCSuggestion {
		t.Error("should have GC category suggestion")
	}
}

func TestAnalyzeGoroutines(t *testing.T) {
	config := &OptimizerConfig{
		GoroutineThreshold: 1, // 设置很低的阈值以触发建议
	}
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 创建高 Goroutine 数量场景
	snapshot := map[string]interface{}{
		"goroutines": 100,
	}
	
	suggestions := optimizer.analyzeGoroutines(snapshot)
	if len(suggestions) == 0 {
		t.Error("should have goroutine suggestions")
	}
	
	// 验证有 Goroutine 相关的建议
	hasGoroutineSuggestion := false
	for _, s := range suggestions {
		if s.Category == OptimizationCategoryGoroutine {
			hasGoroutineSuggestion = true
			break
		}
	}
	if !hasGoroutineSuggestion {
		t.Error("should have goroutine category suggestion")
	}
}

func TestAnalyzeConfig(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	snapshot := map[string]interface{}{}
	suggestions := optimizer.analyzeConfig(snapshot)
	
	// 应该至少有一个配置相关的建议
	if len(suggestions) == 0 {
		t.Error("should have config suggestions")
	}
	
	hasConfigSuggestion := false
	for _, s := range suggestions {
		if s.Category == OptimizationCategoryConfig {
			hasConfigSuggestion = true
			break
		}
	}
	if !hasConfigSuggestion {
		t.Error("should have config category suggestion")
	}
}

func TestCalculateScore(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 初始满分
	score := optimizer.CalculateScore()
	if score != 100.0 {
		t.Errorf("initial score = %f, want 100.0", score)
	}
	
	// 添加不同级别的建议
	optimizer.suggestions = []OptimizationSuggestion{
		{ID: "TEST-001", Level: OptimizationLevelCritical},
		{ID: "TEST-002", Level: OptimizationLevelWarning},
		{ID: "TEST-003", Level: OptimizationLevelInfo},
		{ID: "TEST-004", Level: OptimizationLevelSuggestion},
	}
	
	score = optimizer.CalculateScore()
	if score >= 100.0 {
		t.Error("score should be less than 100")
	}
	if score < 0 {
		t.Error("score should be >= 0")
	}
}

func TestCalculateScoreMinimum(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加大量严重问题
	for i := 0; i < 10; i++ {
		optimizer.suggestions = append(optimizer.suggestions, OptimizationSuggestion{
			ID:    "TEST-CRITICAL",
			Level: OptimizationLevelCritical,
		})
	}
	
	score := optimizer.CalculateScore()
	if score != 0.0 {
		t.Errorf("score = %f, want 0.0", score)
	}
}

func TestGetStatus(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	tests := []struct {
		score    float64
		expected string
	}{
		{95.0, "优秀"},
		{80.0, "良好"},
		{60.0, "一般"},
		{40.0, "较差"},
		{20.0, "严重"},
	}
	
	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			// 通过添加适当级别的建议来控制分数
			optimizer.ClearSuggestions()
			diff := 100.0 - tt.score
			for diff >= 20 {
				optimizer.suggestions = append(optimizer.suggestions, OptimizationSuggestion{
					Level: OptimizationLevelCritical,
				})
				diff -= 20
			}
			for diff >= 10 {
				optimizer.suggestions = append(optimizer.suggestions, OptimizationSuggestion{
					Level: OptimizationLevelWarning,
				})
				diff -= 10
			}
			for diff >= 5 {
				optimizer.suggestions = append(optimizer.suggestions, OptimizationSuggestion{
					Level: OptimizationLevelInfo,
				})
				diff -= 5
			}
			for diff >= 2 {
				optimizer.suggestions = append(optimizer.suggestions, OptimizationSuggestion{
					Level: OptimizationLevelSuggestion,
				})
				diff -= 2
			}
			
			status := optimizer.GetStatus()
			if status != tt.expected {
				t.Errorf("GetStatus() = %s, want %s", status, tt.expected)
			}
		})
	}
}

func TestGenerateReport(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加一些建议
	optimizer.suggestions = []OptimizationSuggestion{
		{
			ID:          "MEM-001",
			Level:       OptimizationLevelCritical,
			Category:    OptimizationCategoryMemory,
			Title:       "内存使用过高",
			Description: "测试描述",
			Impact:      "测试影响",
			Solution:    "测试解决方案",
		},
		{
			ID:          "GC-001",
			Level:       OptimizationLevelWarning,
			Category:    OptimizationCategoryGC,
			Title:       "GC 开销过高",
			Description: "测试描述",
			Impact:      "测试影响",
			Solution:    "测试解决方案",
		},
	}
	
	report := optimizer.GenerateReport()
	if report == "" {
		t.Error("report should not be empty")
	}
	if !strings.Contains(report, "性能优化报告") {
		t.Error("report should contain title")
	}
	if !strings.Contains(report, "MEM-001") {
		t.Error("report should contain MEM-001")
	}
	if !strings.Contains(report, "GC-001") {
		t.Error("report should contain GC-001")
	}
}

func TestGenerateReportNoSuggestions(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	report := optimizer.GenerateReport()
	if report == "" {
		t.Error("report should not be empty")
	}
	if !strings.Contains(report, "未发现性能问题") {
		t.Error("report should contain 'no issues found' message")
	}
}

func TestFormatSolution(t *testing.T) {
	solution := "步骤1\n步骤2\n\n步骤3"
	formatted := formatSolution(solution)
	
	if !strings.Contains(formatted, "步骤1") {
		t.Error("formatted should contain 步骤1")
	}
	if !strings.Contains(formatted, "步骤2") {
		t.Error("formatted should contain 步骤2")
	}
	if !strings.Contains(formatted, "步骤3") {
		t.Error("formatted should contain 步骤3")
	}
}

func TestApplyOptimization(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 测试未知的优化
	suggestion := OptimizationSuggestion{
		ID:       "UNKNOWN",
		Category: OptimizationCategoryMemory,
	}
	
	err := optimizer.ApplyOptimization(suggestion)
	if err == nil {
		t.Error("should fail for unknown optimization")
	}
}

func TestApplyOptimizationCFG001(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	suggestion := OptimizationSuggestion{
		ID: "CFG-001",
		Config: map[string]interface{}{
			"num_cpu": 4,
		},
	}
	
	err := optimizer.ApplyOptimization(suggestion)
	if err != nil {
		t.Errorf("ApplyOptimization failed: %v", err)
	}
}

func TestApplyOptimizationGC001(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	suggestion := OptimizationSuggestion{
		ID: "GC-001",
	}
	
	err := optimizer.ApplyOptimization(suggestion)
	if err == nil {
		t.Error("should fail for GC-001")
	}
	if !strings.Contains(err.Error(), "手动设置 GOGC") {
		t.Error("error should mention manual GOGC setting")
	}
}

func TestOptimizationSuggestionFields(t *testing.T) {
	suggestion := OptimizationSuggestion{
		ID:          "TEST-001",
		Level:       OptimizationLevelCritical,
		Category:    OptimizationCategoryMemory,
		Title:       "测试标题",
		Description: "测试描述",
		Impact:      "测试影响",
		Solution:    "测试解决方案",
		Config: map[string]interface{}{
			"key": "value",
		},
	}
	
	if suggestion.ID != "TEST-001" {
		t.Error("ID mismatch")
	}
	if suggestion.Level != OptimizationLevelCritical {
		t.Error("Level mismatch")
	}
	if suggestion.Category != OptimizationCategoryMemory {
		t.Error("Category mismatch")
	}
	if suggestion.Title != "测试标题" {
		t.Error("Title mismatch")
	}
	if suggestion.Description != "测试描述" {
		t.Error("Description mismatch")
	}
	if suggestion.Impact != "测试影响" {
		t.Error("Impact mismatch")
	}
	if suggestion.Solution != "测试解决方案" {
		t.Error("Solution mismatch")
	}
	if suggestion.Config["key"] != "value" {
		t.Error("Config mismatch")
	}
}

func TestPerformanceReport(t *testing.T) {
	report := &PerformanceReport{
		Timestamp: time.Now(),
		Snapshot: map[string]interface{}{
			"test": "value",
		},
		Suggestions: []OptimizationSuggestion{
			{ID: "TEST-001"},
		},
		Score:  85.0,
		Status: "良好",
	}
	
	if report.Timestamp.IsZero() {
		t.Error("Timestamp should not be zero")
	}
	if report.Snapshot == nil {
		t.Error("Snapshot should not be nil")
	}
	if len(report.Suggestions) != 1 {
		t.Errorf("Suggestions count = %d, want 1", len(report.Suggestions))
	}
	if report.Score != 85.0 {
		t.Errorf("Score = %f, want 85.0", report.Score)
	}
	if report.Status != "良好" {
		t.Errorf("Status = %s, want 良好", report.Status)
	}
}

func TestGenerateFullReport(t *testing.T) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加建议
	optimizer.suggestions = []OptimizationSuggestion{
		{
			ID:    "TEST-001",
			Level: OptimizationLevelCritical,
		},
	}
	optimizer.lastSnapshot = map[string]interface{}{
		"test": "value",
	}
	
	report := optimizer.GenerateFullReport()
	if report == nil {
		t.Fatal("report should not be nil")
	}
	if report.Timestamp.IsZero() {
		t.Error("Timestamp should not be zero")
	}
	if report.Snapshot == nil {
		t.Error("Snapshot should not be nil")
	}
	if len(report.Suggestions) != 1 {
		t.Errorf("Suggestions count = %d, want 1", len(report.Suggestions))
	}
	if report.Score >= 100.0 {
		t.Error("Score should be less than 100")
	}
	if report.Status == "" {
		t.Error("Status should not be empty")
	}
}

func TestOptimizationLevel(t *testing.T) {
	if OptimizationLevelCritical != OptimizationLevel("critical") {
		t.Error("OptimizationLevelCritical mismatch")
	}
	if OptimizationLevelWarning != OptimizationLevel("warning") {
		t.Error("OptimizationLevelWarning mismatch")
	}
	if OptimizationLevelInfo != OptimizationLevel("info") {
		t.Error("OptimizationLevelInfo mismatch")
	}
	if OptimizationLevelSuggestion != OptimizationLevel("suggestion") {
		t.Error("OptimizationLevelSuggestion mismatch")
	}
}

func TestOptimizationCategory(t *testing.T) {
	if OptimizationCategoryMemory != OptimizationCategory("memory") {
		t.Error("OptimizationCategoryMemory mismatch")
	}
	if OptimizationCategoryCPU != OptimizationCategory("cpu") {
		t.Error("OptimizationCategoryCPU mismatch")
	}
	if OptimizationCategoryGC != OptimizationCategory("gc") {
		t.Error("OptimizationCategoryGC mismatch")
	}
	if OptimizationCategoryGoroutine != OptimizationCategory("goroutine") {
		t.Error("OptimizationCategoryGoroutine mismatch")
	}
	if OptimizationCategoryConfig != OptimizationCategory("config") {
		t.Error("OptimizationCategoryConfig mismatch")
	}
}

func TestPerformanceOptimizerMaxSuggestions(t *testing.T) {
	config := &OptimizerConfig{
		MaxSuggestions: 2,
	}
	collector := NewRuntimeMetricsCollector(nil)
	
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加超过限制的建议
	for i := 0; i < 10; i++ {
		optimizer.suggestions = append(optimizer.suggestions, OptimizationSuggestion{
			ID:    "TEST-CRITICAL",
			Level: OptimizationLevelCritical,
		})
	}
	
	// 生成报告应该限制建议数量
	report := optimizer.GenerateReport()
	if report == "" {
		t.Error("report should not be empty")
	}
}

func BenchmarkAnalyze(b *testing.B) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	optimizer := NewPerformanceOptimizer(config, collector)
	
	for i := 0; i < b.N; i++ {
		optimizer.Analyze()
	}
}

func BenchmarkCalculateScore(b *testing.B) {
	config := DefaultOptimizerConfig()
	collector := NewRuntimeMetricsCollector(nil)
	optimizer := NewPerformanceOptimizer(config, collector)
	
	// 添加一些建议
	optimizer.suggestions = []OptimizationSuggestion{
		{ID: "TEST-001", Level: OptimizationLevelCritical},
		{ID: "TEST-002", Level: OptimizationLevelWarning},
	}
	
	for i := 0; i < b.N; i++ {
		optimizer.CalculateScore()
	}
}

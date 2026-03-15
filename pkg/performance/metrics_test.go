package performance

import (
	"testing"
	"time"
)

func TestDefaultMetricsConfig(t *testing.T) {
	config := DefaultMetricsConfig()
	if config == nil {
		t.Fatal("config should not be nil")
	}
	if config.CollectionInterval != 10*time.Second {
		t.Errorf("CollectionInterval = %v, want 10s", config.CollectionInterval)
	}
	if !config.EnableGCMetrics {
		t.Error("EnableGCMetrics should be true")
	}
	if !config.EnableMemMetrics {
		t.Error("EnableMemMetrics should be true")
	}
	if !config.EnableGoroutineMetrics {
		t.Error("EnableGoroutineMetrics should be true")
	}
	if !config.EnableRuntimeMetrics {
		t.Error("EnableRuntimeMetrics should be true")
	}
	if !config.EnableCustomMetrics {
		t.Error("EnableCustomMetrics should be true")
	}
	if config.MaxMetricsHistory != 1000 {
		t.Errorf("MaxMetricsHistory = %d, want 1000", config.MaxMetricsHistory)
	}
}

func TestNewRuntimeMetricsCollector(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	if collector == nil {
		t.Fatal("collector should not be nil")
	}
	if collector.config != config {
		t.Error("config mismatch")
	}
	if collector.metrics == nil {
		t.Error("metrics should not be nil")
	}
	if collector.history == nil {
		t.Error("history should not be nil")
	}
	if collector.stopCh == nil {
		t.Error("stopCh should not be nil")
	}
}

func TestNewRuntimeMetricsCollectorWithNilConfig(t *testing.T) {
	collector := NewRuntimeMetricsCollector(nil)
	if collector == nil {
		t.Fatal("collector should not be nil")
	}
	if collector.config == nil {
		t.Error("config should not be nil")
	}
}

func TestRuntimeMetricsCollectorStartStop(t *testing.T) {
	config := &MetricsConfig{
		CollectionInterval:     100 * time.Millisecond,
		EnableGCMetrics:        true,
		EnableMemMetrics:       true,
		EnableGoroutineMetrics: true,
		EnableRuntimeMetrics:   false,
		EnableCustomMetrics:    false,
		MaxMetricsHistory:      100,
	}
	
	collector := NewRuntimeMetricsCollector(config)
	
	// 测试启动
	err := collector.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	
	// 等待收集
	time.Sleep(200 * time.Millisecond)
	
	// 测试重复启动
	err = collector.Start()
	if err == nil {
		t.Error("should fail when already running")
	}
	
	// 测试停止
	err = collector.Stop()
	if err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
	
	// 测试重复停止
	err = collector.Stop()
	if err == nil {
		t.Error("should fail when not running")
	}
}

func TestRuntimeMetricsCollectorCollect(t *testing.T) {
	config := &MetricsConfig{
		CollectionInterval:     1 * time.Second,
		EnableGCMetrics:        true,
		EnableMemMetrics:       true,
		EnableGoroutineMetrics: true,
		EnableRuntimeMetrics:   false,
		EnableCustomMetrics:    false,
		MaxMetricsHistory:      100,
	}
	
	collector := NewRuntimeMetricsCollector(config)
	
	err := collector.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer collector.Stop()
	
	// 等待收集完成
	time.Sleep(100 * time.Millisecond)
	
	// 获取指标
	metrics := collector.Collect()
	if len(metrics) == 0 {
		t.Error("should have collected some metrics")
	}
	
	// 验证指标类型
	metricNames := make(map[string]bool)
	for _, m := range metrics {
		metricNames[m.Name] = true
		if m.Timestamp.IsZero() {
			t.Error("Timestamp should not be zero")
		}
		if m.Type == "" {
			t.Error("Type should not be empty")
		}
	}
	
	// 验证关键指标存在
	if !metricNames["go_gc_count"] {
		t.Error("should contain go_gc_count")
	}
	if !metricNames["go_mem_alloc_bytes"] {
		t.Error("should contain go_mem_alloc_bytes")
	}
	if !metricNames["go_goroutines"] {
		t.Error("should contain go_goroutines")
	}
}

func TestRuntimeMetricsCollectorGetHistory(t *testing.T) {
	config := &MetricsConfig{
		CollectionInterval:     50 * time.Millisecond,
		EnableGCMetrics:        true,
		EnableMemMetrics:       false,
		EnableGoroutineMetrics: false,
		EnableRuntimeMetrics:   false,
		EnableCustomMetrics:    false,
		MaxMetricsHistory:      10,
	}
	
	collector := NewRuntimeMetricsCollector(config)
	
	err := collector.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer collector.Stop()
	
	// 等待多次收集
	time.Sleep(200 * time.Millisecond)
	
	// 获取历史
	history := collector.GetHistory("go_gc_count")
	if history == nil {
		t.Error("history should not be nil")
	}
	if len(history) == 0 {
		t.Error("should have some history")
	}
}

func TestRuntimeMetricsCollectorGetAllHistory(t *testing.T) {
	config := &MetricsConfig{
		CollectionInterval:     50 * time.Millisecond,
		EnableGCMetrics:        true,
		EnableMemMetrics:       true,
		EnableGoroutineMetrics: false,
		EnableRuntimeMetrics:   false,
		EnableCustomMetrics:    false,
		MaxMetricsHistory:      10,
	}
	
	collector := NewRuntimeMetricsCollector(config)
	
	err := collector.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer collector.Stop()
	
	// 等待多次收集
	time.Sleep(150 * time.Millisecond)
	
	// 获取所有历史
	allHistory := collector.GetAllHistory()
	if allHistory == nil {
		t.Fatal("allHistory should not be nil")
	}
	if len(allHistory) == 0 {
		t.Error("should have some history")
	}
}

func TestRuntimeMetricsCollectorHistoryLimit(t *testing.T) {
	config := &MetricsConfig{
		CollectionInterval:     50 * time.Millisecond,
		EnableGCMetrics:        true,
		EnableMemMetrics:       false,
		EnableGoroutineMetrics: false,
		EnableRuntimeMetrics:   false,
		EnableCustomMetrics:    false,
		MaxMetricsHistory:      3,
	}
	
	collector := NewRuntimeMetricsCollector(config)
	
	err := collector.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer collector.Stop()
	
	// 等待多次收集，超过限制
	time.Sleep(300 * time.Millisecond)
	
	// 获取历史，应该被限制
	history := collector.GetHistory("go_gc_count")
	if len(history) > config.MaxMetricsHistory {
		t.Errorf("history length = %d, should be <= %d", len(history), config.MaxMetricsHistory)
	}
}

func TestRuntimeMetricsCollectorGetStats(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	stats := collector.GetStats()
	if stats == nil {
		t.Fatal("stats should not be nil")
	}
	if _, ok := stats["running"]; !ok {
		t.Error("should contain running")
	}
	if _, ok := stats["metrics_count"]; !ok {
		t.Error("should contain metrics_count")
	}
	if _, ok := stats["history_count"]; !ok {
		t.Error("should contain history_count")
	}
	if _, ok := stats["collection_interval"]; !ok {
		t.Error("should contain collection_interval")
	}
}

func TestGetRuntimeSnapshot(t *testing.T) {
	snapshot := GetRuntimeSnapshot()
	if snapshot == nil {
		t.Fatal("snapshot should not be nil")
	}
	
	// 验证关键字段
	if _, ok := snapshot["timestamp"]; !ok {
		t.Error("should contain timestamp")
	}
	if _, ok := snapshot["goroutines"]; !ok {
		t.Error("should contain goroutines")
	}
	if _, ok := snapshot["cpus"]; !ok {
		t.Error("should contain cpus")
	}
	if _, ok := snapshot["cgo_calls"]; !ok {
		t.Error("should contain cgo_calls")
	}
	if _, ok := snapshot["mem_alloc"]; !ok {
		t.Error("should contain mem_alloc")
	}
	if _, ok := snapshot["mem_total_alloc"]; !ok {
		t.Error("should contain mem_total_alloc")
	}
	if _, ok := snapshot["mem_sys"]; !ok {
		t.Error("should contain mem_sys")
	}
	if _, ok := snapshot["mem_heap_alloc"]; !ok {
		t.Error("should contain mem_heap_alloc")
	}
	if _, ok := snapshot["gc_count"]; !ok {
		t.Error("should contain gc_count")
	}
	if _, ok := snapshot["gc_cpu_fraction"]; !ok {
		t.Error("should contain gc_cpu_fraction")
	}
}

func TestFormatBytes(t *testing.T) {
	tests := []struct {
		bytes    uint64
		expected string
	}{
		{0, "0 B"},
		{100, "100 B"},
		{1024, "1.0 KB"},
		{1536, "1.5 KB"},
		{1024 * 1024, "1.0 MB"},
		{1024 * 1024 * 1024, "1.0 GB"},
	}
	
	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			result := FormatBytes(tt.bytes)
			if result != tt.expected {
				t.Errorf("FormatBytes(%d) = %s, want %s", tt.bytes, result, tt.expected)
			}
		})
	}
}

func TestCustomMetric(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	// 测试 Gauge 类型
	metric := NewCustomMetric(collector, "test_gauge", MetricTypeGauge)
	if metric == nil {
		t.Fatal("metric should not be nil")
	}
	
	metric.Set(100)
	if metric.Get() != 100 {
		t.Errorf("Get() = %f, want 100", metric.Get())
	}
	
	metric.Set(200)
	if metric.Get() != 200 {
		t.Errorf("Get() = %f, want 200", metric.Get())
	}
}

func TestCustomMetricCounter(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	metric := NewCustomMetric(collector, "test_counter", MetricTypeCounter)
	
	// 测试 Add
	metric.Add(10)
	if metric.Get() != 10 {
		t.Errorf("Get() = %f, want 10", metric.Get())
	}
	
	metric.Add(5)
	if metric.Get() != 15 {
		t.Errorf("Get() = %f, want 15", metric.Get())
	}
	
	// 测试 Inc
	metric.Inc()
	if metric.Get() != 16 {
		t.Errorf("Get() = %f, want 16", metric.Get())
	}
	
	// 测试 Dec
	metric.Dec()
	if metric.Get() != 15 {
		t.Errorf("Get() = %f, want 15", metric.Get())
	}
}

func TestTimer(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	timer := NewTimer(collector, "test_timer")
	if timer == nil {
		t.Fatal("timer should not be nil")
	}
	
	// 稍微等待
	time.Sleep(10 * time.Millisecond)
	
	duration := timer.ObserveDuration()
	if duration <= 0 {
		t.Error("duration should be > 0")
	}
	if duration >= 1.0 {
		t.Error("duration should be < 1s")
	}
}

func TestHistogram(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	bounds := []float64{0.1, 0.5, 1.0, 5.0, 10.0}
	histogram := NewHistogram(collector, "test_histogram", bounds)
	if histogram == nil {
		t.Fatal("histogram should not be nil")
	}
	
	// 观察一些值
	histogram.Observe(0.05)
	histogram.Observe(0.3)
	histogram.Observe(0.8)
	histogram.Observe(2.0)
	histogram.Observe(15.0)
	
	sum, count, counts := histogram.GetSnapshot()
	if count != 5 {
		t.Errorf("count = %d, want 5", count)
	}
	if sum != 18.15 {
		t.Errorf("sum = %f, want 18.15", sum)
	}
	if len(counts) != len(bounds)+1 {
		t.Errorf("len(counts) = %d, want %d", len(counts), len(bounds)+1)
	}
	
	// 验证桶计数
	if counts[0] == 0 {
		t.Error("first bucket should have entries")
	}
	if counts[len(counts)-1] == 0 {
		t.Error("last bucket should have entries")
	}
}

func TestHistogramDefaultBounds(t *testing.T) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	// 不提供边界，使用默认值
	histogram := NewHistogram(collector, "test_histogram", nil)
	if histogram == nil {
		t.Fatal("histogram should not be nil")
	}
	if len(histogram.bounds) == 0 {
		t.Error("should have default bounds")
	}
}

func TestRuntimeMetric(t *testing.T) {
	now := time.Now()
	metric := RuntimeMetric{
		Name:      "test_metric",
		Type:      MetricTypeGauge,
		Value:     100.0,
		Timestamp: now,
		Labels:    map[string]string{"key": "value"},
	}
	
	if metric.Name != "test_metric" {
		t.Error("Name mismatch")
	}
	if metric.Type != MetricTypeGauge {
		t.Error("Type mismatch")
	}
	if metric.Value != 100.0 {
		t.Error("Value mismatch")
	}
	if !metric.Timestamp.Equal(now) {
		t.Error("Timestamp mismatch")
	}
	if metric.Labels["key"] != "value" {
		t.Error("Labels mismatch")
	}
}

func TestMetricType(t *testing.T) {
	if MetricTypeCounter != MetricType("counter") {
		t.Error("MetricTypeCounter mismatch")
	}
	if MetricTypeGauge != MetricType("gauge") {
		t.Error("MetricTypeGauge mismatch")
	}
	if MetricTypeHistogram != MetricType("histogram") {
		t.Error("MetricTypeHistogram mismatch")
	}
	if MetricTypeSummary != MetricType("summary") {
		t.Error("MetricTypeSummary mismatch")
	}
}

func TestRuntimeMetricsCollectorConcurrency(t *testing.T) {
	config := &MetricsConfig{
		CollectionInterval:     50 * time.Millisecond,
		EnableGCMetrics:        true,
		EnableMemMetrics:       true,
		EnableGoroutineMetrics: true,
		EnableRuntimeMetrics:   false,
		EnableCustomMetrics:    false,
		MaxMetricsHistory:      100,
	}
	
	collector := NewRuntimeMetricsCollector(config)
	
	err := collector.Start()
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer collector.Stop()
	
	// 并发访问
	done := make(chan bool, 4)
	
	go func() {
		defer done <- true
		for i := 0; i < 10; i++ {
			_ = collector.Collect()
			time.Sleep(10 * time.Millisecond)
		}
	}()
	
	go func() {
		defer done <- true
		for i := 0; i < 10; i++ {
			_ = collector.GetHistory("go_gc_count")
			time.Sleep(10 * time.Millisecond)
		}
	}()
	
	go func() {
		defer done <- true
		for i := 0; i < 10; i++ {
			_ = collector.GetAllHistory()
			time.Sleep(10 * time.Millisecond)
		}
	}()
	
	go func() {
		defer done <- true
		for i := 0; i < 10; i++ {
			_ = collector.GetStats()
			time.Sleep(10 * time.Millisecond)
		}
	}()
	
	// 等待所有 goroutine 完成
	for i := 0; i < 4; i++ {
		<-done
	}
}

func BenchmarkCollect(b *testing.B) {
	config := DefaultMetricsConfig()
	collector := NewRuntimeMetricsCollector(config)
	
	for i := 0; i < b.N; i++ {
		collector.collect()
	}
}

func BenchmarkGetRuntimeSnapshot(b *testing.B) {
	for i := 0; i < b.N; i++ {
		GetRuntimeSnapshot()
	}
}

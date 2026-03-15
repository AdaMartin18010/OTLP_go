// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
package automation

import (
	"context"
	"sync"
	"testing"
	"time"
)

// mockConfigManager is a mock implementation of ConfigManager.
type mockConfigManagerStdlib struct {
	data map[string]interface{}
	mu   sync.RWMutex
}

func newMockConfigManagerStdlib() *mockConfigManagerStdlib {
	return &mockConfigManagerStdlib{
		data: make(map[string]interface{}),
	}
}

func (m *mockConfigManagerStdlib) Get(key string) (interface{}, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()
	val, ok := m.data[key]
	if !ok {
		return nil, ErrConfigNotFound
	}
	return val, nil
}

func (m *mockConfigManagerStdlib) Set(key string, value interface{}) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.data[key] = value
	return nil
}

func (m *mockConfigManagerStdlib) GetInt(key string) (int, error) {
	val, err := m.Get(key)
	if err != nil {
		return 0, err
	}
	v, ok := val.(int)
	if !ok {
		return 0, ErrInvalidConfigValue
	}
	return v, nil
}

func (m *mockConfigManagerStdlib) GetFloat(key string) (float64, error) {
	val, err := m.Get(key)
	if err != nil {
		return 0, err
	}
	v, ok := val.(float64)
	if !ok {
		return 0, ErrInvalidConfigValue
	}
	return v, nil
}

func (m *mockConfigManagerStdlib) GetDuration(key string) (time.Duration, error) {
	val, err := m.Get(key)
	if err != nil {
		return 0, err
	}
	v, ok := val.(time.Duration)
	if !ok {
		return 0, ErrInvalidConfigValue
	}
	return v, nil
}

func (m *mockConfigManagerStdlib) UpdateBatch(updates map[string]interface{}) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	for k, v := range updates {
		m.data[k] = v
	}
	return nil
}

// TestNewAutoConfigStdlib tests auto-config creation.
func TestNewAutoConfigStdlib(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager)

	if ac == nil {
		t.Fatal("NewAutoConfig returned nil")
	}
	if ac.manager != manager {
		t.Error("manager not set correctly")
	}
	if ac.knowledge == nil {
		t.Error("knowledge is nil")
	}
	if ac.adjusters == nil {
		t.Error("adjusters is nil")
	}
	if !ac.IsEnabled() {
		t.Error("should be enabled by default")
	}
}

// TestAutoConfigEnableDisableStdlib tests enable/disable.
func TestAutoConfigEnableDisableStdlib(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager)

	if !ac.IsEnabled() {
		t.Error("should be enabled initially")
	}

	ac.Disable()
	if ac.IsEnabled() {
		t.Error("should be disabled after Disable()")
	}

	ac.Enable()
	if !ac.IsEnabled() {
		t.Error("should be enabled after Enable()")
	}
}

// TestAutoConfigWithKnowledgeStdlib tests setting knowledge.
func TestAutoConfigWithKnowledgeStdlib(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	knowledge := NewMemoryKnowledge()

	ac := NewAutoConfig(manager).WithKnowledge(knowledge)
	if ac.knowledge != knowledge {
		t.Error("knowledge not set correctly")
	}
}

// TestRegisterAdjusterStdlib tests registering adjusters.
func TestRegisterAdjusterStdlib(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager)

	adjuster := &mockAdjusterStdlib{
		name: "test",
		key:  "config.test",
	}

	if err := ac.RegisterAdjuster(adjuster); err != nil {
		t.Fatalf("RegisterAdjuster failed: %v", err)
	}

	retrieved, ok := ac.GetAdjuster("config.test")
	if !ok {
		t.Error("adjuster not found")
	}
	if retrieved != adjuster {
		t.Error("retrieved adjuster is not the same")
	}

	// Test nil adjuster
	if err := ac.RegisterAdjuster(nil); err == nil {
		t.Error("expected error for nil adjuster")
	}
}

// TestUnregisterAdjusterStdlib tests unregistering adjusters.
func TestUnregisterAdjusterStdlib(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager)

	adjuster := &mockAdjusterStdlib{
		name: "test",
		key:  "config.test",
	}

	_ = ac.RegisterAdjuster(adjuster)
	_, ok := ac.GetAdjuster("config.test")
	if !ok {
		t.Error("adjuster should be registered")
	}

	ac.UnregisterAdjuster("config.test")
	_, ok = ac.GetAdjuster("config.test")
	if ok {
		t.Error("adjuster should be unregistered")
	}
}

// TestIntRangeAdjusterStdlib tests integer range adjuster.
func TestIntRangeAdjusterStdlib(t *testing.T) {
	adjuster := NewIntRangeAdjuster(
		"workers",
		"workers.count",
		"cpu_usage",
		1,    // min
		100,  // max
		10,   // default
		70.0, // target
		0.5,  // scale factor
	)

	if adjuster.Name() != "workers" {
		t.Error("name incorrect")
	}
	if adjuster.Key() != "workers.count" {
		t.Error("key incorrect")
	}
	if adjuster.MinValue() != 1 {
		t.Error("min value incorrect")
	}
	if adjuster.MaxValue() != 100 {
		t.Error("max value incorrect")
	}

	// Test valid adjustment
	ctx := context.Background()
	metrics := &MonitoringData{
		Metrics: map[string]float64{"cpu_usage": 90.0},
	}

	newValue, err := adjuster.Adjust(ctx, 10, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	// (90-70)*0.5 = 10, so new value = 10+10 = 20
	if newValue != 20 {
		t.Errorf("expected 20, got %v", newValue)
	}

	// Test clamping to max
	newValue, err = adjuster.Adjust(ctx, 95, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 100 {
		t.Errorf("expected 100 (clamped), got %v", newValue)
	}

	// Test validation
	if err := adjuster.Validate(50); err != nil {
		t.Errorf("Validate(50) failed: %v", err)
	}
	if err := adjuster.Validate(0); err == nil {
		t.Error("Validate(0) should fail")
	}
	if err := adjuster.Validate(101); err == nil {
		t.Error("Validate(101) should fail")
	}
}

// TestDurationRangeAdjusterStdlib tests duration range adjuster.
func TestDurationRangeAdjusterStdlib(t *testing.T) {
	adjuster := NewDurationRangeAdjuster(
		"timeout",
		"request.timeout",
		"latency_ms",
		100*time.Millisecond,
		10*time.Second,
		1*time.Second,
		500.0,
		10*time.Millisecond,
	)

	if adjuster.Name() != "timeout" {
		t.Error("name incorrect")
	}

	ctx := context.Background()
	metrics := &MonitoringData{
		Metrics: map[string]float64{"latency_ms": 800.0},
	}

	newValue, err := adjuster.Adjust(ctx, 1*time.Second, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	// (800-500)*10ms = 3000ms = 3s, so new value = 1s+3s = 4s
	if newValue != 4*time.Second {
		t.Errorf("expected 4s, got %v", newValue)
	}
}

// TestAutoConfigMonitorStdlib tests auto-config monitor.
func TestAutoConfigMonitorStdlib(t *testing.T) {
	monitor := NewAutoConfigMonitor()
	if monitor.Name() != "auto-config-monitor" {
		t.Error("name incorrect")
	}

	collector := &mockCollectorStdlib{
		name: "cpu",
		metrics: map[string]float64{
			"cpu.usage": 50.0,
		},
	}

	monitor.AddCollector(collector)

	ctx := context.Background()
	data, err := monitor.Collect(ctx)
	if err != nil {
		t.Fatalf("Collect failed: %v", err)
	}
	if data == nil {
		t.Fatal("data is nil")
	}
	if data.Metrics["cpu.usage"] != 50.0 {
		t.Error("cpu.usage metric incorrect")
	}
}

// TestAutoConfigAnalyzerStdlib tests auto-config analyzer.
func TestAutoConfigAnalyzerStdlib(t *testing.T) {
	analyzer := NewAutoConfigAnalyzer()
	if analyzer.Name() != "auto-config-analyzer" {
		t.Error("name incorrect")
	}

	analyzer.SetThreshold("cpu.usage", ThresholdConfig{
		Warning:  70.0,
		Critical: 90.0,
		Target:   50.0,
	})

	ctx := context.Background()

	// Test normal metrics
	data := &MonitoringData{
		Timestamp: time.Now(),
		Metrics: map[string]float64{
			"cpu.usage": 50.0,
		},
		Health: HealthHealthy,
	}

	result, err := analyzer.Analyze(ctx, data)
	if err != nil {
		t.Fatalf("Analyze failed: %v", err)
	}
	if result.Severity != SeverityInfo {
		t.Errorf("expected info severity, got %v", result.Severity)
	}

	// Test warning level
	data.Metrics["cpu.usage"] = 75.0
	result, err = analyzer.Analyze(ctx, data)
	if err != nil {
		t.Fatalf("Analyze failed: %v", err)
	}
	if result.Severity != SeverityWarning {
		t.Errorf("expected warning severity, got %v", result.Severity)
	}

	// Test critical level
	data.Metrics["cpu.usage"] = 95.0
	result, err = analyzer.Analyze(ctx, data)
	if err != nil {
		t.Fatalf("Analyze failed: %v", err)
	}
	if result.Severity != SeverityCritical {
		t.Errorf("expected critical severity, got %v", result.Severity)
	}
}

// TestIsSignificantChangeStdlib tests significance check.
func TestIsSignificantChangeStdlib(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager)
	ac.adjustmentThreshold = 0.1 // 10%

	// Test int changes
	if !ac.isSignificantChange(100, 120) {
		t.Error("20% change should be significant")
	}
	if ac.isSignificantChange(100, 105) {
		t.Error("5% change should not be significant")
	}

	// Test float64 changes
	if !ac.isSignificantChange(100.0, 120.0) {
		t.Error("20% float change should be significant")
	}

	// Test duration changes
	if !ac.isSignificantChange(time.Second, 1200*time.Millisecond) {
		t.Error("20% duration change should be significant")
	}
}

// TestConfigAdjusterFuncStdlib tests functional adjuster.
func TestConfigAdjusterFuncStdlib(t *testing.T) {
	adjuster := NewConfigAdjusterFunc(
		"test",
		"test.key",
		func(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error) {
			return 200, nil
		},
		func(value interface{}) error {
			v, ok := value.(int)
			if !ok || v < 0 {
				return ErrInvalidConfigValue
			}
			return nil
		},
		0,
		1000,
	)

	if adjuster.Name() != "test" {
		t.Error("name incorrect")
	}

	ctx := context.Background()
	newValue, err := adjuster.Adjust(ctx, 100, nil, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 200 {
		t.Errorf("expected 200, got %v", newValue)
	}

	if err := adjuster.Validate(500); err != nil {
		t.Errorf("Validate(500) failed: %v", err)
	}
	if err := adjuster.Validate(-1); err == nil {
		t.Error("Validate(-1) should fail")
	}
}

// Mock implementations
type mockAdjusterStdlib struct {
	name     string
	key      string
	newValue interface{}
}

func (m *mockAdjusterStdlib) Name() string                 { return m.name }
func (m *mockAdjusterStdlib) Key() string                  { return m.key }
func (m *mockAdjusterStdlib) MinValue() interface{}        { return 0 }
func (m *mockAdjusterStdlib) MaxValue() interface{}        { return 1000 }
func (m *mockAdjusterStdlib) Validate(v interface{}) error { return nil }
func (m *mockAdjusterStdlib) Adjust(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error) {
	if m.newValue != nil {
		return m.newValue, nil
	}
	return current, nil
}

type mockCollectorStdlib struct {
	name    string
	metrics map[string]float64
}

func (m *mockCollectorStdlib) Name() string { return m.name }
func (m *mockCollectorStdlib) Collect(ctx context.Context) (map[string]float64, error) {
	return m.metrics, nil
}

// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
// This test file uses only standard library to avoid external dependencies.
package automation

import (
	"context"
	"testing"
	"time"
)

// TestNewMAPEKStdlib tests MAPE-K loop creation using stdlib only.
func TestNewMAPEKStdlib(t *testing.T) {
	mapek := NewMAPEK()
	if mapek == nil {
		t.Fatal("NewMAPEK() returned nil")
	}
	if mapek.knowledge == nil {
		t.Error("knowledge is nil")
	}
	if mapek.IsRunning() {
		t.Error("new MAPEK should not be running")
	}
}

// TestMAPEKWithIntervalStdlib tests setting interval.
func TestMAPEKWithIntervalStdlib(t *testing.T) {
	mapek := NewMAPEK().WithInterval(10 * time.Second)
	if mapek.interval != 10*time.Second {
		t.Errorf("expected interval 10s, got %v", mapek.interval)
	}
}

// TestMAPEKWithComponentsStdlib tests setting components.
func TestMAPEKWithComponentsStdlib(t *testing.T) {
	monitor := &simpleMonitor{}
	analyzer := &simpleAnalyzer{}
	planner := &simplePlanner{}
	executor := &simpleExecutor{}
	knowledge := NewMemoryKnowledge()

	mapek := NewMAPEK().
		WithMonitor(monitor).
		WithAnalyzer(analyzer).
		WithPlanner(planner).
		WithExecutor(executor).
		WithKnowledge(knowledge)

	if mapek.monitor != monitor {
		t.Error("monitor not set correctly")
	}
	if mapek.analyzer != analyzer {
		t.Error("analyzer not set correctly")
	}
	if mapek.planner != planner {
		t.Error("planner not set correctly")
	}
	if mapek.executor != executor {
		t.Error("executor not set correctly")
	}
	if mapek.knowledge != knowledge {
		t.Error("knowledge not set correctly")
	}
}

// TestMAPEKStartStopStdlib tests starting and stopping.
func TestMAPEKStartStopStdlib(t *testing.T) {
	monitor := &simpleMonitor{
		data: &MonitoringData{
			Timestamp: time.Now(),
			Metrics:   map[string]float64{"test": 1.0},
			Health:    HealthHealthy,
		},
	}

	mapek := NewMAPEK().
		WithMonitor(monitor).
		WithInterval(100 * time.Millisecond)

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Start should succeed
	if err := mapek.Start(ctx); err != nil {
		t.Fatalf("Start() failed: %v", err)
	}
	if !mapek.IsRunning() {
		t.Error("MAPEK should be running after Start()")
	}

	// Starting again should fail
	if err := mapek.Start(ctx); err != ErrLoopRunning {
		t.Errorf("expected ErrLoopRunning, got %v", err)
	}

	// Stop should succeed
	if err := mapek.Stop(); err != nil {
		t.Fatalf("Stop() failed: %v", err)
	}
	if mapek.IsRunning() {
		t.Error("MAPEK should not be running after Stop()")
	}

	// Stopping again should fail
	if err := mapek.Stop(); err != ErrLoopNotRunning {
		t.Errorf("expected ErrLoopNotRunning, got %v", err)
	}
}

// TestMAPEKStartWithoutMonitorStdlib tests starting without monitor.
func TestMAPEKStartWithoutMonitorStdlib(t *testing.T) {
	mapek := NewMAPEK()
	ctx := context.Background()
	if err := mapek.Start(ctx); err != ErrMissingComponent {
		t.Errorf("expected ErrMissingComponent, got %v", err)
	}
}

// TestHealthStatusStdlib tests health status.
func TestHealthStatusStdlib(t *testing.T) {
	tests := []struct {
		status   HealthStatus
		expected string
	}{
		{HealthUnknown, "unknown"},
		{HealthHealthy, "healthy"},
		{HealthDegraded, "degraded"},
		{HealthUnhealthy, "unhealthy"},
		{HealthStatus(999), "unknown"},
	}

	for _, tt := range tests {
		if got := tt.status.String(); got != tt.expected {
			t.Errorf("HealthStatus(%d).String() = %q, want %q", tt.status, got, tt.expected)
		}
	}
}

// TestSeverityLevelStdlib tests severity level.
func TestSeverityLevelStdlib(t *testing.T) {
	tests := []struct {
		severity SeverityLevel
		expected string
	}{
		{SeverityInfo, "info"},
		{SeverityWarning, "warning"},
		{SeverityCritical, "critical"},
		{SeverityLevel(999), "unknown"},
	}

	for _, tt := range tests {
		if got := tt.severity.String(); got != tt.expected {
			t.Errorf("SeverityLevel(%d).String() = %q, want %q", tt.severity, got, tt.expected)
		}
	}
}

// TestMemoryKnowledgeStdlib tests memory knowledge base.
func TestMemoryKnowledgeStdlib(t *testing.T) {
	k := NewMemoryKnowledge()
	ctx := context.Background()

	// Test Store and Retrieve
	if err := k.Store(ctx, "key1", "value1"); err != nil {
		t.Fatalf("Store failed: %v", err)
	}

	val, err := k.Retrieve(ctx, "key1")
	if err != nil {
		t.Fatalf("Retrieve failed: %v", err)
	}
	if val != "value1" {
		t.Errorf("expected 'value1', got %v", val)
	}

	// Test non-existent key
	_, err = k.Retrieve(ctx, "nonexistent")
	if err == nil {
		t.Error("expected error for non-existent key")
	}

	// Test Update
	if err := k.Update(ctx, "key1", "updated"); err != nil {
		t.Fatalf("Update failed: %v", err)
	}

	val, err = k.Retrieve(ctx, "key1")
	if err != nil {
		t.Fatalf("Retrieve after update failed: %v", err)
	}
	if val != "updated" {
		t.Errorf("expected 'updated', got %v", val)
	}

	// Test History
	if err := k.Store(ctx, "key2", "value1"); err != nil {
		t.Fatalf("Store failed: %v", err)
	}
	time.Sleep(10 * time.Millisecond)
	if err := k.Store(ctx, "key2", "value2"); err != nil {
		t.Fatalf("Store failed: %v", err)
	}

	history, err := k.History(ctx, "key2", 10)
	if err != nil {
		t.Fatalf("History failed: %v", err)
	}
	if len(history) != 2 {
		t.Errorf("expected 2 history entries, got %d", len(history))
	}
}

// TestMonitoringDataStdlib tests monitoring data.
func TestMonitoringDataStdlib(t *testing.T) {
	data := &MonitoringData{
		Timestamp: time.Now(),
		Metrics: map[string]float64{
			"cpu":    50.0,
			"memory": 70.0,
		},
		Attributes: map[string]string{
			"version": "1.0",
		},
		Health: HealthHealthy,
		Components: []ComponentStatus{
			{
				Name:    "service1",
				Status:  HealthHealthy,
				Latency: 100 * time.Millisecond,
			},
		},
	}

	if data.Metrics["cpu"] != 50.0 {
		t.Error("cpu metric incorrect")
	}
	if data.Attributes["version"] != "1.0" {
		t.Error("version attribute incorrect")
	}
	if data.Health != HealthHealthy {
		t.Error("health status incorrect")
	}
	if len(data.Components) != 1 {
		t.Error("components length incorrect")
	}
}

// TestAnalysisResultStdlib tests analysis result.
func TestAnalysisResultStdlib(t *testing.T) {
	result := &AnalysisResult{
		Timestamp: time.Now(),
		Findings: []Finding{
			{
				Type:        "high_cpu",
				Description: "CPU usage is high",
				Severity:    SeverityWarning,
				Component:   "cpu",
				Value:       85.0,
				Threshold:   80.0,
			},
		},
		Severity:   SeverityWarning,
		Confidence: 0.9,
		Recommendations: []Recommendation{
			{
				Type:        "scale_up",
				Description: "Scale up to handle load",
				Priority:    1,
			},
		},
	}

	if len(result.Findings) != 1 {
		t.Error("findings length incorrect")
	}
	if result.Severity != SeverityWarning {
		t.Error("severity incorrect")
	}
	if result.Confidence != 0.9 {
		t.Error("confidence incorrect")
	}
	if len(result.Recommendations) != 1 {
		t.Error("recommendations length incorrect")
	}
}

// TestActionPlanStdlib tests action plan.
func TestActionPlanStdlib(t *testing.T) {
	plan := &ActionPlan{
		ID:        "plan-123",
		Timestamp: time.Now(),
		Actions: []Action{
			{
				Type:      "scale",
				Target:    "service1",
				Operation: "up",
				Parameters: map[string]interface{}{
					"amount": 2,
				},
			},
		},
		Priority: 1,
		Timeout:  5 * time.Minute,
	}

	if plan.ID != "plan-123" {
		t.Error("id incorrect")
	}
	if len(plan.Actions) != 1 {
		t.Error("actions length incorrect")
	}
	if plan.Priority != 1 {
		t.Error("priority incorrect")
	}
	if plan.Timeout != 5*time.Minute {
		t.Error("timeout incorrect")
	}
}

// TestExecutionResultStdlib tests execution result.
func TestExecutionResultStdlib(t *testing.T) {
	result := &ExecutionResult{
		PlanID:    "plan-123",
		Timestamp: time.Now(),
		Success:   true,
		Actions: []ActionResult{
			{
				Success:  true,
				Duration: 1 * time.Second,
			},
		},
		Duration: 2 * time.Second,
	}

	if result.PlanID != "plan-123" {
		t.Error("plan id incorrect")
	}
	if !result.Success {
		t.Error("success should be true")
	}
	if len(result.Actions) != 1 {
		t.Error("actions length incorrect")
	}
	if result.Duration != 2*time.Second {
		t.Error("duration incorrect")
	}
}

// TestKnowledgeRecordStdlib tests knowledge record.
func TestKnowledgeRecordStdlib(t *testing.T) {
	record := KnowledgeRecord{
		Key:       "test-key",
		Value:     "test-value",
		Timestamp: time.Now(),
		Version:   1,
	}

	if record.Key != "test-key" {
		t.Error("key incorrect")
	}
	if record.Value != "test-value" {
		t.Error("value incorrect")
	}
	if record.Version != 1 {
		t.Error("version incorrect")
	}
}

// Simple mock implementations for stdlib tests
type simpleMonitor struct {
	data *MonitoringData
}

func (m *simpleMonitor) Name() string { return "simple-monitor" }
func (m *simpleMonitor) Collect(ctx context.Context) (*MonitoringData, error) {
	if m.data == nil {
		return &MonitoringData{
			Timestamp: time.Now(),
			Metrics:   make(map[string]float64),
			Health:    HealthHealthy,
		}, nil
	}
	return m.data, nil
}

type simpleAnalyzer struct{}

func (a *simpleAnalyzer) Name() string { return "simple-analyzer" }
func (a *simpleAnalyzer) Analyze(ctx context.Context, data *MonitoringData) (*AnalysisResult, error) {
	return &AnalysisResult{
		Timestamp: time.Now(),
		Findings:  []Finding{},
		Severity:  SeverityInfo,
	}, nil
}

type simplePlanner struct{}

func (p *simplePlanner) Name() string { return "simple-planner" }
func (p *simplePlanner) Plan(ctx context.Context, result *AnalysisResult) (*ActionPlan, error) {
	return &ActionPlan{
		ID:        "simple-plan",
		Timestamp: time.Now(),
		Actions:   []Action{},
	}, nil
}

type simpleExecutor struct{}

func (e *simpleExecutor) Name() string { return "simple-executor" }
func (e *simpleExecutor) Execute(ctx context.Context, plan *ActionPlan) (*ExecutionResult, error) {
	return &ExecutionResult{
		PlanID:    plan.ID,
		Timestamp: time.Now(),
		Success:   true,
	}, nil
}

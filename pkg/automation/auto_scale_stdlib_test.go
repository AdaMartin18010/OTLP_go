// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
package automation

import (
	"context"
	"testing"
	"time"
)

// TestNewAutoScalerStdlib tests auto-scaler creation.
func TestNewAutoScalerStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	if scaler == nil {
		t.Fatal("NewAutoScaler returned nil")
	}
	if scaler.knowledge == nil {
		t.Error("knowledge is nil")
	}
	if scaler.policies == nil {
		t.Error("policies is nil")
	}
	if !scaler.IsEnabled() {
		t.Error("should be enabled by default")
	}
	if scaler.GetCurrentInstances() != 1 {
		t.Error("default current instances should be 1")
	}
}

// TestAutoScalerWithInstanceLimitsStdlib tests instance limits.
func TestAutoScalerWithInstanceLimitsStdlib(t *testing.T) {
	scaler := NewAutoScaler().WithInstanceLimits(2, 20)

	if scaler.minInstances != 2 {
		t.Errorf("expected min 2, got %d", scaler.minInstances)
	}
	if scaler.maxInstances != 20 {
		t.Errorf("expected max 20, got %d", scaler.maxInstances)
	}
}

// TestAutoScalerEnableDisableStdlib tests enable/disable.
func TestAutoScalerEnableDisableStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	if !scaler.IsEnabled() {
		t.Error("should be enabled initially")
	}

	scaler.Disable()
	if scaler.IsEnabled() {
		t.Error("should be disabled after Disable()")
	}

	scaler.Enable()
	if !scaler.IsEnabled() {
		t.Error("should be enabled after Enable()")
	}
}

// TestRegisterPolicyStdlib tests registering policies.
func TestRegisterPolicyStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	policy := ScalingPolicy{
		Name:               "cpu-scale",
		MetricKey:          "cpu_utilization",
		ScaleUpThreshold:   80.0,
		ScaleDownThreshold: 20.0,
		ScaleUpStep:        2,
		ScaleDownStep:      1,
		Priority:           1,
		Enabled:            true,
	}

	if err := scaler.RegisterPolicy(policy); err != nil {
		t.Fatalf("RegisterPolicy failed: %v", err)
	}

	retrieved, ok := scaler.GetPolicy("cpu-scale")
	if !ok {
		t.Error("policy not found")
	}
	if retrieved.Name != policy.Name {
		t.Error("retrieved policy name mismatch")
	}

	// Test empty name
	if err := scaler.RegisterPolicy(ScalingPolicy{Name: ""}); err == nil {
		t.Error("expected error for empty policy name")
	}
}

// TestUnregisterPolicyStdlib tests unregistering policies.
func TestUnregisterPolicyStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	policy := ScalingPolicy{
		Name:      "test",
		MetricKey: "test",
	}

	_ = scaler.RegisterPolicy(policy)
	_, ok := scaler.GetPolicy("test")
	if !ok {
		t.Error("policy should be registered")
	}

	scaler.UnregisterPolicy("test")
	_, ok = scaler.GetPolicy("test")
	if ok {
		t.Error("policy should be unregistered")
	}
}

// TestSetCurrentInstancesStdlib tests setting current instances.
func TestSetCurrentInstancesStdlib(t *testing.T) {
	scaler := NewAutoScaler().WithInstanceLimits(1, 10)

	if err := scaler.SetCurrentInstances(5); err != nil {
		t.Fatalf("SetCurrentInstances failed: %v", err)
	}
	if scaler.GetCurrentInstances() != 5 {
		t.Errorf("expected 5 instances, got %d", scaler.GetCurrentInstances())
	}

	// Test below minimum
	if err := scaler.SetCurrentInstances(0); err != ErrInvalidInstanceCount {
		t.Errorf("expected ErrInvalidInstanceCount, got %v", err)
	}

	// Test above maximum
	if err := scaler.SetCurrentInstances(11); err != ErrInvalidInstanceCount {
		t.Errorf("expected ErrInvalidInstanceCount, got %v", err)
	}
}

// TestEvaluateScaleUpStdlib tests scale up evaluation.
func TestEvaluateScaleUpStdlib(t *testing.T) {
	scaler := NewAutoScaler().WithInstanceLimits(1, 10)

	policy := ScalingPolicy{
		Name:               "cpu-scale",
		MetricKey:          "cpu_utilization",
		ScaleUpThreshold:   80.0,
		ScaleDownThreshold: 20.0,
		ScaleUpStep:        2,
		ScaleDownStep:      1,
		Priority:           1,
		Enabled:            true,
	}

	if err := scaler.RegisterPolicy(policy); err != nil {
		t.Fatalf("RegisterPolicy failed: %v", err)
	}

	metrics := &ScalingMetrics{
		CPUUtilization: 85.0, // Above threshold
	}

	ctx := context.Background()
	decision, err := scaler.Evaluate(ctx, metrics)
	if err != nil {
		t.Fatalf("Evaluate failed: %v", err)
	}
	if !decision.ShouldScale {
		t.Error("should scale up")
	}
	if decision.Direction != ScalingDirectionUp {
		t.Errorf("expected scale up, got %v", decision.Direction)
	}
	if decision.Amount != 2 {
		t.Errorf("expected amount 2, got %d", decision.Amount)
	}
}

// TestEvaluateScaleDownStdlib tests scale down evaluation.
func TestEvaluateScaleDownStdlib(t *testing.T) {
	scaler := NewAutoScaler().WithInstanceLimits(1, 10)
	_ = scaler.SetCurrentInstances(5)

	policy := ScalingPolicy{
		Name:               "cpu-scale",
		MetricKey:          "cpu_utilization",
		ScaleUpThreshold:   80.0,
		ScaleDownThreshold: 20.0,
		ScaleUpStep:        2,
		ScaleDownStep:      1,
		Priority:           1,
		Enabled:            true,
	}

	if err := scaler.RegisterPolicy(policy); err != nil {
		t.Fatalf("RegisterPolicy failed: %v", err)
	}

	metrics := &ScalingMetrics{
		CPUUtilization: 15.0, // Below threshold
	}

	ctx := context.Background()
	decision, err := scaler.Evaluate(ctx, metrics)
	if err != nil {
		t.Fatalf("Evaluate failed: %v", err)
	}
	if !decision.ShouldScale {
		t.Error("should scale down")
	}
	if decision.Direction != ScalingDirectionDown {
		t.Errorf("expected scale down, got %v", decision.Direction)
	}
	if decision.Amount != -1 {
		t.Errorf("expected amount -1, got %d", decision.Amount)
	}
}

// TestEvaluateNoScaleStdlib tests no scaling needed.
func TestEvaluateNoScaleStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	policy := ScalingPolicy{
		Name:               "cpu-scale",
		MetricKey:          "cpu_utilization",
		ScaleUpThreshold:   80.0,
		ScaleDownThreshold: 20.0,
		Enabled:            true,
	}

	if err := scaler.RegisterPolicy(policy); err != nil {
		t.Fatalf("RegisterPolicy failed: %v", err)
	}

	metrics := &ScalingMetrics{
		CPUUtilization: 50.0, // Normal range
	}

	ctx := context.Background()
	decision, err := scaler.Evaluate(ctx, metrics)
	if err != nil {
		t.Fatalf("Evaluate failed: %v", err)
	}
	if decision.ShouldScale {
		t.Error("should not scale")
	}
}

// TestExecuteDecisionStdlib tests executing scaling decision.
func TestExecuteDecisionStdlib(t *testing.T) {
	scaler := NewAutoScaler().WithInstanceLimits(1, 10)
	_ = scaler.SetCurrentInstances(3)

	decision := &ScalingDecision{
		ShouldScale: true,
		Type:        ScalingTypeHorizontal,
		Direction:   ScalingDirectionUp,
		Amount:      2,
		Reason:      "High CPU",
	}

	ctx := context.Background()
	event, err := scaler.Execute(ctx, decision)
	if err != nil {
		t.Fatalf("Execute failed: %v", err)
	}

	if event.ID == "" {
		t.Error("event ID is empty")
	}
	if event.Type != ScalingTypeHorizontal {
		t.Error("event type incorrect")
	}
	if event.Direction != ScalingDirectionUp {
		t.Error("event direction incorrect")
	}
	if event.From != 3 {
		t.Errorf("expected from 3, got %d", event.From)
	}
	if event.To != 5 {
		t.Errorf("expected to 5, got %d", event.To)
	}
	if !event.Success {
		t.Error("event should be successful")
	}
	if scaler.GetCurrentInstances() != 5 {
		t.Errorf("expected 5 current instances, got %d", scaler.GetCurrentInstances())
	}
}

// TestScalingTypeStringStdlib tests scaling type strings.
func TestScalingTypeStringStdlib(t *testing.T) {
	if ScalingTypeHorizontal.String() != "horizontal" {
		t.Error("horizontal string incorrect")
	}
	if ScalingTypeVertical.String() != "vertical" {
		t.Error("vertical string incorrect")
	}
	if ScalingType(999).String() != "unknown" {
		t.Error("unknown type string incorrect")
	}
}

// TestScalingDirectionStringStdlib tests scaling direction strings.
func TestScalingDirectionStringStdlib(t *testing.T) {
	if ScalingDirectionUp.String() != "up" {
		t.Error("up string incorrect")
	}
	if ScalingDirectionDown.String() != "down" {
		t.Error("down string incorrect")
	}
	if ScalingDirection(999).String() != "unknown" {
		t.Error("unknown direction string incorrect")
	}
}

// TestLinearPredictionModelStdlib tests linear prediction.
func TestLinearPredictionModelStdlib(t *testing.T) {
	model := NewLinearPredictionModel()

	if model.Name() != "linear-regression" {
		t.Error("model name incorrect")
	}
	if model.Confidence() != 0.8 {
		t.Errorf("expected confidence 0.8, got %f", model.Confidence())
	}

	// Create historical data with upward trend
	history := []MetricPoint{
		{Timestamp: time.Now().Add(-5 * time.Minute), Value: 10.0},
		{Timestamp: time.Now().Add(-4 * time.Minute), Value: 20.0},
		{Timestamp: time.Now().Add(-3 * time.Minute), Value: 30.0},
		{Timestamp: time.Now().Add(-2 * time.Minute), Value: 40.0},
		{Timestamp: time.Now().Add(-1 * time.Minute), Value: 50.0},
	}

	ctx := context.Background()
	predictions, err := model.Predict(ctx, "cpu", history, 5*time.Minute)
	if err != nil {
		t.Fatalf("Predict failed: %v", err)
	}
	if len(predictions) != 5 {
		t.Errorf("expected 5 predictions, got %d", len(predictions))
	}

	// Values should be increasing
	for i := 1; i < len(predictions); i++ {
		if predictions[i].Value < predictions[i-1].Value {
			t.Error("predictions should be increasing")
		}
	}
}

// TestLinearPredictionModelInsufficientDataStdlib tests prediction with insufficient data.
func TestLinearPredictionModelInsufficientDataStdlib(t *testing.T) {
	model := NewLinearPredictionModel()

	history := []MetricPoint{
		{Timestamp: time.Now(), Value: 10.0},
	}

	ctx := context.Background()
	_, err := model.Predict(ctx, "cpu", history, 5*time.Minute)
	if err == nil {
		t.Error("expected error for insufficient data")
	}
}

// TestScalingEventStdlib tests scaling event.
func TestScalingEventStdlib(t *testing.T) {
	now := time.Now()
	event := ScalingEvent{
		ID:        "event-1",
		Timestamp: now,
		Type:      ScalingTypeHorizontal,
		Direction: ScalingDirectionUp,
		From:      3,
		To:        5,
		Reason:    "High load",
		Trigger:   "cpu > 80%",
		Success:   true,
	}

	if event.ID != "event-1" {
		t.Error("id incorrect")
	}
	if event.Type != ScalingTypeHorizontal {
		t.Error("type incorrect")
	}
	if event.Direction != ScalingDirectionUp {
		t.Error("direction incorrect")
	}
	if event.From != 3 {
		t.Error("from incorrect")
	}
	if event.To != 5 {
		t.Error("to incorrect")
	}
	if !event.Success {
		t.Error("success should be true")
	}
}

// TestScalingDecisionStdlib tests scaling decision.
func TestScalingDecisionStdlib(t *testing.T) {
	now := time.Now()
	decision := &ScalingDecision{
		ShouldScale: true,
		Type:        ScalingTypeHorizontal,
		Direction:   ScalingDirectionUp,
		Amount:      2,
		Reason:      "High CPU",
		Confidence:  0.85,
		Timestamp:   now,
	}

	if !decision.ShouldScale {
		t.Error("should scale")
	}
	if decision.Type != ScalingTypeHorizontal {
		t.Error("type incorrect")
	}
	if decision.Direction != ScalingDirectionUp {
		t.Error("direction incorrect")
	}
	if decision.Amount != 2 {
		t.Error("amount incorrect")
	}
	if decision.Confidence != 0.85 {
		t.Error("confidence incorrect")
	}
}

// TestScalingMetricsStdlib tests scaling metrics.
func TestScalingMetricsStdlib(t *testing.T) {
	metrics := &ScalingMetrics{
		CPUUtilization:    75.0,
		MemoryUtilization: 80.0,
		RequestLatency:    100 * time.Millisecond,
		RequestRate:       1000.0,
		ErrorRate:         0.05,
		QueueDepth:        10.0,
		CustomMetrics: map[string]float64{
			"custom": 42.0,
		},
	}

	if metrics.CPUUtilization != 75.0 {
		t.Error("cpu utilization incorrect")
	}
	if metrics.MemoryUtilization != 80.0 {
		t.Error("memory utilization incorrect")
	}
	if metrics.RequestLatency != 100*time.Millisecond {
		t.Error("request latency incorrect")
	}
	if metrics.CustomMetrics["custom"] != 42.0 {
		t.Error("custom metric incorrect")
	}
}

// TestGetScalingHistoryStdlib tests getting scaling history.
func TestGetScalingHistoryStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	// Add some events
	scaler.scalingHistory = []ScalingEvent{
		{ID: "event-1", Success: true},
		{ID: "event-2", Success: true},
		{ID: "event-3", Success: false},
	}

	// Get all
	history := scaler.GetScalingHistory(10)
	if len(history) != 3 {
		t.Errorf("expected 3 history entries, got %d", len(history))
	}

	// Get limited
	history = scaler.GetScalingHistory(2)
	if len(history) != 2 {
		t.Errorf("expected 2 history entries, got %d", len(history))
	}
}

// TestStoreMetricStdlib tests storing metrics.
func TestStoreMetricStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	ctx := context.Background()
	if err := scaler.StoreMetric(ctx, "cpu", 50.0); err != nil {
		t.Fatalf("StoreMetric failed: %v", err)
	}

	history, err := scaler.knowledge.History(ctx, "metrics_cpu", 10)
	if err != nil {
		t.Fatalf("History failed: %v", err)
	}
	if len(history) != 1 {
		t.Errorf("expected 1 history entry, got %d", len(history))
	}
}

// TestBuildMonitoringDataStdlib tests building monitoring data.
func TestBuildMonitoringDataStdlib(t *testing.T) {
	scaler := NewAutoScaler()

	metrics := &ScalingMetrics{
		CPUUtilization:    75.0,
		MemoryUtilization: 80.0,
		RequestLatency:    100 * time.Millisecond,
		RequestRate:       1000.0,
		ErrorRate:         0.05,
		QueueDepth:        10.0,
		CustomMetrics: map[string]float64{
			"custom_metric": 42.0,
		},
	}

	data := scaler.buildMonitoringData(metrics)

	if data.Metrics["cpu_utilization"] != 75.0 {
		t.Error("cpu_utilization incorrect")
	}
	if data.Metrics["memory_utilization"] != 80.0 {
		t.Error("memory_utilization incorrect")
	}
	if data.Metrics["request_rate"] != 1000.0 {
		t.Error("request_rate incorrect")
	}
	if data.Metrics["custom_metric"] != 42.0 {
		t.Error("custom_metric incorrect")
	}
	// With CPU=75 and ErrorRate=0.05, should be Healthy (thresholds use > not >=)
	if data.Health != HealthHealthy {
		t.Errorf("expected healthy health, got %v", data.Health)
	}

	// Test degraded (CPU > 75)
	metrics.CPUUtilization = 76.0
	data = scaler.buildMonitoringData(metrics)
	if data.Health != HealthDegraded {
		t.Errorf("expected degraded health, got %v", data.Health)
	}

	// Test unhealthy (ErrorRate > 0.1)
	metrics.ErrorRate = 0.15
	data = scaler.buildMonitoringData(metrics)
	if data.Health != HealthUnhealthy {
		t.Errorf("expected unhealthy health, got %v", data.Health)
	}
}

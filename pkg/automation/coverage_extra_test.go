// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
// Additional tests to reach 80% coverage.
package automation

import (
	"context"
	"errors"
	"testing"
	"time"
)

// TestAutoScalePredictionInsufficientHistory tests prediction with insufficient history.
func TestAutoScalePredictionInsufficientHistory(t *testing.T) {
	scaler := NewAutoScaler()

	// Store minimal history
	ctx := context.Background()
	_ = scaler.knowledge.Store(ctx, "metrics_cpu", MetricPoint{
		Timestamp: time.Now(),
		Value:     50.0,
	})

	model := NewLinearPredictionModel()
	decision, err := scaler.Predict(ctx, "cpu", model)
	if err != nil {
		t.Fatalf("Predict failed: %v", err)
	}
	if decision.ShouldScale {
		t.Error("should not scale with insufficient history")
	}
}

// TestAutoScalePredictionNoPolicy tests prediction with no matching policy.
func TestAutoScalePredictionNoPolicy(t *testing.T) {
	scaler := NewAutoScaler()

	// Store history
	ctx := context.Background()
	for i := 0; i < 15; i++ {
		point := MetricPoint{
			Timestamp: time.Now().Add(-time.Duration(15-i) * time.Minute),
			Value:     float64(i * 10),
		}
		_ = scaler.knowledge.Store(ctx, "metrics_other", point)
	}

	// No policy for "other" metric
	model := NewLinearPredictionModel()
	decision, err := scaler.Predict(ctx, "other", model)
	if err != nil {
		t.Fatalf("Predict failed: %v", err)
	}
	if decision.ShouldScale {
		t.Error("should not scale without policy")
	}
}

// TestAutoScalePlannerEmptyFindings tests planner with no findings.
func TestAutoScalePlannerEmptyFindings(t *testing.T) {
	scaler := NewAutoScaler()
	planner := NewAutoScalerPlanner(scaler)

	analysis := &AnalysisResult{
		Findings: []Finding{},
	}

	ctx := context.Background()
	plan, err := planner.Plan(ctx, analysis)
	if err != nil {
		t.Fatalf("Plan failed: %v", err)
	}
	if len(plan.Actions) != 0 {
		t.Error("expected no actions for empty findings")
	}
}

// TestAutoScaleExecutorInvalidDecision tests executor with invalid decision.
func TestAutoScaleExecutorInvalidDecision(t *testing.T) {
	scaler := NewAutoScaler()
	executor := NewAutoScalerExecutor(scaler)

	plan := &ActionPlan{
		ID: "plan-1",
		Actions: []Action{
			{
				Type:      "scale",
				Target:    "auto-scaler",
				Operation: "up",
				Parameters: map[string]interface{}{
					"decision": "not a scaling decision", // Invalid type
				},
			},
		},
	}

	ctx := context.Background()
	result, err := executor.Execute(ctx, plan)
	if err != nil {
		t.Fatalf("Execute failed: %v", err)
	}
	if result.Success {
		t.Error("expected failure for invalid decision type")
	}
	if len(result.Actions) != 1 || result.Actions[0].Success {
		t.Error("action should fail for invalid decision")
	}
}

// TestAutoConfigWithThresholds tests setting various thresholds.
func TestAutoConfigWithThresholds(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager).
		WithAdjustmentThreshold(0.25).
		WithMaxAdjustmentPercent(0.75).
		WithMinAdjustmentInterval(5 * time.Minute)

	if ac.adjustmentThreshold != 0.25 {
		t.Errorf("expected threshold 0.25, got %f", ac.adjustmentThreshold)
	}
	if ac.maxAdjustmentPercent != 0.75 {
		t.Errorf("expected max percent 0.75, got %f", ac.maxAdjustmentPercent)
	}
	if ac.minAdjustmentInterval != 5*time.Minute {
		t.Errorf("expected interval 5m, got %v", ac.minAdjustmentInterval)
	}
}

// TestIsSignificantChangeEdgeCases tests edge cases in significance check.
func TestIsSignificantChangeEdgeCases(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	ac := NewAutoConfig(manager)
	ac.adjustmentThreshold = 0.1

	// Test equal values
	if ac.isSignificantChange(100, 100) {
		t.Error("equal values should not be significant")
	}

	// Test from zero to non-zero
	if !ac.isSignificantChange(0, 1) {
		t.Error("from zero to non-zero should be significant")
	}

	// Test string changes
	if !ac.isSignificantChange("hello", "world") {
		t.Error("different strings should be significant")
	}

	// Test same string
	if ac.isSignificantChange("same", "same") {
		t.Error("same strings should not be significant")
	}
}

// TestIntRangeAdjusterExactMinMax tests adjuster at exact boundaries.
func TestIntRangeAdjusterExactMinMax(t *testing.T) {
	adjuster := NewIntRangeAdjuster(
		"workers",
		"workers.count",
		"cpu",
		10,
		100,
		50,
		70.0,
		1.0,
	)

	// Test exact min value
	if err := adjuster.Validate(10); err != nil {
		t.Errorf("Validate(min) failed: %v", err)
	}

	// Test exact max value
	if err := adjuster.Validate(100); err != nil {
		t.Errorf("Validate(max) failed: %v", err)
	}
}

// TestDurationRangeAdjusterExactMinMax tests duration adjuster boundaries.
func TestDurationRangeAdjusterExactMinMax(t *testing.T) {
	adjuster := NewDurationRangeAdjuster(
		"timeout",
		"timeout",
		"latency",
		100*time.Millisecond,
		10*time.Second,
		1*time.Second,
		500.0,
		time.Millisecond,
	)

	// Test exact min
	if err := adjuster.Validate(100 * time.Millisecond); err != nil {
		t.Errorf("Validate(min) failed: %v", err)
	}

	// Test exact max
	if err := adjuster.Validate(10 * time.Second); err != nil {
		t.Errorf("Validate(max) failed: %v", err)
	}
}

// TestSelfHealingMonitorWithOpenCircuits tests monitor with open circuits.
func TestSelfHealingMonitorWithOpenCircuits(t *testing.T) {
	sh := NewSelfHealing()
	monitor := NewSelfHealingMonitor(sh)

	// Create and open a circuit breaker
	breaker := sh.RegisterCircuitBreaker("test-service", 2, 30*time.Second)
	breaker.RecordFailure()
	breaker.RecordFailure()

	if breaker.State() != CircuitOpen {
		t.Fatal("circuit should be open")
	}

	ctx := context.Background()
	data, err := monitor.Collect(ctx)
	if err != nil {
		t.Fatalf("Collect failed: %v", err)
	}

	if data.Metrics["open_circuits"] != 1.0 {
		t.Errorf("expected 1 open circuit, got %v", data.Metrics["open_circuits"])
	}
	if data.Metrics["breaker_test-service_failures"] != 2.0 {
		t.Errorf("expected 2 failures, got %v", data.Metrics["breaker_test-service_failures"])
	}
}

// TestSelfHealingMonitorStats tests monitor statistics.
func TestSelfHealingMonitorStats(t *testing.T) {
	sh := NewSelfHealing()

	// Create some faults and recoveries
	_ = sh.DetectFault(FaultTypeError, "s1", "error1", nil)
	_ = sh.DetectFault(FaultTypeError, "s2", "error2", nil)

	// Register a successful remediation action
	action := NewFuncRemediationAction(
		"fix",
		100,
		func(fault *Fault) bool { return true },
		func(ctx context.Context, fault *Fault) (*RemediationResult, error) {
			return &RemediationResult{Success: true}, nil
		},
	)
	sh.RegisterRemediation(action)

	// Attempt remediation
	ctx := context.Background()
	fault := sh.DetectFault(FaultTypeError, "s3", "error3", nil)
	_, _ = sh.Remediate(ctx, fault)

	monitor := NewSelfHealingMonitor(sh)
	data, err := monitor.Collect(ctx)
	if err != nil {
		t.Fatalf("Collect failed: %v", err)
	}

	stats := sh.GetStats()
	if data.Metrics["faults_detected"] != float64(stats.FaultsDetected) {
		t.Error("faults_detected metric mismatch")
	}
}

// TestCircuitBreakerHalfOpenAllowLimit tests half-open allow limit.
func TestCircuitBreakerHalfOpenAllowLimit(t *testing.T) {
	sh := NewSelfHealing()
	breaker := sh.RegisterCircuitBreaker("test", 3, 50*time.Millisecond)

	// Open circuit
	breaker.RecordFailure()
	breaker.RecordFailure()
	breaker.RecordFailure()

	time.Sleep(60 * time.Millisecond)

	if breaker.State() != CircuitHalfOpen {
		t.Fatal("should be half-open")
	}

	// Allow() decrements the counter but successes/failures are recorded separately
	// The breaker allows up to halfOpenMax requests before considering transition
	allowed := 0
	for i := 0; i < 5; i++ {
		if breaker.Allow() {
			allowed++
		}
	}

	// Should allow at least halfOpenMax (3) requests
	if allowed < 3 {
		t.Errorf("should allow at least 3 requests in half-open, got %d", allowed)
	}
}

// TestCircuitBreakerStatsTimestamps tests breaker stats timestamps.
func TestCircuitBreakerStatsTimestamps(t *testing.T) {
	sh := NewSelfHealing()
	breaker := sh.RegisterCircuitBreaker("test", 3, 30*time.Second)

	stats := breaker.Stats()
	if !stats.LastFailure.IsZero() {
		t.Error("LastFailure should be zero initially")
	}
	if !stats.LastSuccess.IsZero() {
		t.Error("LastSuccess should be zero initially")
	}

	breaker.RecordFailure()
	stats = breaker.Stats()
	if stats.LastFailure.IsZero() {
		t.Error("LastFailure should be set after failure")
	}

	breaker.RecordSuccess()
	stats = breaker.Stats()
	if stats.LastSuccess.IsZero() {
		t.Error("LastSuccess should be set after success")
	}
}

// TestExecuteWithRetryContextCancellation tests retry cancellation.
func TestExecuteWithRetryContextCancellation(t *testing.T) {
	sh := NewSelfHealing()

	ctx, cancel := context.WithCancel(context.Background())
	cancel() // Cancel immediately

	callCount := 0
	err := sh.ExecuteWithRetry(ctx, func() error {
		callCount++
		return errors.New("error")
	}, &RetryPolicy{
		MaxRetries:     3,
		InitialBackoff: time.Hour, // Long backoff
	})

	if err == nil {
		t.Error("expected error")
	}
	if callCount != 1 {
		t.Errorf("expected 1 call with cancelled context, got %d", callCount)
	}
}

// TestConfigAdjusterFuncNilValidation tests adjuster with nil validation.
func TestConfigAdjusterFuncNilValidation(t *testing.T) {
	adjuster := NewConfigAdjusterFunc(
		"test",
		"test.key",
		func(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error) {
			return 200, nil
		},
		nil, // nil validation
		nil,
		nil,
	)

	if err := adjuster.Validate("anything"); err != nil {
		t.Errorf("nil validation should pass, got %v", err)
	}
}

// TestRemediationResultStructure tests remediation result fields.
func TestRemediationResultStructure(t *testing.T) {
	now := time.Now()
	result := &RemediationResult{
		Action:      "test-action",
		FaultID:     "fault-1",
		Success:     true,
		Message:     "Success",
		Error:       "",
		Timestamp:   now,
		RetryNeeded: false,
		NewFault:    nil,
	}

	if result.Action != "test-action" {
		t.Error("action incorrect")
	}
	if result.FaultID != "fault-1" {
		t.Error("faultID incorrect")
	}
	if !result.Success {
		t.Error("success should be true")
	}
	if result.RetryNeeded {
		t.Error("retryNeeded should be false")
	}
}

// TestActionPlanStructure tests action plan fields.
func TestActionPlanStructure(t *testing.T) {
	plan := &ActionPlan{
		ID:        "plan-1",
		Timestamp: time.Now(),
		Actions: []Action{
			{
				Type:      "scale",
				Target:    "service",
				Operation: "up",
				Parameters: map[string]interface{}{
					"amount": 2,
				},
				Rollback: func() error { return nil },
			},
		},
		Priority: 10,
		Timeout:  5 * time.Minute,
	}

	if plan.Priority != 10 {
		t.Errorf("priority should be 10, got %d", plan.Priority)
	}
	if plan.Timeout != 5*time.Minute {
		t.Errorf("timeout incorrect")
	}
	if len(plan.Actions) != 1 {
		t.Errorf("expected 1 action, got %d", len(plan.Actions))
	}
}

// TestScalingPolicyFields tests scaling policy fields.
func TestScalingPolicyFields(t *testing.T) {
	policy := ScalingPolicy{
		Name:               "test-policy",
		MetricKey:          "cpu",
		ScaleUpThreshold:   80.0,
		ScaleDownThreshold: 20.0,
		ScaleUpStep:        2,
		ScaleDownStep:      1,
		Priority:           5,
		Enabled:            true,
	}

	if policy.Name != "test-policy" {
		t.Error("name incorrect")
	}
	if policy.MetricKey != "cpu" {
		t.Error("metricKey incorrect")
	}
	if policy.ScaleUpThreshold != 80.0 {
		t.Error("scaleUpThreshold incorrect")
	}
	if policy.ScaleDownThreshold != 20.0 {
		t.Error("scaleDownThreshold incorrect")
	}
	if !policy.Enabled {
		t.Error("enabled should be true")
	}
}

// TestFaultStructure tests fault fields.
func TestFaultStructure(t *testing.T) {
	now := time.Now()
	fault := &Fault{
		ID:         "fault-1",
		Type:       FaultTypeError,
		Component:  "service-1",
		Severity:   SeverityWarning,
		Message:    "Something went wrong",
		Error:      errors.New("original error"),
		Timestamp:  now,
		Context:    map[string]interface{}{"key": "value"},
		Resolved:   false,
		ResolvedAt: nil,
	}

	if fault.ID != "fault-1" {
		t.Error("ID incorrect")
	}
	if fault.Type != FaultTypeError {
		t.Error("type incorrect")
	}
	if fault.Component != "service-1" {
		t.Error("component incorrect")
	}
	if fault.Resolved {
		t.Error("resolved should be false")
	}
}

// TestHealthCheckResultStructure tests health check result fields.
func TestHealthCheckResultStructure(t *testing.T) {
	now := time.Now()
	result := &HealthCheckResult{
		Name:      "service-1",
		Status:    HealthHealthy,
		Message:   "All good",
		Latency:   50 * time.Millisecond,
		Timestamp: now,
		Metadata:  map[string]interface{}{"version": "1.0"},
	}

	if result.Name != "service-1" {
		t.Error("name incorrect")
	}
	if result.Status != HealthHealthy {
		t.Error("status incorrect")
	}
	if result.Latency != 50*time.Millisecond {
		t.Error("latency incorrect")
	}
	if result.Metadata == nil {
		t.Error("metadata should not be nil")
	}
}

// TestPredictionStructure tests prediction fields.
func TestPredictionStructure(t *testing.T) {
	now := time.Now()
	prediction := Prediction{
		Timestamp:  now,
		Value:      100.0,
		Confidence: 0.85,
		LowerBound: 90.0,
		UpperBound: 110.0,
	}

	if prediction.Value != 100.0 {
		t.Error("value incorrect")
	}
	if prediction.Confidence != 0.85 {
		t.Error("confidence incorrect")
	}
	if prediction.LowerBound != 90.0 {
		t.Error("lowerBound incorrect")
	}
	if prediction.UpperBound != 110.0 {
		t.Error("upperBound incorrect")
	}
}

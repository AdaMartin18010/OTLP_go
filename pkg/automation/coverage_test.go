// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
// Additional tests to improve coverage.
package automation

import (
	"context"
	"errors"
	"testing"
	"time"
)

// mockAdjusterWithValidation extends mockAdjuster with validation
type mockAdjusterWithValidation struct {
	mockAdjusterStdlib
	validateFn func(v interface{}) error
}

func (m *mockAdjusterWithValidation) Validate(v interface{}) error {
	if m.validateFn != nil {
		return m.validateFn(v)
	}
	return nil
}

// TestMAPEKWithKnowledgeNil tests MAPEK with nil knowledge.
func TestMAPEKWithKnowledgeNil(t *testing.T) {
	mapek := NewMAPEK()
	mapek.WithKnowledge(nil)
	if mapek.knowledge != nil {
		t.Error("knowledge should be nil")
	}
}

// TestMAPEKIterateNoAnalyzer tests MAPEK iteration without analyzer.
func TestMAPEKIterateNoAnalyzer(t *testing.T) {
	monitor := &simpleMonitor{
		data: &MonitoringData{
			Timestamp: time.Now(),
			Metrics:   map[string]float64{"test": 1.0},
			Health:    HealthHealthy,
		},
	}

	mapek := NewMAPEK().
		WithMonitor(monitor).
		WithInterval(50 * time.Millisecond)

	ctx, cancel := context.WithTimeout(context.Background(), 150*time.Millisecond)
	defer cancel()

	if err := mapek.Start(ctx); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	time.Sleep(100 * time.Millisecond)

	if err := mapek.Stop(); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
}

// TestMAPEKIterateWithAnalyzerNoPlanner tests with analyzer but no planner.
func TestMAPEKIterateWithAnalyzerNoPlanner(t *testing.T) {
	monitor := &simpleMonitor{
		data: &MonitoringData{
			Timestamp: time.Now(),
			Metrics:   map[string]float64{"test": 1.0},
			Health:    HealthHealthy,
		},
	}

	analyzer := &simpleAnalyzer{}

	mapek := NewMAPEK().
		WithMonitor(monitor).
		WithAnalyzer(analyzer).
		WithInterval(50 * time.Millisecond)

	ctx, cancel := context.WithTimeout(context.Background(), 150*time.Millisecond)
	defer cancel()

	if err := mapek.Start(ctx); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	time.Sleep(100 * time.Millisecond)

	if err := mapek.Stop(); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
}

// TestMemoryKnowledgeHistoryLimit tests history with limit.
func TestMemoryKnowledgeHistoryLimit(t *testing.T) {
	k := NewMemoryKnowledge()
	ctx := context.Background()

	// Store multiple values
	for i := 0; i < 5; i++ {
		if err := k.Store(ctx, "key", i); err != nil {
			t.Fatalf("Store failed: %v", err)
		}
	}

	// Get limited history
	history, err := k.History(ctx, "key", 3)
	if err != nil {
		t.Fatalf("History failed: %v", err)
	}
	if len(history) != 3 {
		t.Errorf("expected 3 history entries, got %d", len(history))
	}

	// Get with zero limit (should return all)
	history, err = k.History(ctx, "key", 0)
	if err != nil {
		t.Fatalf("History failed: %v", err)
	}
	if len(history) != 5 {
		t.Errorf("expected 5 history entries with limit 0, got %d", len(history))
	}
}

// TestAutoConfigAdjustWithValidationError tests adjustment with validation error.
func TestAutoConfigAdjustWithValidationError(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	_ = manager.Set("test.key", 100)

	ac := NewAutoConfig(manager)

	adjuster := &mockAdjusterWithValidation{
		mockAdjusterStdlib: mockAdjusterStdlib{
			name:     "test",
			key:      "test.key",
			newValue: 150,
		},
		validateFn: func(v interface{}) error {
			return errors.New("validation failed")
		},
	}

	if err := ac.RegisterAdjuster(adjuster); err != nil {
		t.Fatalf("RegisterAdjuster failed: %v", err)
	}

	metrics := &MonitoringData{
		Timestamp: time.Now(),
		Metrics:   map[string]float64{},
		Health:    HealthHealthy,
	}

	ctx := context.Background()
	changes, err := ac.Adjust(ctx, metrics)
	// Should not error, just skip invalid adjustment
	if err != nil {
		t.Logf("Adjust returned error (expected): %v", err)
	}
	if len(changes) != 0 {
		t.Error("expected no changes due to validation error")
	}
}

// TestAutoConfigAdjustNilAdjusterValue tests adjustment with nil value handling.
func TestAutoConfigAdjustNilAdjusterValue(t *testing.T) {
	manager := newMockConfigManagerStdlib()
	_ = manager.Set("test.key", nil)

	ac := NewAutoConfig(manager)

	adjuster := &mockAdjusterStdlib{
		name:     "test",
		key:      "test.key",
		newValue: "test",
	}

	_ = ac.RegisterAdjuster(adjuster)

	metrics := &MonitoringData{
		Timestamp: time.Now(),
		Metrics:   map[string]float64{},
		Health:    HealthHealthy,
	}

	ctx := context.Background()
	changes, _ := ac.Adjust(ctx, metrics)
	if len(changes) != 1 {
		t.Errorf("expected 1 change, got %d", len(changes))
	}
}

// TestDurationAdjusterMissingMetric tests duration adjuster with missing metric.
func TestDurationAdjusterMissingMetric(t *testing.T) {
	adjuster := NewDurationRangeAdjuster(
		"timeout",
		"request.timeout",
		"missing_metric",
		100*time.Millisecond,
		10*time.Second,
		1*time.Second,
		500.0,
		10*time.Millisecond,
	)

	ctx := context.Background()
	metrics := &MonitoringData{
		Metrics: map[string]float64{}, // Missing the metric
	}

	newValue, err := adjuster.Adjust(ctx, 2*time.Second, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 2*time.Second {
		t.Error("value should be unchanged when metric is missing")
	}
}

// TestDurationAdjusterClampMax tests duration adjuster clamping to max.
func TestDurationAdjusterClampMax(t *testing.T) {
	adjuster := NewDurationRangeAdjuster(
		"timeout",
		"request.timeout",
		"latency",
		100*time.Millisecond,
		5*time.Second, // max 5s
		1*time.Second,
		100.0, // target 100ms
		100*time.Millisecond,
	)

	ctx := context.Background()
	metrics := &MonitoringData{
		Metrics: map[string]float64{"latency": 1000.0}, // 1000ms, way above target
	}

	// Current at 4s, adding (1000-100)*100ms = 90s, should clamp to 5s max
	newValue, err := adjuster.Adjust(ctx, 4*time.Second, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 5*time.Second { // Should be clamped to max
		t.Errorf("expected max value 5s, got %v", newValue)
	}
}

// TestIntAdjusterMissingMetric tests int adjuster with missing metric.
func TestIntAdjusterMissingMetric(t *testing.T) {
	adjuster := NewIntRangeAdjuster(
		"workers",
		"workers.count",
		"missing_metric",
		1,
		100,
		10,
		70.0,
		0.5,
	)

	ctx := context.Background()
	metrics := &MonitoringData{
		Metrics: map[string]float64{},
	}

	newValue, err := adjuster.Adjust(ctx, 20, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 20 {
		t.Error("value should be unchanged when metric is missing")
	}
}

// TestIntAdjusterClampToMax tests int adjuster clamping to max.
func TestIntAdjusterClampToMax(t *testing.T) {
	adjuster := NewIntRangeAdjuster(
		"workers",
		"workers.count",
		"cpu",
		1,
		50, // max 50
		10,
		50.0,
		2.0, // scale factor 2
	)

	ctx := context.Background()
	metrics := &MonitoringData{
		Metrics: map[string]float64{"cpu": 100.0}, // 100% CPU
	}

	// Current 40, diff 50, adjustment 100, new value 140, should clamp to 50
	newValue, err := adjuster.Adjust(ctx, 40, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 50 { // Should be clamped to max
		t.Errorf("expected max value 50, got %v", newValue)
	}
}

// TestIntAdjusterAtTarget tests int adjuster at target value.
func TestIntAdjusterAtTarget(t *testing.T) {
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

	ctx := context.Background()
	// CPU exactly at target
	metrics := &MonitoringData{
		Metrics: map[string]float64{"cpu": 70.0},
	}

	// No adjustment needed when at target
	newValue, err := adjuster.Adjust(ctx, 50, metrics, nil)
	if err != nil {
		t.Fatalf("Adjust failed: %v", err)
	}
	if newValue != 50 { // Should stay same
		t.Errorf("expected unchanged value 50, got %v", newValue)
	}
}

// TestAutoConfigAnalyzerNoThresholds tests analyzer with no thresholds set.
func TestAutoConfigAnalyzerNoThresholds(t *testing.T) {
	analyzer := NewAutoConfigAnalyzer()

	ctx := context.Background()
	data := &MonitoringData{
		Timestamp: time.Now(),
		Metrics: map[string]float64{
			"unknown_metric": 100.0,
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
	if len(result.Findings) != 0 {
		t.Error("expected no findings for unknown metrics")
	}
}

// TestAutoConfigCollectorEmpty tests collector returning empty metrics.
func TestAutoConfigCollectorEmpty(t *testing.T) {
	monitor := NewAutoConfigMonitor()

	collector := &mockCollectorStdlib{
		name:    "empty",
		metrics: map[string]float64{},
	}

	monitor.AddCollector(collector)

	ctx := context.Background()
	data, err := monitor.Collect(ctx)
	if err != nil {
		t.Fatalf("Collect failed: %v", err)
	}
	if data == nil {
		t.Error("data should not be nil")
	}
	if len(data.Metrics) != 0 {
		t.Error("expected no metrics from empty collector")
	}
}

// TestAutoScaleEvaluateMultiplePolicies tests evaluation with multiple policies.
func TestAutoScaleEvaluateMultiplePolicies(t *testing.T) {
	scaler := NewAutoScaler().WithInstanceLimits(1, 10)

	cpuPolicy := ScalingPolicy{
		Name:               "cpu-scale",
		MetricKey:          "cpu_utilization",
		ScaleUpThreshold:   80.0,
		ScaleDownThreshold: 20.0,
		ScaleUpStep:        2,
		ScaleDownStep:      1,
		Priority:           1,
		Enabled:            true,
	}

	memoryPolicy := ScalingPolicy{
		Name:               "memory-scale",
		MetricKey:          "memory_utilization",
		ScaleUpThreshold:   85.0,
		ScaleDownThreshold: 15.0,
		ScaleUpStep:        1,
		ScaleDownStep:      1,
		Priority:           2, // Higher priority
		Enabled:            true,
	}

	_ = scaler.RegisterPolicy(cpuPolicy)
	_ = scaler.RegisterPolicy(memoryPolicy)

	// Both metrics trigger scale up
	metrics := &ScalingMetrics{
		CPUUtilization:    85.0,
		MemoryUtilization: 90.0,
	}

	ctx := context.Background()
	decision, err := scaler.Evaluate(ctx, metrics)
	if err != nil {
		t.Fatalf("Evaluate failed: %v", err)
	}
	if !decision.ShouldScale {
		t.Error("should scale")
	}
	// Memory policy has higher priority, should be selected
	if decision.Amount != 1 {
		t.Errorf("expected amount 1 from memory policy, got %d", decision.Amount)
	}
}

// TestAutoScaleEvaluateCooldownDown tests scale down cooldown.
func TestAutoScaleEvaluateCooldownDown(t *testing.T) {
	scaler := NewAutoScaler().WithCooldowns(time.Hour, time.Hour)
	scaler.lastScaleDown = time.Now()

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

	_ = scaler.RegisterPolicy(policy)

	metrics := &ScalingMetrics{
		CPUUtilization: 10.0, // Triggers scale down
	}

	ctx := context.Background()
	decision, err := scaler.Evaluate(ctx, metrics)
	if err != ErrScalingCooldown {
		t.Errorf("expected ErrScalingCooldown, got %v", err)
	}
	if decision.ShouldScale {
		t.Error("should not scale during cooldown")
	}
}

// TestAutoScaleExecuteNoScale tests execute with no-scale decision.
func TestAutoScaleExecuteNoScale(t *testing.T) {
	scaler := NewAutoScaler()

	decision := &ScalingDecision{
		ShouldScale: false,
	}

	ctx := context.Background()
	_, err := scaler.Execute(ctx, decision)
	if err == nil {
		t.Error("expected error for no-scale decision")
	}
}

// TestAutoScalePredictionWithHistory tests prediction with metric history.
func TestAutoScalePredictionWithHistory(t *testing.T) {
	scaler := NewAutoScaler()

	// Store some metric history
	ctx := context.Background()
	for i := 0; i < 15; i++ {
		point := MetricPoint{
			Timestamp: time.Now().Add(-time.Duration(15-i) * time.Minute),
			Value:     float64(i * 10),
		}
		_ = scaler.knowledge.Store(ctx, "metrics_cpu", point)
	}

	model := NewLinearPredictionModel()
	decision, err := scaler.Predict(ctx, "cpu", model)
	if err != nil {
		t.Fatalf("Predict failed: %v", err)
	}
	// May or may not trigger scaling depending on prediction
	_ = decision
}

// TestAutoScalePredictionLowConfidence tests prediction with low confidence.
func TestAutoScalePredictionLowConfidence(t *testing.T) {
	scaler := NewAutoScaler()

	// Store some metric history
	ctx := context.Background()
	for i := 0; i < 15; i++ {
		point := MetricPoint{
			Timestamp: time.Now().Add(-time.Duration(15-i) * time.Minute),
			Value:     float64(i * 10),
		}
		_ = scaler.knowledge.Store(ctx, "metrics_cpu", point)
	}

	// Set policy with very high threshold
	policy := ScalingPolicy{
		Name:             "cpu-scale",
		MetricKey:        "cpu_utilization",
		ScaleUpThreshold: 999.0, // Very high
		ScaleUpStep:      2,
		Enabled:          true,
	}
	_ = scaler.RegisterPolicy(policy)

	model := NewLinearPredictionModel()
	decision, err := scaler.Predict(ctx, "cpu", model)
	if err != nil {
		t.Fatalf("Predict failed: %v", err)
	}
	// Should not scale with very high threshold
	if decision.ShouldScale {
		t.Error("should not scale with very high threshold")
	}
}

// TestSelfHealingRemediateSpecificType tests remediation for specific fault type.
func TestSelfHealingRemediateSpecificType(t *testing.T) {
	sh := NewSelfHealing()

	// Register action only for network faults
	networkAction := NewFuncRemediationAction(
		"network-fix",
		100,
		func(fault *Fault) bool { return fault.Type == FaultTypeNetwork },
		func(ctx context.Context, fault *Fault) (*RemediationResult, error) {
			return &RemediationResult{
				Action:    "network-fix",
				FaultID:   fault.ID,
				Success:   true,
				Timestamp: time.Now(),
			}, nil
		},
	)

	sh.RegisterRemediation(networkAction)

	// Create a network fault - should be handled
	fault := sh.DetectFault(FaultTypeNetwork, "service", "network error", nil)

	ctx := context.Background()
	result, err := sh.Remediate(ctx, fault)
	if err != nil {
		t.Fatalf("Remediate failed: %v", err)
	}
	if !result.Success {
		t.Error("result should be successful for network fault")
	}

	// Create a different fault type - should fail (no matching action)
	fault2 := sh.DetectFault(FaultTypeError, "service", "other error", nil)
	_, err = sh.Remediate(ctx, fault2)
	if err != ErrNoRemediationAvailable {
		t.Errorf("expected ErrNoRemediationAvailable for non-matching fault, got %v", err)
	}
}

// TestSelfHealingCircuitBreakerNonExistent tests execute with non-existent breaker.
func TestSelfHealingCircuitBreakerNonExistent(t *testing.T) {
	sh := NewSelfHealing()

	ctx := context.Background()
	callCount := 0
	err := sh.Execute(ctx, "nonexistent", func() error {
		callCount++
		return nil
	})

	if err != nil {
		t.Errorf("Execute failed: %v", err)
	}
	if callCount != 1 {
		t.Errorf("expected 1 call, got %d", callCount)
	}
}

// TestSelfHealingRetryNonRetryable tests retry with non-retryable error.
func TestSelfHealingRetryNonRetryable(t *testing.T) {
	sh := NewSelfHealing()

	ctx := context.Background()
	retryableErr := errors.New("retryable")
	nonRetryableErr := errors.New("non-retryable")

	callCount := 0
	err := sh.ExecuteWithRetry(ctx, func() error {
		callCount++
		return nonRetryableErr
	}, &RetryPolicy{
		MaxRetries:      3,
		InitialBackoff:  1 * time.Millisecond,
		RetryableErrors: []error{retryableErr},
	})

	if err == nil {
		t.Error("expected error")
	}
	if callCount != 1 {
		t.Errorf("expected 1 call for non-retryable error, got %d", callCount)
	}
}

// TestSelfHealingHealthCheckContext tests health check with context.
func TestSelfHealingHealthCheckContext(t *testing.T) {
	sh := NewSelfHealing()

	checker := NewFuncHealthChecker(
		"slow-service",
		30*time.Second,
		func(ctx context.Context) (*HealthCheckResult, error) {
			select {
			case <-ctx.Done():
				return nil, ctx.Err()
			case <-time.After(10 * time.Millisecond):
				return &HealthCheckResult{
					Name:      "slow-service",
					Status:    HealthHealthy,
					Timestamp: time.Now(),
				}, nil
			}
		},
	)

	sh.RegisterHealthChecker(checker)

	ctx := context.Background()
	results, _ := sh.RunHealthChecks(ctx)

	if len(results) != 1 {
		t.Errorf("expected 1 result, got %d", len(results))
	}
}

// TestFuncRemediationActionCanHandleNil tests remediation action with nil canHandle.
func TestFuncRemediationActionCanHandleNil(t *testing.T) {
	action := NewFuncRemediationAction(
		"test",
		100,
		nil, // nil canHandle should return true
		func(ctx context.Context, fault *Fault) (*RemediationResult, error) {
			return &RemediationResult{Success: true}, nil
		},
	)

	fault := &Fault{Type: FaultTypeError}
	if !action.CanHandle(fault) {
		t.Error("should handle when canHandle is nil")
	}
}

// TestSelfHealingExecuteWithRetryNilPolicy tests retry with nil policy.
func TestSelfHealingExecuteWithRetryNilPolicy(t *testing.T) {
	sh := NewSelfHealing()

	ctx := context.Background()
	callCount := 0
	err := sh.ExecuteWithRetry(ctx, func() error {
		callCount++
		return nil
	}, nil)

	if err != nil {
		t.Errorf("ExecuteWithRetry failed: %v", err)
	}
	if callCount != 1 {
		t.Errorf("expected 1 call, got %d", callCount)
	}
}

// TestSelfHealingMonitorDisabled tests self-healing monitor when disabled.
func TestSelfHealingMonitorDisabled(t *testing.T) {
	sh := NewSelfHealing()
	sh.Disable()

	monitor := NewSelfHealingMonitor(sh)

	ctx := context.Background()
	data, err := monitor.Collect(ctx)
	if err != nil {
		t.Fatalf("Collect failed: %v", err)
	}
	if data.Health != HealthDegraded {
		t.Errorf("expected degraded health when disabled, got %v", data.Health)
	}
}

// TestSelfHealingGetMetricHistoryEmpty tests getting empty metric history.
func TestSelfHealingGetMetricHistoryEmpty(t *testing.T) {
	scaler := NewAutoScaler()

	ctx := context.Background()
	history, err := scaler.getMetricHistory(ctx, "nonexistent", 10)
	if err != nil {
		t.Fatalf("getMetricHistory failed: %v", err)
	}
	if len(history) != 0 {
		t.Errorf("expected empty history, got %d", len(history))
	}
}

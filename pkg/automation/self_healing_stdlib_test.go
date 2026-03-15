// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
package automation

import (
	"context"
	"errors"
	"testing"
	"time"
)

// TestNewSelfHealingStdlib tests self-healing creation.
func TestNewSelfHealingStdlib(t *testing.T) {
	sh := NewSelfHealing()

	if sh == nil {
		t.Fatal("NewSelfHealing returned nil")
	}
	if sh.knowledge == nil {
		t.Error("knowledge is nil")
	}
	if sh.breakers == nil {
		t.Error("breakers is nil")
	}
	if sh.healthChecks == nil {
		t.Error("healthChecks is nil")
	}
	if sh.remediations == nil {
		t.Error("remediations is nil")
	}
	if !sh.IsEnabled() {
		t.Error("should be enabled by default")
	}
}

// TestSelfHealingEnableDisableStdlib tests enable/disable.
func TestSelfHealingEnableDisableStdlib(t *testing.T) {
	sh := NewSelfHealing()

	if !sh.IsEnabled() {
		t.Error("should be enabled initially")
	}

	sh.Disable()
	if sh.IsEnabled() {
		t.Error("should be disabled after Disable()")
	}

	sh.Enable()
	if !sh.IsEnabled() {
		t.Error("should be enabled after Enable()")
	}
}

// TestRegisterCircuitBreakerStdlib tests registering circuit breakers.
func TestRegisterCircuitBreakerStdlib(t *testing.T) {
	sh := NewSelfHealing()

	breaker := sh.RegisterCircuitBreaker("service-a", 5, 30*time.Second)
	if breaker == nil {
		t.Fatal("RegisterCircuitBreaker returned nil")
	}
	if breaker.name != "service-a" {
		t.Errorf("expected name 'service-a', got %q", breaker.name)
	}
	if breaker.state != CircuitClosed {
		t.Error("new breaker should be closed")
	}
	if breaker.threshold != 5 {
		t.Errorf("expected threshold 5, got %d", breaker.threshold)
	}

	retrieved, ok := sh.GetCircuitBreaker("service-a")
	if !ok {
		t.Error("breaker not found")
	}
	if retrieved != breaker {
		t.Error("retrieved breaker is not the same")
	}

	// Test non-existent breaker
	_, ok = sh.GetCircuitBreaker("nonexistent")
	if ok {
		t.Error("non-existent breaker should not be found")
	}
}

// TestCircuitBreakerStateStdlib tests circuit breaker state transitions.
func TestCircuitBreakerStateStdlib(t *testing.T) {
	sh := NewSelfHealing()
	breaker := sh.RegisterCircuitBreaker("test", 3, 100*time.Millisecond)

	// Initial state: closed
	if breaker.State() != CircuitClosed {
		t.Error("initial state should be closed")
	}
	if !breaker.Allow() {
		t.Error("should allow when closed")
	}

	// Record failures to open circuit
	breaker.RecordFailure()
	if breaker.State() != CircuitClosed {
		t.Error("should still be closed after 1 failure")
	}

	breaker.RecordFailure()
	if breaker.State() != CircuitClosed {
		t.Error("should still be closed after 2 failures")
	}

	breaker.RecordFailure()
	if breaker.State() != CircuitOpen {
		t.Error("should be open after 3 failures")
	}
	if breaker.Allow() {
		t.Error("should not allow when open")
	}

	// Wait for reset timeout
	time.Sleep(150 * time.Millisecond)
	if breaker.State() != CircuitHalfOpen {
		t.Error("should be half-open after timeout")
	}
	if !breaker.Allow() {
		t.Error("should allow in half-open")
	}

	// Record success in half-open to close circuit
	breaker.RecordSuccess()
	breaker.RecordSuccess()
	breaker.RecordSuccess()
	if breaker.State() != CircuitClosed {
		t.Errorf("should be closed after 3 successes in half-open, got %v", breaker.State())
	}
}

// TestCircuitBreakerRecordFailureInHalfOpenStdlib tests failure in half-open.
func TestCircuitBreakerRecordFailureInHalfOpenStdlib(t *testing.T) {
	sh := NewSelfHealing()
	breaker := sh.RegisterCircuitBreaker("test", 3, 50*time.Millisecond)

	// Open circuit
	breaker.RecordFailure()
	breaker.RecordFailure()
	breaker.RecordFailure()
	if breaker.State() != CircuitOpen {
		t.Error("should be open")
	}

	// Wait for half-open
	time.Sleep(60 * time.Millisecond)
	if breaker.State() != CircuitHalfOpen {
		t.Error("should be half-open")
	}

	// Single failure in half-open should reopen circuit
	breaker.RecordFailure()
	if breaker.State() != CircuitOpen {
		t.Error("should be open after failure in half-open")
	}
}

// TestCircuitBreakerStatsStdlib tests circuit breaker statistics.
func TestCircuitBreakerStatsStdlib(t *testing.T) {
	sh := NewSelfHealing()
	breaker := sh.RegisterCircuitBreaker("test", 5, 30*time.Second)

	stats := breaker.Stats()
	if stats.Name != "test" {
		t.Error("name incorrect")
	}
	if stats.State != CircuitClosed {
		t.Error("initial state incorrect")
	}
	if stats.Failures != 0 {
		t.Error("initial failures should be 0")
	}
	if stats.Successes != 0 {
		t.Error("initial successes should be 0")
	}

	breaker.RecordFailure()
	breaker.RecordFailure()
	breaker.RecordSuccess()

	stats = breaker.Stats()
	if stats.Failures != 2 {
		t.Errorf("expected 2 failures, got %d", stats.Failures)
	}
	if stats.Successes != 1 {
		t.Errorf("expected 1 success, got %d", stats.Successes)
	}
}

// TestCircuitStateStringStdlib tests circuit state strings.
func TestCircuitStateStringStdlib(t *testing.T) {
	if CircuitClosed.String() != "closed" {
		t.Error("closed string incorrect")
	}
	if CircuitOpen.String() != "open" {
		t.Error("open string incorrect")
	}
	if CircuitHalfOpen.String() != "half-open" {
		t.Error("half-open string incorrect")
	}
	if CircuitState(999).String() != "unknown" {
		t.Error("unknown state string incorrect")
	}
}

// TestExecuteStdlib tests executing with circuit breaker.
func TestExecuteStdlib(t *testing.T) {
	sh := NewSelfHealing()
	sh.RegisterCircuitBreaker("test", 3, 30*time.Second)

	ctx := context.Background()

	// Successful execution
	callCount := 0
	err := sh.Execute(ctx, "test", func() error {
		callCount++
		return nil
	})
	if err != nil {
		t.Errorf("Execute failed: %v", err)
	}
	if callCount != 1 {
		t.Errorf("expected 1 call, got %d", callCount)
	}

	// Failed execution
	err = sh.Execute(ctx, "test", func() error {
		return errors.New("test error")
	})
	if err == nil {
		t.Error("expected error from failed execution")
	}
}

// TestExecuteCircuitOpenStdlib tests execution with open circuit.
func TestExecuteCircuitOpenStdlib(t *testing.T) {
	sh := NewSelfHealing()
	breaker := sh.RegisterCircuitBreaker("test", 2, 30*time.Second)

	// Open circuit
	breaker.RecordFailure()
	breaker.RecordFailure()
	if breaker.State() != CircuitOpen {
		t.Error("circuit should be open")
	}

	ctx := context.Background()
	callCount := 0
	err := sh.Execute(ctx, "test", func() error {
		callCount++
		return nil
	})

	if err == nil {
		t.Error("expected error for open circuit")
	}
	if callCount != 0 {
		t.Error("function should not be called when circuit is open")
	}
}

// TestExecuteDisabledStdlib tests execution when disabled.
func TestExecuteDisabledStdlib(t *testing.T) {
	sh := NewSelfHealing()
	sh.Disable()
	sh.RegisterCircuitBreaker("test", 3, 30*time.Second)

	ctx := context.Background()
	callCount := 0
	err := sh.Execute(ctx, "test", func() error {
		callCount++
		return nil
	})

	if err != nil {
		t.Errorf("Execute failed: %v", err)
	}
	if callCount != 1 {
		t.Error("function should be called when disabled")
	}
}

// TestExecuteWithRetryStdlib tests retry logic.
func TestExecuteWithRetryStdlib(t *testing.T) {
	sh := NewSelfHealing()

	ctx := context.Background()

	// Success on first attempt
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

	// Success after retries
	callCount = 0
	err = sh.ExecuteWithRetry(ctx, func() error {
		callCount++
		if callCount < 3 {
			return errors.New("temporary error")
		}
		return nil
	}, &RetryPolicy{
		MaxRetries:        5,
		InitialBackoff:    10 * time.Millisecond,
		MaxBackoff:        100 * time.Millisecond,
		BackoffMultiplier: 2.0,
	})
	if err != nil {
		t.Errorf("ExecuteWithRetry failed: %v", err)
	}
	if callCount != 3 {
		t.Errorf("expected 3 calls, got %d", callCount)
	}

	// Max retries exceeded
	callCount = 0
	err = sh.ExecuteWithRetry(ctx, func() error {
		callCount++
		return errors.New("persistent error")
	}, &RetryPolicy{
		MaxRetries:     2,
		InitialBackoff: 1 * time.Millisecond,
	})
	if err == nil {
		t.Error("expected error after max retries")
	}
	if callCount != 3 { // Initial + 2 retries
		t.Errorf("expected 3 calls, got %d", callCount)
	}
}

// TestDetectFaultStdlib tests fault detection.
func TestDetectFaultStdlib(t *testing.T) {
	sh := NewSelfHealing()

	testErr := errors.New("test error")
	fault := sh.DetectFault(FaultTypeError, "service-a", "Service failed", testErr)

	if fault == nil {
		t.Fatal("DetectFault returned nil")
	}
	if fault.ID == "" {
		t.Error("fault ID is empty")
	}
	if fault.Type != FaultTypeError {
		t.Error("fault type incorrect")
	}
	if fault.Component != "service-a" {
		t.Error("component incorrect")
	}
	if fault.Message != "Service failed" {
		t.Error("message incorrect")
	}
	if fault.Error != testErr {
		t.Error("error incorrect")
	}
	if fault.Resolved {
		t.Error("fault should not be resolved initially")
	}

	// Verify stored in knowledge
	ctx := context.Background()
	stored, err := sh.knowledge.Retrieve(ctx, "fault_"+fault.ID)
	if err != nil {
		t.Errorf("fault not stored in knowledge: %v", err)
	}
	if stored == nil {
		t.Error("stored fault is nil")
	}
}

// TestDetectFaultSeveritiesStdlib tests fault severity inference.
func TestDetectFaultSeveritiesStdlib(t *testing.T) {
	sh := NewSelfHealing()

	tests := []struct {
		faultType FaultType
		expected  SeverityLevel
	}{
		{FaultTypePanic, SeverityCritical},
		{FaultTypeResource, SeverityCritical},
		{FaultTypeTimeout, SeverityWarning},
		{FaultTypeNetwork, SeverityWarning},
		{FaultTypeError, SeverityWarning},
		{FaultTypeUnknown, SeverityInfo},
	}

	for _, tt := range tests {
		fault := sh.DetectFault(tt.faultType, "test", "test", nil)
		if fault.Severity != tt.expected {
			t.Errorf("FaultType %v: expected severity %v, got %v", tt.faultType, tt.expected, fault.Severity)
		}
	}
}

// TestGetFaultStdlib tests retrieving a fault.
func TestGetFaultStdlib(t *testing.T) {
	sh := NewSelfHealing()

	fault := sh.DetectFault(FaultTypeError, "service", "error", nil)

	ctx := context.Background()
	retrieved, err := sh.GetFault(ctx, fault.ID)
	if err != nil {
		t.Fatalf("GetFault failed: %v", err)
	}
	if retrieved.ID != fault.ID {
		t.Error("retrieved fault ID mismatch")
	}

	// Test non-existent fault
	_, err = sh.GetFault(ctx, "nonexistent")
	if err != ErrFaultNotFound {
		t.Errorf("expected ErrFaultNotFound, got %v", err)
	}
}

// TestResolveFaultStdlib tests resolving a fault.
func TestResolveFaultStdlib(t *testing.T) {
	sh := NewSelfHealing()

	fault := sh.DetectFault(FaultTypeError, "service", "error", nil)
	if fault.Resolved {
		t.Error("fault should not be resolved initially")
	}

	ctx := context.Background()
	err := sh.ResolveFault(ctx, fault.ID)
	if err != nil {
		t.Fatalf("ResolveFault failed: %v", err)
	}

	// Verify resolved
	retrieved, err := sh.GetFault(ctx, fault.ID)
	if err != nil {
		t.Fatalf("GetFault failed: %v", err)
	}
	if !retrieved.Resolved {
		t.Error("fault should be resolved")
	}
	if retrieved.ResolvedAt == nil {
		t.Error("ResolvedAt should be set")
	}

	// Test resolving non-existent fault
	err = sh.ResolveFault(ctx, "nonexistent")
	if err != ErrFaultNotFound {
		t.Errorf("expected ErrFaultNotFound, got %v", err)
	}
}

// TestRemediateStdlib tests fault remediation.
func TestRemediateStdlib(t *testing.T) {
	sh := NewSelfHealing()

	remediationCalled := false
	action := NewFuncRemediationAction(
		"test-action",
		100,
		func(fault *Fault) bool {
			return fault.Type == FaultTypeError
		},
		func(ctx context.Context, fault *Fault) (*RemediationResult, error) {
			remediationCalled = true
			return &RemediationResult{
				Action:    "test-action",
				FaultID:   fault.ID,
				Success:   true,
				Message:   "Fixed",
				Timestamp: time.Now(),
			}, nil
		},
	)

	sh.RegisterRemediation(action)

	fault := sh.DetectFault(FaultTypeError, "service", "error", nil)

	ctx := context.Background()
	result, err := sh.Remediate(ctx, fault)
	if err != nil {
		t.Fatalf("Remediate failed: %v", err)
	}
	if result == nil {
		t.Fatal("result is nil")
	}

	if !remediationCalled {
		t.Error("remediation action was not called")
	}
	if !result.Success {
		t.Error("remediation should succeed")
	}

	// Verify fault is resolved
	retrieved, _ := sh.GetFault(ctx, fault.ID)
	if !retrieved.Resolved {
		t.Error("fault should be resolved after successful remediation")
	}
}

// TestRemediateNoActionStdlib tests remediation with no available action.
func TestRemediateNoActionStdlib(t *testing.T) {
	sh := NewSelfHealing()

	fault := sh.DetectFault(FaultTypeError, "service", "error", nil)

	ctx := context.Background()
	_, err := sh.Remediate(ctx, fault)
	if err != ErrNoRemediationAvailable {
		t.Errorf("expected ErrNoRemediationAvailable, got %v", err)
	}
}

// TestHealthCheckerStdlib tests health checker interface.
func TestHealthCheckerStdlib(t *testing.T) {
	sh := NewSelfHealing()

	checkCount := 0
	checker := NewFuncHealthChecker(
		"test-service",
		30*time.Second,
		func(ctx context.Context) (*HealthCheckResult, error) {
			checkCount++
			return &HealthCheckResult{
				Name:      "test-service",
				Status:    HealthHealthy,
				Message:   "All good",
				Latency:   10 * time.Millisecond,
				Timestamp: time.Now(),
			}, nil
		},
	)

	sh.RegisterHealthChecker(checker)

	ctx := context.Background()
	results, faults := sh.RunHealthChecks(ctx)

	if len(results) != 1 {
		t.Errorf("expected 1 result, got %d", len(results))
	}
	if results[0].Name != "test-service" {
		t.Error("result name incorrect")
	}
	if results[0].Status != HealthHealthy {
		t.Error("result status should be healthy")
	}
	if len(faults) != 0 {
		t.Error("should have no faults for healthy check")
	}
	if checkCount != 1 {
		t.Errorf("expected 1 check, got %d", checkCount)
	}
}

// TestHealthCheckerUnhealthyStdlib tests unhealthy health check.
func TestHealthCheckerUnhealthyStdlib(t *testing.T) {
	sh := NewSelfHealing()

	checker := NewFuncHealthChecker(
		"unhealthy-service",
		30*time.Second,
		func(ctx context.Context) (*HealthCheckResult, error) {
			return &HealthCheckResult{
				Name:      "unhealthy-service",
				Status:    HealthUnhealthy,
				Message:   "Service down",
				Timestamp: time.Now(),
			}, nil
		},
	)

	sh.RegisterHealthChecker(checker)

	ctx := context.Background()
	results, faults := sh.RunHealthChecks(ctx)

	if len(results) != 1 {
		t.Errorf("expected 1 result, got %d", len(results))
	}
	if results[0].Status != HealthUnhealthy {
		t.Error("result status should be unhealthy")
	}
	if len(faults) != 1 {
		t.Errorf("expected 1 fault, got %d", len(faults))
	}
	if faults[0].Component != "unhealthy-service" {
		t.Error("fault component incorrect")
	}
}

// TestGetStatsStdlib tests statistics.
func TestGetStatsStdlib(t *testing.T) {
	sh := NewSelfHealing()

	// Initial stats
	stats := sh.GetStats()
	if stats.FaultsDetected != 0 {
		t.Error("initial faults should be 0")
	}
	if stats.RecoveriesAttempted != 0 {
		t.Error("initial recoveries attempted should be 0")
	}
	if stats.RecoveriesSucceeded != 0 {
		t.Error("initial recoveries succeeded should be 0")
	}

	// Detect faults
	_ = sh.DetectFault(FaultTypeError, "service", "error", nil)
	_ = sh.DetectFault(FaultTypeError, "service", "error2", nil)

	stats = sh.GetStats()
	if stats.FaultsDetected != 2 {
		t.Errorf("expected 2 faults detected, got %d", stats.FaultsDetected)
	}
}

// TestFaultTypeStringStdlib tests fault type strings.
func TestFaultTypeStringStdlib(t *testing.T) {
	if FaultTypeNetwork.String() != "network" {
		t.Error("network string incorrect")
	}
	if FaultTypeResource.String() != "resource" {
		t.Error("resource string incorrect")
	}
	if FaultTypeTimeout.String() != "timeout" {
		t.Error("timeout string incorrect")
	}
	if FaultTypeError.String() != "error" {
		t.Error("error string incorrect")
	}
	if FaultTypePanic.String() != "panic" {
		t.Error("panic string incorrect")
	}
	if FaultTypeUnknown.String() != "unknown" {
		t.Error("unknown string incorrect")
	}
	if FaultType(999).String() != "unknown" {
		t.Error("unknown type string incorrect")
	}
}

// TestRestartRemediationActionStdlib tests restart action.
func TestRestartRemediationActionStdlib(t *testing.T) {
	restartCalled := false
	action := NewRestartRemediationAction(func(ctx context.Context, component string) error {
		restartCalled = true
		if component != "test-service" {
			t.Errorf("expected 'test-service', got %q", component)
		}
		return nil
	})

	if action.Name() != "restart" {
		t.Error("name incorrect")
	}
	if action.Priority() != 100 {
		t.Error("priority incorrect")
	}

	fault := &Fault{
		ID:        "fault-1",
		Type:      FaultTypeError,
		Component: "test-service",
	}

	if !action.CanHandle(fault) {
		t.Error("should handle error fault")
	}

	ctx := context.Background()
	result, err := action.Execute(ctx, fault)
	if err != nil {
		t.Fatalf("Execute failed: %v", err)
	}

	if !restartCalled {
		t.Error("restart function was not called")
	}
	if !result.Success {
		t.Error("result should be successful")
	}
	if result.Message == "" {
		t.Error("message should not be empty")
	}

	// Test panic fault
	fault.Type = FaultTypePanic
	if !action.CanHandle(fault) {
		t.Error("should handle panic fault")
	}

	// Test non-handled fault type
	fault.Type = FaultTypeTimeout
	if action.CanHandle(fault) {
		t.Error("should not handle timeout fault")
	}
}

// TestRestartRemediationActionFailureStdlib tests failed restart.
func TestRestartRemediationActionFailureStdlib(t *testing.T) {
	action := NewRestartRemediationAction(func(ctx context.Context, component string) error {
		return errors.New("restart failed")
	})

	fault := &Fault{
		ID:        "fault-1",
		Type:      FaultTypeError,
		Component: "test-service",
	}

	ctx := context.Background()
	result, err := action.Execute(ctx, fault)
	if err == nil {
		t.Error("expected error")
	}

	if result.Success {
		t.Error("result should not be successful")
	}
	if result.Error == "" {
		t.Error("error should be set")
	}
}

// TestRestartRemediationActionNilFuncStdlib tests restart with nil function.
func TestRestartRemediationActionNilFuncStdlib(t *testing.T) {
	action := NewRestartRemediationAction(nil)

	fault := &Fault{
		ID:        "fault-1",
		Type:      FaultTypeError,
		Component: "test-service",
	}

	ctx := context.Background()
	_, err := action.Execute(ctx, fault)
	if err == nil {
		t.Error("expected error")
	}
}

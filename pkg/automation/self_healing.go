// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
//
// This file implements self-healing mechanisms for automatic fault detection and recovery.
// It includes circuit breakers, retry policies, fallback mechanisms, and automated
// remediation actions.
package automation

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"sync/atomic"
	"time"
)

// SelfHealing provides automatic fault detection and recovery capabilities.
// It implements circuit breaker pattern, automated retries, and remediation actions.
type SelfHealing struct {
	knowledge    Knowledge
	breakers     map[string]*CircuitBreaker
	healthChecks map[string]HealthChecker
	remediations map[string]RemediationAction
	enabled      bool

	// Configuration
	defaultTimeout   time.Duration
	recoveryInterval time.Duration
	maxRetries       int
	retryBackoff     time.Duration

	// Statistics
	faultsDetected      uint64
	recoveriesAttempted uint64
	recoveriesSucceeded uint64

	mu sync.RWMutex
}

// CircuitBreaker implements the circuit breaker pattern.
type CircuitBreaker struct {
	name         string
	state        CircuitState
	failures     uint64
	successes    uint64
	lastFailure  time.Time
	lastSuccess  time.Time
	threshold    uint32
	resetTimeout time.Duration
	halfOpenMax  uint32

	mu sync.RWMutex
}

// CircuitState represents the state of a circuit breaker.
type CircuitState int32

const (
	// CircuitClosed means the circuit is closed and requests flow normally
	CircuitClosed CircuitState = iota
	// CircuitOpen means the circuit is open and requests are blocked
	CircuitOpen
	// CircuitHalfOpen means the circuit is testing if the problem is resolved
	CircuitHalfOpen
)

// String returns the string representation of circuit state.
func (s CircuitState) String() string {
	switch s {
	case CircuitClosed:
		return "closed"
	case CircuitOpen:
		return "open"
	case CircuitHalfOpen:
		return "half-open"
	default:
		return "unknown"
	}
}

// HealthChecker checks the health of a component.
type HealthChecker interface {
	// Check performs a health check
	Check(ctx context.Context) (*HealthCheckResult, error)
	// Name returns the checker name
	Name() string
	// Interval returns the check interval
	Interval() time.Duration
}

// HealthCheckResult represents the result of a health check.
type HealthCheckResult struct {
	Name      string
	Status    HealthStatus
	Message   string
	Latency   time.Duration
	Timestamp time.Time
	Metadata  map[string]interface{}
}

// RemediationAction represents an action to remediate a fault.
type RemediationAction interface {
	// Execute executes the remediation action
	Execute(ctx context.Context, fault *Fault) (*RemediationResult, error)
	// Name returns the action name
	Name() string
	// CanHandle checks if this action can handle the fault
	CanHandle(fault *Fault) bool
	// Priority returns the action priority (higher = more urgent)
	Priority() int
}

// Fault represents a detected fault in the system.
type Fault struct {
	ID         string
	Type       FaultType
	Component  string
	Severity   SeverityLevel
	Message    string
	Error      error
	Timestamp  time.Time
	Context    map[string]interface{}
	Resolved   bool
	ResolvedAt *time.Time
}

// FaultType represents the type of fault.
type FaultType int

const (
	// FaultTypeUnknown represents an unknown fault type
	FaultTypeUnknown FaultType = iota
	// FaultTypeNetwork represents a network-related fault
	FaultTypeNetwork
	// FaultTypeResource represents a resource exhaustion fault
	FaultTypeResource
	// FaultTypeTimeout represents a timeout fault
	FaultTypeTimeout
	// FaultTypeError represents a general error fault
	FaultTypeError
	// FaultTypePanic represents a panic/crash fault
	FaultTypePanic
)

// String returns the string representation of fault type.
func (t FaultType) String() string {
	switch t {
	case FaultTypeNetwork:
		return "network"
	case FaultTypeResource:
		return "resource"
	case FaultTypeTimeout:
		return "timeout"
	case FaultTypeError:
		return "error"
	case FaultTypePanic:
		return "panic"
	default:
		return "unknown"
	}
}

// RemediationResult represents the result of a remediation action.
type RemediationResult struct {
	Action      string
	FaultID     string
	Success     bool
	Message     string
	Error       string
	Timestamp   time.Time
	RetryNeeded bool
	NewFault    *Fault
}

// RetryPolicy defines retry behavior for operations.
type RetryPolicy struct {
	MaxRetries        int
	InitialBackoff    time.Duration
	MaxBackoff        time.Duration
	BackoffMultiplier float64
	RetryableErrors   []error
}

// Common errors.
var (
	// ErrCircuitOpen is returned when the circuit breaker is open
	ErrCircuitOpen = errors.New("circuit breaker is open")
	// ErrHealthCheckFailed is returned when a health check fails
	ErrHealthCheckFailed = errors.New("health check failed")
	// ErrRemediationFailed is returned when remediation fails
	ErrRemediationFailed = errors.New("remediation failed")
	// ErrNoRemediationAvailable is returned when no remediation is available
	ErrNoRemediationAvailable = errors.New("no remediation action available")
	// ErrFaultNotFound is returned when a fault is not found
	ErrFaultNotFound = errors.New("fault not found")
)

// NewSelfHealing creates a new self-healing manager.
func NewSelfHealing() *SelfHealing {
	return &SelfHealing{
		knowledge:        NewMemoryKnowledge(),
		breakers:         make(map[string]*CircuitBreaker),
		healthChecks:     make(map[string]HealthChecker),
		remediations:     make(map[string]RemediationAction),
		defaultTimeout:   30 * time.Second,
		recoveryInterval: 30 * time.Second,
		maxRetries:       3,
		retryBackoff:     time.Second,
		enabled:          true,
	}
}

// WithKnowledge sets the knowledge base.
func (s *SelfHealing) WithKnowledge(knowledge Knowledge) *SelfHealing {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.knowledge = knowledge
	return s
}

// WithDefaultTimeout sets the default timeout.
func (s *SelfHealing) WithDefaultTimeout(timeout time.Duration) *SelfHealing {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.defaultTimeout = timeout
	return s
}

// WithRecoveryInterval sets the recovery check interval.
func (s *SelfHealing) WithRecoveryInterval(interval time.Duration) *SelfHealing {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.recoveryInterval = interval
	return s
}

// WithMaxRetries sets the maximum retry count.
func (s *SelfHealing) WithMaxRetries(maxRetries int) *SelfHealing {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.maxRetries = maxRetries
	return s
}

// Enable enables self-healing.
func (s *SelfHealing) Enable() {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.enabled = true
}

// Disable disables self-healing.
func (s *SelfHealing) Disable() {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.enabled = false
}

// IsEnabled returns whether self-healing is enabled.
func (s *SelfHealing) IsEnabled() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.enabled
}

// RegisterCircuitBreaker registers a circuit breaker.
func (s *SelfHealing) RegisterCircuitBreaker(name string, threshold uint32, resetTimeout time.Duration) *CircuitBreaker {
	s.mu.Lock()
	defer s.mu.Unlock()

	breaker := &CircuitBreaker{
		name:         name,
		state:        CircuitClosed,
		threshold:    threshold,
		resetTimeout: resetTimeout,
		halfOpenMax:  3,
	}

	s.breakers[name] = breaker
	return breaker
}

// GetCircuitBreaker returns a registered circuit breaker.
func (s *SelfHealing) GetCircuitBreaker(name string) (*CircuitBreaker, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	breaker, ok := s.breakers[name]
	return breaker, ok
}

// RegisterHealthChecker registers a health checker.
func (s *SelfHealing) RegisterHealthChecker(checker HealthChecker) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.healthChecks[checker.Name()] = checker
}

// UnregisterHealthChecker removes a health checker.
func (s *SelfHealing) UnregisterHealthChecker(name string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	delete(s.healthChecks, name)
}

// RegisterRemediation registers a remediation action.
func (s *SelfHealing) RegisterRemediation(action RemediationAction) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.remediations[action.Name()] = action
}

// UnregisterRemediation removes a remediation action.
func (s *SelfHealing) UnregisterRemediation(name string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	delete(s.remediations, name)
}

// Execute executes a function with circuit breaker protection.
func (s *SelfHealing) Execute(ctx context.Context, breakerName string, fn func() error) error {
	s.mu.RLock()
	breaker, ok := s.breakers[breakerName]
	enabled := s.enabled
	s.mu.RUnlock()

	if !enabled {
		return fn()
	}

	if !ok {
		return fn()
	}

	if !breaker.Allow() {
		return fmt.Errorf("%w: %s", ErrCircuitOpen, breakerName)
	}

	err := fn()
	if err != nil {
		breaker.RecordFailure()
		return err
	}

	breaker.RecordSuccess()
	return nil
}

// ExecuteWithRetry executes a function with retry logic.
func (s *SelfHealing) ExecuteWithRetry(ctx context.Context, fn func() error, policy *RetryPolicy) error {
	s.mu.RLock()
	maxRetries := s.maxRetries
	backoff := s.retryBackoff
	s.mu.RUnlock()

	if policy != nil {
		maxRetries = policy.MaxRetries
		backoff = policy.InitialBackoff
	}

	var lastErr error
	for i := 0; i <= maxRetries; i++ {
		if i > 0 {
			// Wait before retry
			select {
			case <-ctx.Done():
				return ctx.Err()
			case <-time.After(backoff):
			}

			// Exponential backoff
			if policy != nil && policy.BackoffMultiplier > 0 {
				backoff = time.Duration(float64(backoff) * policy.BackoffMultiplier)
				if policy.MaxBackoff > 0 && backoff > policy.MaxBackoff {
					backoff = policy.MaxBackoff
				}
			}
		}

		err := fn()
		if err == nil {
			return nil
		}

		lastErr = err

		// Check if error is retryable
		if policy != nil && len(policy.RetryableErrors) > 0 {
			retryable := false
			for _, retryableErr := range policy.RetryableErrors {
				if errors.Is(err, retryableErr) {
					retryable = true
					break
				}
			}
			if !retryable {
				return err
			}
		}
	}

	return fmt.Errorf("max retries exceeded: %w", lastErr)
}

// DetectFault detects and records a fault.
func (s *SelfHealing) DetectFault(faultType FaultType, component, message string, err error) *Fault {
	atomic.AddUint64(&s.faultsDetected, 1)

	fault := &Fault{
		ID:        fmt.Sprintf("fault-%d", time.Now().UnixNano()),
		Type:      faultType,
		Component: component,
		Severity:  s.inferSeverity(faultType),
		Message:   message,
		Error:     err,
		Timestamp: time.Now(),
		Context:   make(map[string]interface{}),
		Resolved:  false,
	}

	// Store in knowledge
	_ = s.knowledge.Store(context.Background(), "fault_"+fault.ID, fault)
	_ = s.knowledge.Store(context.Background(), "last_fault", fault)

	return fault
}

// GetFault retrieves a fault by ID.
func (s *SelfHealing) GetFault(ctx context.Context, id string) (*Fault, error) {
	value, err := s.knowledge.Retrieve(ctx, "fault_"+id)
	if err != nil {
		return nil, ErrFaultNotFound
	}

	fault, ok := value.(*Fault)
	if !ok {
		return nil, ErrFaultNotFound
	}

	return fault, nil
}

// ResolveFault marks a fault as resolved.
func (s *SelfHealing) ResolveFault(ctx context.Context, id string) error {
	fault, err := s.GetFault(ctx, id)
	if err != nil {
		return err
	}

	fault.Resolved = true
	now := time.Now()
	fault.ResolvedAt = &now

	return s.knowledge.Update(ctx, "fault_"+id, fault)
}

// Remediate attempts to remediate a fault.
func (s *SelfHealing) Remediate(ctx context.Context, fault *Fault) (*RemediationResult, error) {
	atomic.AddUint64(&s.recoveriesAttempted, 1)

	s.mu.RLock()
	remediations := make(map[string]RemediationAction, len(s.remediations))
	for k, v := range s.remediations {
		remediations[k] = v
	}
	s.mu.RUnlock()

	// Find suitable remediation actions
	var candidates []RemediationAction
	for _, action := range remediations {
		if action.CanHandle(fault) {
			candidates = append(candidates, action)
		}
	}

	if len(candidates) == 0 {
		return nil, ErrNoRemediationAvailable
	}

	// Sort by priority (higher first)
	for i := 0; i < len(candidates)-1; i++ {
		for j := i + 1; j < len(candidates); j++ {
			if candidates[j].Priority() > candidates[i].Priority() {
				candidates[i], candidates[j] = candidates[j], candidates[i]
			}
		}
	}

	// Try each action
	for _, action := range candidates {
		result, err := action.Execute(ctx, fault)
		if err != nil {
			continue
		}

		if result.Success {
			atomic.AddUint64(&s.recoveriesSucceeded, 1)
			_ = s.ResolveFault(ctx, fault.ID)
		}

		return result, nil
	}

	return nil, ErrRemediationFailed
}

// RunHealthChecks runs all registered health checks.
func (s *SelfHealing) RunHealthChecks(ctx context.Context) ([]*HealthCheckResult, []*Fault) {
	s.mu.RLock()
	checkers := make(map[string]HealthChecker, len(s.healthChecks))
	for k, v := range s.healthChecks {
		checkers[k] = v
	}
	s.mu.RUnlock()

	var results []*HealthCheckResult
	var faults []*Fault

	for _, checker := range checkers {
		result, err := checker.Check(ctx)
		if err != nil {
			result = &HealthCheckResult{
				Name:      checker.Name(),
				Status:    HealthUnhealthy,
				Message:   err.Error(),
				Timestamp: time.Now(),
			}
		}

		results = append(results, result)

		// Create fault for unhealthy checks
		if result.Status == HealthUnhealthy || result.Status == HealthDegraded {
			fault := s.DetectFault(FaultTypeError, result.Name, result.Message, err)
			faults = append(faults, fault)
		}

		// Store result in knowledge
		_ = s.knowledge.Store(ctx, "health_"+result.Name, result)
	}

	_ = s.knowledge.Store(ctx, "last_health_check", time.Now())

	return results, faults
}

// GetStats returns self-healing statistics.
func (s *SelfHealing) GetStats() SelfHealingStats {
	return SelfHealingStats{
		FaultsDetected:      atomic.LoadUint64(&s.faultsDetected),
		RecoveriesAttempted: atomic.LoadUint64(&s.recoveriesAttempted),
		RecoveriesSucceeded: atomic.LoadUint64(&s.recoveriesSucceeded),
	}
}

// SelfHealingStats contains self-healing statistics.
type SelfHealingStats struct {
	FaultsDetected      uint64
	RecoveriesAttempted uint64
	RecoveriesSucceeded uint64
}

// inferSeverity infers fault severity from type.
func (s *SelfHealing) inferSeverity(faultType FaultType) SeverityLevel {
	switch faultType {
	case FaultTypePanic:
		return SeverityCritical
	case FaultTypeResource:
		return SeverityCritical
	case FaultTypeTimeout:
		return SeverityWarning
	case FaultTypeNetwork:
		return SeverityWarning
	case FaultTypeError:
		return SeverityWarning
	default:
		return SeverityInfo
	}
}

// Circuit breaker methods

// State returns the current circuit state.
func (cb *CircuitBreaker) State() CircuitState {
	cb.mu.RLock()
	state := cb.state
	lastFailure := cb.lastFailure
	cb.mu.RUnlock()

	// Check if we should transition from open to half-open
	if state == CircuitOpen && time.Since(lastFailure) > cb.resetTimeout {
		cb.mu.Lock()
		if cb.state == CircuitOpen && time.Since(cb.lastFailure) > cb.resetTimeout {
			cb.state = CircuitHalfOpen
			cb.failures = 0
			cb.successes = 0
		}
		state = cb.state
		cb.mu.Unlock()
	}

	return state
}

// Allow checks if a request should be allowed.
func (cb *CircuitBreaker) Allow() bool {
	state := cb.State()

	switch state {
	case CircuitClosed:
		return true
	case CircuitHalfOpen:
		cb.mu.RLock()
		allow := cb.failures+cb.successes < uint64(cb.halfOpenMax)
		cb.mu.RUnlock()
		return allow
	default: // CircuitOpen
		return false
	}
}

// RecordSuccess records a successful call.
func (cb *CircuitBreaker) RecordSuccess() {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	cb.successes++
	cb.lastSuccess = time.Now()

	if cb.state == CircuitHalfOpen {
		if cb.successes >= uint64(cb.halfOpenMax) {
			cb.state = CircuitClosed
			cb.failures = 0
		}
	}
}

// RecordFailure records a failed call.
func (cb *CircuitBreaker) RecordFailure() {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	cb.failures++
	cb.lastFailure = time.Now()

	switch cb.state {
	case CircuitClosed:
		if cb.failures >= uint64(cb.threshold) {
			cb.state = CircuitOpen
		}
	case CircuitHalfOpen:
		cb.state = CircuitOpen
	}
}

// Stats returns circuit breaker statistics.
func (cb *CircuitBreaker) Stats() CircuitBreakerStats {
	cb.mu.RLock()
	defer cb.mu.RUnlock()

	return CircuitBreakerStats{
		Name:        cb.name,
		State:       cb.state,
		Failures:    cb.failures,
		Successes:   cb.successes,
		LastFailure: cb.lastFailure,
		LastSuccess: cb.lastSuccess,
	}
}

// CircuitBreakerStats contains circuit breaker statistics.
type CircuitBreakerStats struct {
	Name        string
	State       CircuitState
	Failures    uint64
	Successes   uint64
	LastFailure time.Time
	LastSuccess time.Time
}

// FuncHealthChecker adapts a function to HealthChecker.
type FuncHealthChecker struct {
	name     string
	interval time.Duration
	check    func(ctx context.Context) (*HealthCheckResult, error)
}

// NewFuncHealthChecker creates a new functional health checker.
func NewFuncHealthChecker(name string, interval time.Duration, check func(ctx context.Context) (*HealthCheckResult, error)) HealthChecker {
	return &FuncHealthChecker{
		name:     name,
		interval: interval,
		check:    check,
	}
}

// Name returns the checker name.
func (f *FuncHealthChecker) Name() string { return f.name }

// Interval returns the check interval.
func (f *FuncHealthChecker) Interval() time.Duration { return f.interval }

// Check performs the health check.
func (f *FuncHealthChecker) Check(ctx context.Context) (*HealthCheckResult, error) {
	return f.check(ctx)
}

// FuncRemediationAction adapts a function to RemediationAction.
type FuncRemediationAction struct {
	name      string
	priority  int
	canHandle func(fault *Fault) bool
	execute   func(ctx context.Context, fault *Fault) (*RemediationResult, error)
}

// NewFuncRemediationAction creates a new functional remediation action.
func NewFuncRemediationAction(
	name string,
	priority int,
	canHandle func(fault *Fault) bool,
	execute func(ctx context.Context, fault *Fault) (*RemediationResult, error),
) RemediationAction {
	return &FuncRemediationAction{
		name:      name,
		priority:  priority,
		canHandle: canHandle,
		execute:   execute,
	}
}

// Name returns the action name.
func (f *FuncRemediationAction) Name() string { return f.name }

// Priority returns the action priority.
func (f *FuncRemediationAction) Priority() int { return f.priority }

// CanHandle checks if this action can handle the fault.
func (f *FuncRemediationAction) CanHandle(fault *Fault) bool {
	if f.canHandle != nil {
		return f.canHandle(fault)
	}
	return true
}

// Execute executes the remediation action.
func (f *FuncRemediationAction) Execute(ctx context.Context, fault *Fault) (*RemediationResult, error) {
	return f.execute(ctx, fault)
}

// SelfHealingMonitor implements the Monitor interface.
type SelfHealingMonitor struct {
	selfHealing *SelfHealing
}

// NewSelfHealingMonitor creates a new self-healing monitor.
func NewSelfHealingMonitor(sh *SelfHealing) *SelfHealingMonitor {
	return &SelfHealingMonitor{
		selfHealing: sh,
	}
}

// Name returns the monitor name.
func (m *SelfHealingMonitor) Name() string {
	return "self-healing-monitor"
}

// Collect gathers monitoring data.
func (m *SelfHealingMonitor) Collect(ctx context.Context) (*MonitoringData, error) {
	data := &MonitoringData{
		Timestamp:  time.Now(),
		Metrics:    make(map[string]float64),
		Attributes: make(map[string]string),
		Health:     HealthHealthy,
	}

	// Add circuit breaker stats
	m.selfHealing.mu.RLock()
	breakers := make(map[string]*CircuitBreaker, len(m.selfHealing.breakers))
	for k, v := range m.selfHealing.breakers {
		breakers[k] = v
	}
	enabled := m.selfHealing.enabled
	m.selfHealing.mu.RUnlock()

	if !enabled {
		data.Health = HealthDegraded
		data.Attributes["self_healing"] = "disabled"
	}

	totalFailures := uint64(0)
	openCircuits := 0

	for name, breaker := range breakers {
		stats := breaker.Stats()
		totalFailures += stats.Failures
		if stats.State == CircuitOpen {
			openCircuits++
		}
		data.Metrics["breaker_"+name+"_failures"] = float64(stats.Failures)
	}

	data.Metrics["total_circuit_failures"] = float64(totalFailures)
	data.Metrics["open_circuits"] = float64(openCircuits)

	// Add stats
	stats := m.selfHealing.GetStats()
	data.Metrics["faults_detected"] = float64(stats.FaultsDetected)
	data.Metrics["recoveries_attempted"] = float64(stats.RecoveriesAttempted)
	data.Metrics["recoveries_succeeded"] = float64(stats.RecoveriesSucceeded)

	if stats.RecoveriesAttempted > 0 {
		successRate := float64(stats.RecoveriesSucceeded) / float64(stats.RecoveriesAttempted)
		data.Metrics["recovery_success_rate"] = successRate
	}

	// Determine health
	if openCircuits > 0 || !enabled {
		data.Health = HealthDegraded
	}

	return data, nil
}

// RestartRemediationAction restarts a component.
type RestartRemediationAction struct {
	restartFn func(ctx context.Context, component string) error
}

// NewRestartRemediationAction creates a restart action.
func NewRestartRemediationAction(restartFn func(ctx context.Context, component string) error) RemediationAction {
	return &RestartRemediationAction{
		restartFn: restartFn,
	}
}

// Name returns the action name.
func (r *RestartRemediationAction) Name() string {
	return "restart"
}

// Priority returns the action priority.
func (r *RestartRemediationAction) Priority() int {
	return 100
}

// CanHandle checks if this action can handle the fault.
func (r *RestartRemediationAction) CanHandle(fault *Fault) bool {
	return fault.Type == FaultTypePanic || fault.Type == FaultTypeError
}

// Execute executes the restart.
func (r *RestartRemediationAction) Execute(ctx context.Context, fault *Fault) (*RemediationResult, error) {
	if r.restartFn == nil {
		return nil, errors.New("restart function not configured")
	}

	err := r.restartFn(ctx, fault.Component)

	result := &RemediationResult{
		Action:    "restart",
		FaultID:   fault.ID,
		Success:   err == nil,
		Timestamp: time.Now(),
	}

	if err != nil {
		result.Error = err.Error()
		result.Message = fmt.Sprintf("Failed to restart %s: %v", fault.Component, err)
	} else {
		result.Message = fmt.Sprintf("Successfully restarted %s", fault.Component)
	}

	return result, err
}

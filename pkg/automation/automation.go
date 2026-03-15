// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
//
// This package implements MAPE-K (Monitor-Analyze-Plan-Execute-Knowledge) loop
// for autonomous system management including:
//   - Auto-configuration based on metrics
//   - Predictive auto-scaling
//   - Self-healing and fault tolerance
//
// Example usage:
//
//	// Create MAPE-K loop
//
// mapek := automation.NewMAPEK()
//
//	// Add monitoring
//	mapek.WithMonitor(automation.NewMetricsMonitor())
//
//	// Add auto-scaling
//	scaler := automation.NewAutoScaler(config)
//	mapek.WithExecutor(scaler)
//
//	// Start the loop
//	ctx, cancel := context.WithCancel(context.Background())
//	defer cancel()
//	if err := mapek.Start(ctx); err != nil {
//	    log.Fatal(err)
//	}
package automation

import (
	"context"
	"errors"
	"sync"
	"time"
)

// MAPEKLoop implements the MAPE-K (Monitor-Analyze-Plan-Execute-Knowledge) control loop.
// It provides a framework for autonomous system management through continuous monitoring,
// analysis, planning, and execution with knowledge retention.
type MAPEKLoop struct {
	monitor   Monitor
	analyzer  Analyzer
	planner   Planner
	executor  Executor
	knowledge Knowledge

	interval time.Duration
	running  bool
	stopCh   chan struct{}
	wg       sync.WaitGroup
	mu       sync.RWMutex
}

// Monitor collects data from the system and environment.
type Monitor interface {
	// Collect gathers monitoring data
	Collect(ctx context.Context) (*MonitoringData, error)
	// Name returns the monitor name
	Name() string
}

// Analyzer processes monitoring data to detect issues and opportunities.
type Analyzer interface {
	// Analyze processes monitoring data and returns analysis results
	Analyze(ctx context.Context, data *MonitoringData) (*AnalysisResult, error)
	// Name returns the analyzer name
	Name() string
}

// Planner creates action plans based on analysis results.
type Planner interface {
	// Plan creates an action plan based on analysis
	Plan(ctx context.Context, result *AnalysisResult) (*ActionPlan, error)
	// Name returns the planner name
	Name() string
}

// Executor carries out the planned actions.
type Executor interface {
	// Execute carries out the action plan
	Execute(ctx context.Context, plan *ActionPlan) (*ExecutionResult, error)
	// Name returns the executor name
	Name() string
}

// Knowledge stores and manages system state and learned information.
type Knowledge interface {
	// Store saves information to knowledge base
	Store(ctx context.Context, key string, value interface{}) error
	// Retrieve gets information from knowledge base
	Retrieve(ctx context.Context, key string) (interface{}, error)
	// Update updates existing information
	Update(ctx context.Context, key string, value interface{}) error
	// History returns historical data for a key
	History(ctx context.Context, key string, limit int) ([]KnowledgeRecord, error)
}

// MonitoringData represents data collected from system monitoring.
type MonitoringData struct {
	Timestamp  time.Time
	Metrics    map[string]float64
	Attributes map[string]string
	Health     HealthStatus
	Components []ComponentStatus
}

// HealthStatus represents the overall health of the system.
type HealthStatus int

const (
	// HealthUnknown indicates health status is unknown
	HealthUnknown HealthStatus = iota
	// HealthHealthy indicates system is healthy
	HealthHealthy
	// HealthDegraded indicates system is degraded but functioning
	HealthDegraded
	// HealthUnhealthy indicates system is unhealthy
	HealthUnhealthy
)

// String returns the string representation of health status.
func (h HealthStatus) String() string {
	switch h {
	case HealthHealthy:
		return "healthy"
	case HealthDegraded:
		return "degraded"
	case HealthUnhealthy:
		return "unhealthy"
	default:
		return "unknown"
	}
}

// ComponentStatus represents the status of a system component.
type ComponentStatus struct {
	Name      string
	Status    HealthStatus
	Latency   time.Duration
	ErrorRate float64
	Metadata  map[string]string
}

// AnalysisResult represents the result of analyzing monitoring data.
type AnalysisResult struct {
	Timestamp       time.Time
	Findings        []Finding
	Severity        SeverityLevel
	Confidence      float64
	Recommendations []Recommendation
}

// SeverityLevel represents the severity of analysis findings.
type SeverityLevel int

const (
	// SeverityInfo represents informational findings
	SeverityInfo SeverityLevel = iota
	// SeverityWarning represents warning level findings
	SeverityWarning
	// SeverityCritical represents critical findings
	SeverityCritical
)

// String returns the string representation of severity level.
func (s SeverityLevel) String() string {
	switch s {
	case SeverityInfo:
		return "info"
	case SeverityWarning:
		return "warning"
	case SeverityCritical:
		return "critical"
	default:
		return "unknown"
	}
}

// Finding represents a single analysis finding.
type Finding struct {
	Type        string
	Description string
	Severity    SeverityLevel
	Component   string
	Value       float64
	Threshold   float64
}

// Recommendation represents a recommended action.
type Recommendation struct {
	Type        string
	Description string
	Priority    int
	Action      string
	Params      map[string]interface{}
}

// ActionPlan represents a plan of actions to execute.
type ActionPlan struct {
	ID        string
	Timestamp time.Time
	Actions   []Action
	Priority  int
	Timeout   time.Duration
}

// Action represents a single action in a plan.
type Action struct {
	Type       string
	Target     string
	Operation  string
	Parameters map[string]interface{}
	Rollback   func() error
}

// ExecutionResult represents the result of executing an action plan.
type ExecutionResult struct {
	PlanID    string
	Timestamp time.Time
	Success   bool
	Actions   []ActionResult
	Error     string
	Duration  time.Duration
}

// ActionResult represents the result of executing a single action.
type ActionResult struct {
	Action   Action
	Success  bool
	Error    string
	Duration time.Duration
}

// KnowledgeRecord represents a single record in the knowledge base.
type KnowledgeRecord struct {
	Key       string
	Value     interface{}
	Timestamp time.Time
	Version   int
}

// Common errors.
var (
	// ErrLoopRunning is returned when trying to start an already running loop
	ErrLoopRunning = errors.New("MAPE-K loop is already running")
	// ErrLoopNotRunning is returned when trying to stop a non-running loop
	ErrLoopNotRunning = errors.New("MAPE-K loop is not running")
	// ErrMissingComponent is returned when a required component is missing
	ErrMissingComponent = errors.New("required MAPE-K component is missing")
	// ErrExecutionFailed is returned when action execution fails
	ErrExecutionFailed = errors.New("action execution failed")
)

// NewMAPEK creates a new MAPE-K loop with default configuration.
func NewMAPEK() *MAPEKLoop {
	return &MAPEKLoop{
		interval:  30 * time.Second,
		stopCh:    make(chan struct{}),
		knowledge: NewMemoryKnowledge(),
	}
}

// WithInterval sets the control loop interval.
func (m *MAPEKLoop) WithInterval(interval time.Duration) *MAPEKLoop {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.interval = interval
	return m
}

// WithMonitor sets the monitor component.
func (m *MAPEKLoop) WithMonitor(monitor Monitor) *MAPEKLoop {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.monitor = monitor
	return m
}

// WithAnalyzer sets the analyzer component.
func (m *MAPEKLoop) WithAnalyzer(analyzer Analyzer) *MAPEKLoop {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.analyzer = analyzer
	return m
}

// WithPlanner sets the planner component.
func (m *MAPEKLoop) WithPlanner(planner Planner) *MAPEKLoop {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.planner = planner
	return m
}

// WithExecutor sets the executor component.
func (m *MAPEKLoop) WithExecutor(executor Executor) *MAPEKLoop {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.executor = executor
	return m
}

// WithKnowledge sets the knowledge component.
func (m *MAPEKLoop) WithKnowledge(knowledge Knowledge) *MAPEKLoop {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.knowledge = knowledge
	return m
}

// Start begins the MAPE-K control loop.
func (m *MAPEKLoop) Start(ctx context.Context) error {
	m.mu.Lock()

	if m.running {
		m.mu.Unlock()
		return ErrLoopRunning
	}

	// Validate required components
	if m.monitor == nil {
		m.mu.Unlock()
		return ErrMissingComponent
	}

	m.running = true
	m.stopCh = make(chan struct{})
	m.mu.Unlock()

	m.wg.Add(1)
	go m.run(ctx)

	return nil
}

// Stop halts the MAPE-K control loop.
func (m *MAPEKLoop) Stop() error {
	m.mu.Lock()

	if !m.running {
		m.mu.Unlock()
		return ErrLoopNotRunning
	}

	m.running = false
	close(m.stopCh)
	m.mu.Unlock()

	m.wg.Wait()
	return nil
}

// IsRunning returns whether the loop is currently running.
func (m *MAPEKLoop) IsRunning() bool {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.running
}

// run executes the MAPE-K loop.
func (m *MAPEKLoop) run(ctx context.Context) {
	defer m.wg.Done()

	ticker := time.NewTicker(m.interval)
	defer ticker.Stop()

	// Execute immediately on start
	m.iterate(ctx)

	for {
		select {
		case <-ctx.Done():
			return
		case <-m.stopCh:
			return
		case <-ticker.C:
			m.iterate(ctx)
		}
	}
}

// iterate performs one iteration of the MAPE-K loop.
func (m *MAPEKLoop) iterate(ctx context.Context) {
	// Monitor
	data, err := m.monitor.Collect(ctx)
	if err != nil {
		return
	}

	// Store raw metrics in knowledge
	_ = m.knowledge.Store(ctx, "last_metrics", data.Metrics)
	_ = m.knowledge.Store(ctx, "last_health", data.Health)

	// Analyze (if analyzer is configured)
	if m.analyzer == nil {
		return
	}

	result, err := m.analyzer.Analyze(ctx, data)
	if err != nil {
		return
	}

	// Store analysis in knowledge
	_ = m.knowledge.Store(ctx, "last_analysis", result)

	// Plan (if planner is configured)
	if m.planner == nil {
		return
	}

	plan, err := m.planner.Plan(ctx, result)
	if err != nil {
		return
	}

	// Skip if no actions
	if len(plan.Actions) == 0 {
		return
	}

	// Store plan in knowledge
	_ = m.knowledge.Store(ctx, "last_plan", plan)

	// Execute (if executor is configured)
	if m.executor == nil {
		return
	}

	execResult, err := m.executor.Execute(ctx, plan)
	if err != nil {
		execResult = &ExecutionResult{
			PlanID:    plan.ID,
			Success:   false,
			Error:     err.Error(),
			Timestamp: time.Now(),
		}
	}

	// Store execution result in knowledge
	_ = m.knowledge.Store(ctx, "last_execution", execResult)
}

// MemoryKnowledge implements Knowledge interface using in-memory storage.
type MemoryKnowledge struct {
	data    map[string]interface{}
	history map[string][]KnowledgeRecord
	mu      sync.RWMutex
	version int
}

// NewMemoryKnowledge creates a new in-memory knowledge base.
func NewMemoryKnowledge() *MemoryKnowledge {
	return &MemoryKnowledge{
		data:    make(map[string]interface{}),
		history: make(map[string][]KnowledgeRecord),
	}
}

// Store saves information to knowledge base.
func (m *MemoryKnowledge) Store(ctx context.Context, key string, value interface{}) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	m.version++
	m.data[key] = value

	// Add to history
	record := KnowledgeRecord{
		Key:       key,
		Value:     value,
		Timestamp: time.Now(),
		Version:   m.version,
	}
	m.history[key] = append(m.history[key], record)

	return nil
}

// Retrieve gets information from knowledge base.
func (m *MemoryKnowledge) Retrieve(ctx context.Context, key string) (interface{}, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	value, ok := m.data[key]
	if !ok {
		return nil, errors.New("key not found")
	}

	return value, nil
}

// Update updates existing information.
func (m *MemoryKnowledge) Update(ctx context.Context, key string, value interface{}) error {
	return m.Store(ctx, key, value)
}

// History returns historical data for a key.
func (m *MemoryKnowledge) History(ctx context.Context, key string, limit int) ([]KnowledgeRecord, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	history, ok := m.history[key]
	if !ok {
		return nil, nil
	}

	if limit <= 0 || limit > len(history) {
		limit = len(history)
	}

	// Return most recent records
	start := len(history) - limit
	if start < 0 {
		start = 0
	}

	result := make([]KnowledgeRecord, limit)
	copy(result, history[start:])

	return result, nil
}

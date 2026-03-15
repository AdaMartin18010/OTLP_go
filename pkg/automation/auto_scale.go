// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
//
// This file implements predictive auto-scaling based on metrics and trend analysis.
// It supports horizontal scaling (adding/removing instances) and vertical scaling
// (adjusting resource allocation per instance).
package automation

import (
	"context"
	"errors"
	"fmt"
	"math"
	"sync"
	"time"
)

// AutoScaler provides automatic scaling capabilities based on metrics and predictions.
// It supports both horizontal scaling (changing instance count) and vertical scaling
// (changing resource allocation).
type AutoScaler struct {
	knowledge Knowledge
	policies  map[string]ScalingPolicy
	metrics   *ScalingMetrics

	// Configuration
	minInstances      int
	maxInstances      int
	scaleUpCooldown   time.Duration
	scaleDownCooldown time.Duration
	predictionWindow  time.Duration
	enabled           bool

	// State
	lastScaleUp      time.Time
	lastScaleDown    time.Time
	currentInstances int
	targetInstances  int
	scalingHistory   []ScalingEvent

	mu sync.RWMutex
}

// ScalingPolicy defines scaling rules for a specific metric.
type ScalingPolicy struct {
	Name               string
	MetricKey          string
	ScaleUpThreshold   float64
	ScaleDownThreshold float64
	ScaleUpStep        int
	ScaleDownStep      int
	Priority           int
	Enabled            bool
}

// ScalingMetrics tracks scaling-related metrics.
type ScalingMetrics struct {
	CPUUtilization    float64
	MemoryUtilization float64
	RequestLatency    time.Duration
	RequestRate       float64
	ErrorRate         float64
	QueueDepth        float64
	CustomMetrics     map[string]float64
}

// ScalingEvent represents a scaling operation.
type ScalingEvent struct {
	ID        string
	Timestamp time.Time
	Type      ScalingType
	Direction ScalingDirection
	From      int
	To        int
	Reason    string
	Trigger   string
	Success   bool
	Error     string
}

// ScalingType indicates the type of scaling.
type ScalingType int

const (
	// ScalingTypeHorizontal scales by adding/removing instances
	ScalingTypeHorizontal ScalingType = iota
	// ScalingTypeVertical scales by adjusting resources per instance
	ScalingTypeVertical
)

// String returns the string representation of scaling type.
func (s ScalingType) String() string {
	switch s {
	case ScalingTypeHorizontal:
		return "horizontal"
	case ScalingTypeVertical:
		return "vertical"
	default:
		return "unknown"
	}
}

// ScalingDirection indicates the direction of scaling.
type ScalingDirection int

const (
	// ScalingDirectionUp scales up (add resources/instances)
	ScalingDirectionUp ScalingDirection = iota
	// ScalingDirectionDown scales down (remove resources/instances)
	ScalingDirectionDown
)

// String returns the string representation of scaling direction.
func (s ScalingDirection) String() string {
	switch s {
	case ScalingDirectionUp:
		return "up"
	case ScalingDirectionDown:
		return "down"
	default:
		return "unknown"
	}
}

// PredictionModel represents a predictive scaling model.
type PredictionModel interface {
	// Predict predicts future metric values
	Predict(ctx context.Context, metricKey string, history []MetricPoint, horizon time.Duration) ([]Prediction, error)
	// Name returns the model name
	Name() string
	// Confidence returns the model's confidence level (0-1)
	Confidence() float64
}

// MetricPoint represents a single metric data point.
type MetricPoint struct {
	Timestamp time.Time
	Value     float64
}

// Prediction represents a predicted future value.
type Prediction struct {
	Timestamp  time.Time
	Value      float64
	Confidence float64
	LowerBound float64
	UpperBound float64
}

// ScalingDecision represents a decision to scale.
type ScalingDecision struct {
	ShouldScale bool
	Type        ScalingType
	Direction   ScalingDirection
	Amount      int
	Reason      string
	Confidence  float64
	Timestamp   time.Time
	Trigger     string // Policy name that triggered this decision
}

// Common errors.
var (
	// ErrInvalidInstanceCount is returned when instance count is invalid
	ErrInvalidInstanceCount = errors.New("invalid instance count")
	// ErrScalingCooldown is returned when scaling is in cooldown period
	ErrScalingCooldown = errors.New("scaling is in cooldown period")
	// ErrMaxInstancesReached is returned when maximum instances reached
	ErrMaxInstancesReached = errors.New("maximum instances reached")
	// ErrMinInstancesReached is returned when minimum instances reached
	ErrMinInstancesReached = errors.New("minimum instances reached")
	// ErrPredictionFailed is returned when prediction fails
	ErrPredictionFailed = errors.New("prediction failed")
)

// NewAutoScaler creates a new auto-scaler with default configuration.
func NewAutoScaler() *AutoScaler {
	return &AutoScaler{
		knowledge:         NewMemoryKnowledge(),
		policies:          make(map[string]ScalingPolicy),
		minInstances:      1,
		maxInstances:      10,
		scaleUpCooldown:   5 * time.Minute,
		scaleDownCooldown: 10 * time.Minute,
		predictionWindow:  5 * time.Minute,
		currentInstances:  1,
		targetInstances:   1,
		enabled:           true,
		scalingHistory:    make([]ScalingEvent, 0),
	}
}

// WithKnowledge sets the knowledge base.
func (a *AutoScaler) WithKnowledge(knowledge Knowledge) *AutoScaler {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.knowledge = knowledge
	return a
}

// WithInstanceLimits sets the minimum and maximum instance limits.
func (a *AutoScaler) WithInstanceLimits(min, max int) *AutoScaler {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.minInstances = min
	a.maxInstances = max
	return a
}

// WithCooldowns sets the scaling cooldown periods.
func (a *AutoScaler) WithCooldowns(scaleUp, scaleDown time.Duration) *AutoScaler {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.scaleUpCooldown = scaleUp
	a.scaleDownCooldown = scaleDown
	return a
}

// WithPredictionWindow sets the prediction window.
func (a *AutoScaler) WithPredictionWindow(window time.Duration) *AutoScaler {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.predictionWindow = window
	return a
}

// Enable enables auto-scaling.
func (a *AutoScaler) Enable() {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.enabled = true
}

// Disable disables auto-scaling.
func (a *AutoScaler) Disable() {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.enabled = false
}

// IsEnabled returns whether auto-scaling is enabled.
func (a *AutoScaler) IsEnabled() bool {
	a.mu.RLock()
	defer a.mu.RUnlock()
	return a.enabled
}

// RegisterPolicy registers a scaling policy.
func (a *AutoScaler) RegisterPolicy(policy ScalingPolicy) error {
	a.mu.Lock()
	defer a.mu.Unlock()

	if policy.Name == "" {
		return errors.New("policy name cannot be empty")
	}

	a.policies[policy.Name] = policy
	return nil
}

// UnregisterPolicy removes a scaling policy.
func (a *AutoScaler) UnregisterPolicy(name string) {
	a.mu.Lock()
	defer a.mu.Unlock()
	delete(a.policies, name)
}

// GetPolicy returns a registered policy.
func (a *AutoScaler) GetPolicy(name string) (ScalingPolicy, bool) {
	a.mu.RLock()
	defer a.mu.RUnlock()
	policy, ok := a.policies[name]
	return policy, ok
}

// SetCurrentInstances sets the current instance count.
func (a *AutoScaler) SetCurrentInstances(count int) error {
	a.mu.Lock()
	defer a.mu.Unlock()

	if count < a.minInstances || count > a.maxInstances {
		return ErrInvalidInstanceCount
	}

	a.currentInstances = count
	return nil
}

// GetCurrentInstances returns the current instance count.
func (a *AutoScaler) GetCurrentInstances() int {
	a.mu.RLock()
	defer a.mu.RUnlock()
	return a.currentInstances
}

// GetTargetInstances returns the target instance count.
func (a *AutoScaler) GetTargetInstances() int {
	a.mu.RLock()
	defer a.mu.RUnlock()
	return a.targetInstances
}

// Evaluate evaluates metrics and returns a scaling decision.
func (a *AutoScaler) Evaluate(ctx context.Context, metrics *ScalingMetrics) (*ScalingDecision, error) {
	a.mu.RLock()
	if !a.enabled {
		a.mu.RUnlock()
		return &ScalingDecision{ShouldScale: false}, nil
	}
	policies := make(map[string]ScalingPolicy, len(a.policies))
	for k, v := range a.policies {
		policies[k] = v
	}
	currentInstances := a.currentInstances
	lastScaleUp := a.lastScaleUp
	lastScaleDown := a.lastScaleDown
	a.mu.RUnlock()

	// Build monitoring data
	monitoringData := a.buildMonitoringData(metrics)

	// Evaluate each policy
	var decisions []ScalingDecision

	for _, policy := range policies {
		if !policy.Enabled {
			continue
		}

		decision := a.evaluatePolicy(policy, monitoringData, currentInstances)
		if decision.ShouldScale {
			decisions = append(decisions, *decision)
		}
	}

	if len(decisions) == 0 {
		return &ScalingDecision{ShouldScale: false}, nil
	}

	// Select the most urgent decision
	finalDecision := a.selectDecision(decisions)

	// Check cooldowns
	now := time.Now()
	if finalDecision.Direction == ScalingDirectionUp {
		if now.Sub(lastScaleUp) < a.scaleUpCooldown {
			return &ScalingDecision{ShouldScale: false}, ErrScalingCooldown
		}
	} else {
		if now.Sub(lastScaleDown) < a.scaleDownCooldown {
			return &ScalingDecision{ShouldScale: false}, ErrScalingCooldown
		}
	}

	// Check instance limits
	newCount := currentInstances + finalDecision.Amount
	if finalDecision.Direction == ScalingDirectionUp {
		if newCount > a.maxInstances {
			finalDecision.Amount = a.maxInstances - currentInstances
			if finalDecision.Amount <= 0 {
				return &ScalingDecision{ShouldScale: false}, ErrMaxInstancesReached
			}
		}
	} else {
		if newCount < a.minInstances {
			finalDecision.Amount = currentInstances - a.minInstances
			if finalDecision.Amount <= 0 {
				return &ScalingDecision{ShouldScale: false}, ErrMinInstancesReached
			}
			finalDecision.Amount = -finalDecision.Amount
		}
	}

	return &finalDecision, nil
}

// evaluatePolicy evaluates a single scaling policy.
func (a *AutoScaler) evaluatePolicy(policy ScalingPolicy, data *MonitoringData, currentInstances int) *ScalingDecision {
	value, ok := data.Metrics[policy.MetricKey]
	if !ok {
		return &ScalingDecision{ShouldScale: false}
	}

	decision := &ScalingDecision{
		ShouldScale: false,
		Type:        ScalingTypeHorizontal,
		Timestamp:   time.Now(),
	}

	if value >= policy.ScaleUpThreshold {
		decision.ShouldScale = true
		decision.Direction = ScalingDirectionUp
		decision.Amount = policy.ScaleUpStep
		decision.Reason = fmt.Sprintf("%s metric (%.2f) exceeded scale-up threshold (%.2f)",
			policy.MetricKey, value, policy.ScaleUpThreshold)
		decision.Confidence = math.Min(1.0, value/policy.ScaleUpThreshold)
		decision.Trigger = policy.Name
	} else if value <= policy.ScaleDownThreshold {
		decision.ShouldScale = true
		decision.Direction = ScalingDirectionDown
		decision.Trigger = policy.Name
		decision.Amount = -policy.ScaleDownStep
		decision.Reason = fmt.Sprintf("%s metric (%.2f) below scale-down threshold (%.2f)",
			policy.MetricKey, value, policy.ScaleDownThreshold)
		decision.Confidence = math.Min(1.0, policy.ScaleDownThreshold/value)
	}

	return decision
}

// selectDecision selects the most urgent scaling decision.
func (a *AutoScaler) selectDecision(decisions []ScalingDecision) ScalingDecision {
	if len(decisions) == 0 {
		return ScalingDecision{ShouldScale: false}
	}

	// Prioritize scale-up over scale-down
	var bestDecision ScalingDecision
	bestPriority := -1

	for _, d := range decisions {
		policy := a.policies[d.Trigger]
		priority := policy.Priority

		if d.Direction == ScalingDirectionUp {
			priority += 100 // Boost priority for scale-up
		}

		if priority > bestPriority {
			bestPriority = priority
			bestDecision = d
		}
	}

	return bestDecision
}

// Predict performs predictive scaling based on historical data.
func (a *AutoScaler) Predict(ctx context.Context, metricKey string, model PredictionModel) (*ScalingDecision, error) {
	// Get historical data from knowledge
	history, err := a.getMetricHistory(ctx, metricKey, 100)
	if err != nil {
		return nil, err
	}

	if len(history) < 10 {
		return &ScalingDecision{ShouldScale: false}, nil
	}

	// Run prediction
	predictions, err := model.Predict(ctx, metricKey, history, a.predictionWindow)
	if err != nil {
		return nil, fmt.Errorf("%w: %v", ErrPredictionFailed, err)
	}

	if len(predictions) == 0 {
		return &ScalingDecision{ShouldScale: false}, nil
	}

	// Find the highest predicted value
	var maxPrediction Prediction
	for _, p := range predictions {
		if p.Value > maxPrediction.Value {
			maxPrediction = p
		}
	}

	// Check if predicted value triggers scaling
	a.mu.RLock()
	policies := make(map[string]ScalingPolicy, len(a.policies))
	for k, v := range a.policies {
		policies[k] = v
	}
	a.mu.RUnlock()

	for _, policy := range policies {
		if policy.MetricKey != metricKey || !policy.Enabled {
			continue
		}

		if maxPrediction.Value >= policy.ScaleUpThreshold && maxPrediction.Confidence > 0.7 {
			return &ScalingDecision{
				ShouldScale: true,
				Type:        ScalingTypeHorizontal,
				Direction:   ScalingDirectionUp,
				Amount:      policy.ScaleUpStep,
				Reason:      fmt.Sprintf("Predicted %s will reach %.2f at %s", metricKey, maxPrediction.Value, maxPrediction.Timestamp.Format(time.RFC3339)),
				Confidence:  maxPrediction.Confidence,
				Timestamp:   time.Now(),
			}, nil
		}
	}

	return &ScalingDecision{ShouldScale: false}, nil
}

// Execute executes a scaling decision.
func (a *AutoScaler) Execute(ctx context.Context, decision *ScalingDecision) (*ScalingEvent, error) {
	a.mu.Lock()
	defer a.mu.Unlock()

	if !decision.ShouldScale {
		return nil, errors.New("no scaling needed")
	}

	from := a.currentInstances
	to := from + decision.Amount

	// Ensure limits
	if to < a.minInstances {
		to = a.minInstances
	}
	if to > a.maxInstances {
		to = a.maxInstances
	}

	// Create event
	event := &ScalingEvent{
		ID:        fmt.Sprintf("scale-%d", time.Now().UnixNano()),
		Timestamp: time.Now(),
		Type:      decision.Type,
		Direction: decision.Direction,
		From:      from,
		To:        to,
		Reason:    decision.Reason,
		Trigger:   decision.Reason,
		Success:   true,
	}

	// Update state
	a.currentInstances = to
	a.targetInstances = to

	if decision.Direction == ScalingDirectionUp {
		a.lastScaleUp = time.Now()
	} else {
		a.lastScaleDown = time.Now()
	}

	// Store in history
	a.scalingHistory = append(a.scalingHistory, *event)

	// Store in knowledge
	_ = a.knowledge.Store(ctx, fmt.Sprintf("scaling_event_%s", event.ID), *event)

	return event, nil
}

// GetScalingHistory returns the scaling history.
func (a *AutoScaler) GetScalingHistory(limit int) []ScalingEvent {
	a.mu.RLock()
	defer a.mu.RUnlock()

	if limit <= 0 || limit > len(a.scalingHistory) {
		limit = len(a.scalingHistory)
	}

	start := len(a.scalingHistory) - limit
	if start < 0 {
		start = 0
	}

	result := make([]ScalingEvent, limit)
	copy(result, a.scalingHistory[start:])
	return result
}

// buildMonitoringData builds monitoring data from scaling metrics.
func (a *AutoScaler) buildMonitoringData(metrics *ScalingMetrics) *MonitoringData {
	data := &MonitoringData{
		Timestamp: time.Now(),
		Metrics: map[string]float64{
			"cpu_utilization":    metrics.CPUUtilization,
			"memory_utilization": metrics.MemoryUtilization,
			"error_rate":         metrics.ErrorRate,
			"request_rate":       metrics.RequestRate,
			"queue_depth":        metrics.QueueDepth,
		},
		Health: HealthHealthy,
	}

	// Add latency as milliseconds
	data.Metrics["request_latency_ms"] = float64(metrics.RequestLatency) / float64(time.Millisecond)

	// Add custom metrics
	for k, v := range metrics.CustomMetrics {
		data.Metrics[k] = v
	}

	// Determine health
	if metrics.ErrorRate > 0.1 || metrics.CPUUtilization > 90 {
		data.Health = HealthUnhealthy
	} else if metrics.ErrorRate > 0.05 || metrics.CPUUtilization > 75 {
		data.Health = HealthDegraded
	}

	return data
}

// getMetricHistory retrieves metric history from knowledge.
func (a *AutoScaler) getMetricHistory(ctx context.Context, metricKey string, limit int) ([]MetricPoint, error) {
	records, err := a.knowledge.History(ctx, "metrics_"+metricKey, limit)
	if err != nil {
		return nil, err
	}

	points := make([]MetricPoint, 0, len(records))
	for _, record := range records {
		if point, ok := record.Value.(MetricPoint); ok {
			points = append(points, point)
		}
	}

	return points, nil
}

// StoreMetric stores a metric value in knowledge.
func (a *AutoScaler) StoreMetric(ctx context.Context, metricKey string, value float64) error {
	point := MetricPoint{
		Timestamp: time.Now(),
		Value:     value,
	}
	return a.knowledge.Store(ctx, "metrics_"+metricKey, point)
}

// LinearPredictionModel implements a simple linear regression prediction model.
type LinearPredictionModel struct {
	confidence float64
}

// NewLinearPredictionModel creates a new linear prediction model.
func NewLinearPredictionModel() *LinearPredictionModel {
	return &LinearPredictionModel{
		confidence: 0.8,
	}
}

// Name returns the model name.
func (m *LinearPredictionModel) Name() string {
	return "linear-regression"
}

// Confidence returns the model's confidence level.
func (m *LinearPredictionModel) Confidence() float64 {
	return m.confidence
}

// Predict predicts future values using linear regression.
func (m *LinearPredictionModel) Predict(ctx context.Context, metricKey string, history []MetricPoint, horizon time.Duration) ([]Prediction, error) {
	if len(history) < 2 {
		return nil, errors.New("insufficient data for prediction")
	}

	// Calculate linear regression coefficients
	n := float64(len(history))
	var sumX, sumY, sumXY, sumX2 float64

	baseTime := history[0].Timestamp.Unix()

	for i, point := range history {
		x := float64(i)
		y := point.Value
		sumX += x
		sumY += y
		sumXY += x * y
		sumX2 += x * x
	}

	// Calculate slope and intercept
	slope := (n*sumXY - sumX*sumY) / (n*sumX2 - sumX*sumX)
	intercept := (sumY - slope*sumX) / n

	// Generate predictions
	intervals := int(horizon.Minutes())
	if intervals < 1 {
		intervals = 1
	}

	predictions := make([]Prediction, intervals)
	lastIdx := float64(len(history) - 1)

	for i := 0; i < intervals; i++ {
		x := lastIdx + float64(i+1)
		predictedValue := slope*x + intercept

		// Calculate confidence interval
		confidence := m.confidence * (1.0 - float64(i)*0.1)
		if confidence < 0.5 {
			confidence = 0.5
		}

		margin := math.Abs(predictedValue) * (1.0 - confidence)

		predictions[i] = Prediction{
			Timestamp:  time.Unix(baseTime, 0).Add(time.Duration(i+1) * time.Minute),
			Value:      predictedValue,
			Confidence: confidence,
			LowerBound: predictedValue - margin,
			UpperBound: predictedValue + margin,
		}
	}

	return predictions, nil
}

// AutoScalerExecutor implements the Executor interface for auto-scaling.
type AutoScalerExecutor struct {
	scaler *AutoScaler
}

// NewAutoScalerExecutor creates a new auto-scaler executor.
func NewAutoScalerExecutor(scaler *AutoScaler) *AutoScalerExecutor {
	return &AutoScalerExecutor{
		scaler: scaler,
	}
}

// Name returns the executor name.
func (e *AutoScalerExecutor) Name() string {
	return "auto-scaler-executor"
}

// Execute carries out the action plan.
func (e *AutoScalerExecutor) Execute(ctx context.Context, plan *ActionPlan) (*ExecutionResult, error) {
	result := &ExecutionResult{
		PlanID:    plan.ID,
		Timestamp: time.Now(),
		Success:   true,
		Actions:   make([]ActionResult, 0, len(plan.Actions)),
	}

	start := time.Now()

	for _, action := range plan.Actions {
		actionStart := time.Now()
		actionResult := ActionResult{
			Action:   action,
			Duration: time.Since(actionStart),
		}

		// Parse scaling decision from action
		decision, ok := action.Parameters["decision"].(*ScalingDecision)
		if !ok {
			actionResult.Success = false
			actionResult.Error = "invalid scaling decision"
			result.Success = false
		} else {
			event, err := e.scaler.Execute(ctx, decision)
			if err != nil {
				actionResult.Success = false
				actionResult.Error = err.Error()
				result.Success = false
			} else {
				actionResult.Success = true
				_ = event // Event is already stored by Execute
			}
		}

		result.Actions = append(result.Actions, actionResult)
	}

	result.Duration = time.Since(start)

	return result, nil
}

// AutoScalerPlanner implements the Planner interface for auto-scaling.
type AutoScalerPlanner struct {
	scaler *AutoScaler
}

// NewAutoScalerPlanner creates a new auto-scaler planner.
func NewAutoScalerPlanner(scaler *AutoScaler) *AutoScalerPlanner {
	return &AutoScalerPlanner{
		scaler: scaler,
	}
}

// Name returns the planner name.
func (p *AutoScalerPlanner) Name() string {
	return "auto-scaler-planner"
}

// Plan creates an action plan based on analysis.
func (p *AutoScalerPlanner) Plan(ctx context.Context, result *AnalysisResult) (*ActionPlan, error) {
	plan := &ActionPlan{
		ID:        fmt.Sprintf("plan-%d", time.Now().UnixNano()),
		Timestamp: time.Now(),
		Actions:   make([]Action, 0),
		Priority:  1,
		Timeout:   5 * time.Minute,
	}

	// Convert findings to scaling decisions
	for _, finding := range result.Findings {
		if finding.Severity < SeverityWarning {
			continue
		}

		var direction ScalingDirection
		var amount int

		if finding.Value > finding.Threshold {
			direction = ScalingDirectionUp
			amount = 1
		} else {
			direction = ScalingDirectionDown
			amount = -1
		}

		decision := &ScalingDecision{
			ShouldScale: true,
			Type:        ScalingTypeHorizontal,
			Direction:   direction,
			Amount:      amount,
			Reason:      finding.Description,
			Confidence:  0.8,
			Timestamp:   time.Now(),
		}

		action := Action{
			Type:      "scale",
			Target:    "auto-scaler",
			Operation: direction.String(),
			Parameters: map[string]interface{}{
				"decision": decision,
			},
		}

		plan.Actions = append(plan.Actions, action)
	}

	return plan, nil
}

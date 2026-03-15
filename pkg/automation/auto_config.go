// Package automation provides self-adaptive automation capabilities for the OTLP Go SDK.
//
// This file implements auto-configuration based on system metrics and learned patterns.
// It uses the MAPE-K loop to continuously adjust configuration parameters for optimal
// performance and resource utilization.
package automation

import (
	"context"
	"errors"
	"fmt"
	"math"
	"sync"
	"time"
)

// AutoConfig provides automatic configuration adjustment based on metrics and learned patterns.
// It implements the MAPE-K components for configuration management.
type AutoConfig struct {
	manager   ConfigManager
	knowledge Knowledge
	adjusters map[string]ConfigAdjuster
	enabled   bool
	mu        sync.RWMutex

	// Configuration parameters
	minAdjustmentInterval time.Duration
	adjustmentThreshold   float64
	maxAdjustmentPercent  float64
}

// ConfigManager manages application configuration.
type ConfigManager interface {
	// Get retrieves a configuration value
	Get(key string) (interface{}, error)
	// Set sets a configuration value
	Set(key string, value interface{}) error
	// GetInt gets an integer configuration value
	GetInt(key string) (int, error)
	// GetFloat gets a float configuration value
	GetFloat(key string) (float64, error)
	// GetDuration gets a duration configuration value
	GetDuration(key string) (time.Duration, error)
	// UpdateBatch updates multiple configuration values atomically
	UpdateBatch(updates map[string]interface{}) error
}

// ConfigAdjuster adjusts a specific configuration parameter.
type ConfigAdjuster interface {
	// Name returns the adjuster name
	Name() string
	// Key returns the configuration key this adjuster manages
	Key() string
	// Adjust calculates the new configuration value based on metrics
	Adjust(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error)
	// Validate validates a configuration value
	Validate(value interface{}) error
	// MinValue returns the minimum allowed value
	MinValue() interface{}
	// MaxValue returns the maximum allowed value
	MaxValue() interface{}
}

// ConfigChange represents a configuration change.
type ConfigChange struct {
	Key       string
	OldValue  interface{}
	NewValue  interface{}
	Reason    string
	Timestamp time.Time
	Auto      bool
}

// ConfigAdjusterFunc is a function adapter for ConfigAdjuster.
type ConfigAdjusterFunc struct {
	name     string
	key      string
	adjust   func(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error)
	validate func(value interface{}) error
	minValue interface{}
	maxValue interface{}
}

// Name returns the adjuster name.
func (f *ConfigAdjusterFunc) Name() string { return f.name }

// Key returns the configuration key.
func (f *ConfigAdjusterFunc) Key() string { return f.key }

// Adjust calculates the new configuration value.
func (f *ConfigAdjusterFunc) Adjust(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error) {
	return f.adjust(ctx, current, metrics, knowledge)
}

// Validate validates a configuration value.
func (f *ConfigAdjusterFunc) Validate(value interface{}) error {
	if f.validate != nil {
		return f.validate(value)
	}
	return nil
}

// MinValue returns the minimum allowed value.
func (f *ConfigAdjusterFunc) MinValue() interface{} { return f.minValue }

// MaxValue returns the maximum allowed value.
func (f *ConfigAdjusterFunc) MaxValue() interface{} { return f.maxValue }

// NewConfigAdjusterFunc creates a new functional config adjuster.
func NewConfigAdjusterFunc(
	name, key string,
	adjust func(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error),
	validate func(value interface{}) error,
	minValue, maxValue interface{},
) ConfigAdjuster {
	return &ConfigAdjusterFunc{
		name:     name,
		key:      key,
		adjust:   adjust,
		validate: validate,
		minValue: minValue,
		maxValue: maxValue,
	}
}

// Common errors.
var (
	// ErrConfigNotFound is returned when a configuration key is not found
	ErrConfigNotFound = errors.New("configuration not found")
	// ErrInvalidConfigValue is returned when a configuration value is invalid
	ErrInvalidConfigValue = errors.New("invalid configuration value")
	// ErrAdjustmentFailed is returned when configuration adjustment fails
	ErrAdjustmentFailed = errors.New("configuration adjustment failed")
	// ErrAdjusterNotFound is returned when an adjuster is not found
	ErrAdjusterNotFound = errors.New("config adjuster not found")
)

// NewAutoConfig creates a new auto-configuration manager.
func NewAutoConfig(manager ConfigManager) *AutoConfig {
	return &AutoConfig{
		manager:               manager,
		knowledge:             NewMemoryKnowledge(),
		adjusters:             make(map[string]ConfigAdjuster),
		minAdjustmentInterval: 30 * time.Second,
		adjustmentThreshold:   0.1, // 10% change threshold
		maxAdjustmentPercent:  0.5, // 50% max adjustment per cycle
		enabled:               true,
	}
}

// WithKnowledge sets the knowledge base.
func (a *AutoConfig) WithKnowledge(knowledge Knowledge) *AutoConfig {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.knowledge = knowledge
	return a
}

// WithMinAdjustmentInterval sets the minimum interval between adjustments.
func (a *AutoConfig) WithMinAdjustmentInterval(interval time.Duration) *AutoConfig {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.minAdjustmentInterval = interval
	return a
}

// WithAdjustmentThreshold sets the threshold for triggering adjustments.
func (a *AutoConfig) WithAdjustmentThreshold(threshold float64) *AutoConfig {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.adjustmentThreshold = threshold
	return a
}

// WithMaxAdjustmentPercent sets the maximum percentage adjustment per cycle.
func (a *AutoConfig) WithMaxAdjustmentPercent(percent float64) *AutoConfig {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.maxAdjustmentPercent = percent
	return a
}

// Enable enables auto-configuration.
func (a *AutoConfig) Enable() {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.enabled = true
}

// Disable disables auto-configuration.
func (a *AutoConfig) Disable() {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.enabled = false
}

// IsEnabled returns whether auto-configuration is enabled.
func (a *AutoConfig) IsEnabled() bool {
	a.mu.RLock()
	defer a.mu.RUnlock()
	return a.enabled
}

// RegisterAdjuster registers a configuration adjuster.
func (a *AutoConfig) RegisterAdjuster(adjuster ConfigAdjuster) error {
	a.mu.Lock()
	defer a.mu.Unlock()

	if adjuster == nil {
		return errors.New("adjuster cannot be nil")
	}

	a.adjusters[adjuster.Key()] = adjuster
	return nil
}

// UnregisterAdjuster removes a configuration adjuster.
func (a *AutoConfig) UnregisterAdjuster(key string) {
	a.mu.Lock()
	defer a.mu.Unlock()
	delete(a.adjusters, key)
}

// GetAdjuster returns a registered adjuster.
func (a *AutoConfig) GetAdjuster(key string) (ConfigAdjuster, bool) {
	a.mu.RLock()
	defer a.mu.RUnlock()
	adjuster, ok := a.adjusters[key]
	return adjuster, ok
}

// Adjust performs configuration adjustment for all registered adjusters.
func (a *AutoConfig) Adjust(ctx context.Context, metrics *MonitoringData) ([]ConfigChange, error) {
	a.mu.RLock()
	if !a.enabled {
		a.mu.RUnlock()
		return nil, nil
	}
	adjusters := make(map[string]ConfigAdjuster, len(a.adjusters))
	for k, v := range a.adjusters {
		adjusters[k] = v
	}
	a.mu.RUnlock()

	var changes []ConfigChange

	for key, adjuster := range adjusters {
		change, err := a.adjustConfig(ctx, key, adjuster, metrics)
		if err != nil {
			continue
		}
		if change != nil {
			changes = append(changes, *change)
		}
	}

	return changes, nil
}

// adjustConfig adjusts a single configuration parameter.
func (a *AutoConfig) adjustConfig(ctx context.Context, key string, adjuster ConfigAdjuster, metrics *MonitoringData) (*ConfigChange, error) {
	// Get current value
	current, err := a.manager.Get(key)
	if err != nil {
		return nil, fmt.Errorf("failed to get current value for %s: %w", key, err)
	}

	// Calculate new value
	newValue, err := adjuster.Adjust(ctx, current, metrics, a.knowledge)
	if err != nil {
		return nil, fmt.Errorf("adjustment calculation failed for %s: %w", key, err)
	}

	// Validate new value
	if err := adjuster.Validate(newValue); err != nil {
		return nil, fmt.Errorf("validation failed for %s: %w", key, err)
	}

	// Check if adjustment is significant
	if !a.isSignificantChange(current, newValue) {
		return nil, nil
	}

	// Apply the change
	if err := a.manager.Set(key, newValue); err != nil {
		return nil, fmt.Errorf("failed to apply change for %s: %w", key, err)
	}

	// Record the change
	change := ConfigChange{
		Key:       key,
		OldValue:  current,
		NewValue:  newValue,
		Timestamp: time.Now(),
		Auto:      true,
		Reason:    fmt.Sprintf("Adjusted based on metric trends (adjuster: %s)", adjuster.Name()),
	}

	// Store in knowledge
	_ = a.knowledge.Store(ctx, fmt.Sprintf("config_change_%s", key), change)

	return &change, nil
}

// isSignificantChange determines if a change is significant enough to apply.
func (a *AutoConfig) isSignificantChange(old, new interface{}) bool {
	switch o := old.(type) {
	case int:
		n, ok := new.(int)
		if !ok {
			return true
		}
		if o == 0 {
			return n != 0
		}
		change := math.Abs(float64(n-o)) / float64(o)
		return change >= a.adjustmentThreshold

	case int64:
		n, ok := new.(int64)
		if !ok {
			return true
		}
		if o == 0 {
			return n != 0
		}
		change := math.Abs(float64(n-o)) / float64(o)
		return change >= a.adjustmentThreshold

	case float64:
		n, ok := new.(float64)
		if !ok {
			return true
		}
		if o == 0 {
			return n != 0
		}
		change := math.Abs(n-o) / o
		return change >= a.adjustmentThreshold

	case time.Duration:
		n, ok := new.(time.Duration)
		if !ok {
			return true
		}
		if o == 0 {
			return n != 0
		}
		change := math.Abs(float64(n-o)) / float64(o)
		return change >= a.adjustmentThreshold

	default:
		// For other types, any change is significant
		return old != new
	}
}

// GetAdjustmentHistory returns the history of adjustments for a key.
func (a *AutoConfig) GetAdjustmentHistory(ctx context.Context, key string, limit int) ([]ConfigChange, error) {
	records, err := a.knowledge.History(ctx, fmt.Sprintf("config_change_%s", key), limit)
	if err != nil {
		return nil, err
	}

	changes := make([]ConfigChange, 0, len(records))
	for _, record := range records {
		if change, ok := record.Value.(ConfigChange); ok {
			changes = append(changes, change)
		}
	}

	return changes, nil
}

// ConfigAdjuster implementations

// IntRangeAdjuster adjusts integer values within a range.
type IntRangeAdjuster struct {
	name        string
	key         string
	minVal      int
	maxVal      int
	defaultVal  int
	metricKey   string
	targetValue float64
	scaleFactor float64
}

// NewIntRangeAdjuster creates a new integer range adjuster.
func NewIntRangeAdjuster(name, key, metricKey string, minVal, maxVal, defaultVal int, targetValue, scaleFactor float64) *IntRangeAdjuster {
	return &IntRangeAdjuster{
		name:        name,
		key:         key,
		minVal:      minVal,
		maxVal:      maxVal,
		defaultVal:  defaultVal,
		metricKey:   metricKey,
		targetValue: targetValue,
		scaleFactor: scaleFactor,
	}
}

// Name returns the adjuster name.
func (a *IntRangeAdjuster) Name() string { return a.name }

// Key returns the configuration key.
func (a *IntRangeAdjuster) Key() string { return a.key }

// MinValue returns the minimum allowed value.
func (a *IntRangeAdjuster) MinValue() interface{} { return a.minVal }

// MaxValue returns the maximum allowed value.
func (a *IntRangeAdjuster) MaxValue() interface{} { return a.maxVal }

// Adjust calculates the new configuration value.
func (a *IntRangeAdjuster) Adjust(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error) {
	currentVal, ok := current.(int)
	if !ok {
		currentVal = a.defaultVal
	}

	// Get metric value
	metricValue, ok := metrics.Metrics[a.metricKey]
	if !ok {
		return currentVal, nil
	}

	// Calculate adjustment
	diff := metricValue - a.targetValue
	adjustment := int(diff * a.scaleFactor)

	newVal := currentVal + adjustment

	// Clamp to range
	if newVal < a.minVal {
		newVal = a.minVal
	}
	if newVal > a.maxVal {
		newVal = a.maxVal
	}

	return newVal, nil
}

// Validate validates the configuration value.
func (a *IntRangeAdjuster) Validate(value interface{}) error {
	v, ok := value.(int)
	if !ok {
		return ErrInvalidConfigValue
	}
	if v < a.minVal || v > a.maxVal {
		return fmt.Errorf("value %d out of range [%d, %d]", v, a.minVal, a.maxVal)
	}
	return nil
}

// DurationRangeAdjuster adjusts duration values within a range.
type DurationRangeAdjuster struct {
	name        string
	key         string
	minVal      time.Duration
	maxVal      time.Duration
	defaultVal  time.Duration
	metricKey   string
	targetValue float64
	scaleFactor time.Duration
}

// NewDurationRangeAdjuster creates a new duration range adjuster.
func NewDurationRangeAdjuster(name, key, metricKey string, minVal, maxVal, defaultVal time.Duration, targetValue float64, scaleFactor time.Duration) *DurationRangeAdjuster {
	return &DurationRangeAdjuster{
		name:        name,
		key:         key,
		minVal:      minVal,
		maxVal:      maxVal,
		defaultVal:  defaultVal,
		metricKey:   metricKey,
		targetValue: targetValue,
		scaleFactor: scaleFactor,
	}
}

// Name returns the adjuster name.
func (a *DurationRangeAdjuster) Name() string { return a.name }

// Key returns the configuration key.
func (a *DurationRangeAdjuster) Key() string { return a.key }

// MinValue returns the minimum allowed value.
func (a *DurationRangeAdjuster) MinValue() interface{} { return a.minVal }

// MaxValue returns the maximum allowed value.
func (a *DurationRangeAdjuster) MaxValue() interface{} { return a.maxVal }

// Adjust calculates the new configuration value.
func (a *DurationRangeAdjuster) Adjust(ctx context.Context, current interface{}, metrics *MonitoringData, knowledge Knowledge) (interface{}, error) {
	currentVal, ok := current.(time.Duration)
	if !ok {
		currentVal = a.defaultVal
	}

	// Get metric value
	metricValue, ok := metrics.Metrics[a.metricKey]
	if !ok {
		return currentVal, nil
	}

	// Calculate adjustment
	diff := metricValue - a.targetValue
	adjustment := time.Duration(diff) * a.scaleFactor

	newVal := currentVal + adjustment

	// Clamp to range
	if newVal < a.minVal {
		newVal = a.minVal
	}
	if newVal > a.maxVal {
		newVal = a.maxVal
	}

	return newVal, nil
}

// Validate validates the configuration value.
func (a *DurationRangeAdjuster) Validate(value interface{}) error {
	v, ok := value.(time.Duration)
	if !ok {
		return ErrInvalidConfigValue
	}
	if v < a.minVal || v > a.maxVal {
		return fmt.Errorf("value %v out of range [%v, %v]", v, a.minVal, a.maxVal)
	}
	return nil
}

// AutoConfigMonitor implements the Monitor interface for auto-configuration.
type AutoConfigMonitor struct {
	collectors []MetricCollector
}

// MetricCollector collects specific metrics.
type MetricCollector interface {
	Collect(ctx context.Context) (map[string]float64, error)
	Name() string
}

// NewAutoConfigMonitor creates a new auto-configuration monitor.
func NewAutoConfigMonitor() *AutoConfigMonitor {
	return &AutoConfigMonitor{
		collectors: make([]MetricCollector, 0),
	}
}

// AddCollector adds a metric collector.
func (m *AutoConfigMonitor) AddCollector(collector MetricCollector) {
	m.collectors = append(m.collectors, collector)
}

// Name returns the monitor name.
func (m *AutoConfigMonitor) Name() string {
	return "auto-config-monitor"
}

// Collect gathers monitoring data.
func (m *AutoConfigMonitor) Collect(ctx context.Context) (*MonitoringData, error) {
	data := &MonitoringData{
		Timestamp:  time.Now(),
		Metrics:    make(map[string]float64),
		Attributes: make(map[string]string),
		Health:     HealthHealthy,
	}

	for _, collector := range m.collectors {
		metrics, err := collector.Collect(ctx)
		if err != nil {
			continue
		}
		for k, v := range metrics {
			data.Metrics[k] = v
		}
	}

	return data, nil
}

// AutoConfigAnalyzer implements the Analyzer interface for auto-configuration.
type AutoConfigAnalyzer struct {
	thresholds map[string]ThresholdConfig
}

// ThresholdConfig defines thresholds for metric analysis.
type ThresholdConfig struct {
	Warning  float64
	Critical float64
	Target   float64
}

// NewAutoConfigAnalyzer creates a new auto-configuration analyzer.
func NewAutoConfigAnalyzer() *AutoConfigAnalyzer {
	return &AutoConfigAnalyzer{
		thresholds: make(map[string]ThresholdConfig),
	}
}

// SetThreshold sets the threshold for a metric.
func (a *AutoConfigAnalyzer) SetThreshold(metric string, config ThresholdConfig) {
	a.thresholds[metric] = config
}

// Name returns the analyzer name.
func (a *AutoConfigAnalyzer) Name() string {
	return "auto-config-analyzer"
}

// Analyze processes monitoring data.
func (a *AutoConfigAnalyzer) Analyze(ctx context.Context, data *MonitoringData) (*AnalysisResult, error) {
	result := &AnalysisResult{
		Timestamp: time.Now(),
		Findings:  make([]Finding, 0),
		Severity:  SeverityInfo,
	}

	for metric, value := range data.Metrics {
		threshold, ok := a.thresholds[metric]
		if !ok {
			continue
		}

		finding := Finding{
			Type:      "metric_threshold",
			Component: metric,
			Value:     value,
			Threshold: threshold.Target,
		}

		if value >= threshold.Critical {
			finding.Severity = SeverityCritical
			finding.Description = fmt.Sprintf("Metric %s is at critical level: %.2f (threshold: %.2f)", metric, value, threshold.Critical)
			if result.Severity < SeverityCritical {
				result.Severity = SeverityCritical
			}
		} else if value >= threshold.Warning {
			finding.Severity = SeverityWarning
			finding.Description = fmt.Sprintf("Metric %s is at warning level: %.2f (threshold: %.2f)", metric, value, threshold.Warning)
			if result.Severity < SeverityWarning {
				result.Severity = SeverityWarning
			}
		} else {
			finding.Severity = SeverityInfo
			finding.Description = fmt.Sprintf("Metric %s is normal: %.2f", metric, value)
		}

		result.Findings = append(result.Findings, finding)
	}

	return result, nil
}

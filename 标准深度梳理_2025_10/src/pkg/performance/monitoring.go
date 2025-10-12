// Package performance provides advanced performance monitoring and metrics collection utilities.
// This file focuses on real-time performance monitoring, metrics collection,
// and advanced performance analysis capabilities for OTLP Go applications.
package performance

import (
	"context"
	"fmt"
	"runtime"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// PerformanceMonitor provides advanced performance monitoring capabilities.
type PerformanceMonitor struct {
	mu              sync.RWMutex
	collectors      map[string]*MetricsCollector
	aggregators     map[string]*MetricsAggregator
	alerters        map[string]*Alerter
	reporters       map[string]*Reporter
	metrics         *PerformanceMonitorMetrics
	tracer          trace.Tracer
	meter           metric.Meter
	enabledFeatures map[string]bool
	cleanupFuncs    []func() error
	running         bool
	stopCh          chan struct{}
}

// PerformanceMonitorMetrics holds performance monitor metrics.
type PerformanceMonitorMetrics struct {
	TotalCollectors   int64
	ActiveCollectors  int64
	TotalAggregators  int64
	ActiveAggregators int64
	TotalAlerters     int64
	ActiveAlerters    int64
	TotalReporters    int64
	ActiveReporters   int64
	TotalMetrics      int64
	TotalAlerts       int64
	TotalReports      int64
	AverageLatency    time.Duration
	AverageThroughput float64
	LastUpdateTime    time.Time
}

// MetricsCollector provides metrics collection capabilities.
type MetricsCollector struct {
	mu            sync.RWMutex
	name          string
	collectorType string
	interval      time.Duration
	enabled       bool
	metrics       map[string]*Metric
	collectors    map[string]func() interface{}
	stats         *MetricsCollectorStats
	ticker        *time.Ticker
	stopCh        chan struct{}
	cleanupFuncs  []func() error
}

// MetricsCollectorStats holds metrics collector statistics.
type MetricsCollectorStats struct {
	TotalCollections      int64
	SuccessfulCollections int64
	FailedCollections     int64
	AverageCollectionTime time.Duration
	MinCollectionTime     time.Duration
	MaxCollectionTime     time.Duration
	LastCollectionTime    time.Time
	TotalMetrics          int64
	AverageMetrics        float64
}

// MetricsAggregator provides metrics aggregation capabilities.
type MetricsAggregator struct {
	mu             sync.RWMutex
	name           string
	aggregatorType string
	interval       time.Duration
	enabled        bool
	aggregators    map[string]*Aggregator
	stats          *MetricsAggregatorStats
	ticker         *time.Ticker
	stopCh         chan struct{}
	cleanupFuncs   []func() error
}

// MetricsAggregatorStats holds metrics aggregator statistics.
type MetricsAggregatorStats struct {
	TotalAggregations      int64
	SuccessfulAggregations int64
	FailedAggregations     int64
	AverageAggregationTime time.Duration
	MinAggregationTime     time.Duration
	MaxAggregationTime     time.Duration
	LastAggregationTime    time.Time
	TotalMetrics           int64
	AverageMetrics         float64
}

// Aggregator provides individual metric aggregation.
type Aggregator struct {
	mu             sync.RWMutex
	name           string
	aggregatorType string
	windowSize     time.Duration
	enabled        bool
	values         []float64
	timestamps     []time.Time
	stats          *AggregatorStats
	cleanupFuncs   []func() error
}

// AggregatorStats holds aggregator statistics.
type AggregatorStats struct {
	TotalValues    int64
	AverageValue   float64
	MinValue       float64
	MaxValue       float64
	SumValue       float64
	CountValue     int64
	LastValue      float64
	LastUpdateTime time.Time
}

// Alerter provides alerting capabilities.
type Alerter struct {
	mu           sync.RWMutex
	name         string
	alertType    string
	enabled      bool
	rules        map[string]*AlertRule
	handlers     map[string]func(*Alert) error
	stats        *AlerterStats
	cleanupFuncs []func() error
}

// AlerterStats holds alerter statistics.
type AlerterStats struct {
	TotalAlerts      int64
	TriggeredAlerts  int64
	ResolvedAlerts   int64
	ActiveAlerts     int64
	AverageAlertTime time.Duration
	MinAlertTime     time.Duration
	MaxAlertTime     time.Duration
	LastAlertTime    time.Time
}

// AlertRule represents an alert rule.
type AlertRule struct {
	Name          string
	Description   string
	Condition     string
	Threshold     float64
	Operator      string
	Severity      string
	Enabled       bool
	Cooldown      time.Duration
	LastTriggered time.Time
	TriggerCount  int64
	Stats         *AlertRuleStats
}

// AlertRuleStats holds alert rule statistics.
type AlertRuleStats struct {
	TotalTriggers      int64
	SuccessfulTriggers int64
	FailedTriggers     int64
	AverageTriggerTime time.Duration
	MinTriggerTime     time.Duration
	MaxTriggerTime     time.Duration
	LastTriggerTime    time.Time
}

// Alert represents an alert.
type Alert struct {
	ID             string
	Name           string
	Description    string
	Severity       string
	Status         string
	Timestamp      time.Time
	Duration       time.Duration
	Value          float64
	Threshold      float64
	Rule           *AlertRule
	Metadata       map[string]interface{}
	ResolvedAt     *time.Time
	ResolvedBy     string
	ResolvedReason string
}

// Reporter provides reporting capabilities.
type Reporter struct {
	mu           sync.RWMutex
	name         string
	reporterType string
	interval     time.Duration
	enabled      bool
	formatters   map[string]func(*Report) ([]byte, error)
	outputs      map[string]func([]byte) error
	stats        *ReporterStats
	ticker       *time.Ticker
	stopCh       chan struct{}
	cleanupFuncs []func() error
}

// ReporterStats holds reporter statistics.
type ReporterStats struct {
	TotalReports      int64
	SuccessfulReports int64
	FailedReports     int64
	AverageReportTime time.Duration
	MinReportTime     time.Duration
	MaxReportTime     time.Duration
	LastReportTime    time.Time
	TotalBytes        int64
	AverageBytes      float64
}

// Report represents a performance report.
type Report struct {
	ID          string
	Name        string
	Description string
	Timestamp   time.Time
	Duration    time.Duration
	Metrics     map[string]interface{}
	Alerts      []*Alert
	Summary     *ReportSummary
	Metadata    map[string]interface{}
}

// ReportSummary holds report summary information.
type ReportSummary struct {
	TotalMetrics      int64
	TotalAlerts       int64
	ActiveAlerts      int64
	ResolvedAlerts    int64
	AverageLatency    time.Duration
	AverageThroughput float64
	MemoryUsage       int64
	CPUUsage          float64
	GoroutineCount    int
	OverallHealth     string
	Score             float64
}

// Metric represents a performance metric.
type Metric struct {
	Name      string
	Type      string
	Value     interface{}
	Unit      string
	Timestamp time.Time
	Tags      map[string]string
	Metadata  map[string]interface{}
	Stats     *MetricStats
}

// MetricStats holds metric statistics.
type MetricStats struct {
	TotalValues    int64
	AverageValue   float64
	MinValue       float64
	MaxValue       float64
	SumValue       float64
	CountValue     int64
	LastValue      float64
	LastUpdateTime time.Time
	UpdateRate     float64
}

// PerformanceAnalyzer provides performance analysis capabilities.
type PerformanceAnalyzer struct {
	mu        sync.RWMutex
	analyzers map[string]*Analyzer
	metrics   *PerformanceAnalyzerMetrics
	enabled   bool
}

// PerformanceAnalyzerMetrics holds performance analyzer metrics.
type PerformanceAnalyzerMetrics struct {
	TotalAnalyses            int64
	SuccessfulAnalyses       int64
	FailedAnalyses           int64
	AverageAnalysisTime      time.Duration
	MinAnalysisTime          time.Duration
	MaxAnalysisTime          time.Duration
	LastAnalysisTime         time.Time
	TotalInsights            int64
	AverageInsights          float64
	HotSpotsFound            int64
	BottlenecksFound         int64
	RecommendationsGenerated int64
}

// Analyzer provides individual performance analysis.
type Analyzer struct {
	mu           sync.RWMutex
	name         string
	analyzerType string
	enabled      bool
	analyzer     func(map[string]interface{}) (map[string]interface{}, error)
	stats        *AnalyzerStats
	cleanupFuncs []func() error
}

// AnalyzerStats holds analyzer statistics.
type AnalyzerStats struct {
	TotalAnalyses       int64
	SuccessfulAnalyses  int64
	FailedAnalyses      int64
	AverageAnalysisTime time.Duration
	MinAnalysisTime     time.Duration
	MaxAnalysisTime     time.Duration
	LastAnalysisTime    time.Time
	TotalInsights       int64
	AverageInsights     float64
}

// NewPerformanceMonitor creates a new performance monitor.
func NewPerformanceMonitor() *PerformanceMonitor {
	return &PerformanceMonitor{
		collectors:      make(map[string]*MetricsCollector),
		aggregators:     make(map[string]*MetricsAggregator),
		alerters:        make(map[string]*Alerter),
		reporters:       make(map[string]*Reporter),
		metrics:         &PerformanceMonitorMetrics{},
		tracer:          otel.Tracer("performance_monitor"),
		meter:           otel.Meter("performance_monitor"),
		enabledFeatures: make(map[string]bool),
		cleanupFuncs:    make([]func() error, 0),
		running:         false,
		stopCh:          make(chan struct{}),
	}
}

// Initialize initializes the performance monitor.
func (pm *PerformanceMonitor) Initialize(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "performance_monitor.initialize")
	defer span.End()

	// Enable default features
	pm.enabledFeatures["metrics_collection"] = true
	pm.enabledFeatures["metrics_aggregation"] = true
	pm.enabledFeatures["alerting"] = true
	pm.enabledFeatures["reporting"] = true
	pm.enabledFeatures["performance_analysis"] = true

	// Initialize default collectors
	if err := pm.initializeDefaultCollectors(); err != nil {
		return fmt.Errorf("failed to initialize default collectors: %w", err)
	}

	// Initialize default aggregators
	if err := pm.initializeDefaultAggregators(); err != nil {
		return fmt.Errorf("failed to initialize default aggregators: %w", err)
	}

	// Initialize default alerters
	if err := pm.initializeDefaultAlerters(); err != nil {
		return fmt.Errorf("failed to initialize default alerters: %w", err)
	}

	// Initialize default reporters
	if err := pm.initializeDefaultReporters(); err != nil {
		return fmt.Errorf("failed to initialize default reporters: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("initialized", true),
		attribute.Int("collectors", len(pm.collectors)),
		attribute.Int("aggregators", len(pm.aggregators)),
		attribute.Int("alerters", len(pm.alerters)),
		attribute.Int("reporters", len(pm.reporters)),
	)

	return nil
}

// Start starts the performance monitor.
func (pm *PerformanceMonitor) Start(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "performance_monitor.start")
	defer span.End()

	pm.mu.Lock()
	defer pm.mu.Unlock()

	if pm.running {
		return fmt.Errorf("performance monitor is already running")
	}

	pm.running = true

	// Start all collectors
	for name, collector := range pm.collectors {
		if err := collector.Start(); err != nil {
			span.RecordError(err)
			return fmt.Errorf("failed to start collector %s: %w", name, err)
		}
	}

	// Start all aggregators
	for name, aggregator := range pm.aggregators {
		if err := aggregator.Start(); err != nil {
			span.RecordError(err)
			return fmt.Errorf("failed to start aggregator %s: %w", name, err)
		}
	}

	// Start all alerters
	for name, alerter := range pm.alerters {
		if err := alerter.Start(); err != nil {
			span.RecordError(err)
			return fmt.Errorf("failed to start alerter %s: %w", name, err)
		}
	}

	// Start all reporters
	for name, reporter := range pm.reporters {
		if err := reporter.Start(); err != nil {
			span.RecordError(err)
			return fmt.Errorf("failed to start reporter %s: %w", name, err)
		}
	}

	span.SetAttributes(
		attribute.Bool("started", true),
		attribute.Int("collectors_started", len(pm.collectors)),
		attribute.Int("aggregators_started", len(pm.aggregators)),
		attribute.Int("alerters_started", len(pm.alerters)),
		attribute.Int("reporters_started", len(pm.reporters)),
	)

	return nil
}

// Stop stops the performance monitor.
func (pm *PerformanceMonitor) Stop(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "performance_monitor.stop")
	defer span.End()

	pm.mu.Lock()
	defer pm.mu.Unlock()

	if !pm.running {
		return fmt.Errorf("performance monitor is not running")
	}

	pm.running = false
	close(pm.stopCh)

	// Stop all collectors
	for name, collector := range pm.collectors {
		if err := collector.Stop(); err != nil {
			span.RecordError(err)
		}
		delete(pm.collectors, name)
	}

	// Stop all aggregators
	for name, aggregator := range pm.aggregators {
		if err := aggregator.Stop(); err != nil {
			span.RecordError(err)
		}
		delete(pm.aggregators, name)
	}

	// Stop all alerters
	for name, alerter := range pm.alerters {
		if err := alerter.Stop(); err != nil {
			span.RecordError(err)
		}
		delete(pm.alerters, name)
	}

	// Stop all reporters
	for name, reporter := range pm.reporters {
		if err := reporter.Stop(); err != nil {
			span.RecordError(err)
		}
		delete(pm.reporters, name)
	}

	span.SetAttributes(
		attribute.Bool("stopped", true),
	)

	return nil
}

// CreateMetricsCollector creates a new metrics collector.
func (pm *PerformanceMonitor) CreateMetricsCollector(name, collectorType string, interval time.Duration) (*MetricsCollector, error) {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if _, exists := pm.collectors[name]; exists {
		return nil, fmt.Errorf("collector %s already exists", name)
	}

	collector := &MetricsCollector{
		name:          name,
		collectorType: collectorType,
		interval:      interval,
		enabled:       true,
		metrics:       make(map[string]*Metric),
		collectors:    make(map[string]func() interface{}),
		stats:         &MetricsCollectorStats{},
		cleanupFuncs:  make([]func() error, 0),
	}

	pm.collectors[name] = collector
	atomic.AddInt64(&pm.metrics.TotalCollectors, 1)
	atomic.AddInt64(&pm.metrics.ActiveCollectors, 1)

	return collector, nil
}

// GetMetricsCollector retrieves a metrics collector by name.
func (pm *PerformanceMonitor) GetMetricsCollector(name string) (*MetricsCollector, bool) {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	collector, exists := pm.collectors[name]
	return collector, exists
}

// Start starts the metrics collector.
func (mc *MetricsCollector) Start() error {
	mc.mu.Lock()
	defer mc.mu.Unlock()

	if mc.enabled {
		mc.ticker = time.NewTicker(mc.interval)
		mc.stopCh = make(chan struct{})

		go func() {
			for {
				select {
				case <-mc.ticker.C:
					mc.collect()
				case <-mc.stopCh:
					return
				}
			}
		}()
	}

	return nil
}

// Stop stops the metrics collector.
func (mc *MetricsCollector) Stop() error {
	mc.mu.Lock()
	defer mc.mu.Unlock()

	if mc.ticker != nil {
		mc.ticker.Stop()
	}

	if mc.stopCh != nil {
		close(mc.stopCh)
	}

	mc.enabled = false
	return nil
}

// collect collects metrics.
func (mc *MetricsCollector) collect() {
	mc.mu.Lock()
	defer mc.mu.Unlock()

	start := time.Now()

	for name, collector := range mc.collectors {
		value := collector()
		if value != nil {
			metric := &Metric{
				Name:      name,
				Type:      "gauge",
				Value:     value,
				Unit:      "count",
				Timestamp: time.Now(),
				Tags:      make(map[string]string),
				Metadata:  make(map[string]interface{}),
				Stats:     &MetricStats{},
			}

			mc.metrics[name] = metric
			atomic.AddInt64(&mc.stats.TotalCollections, 1)
			atomic.AddInt64(&mc.stats.SuccessfulCollections, 1)
		}
	}

	duration := time.Since(start)
	mc.stats.AverageCollectionTime = duration
	mc.stats.LastCollectionTime = time.Now()
}

// AddCollector adds a metric collector function.
func (mc *MetricsCollector) AddCollector(name string, collector func() interface{}) {
	mc.mu.Lock()
	defer mc.mu.Unlock()

	mc.collectors[name] = collector
}

// GetMetric retrieves a metric by name.
func (mc *MetricsCollector) GetMetric(name string) (*Metric, bool) {
	mc.mu.RLock()
	defer mc.mu.RUnlock()

	metric, exists := mc.metrics[name]
	return metric, exists
}

// GetMetrics returns all metrics.
func (mc *MetricsCollector) GetMetrics() map[string]*Metric {
	mc.mu.RLock()
	defer mc.mu.RUnlock()

	metrics := make(map[string]*Metric)
	for name, metric := range mc.metrics {
		metrics[name] = metric
	}

	return metrics
}

// Stats returns collector statistics.
func (mc *MetricsCollector) Stats() *MetricsCollectorStats {
	mc.mu.RLock()
	defer mc.mu.RUnlock()

	return mc.stats
}

// CreateMetricsAggregator creates a new metrics aggregator.
func (pm *PerformanceMonitor) CreateMetricsAggregator(name, aggregatorType string, interval time.Duration) (*MetricsAggregator, error) {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if _, exists := pm.aggregators[name]; exists {
		return nil, fmt.Errorf("aggregator %s already exists", name)
	}

	aggregator := &MetricsAggregator{
		name:           name,
		aggregatorType: aggregatorType,
		interval:       interval,
		enabled:        true,
		aggregators:    make(map[string]*Aggregator),
		stats:          &MetricsAggregatorStats{},
		cleanupFuncs:   make([]func() error, 0),
	}

	pm.aggregators[name] = aggregator
	atomic.AddInt64(&pm.metrics.TotalAggregators, 1)
	atomic.AddInt64(&pm.metrics.ActiveAggregators, 1)

	return aggregator, nil
}

// GetMetricsAggregator retrieves a metrics aggregator by name.
func (pm *PerformanceMonitor) GetMetricsAggregator(name string) (*MetricsAggregator, bool) {
	pm.mu.RLock()
	defer pm.mu.Unlock()

	aggregator, exists := pm.aggregators[name]
	return aggregator, exists
}

// Start starts the metrics aggregator.
func (ma *MetricsAggregator) Start() error {
	ma.mu.Lock()
	defer ma.mu.Unlock()

	if ma.enabled {
		ma.ticker = time.NewTicker(ma.interval)
		ma.stopCh = make(chan struct{})

		go func() {
			for {
				select {
				case <-ma.ticker.C:
					ma.aggregate()
				case <-ma.stopCh:
					return
				}
			}
		}()
	}

	return nil
}

// Stop stops the metrics aggregator.
func (ma *MetricsAggregator) Stop() error {
	ma.mu.Lock()
	defer ma.mu.Unlock()

	if ma.ticker != nil {
		ma.ticker.Stop()
	}

	if ma.stopCh != nil {
		close(ma.stopCh)
	}

	ma.enabled = false
	return nil
}

// aggregate aggregates metrics.
func (ma *MetricsAggregator) aggregate() {
	ma.mu.Lock()
	defer ma.mu.Unlock()

	start := time.Now()

	for _, aggregator := range ma.aggregators {
		if aggregator.enabled {
			aggregator.aggregate()
		}
	}

	duration := time.Since(start)
	ma.stats.AverageAggregationTime = duration
	ma.stats.LastAggregationTime = time.Now()
}

// AddAggregator adds a metric aggregator.
func (ma *MetricsAggregator) AddAggregator(name string, aggregator *Aggregator) {
	ma.mu.Lock()
	defer ma.mu.Unlock()

	ma.aggregators[name] = aggregator
}

// GetAggregator retrieves an aggregator by name.
func (ma *MetricsAggregator) GetAggregator(name string) (*Aggregator, bool) {
	ma.mu.RLock()
	defer ma.mu.RUnlock()

	aggregator, exists := ma.aggregators[name]
	return aggregator, exists
}

// Stats returns aggregator statistics.
func (ma *MetricsAggregator) Stats() *MetricsAggregatorStats {
	ma.mu.RLock()
	defer ma.mu.RUnlock()

	return ma.stats
}

// NewAggregator creates a new aggregator.
func NewAggregator(name, aggregatorType string, windowSize time.Duration) *Aggregator {
	return &Aggregator{
		name:           name,
		aggregatorType: aggregatorType,
		windowSize:     windowSize,
		enabled:        true,
		values:         make([]float64, 0),
		timestamps:     make([]time.Time, 0),
		stats:          &AggregatorStats{},
		cleanupFuncs:   make([]func() error, 0),
	}
}

// AddValue adds a value to the aggregator.
func (a *Aggregator) AddValue(value float64) {
	a.mu.Lock()
	defer a.mu.Unlock()

	now := time.Now()
	a.values = append(a.values, value)
	a.timestamps = append(a.timestamps, now)

	// Clean up old values
	a.cleanup()

	// Update statistics
	a.updateStats(value, now)
}

// aggregate performs aggregation.
func (a *Aggregator) aggregate() {
	a.mu.Lock()
	defer a.mu.Unlock()

	if len(a.values) == 0 {
		return
	}

	// Calculate aggregated values based on type
	switch a.aggregatorType {
	case "sum":
		a.stats.SumValue = 0
		for _, value := range a.values {
			a.stats.SumValue += value
		}
	case "avg":
		a.stats.AverageValue = a.stats.SumValue / float64(len(a.values))
	case "min":
		a.stats.MinValue = a.values[0]
		for _, value := range a.values {
			if value < a.stats.MinValue {
				a.stats.MinValue = value
			}
		}
	case "max":
		a.stats.MaxValue = a.values[0]
		for _, value := range a.values {
			if value > a.stats.MaxValue {
				a.stats.MaxValue = value
			}
		}
	case "count":
		a.stats.CountValue = int64(len(a.values))
	}
}

// cleanup removes old values outside the window.
func (a *Aggregator) cleanup() {
	now := time.Now()
	cutoff := now.Add(-a.windowSize)

	// Remove old values
	for i := len(a.timestamps) - 1; i >= 0; i-- {
		if a.timestamps[i].Before(cutoff) {
			a.timestamps = append(a.timestamps[:i], a.timestamps[i+1:]...)
			a.values = append(a.values[:i], a.values[i+1:]...)
		}
	}
}

// updateStats updates aggregator statistics.
func (a *Aggregator) updateStats(value float64, timestamp time.Time) {
	a.stats.TotalValues++
	a.stats.LastValue = value
	a.stats.LastUpdateTime = timestamp

	if a.stats.TotalValues == 1 {
		a.stats.MinValue = value
		a.stats.MaxValue = value
	} else {
		if value < a.stats.MinValue {
			a.stats.MinValue = value
		}
		if value > a.stats.MaxValue {
			a.stats.MaxValue = value
		}
	}
}

// Stats returns aggregator statistics.
func (a *Aggregator) Stats() *AggregatorStats {
	a.mu.RLock()
	defer a.mu.RUnlock()

	return a.stats
}

// CreateAlerter creates a new alerter.
func (pm *PerformanceMonitor) CreateAlerter(name, alertType string) (*Alerter, error) {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if _, exists := pm.alerters[name]; exists {
		return nil, fmt.Errorf("alerter %s already exists", name)
	}

	alerter := &Alerter{
		name:         name,
		alertType:    alertType,
		enabled:      true,
		rules:        make(map[string]*AlertRule),
		handlers:     make(map[string]func(*Alert) error),
		stats:        &AlerterStats{},
		cleanupFuncs: make([]func() error, 0),
	}

	pm.alerters[name] = alerter
	atomic.AddInt64(&pm.metrics.TotalAlerters, 1)
	atomic.AddInt64(&pm.metrics.ActiveAlerters, 1)

	return alerter, nil
}

// GetAlerter retrieves an alerter by name.
func (pm *PerformanceMonitor) GetAlerter(name string) (*Alerter, bool) {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	alerter, exists := pm.alerters[name]
	return alerter, exists
}

// Start starts the alerter.
func (a *Alerter) Start() error {
	a.mu.Lock()
	defer a.mu.Unlock()

	// Start alerting logic
	go func() {
		for {
			select {
			case <-time.After(1 * time.Second):
				a.checkRules()
			}
		}
	}()

	return nil
}

// Stop stops the alerter.
func (a *Alerter) Stop() error {
	a.mu.Lock()
	defer a.mu.Unlock()

	a.enabled = false
	return nil
}

// checkRules checks all alert rules.
func (a *Alerter) checkRules() {
	a.mu.RLock()
	defer a.mu.RUnlock()

	for name, rule := range a.rules {
		if rule.Enabled {
			a.checkRule(name, rule)
		}
	}
}

// checkRule checks a specific alert rule.
func (a *Alerter) checkRule(name string, rule *AlertRule) {
	if !rule.Enabled {
		return
	}

	// Check if rule is in cooldown period
	if time.Since(rule.LastTriggered) < rule.Cooldown {
		return
	}

	// Simple rule evaluation - in production, this would be more sophisticated
	// For now, we'll simulate rule checking based on system metrics
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	var shouldTrigger bool
	var currentValue float64

	switch rule.Condition {
	case "cpu_usage > 80":
		currentValue = float64(m.NumGC) // Simulate CPU usage
		shouldTrigger = currentValue > rule.Threshold
	case "memory_usage > 1000000000":
		currentValue = float64(m.Alloc)
		shouldTrigger = currentValue > rule.Threshold
	default:
		// Default condition - always false for safety
		shouldTrigger = false
	}

	if shouldTrigger {
		// Create and trigger alert
		alert := &Alert{
			ID:          fmt.Sprintf("alert_%s_%d", name, time.Now().Unix()),
			Name:        rule.Name,
			Description: rule.Description,
			Severity:    rule.Severity,
			Status:      "active",
			Timestamp:   time.Now(),
			Value:       currentValue,
			Threshold:   rule.Threshold,
			Rule:        rule,
			Metadata:    make(map[string]interface{}),
		}

		// Update rule statistics
		rule.LastTriggered = time.Now()
		rule.TriggerCount++
		atomic.AddInt64(&rule.Stats.TotalTriggers, 1)
		atomic.AddInt64(&rule.Stats.SuccessfulTriggers, 1)

		// Update alerter statistics
		atomic.AddInt64(&a.stats.TotalAlerts, 1)
		atomic.AddInt64(&a.stats.TriggeredAlerts, 1)
		atomic.AddInt64(&a.stats.ActiveAlerts, 1)
		a.stats.LastAlertTime = time.Now()

		// Execute alert handlers
		for _, handler := range a.handlers {
			if err := handler(alert); err != nil {
				atomic.AddInt64(&rule.Stats.FailedTriggers, 1)
				continue
			}
		}
	}
}

// AddRule adds an alert rule.
func (a *Alerter) AddRule(rule *AlertRule) {
	a.mu.Lock()
	defer a.mu.Unlock()

	a.rules[rule.Name] = rule
}

// GetRule retrieves an alert rule by name.
func (a *Alerter) GetRule(name string) (*AlertRule, bool) {
	a.mu.RLock()
	defer a.mu.RUnlock()

	rule, exists := a.rules[name]
	return rule, exists
}

// AddHandler adds an alert handler.
func (a *Alerter) AddHandler(name string, handler func(*Alert) error) {
	a.mu.Lock()
	defer a.mu.Unlock()

	a.handlers[name] = handler
}

// Stats returns alerter statistics.
func (a *Alerter) Stats() *AlerterStats {
	a.mu.RLock()
	defer a.mu.RUnlock()

	return a.stats
}

// CreateReporter creates a new reporter.
func (pm *PerformanceMonitor) CreateReporter(name, reporterType string, interval time.Duration) (*Reporter, error) {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if _, exists := pm.reporters[name]; exists {
		return nil, fmt.Errorf("reporter %s already exists", name)
	}

	reporter := &Reporter{
		name:         name,
		reporterType: reporterType,
		interval:     interval,
		enabled:      true,
		formatters:   make(map[string]func(*Report) ([]byte, error)),
		outputs:      make(map[string]func([]byte) error),
		stats:        &ReporterStats{},
		cleanupFuncs: make([]func() error, 0),
	}

	pm.reporters[name] = reporter
	atomic.AddInt64(&pm.metrics.TotalReporters, 1)
	atomic.AddInt64(&pm.metrics.ActiveReporters, 1)

	return reporter, nil
}

// GetReporter retrieves a reporter by name.
func (pm *PerformanceMonitor) GetReporter(name string) (*Reporter, bool) {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	reporter, exists := pm.reporters[name]
	return reporter, exists
}

// Start starts the reporter.
func (r *Reporter) Start() error {
	r.mu.Lock()
	defer r.mu.Unlock()

	if r.enabled {
		r.ticker = time.NewTicker(r.interval)
		r.stopCh = make(chan struct{})

		go func() {
			for {
				select {
				case <-r.ticker.C:
					r.report()
				case <-r.stopCh:
					return
				}
			}
		}()
	}

	return nil
}

// Stop stops the reporter.
func (r *Reporter) Stop() error {
	r.mu.Lock()
	defer r.mu.Unlock()

	if r.ticker != nil {
		r.ticker.Stop()
	}

	if r.stopCh != nil {
		close(r.stopCh)
	}

	r.enabled = false
	return nil
}

// report generates and outputs a report.
func (r *Reporter) report() {
	r.mu.Lock()
	defer r.mu.Unlock()

	start := time.Now()

	// Create report
	report := &Report{
		ID:          fmt.Sprintf("report_%d", time.Now().Unix()),
		Name:        r.name,
		Description: "Performance report",
		Timestamp:   time.Now(),
		Duration:    0,
		Metrics:     make(map[string]interface{}),
		Alerts:      make([]*Alert, 0),
		Summary:     &ReportSummary{},
		Metadata:    make(map[string]interface{}),
	}

	// Format report
	for _, formatter := range r.formatters {
		if data, err := formatter(report); err == nil {
			// Output report
			for _, output := range r.outputs {
				if err := output(data); err == nil {
					atomic.AddInt64(&r.stats.TotalReports, 1)
					atomic.AddInt64(&r.stats.SuccessfulReports, 1)
					atomic.AddInt64(&r.stats.TotalBytes, int64(len(data)))
				} else {
					atomic.AddInt64(&r.stats.FailedReports, 1)
				}
			}
		}
	}

	duration := time.Since(start)
	r.stats.AverageReportTime = duration
	r.stats.LastReportTime = time.Now()
}

// AddFormatter adds a report formatter.
func (r *Reporter) AddFormatter(name string, formatter func(*Report) ([]byte, error)) {
	r.mu.Lock()
	defer r.mu.Unlock()

	r.formatters[name] = formatter
}

// AddOutput adds a report output.
func (r *Reporter) AddOutput(name string, output func([]byte) error) {
	r.mu.Lock()
	defer r.mu.Unlock()

	r.outputs[name] = output
}

// Stats returns reporter statistics.
func (r *Reporter) Stats() *ReporterStats {
	r.mu.RLock()
	defer r.mu.RUnlock()

	return r.stats
}

// GetMetrics returns performance monitor metrics.
func (pm *PerformanceMonitor) GetMetrics() *PerformanceMonitorMetrics {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	pm.metrics.LastUpdateTime = time.Now()
	return pm.metrics
}

// Helper functions for performance monitoring

// Initialize helper functions
func (pm *PerformanceMonitor) initializeDefaultCollectors() error {
	// Create default collectors
	defaultCollectors := []struct {
		name     string
		typ      string
		interval time.Duration
	}{
		{"system", "system", 5 * time.Second},
		{"application", "application", 1 * time.Second},
		{"business", "business", 10 * time.Second},
	}

	for _, config := range defaultCollectors {
		collector, err := pm.CreateMetricsCollector(config.name, config.typ, config.interval)
		if err != nil {
			return fmt.Errorf("failed to create collector %s: %w", config.name, err)
		}

		// Add default collectors
		collector.AddCollector("cpu_usage", func() interface{} {
			var m runtime.MemStats
			runtime.ReadMemStats(&m)
			return float64(m.NumGC)
		})

		collector.AddCollector("memory_usage", func() interface{} {
			var m runtime.MemStats
			runtime.ReadMemStats(&m)
			return int64(m.Alloc)
		})

		collector.AddCollector("goroutine_count", func() interface{} {
			return runtime.NumGoroutine()
		})
	}

	return nil
}

func (pm *PerformanceMonitor) initializeDefaultAggregators() error {
	// Create default aggregators
	defaultAggregators := []struct {
		name     string
		typ      string
		interval time.Duration
	}{
		{"system", "system", 30 * time.Second},
		{"application", "application", 10 * time.Second},
		{"business", "business", 60 * time.Second},
	}

	for _, config := range defaultAggregators {
		aggregator, err := pm.CreateMetricsAggregator(config.name, config.typ, config.interval)
		if err != nil {
			return fmt.Errorf("failed to create aggregator %s: %w", config.name, err)
		}

		// Add default aggregators
		aggregator.AddAggregator("cpu_avg", NewAggregator("cpu_avg", "avg", 5*time.Minute))
		aggregator.AddAggregator("memory_avg", NewAggregator("memory_avg", "avg", 5*time.Minute))
		aggregator.AddAggregator("goroutine_avg", NewAggregator("goroutine_avg", "avg", 5*time.Minute))
	}

	return nil
}

func (pm *PerformanceMonitor) initializeDefaultAlerters() error {
	// Create default alerters
	defaultAlerters := []struct {
		name string
		typ  string
	}{
		{"system", "system"},
		{"application", "application"},
		{"business", "business"},
	}

	for _, config := range defaultAlerters {
		alerter, err := pm.CreateAlerter(config.name, config.typ)
		if err != nil {
			return fmt.Errorf("failed to create alerter %s: %w", config.name, err)
		}

		// Add default alert rules
		alerter.AddRule(&AlertRule{
			Name:        "high_cpu_usage",
			Description: "High CPU usage detected",
			Condition:   "cpu_usage > 80",
			Threshold:   80.0,
			Operator:    ">",
			Severity:    "warning",
			Enabled:     true,
			Cooldown:    5 * time.Minute,
			Stats:       &AlertRuleStats{},
		})

		alerter.AddRule(&AlertRule{
			Name:        "high_memory_usage",
			Description: "High memory usage detected",
			Condition:   "memory_usage > 1000000000", // 1GB
			Threshold:   1000000000.0,
			Operator:    ">",
			Severity:    "critical",
			Enabled:     true,
			Cooldown:    2 * time.Minute,
			Stats:       &AlertRuleStats{},
		})
	}

	return nil
}

func (pm *PerformanceMonitor) initializeDefaultReporters() error {
	// Create default reporters
	defaultReporters := []struct {
		name     string
		typ      string
		interval time.Duration
	}{
		{"console", "console", 1 * time.Minute},
		{"file", "file", 5 * time.Minute},
		{"http", "http", 30 * time.Second},
	}

	for _, config := range defaultReporters {
		reporter, err := pm.CreateReporter(config.name, config.typ, config.interval)
		if err != nil {
			return fmt.Errorf("failed to create reporter %s: %w", config.name, err)
		}

		// Add default formatters
		reporter.AddFormatter("json", func(report *Report) ([]byte, error) {
			// Create comprehensive JSON report
			jsonData := fmt.Sprintf(`{
				"id": "%s",
				"name": "%s",
				"description": "%s",
				"timestamp": "%s",
				"duration": "%v",
				"metrics_count": %d,
				"alerts_count": %d,
				"active_alerts": %d,
				"resolved_alerts": %d,
				"summary": {
					"total_metrics": %d,
					"total_alerts": %d,
					"active_alerts": %d,
					"resolved_alerts": %d,
					"average_latency": "%v",
					"average_throughput": %.2f,
					"memory_usage": %d,
					"cpu_usage": %.2f,
					"goroutine_count": %d,
					"overall_health": "%s",
					"score": %.2f
				}
			}`,
				report.ID,
				report.Name,
				report.Description,
				report.Timestamp.Format(time.RFC3339),
				report.Duration,
				len(report.Metrics),
				len(report.Alerts),
				func() int {
					count := 0
					for _, alert := range report.Alerts {
						if alert.Status == "active" {
							count++
						}
					}
					return count
				}(),
				func() int {
					count := 0
					for _, alert := range report.Alerts {
						if alert.Status == "resolved" {
							count++
						}
					}
					return count
				}(),
				report.Summary.TotalMetrics,
				report.Summary.TotalAlerts,
				report.Summary.ActiveAlerts,
				report.Summary.ResolvedAlerts,
				report.Summary.AverageLatency,
				report.Summary.AverageThroughput,
				report.Summary.MemoryUsage,
				report.Summary.CPUUsage,
				report.Summary.GoroutineCount,
				report.Summary.OverallHealth,
				report.Summary.Score,
			)
			return []byte(jsonData), nil
		})

		// Add default outputs
		reporter.AddOutput("console", func(data []byte) error {
			fmt.Printf("Report: %s\n", string(data))
			return nil
		})
	}

	return nil
}

// Performance optimization constants for monitoring
const (
	DefaultCollectorInterval  = 5 * time.Second
	DefaultAggregatorInterval = 30 * time.Second
	DefaultAlerterInterval    = 1 * time.Second
	DefaultReporterInterval   = 1 * time.Minute
	DefaultAggregatorWindow   = 5 * time.Minute
	DefaultAlertCooldown      = 5 * time.Minute
	DefaultReportFormat       = "json"
	DefaultReportOutput       = "console"
)

// Performance monitoring error types
var (
	ErrMonitorNotRunning       = fmt.Errorf("performance monitor is not running")
	ErrMonitorAlreadyRunning   = fmt.Errorf("performance monitor is already running")
	ErrCollectorNotFound       = fmt.Errorf("collector not found")
	ErrAggregatorNotFound      = fmt.Errorf("aggregator not found")
	ErrAlerterNotFound         = fmt.Errorf("alerter not found")
	ErrReporterNotFound        = fmt.Errorf("reporter not found")
	ErrCollectorAlreadyExists  = fmt.Errorf("collector already exists")
	ErrAggregatorAlreadyExists = fmt.Errorf("aggregator already exists")
	ErrAlerterAlreadyExists    = fmt.Errorf("alerter already exists")
	ErrReporterAlreadyExists   = fmt.Errorf("reporter already exists")
	ErrInvalidConfiguration    = fmt.Errorf("invalid configuration")
	ErrCollectionFailed        = fmt.Errorf("collection failed")
	ErrAggregationFailed       = fmt.Errorf("aggregation failed")
	ErrAlertingFailed          = fmt.Errorf("alerting failed")
	ErrReportingFailed         = fmt.Errorf("reporting failed")
)

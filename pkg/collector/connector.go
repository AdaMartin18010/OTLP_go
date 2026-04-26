package collector

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"go.uber.org/zap"
)

// Connector is a component that translates data between pipelines.
type Connector interface {
	Component
	// InputDataType returns the data type this connector consumes.
	InputDataType() DataType
	// OutputDataType returns the data type this connector produces.
	OutputDataType() DataType
}

// ConnectorFactory creates Connector instances.
type ConnectorFactory interface {
	Factory
	// CreateDefaultConfig returns the default configuration for the connector.
	CreateDefaultConfig() interface{}
	// CreateTracesToMetrics creates a connector that consumes traces and produces metrics.
	CreateTracesToMetrics(ctx context.Context, set CreateSettings, cfg interface{}) (TracesToMetrics, error)
	// CreateTracesToLogs creates a connector that consumes traces and produces logs.
	CreateTracesToLogs(ctx context.Context, set CreateSettings, cfg interface{}) (TracesToLogs, error)
	// CreateMetricsToLogs creates a connector that consumes metrics and produces logs.
	CreateMetricsToLogs(ctx context.Context, set CreateSettings, cfg interface{}) (MetricsToLogs, error)
	// CreateMetricsToMetrics creates a connector that consumes metrics and produces metrics.
	CreateMetricsToMetrics(ctx context.Context, set CreateSettings, cfg interface{}) (MetricsToMetrics, error)
}

// TracesToMetrics consumes trace data and produces metric data.
type TracesToMetrics interface {
	Connector
}

// TracesToLogs consumes trace data and produces log data.
type TracesToLogs interface {
	Connector
}

// MetricsToLogs consumes metric data and produces log data.
type MetricsToLogs interface {
	Connector
}

// MetricsToMetrics consumes metric data and produces metric data.
type MetricsToMetrics interface {
	Connector
}

// spanCountConnector counts spans and emits them as metrics.
type spanCountConnector struct {
	id       ComponentID
	logger   Logger
	started  atomic.Bool
	shutdown chan struct{}
	mu       sync.RWMutex
	counts   map[string]int64 // keyed by service name or span kind
}

// NewSpanCountConnector creates a connector that converts traces to metrics by counting spans.
func NewSpanCountConnector(set CreateSettings) (TracesToMetrics, error) {
	return &spanCountConnector{
		id:       set.ID,
		logger:   set.Logger,
		shutdown: make(chan struct{}),
		counts:   make(map[string]int64),
	}, nil
}

func (c *spanCountConnector) Start(ctx context.Context) error {
	if !c.started.CompareAndSwap(false, true) {
		return fmt.Errorf("connector %q already started", c.id.String())
	}
	c.logger.Info("span count connector started", zap.String("connector", c.id.String()))
	return nil
}

func (c *spanCountConnector) Shutdown(ctx context.Context) error {
	if !c.started.CompareAndSwap(true, false) {
		return nil
	}
	close(c.shutdown)
	c.logger.Info("span count connector shutdown", zap.String("connector", c.id.String()))
	return nil
}

func (c *spanCountConnector) InputDataType() DataType  { return DataTypeTraces }
func (c *spanCountConnector) OutputDataType() DataType { return DataTypeMetrics }

// RecordSpan is called for each span to update internal counters.
func (c *spanCountConnector) RecordSpan(serviceName, spanKind string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	key := serviceName + "/" + spanKind
	c.counts[key]++
}

// GetCounts returns a snapshot of current span counts.
func (c *spanCountConnector) GetCounts() map[string]int64 {
	c.mu.RLock()
	defer c.mu.RUnlock()
	out := make(map[string]int64, len(c.counts))
	for k, v := range c.counts {
		out[k] = v
	}
	return out
}

// errorCountConnector counts error spans and emits them as metrics.
type errorCountConnector struct {
	id       ComponentID
	logger   Logger
	started  atomic.Bool
	shutdown chan struct{}
	mu       sync.RWMutex
	errors   map[string]int64 // keyed by service name
}

// NewErrorCountConnector creates a connector that converts trace errors to metrics.
func NewErrorCountConnector(set CreateSettings) (TracesToMetrics, error) {
	return &errorCountConnector{
		id:       set.ID,
		logger:   set.Logger,
		shutdown: make(chan struct{}),
		errors:   make(map[string]int64),
	}, nil
}

func (c *errorCountConnector) Start(ctx context.Context) error {
	if !c.started.CompareAndSwap(false, true) {
		return fmt.Errorf("connector %q already started", c.id.String())
	}
	c.logger.Info("error count connector started", zap.String("connector", c.id.String()))
	return nil
}

func (c *errorCountConnector) Shutdown(ctx context.Context) error {
	if !c.started.CompareAndSwap(true, false) {
		return nil
	}
	close(c.shutdown)
	c.logger.Info("error count connector shutdown", zap.String("connector", c.id.String()))
	return nil
}

func (c *errorCountConnector) InputDataType() DataType  { return DataTypeTraces }
func (c *errorCountConnector) OutputDataType() DataType { return DataTypeMetrics }

// RecordError increments the error count for a service.
func (c *errorCountConnector) RecordError(serviceName string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.errors[serviceName]++
}

// GetErrors returns a snapshot of current error counts.
func (c *errorCountConnector) GetErrors() map[string]int64 {
	c.mu.RLock()
	defer c.mu.RUnlock()
	out := make(map[string]int64, len(c.errors))
	for k, v := range c.errors {
		out[k] = v
	}
	return out
}

// metricToLogConnector converts anomalous metrics into log alerts.
type metricToLogConnector struct {
	id        ComponentID
	logger    Logger
	started   atomic.Bool
	shutdown  chan struct{}
	mu        sync.RWMutex
	alerts    []LogAlert
	threshold float64
}

// LogAlert represents an alert generated from a metric anomaly.
type LogAlert struct {
	Timestamp time.Time `json:"timestamp"`
	Severity  string    `json:"severity"`
	Message   string    `json:"message"`
	MetricName string   `json:"metric_name"`
	Value     float64   `json:"value"`
}

// NewMetricToLogConnector creates a connector that converts metrics to logs.
func NewMetricToLogConnector(set CreateSettings, threshold float64) (MetricsToLogs, error) {
	return &metricToLogConnector{
		id:        set.ID,
		logger:    set.Logger,
		shutdown:  make(chan struct{}),
		threshold: threshold,
	}, nil
}

func (c *metricToLogConnector) Start(ctx context.Context) error {
	if !c.started.CompareAndSwap(false, true) {
		return fmt.Errorf("connector %q already started", c.id.String())
	}
	c.logger.Info("metric to log connector started", zap.String("connector", c.id.String()))
	return nil
}

func (c *metricToLogConnector) Shutdown(ctx context.Context) error {
	if !c.started.CompareAndSwap(true, false) {
		return nil
	}
	close(c.shutdown)
	c.logger.Info("metric to log connector shutdown", zap.String("connector", c.id.String()))
	return nil
}

func (c *metricToLogConnector) InputDataType() DataType  { return DataTypeMetrics }
func (c *metricToLogConnector) OutputDataType() DataType { return DataTypeLogs }

// EvaluateMetric checks a metric value against the threshold and generates an alert if exceeded.
func (c *metricToLogConnector) EvaluateMetric(name string, value float64) *LogAlert {
	if value < c.threshold {
		return nil
	}
	alert := LogAlert{
		Timestamp:  time.Now().UTC(),
		Severity:   "WARNING",
		Message:    fmt.Sprintf("metric %s exceeded threshold: %.2f > %.2f", name, value, c.threshold),
		MetricName: name,
		Value:      value,
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	c.alerts = append(c.alerts, alert)
	return &alert
}

// GetAlerts returns a snapshot of current alerts.
func (c *metricToLogConnector) GetAlerts() []LogAlert {
	c.mu.RLock()
	defer c.mu.RUnlock()
	out := make([]LogAlert, len(c.alerts))
	copy(out, c.alerts)
	return out
}

// Logger is a minimal logging interface used within the collector package.
type Logger interface {
	Info(msg string, fields ...zap.Field)
	Warn(msg string, fields ...zap.Field)
	Error(msg string, fields ...zap.Field)
}

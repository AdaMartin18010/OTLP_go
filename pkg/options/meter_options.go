// Package options provides functional options pattern implementations
// for configuring OTLP Go SDK components.
package options

import (
	"fmt"
	"time"
)

// AggregationTemporality represents the aggregation temporality for metrics.
type AggregationTemporality string

const (
	// AggregationTemporalityDelta uses delta temporality.
	AggregationTemporalityDelta AggregationTemporality = "delta"
	// AggregationTemporalityCumulative uses cumulative temporality.
	AggregationTemporalityCumulative AggregationTemporality = "cumulative"
)

// IsValid returns true if the aggregation temporality is valid.
func (a AggregationTemporality) IsValid() bool {
	switch a {
	case AggregationTemporalityDelta, AggregationTemporalityCumulative:
		return true
	default:
		return false
	}
}

// MetricExporterType represents the type of metric exporter.
type MetricExporterType string

const (
	// MetricExporterOTLP uses OTLP/gRPC exporter.
	MetricExporterOTLP MetricExporterType = "otlp"
	// MetricExporterPrometheus uses Prometheus exporter.
	MetricExporterPrometheus MetricExporterType = "prometheus"
	// MetricExporterConsole uses console exporter.
	MetricExporterConsole MetricExporterType = "console"
)

// IsValid returns true if the metric exporter type is valid.
func (m MetricExporterType) IsValid() bool {
	switch m {
	case MetricExporterOTLP, MetricExporterPrometheus, MetricExporterConsole:
		return true
	default:
		return false
	}
}

// ViewType represents the type of view for metric customization.
type ViewType string

const (
	// ViewTypeDrop drops the metric.
	ViewTypeDrop ViewType = "drop"
	// ViewTypeRename renames the metric.
	ViewTypeRename ViewType = "rename"
	// ViewTypeChangeAggregation changes the aggregation.
	ViewTypeChangeAggregation ViewType = "change_aggregation"
)

// IsValid returns true if the view type is valid.
func (v ViewType) IsValid() bool {
	switch v {
	case ViewTypeDrop, ViewTypeRename, ViewTypeChangeAggregation:
		return true
	default:
		return false
	}
}

// MeterConfig holds configuration specific to the meter provider.
type MeterConfig struct {
	BaseConfig

	// ServiceName is the name of the service.
	ServiceName string

	// ServiceVersion is the version of the service.
	ServiceVersion string

	// ExporterType is the type of metric exporter to use.
	ExporterType MetricExporterType

	// Temporality is the aggregation temporality preference.
	Temporality AggregationTemporality

	// PeriodicReaderInterval is the interval for periodic metric collection.
	PeriodicReaderInterval time.Duration

	// PeriodicReaderTimeout is the timeout for periodic metric collection.
	PeriodicReaderTimeout time.Duration

	// Views are custom views for metric customization.
	Views []View

	// ResourceAttributes are additional resource attributes.
	ResourceAttributes map[string]interface{}

	// DisableBuiltinMetrics disables built-in runtime/host metrics.
	DisableBuiltinMetrics bool
}

// View represents a custom view for metric customization.
type View struct {
	// Type is the type of view.
	Type ViewType

	// InstrumentName is the name of the instrument to match.
	InstrumentName string

	// NewName is the new name for rename views.
	NewName string

	// Aggregation is the new aggregation for change aggregation views.
	Aggregation AggregationType
}

// AggregationType represents the type of aggregation.
type AggregationType string

const (
	// AggregationDefault uses the default aggregation.
	AggregationDefault AggregationType = "default"
	// AggregationSum uses sum aggregation.
	AggregationSum AggregationType = "sum"
	// AggregationCount uses count aggregation.
	AggregationCount AggregationType = "count"
	// AggregationLastValue uses last value aggregation.
	AggregationLastValue AggregationType = "last_value"
	// AggregationExplicitBucketHistogram uses explicit bucket histogram.
	AggregationExplicitBucketHistogram AggregationType = "explicit_bucket_histogram"
)

// IsValid returns true if the aggregation type is valid.
func (a AggregationType) IsValid() bool {
	switch a {
	case AggregationDefault, AggregationSum, AggregationCount, AggregationLastValue, AggregationExplicitBucketHistogram:
		return true
	default:
		return false
	}
}

// DefaultMeterConfig returns the default meter configuration.
func DefaultMeterConfig() *MeterConfig {
	return &MeterConfig{
		BaseConfig:             *DefaultBaseConfig(),
		ExporterType:           MetricExporterOTLP,
		Temporality:            AggregationTemporalityCumulative,
		PeriodicReaderInterval: 60 * time.Second,
		PeriodicReaderTimeout:  30 * time.Second,
		Views:                  make([]View, 0),
		ResourceAttributes:     make(map[string]interface{}),
		DisableBuiltinMetrics:  false,
	}
}

// Validate validates the meter configuration.
func (c *MeterConfig) Validate() error {
	if err := c.BaseConfig.Validate(); err != nil {
		return fmt.Errorf("base config validation failed: %w", err)
	}
	if c.ServiceName == "" {
		return fmt.Errorf("service name is required")
	}
	if !c.ExporterType.IsValid() {
		return fmt.Errorf("invalid exporter type: %s", c.ExporterType)
	}
	if !c.Temporality.IsValid() {
		return fmt.Errorf("invalid temporality: %s", c.Temporality)
	}
	if c.PeriodicReaderInterval <= 0 {
		return fmt.Errorf("periodic reader interval must be positive: %v", c.PeriodicReaderInterval)
	}
	if c.PeriodicReaderTimeout <= 0 {
		return fmt.Errorf("periodic reader timeout must be positive: %v", c.PeriodicReaderTimeout)
	}
	if c.PeriodicReaderTimeout > c.PeriodicReaderInterval {
		return fmt.Errorf("periodic reader timeout (%v) must be <= interval (%v)",
			c.PeriodicReaderTimeout, c.PeriodicReaderInterval)
	}
	for i, view := range c.Views {
		if err := view.Validate(); err != nil {
			return fmt.Errorf("view %d validation failed: %w", i, err)
		}
	}
	return nil
}

// Validate validates a view configuration.
func (v View) Validate() error {
	if !v.Type.IsValid() {
		return fmt.Errorf("invalid view type: %s", v.Type)
	}
	if v.InstrumentName == "" {
		return fmt.Errorf("instrument name is required")
	}
	if v.Type == ViewTypeRename && v.NewName == "" {
		return fmt.Errorf("new name is required for rename view")
	}
	if v.Type == ViewTypeChangeAggregation && !v.Aggregation.IsValid() {
		return fmt.Errorf("invalid aggregation type: %s", v.Aggregation)
	}
	return nil
}

// MeterOption is a functional option for configuring the meter.
type MeterOption func(*MeterConfig) error

// Apply implements the Option interface.
func (o MeterOption) Apply(cfg interface{}) error {
	if c, ok := cfg.(*MeterConfig); ok {
		return o(c)
	}
	return fmt.Errorf("expected *MeterConfig, got %T", cfg)
}

// WithMeterServiceName sets the service name for the meter.
func WithMeterServiceName(name string) MeterOption {
	return func(cfg *MeterConfig) error {
		if name == "" {
			return fmt.Errorf("service name cannot be empty")
		}
		cfg.ServiceName = name
		return nil
	}
}

// WithMeterServiceVersion sets the service version for the meter.
func WithMeterServiceVersion(version string) MeterOption {
	return func(cfg *MeterConfig) error {
		cfg.ServiceVersion = version
		return nil
	}
}

// WithMetricExporter sets the metric exporter type.
func WithMetricExporter(exporter MetricExporterType) MeterOption {
	return func(cfg *MeterConfig) error {
		if !exporter.IsValid() {
			return fmt.Errorf("invalid exporter type: %s", exporter)
		}
		cfg.ExporterType = exporter
		return nil
	}
}

// WithTemporality sets the aggregation temporality.
func WithTemporality(temporality AggregationTemporality) MeterOption {
	return func(cfg *MeterConfig) error {
		if !temporality.IsValid() {
			return fmt.Errorf("invalid temporality: %s", temporality)
		}
		cfg.Temporality = temporality
		return nil
	}
}

// WithPeriodicReaderInterval sets the periodic reader interval.
func WithPeriodicReaderInterval(interval time.Duration) MeterOption {
	return func(cfg *MeterConfig) error {
		if interval <= 0 {
			return fmt.Errorf("periodic reader interval must be positive: %v", interval)
		}
		cfg.PeriodicReaderInterval = interval
		return nil
	}
}

// WithPeriodicReaderTimeout sets the periodic reader timeout.
func WithPeriodicReaderTimeout(timeout time.Duration) MeterOption {
	return func(cfg *MeterConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("periodic reader timeout must be positive: %v", timeout)
		}
		cfg.PeriodicReaderTimeout = timeout
		return nil
	}
}

// WithView adds a custom view for metric customization.
func WithView(view View) MeterOption {
	return func(cfg *MeterConfig) error {
		if err := view.Validate(); err != nil {
			return fmt.Errorf("invalid view: %w", err)
		}
		cfg.Views = append(cfg.Views, view)
		return nil
	}
}

// WithDropView adds a view that drops metrics matching the instrument name.
func WithDropView(instrumentName string) MeterOption {
	return func(cfg *MeterConfig) error {
		view := View{
			Type:           ViewTypeDrop,
			InstrumentName: instrumentName,
		}
		if err := view.Validate(); err != nil {
			return err
		}
		cfg.Views = append(cfg.Views, view)
		return nil
	}
}

// WithRenameView adds a view that renames metrics.
func WithRenameView(instrumentName, newName string) MeterOption {
	return func(cfg *MeterConfig) error {
		view := View{
			Type:           ViewTypeRename,
			InstrumentName: instrumentName,
			NewName:        newName,
		}
		if err := view.Validate(); err != nil {
			return err
		}
		cfg.Views = append(cfg.Views, view)
		return nil
	}
}

// WithChangeAggregationView adds a view that changes metric aggregation.
func WithChangeAggregationView(instrumentName string, aggregation AggregationType) MeterOption {
	return func(cfg *MeterConfig) error {
		view := View{
			Type:           ViewTypeChangeAggregation,
			InstrumentName: instrumentName,
			Aggregation:    aggregation,
		}
		if err := view.Validate(); err != nil {
			return err
		}
		cfg.Views = append(cfg.Views, view)
		return nil
	}
}

// WithMeterResourceAttribute adds a resource attribute for the meter.
func WithMeterResourceAttribute(key string, value interface{}) MeterOption {
	return func(cfg *MeterConfig) error {
		if cfg.ResourceAttributes == nil {
			cfg.ResourceAttributes = make(map[string]interface{})
		}
		cfg.ResourceAttributes[key] = value
		return nil
	}
}

// WithMeterResourceAttributes sets multiple resource attributes for the meter.
func WithMeterResourceAttributes(attrs map[string]interface{}) MeterOption {
	return func(cfg *MeterConfig) error {
		if cfg.ResourceAttributes == nil {
			cfg.ResourceAttributes = make(map[string]interface{})
		}
		for k, v := range attrs {
			cfg.ResourceAttributes[k] = v
		}
		return nil
	}
}

// WithBuiltinMetricsDisabled disables built-in metrics.
func WithBuiltinMetricsDisabled() MeterOption {
	return func(cfg *MeterConfig) error {
		cfg.DisableBuiltinMetrics = true
		return nil
	}
}

// ApplyMeterOptions applies meter options and returns the configuration.
func ApplyMeterOptions(opts ...MeterOption) (*MeterConfig, error) {
	cfg := DefaultMeterConfig()
	for _, opt := range opts {
		if err := opt(cfg); err != nil {
			return nil, err
		}
	}
	if err := cfg.Validate(); err != nil {
		return nil, err
	}
	return cfg, nil
}

// MeterBaseEndpoint sets the meter endpoint (wrapper around WithEndpoint).
func MeterBaseEndpoint(endpoint string) MeterOption {
	return func(cfg *MeterConfig) error {
		if endpoint == "" {
			return fmt.Errorf("endpoint cannot be empty")
		}
		cfg.Endpoint = endpoint
		return nil
	}
}

// MeterBaseTimeout sets the meter timeout (wrapper around WithTimeout).
func MeterBaseTimeout(timeout time.Duration) MeterOption {
	return func(cfg *MeterConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("timeout must be positive: %v", timeout)
		}
		cfg.Timeout = timeout
		return nil
	}
}

// MeterBaseHeaders sets the meter headers (wrapper around WithHeaders).
func MeterBaseHeaders(headers map[string]string) MeterOption {
	return func(cfg *MeterConfig) error {
		cfg.Headers = make(map[string]string)
		for k, v := range headers {
			cfg.Headers[k] = v
		}
		return nil
	}
}

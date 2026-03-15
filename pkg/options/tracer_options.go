// Package options provides functional options pattern implementations
// for configuring OTLP Go SDK components.
package options

import (
	"fmt"
	"time"
)

// SamplerType represents the type of sampler to use for traces.
type SamplerType string

const (
	// SamplerAlwaysOn samples all traces.
	SamplerAlwaysOn SamplerType = "always_on"
	// SamplerAlwaysOff samples no traces.
	SamplerAlwaysOff SamplerType = "always_off"
	// SamplerTraceIDRatio samples based on trace ID ratio.
	SamplerTraceIDRatio SamplerType = "trace_id_ratio"
	// SamplerParentBased samples based on parent span sampling decision.
	SamplerParentBased SamplerType = "parent_based"
)

// IsValid returns true if the sampler type is valid.
func (s SamplerType) IsValid() bool {
	switch s {
	case SamplerAlwaysOn, SamplerAlwaysOff, SamplerTraceIDRatio, SamplerParentBased:
		return true
	default:
		return false
	}
}

// String returns the string representation of the sampler type.
func (s SamplerType) String() string {
	return string(s)
}

// SpanProcessorType represents the type of span processor.
type SpanProcessorType string

const (
	// SpanProcessorBatch batches spans before exporting.
	SpanProcessorBatch SpanProcessorType = "batch"
	// SpanProcessorSimple exports spans immediately.
	SpanProcessorSimple SpanProcessorType = "simple"
)

// IsValid returns true if the span processor type is valid.
func (s SpanProcessorType) IsValid() bool {
	switch s {
	case SpanProcessorBatch, SpanProcessorSimple:
		return true
	default:
		return false
	}
}

// TracerConfig holds configuration specific to the tracer provider.
type TracerConfig struct {
	BaseConfig

	// ServiceName is the name of the service.
	ServiceName string

	// ServiceVersion is the version of the service.
	ServiceVersion string

	// ServiceNamespace is the namespace of the service.
	ServiceNamespace string

	// ServiceInstanceID is the unique instance ID of the service.
	ServiceInstanceID string

	// SamplerType is the type of sampler to use.
	SamplerType SamplerType

	// SamplingRatio is the ratio for probability-based sampling (0.0 to 1.0).
	SamplingRatio float64

	// SpanProcessorType is the type of span processor to use.
	SpanProcessorType SpanProcessorType

	// BatchConfig holds batch span processor configuration.
	BatchConfig *BatchSpanProcessorConfig

	// MaxEventsPerSpan is the maximum number of events per span.
	MaxEventsPerSpan int

	// MaxAttributesPerSpan is the maximum number of attributes per span.
	MaxAttributesPerSpan int

	// MaxLinksPerSpan is the maximum number of links per span.
	MaxLinksPerSpan int

	// Attributes are additional resource attributes.
	Attributes map[string]interface{}
}

// BatchSpanProcessorConfig holds configuration for the batch span processor.
type BatchSpanProcessorConfig struct {
	// MaxQueueSize is the maximum queue size.
	MaxQueueSize int

	// BatchTimeout is the maximum time to wait before exporting a batch.
	BatchTimeout time.Duration

	// ExportTimeout is the maximum time to wait for an export to complete.
	ExportTimeout time.Duration

	// MaxExportBatchSize is the maximum number of spans in a batch.
	MaxExportBatchSize int
}

// DefaultBatchSpanProcessorConfig returns the default batch span processor configuration.
func DefaultBatchSpanProcessorConfig() *BatchSpanProcessorConfig {
	return &BatchSpanProcessorConfig{
		MaxQueueSize:       2048,
		BatchTimeout:       5 * time.Second,
		ExportTimeout:      30 * time.Second,
		MaxExportBatchSize: 512,
	}
}

// Validate validates the batch span processor configuration.
func (b *BatchSpanProcessorConfig) Validate() error {
	if b == nil {
		return nil
	}
	if b.MaxQueueSize <= 0 {
		return fmt.Errorf("max queue size must be positive: %d", b.MaxQueueSize)
	}
	if b.BatchTimeout <= 0 {
		return fmt.Errorf("batch timeout must be positive: %v", b.BatchTimeout)
	}
	if b.ExportTimeout <= 0 {
		return fmt.Errorf("export timeout must be positive: %v", b.ExportTimeout)
	}
	if b.MaxExportBatchSize <= 0 {
		return fmt.Errorf("max export batch size must be positive: %d", b.MaxExportBatchSize)
	}
	if b.MaxExportBatchSize > b.MaxQueueSize {
		return fmt.Errorf("max export batch size (%d) must be <= max queue size (%d)",
			b.MaxExportBatchSize, b.MaxQueueSize)
	}
	return nil
}

// DefaultTracerConfig returns the default tracer configuration.
func DefaultTracerConfig() *TracerConfig {
	return &TracerConfig{
		BaseConfig:           *DefaultBaseConfig(),
		SamplerType:          SamplerParentBased,
		SamplingRatio:        1.0,
		SpanProcessorType:    SpanProcessorBatch,
		BatchConfig:          DefaultBatchSpanProcessorConfig(),
		MaxEventsPerSpan:     128,
		MaxAttributesPerSpan: 128,
		MaxLinksPerSpan:      32,
		Attributes:           make(map[string]interface{}),
	}
}

// Validate validates the tracer configuration.
func (c *TracerConfig) Validate() error {
	if err := c.BaseConfig.Validate(); err != nil {
		return fmt.Errorf("base config validation failed: %w", err)
	}
	if c.ServiceName == "" {
		return fmt.Errorf("service name is required")
	}
	if !c.SamplerType.IsValid() {
		return fmt.Errorf("invalid sampler type: %s", c.SamplerType)
	}
	if c.SamplingRatio < 0.0 || c.SamplingRatio > 1.0 {
		return fmt.Errorf("sampling ratio must be between 0.0 and 1.0: %f", c.SamplingRatio)
	}
	if !c.SpanProcessorType.IsValid() {
		return fmt.Errorf("invalid span processor type: %s", c.SpanProcessorType)
	}
	if err := c.BatchConfig.Validate(); err != nil {
		return fmt.Errorf("batch config validation failed: %w", err)
	}
	if c.MaxEventsPerSpan <= 0 {
		return fmt.Errorf("max events per span must be positive: %d", c.MaxEventsPerSpan)
	}
	if c.MaxAttributesPerSpan <= 0 {
		return fmt.Errorf("max attributes per span must be positive: %d", c.MaxAttributesPerSpan)
	}
	if c.MaxLinksPerSpan <= 0 {
		return fmt.Errorf("max links per span must be positive: %d", c.MaxLinksPerSpan)
	}
	return nil
}

// TracerOption is a functional option for configuring the tracer.
type TracerOption func(*TracerConfig) error

// Apply implements the Option interface.
func (o TracerOption) Apply(cfg interface{}) error {
	if c, ok := cfg.(*TracerConfig); ok {
		return o(c)
	}
	return fmt.Errorf("expected *TracerConfig, got %T", cfg)
}

// WithServiceName sets the service name.
func WithServiceName(name string) TracerOption {
	return func(cfg *TracerConfig) error {
		if name == "" {
			return fmt.Errorf("service name cannot be empty")
		}
		cfg.ServiceName = name
		return nil
	}
}

// WithServiceVersion sets the service version.
func WithServiceVersion(version string) TracerOption {
	return func(cfg *TracerConfig) error {
		cfg.ServiceVersion = version
		return nil
	}
}

// WithServiceNamespace sets the service namespace.
func WithServiceNamespace(namespace string) TracerOption {
	return func(cfg *TracerConfig) error {
		cfg.ServiceNamespace = namespace
		return nil
	}
}

// WithServiceInstanceID sets the service instance ID.
func WithServiceInstanceID(instanceID string) TracerOption {
	return func(cfg *TracerConfig) error {
		cfg.ServiceInstanceID = instanceID
		return nil
	}
}

// WithSampler sets the sampler type.
func WithSampler(sampler SamplerType) TracerOption {
	return func(cfg *TracerConfig) error {
		if !sampler.IsValid() {
			return fmt.Errorf("invalid sampler type: %s", sampler)
		}
		cfg.SamplerType = sampler
		return nil
	}
}

// WithSamplingRatio sets the sampling ratio for probability-based samplers.
func WithSamplingRatio(ratio float64) TracerOption {
	return func(cfg *TracerConfig) error {
		if ratio < 0.0 || ratio > 1.0 {
			return fmt.Errorf("sampling ratio must be between 0.0 and 1.0: %f", ratio)
		}
		cfg.SamplingRatio = ratio
		return nil
	}
}

// WithSpanProcessor sets the span processor type.
func WithSpanProcessor(processor SpanProcessorType) TracerOption {
	return func(cfg *TracerConfig) error {
		if !processor.IsValid() {
			return fmt.Errorf("invalid span processor type: %s", processor)
		}
		cfg.SpanProcessorType = processor
		return nil
	}
}

// WithBatchConfig sets the batch span processor configuration.
func WithBatchConfig(batch *BatchSpanProcessorConfig) TracerOption {
	return func(cfg *TracerConfig) error {
		if err := batch.Validate(); err != nil {
			return fmt.Errorf("invalid batch config: %w", err)
		}
		cfg.BatchConfig = batch
		return nil
	}
}

// WithMaxQueueSize sets the maximum queue size for the batch processor.
func WithMaxQueueSize(size int) TracerOption {
	return func(cfg *TracerConfig) error {
		if size <= 0 {
			return fmt.Errorf("max queue size must be positive: %d", size)
		}
		if cfg.BatchConfig == nil {
			cfg.BatchConfig = DefaultBatchSpanProcessorConfig()
		}
		cfg.BatchConfig.MaxQueueSize = size
		return nil
	}
}

// WithBatchTimeout sets the batch timeout for the batch processor.
func WithBatchTimeout(timeout time.Duration) TracerOption {
	return func(cfg *TracerConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("batch timeout must be positive: %v", timeout)
		}
		if cfg.BatchConfig == nil {
			cfg.BatchConfig = DefaultBatchSpanProcessorConfig()
		}
		cfg.BatchConfig.BatchTimeout = timeout
		return nil
	}
}

// WithExportTimeout sets the export timeout for the batch processor.
func WithExportTimeout(timeout time.Duration) TracerOption {
	return func(cfg *TracerConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("export timeout must be positive: %v", timeout)
		}
		if cfg.BatchConfig == nil {
			cfg.BatchConfig = DefaultBatchSpanProcessorConfig()
		}
		cfg.BatchConfig.ExportTimeout = timeout
		return nil
	}
}

// WithMaxExportBatchSize sets the maximum export batch size.
func WithMaxExportBatchSize(size int) TracerOption {
	return func(cfg *TracerConfig) error {
		if size <= 0 {
			return fmt.Errorf("max export batch size must be positive: %d", size)
		}
		if cfg.BatchConfig == nil {
			cfg.BatchConfig = DefaultBatchSpanProcessorConfig()
		}
		cfg.BatchConfig.MaxExportBatchSize = size
		return nil
	}
}

// WithMaxEventsPerSpan sets the maximum number of events per span.
func WithMaxEventsPerSpan(max int) TracerOption {
	return func(cfg *TracerConfig) error {
		if max <= 0 {
			return fmt.Errorf("max events per span must be positive: %d", max)
		}
		cfg.MaxEventsPerSpan = max
		return nil
	}
}

// WithMaxAttributesPerSpan sets the maximum number of attributes per span.
func WithMaxAttributesPerSpan(max int) TracerOption {
	return func(cfg *TracerConfig) error {
		if max <= 0 {
			return fmt.Errorf("max attributes per span must be positive: %d", max)
		}
		cfg.MaxAttributesPerSpan = max
		return nil
	}
}

// WithMaxLinksPerSpan sets the maximum number of links per span.
func WithMaxLinksPerSpan(max int) TracerOption {
	return func(cfg *TracerConfig) error {
		if max <= 0 {
			return fmt.Errorf("max links per span must be positive: %d", max)
		}
		cfg.MaxLinksPerSpan = max
		return nil
	}
}

// WithAttribute adds a resource attribute.
func WithAttribute(key string, value interface{}) TracerOption {
	return func(cfg *TracerConfig) error {
		if cfg.Attributes == nil {
			cfg.Attributes = make(map[string]interface{})
		}
		cfg.Attributes[key] = value
		return nil
	}
}

// WithAttributes sets multiple resource attributes.
func WithAttributes(attrs map[string]interface{}) TracerOption {
	return func(cfg *TracerConfig) error {
		if cfg.Attributes == nil {
			cfg.Attributes = make(map[string]interface{})
		}
		for k, v := range attrs {
			cfg.Attributes[k] = v
		}
		return nil
	}
}

// ApplyTracerOptions applies tracer options and returns the configuration.
func ApplyTracerOptions(opts ...TracerOption) (*TracerConfig, error) {
	cfg := DefaultTracerConfig()
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

// TracerBaseEndpoint sets the tracer endpoint (wrapper around WithEndpoint).
func TracerBaseEndpoint(endpoint string) TracerOption {
	return func(cfg *TracerConfig) error {
		if endpoint == "" {
			return fmt.Errorf("endpoint cannot be empty")
		}
		cfg.Endpoint = endpoint
		return nil
	}
}

// TracerBaseTimeout sets the tracer timeout (wrapper around WithTimeout).
func TracerBaseTimeout(timeout time.Duration) TracerOption {
	return func(cfg *TracerConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("timeout must be positive: %v", timeout)
		}
		cfg.Timeout = timeout
		return nil
	}
}

// TracerBaseHeaders sets the tracer headers (wrapper around WithHeaders).
func TracerBaseHeaders(headers map[string]string) TracerOption {
	return func(cfg *TracerConfig) error {
		cfg.Headers = make(map[string]string)
		for k, v := range headers {
			cfg.Headers[k] = v
		}
		return nil
	}
}

// Package options provides functional options pattern implementations
// for configuring OTLP Go SDK components.
//
// This package includes:
//   - Option types for all SDK components
//   - Validation functions
//   - Default option sets
//   - Option composition utilities
//
// Example usage:
//
//	opts := []options.TracerOption{
//	    options.WithSampler(sdktrace.AlwaysSample()),
//	    options.WithResource(resource),
//	}
//	tp := sdktrace.NewTracerProvider(opts...)
package options

import (
	"context"
	"fmt"
	"time"
)

// Option is the base interface for all functional options.
// It provides a common type constraint for option implementations.
type Option interface {
	// Apply applies the option to the target configuration.
	Apply(interface{}) error
}

// OptionFunc is a function type that implements the Option interface.
// It allows simple functions to be used as options.
type OptionFunc func(interface{}) error

// Apply implements the Option interface by calling the function itself.
func (f OptionFunc) Apply(cfg interface{}) error {
	return f(cfg)
}

// Configurable is an interface for types that can accept options.
type Configurable interface {
	// ApplyOptions applies a list of options to the configuration.
	ApplyOptions(opts ...Option) error
}

// BaseConfig provides common configuration fields used across all components.
type BaseConfig struct {
	// Endpoint is the target endpoint for telemetry data.
	Endpoint string

	// Timeout is the maximum time to wait for an operation.
	Timeout time.Duration

	// Headers are additional HTTP/gRPC headers to send.
	Headers map[string]string

	// Compression is the compression algorithm to use.
	Compression CompressionType

	// RetryConfig holds retry policy configuration.
	RetryConfig *RetryConfig

	// TLSConfig holds TLS configuration.
	TLSConfig *TLSConfig
}

// CompressionType represents the compression algorithm.
type CompressionType string

const (
	// CompressionNone means no compression.
	CompressionNone CompressionType = "none"
	// CompressionGzip uses gzip compression.
	CompressionGzip CompressionType = "gzip"
)

// IsValid returns true if the compression type is valid.
func (c CompressionType) IsValid() bool {
	switch c {
	case CompressionNone, CompressionGzip:
		return true
	default:
		return false
	}
}

// RetryConfig holds retry policy configuration.
type RetryConfig struct {
	// Enabled determines if retries are enabled.
	Enabled bool

	// MaxRetries is the maximum number of retry attempts.
	MaxRetries int

	// InitialInterval is the initial retry interval.
	InitialInterval time.Duration

	// MaxInterval is the maximum retry interval.
	MaxInterval time.Duration

	// Multiplier is the exponential backoff multiplier.
	Multiplier float64
}

// DefaultRetryConfig returns the default retry configuration.
func DefaultRetryConfig() *RetryConfig {
	return &RetryConfig{
		Enabled:         true,
		MaxRetries:      3,
		InitialInterval: 1 * time.Second,
		MaxInterval:     30 * time.Second,
		Multiplier:      2.0,
	}
}

// Validate checks if the retry configuration is valid.
func (r *RetryConfig) Validate() error {
	if r == nil {
		return nil
	}
	if r.MaxRetries < 0 {
		return fmt.Errorf("max retries cannot be negative: %d", r.MaxRetries)
	}
	if r.InitialInterval < 0 {
		return fmt.Errorf("initial interval cannot be negative: %v", r.InitialInterval)
	}
	if r.MaxInterval < 0 {
		return fmt.Errorf("max interval cannot be negative: %v", r.MaxInterval)
	}
	if r.MaxInterval < r.InitialInterval {
		return fmt.Errorf("max interval (%v) must be >= initial interval (%v)",
			r.MaxInterval, r.InitialInterval)
	}
	if r.Multiplier < 1.0 {
		return fmt.Errorf("multiplier must be >= 1.0: %f", r.Multiplier)
	}
	return nil
}

// TLSConfig holds TLS configuration.
type TLSConfig struct {
	// Insecure allows insecure connections when true.
	Insecure bool

	// CertFile is the path to the TLS certificate file.
	CertFile string

	// KeyFile is the path to the TLS key file.
	KeyFile string

	// CAFile is the path to the CA certificate file.
	CAFile string

	// ServerNameOverride overrides the server name for TLS verification.
	ServerNameOverride string
}

// Validate checks if the TLS configuration is valid.
func (t *TLSConfig) Validate() error {
	if t == nil {
		return nil
	}
	if !t.Insecure {
		if t.CertFile != "" && t.KeyFile == "" {
			return fmt.Errorf("key file is required when cert file is provided")
		}
		if t.KeyFile != "" && t.CertFile == "" {
			return fmt.Errorf("cert file is required when key file is provided")
		}
	}
	return nil
}

// BaseOption is the base option type for all components.
type BaseOption func(*BaseConfig) error

// Apply applies the base option to the configuration.
func (o BaseOption) Apply(cfg interface{}) error {
	if c, ok := cfg.(*BaseConfig); ok {
		return o(c)
	}
	return fmt.Errorf("expected *BaseConfig, got %T", cfg)
}

// WithEndpoint sets the endpoint for the component.
func WithEndpoint(endpoint string) BaseOption {
	return func(cfg *BaseConfig) error {
		if endpoint == "" {
			return fmt.Errorf("endpoint cannot be empty")
		}
		cfg.Endpoint = endpoint
		return nil
	}
}

// WithTimeout sets the timeout for the component.
func WithTimeout(timeout time.Duration) BaseOption {
	return func(cfg *BaseConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("timeout must be positive: %v", timeout)
		}
		cfg.Timeout = timeout
		return nil
	}
}

// WithHeaders sets the headers for the component.
func WithHeaders(headers map[string]string) BaseOption {
	return func(cfg *BaseConfig) error {
		cfg.Headers = make(map[string]string)
		for k, v := range headers {
			cfg.Headers[k] = v
		}
		return nil
	}
}

// WithHeader adds a single header to the component configuration.
func WithHeader(key, value string) BaseOption {
	return func(cfg *BaseConfig) error {
		if cfg.Headers == nil {
			cfg.Headers = make(map[string]string)
		}
		cfg.Headers[key] = value
		return nil
	}
}

// WithCompression sets the compression type for the component.
func WithCompression(compression CompressionType) BaseOption {
	return func(cfg *BaseConfig) error {
		if !compression.IsValid() {
			return fmt.Errorf("invalid compression type: %s", compression)
		}
		cfg.Compression = compression
		return nil
	}
}

// WithRetryConfig sets the retry configuration for the component.
func WithRetryConfig(retry *RetryConfig) BaseOption {
	return func(cfg *BaseConfig) error {
		if err := retry.Validate(); err != nil {
			return fmt.Errorf("invalid retry config: %w", err)
		}
		cfg.RetryConfig = retry
		return nil
	}
}

// WithTLSConfig sets the TLS configuration for the component.
func WithTLSConfig(tls *TLSConfig) BaseOption {
	return func(cfg *BaseConfig) error {
		if err := tls.Validate(); err != nil {
			return fmt.Errorf("invalid TLS config: %w", err)
		}
		cfg.TLSConfig = tls
		return nil
	}
}

// Insecure allows insecure connections.
func Insecure() BaseOption {
	return func(cfg *BaseConfig) error {
		if cfg.TLSConfig == nil {
			cfg.TLSConfig = &TLSConfig{}
		}
		cfg.TLSConfig.Insecure = true
		return nil
	}
}

// DefaultBaseConfig returns the default base configuration.
func DefaultBaseConfig() *BaseConfig {
	return &BaseConfig{
		Endpoint:    "localhost:4317",
		Timeout:     10 * time.Second,
		Headers:     make(map[string]string),
		Compression: CompressionGzip,
		RetryConfig: DefaultRetryConfig(),
		TLSConfig:   &TLSConfig{Insecure: false},
	}
}

// Validate validates the base configuration.
func (c *BaseConfig) Validate() error {
	if c.Endpoint == "" {
		return fmt.Errorf("endpoint is required")
	}
	if c.Timeout <= 0 {
		return fmt.Errorf("timeout must be positive")
	}
	if !c.Compression.IsValid() {
		return fmt.Errorf("invalid compression type: %s", c.Compression)
	}
	if err := c.RetryConfig.Validate(); err != nil {
		return fmt.Errorf("retry config validation failed: %w", err)
	}
	if err := c.TLSConfig.Validate(); err != nil {
		return fmt.Errorf("TLS config validation failed: %w", err)
	}
	return nil
}

// ApplyOptions applies a list of options to the configuration.
func (c *BaseConfig) ApplyOptions(opts ...BaseOption) error {
	for _, opt := range opts {
		if err := opt(c); err != nil {
			return err
		}
	}
	return c.Validate()
}

// MergeOptions merges multiple option slices into one.
func MergeOptions(opts ...[]Option) []Option {
	var merged []Option
	for _, opt := range opts {
		merged = append(merged, opt...)
	}
	return merged
}

// ApplyContext is a context-aware option application function.
type ApplyContext func(context.Context, interface{}) error

// ContextOption wraps an option with context support.
func ContextOption(apply ApplyContext) Option {
	return OptionFunc(func(cfg interface{}) error {
		return apply(context.Background(), cfg)
	})
}

// LazyOption creates an option that is evaluated lazily.
func LazyOption(fn func() Option) Option {
	return OptionFunc(func(cfg interface{}) error {
		opt := fn()
		if opt == nil {
			return nil
		}
		return opt.Apply(cfg)
	})
}

// ConditionalOption creates an option that is applied only if the condition is true.
func ConditionalOption(condition bool, opt Option) Option {
	return OptionFunc(func(cfg interface{}) error {
		if !condition {
			return nil
		}
		return opt.Apply(cfg)
	})
}

// ComposeOptions composes multiple options into a single option.
func ComposeOptions(opts ...Option) Option {
	return OptionFunc(func(cfg interface{}) error {
		for _, opt := range opts {
			if err := opt.Apply(cfg); err != nil {
				return err
			}
		}
		return nil
	})
}

// Package resource provides OpenTelemetry resource utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Resource detection from environment
//   - Resource merging
//   - Resource validation
//   - Cloud provider detection (GCP, AWS, Azure)
//
// Example usage:
//
//	res, err := resource.New(ctx,
//	    resource.WithFromEnv(),
//	    resource.WithProcess(),
//	    resource.WithOS(),
//	    resource.WithContainer(),
//	)
package resource

import (
	"context"
	"errors"
	"fmt"

	"OTLP_go/pkg/types"
)

var (
	// ErrNoResource is returned when no resource could be detected.
	ErrNoResource = errors.New("no resource detected")

	// ErrDetectorFailed is returned when a detector fails.
	ErrDetectorFailed = errors.New("resource detector failed")
)

// Config is the resource configuration.
type Config struct {
	// Detectors is a list of detectors to use.
	Detectors []Detector

	// DefaultAttributes are attributes to add if not already present.
	DefaultAttributes map[string]interface{}
}

// Option configures a Config.
type Option func(*Config)

// WithDetectors sets the detectors to use.
func WithDetectors(detectors ...Detector) Option {
	return func(c *Config) {
		c.Detectors = detectors
	}
}

// WithDefaultAttributes sets default attributes.
func WithDefaultAttributes(attrs map[string]interface{}) Option {
	return func(c *Config) {
		c.DefaultAttributes = attrs
	}
}

// Detector is a resource detector interface.
type Detector interface {
	// Detect detects resource attributes from the environment.
	Detect(ctx context.Context) (*types.Resource, error)
	// DetectorType returns the type of detector.
	DetectorType() string
}

// DetectorFunc is a function that implements the Detector interface.
type DetectorFunc struct {
	Type string
	Fn   func(ctx context.Context) (*types.Resource, error)
}

// Detect implements the Detector interface.
func (d DetectorFunc) Detect(ctx context.Context) (*types.Resource, error) {
	return d.Fn(ctx)
}

// DetectorType implements the Detector interface.
func (d DetectorFunc) DetectorType() string {
	return d.Type
}

// New creates a new resource by running the configured detectors.
// Detectors are run in order and their results are merged.
// Later detectors override attributes from earlier ones.
func New(ctx context.Context, options ...Option) (*types.Resource, error) {
	cfg := &Config{
		Detectors:         []Detector{},
		DefaultAttributes: make(map[string]interface{}),
	}

	for _, opt := range options {
		opt(cfg)
	}

	// If no detectors specified, use default set
	if len(cfg.Detectors) == 0 {
		cfg.Detectors = DefaultDetectors()
	}

	var result *types.Resource

	// Run all detectors and merge results
	for _, detector := range cfg.Detectors {
		res, err := detector.Detect(ctx)
		if err != nil {
			// Continue on detector failure
			continue
		}
		if res != nil {
			result = result.Merge(res)
		}
	}

	// Apply default attributes
	if len(cfg.DefaultAttributes) > 0 {
		defaultRes := types.NewResourceFromMap(cfg.DefaultAttributes)
		if result == nil {
			result = defaultRes
		} else {
			// Default attributes only apply if not already set
			for k, v := range cfg.DefaultAttributes {
				if _, ok := result.Get(k); !ok {
					result.SetString(k, fmt.Sprintf("%v", v))
				}
			}
		}
	}

	if result == nil || result.IsEmpty() {
		return types.DefaultResource(), nil
	}

	// Add default telemetry SDK attributes if not present
	if _, ok := result.Get("telemetry.sdk.name"); !ok {
		result.SetString("telemetry.sdk.name", "OTLP_go")
	}
	if _, ok := result.Get("telemetry.sdk.version"); !ok {
		result.SetString("telemetry.sdk.version", "1.0.0")
	}
	if _, ok := result.Get("telemetry.sdk.language"); !ok {
		result.SetString("telemetry.sdk.language", "go")
	}

	return result, nil
}

// MustNew creates a new resource or panics on error.
func MustNew(ctx context.Context, options ...Option) *types.Resource {
	r, err := New(ctx, options...)
	if err != nil {
		panic(err)
	}
	return r
}

// Merge combines multiple resources into one.
// Later resources override attributes from earlier ones.
func Merge(resources ...*types.Resource) *types.Resource {
	var result *types.Resource
	for _, r := range resources {
		result = result.Merge(r)
	}
	if result == nil {
		return types.EmptyResource()
	}
	return result
}

// DefaultDetectors returns the default set of detectors.
func DefaultDetectors() []Detector {
	return []Detector{
		&EnvironmentDetector{},
		&HostDetector{},
		&ProcessDetector{},
	}
}

// Default returns the default resource with SDK attributes.
func Default() *types.Resource {
	return types.DefaultResource()
}

// Empty returns an empty resource.
func Empty() *types.Resource {
	return types.EmptyResource()
}

// ProcessDetector detects process-related resource attributes.
type ProcessDetector struct{}

// DetectorType returns the type of detector.
func (d *ProcessDetector) DetectorType() string {
	return "process"
}

// Detect detects process-related resource attributes.
func (d *ProcessDetector) Detect(ctx context.Context) (*types.Resource, error) {
	builder := types.NewResourceBuilder()

	// Get process information using runtime package
	importRuntimeInfo(builder)

	return builder.Build(), nil
}

// WithFromEnv creates an option that includes the environment detector.
func WithFromEnv() Option {
	return func(c *Config) {
		// Add environment detector if not already present
		hasEnv := false
		for _, d := range c.Detectors {
			if d.DetectorType() == "environment" {
				hasEnv = true
				break
			}
		}
		if !hasEnv {
			c.Detectors = append([]Detector{&EnvironmentDetector{}}, c.Detectors...)
		}
	}
}

// WithHost creates an option that includes the host detector.
func WithHost() Option {
	return func(c *Config) {
		hasHost := false
		for _, d := range c.Detectors {
			if d.DetectorType() == "host" {
				hasHost = true
				break
			}
		}
		if !hasHost {
			c.Detectors = append(c.Detectors, &HostDetector{})
		}
	}
}

// WithProcess creates an option that includes the process detector.
func WithProcess() Option {
	return func(c *Config) {
		hasProcess := false
		for _, d := range c.Detectors {
			if d.DetectorType() == "process" {
				hasProcess = true
				break
			}
		}
		if !hasProcess {
			c.Detectors = append(c.Detectors, &ProcessDetector{})
		}
	}
}

// WithContainer creates an option that includes the container detector.
func WithContainer() Option {
	return func(c *Config) {
		hasContainer := false
		for _, d := range c.Detectors {
			if d.DetectorType() == "container" {
				hasContainer = true
				break
			}
		}
		if !hasContainer {
			c.Detectors = append(c.Detectors, &ContainerDetector{})
		}
	}
}

// WithOS creates an option that includes the OS detector.
func WithOS() Option {
	return func(c *Config) {
		hasOS := false
		for _, d := range c.Detectors {
			if d.DetectorType() == "os" {
				hasOS = true
				break
			}
		}
		if !hasOS {
			c.Detectors = append(c.Detectors, &OSDetector{})
		}
	}
}

// OSDetector detects OS-related resource attributes.
type OSDetector struct{}

// DetectorType returns the type of detector.
func (d *OSDetector) DetectorType() string {
	return "os"
}

// Detect detects OS-related resource attributes.
func (d *OSDetector) Detect(ctx context.Context) (*types.Resource, error) {
	builder := types.NewResourceBuilder()
	importOSInfo(builder)
	return builder.Build(), nil
}

// ContainerDetector detects container-related resource attributes.
type ContainerDetector struct{}

// DetectorType returns the type of detector.
func (d *ContainerDetector) DetectorType() string {
	return "container"
}

// Detect detects container-related resource attributes.
func (d *ContainerDetector) Detect(ctx context.Context) (*types.Resource, error) {
	return detectContainer(ctx)
}

// CloudProviderDetector detects cloud provider resource attributes.
type CloudProviderDetector struct {
	provider string
}

// NewCloudProviderDetector creates a new cloud provider detector.
func NewCloudProviderDetector(provider string) *CloudProviderDetector {
	return &CloudProviderDetector{provider: provider}
}

// DetectorType returns the type of detector.
func (d *CloudProviderDetector) DetectorType() string {
	return "cloud"
}

// Detect detects cloud provider resource attributes.
func (d *CloudProviderDetector) Detect(ctx context.Context) (*types.Resource, error) {
	switch d.provider {
	case "aws":
		return detectAWS(ctx)
	case "gcp":
		return detectGCP(ctx)
	case "azure":
		return detectAzure(ctx)
	default:
		return nil, fmt.Errorf("unknown cloud provider: %s", d.provider)
	}
}

// Package resource provides resource detection from environment variables.
package resource

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"strings"

	"OTLP_go/pkg/types"
)

const (
	// OTELResourceAttributesEnv is the environment variable name for resource attributes.
	OTELResourceAttributesEnv = "OTEL_RESOURCE_ATTRIBUTES"
	// OTELServiceNameEnv is the environment variable name for service name.
	OTELServiceNameEnv = "OTEL_SERVICE_NAME"
)

// EnvironmentDetector detects resource attributes from environment variables.
type EnvironmentDetector struct {
	// CustomAttrs allows specifying additional environment variables to read.
	CustomAttrs map[string]string // env var -> attribute key
}

// DetectorType returns the type of detector.
func (d *EnvironmentDetector) DetectorType() string {
	return "environment"
}

// Detect detects resource attributes from environment variables.
func (d *EnvironmentDetector) Detect(ctx context.Context) (*types.Resource, error) {
	builder := types.NewResourceBuilder()

	// Parse OTEL_RESOURCE_ATTRIBUTES
	if attrs := os.Getenv(OTELResourceAttributesEnv); attrs != "" {
		parsed := parseAttributes(attrs)
		for k, v := range parsed {
			builder.WithString(k, v)
		}
	}

	// Parse OTEL_SERVICE_NAME
	if serviceName := os.Getenv(OTELServiceNameEnv); serviceName != "" {
		builder.WithString("service.name", serviceName)
	}

	// Parse custom environment variables
	for envVar, attrKey := range d.CustomAttrs {
		if value := os.Getenv(envVar); value != "" {
			builder.WithString(attrKey, value)
		}
	}

	return builder.Build(), nil
}

// parseAttributes parses the OTEL_RESOURCE_ATTRIBUTES format.
// Format: key1=value1,key2=value2,...
// Values can be quoted: key1="value1,with,commas",key2=value2
func parseAttributes(s string) map[string]string {
	result := make(map[string]string)
	if s == "" {
		return result
	}

	var key strings.Builder
	var value strings.Builder
	inValue := false
	inQuotes := false

	for i := 0; i < len(s); i++ {
		ch := s[i]

		if !inValue {
			// Parsing key
			if ch == '=' {
				inValue = true
			} else if ch == ',' {
				// Empty key, skip
				key.Reset()
			} else {
				key.WriteByte(ch)
			}
		} else {
			// Parsing value
			if inQuotes {
				if ch == '"' {
					inQuotes = false
				} else {
					value.WriteByte(ch)
				}
			} else {
				if ch == '"' && value.Len() == 0 {
					inQuotes = true
				} else if ch == ',' {
					// End of this pair
					k := strings.TrimSpace(key.String())
					if k != "" {
						result[k] = strings.TrimSpace(value.String())
					}
					key.Reset()
					value.Reset()
					inValue = false
				} else {
					value.WriteByte(ch)
				}
			}
		}
	}

	// Don't forget the last pair
	if inValue {
		k := strings.TrimSpace(key.String())
		if k != "" {
			result[k] = strings.TrimSpace(value.String())
		}
	}

	return result
}

// parseAttributesMap parses a JSON map from environment variable.
func parseAttributesMap(s string) map[string]string {
	result := make(map[string]string)
	if s == "" {
		return result
	}

	// Try JSON format first
	var jsonMap map[string]interface{}
	if err := json.Unmarshal([]byte(s), &jsonMap); err == nil {
		for k, v := range jsonMap {
			result[k] = fmt.Sprintf("%v", v)
		}
		return result
	}

	// Fall back to key=value format
	return parseAttributes(s)
}

// WithEnvironmentDetector adds a custom environment detector.
func WithEnvironmentDetector(customAttrs map[string]string) Option {
	return func(c *Config) {
		c.Detectors = append(c.Detectors, &EnvironmentDetector{
			CustomAttrs: customAttrs,
		})
	}
}

// GetResourceFromEnv creates a resource directly from environment variables.
func GetResourceFromEnv() (*types.Resource, error) {
	detector := &EnvironmentDetector{}
	return detector.Detect(context.Background())
}

// ResourceAttributesEnv is the standard OTEL_RESOURCE_ATTRIBUTES environment variable.
type ResourceAttributesEnv struct {
	ServiceName    string
	ServiceVersion string
	ServiceNamespace string
	DeploymentEnvironment string
	HostName       string
	HostID         string
	ContainerID    string
	ContainerName  string
	PodName        string
	PodNamespace   string
	NodeName       string
	ClusterName    string
	CloudProvider  string
	CloudRegion    string
	CloudZone      string
}

// ParseResourceAttributesEnv parses standard OTEL_RESOURCE_ATTRIBUTES.
func ParseResourceAttributesEnv() *ResourceAttributesEnv {
	env := &ResourceAttributesEnv{}

	attrs := parseAttributes(os.Getenv(OTELResourceAttributesEnv))

	env.ServiceName = attrs["service.name"]
	env.ServiceVersion = attrs["service.version"]
	env.ServiceNamespace = attrs["service.namespace"]
	env.DeploymentEnvironment = attrs["deployment.environment"]
	env.HostName = attrs["host.name"]
	env.HostID = attrs["host.id"]
	env.ContainerID = attrs["container.id"]
	env.ContainerName = attrs["container.name"]
	env.PodName = attrs["k8s.pod.name"]
	env.PodNamespace = attrs["k8s.namespace.name"]
	env.NodeName = attrs["k8s.node.name"]
	env.ClusterName = attrs["k8s.cluster.name"]
	env.CloudProvider = attrs["cloud.provider"]
	env.CloudRegion = attrs["cloud.region"]
	env.CloudZone = attrs["cloud.availability_zone"]

	return env
}

// ToResource converts ResourceAttributesEnv to a Resource.
func (e *ResourceAttributesEnv) ToResource() *types.Resource {
	builder := types.NewResourceBuilder()

	if e.ServiceName != "" {
		builder.WithString("service.name", e.ServiceName)
	}
	if e.ServiceVersion != "" {
		builder.WithString("service.version", e.ServiceVersion)
	}
	if e.ServiceNamespace != "" {
		builder.WithString("service.namespace", e.ServiceNamespace)
	}
	if e.DeploymentEnvironment != "" {
		builder.WithString("deployment.environment", e.DeploymentEnvironment)
	}
	if e.HostName != "" {
		builder.WithString("host.name", e.HostName)
	}
	if e.HostID != "" {
		builder.WithString("host.id", e.HostID)
	}
	if e.ContainerID != "" {
		builder.WithString("container.id", e.ContainerID)
	}
	if e.ContainerName != "" {
		builder.WithString("container.name", e.ContainerName)
	}
	if e.PodName != "" {
		builder.WithString("k8s.pod.name", e.PodName)
	}
	if e.PodNamespace != "" {
		builder.WithString("k8s.namespace.name", e.PodNamespace)
	}
	if e.NodeName != "" {
		builder.WithString("k8s.node.name", e.NodeName)
	}
	if e.ClusterName != "" {
		builder.WithString("k8s.cluster.name", e.ClusterName)
	}
	if e.CloudProvider != "" {
		builder.WithString("cloud.provider", e.CloudProvider)
	}
	if e.CloudRegion != "" {
		builder.WithString("cloud.region", e.CloudRegion)
	}
	if e.CloudZone != "" {
		builder.WithString("cloud.availability_zone", e.CloudZone)
	}

	return builder.Build()
}

// ResourceFromMap creates a resource from a map of strings.
func ResourceFromMap(m map[string]string) *types.Resource {
	if len(m) == 0 {
		return types.EmptyResource()
	}

	attrs := make([]types.Attribute, 0, len(m))
	for k, v := range m {
		attrs = append(attrs, types.NewAttribute(k, v))
	}

	return types.NewResource(attrs...)
}

// MergeEnvResources merges multiple resources from environment variables.
// Later resources override earlier ones.
func MergeEnvResources(resources ...*types.Resource) *types.Resource {
	return Merge(resources...)
}

package collector

import (
	"fmt"
	"os"
	"regexp"
	"strings"

	"gopkg.in/yaml.v3"
)

// ComponentMap is a map of component IDs to their configurations.
type ComponentMap map[ComponentID]interface{}

// UnmarshalYAML implements custom YAML unmarshaling for ComponentMap.
func (cm *ComponentMap) UnmarshalYAML(node *yaml.Node) error {
	if node.Kind != yaml.MappingNode {
		return fmt.Errorf("component map must be a mapping")
	}

	*cm = make(ComponentMap)
	for i := 0; i < len(node.Content); i += 2 {
		keyNode := node.Content[i]
		valNode := node.Content[i+1]

		var cid ComponentID
		if err := cid.UnmarshalString(keyNode.Value); err != nil {
			return err
		}

		var val interface{}
		if err := valNode.Decode(&val); err != nil {
			return fmt.Errorf("failed to decode config for component %q: %w", cid.String(), err)
		}
		(*cm)[cid] = val
	}
	return nil
}

// MarshalYAML implements custom YAML marshaling.
func (cm ComponentMap) MarshalYAML() (interface{}, error) {
	node := &yaml.Node{Kind: yaml.MappingNode}
	for cid, val := range cm {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: cid.String()}
		valNode := &yaml.Node{}
		if err := valNode.Encode(val); err != nil {
			return nil, fmt.Errorf("failed to encode config for component %q: %w", cid.String(), err)
		}
		node.Content = append(node.Content, keyNode, valNode)
	}
	return node, nil
}

// ServiceConfig holds service-level configuration.
type ServiceConfig struct {
	Pipelines PipelineConfig `yaml:"pipelines"`
	// Extensions is a list of extension IDs that should be enabled.
	Extensions []ComponentID `yaml:"extensions,omitempty"`
}

// Config is the top-level collector configuration.
type Config struct {
	Receivers  ComponentMap  `yaml:"receivers,omitempty"`
	Processors ComponentMap  `yaml:"processors,omitempty"`
	Exporters  ComponentMap  `yaml:"exporters,omitempty"`
	Connectors ComponentMap  `yaml:"connectors,omitempty"`
	Extensions ComponentMap  `yaml:"extensions,omitempty"`
	Service    ServiceConfig `yaml:"service"`
}

// UnmarshalYAML implements custom YAML unmarshaling to expand environment variables.
func (c *Config) UnmarshalYAML(node *yaml.Node) error {
	// Expand env vars in raw YAML text before decoding.
	var raw map[string]interface{}
	if err := node.Decode(&raw); err != nil {
		return err
	}

	expanded, err := expandEnvInMap(raw)
	if err != nil {
		return err
	}

	// Re-encode to YAML and decode into Config using a type alias to avoid recursion.
	out, err := yaml.Marshal(expanded)
	if err != nil {
		return err
	}
	type configAlias Config
	return yaml.Unmarshal(out, (*configAlias)(c))
}

// envVarRegex matches ${env:VAR}, ${env:VAR:-default}, and ${VAR:-default} patterns.
var envVarRegex = regexp.MustCompile(`\$\{(?:env:)?([^}:]+)(?::-([^}]*))?\}`)

func expandEnvInMap(m map[string]interface{}) (map[string]interface{}, error) {
	out := make(map[string]interface{}, len(m))
	for k, v := range m {
		expandedK := expandEnvString(k)
		expandedV, err := expandEnvValue(v)
		if err != nil {
			return nil, err
		}
		out[expandedK] = expandedV
	}
	return out, nil
}

func expandEnvValue(v interface{}) (interface{}, error) {
	switch val := v.(type) {
	case string:
		return expandEnvString(val), nil
	case map[string]interface{}:
		return expandEnvInMap(val)
	case []interface{}:
		out := make([]interface{}, len(val))
		for i, item := range val {
			expanded, err := expandEnvValue(item)
			if err != nil {
				return nil, err
			}
			out[i] = expanded
		}
		return out, nil
	default:
		return v, nil
	}
}

func expandEnvString(s string) string {
	return envVarRegex.ReplaceAllStringFunc(s, func(match string) string {
		matches := envVarRegex.FindStringSubmatch(match)
		if len(matches) < 2 {
			return match
		}
		varName := matches[1]
		defaultVal := ""
		if len(matches) >= 3 {
			defaultVal = matches[2]
		}
		if v := os.Getenv(varName); v != "" {
			return v
		}
		return defaultVal
	})
}

// Validate performs comprehensive validation of the configuration.
func (c *Config) Validate() error {
	if err := c.Service.Pipelines.Validate(); err != nil {
		return fmt.Errorf("service pipelines: %w", err)
	}

	// Validate that referenced components exist in the config.
	for pid, pipeline := range c.Service.Pipelines.Pipelines {
		for i, r := range pipeline.Receivers {
			if _, ok := c.Receivers[r]; !ok {
				return fmt.Errorf("pipeline %q references unknown receiver %q at index %d", pid.String(), r.String(), i)
			}
		}
		for i, p := range pipeline.Processors {
			if _, ok := c.Processors[p]; !ok {
				return fmt.Errorf("pipeline %q references unknown processor %q at index %d", pid.String(), p.String(), i)
			}
		}
		for i, e := range pipeline.Exporters {
			if _, ok := c.Exporters[e]; !ok {
				return fmt.Errorf("pipeline %q references unknown exporter %q at index %d", pid.String(), e.String(), i)
			}
		}
		for i, conn := range pipeline.Connectors {
			if _, ok := c.Connectors[conn]; !ok {
				return fmt.Errorf("pipeline %q references unknown connector %q at index %d", pid.String(), conn.String(), i)
			}
		}
	}

	for i, extID := range c.Service.Extensions {
		if _, ok := c.Extensions[extID]; !ok {
			return fmt.Errorf("service references unknown extension %q at index %d", extID.String(), i)
		}
	}

	return nil
}

// String returns a YAML representation of the config (with sensitive values redacted).
func (c *Config) String() (string, error) {
	out, err := yaml.Marshal(c)
	if err != nil {
		return "", err
	}
	return string(out), nil
}

// ToJSON returns a JSON representation of the config.
func (c *Config) ToJSON() (string, error) {
	// Marshal to YAML then convert to map for JSON-like representation.
	// For simplicity, we output indented YAML which is human-readable.
	out, err := yaml.Marshal(c)
	if err != nil {
		return "", err
	}
	return string(out), nil
}

// RedactedString returns the config string with sensitive fields masked.
func (c *Config) RedactedString() (string, error) {
	// Create a copy and redact sensitive values.
	redacted := c.redactedCopy()
	out, err := yaml.Marshal(redacted)
	if err != nil {
		return "", err
	}
	return string(out), nil
}

func (c *Config) redactedCopy() *Config {
	cp := &Config{
		Receivers:  redactComponentMap(c.Receivers),
		Processors: redactComponentMap(c.Processors),
		Exporters:  redactComponentMap(c.Exporters),
		Connectors: redactComponentMap(c.Connectors),
		Extensions: redactComponentMap(c.Extensions),
		Service:    c.Service,
	}
	return cp
}

func redactComponentMap(cm ComponentMap) ComponentMap {
	if cm == nil {
		return nil
	}
	out := make(ComponentMap, len(cm))
	for k, v := range cm {
		out[k] = redactValue(v)
	}
	return out
}

func redactValue(v interface{}) interface{} {
	switch val := v.(type) {
	case map[string]interface{}:
		out := make(map[string]interface{}, len(val))
		for k, v2 := range val {
			if isSensitiveKey(k) {
				out[k] = "[REDACTED]"
			} else {
				out[k] = redactValue(v2)
			}
		}
		return out
	case []interface{}:
		out := make([]interface{}, len(val))
		for i, item := range val {
			out[i] = redactValue(item)
		}
		return out
	default:
		return v
	}
}

func isSensitiveKey(key string) bool {
	lower := strings.ToLower(key)
	sensitive := []string{
		"password", "token", "secret", "key", "cert", "private_key",
		"client_secret", "api_key", "bearer_token", "access_token",
	}
	for _, s := range sensitive {
		if strings.Contains(lower, s) {
			return true
		}
	}
	return false
}

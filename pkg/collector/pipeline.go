package collector

import (
	"fmt"
	"strings"

	"gopkg.in/yaml.v3"
)

// DataType represents the type of telemetry data.
type DataType string

const (
	DataTypeTraces  DataType = "traces"
	DataTypeMetrics DataType = "metrics"
	DataTypeLogs    DataType = "logs"
	DataTypeProfiles DataType = "profiles"
)

// Valid returns true if the DataType is a known telemetry type.
func (dt DataType) Valid() bool {
	switch dt {
	case DataTypeTraces, DataTypeMetrics, DataTypeLogs, DataTypeProfiles:
		return true
	}
	return false
}

// PipelineID identifies a pipeline by its data type and optional name.
type PipelineID struct {
	Type DataType
	Name string
}

// String returns the canonical representation.
func (p PipelineID) String() string {
	if p.Name == "" {
		return string(p.Type)
	}
	return string(p.Type) + "/" + p.Name
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (p *PipelineID) UnmarshalText(text []byte) error {
	return p.UnmarshalString(string(text))
}

// UnmarshalString parses a PipelineID from a string.
func (p *PipelineID) UnmarshalString(s string) error {
	s = strings.TrimSpace(s)
	if s == "" {
		return fmt.Errorf("pipeline ID cannot be empty")
	}

	parts := strings.SplitN(s, "/", 2)
	p.Type = DataType(parts[0])
	if !p.Type.Valid() {
		return fmt.Errorf("pipeline ID %q: invalid data type %q", s, parts[0])
	}

	if len(parts) == 2 {
		p.Name = strings.TrimSpace(parts[1])
	} else {
		p.Name = ""
	}
	return nil
}

// MarshalText implements encoding.TextMarshaler.
func (p PipelineID) MarshalText() ([]byte, error) {
	return []byte(p.String()), nil
}

// Pipeline defines a single processing pipeline.
type Pipeline struct {
	Receivers  []ComponentID `yaml:"receivers"`
	Processors []ComponentID `yaml:"processors,omitempty"`
	Exporters  []ComponentID `yaml:"exporters"`
	Connectors []ComponentID `yaml:"connectors,omitempty"`
}

// Validate checks that the pipeline is well-formed.
func (p Pipeline) Validate() error {
	if len(p.Receivers) == 0 {
		return fmt.Errorf("pipeline must have at least one receiver")
	}
	if len(p.Exporters) == 0 {
		return fmt.Errorf("pipeline must have at least one exporter")
	}
	for i, r := range p.Receivers {
		if r.IsEmpty() {
			return fmt.Errorf("pipeline receiver at index %d is empty", i)
		}
	}
	for i, e := range p.Exporters {
		if e.IsEmpty() {
			return fmt.Errorf("pipeline exporter at index %d is empty", i)
		}
	}
	return nil
}

// PipelineConfig holds all pipeline definitions keyed by PipelineID.
type PipelineConfig struct {
	Pipelines map[PipelineID]Pipeline `yaml:"pipelines"`
}

// UnmarshalYAML implements custom YAML unmarshaling to support PipelineID keys.
func (pc *PipelineConfig) UnmarshalYAML(node *yaml.Node) error {
	if node.Kind != yaml.MappingNode {
		return fmt.Errorf("pipeline config must be a mapping")
	}

	pc.Pipelines = make(map[PipelineID]Pipeline)
	for i := 0; i < len(node.Content); i += 2 {
		keyNode := node.Content[i]
		valNode := node.Content[i+1]

		var pid PipelineID
		if err := pid.UnmarshalString(keyNode.Value); err != nil {
			return err
		}

		var pipeline Pipeline
		if err := valNode.Decode(&pipeline); err != nil {
			return fmt.Errorf("failed to decode pipeline %q: %w", pid.String(), err)
		}
		pc.Pipelines[pid] = pipeline
	}
	return nil
}

// MarshalYAML implements custom YAML marshaling.
func (pc PipelineConfig) MarshalYAML() (interface{}, error) {
	node := &yaml.Node{Kind: yaml.MappingNode}
	for pid, pipeline := range pc.Pipelines {
		keyNode := &yaml.Node{Kind: yaml.ScalarNode, Value: pid.String()}
		valNode := &yaml.Node{}
		if err := pipeline.encodeYAML(valNode); err != nil {
			return nil, err
		}
		node.Content = append(node.Content, keyNode, valNode)
	}
	return node, nil
}

func (p Pipeline) encodeYAML(node *yaml.Node) error {
	*node = yaml.Node{Kind: yaml.MappingNode}

	receiversNode := &yaml.Node{Kind: yaml.SequenceNode}
	for _, r := range p.Receivers {
		receiversNode.Content = append(receiversNode.Content, &yaml.Node{Kind: yaml.ScalarNode, Value: r.String()})
	}
	node.Content = append(node.Content,
		&yaml.Node{Kind: yaml.ScalarNode, Value: "receivers"},
		receiversNode,
	)

	if len(p.Processors) > 0 {
		processorsNode := &yaml.Node{Kind: yaml.SequenceNode}
		for _, pr := range p.Processors {
			processorsNode.Content = append(processorsNode.Content, &yaml.Node{Kind: yaml.ScalarNode, Value: pr.String()})
		}
		node.Content = append(node.Content,
			&yaml.Node{Kind: yaml.ScalarNode, Value: "processors"},
			processorsNode,
		)
	}

	exportersNode := &yaml.Node{Kind: yaml.SequenceNode}
	for _, e := range p.Exporters {
		exportersNode.Content = append(exportersNode.Content, &yaml.Node{Kind: yaml.ScalarNode, Value: e.String()})
	}
	node.Content = append(node.Content,
		&yaml.Node{Kind: yaml.ScalarNode, Value: "exporters"},
		exportersNode,
	)

	if len(p.Connectors) > 0 {
		connectorsNode := &yaml.Node{Kind: yaml.SequenceNode}
		for _, c := range p.Connectors {
			connectorsNode.Content = append(connectorsNode.Content, &yaml.Node{Kind: yaml.ScalarNode, Value: c.String()})
		}
		node.Content = append(node.Content,
			&yaml.Node{Kind: yaml.ScalarNode, Value: "connectors"},
			connectorsNode,
		)
	}

	return nil
}

// Validate checks all pipelines in the configuration.
func (pc PipelineConfig) Validate() error {
	for pid, pipeline := range pc.Pipelines {
		if err := pipeline.Validate(); err != nil {
			return fmt.Errorf("pipeline %q: %w", pid.String(), err)
		}
	}
	return nil
}

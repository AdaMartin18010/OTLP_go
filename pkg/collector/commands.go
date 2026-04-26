package collector

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"sort"
	"text/tabwriter"
	"time"

	"gopkg.in/yaml.v3"
)

// BuildInfoCommand outputs build information.
type BuildInfoCommand struct {
	BuildInfo BuildInfo
}

// Run executes the build info command.
func (c *BuildInfoCommand) Run() error {
	fmt.Printf("Command:     %s\n", c.BuildInfo.Command)
	fmt.Printf("Description: %s\n", c.BuildInfo.Description)
	fmt.Printf("Version:     %s\n", c.BuildInfo.Version)
	fmt.Printf("GitHash:     %s\n", c.BuildInfo.GitHash)
	fmt.Printf("GoVersion:   %s\n", os.Getenv("GOVERSION"))
	fmt.Printf("BuiltAt:     %s\n", time.Now().UTC().Format(time.RFC3339))
	return nil
}

// ValidateCommand validates a collector configuration file.
type ValidateCommand struct {
	Provider ConfigProvider
}

// Run executes the validate command.
func (c *ValidateCommand) Run() error {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	data, err := c.Provider.Retrieve(ctx)
	if err != nil {
		return fmt.Errorf("failed to retrieve config: %w", err)
	}

	var cfg Config
	if err := yaml.Unmarshal(data, &cfg); err != nil {
		return fmt.Errorf("failed to parse config: %w", err)
	}

	if err := cfg.Validate(); err != nil {
		return fmt.Errorf("configuration is invalid: %w", err)
	}

	fmt.Println("Configuration is valid.")
	return nil
}

// PrintConfigCommand prints the resolved collector configuration.
type PrintConfigCommand struct {
	Provider ConfigProvider
	Redacted bool
	JSON     bool
}

// Run executes the print config command.
func (c *PrintConfigCommand) Run() error {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	data, err := c.Provider.Retrieve(ctx)
	if err != nil {
		return fmt.Errorf("failed to retrieve config: %w", err)
	}

	var cfg Config
	if err := yaml.Unmarshal(data, &cfg); err != nil {
		return fmt.Errorf("failed to parse config: %w", err)
	}

	var out string
	if c.Redacted {
		out, err = cfg.RedactedString()
	} else {
		out, err = cfg.String()
	}
	if err != nil {
		return fmt.Errorf("failed to format config: %w", err)
	}

	if c.JSON {
		// Convert YAML string to a generic map and then to JSON.
		var raw map[string]interface{}
		if err := yaml.Unmarshal([]byte(out), &raw); err != nil {
			return fmt.Errorf("failed to convert config to JSON: %w", err)
		}
		jsonBytes, err := json.MarshalIndent(raw, "", "  ")
		if err != nil {
			return fmt.Errorf("failed to marshal JSON: %w", err)
		}
		fmt.Println(string(jsonBytes))
	} else {
		fmt.Println(out)
	}
	return nil
}

// ComponentsCommand lists all registered components.
type ComponentsCommand struct {
	ReceiverFactories  map[string]Factory
	ProcessorFactories map[string]Factory
	ExporterFactories  map[string]Factory
	ConnectorFactories map[string]Factory
	ExtensionFactories map[string]Factory
}

// Run executes the components command.
func (c *ComponentsCommand) Run() error {
	w := tabwriter.NewWriter(os.Stdout, 0, 0, 2, ' ', 0)
	fmt.Fprintln(w, "KIND\tTYPE")
	fmt.Fprintln(w, "----\t----")

	printFactories(w, "receiver", c.ReceiverFactories)
	printFactories(w, "processor", c.ProcessorFactories)
	printFactories(w, "exporter", c.ExporterFactories)
	printFactories(w, "connector", c.ConnectorFactories)
	printFactories(w, "extension", c.ExtensionFactories)

	return w.Flush()
}

func printFactories(w *tabwriter.Writer, kind string, factories map[string]Factory) {
	var names []string
	for name := range factories {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		fmt.Fprintf(w, "%s\t%s\n", kind, name)
	}
}

// ComponentRegistry holds all registered component factories.
type ComponentRegistry struct {
	Receivers  map[string]Factory
	Processors map[string]Factory
	Exporters  map[string]Factory
	Connectors map[string]Factory
	Extensions map[string]Factory
}

// NewComponentRegistry creates an empty component registry.
func NewComponentRegistry() *ComponentRegistry {
	return &ComponentRegistry{
		Receivers:  make(map[string]Factory),
		Processors: make(map[string]Factory),
		Exporters:  make(map[string]Factory),
		Connectors: make(map[string]Factory),
		Extensions: make(map[string]Factory),
	}
}

// RegisterReceiver registers a receiver factory.
func (r *ComponentRegistry) RegisterReceiver(f Factory) {
	r.Receivers[f.Type()] = f
}

// RegisterProcessor registers a processor factory.
func (r *ComponentRegistry) RegisterProcessor(f Factory) {
	r.Processors[f.Type()] = f
}

// RegisterExporter registers an exporter factory.
func (r *ComponentRegistry) RegisterExporter(f Factory) {
	r.Exporters[f.Type()] = f
}

// RegisterConnector registers a connector factory.
func (r *ComponentRegistry) RegisterConnector(f Factory) {
	r.Connectors[f.Type()] = f
}

// RegisterExtension registers an extension factory.
func (r *ComponentRegistry) RegisterExtension(f Factory) {
	r.Extensions[f.Type()] = f
}

// ToCommand returns a ComponentsCommand populated from the registry.
func (r *ComponentRegistry) ToCommand() *ComponentsCommand {
	return &ComponentsCommand{
		ReceiverFactories:  r.Receivers,
		ProcessorFactories: r.Processors,
		ExporterFactories:  r.Exporters,
		ConnectorFactories: r.Connectors,
		ExtensionFactories: r.Extensions,
	}
}

// GetFactory returns the factory for a given kind and type.
func (r *ComponentRegistry) GetFactory(kind Kind, typ string) (Factory, bool) {
	switch kind {
	case KindReceiver:
		f, ok := r.Receivers[typ]
		return f, ok
	case KindProcessor:
		f, ok := r.Processors[typ]
		return f, ok
	case KindExporter:
		f, ok := r.Exporters[typ]
		return f, ok
	case KindConnector:
		f, ok := r.Connectors[typ]
		return f, ok
	case KindExtension:
		f, ok := r.Extensions[typ]
		return f, ok
	default:
		return nil, false
	}
}

// Types returns all registered types for a given kind.
func (r *ComponentRegistry) Types(kind Kind) []string {
	var m map[string]Factory
	switch kind {
	case KindReceiver:
		m = r.Receivers
	case KindProcessor:
		m = r.Processors
	case KindExporter:
		m = r.Exporters
	case KindConnector:
		m = r.Connectors
	case KindExtension:
		m = r.Extensions
	default:
		return nil
	}
	var types []string
	for t := range m {
		types = append(types, t)
	}
	sort.Strings(types)
	return types
}

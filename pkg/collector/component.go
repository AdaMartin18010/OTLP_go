// Package collector provides OpenTelemetry Collector components for the OTLP Go SDK.
//
// Stability: Development
// Compliance: OpenTelemetry Specification v1.42.0
package collector

import (
	"context"
	"fmt"
	"strings"

	"go.uber.org/zap"
)

// BuildInfo holds build metadata for the collector.
type BuildInfo struct {
	Command     string
	Description string
	Version     string
	GitHash     string
}

// DefaultBuildInfo returns a BuildInfo with sensible defaults.
func DefaultBuildInfo() BuildInfo {
	return BuildInfo{
		Command:     "otelcol",
		Description: "OpenTelemetry Collector",
		Version:     "0.0.1-dev",
		GitHash:     "unknown",
	}
}

// Component is the base interface for all collector components.
type Component interface {
	// Start begins the component's operation.
	Start(ctx context.Context) error
	// Shutdown gracefully stops the component.
	Shutdown(ctx context.Context) error
}

// Kind represents the kind of component.
type Kind int

const (
	KindReceiver Kind = iota
	KindProcessor
	KindExporter
	KindConnector
	KindExtension
)

func (k Kind) String() string {
	switch k {
	case KindReceiver:
		return "receiver"
	case KindProcessor:
		return "processor"
	case KindExporter:
		return "exporter"
	case KindConnector:
		return "connector"
	case KindExtension:
		return "extension"
	default:
		return "unknown"
	}
}

// ComponentID uniquely identifies a component instance in the format "type/name".
type ComponentID struct {
	Type string
	Name string
}

// String returns the canonical representation of the ID.
// If Name is empty, returns only the Type.
func (id ComponentID) String() string {
	if id.Name == "" {
		return id.Type
	}
	return id.Type + "/" + id.Name
}

// MarshalText implements encoding.TextMarshaler.
func (id ComponentID) MarshalText() ([]byte, error) {
	return []byte(id.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (id *ComponentID) UnmarshalText(text []byte) error {
	return id.UnmarshalString(string(text))
}

// UnmarshalString parses a ComponentID from a string.
func (id *ComponentID) UnmarshalString(s string) error {
	s = strings.TrimSpace(s)
	if s == "" {
		return fmt.Errorf("component ID cannot be empty")
	}

	parts := strings.SplitN(s, "/", 2)
	id.Type = strings.TrimSpace(parts[0])
	if id.Type == "" {
		return fmt.Errorf("component ID %q: type cannot be empty", s)
	}

	if len(parts) == 2 {
		id.Name = strings.TrimSpace(parts[1])
	} else {
		id.Name = ""
	}
	return nil
}

// IsEmpty returns true if the ComponentID has no type.
func (id ComponentID) IsEmpty() bool {
	return id.Type == ""
}

// CreateSettings holds common settings for creating components.
type CreateSettings struct {
	ID        ComponentID
	Logger    *zap.Logger
	BuildInfo BuildInfo
}

// Factory is the base interface for all component factories.
type Factory interface {
	// Type returns the component type string.
	Type() string
}

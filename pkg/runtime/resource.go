// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
package runtime

import (
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strings"
)

// ResourceAttributes holds OpenTelemetry resource attributes.
// These follow the OpenTelemetry semantic conventions for process and runtime.
type ResourceAttributes struct {
	// Process attributes
	ProcessPID             int32
	ProcessExecutableName  string
	ProcessExecutablePath  string
	ProcessCommand         string
	ProcessCommandLine     string
	ProcessOwner           string

	// Runtime attributes
	RuntimeName    string
	RuntimeVersion string
	RuntimeDescription string

	// Go-specific attributes
	GoMaxProcs    int
	GoNumGoroutine int
	GoMemoryLimit int64
}

// ResourceExporter exports runtime info as OpenTelemetry resource attributes.
type ResourceExporter struct {
	info       *Info
	buildInfo  *BuildInfo
	includeEnv bool
	envVars    []string
}

// ResourceOption configures ResourceExporter.
type ResourceOption func(*ResourceExporter)

// WithEnvVars includes specific environment variables in resource attributes.
func WithEnvVars(vars ...string) ResourceOption {
	return func(r *ResourceExporter) {
		r.includeEnv = true
		r.envVars = vars
	}
}

// WithAllEnvVars includes all OTEL_ environment variables.
func WithAllEnvVars() ResourceOption {
	return func(r *ResourceExporter) {
		r.includeEnv = true
	}
}

// NewResourceExporter creates a new ResourceExporter.
func NewResourceExporter(opts ...ResourceOption) *ResourceExporter {
	exporter := &ResourceExporter{
		info:      GetInfo(),
		buildInfo: GetBuildInfo(),
	}

	for _, opt := range opts {
		opt(exporter)
	}

	return exporter
}

// Export exports runtime information as resource attributes.
func (r *ResourceExporter) Export() *ResourceAttributes {
	attrs := &ResourceAttributes{
		RuntimeName:    "go",
		RuntimeVersion: r.info.GoVersion,
		RuntimeDescription: fmt.Sprintf("Go %s %s/%s", 
			r.info.GoVersion, r.info.GOOS, r.info.GOARCH),
		ProcessPID: int32(r.info.PID),
		GoMaxProcs: r.info.NumCPU,
		GoNumGoroutine: r.info.NumGoroutine,
	}

	// Process information
	if exe, err := os.Executable(); err == nil {
		attrs.ProcessExecutablePath = exe
		attrs.ProcessExecutableName = filepath.Base(exe)
	}

	// Command line
	if len(os.Args) > 0 {
		attrs.ProcessCommand = os.Args[0]
		attrs.ProcessCommandLine = strings.Join(os.Args, " ")
	}

	// Memory limit
	memLimit := GetGOMEMLIMIT()
	if memLimit.Enabled {
		attrs.GoMemoryLimit = memLimit.Current
	}

	return attrs
}

// ExportMap exports runtime information as a map for OpenTelemetry resource.
func (r *ResourceExporter) ExportMap() map[string]string {
	attrs := r.Export()
	result := make(map[string]string)

	// Process attributes (semantic conventions)
	if attrs.ProcessPID > 0 {
		result["process.pid"] = fmt.Sprintf("%d", attrs.ProcessPID)
	}
	if attrs.ProcessExecutableName != "" {
		result["process.executable.name"] = attrs.ProcessExecutableName
	}
	if attrs.ProcessExecutablePath != "" {
		result["process.executable.path"] = attrs.ProcessExecutablePath
	}
	if attrs.ProcessCommand != "" {
		result["process.command"] = attrs.ProcessCommand
	}
	if attrs.ProcessCommandLine != "" {
		result["process.command_line"] = attrs.ProcessCommandLine
	}
	if attrs.ProcessOwner != "" {
		result["process.owner"] = attrs.ProcessOwner
	}

	// Runtime attributes
	result["runtime.name"] = attrs.RuntimeName
	result["runtime.version"] = attrs.RuntimeVersion
	if attrs.RuntimeDescription != "" {
		result["runtime.description"] = attrs.RuntimeDescription
	}

	// Go-specific attributes
	result["go.maxprocs"] = fmt.Sprintf("%d", attrs.GoMaxProcs)
	result["go.numgoroutine"] = fmt.Sprintf("%d", attrs.GoNumGoroutine)
	if attrs.GoMemoryLimit > 0 {
		result["go.memlimit"] = fmt.Sprintf("%d", attrs.GoMemoryLimit)
	}

	// Build info
	if r.buildInfo != nil {
		if r.buildInfo.Path != "" {
			result["go.build.path"] = r.buildInfo.Path
		}
		if r.buildInfo.Version != "" {
			result["go.build.version"] = r.buildInfo.Version
		}
		if r.buildInfo.Revision != "" {
			result["go.build.revision"] = r.buildInfo.Revision
		}
		if r.buildInfo.Time != "" {
			result["go.build.time"] = r.buildInfo.Time
		}
	}

	// Environment variables
	if r.includeEnv {
		r.addEnvVars(result)
	}

	return result
}

// addEnvVars adds environment variables to the map.
func (r *ResourceExporter) addEnvVars(result map[string]string) {
	if len(r.envVars) == 0 {
		// Add all OTEL_ variables
		for _, env := range os.Environ() {
			if strings.HasPrefix(env, "OTEL_") {
				parts := strings.SplitN(env, "=", 2)
				if len(parts) == 2 {
					key := "env." + strings.ToLower(strings.ReplaceAll(parts[0], "_", "."))
					result[key] = parts[1]
				}
			}
		}
	} else {
		for _, name := range r.envVars {
			if value := os.Getenv(name); value != "" {
				key := "env." + strings.ToLower(strings.ReplaceAll(name, "_", "."))
				result[key] = value
			}
		}
	}
}

// GetResourceAttributes returns standard OpenTelemetry resource attributes.
func GetResourceAttributes() *ResourceAttributes {
	return NewResourceExporter().Export()
}

// GetResourceAttributeMap returns resource attributes as a map.
func GetResourceAttributeMap() map[string]string {
	return NewResourceExporter().ExportMap()
}

// GetResourceAttributeMapWithEnv returns resource attributes including OTEL_ env vars.
func GetResourceAttributeMapWithEnv() map[string]string {
	return NewResourceExporter(WithAllEnvVars()).ExportMap()
}

// ResourceDetector implements OpenTelemetry resource detection.
type ResourceDetector struct {
	exporter *ResourceExporter
}

// NewResourceDetector creates a new resource detector.
func NewResourceDetector(opts ...ResourceOption) *ResourceDetector {
	return &ResourceDetector{
		exporter: NewResourceExporter(opts...),
	}
}

// Detect detects and returns resource attributes.
func (d *ResourceDetector) Detect() (*ResourceAttributes, error) {
	attrs := d.exporter.Export()
	if attrs.RuntimeName == "" {
		return nil, fmt.Errorf("failed to detect runtime")
	}
	return attrs, nil
}

// String returns string representation of ResourceAttributes.
func (r *ResourceAttributes) String() string {
	return fmt.Sprintf(
		"ResourceAttributes{Runtime: %s %s, PID: %d, MaxProcs: %d}",
		r.RuntimeName, r.RuntimeVersion, r.ProcessPID, r.GoMaxProcs,
	)
}

// ToMap converts ResourceAttributes to a map.
func (r *ResourceAttributes) ToMap() map[string]interface{} {
	return map[string]interface{}{
		"process.pid":              r.ProcessPID,
		"process.executable.name":  r.ProcessExecutableName,
		"process.executable.path":  r.ProcessExecutablePath,
		"process.command":          r.ProcessCommand,
		"process.command_line":     r.ProcessCommandLine,
		"process.owner":            r.ProcessOwner,
		"runtime.name":             r.RuntimeName,
		"runtime.version":          r.RuntimeVersion,
		"runtime.description":      r.RuntimeDescription,
		"go.maxprocs":              r.GoMaxProcs,
		"go.numgoroutine":          r.GoNumGoroutine,
		"go.memlimit":              r.GoMemoryLimit,
	}
}

// MergeResourceAttributes merges multiple resource attributes.
// Later attributes override earlier ones.
func MergeResourceAttributes(attrs ...*ResourceAttributes) *ResourceAttributes {
	if len(attrs) == 0 {
		return &ResourceAttributes{}
	}

	result := &ResourceAttributes{}
	for _, attr := range attrs {
		if attr == nil {
			continue
		}

		if attr.ProcessPID > 0 {
			result.ProcessPID = attr.ProcessPID
		}
		if attr.ProcessExecutableName != "" {
			result.ProcessExecutableName = attr.ProcessExecutableName
		}
		if attr.ProcessExecutablePath != "" {
			result.ProcessExecutablePath = attr.ProcessExecutablePath
		}
		if attr.ProcessCommand != "" {
			result.ProcessCommand = attr.ProcessCommand
		}
		if attr.ProcessCommandLine != "" {
			result.ProcessCommandLine = attr.ProcessCommandLine
		}
		if attr.ProcessOwner != "" {
			result.ProcessOwner = attr.ProcessOwner
		}
		if attr.RuntimeName != "" {
			result.RuntimeName = attr.RuntimeName
		}
		if attr.RuntimeVersion != "" {
			result.RuntimeVersion = attr.RuntimeVersion
		}
		if attr.RuntimeDescription != "" {
			result.RuntimeDescription = attr.RuntimeDescription
		}
		if attr.GoMaxProcs > 0 {
			result.GoMaxProcs = attr.GoMaxProcs
		}
		if attr.GoNumGoroutine > 0 {
			result.GoNumGoroutine = attr.GoNumGoroutine
		}
		if attr.GoMemoryLimit > 0 {
			result.GoMemoryLimit = attr.GoMemoryLimit
		}
	}

	return result
}

// ProcessInfo holds information about the current process.
type ProcessInfo struct {
	PID            int32
	PPID           int32
	Name           string
	Executable     string
	CWD            string
	Environment    map[string]string
}

// GetProcessInfo returns information about the current process.
func GetProcessInfo() *ProcessInfo {
	info := &ProcessInfo{
		PID:         int32(os.Getpid()),
		Environment: make(map[string]string),
	}

	if exe, err := os.Executable(); err == nil {
		info.Executable = exe
		info.Name = filepath.Base(exe)
	}

	if cwd, err := os.Getwd(); err == nil {
		info.CWD = cwd
	}

	// Get specific environment variables
	for _, key := range []string{"HOME", "USER", "HOSTNAME", "PATH"} {
		if val := os.Getenv(key); val != "" {
			info.Environment[key] = val
		}
	}

	return info
}

// String returns string representation of ProcessInfo.
func (p *ProcessInfo) String() string {
	return fmt.Sprintf("ProcessInfo{PID: %d, Name: %s, Executable: %s}",
		p.PID, p.Name, p.Executable)
}

// GetGoRoot returns the GOROOT.
func GetGoRoot() string {
	return runtime.GOROOT()
}

// GetGoPath returns the GOPATH.
func GetGoPath() string {
	return os.Getenv("GOPATH")
}

// GetModulePath returns the main module path from build info.
func GetModulePath() string {
	if info := GetBuildInfo(); info != nil {
		return info.Path
	}
	return ""
}

// GetModuleVersion returns the main module version from build info.
func GetModuleVersion() string {
	if info := GetBuildInfo(); info != nil {
		return info.Version
	}
	return ""
}

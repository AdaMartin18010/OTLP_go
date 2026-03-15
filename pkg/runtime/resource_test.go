// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
package runtime

import (
	"runtime"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestResourceAttributesExport tests exporting resource attributes.
func TestResourceAttributesExport(t *testing.T) {
	exporter := NewResourceExporter()
	attrs := exporter.Export()

	require.NotNil(t, attrs)
	assert.Equal(t, "go", attrs.RuntimeName)
	assert.NotEmpty(t, attrs.RuntimeVersion)
	assert.NotEmpty(t, attrs.RuntimeDescription)
	assert.Greater(t, attrs.ProcessPID, int32(0))
	assert.Greater(t, attrs.GoMaxProcs, 0)
	assert.GreaterOrEqual(t, attrs.GoNumGoroutine, 1)
}

// TestResourceAttributesExportMap tests exporting resource attributes as map.
func TestResourceAttributesExportMap(t *testing.T) {
	exporter := NewResourceExporter()
	m := exporter.ExportMap()

	require.NotNil(t, m)
	assert.Contains(t, m, "runtime.name")
	assert.Equal(t, "go", m["runtime.name"])
	assert.Contains(t, m, "runtime.version")
	assert.Contains(t, m, "runtime.description")
	assert.Contains(t, m, "process.pid")
	assert.Contains(t, m, "go.maxprocs")
	assert.Contains(t, m, "go.numgoroutine")
}

// TestResourceExporterWithEnvVars tests exporter with specific env vars.
func TestResourceExporterWithEnvVars(t *testing.T) {
	// Set test env vars
	t.Setenv("OTEL_TEST_VAR", "test_value")
	t.Setenv("OTEL_OTHER_VAR", "other_value")

	exporter := NewResourceExporter(WithEnvVars("OTEL_TEST_VAR"))
	m := exporter.ExportMap()

	assert.Contains(t, m, "env.otel.test.var")
	assert.Equal(t, "test_value", m["env.otel.test.var"])
	assert.NotContains(t, m, "env.otel.other.var")
}

// TestResourceExporterWithAllEnvVars tests exporter with all OTEL_ env vars.
func TestResourceExporterWithAllEnvVars(t *testing.T) {
	// Set test env vars
	t.Setenv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317")
	t.Setenv("OTEL_SERVICE_NAME", "test-service")

	exporter := NewResourceExporter(WithAllEnvVars())
	m := exporter.ExportMap()

	assert.Contains(t, m, "env.otel.exporter.otlp.endpoint")
	assert.Contains(t, m, "env.otel.service.name")
	assert.Equal(t, "http://localhost:4317", m["env.otel.exporter.otlp.endpoint"])
	assert.Equal(t, "test-service", m["env.otel.service.name"])
}

// TestGetResourceAttributes tests getting resource attributes.
func TestGetResourceAttributes(t *testing.T) {
	attrs := GetResourceAttributes()

	require.NotNil(t, attrs)
	assert.Equal(t, "go", attrs.RuntimeName)
	assert.NotEmpty(t, attrs.RuntimeVersion)
}

// TestGetResourceAttributeMap tests getting resource attribute map.
func TestGetResourceAttributeMap(t *testing.T) {
	m := GetResourceAttributeMap()

	require.NotNil(t, m)
	assert.Contains(t, m, "runtime.name")
	assert.Contains(t, m, "runtime.version")
}

// TestGetResourceAttributeMapWithEnv tests getting resource attributes with env.
func TestGetResourceAttributeMapWithEnv(t *testing.T) {
	t.Setenv("OTEL_TEST", "value")

	m := GetResourceAttributeMapWithEnv()
	require.NotNil(t, m)
	assert.Contains(t, m, "env.otel.test")
}

// TestResourceDetector tests resource detection.
func TestResourceDetector(t *testing.T) {
	detector := NewResourceDetector()
	attrs, err := detector.Detect()

	require.NoError(t, err)
	require.NotNil(t, attrs)
	assert.Equal(t, "go", attrs.RuntimeName)
	assert.NotEmpty(t, attrs.RuntimeVersion)
}

// TestResourceAttributesToMap tests converting attributes to map.
func TestResourceAttributesToMap(t *testing.T) {
	attrs := &ResourceAttributes{
		ProcessPID:             1234,
		ProcessExecutableName:  "test",
		RuntimeName:            "go",
		RuntimeVersion:         "go1.26",
		RuntimeDescription:     "Test runtime",
		GoMaxProcs:             8,
		GoNumGoroutine:         10,
		GoMemoryLimit:          1073741824,
	}

	m := attrs.ToMap()

	assert.Equal(t, int32(1234), m["process.pid"])
	assert.Equal(t, "test", m["process.executable.name"])
	assert.Equal(t, "go", m["runtime.name"])
	assert.Equal(t, "go1.26", m["runtime.version"])
	assert.Equal(t, "Test runtime", m["runtime.description"])
	assert.Equal(t, 8, m["go.maxprocs"])
	assert.Equal(t, 10, m["go.numgoroutine"])
	assert.Equal(t, int64(1073741824), m["go.memlimit"])
}

// TestResourceAttributesString tests ResourceAttributes string representation.
func TestResourceAttributesString(t *testing.T) {
	attrs := &ResourceAttributes{
		RuntimeName:    "go",
		RuntimeVersion: "go1.26",
		ProcessPID:     1234,
		GoMaxProcs:     8,
	}

	s := attrs.String()
	assert.Contains(t, s, "go")
	assert.Contains(t, s, "go1.26")
	assert.Contains(t, s, "PID: 1234")
	assert.Contains(t, s, "MaxProcs: 8")
}

// TestMergeResourceAttributes tests merging resource attributes.
func TestMergeResourceAttributes(t *testing.T) {
	attrs1 := &ResourceAttributes{
		RuntimeName:    "go",
		RuntimeVersion: "go1.25",
		ProcessPID:     1234,
		GoMaxProcs:     4,
	}

	attrs2 := &ResourceAttributes{
		RuntimeVersion: "go1.26",
		GoMaxProcs:     8,
		GoNumGoroutine: 10,
	}

	merged := MergeResourceAttributes(attrs1, attrs2)

	assert.Equal(t, "go", merged.RuntimeName)        // From attrs1
	assert.Equal(t, "go1.26", merged.RuntimeVersion) // From attrs2 (override)
	assert.Equal(t, int32(1234), merged.ProcessPID)  // From attrs1
	assert.Equal(t, 8, merged.GoMaxProcs)            // From attrs2 (override)
	assert.Equal(t, 10, merged.GoNumGoroutine)       // From attrs2
}

// TestMergeResourceAttributesEmpty tests merging empty attributes.
func TestMergeResourceAttributesEmpty(t *testing.T) {
	merged := MergeResourceAttributes()
	assert.NotNil(t, merged)
	assert.Equal(t, &ResourceAttributes{}, merged)

	merged = MergeResourceAttributes(nil)
	assert.NotNil(t, merged)
	assert.Equal(t, &ResourceAttributes{}, merged)
}

// TestMergeResourceAttributesWithNil tests merging with nil attributes.
func TestMergeResourceAttributesWithNil(t *testing.T) {
	attrs := &ResourceAttributes{
		RuntimeName: "go",
	}

	merged := MergeResourceAttributes(attrs, nil)

	assert.Equal(t, "go", merged.RuntimeName)
}

// TestGetProcessInfo tests getting process information.
func TestGetProcessInfo(t *testing.T) {
	info := GetProcessInfo()

	require.NotNil(t, info)
	assert.Greater(t, info.PID, int32(0))
	assert.NotEmpty(t, info.Executable)
	assert.NotEmpty(t, info.Name)
	assert.NotEmpty(t, info.CWD)
}

// TestProcessInfoString tests ProcessInfo string representation.
func TestProcessInfoString(t *testing.T) {
	info := &ProcessInfo{
		PID:        1234,
		Name:       "test",
		Executable: "/path/to/test",
	}

	s := info.String()
	assert.Contains(t, s, "PID: 1234")
	assert.Contains(t, s, "Name: test")
	assert.Contains(t, s, "/path/to/test")
}

// TestGetGoRoot tests getting GOROOT.
func TestGetGoRoot(t *testing.T) {
	goroot := GetGoRoot()
	assert.NotEmpty(t, goroot)
	assert.True(t, strings.HasSuffix(goroot, runtime.Version()) || strings.Contains(goroot, "go"))
}

// TestGetGoPath tests getting GOPATH.
func TestGetGoPath(t *testing.T) {
	// GOPATH may be empty in module mode
	_ = GetGoPath()
	// Just ensure it doesn't panic
}

// TestGetModulePath tests getting module path.
func TestGetModulePath(t *testing.T) {
	// May be empty in test environment
	_ = GetModulePath()
	// Just ensure it doesn't panic
}

// TestGetModuleVersion tests getting module version.
func TestGetModuleVersion(t *testing.T) {
	// May be empty in test environment
	_ = GetModuleVersion()
	// Just ensure it doesn't panic
}

// TestResourceExporterWithBuildInfo tests exporter with build info.
func TestResourceExporterWithBuildInfo(t *testing.T) {
	exporter := NewResourceExporter()
	m := exporter.ExportMap()

	// Build info may not be available in test environment
	if GetBuildInfo() != nil {
		// At least some fields should be present if build info is available
		assert.True(t, m["go.build.path"] != "" || m["go.build.version"] != "" ||
			m["go.build.revision"] != "" || m["go.build.time"] != "")
	}
}

// TestResourceExporterMemoryLimit tests exporter with memory limit.
func TestResourceExporterMemoryLimit(t *testing.T) {
	// Set a memory limit
	original := GetGOMEMLIMIT().Current
	SetGOMEMLIMIT(512 * 1024 * 1024)
	defer SetGOMEMLIMIT(original)

	exporter := NewResourceExporter()
	attrs := exporter.Export()

	assert.Equal(t, int64(512*1024*1024), attrs.GoMemoryLimit)

	m := exporter.ExportMap()
	assert.Contains(t, m, "go.memlimit")
	assert.Equal(t, "536870912", m["go.memlimit"])
}

// BenchmarkResourceAttributesExport benchmarks exporting resource attributes.
func BenchmarkResourceAttributesExport(b *testing.B) {
	exporter := NewResourceExporter()
	for i := 0; i < b.N; i++ {
		_ = exporter.Export()
	}
}

// BenchmarkResourceAttributesExportMap benchmarks exporting as map.
func BenchmarkResourceAttributesExportMap(b *testing.B) {
	exporter := NewResourceExporter()
	for i := 0; i < b.N; i++ {
		_ = exporter.ExportMap()
	}
}

// BenchmarkGetResourceAttributeMap benchmarks getting resource attribute map.
func BenchmarkGetResourceAttributeMap(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetResourceAttributeMap()
	}
}

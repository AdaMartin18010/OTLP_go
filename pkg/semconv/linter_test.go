package semconv

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewLinter(t *testing.T) {
	l := NewLinter()
	assert.NotNil(t, l)
	assert.NotEmpty(t, l.rules)
}

func TestNewLinterWithRules(t *testing.T) {
	custom := map[string]string{
		"custom.key": "CustomConstant",
	}
	l := NewLinterWithRules(custom)
	assert.Equal(t, custom, l.rules)
}

func TestLinterAddRule(t *testing.T) {
	l := NewLinter()
	l.AddRule("new.key", "NewConstant")
	assert.Equal(t, "NewConstant", l.rules["new.key"])
}

func TestViolationString(t *testing.T) {
	v := Violation{
		File:       "test.go",
		Line:       10,
		Column:     5,
		Literal:    "http.method",
		Suggestion: "semconv.AttributeKeyHTTPMethod",
	}
	assert.Contains(t, v.String(), "test.go:10:5")
	assert.Contains(t, v.String(), "semconv.AttributeKeyHTTPMethod")
	assert.Contains(t, v.String(), "http.method")
}

func TestLinterScanFile(t *testing.T) {
	tmpDir := t.TempDir()
	goFile := filepath.Join(tmpDir, "example.go")

	content := `package example

import "fmt"

func main() {
	_ = "http.request.method"
	_ = "db.system"
	_ = "unknown.key"
	_ = "regular string"
}
`
	require.NoError(t, os.WriteFile(goFile, []byte(content), 0644))

	l := NewLinter()
	violations, err := l.ScanFile(goFile)
	require.NoError(t, err)
	assert.Len(t, violations, 2)

	literals := make(map[string]bool)
	for _, v := range violations {
		literals[v.Literal] = true
	}
	assert.True(t, literals["http.request.method"])
	assert.True(t, literals["db.system"])
}

func TestLinterScanFileNoViolations(t *testing.T) {
	tmpDir := t.TempDir()
	goFile := filepath.Join(tmpDir, "clean.go")

	content := `package clean

func main() {
	_ = "some random string"
}
`
	require.NoError(t, os.WriteFile(goFile, []byte(content), 0644))

	l := NewLinter()
	violations, err := l.ScanFile(goFile)
	require.NoError(t, err)
	assert.Empty(t, violations)
}

func TestLinterScanFileNotFound(t *testing.T) {
	l := NewLinter()
	_, err := l.ScanFile("/nonexistent/file.go")
	assert.Error(t, err)
}

func TestLinterScanDir(t *testing.T) {
	tmpDir := t.TempDir()

	content := `package example
func main() {
	_ = "http.request.method"
}
`
	require.NoError(t, os.WriteFile(filepath.Join(tmpDir, "a.go"), []byte(content), 0644))
	require.NoError(t, os.WriteFile(filepath.Join(tmpDir, "b.go"), []byte(content), 0644))

	l := NewLinter()
	violations, err := l.ScanDir(tmpDir)
	require.NoError(t, err)
	assert.Len(t, violations, 2)
}

func TestLinterScanDirNested(t *testing.T) {
	tmpDir := t.TempDir()
	subDir := filepath.Join(tmpDir, "sub")
	require.NoError(t, os.MkdirAll(subDir, 0755))

	content := `package example
func main() {
	_ = "db.system"
}
`
	require.NoError(t, os.WriteFile(filepath.Join(subDir, "nested.go"), []byte(content), 0644))

	l := NewLinter()
	violations, err := l.ScanDir(tmpDir)
	require.NoError(t, err)
	assert.Len(t, violations, 1)
}

func TestRunWithFile(t *testing.T) {
	tmpDir := t.TempDir()
	goFile := filepath.Join(tmpDir, "main.go")

	content := `package main
func main() {
	_ = "http.request.method"
}
`
	require.NoError(t, os.WriteFile(goFile, []byte(content), 0644))

	found, err := Run(goFile)
	require.NoError(t, err)
	assert.True(t, found)
}

func TestRunWithDir(t *testing.T) {
	tmpDir := t.TempDir()
	goFile := filepath.Join(tmpDir, "main.go")

	content := `package main
func main() {
	_ = "db.system"
}
`
	require.NoError(t, os.WriteFile(goFile, []byte(content), 0644))

	found, err := Run(tmpDir)
	require.NoError(t, err)
	assert.True(t, found)
}

func TestRunClean(t *testing.T) {
	tmpDir := t.TempDir()
	goFile := filepath.Join(tmpDir, "clean.go")

	content := `package clean
func main() {
	_ = "no violations here"
}
`
	require.NoError(t, os.WriteFile(goFile, []byte(content), 0644))

	found, err := Run(goFile)
	require.NoError(t, err)
	assert.False(t, found)
}

func TestRunInvalidPath(t *testing.T) {
	_, err := Run("/nonexistent/path")
	assert.Error(t, err)
}

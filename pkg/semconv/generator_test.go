package semconv

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewGenerator(t *testing.T) {
	g := NewGenerator()
	assert.NotNil(t, g)
}

func TestToGoConstName(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"http.request.method", "AttributeKeyHTTPRequestMethod"},
		{"db.system", "AttributeKeyDBSystem"},
		{"rpc.grpc.status_code", "AttributeKeyRPCGRPCStatusCode"},
		{"gen_ai.system", "AttributeKeyGenAISystem"},
		{"service.instance.id", "AttributeKeyServiceInstanceID"},
		{"messaging.destination.name", "AttributeKeyMessagingDestinationName"},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			assert.Equal(t, tt.expected, toGoConstName(tt.input))
		})
	}
}

func TestToPascalCase(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"method", "Method"},
		{"status_code", "StatusCode"},
		{"instance-id", "InstanceID"},
		{"", ""},
	}

	for _, tt := range tests {
		t.Run(tt.input, func(t *testing.T) {
			assert.Equal(t, tt.expected, toPascalCase(tt.input))
		})
	}
}

func TestGoTypeForAttr(t *testing.T) {
	assert.Equal(t, "string", goTypeForAttr(TypeString))
	assert.Equal(t, "int64", goTypeForAttr(TypeInt))
	assert.Equal(t, "int64", goTypeForAttr(TypeInt64))
	assert.Equal(t, "float64", goTypeForAttr(TypeFloat64))
	assert.Equal(t, "bool", goTypeForAttr(TypeBool))
	assert.Equal(t, "string", goTypeForAttr(AttributeType("unknown")))
}

func TestGoMethodForAttr(t *testing.T) {
	assert.Equal(t, "String", goMethodForAttr(TypeString))
	assert.Equal(t, "Int", goMethodForAttr(TypeInt))
	assert.Equal(t, "Int64", goMethodForAttr(TypeInt64))
	assert.Equal(t, "Float64", goMethodForAttr(TypeFloat64))
	assert.Equal(t, "Bool", goMethodForAttr(TypeBool))
	assert.Equal(t, "String", goMethodForAttr(AttributeType("unknown")))
}

func TestGoZeroValue(t *testing.T) {
	assert.Equal(t, `""`, goZeroValue(TypeString))
	assert.Equal(t, "0", goZeroValue(TypeInt))
	assert.Equal(t, "0", goZeroValue(TypeInt64))
	assert.Equal(t, "0.0", goZeroValue(TypeFloat64))
	assert.Equal(t, "false", goZeroValue(TypeBool))
	assert.Equal(t, `""`, goZeroValue(AttributeType("unknown")))
}

func TestGeneratorGenerate(t *testing.T) {
	g := NewGenerator()

	spec := DomainSpec{
		Domain:  "HTTP",
		Package: "semconv",
		Attributes: []AttributeSpec{
			{
				Name:        "HTTPMethod",
				Key:         "http.request.method",
				Description: "HTTP request method",
				Type:        TypeString,
			},
			{
				Name:        "HTTPStatusCode",
				Key:         "http.response.status_code",
				Description: "HTTP response status code",
				Type:        TypeInt,
			},
		},
	}

	code, err := g.Generate(spec)
	require.NoError(t, err)
	assert.Contains(t, string(code), "package semconv")
	assert.Contains(t, string(code), `AttributeKeyHTTPRequestMethod = attribute.Key("http.request.method")`)
	assert.Contains(t, string(code), `AttributeKeyHTTPResponseStatusCode = attribute.Key("http.response.status_code")`)
	assert.Contains(t, string(code), "func HTTPRequestMethod(val string) attribute.KeyValue")
	assert.Contains(t, string(code), "func HTTPResponseStatusCode(val int64) attribute.KeyValue")
}

func TestGeneratorGenerateFromJSON(t *testing.T) {
	tmpDir := t.TempDir()
	jsonPath := filepath.Join(tmpDir, "spec.json")

	jsonContent := `{
		"domain": "Test",
		"package": "testpkg",
		"attributes": [
			{"name": "TestAttr", "key": "test.attr", "type": "string"}
		]
	}`
	require.NoError(t, os.WriteFile(jsonPath, []byte(jsonContent), 0644))

	g := NewGenerator()
	code, err := g.GenerateFromJSON(jsonPath)
	require.NoError(t, err)
	assert.Contains(t, string(code), "package testpkg")
	assert.Contains(t, string(code), `AttributeKeyTestAttr = attribute.Key("test.attr")`)
}

func TestGeneratorGenerateFromYAML(t *testing.T) {
	tmpDir := t.TempDir()
	yamlPath := filepath.Join(tmpDir, "spec.yaml")

	yamlContent := `domain: Test
package: testpkg
attributes:
  - name: TestAttr
    key: test.attr
    type: string
`
	require.NoError(t, os.WriteFile(yamlPath, []byte(yamlContent), 0644))

	g := NewGenerator()
	code, err := g.GenerateFromYAML(yamlPath)
	require.NoError(t, err)
	assert.Contains(t, string(code), "package testpkg")
	assert.Contains(t, string(code), `AttributeKeyTestAttr = attribute.Key("test.attr")`)
}

func TestGeneratorGenerateMissingFile(t *testing.T) {
	g := NewGenerator()
	_, err := g.GenerateFromJSON("/nonexistent/path/spec.json")
	assert.Error(t, err)
}

func TestGeneratorGenerateDeterministic(t *testing.T) {
	g := NewGenerator()

	spec := DomainSpec{
		Domain: "RPC",
		Attributes: []AttributeSpec{
			{Name: "RPCMethod", Key: "rpc.method", Type: TypeString},
			{Name: "RPCSystem", Key: "rpc.system", Type: TypeString},
		},
	}

	code1, err := g.Generate(spec)
	require.NoError(t, err)
	code2, err := g.Generate(spec)
	require.NoError(t, err)
	assert.Equal(t, string(code1), string(code2))
}

func TestGeneratorGenerateDefaultPackage(t *testing.T) {
	g := NewGenerator()

	spec := DomainSpec{
		Domain: "Empty",
		Attributes: []AttributeSpec{
			{Name: "EmptyAttr", Key: "empty.attr", Type: TypeString},
		},
	}

	code, err := g.Generate(spec)
	require.NoError(t, err)
	assert.True(t, strings.Contains(string(code), "package semconv"))
}

// Package semconv provides OpenTelemetry semantic convention attributes and tools.
package semconv

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/format"
	"os"
	"sort"
	"strings"
	"text/template"
	"unicode"

	"gopkg.in/yaml.v3"
)

// AttributeType describes the type of an attribute value.
type AttributeType string

const (
	// TypeString represents a string attribute type.
	TypeString AttributeType = "string"
	// TypeInt represents an int attribute type.
	TypeInt AttributeType = "int"
	// TypeInt64 represents an int64 attribute type.
	TypeInt64 AttributeType = "int64"
	// TypeFloat64 represents a float64 attribute type.
	TypeFloat64 AttributeType = "float64"
	// TypeBool represents a bool attribute type.
	TypeBool AttributeType = "bool"
)

// AttributeSpec defines a single semantic convention attribute.
type AttributeSpec struct {
	Name             string        `json:"name" yaml:"name"`
	Key              string        `json:"key" yaml:"key"`
	Description      string        `json:"description" yaml:"description"`
	Type             AttributeType `json:"type" yaml:"type"`
	RequirementLevel string        `json:"requirement_level,omitempty" yaml:"requirement_level,omitempty"`
	Examples         []string      `json:"examples,omitempty" yaml:"examples,omitempty"`
}

// DomainSpec defines a domain of semantic conventions.
type DomainSpec struct {
	Domain     string          `json:"domain" yaml:"domain"`
	Package    string          `json:"package" yaml:"package"`
	Attributes []AttributeSpec `json:"attributes" yaml:"attributes"`
}

// Generator generates Go code from semantic convention specifications.
type Generator struct {
	tmpl *template.Template
}

// NewGenerator creates a new semantic convention code generator.
func NewGenerator() *Generator {
	funcMap := template.FuncMap{
		"goConstName": toGoConstName,
		"goType":      goTypeForAttr,
		"goMethod":    goMethodForAttr,
		"goZero":      goZeroValue,
		"trimPrefix":  func(prefix, s string) string { return strings.TrimPrefix(s, prefix) },
	}
	tmpl := template.Must(template.New("semconv").Funcs(funcMap).Parse(codeTemplate))
	return &Generator{tmpl: tmpl}
}

// GenerateFromYAML reads a YAML spec and generates formatted Go code.
func (g *Generator) GenerateFromYAML(path string) ([]byte, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read yaml file: %w", err)
	}

	var spec DomainSpec
	if err := yaml.Unmarshal(data, &spec); err != nil {
		return nil, fmt.Errorf("unmarshal yaml: %w", err)
	}

	return g.Generate(spec)
}

// GenerateFromJSON reads a JSON spec and generates formatted Go code.
func (g *Generator) GenerateFromJSON(path string) ([]byte, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("read json file: %w", err)
	}

	var spec DomainSpec
	if err := json.Unmarshal(data, &spec); err != nil {
		return nil, fmt.Errorf("unmarshal json: %w", err)
	}

	return g.Generate(spec)
}

// Generate produces formatted Go source code from a DomainSpec.
func (g *Generator) Generate(spec DomainSpec) ([]byte, error) {
	if spec.Package == "" {
		spec.Package = "semconv"
	}

	// Sort attributes by key for deterministic output
	sort.Slice(spec.Attributes, func(i, j int) bool {
		return spec.Attributes[i].Key < spec.Attributes[j].Key
	})

	var buf bytes.Buffer
	if err := g.tmpl.Execute(&buf, spec); err != nil {
		return nil, fmt.Errorf("execute template: %w", err)
	}

	formatted, err := format.Source(buf.Bytes())
	if err != nil {
		return buf.Bytes(), fmt.Errorf("format source: %w", err)
	}

	return formatted, nil
}

// toGoConstName converts a semantic convention key to a Go constant name.
// e.g., "http.request.method" -> "AttributeKeyHTTPMethod"
func toGoConstName(key string) string {
	parts := strings.Split(key, ".")
	var sb strings.Builder
	sb.WriteString("AttributeKey")
	for _, part := range parts {
		sb.WriteString(toPascalCase(part))
	}
	return sb.String()
}

// knownAcronyms maps lowercase words to their uppercase acronym forms.
var knownAcronyms = map[string]string{
	"http":   "HTTP",
	"https":  "HTTPS",
	"db":     "DB",
	"rpc":    "RPC",
	"grpc":   "GRPC",
	"ai":     "AI",
	"id":     "ID",
	"url":    "URL",
	"ecs":    "ECS",
	"eks":    "EKS",
	"gke":    "GKE",
	"aks":    "AKS",
	"vm":     "VM",
	"gce":    "GCE",
	"os":     "OS",
	"cpu":    "CPU",
	"sql":    "SQL",
	"k8s":    "K8s",
}

// toPascalCase converts a snake_case or kebab-case word to PascalCase.
func toPascalCase(s string) string {
	parts := strings.FieldsFunc(s, func(r rune) bool {
		return r == '_' || r == '-'
	})
	var sb strings.Builder
	for _, p := range parts {
		if p == "" {
			continue
		}
		if acronym, ok := knownAcronyms[strings.ToLower(p)]; ok {
			sb.WriteString(acronym)
			continue
		}
		runes := []rune(p)
		runes[0] = unicode.ToUpper(runes[0])
		sb.WriteString(string(runes))
	}
	return sb.String()
}

// goTypeForAttr returns the Go type string for an attribute type.
func goTypeForAttr(t AttributeType) string {
	switch t {
	case TypeString:
		return "string"
	case TypeInt, TypeInt64:
		return "int64"
	case TypeFloat64:
		return "float64"
	case TypeBool:
		return "bool"
	default:
		return "string"
	}
}

// goMethodForAttr returns the attribute.KeyValue method name for the type.
func goMethodForAttr(t AttributeType) string {
	switch t {
	case TypeString:
		return "String"
	case TypeInt:
		return "Int"
	case TypeInt64:
		return "Int64"
	case TypeFloat64:
		return "Float64"
	case TypeBool:
		return "Bool"
	default:
		return "String"
	}
}

// goZeroValue returns the zero value literal for the Go type.
func goZeroValue(t AttributeType) string {
	switch t {
	case TypeString:
		return `""`
	case TypeInt, TypeInt64:
		return "0"
	case TypeFloat64:
		return "0.0"
	case TypeBool:
		return "false"
	default:
		return `""`
	}
}

const codeTemplate = `// Code generated from semantic convention specification. DO NOT EDIT.

package {{.Package}}

import "go.opentelemetry.io/otel/attribute"

// {{.Domain}} semantic convention attribute keys.
const (
{{- range .Attributes }}
	// {{ .Key | goConstName }} is the attribute Key conforming to the
	// "{{ .Key }}" semantic convention.
	{{ .Key | goConstName }} = attribute.Key("{{ .Key }}")
{{- end }}
)

{{- range .Attributes }}

// {{ .Key | goConstName | trimPrefix "AttributeKey" }} returns an attribute KeyValue conforming to the
// "{{ .Key }}" semantic convention.
func {{ .Key | goConstName | trimPrefix "AttributeKey" }}(val {{ .Type | goType }}) attribute.KeyValue {
	return {{ .Key | goConstName }}.{{ .Type | goMethod }}(val)
}
{{- end }}
`

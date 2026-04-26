// Package semconv provides OpenTelemetry semantic convention attributes and tools.
package semconv

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
)

// defaultKnownAttributes maps hardcoded semantic convention attribute keys to
// their recommended constant names in the semconv package.
var defaultKnownAttributes = map[string]string{
	"http.request.method":        "semconv.AttributeKeyHTTPMethod",
	"http.response.status_code":  "semconv.AttributeKeyHTTPStatusCode",
	"http.route":                 "semconv.AttributeKeyHTTPRoute",
	"server.address":             "semconv.AttributeKeyServerAddress",
	"server.port":                "semconv.AttributeKeyServerPort",
	"db.system":                  "semconv.AttributeKeyDBSystem",
	"db.operation":               "semconv.AttributeKeyDBOperation",
	"db.sql.table":               "semconv.AttributeKeyDBSQLTable",
	"db.query.text":              "semconv.AttributeKeyDBQueryText",
	"db.name":                    "semconv.AttributeKeyDBName",
	"messaging.system":           "semconv.AttributeKeyMessagingSystem",
	"messaging.destination.name": "semconv.AttributeKeyMessagingDestinationName",
	"messaging.operation.type":   "semconv.AttributeKeyMessagingOperationType",
	"rpc.system":                 "semconv.AttributeKeyRPCSystem",
	"rpc.service":                "semconv.AttributeKeyRPCService",
	"rpc.method":                 "semconv.AttributeKeyRPCMethod",
	"rpc.grpc.status_code":       "semconv.AttributeKeyRPCGRPCStatusCode",
	"gen_ai.system":              "semconv.AttributeKeyGenAISystem",
	"gen_ai.request.model":       "semconv.AttributeKeyGenAIRequestModel",
	"gen_ai.usage.input_tokens":  "semconv.AttributeKeyGenAIUsageInputTokens",
	"gen_ai.usage.output_tokens": "semconv.AttributeKeyGenAIUsageOutputTokens",
	"service.name":               "semconv.AttributeKeyServiceName",
	"service.namespace":          "semconv.AttributeKeyServiceNamespace",
	"service.instance.id":        "semconv.AttributeKeyServiceInstanceID",
	"service.version":            "semconv.AttributeKeyServiceVersion",
	"deployment.environment":     "semconv.AttributeKeyDeploymentEnvironment",
	"system.cpu.time":            "semconv.AttributeKeySystemCPUTime",
	"system.memory.usage":        "semconv.AttributeKeySystemMemoryUsage",
	"system.disk.io":             "semconv.AttributeKeySystemDiskIO",
	"system.network.io":          "semconv.AttributeKeySystemNetworkIO",
	"cloud.provider":             "semconv.AttributeKeyCloudProvider",
	"cloud.region":               "semconv.AttributeKeyCloudRegion",
	"cloud.account.id":           "semconv.AttributeKeyCloudAccountID",
}

// Violation represents a hardcoded attribute string that should be replaced.
type Violation struct {
	File       string
	Line       int
	Column     int
	Literal    string
	Suggestion string
}

// String returns a formatted violation message.
func (v Violation) String() string {
	return fmt.Sprintf("%s:%d:%d: use %s instead of hardcoded %q", v.File, v.Line, v.Column, v.Suggestion, v.Literal)
}

// Linter scans Go source code for hardcoded semantic convention strings.
type Linter struct {
	rules map[string]string
}

// NewLinter creates a linter with the default known attribute rules.
func NewLinter() *Linter {
	rules := make(map[string]string, len(defaultKnownAttributes))
	for k, v := range defaultKnownAttributes {
		rules[k] = v
	}
	return &Linter{rules: rules}
}

// NewLinterWithRules creates a linter with custom rules.
func NewLinterWithRules(rules map[string]string) *Linter {
	return &Linter{rules: rules}
}

// AddRule adds or updates a linting rule.
func (l *Linter) AddRule(literal, suggestion string) {
	l.rules[literal] = suggestion
}

// ScanDir recursively scans all .go files in a directory for violations.
func (l *Linter) ScanDir(root string) ([]Violation, error) {
	var violations []Violation

	err := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}
		if info.IsDir() || !strings.HasSuffix(path, ".go") {
			return nil
		}
		fileViolations, err := l.ScanFile(path)
		if err != nil {
			return err
		}
		violations = append(violations, fileViolations...)
		return nil
	})

	return violations, err
}

// ScanFile scans a single Go file for hardcoded attribute strings.
func (l *Linter) ScanFile(path string) ([]Violation, error) {
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}

	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, src, parser.AllErrors)
	if err != nil {
		return nil, err
	}

	var violations []Violation
	ast.Inspect(f, func(n ast.Node) bool {
		lit, ok := n.(*ast.BasicLit)
		if !ok || lit.Kind != token.STRING {
			return true
		}

		value := strings.Trim(lit.Value, "`\"")
		if suggestion, found := l.rules[value]; found {
			pos := fset.Position(lit.Pos())
			violations = append(violations, Violation{
				File:       path,
				Line:       pos.Line,
				Column:     pos.Column,
				Literal:    value,
				Suggestion: suggestion,
			})
		}

		return true
	})

	return violations, nil
}

// Run is a convenience function to run the linter on paths and print results.
// Returns true if any violations were found.
func Run(paths ...string) (bool, error) {
	linter := NewLinter()
	var allViolations []Violation

	for _, path := range paths {
		info, err := os.Stat(path)
		if err != nil {
			return false, err
		}

		var violations []Violation
		if info.IsDir() {
			violations, err = linter.ScanDir(path)
		} else {
			violations, err = linter.ScanFile(path)
		}
		if err != nil {
			return false, err
		}
		allViolations = append(allViolations, violations...)
	}

	for _, v := range allViolations {
		fmt.Println(v.String())
	}

	return len(allViolations) > 0, nil
}

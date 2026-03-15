package resource

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestParseAttributesComplexCases(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected map[string]string
	}{
		{
			name:     "only commas",
			input:    ",,,",
			expected: map[string]string{},
		},
		{
			name:     "key without value",
			input:    "key1=,key2=value2",
			expected: map[string]string{"key1": "", "key2": "value2"},
		},
		{
			name:     "multiple equals signs",
			input:    "key=value=with=equals",
			expected: map[string]string{"key": "value=with=equals"},
		},
		{
			name:     "whitespace handling",
			input:    "  key1  =  value1  ,  key2  =  value2  ",
			expected: map[string]string{"key1": "value1", "key2": "value2"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := parseAttributes(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestParseAttributesMapInvalidJSON(t *testing.T) {
	// Invalid JSON should fall back to key=value format
	input := "key1=value1,key2=value2"
	result := parseAttributesMap(input)

	assert.Equal(t, "value1", result["key1"])
	assert.Equal(t, "value2", result["key2"])
}

func TestResourceAttributesEnvEmpty(t *testing.T) {
	env := &ResourceAttributesEnv{}
	res := env.ToResource()
	
	// Empty env should produce empty resource
	assert.True(t, res.IsEmpty())
}

func TestResourceAttributesEnvPartial(t *testing.T) {
	env := &ResourceAttributesEnv{
		ServiceName: "test-service",
		// Leave other fields empty
	}
	res := env.ToResource()
	
	assert.Equal(t, "test-service", res.GetString("service.name"))
	// Other attributes should not exist
	_, hasServiceVersion := res.Get("service.version")
	assert.False(t, hasServiceVersion)
}

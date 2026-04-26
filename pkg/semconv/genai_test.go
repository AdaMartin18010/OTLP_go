package semconv

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestGenAISystem(t *testing.T) {
	kv := GenAISystem("openai")
	assert.Equal(t, string(AttributeKeyGenAISystem), string(kv.Key))
	assert.Equal(t, "openai", kv.Value.AsString())
}

func TestGenAIRequestModel(t *testing.T) {
	kv := GenAIRequestModel("gpt-4")
	assert.Equal(t, string(AttributeKeyGenAIRequestModel), string(kv.Key))
	assert.Equal(t, "gpt-4", kv.Value.AsString())
}

func TestGenAIUsageInputTokens(t *testing.T) {
	kv := GenAIUsageInputTokens(100)
	assert.Equal(t, string(AttributeKeyGenAIUsageInputTokens), string(kv.Key))
	assert.Equal(t, int64(100), kv.Value.AsInt64())
}

func TestGenAIUsageOutputTokens(t *testing.T) {
	kv := GenAIUsageOutputTokens(50)
	assert.Equal(t, string(AttributeKeyGenAIUsageOutputTokens), string(kv.Key))
	assert.Equal(t, int64(50), kv.Value.AsInt64())
}

func TestGenAIResponseModel(t *testing.T) {
	kv := GenAIResponseModel("gpt-4-turbo")
	assert.Equal(t, string(AttributeKeyGenAIResponseModel), string(kv.Key))
	assert.Equal(t, "gpt-4-turbo", kv.Value.AsString())
}

func TestGenAIAttributes(t *testing.T) {
	attrs := GenAIAttributes("openai", "gpt-4", 100, 50)
	assert.Len(t, attrs, 4)

	m := make(map[string]interface{})
	for _, attr := range attrs {
		m[string(attr.Key)] = attr.Value.AsInterface()
	}

	assert.Equal(t, "openai", m["gen_ai.system"])
	assert.Equal(t, "gpt-4", m["gen_ai.request.model"])
	assert.Equal(t, int64(100), m["gen_ai.usage.input_tokens"])
	assert.Equal(t, int64(50), m["gen_ai.usage.output_tokens"])
}

func TestGenAIConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("gen_ai.system"), AttributeKeyGenAISystem)
	assert.Equal(t, attribute.Key("gen_ai.request.model"), AttributeKeyGenAIRequestModel)
	assert.Equal(t, attribute.Key("gen_ai.usage.input_tokens"), AttributeKeyGenAIUsageInputTokens)
	assert.Equal(t, attribute.Key("gen_ai.usage.output_tokens"), AttributeKeyGenAIUsageOutputTokens)
}

package semconv

import "go.opentelemetry.io/otel/attribute"

// Generative AI semantic convention attribute keys.
const (
	AttributeKeyGenAISystem            = attribute.Key("gen_ai.system")
	AttributeKeyGenAIRequestModel      = attribute.Key("gen_ai.request.model")
	AttributeKeyGenAIUsageInputTokens  = attribute.Key("gen_ai.usage.input_tokens")
	AttributeKeyGenAIUsageOutputTokens = attribute.Key("gen_ai.usage.output_tokens")
	AttributeKeyGenAIResponseModel     = attribute.Key("gen_ai.response.model")
)

// GenAISystem returns an attribute KeyValue conforming to the
// "gen_ai.system" semantic convention.
func GenAISystem(val string) attribute.KeyValue {
	return AttributeKeyGenAISystem.String(val)
}

// GenAIRequestModel returns an attribute KeyValue conforming to the
// "gen_ai.request.model" semantic convention.
func GenAIRequestModel(val string) attribute.KeyValue {
	return AttributeKeyGenAIRequestModel.String(val)
}

// GenAIUsageInputTokens returns an attribute KeyValue conforming to the
// "gen_ai.usage.input_tokens" semantic convention.
func GenAIUsageInputTokens(val int64) attribute.KeyValue {
	return AttributeKeyGenAIUsageInputTokens.Int64(val)
}

// GenAIUsageOutputTokens returns an attribute KeyValue conforming to the
// "gen_ai.usage.output_tokens" semantic convention.
func GenAIUsageOutputTokens(val int64) attribute.KeyValue {
	return AttributeKeyGenAIUsageOutputTokens.Int64(val)
}

// GenAIResponseModel returns an attribute KeyValue conforming to the
// "gen_ai.response.model" semantic convention.
func GenAIResponseModel(val string) attribute.KeyValue {
	return AttributeKeyGenAIResponseModel.String(val)
}

// GenAIAttributes returns GenAI attributes for the given system, model, and token usage.
func GenAIAttributes(system, model string, inputTokens, outputTokens int64) []attribute.KeyValue {
	return []attribute.KeyValue{
		GenAISystem(system),
		GenAIRequestModel(model),
		GenAIUsageInputTokens(inputTokens),
		GenAIUsageOutputTokens(outputTokens),
	}
}

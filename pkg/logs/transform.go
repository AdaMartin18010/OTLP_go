// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This file contains data transformation utilities for converting between
// internal LogRecord and OTLP protobuf-like formats.
package logs

import (
	"fmt"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

// ToOTLP converts a LogRecord to an OTLP-like map representation.
func ToOTLP(record LogRecord) map[string]interface{} {
	result := map[string]interface{}{
		"timestamp":          record.Timestamp.Format(time.RFC3339Nano),
		"observed_timestamp": record.ObservedTimestamp.Format(time.RFC3339Nano),
		"severity_number":    int32(record.SeverityNumber),
		"severity_text":      record.SeverityText,
		"body":               toOTLPValue(record.Body),
		"event_name":         record.EventName,
	}

	if record.TraceID.IsValid() {
		result["trace_id"] = record.TraceID.String()
	}
	if record.SpanID.IsValid() {
		result["span_id"] = record.SpanID.String()
	}
	if record.TraceFlags != 0 {
		result["trace_flags"] = byte(record.TraceFlags)
	}

	if len(record.Attributes) > 0 {
		attrs := make(map[string]interface{}, len(record.Attributes))
		for _, attr := range record.Attributes {
			attrs[string(attr.Key)] = attributeValueToInterface(attr.Value)
		}
		result["attributes"] = attrs
	}

	return result
}

// FromOTLP converts an OTLP-like map representation to a LogRecord.
func FromOTLP(data map[string]interface{}) LogRecord {
	record := LogRecord{}

	if v, ok := data["timestamp"].(string); ok {
		if t, err := time.Parse(time.RFC3339Nano, v); err == nil {
			record.Timestamp = t
		}
	}
	if v, ok := data["observed_timestamp"].(string); ok {
		if t, err := time.Parse(time.RFC3339Nano, v); err == nil {
			record.ObservedTimestamp = t
		}
	}
	if v, ok := data["severity_number"].(int32); ok {
		record.SeverityNumber = SeverityNumber(v)
	} else if v, ok := data["severity_number"].(int); ok {
		record.SeverityNumber = SeverityNumber(v)
	} else if v, ok := data["severity_number"].(float64); ok {
		record.SeverityNumber = SeverityNumber(int32(v))
	}
	if v, ok := data["severity_text"].(string); ok {
		record.SeverityText = v
	}
	if v, ok := data["body"]; ok {
		record.Body = fromOTLPValue(v)
	}
	if v, ok := data["event_name"].(string); ok {
		record.EventName = v
	}

	// Attributes
	if v, ok := data["attributes"].(map[string]interface{}); ok {
		for key, val := range v {
			record.Attributes = append(record.Attributes, interfaceToAttribute(key, val))
		}
	}

	return record
}

func toOTLPValue(v interface{}) interface{} {
	switch val := v.(type) {
	case string:
		return val
	case int:
		return int64(val)
	case int8:
		return int64(val)
	case int16:
		return int64(val)
	case int32:
		return int64(val)
	case int64:
		return val
	case uint:
		return int64(val)
	case uint8:
		return int64(val)
	case uint16:
		return int64(val)
	case uint32:
		return int64(val)
	case uint64:
		return int64(val)
	case float32:
		return float64(val)
	case float64:
		return val
	case bool:
		return val
	case []byte:
		return string(val)
	case []interface{}:
		arr := make([]interface{}, len(val))
		for i, item := range val {
			arr[i] = toOTLPValue(item)
		}
		return arr
	case map[string]interface{}:
		m := make(map[string]interface{}, len(val))
		for k, v := range val {
			m[k] = toOTLPValue(v)
		}
		return m
	case attribute.Value:
		return attributeValueToInterface(val)
	default:
		return fmt.Sprintf("%v", v)
	}
}

func fromOTLPValue(v interface{}) interface{} {
	return v
}

func attributeValueToInterface(v attribute.Value) interface{} {
	switch v.Type() {
	case attribute.BOOL:
		return v.AsBool()
	case attribute.INT64:
		return v.AsInt64()
	case attribute.FLOAT64:
		return v.AsFloat64()
	case attribute.STRING:
		return v.AsString()
	case attribute.BOOLSLICE:
		return v.AsBoolSlice()
	case attribute.INT64SLICE:
		return v.AsInt64Slice()
	case attribute.FLOAT64SLICE:
		return v.AsFloat64Slice()
	case attribute.STRINGSLICE:
		return v.AsStringSlice()
	default:
		return v.AsString()
	}
}

func interfaceToAttribute(key string, v interface{}) attribute.KeyValue {
	switch val := v.(type) {
	case bool:
		return attribute.Bool(key, val)
	case int:
		return attribute.Int64(key, int64(val))
	case int8:
		return attribute.Int64(key, int64(val))
	case int16:
		return attribute.Int64(key, int64(val))
	case int32:
		return attribute.Int64(key, int64(val))
	case int64:
		return attribute.Int64(key, val)
	case uint:
		return attribute.Int64(key, int64(val))
	case uint8:
		return attribute.Int64(key, int64(val))
	case uint16:
		return attribute.Int64(key, int64(val))
	case uint32:
		return attribute.Int64(key, int64(val))
	case uint64:
		return attribute.Int64(key, int64(val))
	case float32:
		return attribute.Float64(key, float64(val))
	case float64:
		return attribute.Float64(key, val)
	case string:
		return attribute.String(key, val)
	case []bool:
		return attribute.BoolSlice(key, val)
	case []int:
		return attribute.Int64Slice(key, convertIntSlice(val))
	case []int64:
		return attribute.Int64Slice(key, val)
	case []float64:
		return attribute.Float64Slice(key, val)
	case []string:
		return attribute.StringSlice(key, val)
	default:
		return attribute.String(key, fmt.Sprintf("%v", v))
	}
}

func convertIntSlice(vals []int) []int64 {
	result := make([]int64, len(vals))
	for i, v := range vals {
		result[i] = int64(v)
	}
	return result
}

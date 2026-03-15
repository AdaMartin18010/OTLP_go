// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This file contains log field types for structured logging.
package logs

import (
	"fmt"
	"math"
	"strconv"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

// FieldType represents the type of a log field.
type FieldType int

const (
	// UnknownType is an unknown field type.
	UnknownType FieldType = iota
	// BoolType is a boolean field.
	BoolType
	// Int64Type is an int64 field.
	Int64Type
	// Uint64Type is a uint64 field.
	Uint64Type
	// Float64Type is a float64 field.
	Float64Type
	// StringType is a string field.
	StringType
	// DurationType is a time.Duration field.
	DurationType
	// TimeType is a time.Time field.
	TimeType
	// ErrorType is an error field.
	ErrorType
	// AnyType is any type field (uses reflection).
	AnyType
)

// String returns the string representation of the field type.
func (t FieldType) String() string {
	switch t {
	case BoolType:
		return "bool"
	case Int64Type:
		return "int64"
	case Uint64Type:
		return "uint64"
	case Float64Type:
		return "float64"
	case StringType:
		return "string"
	case DurationType:
		return "duration"
	case TimeType:
		return "time"
	case ErrorType:
		return "error"
	case AnyType:
		return "any"
	default:
		return "unknown"
	}
}

// Field represents a structured log field.
type Field struct {
	Key   string
	Type  FieldType
	Value interface{}
}

// String returns a string representation of the field.
func (f Field) String() string {
	return fmt.Sprintf("%s=%v", f.Key, f.Value)
}

// ToAttribute converts the field to an OpenTelemetry attribute.
func (f Field) ToAttribute() attribute.KeyValue {
	switch f.Type {
	case BoolType:
		return attribute.Bool(f.Key, f.Value.(bool))
	case Int64Type:
		return attribute.Int64(f.Key, f.Value.(int64))
	case Uint64Type:
		return attribute.Int64(f.Key, int64(f.Value.(uint64)))
	case Float64Type:
		return attribute.Float64(f.Key, f.Value.(float64))
	case StringType:
		return attribute.String(f.Key, f.Value.(string))
	case DurationType:
		return attribute.String(f.Key, f.Value.(time.Duration).String())
	case TimeType:
		return attribute.String(f.Key, f.Value.(time.Time).Format(time.RFC3339Nano))
	case ErrorType:
		if err, ok := f.Value.(error); ok && err != nil {
			return attribute.String(f.Key, err.Error())
		}
		return attribute.String(f.Key, "null")
	default:
		return attribute.String(f.Key, fmt.Sprintf("%v", f.Value))
	}
}

// Field constructors for convenient usage.

// Bool creates a boolean field.
func Bool(key string, val bool) Field {
	return Field{Key: key, Type: BoolType, Value: val}
}

// Int creates an int field.
func Int(key string, val int) Field {
	return Field{Key: key, Type: Int64Type, Value: int64(val)}
}

// Int8 creates an int8 field.
func Int8(key string, val int8) Field {
	return Field{Key: key, Type: Int64Type, Value: int64(val)}
}

// Int16 creates an int16 field.
func Int16(key string, val int16) Field {
	return Field{Key: key, Type: Int64Type, Value: int64(val)}
}

// Int32 creates an int32 field.
func Int32(key string, val int32) Field {
	return Field{Key: key, Type: Int64Type, Value: int64(val)}
}

// Int64 creates an int64 field.
func Int64(key string, val int64) Field {
	return Field{Key: key, Type: Int64Type, Value: val}
}

// Uint creates a uint field.
func Uint(key string, val uint) Field {
	return Field{Key: key, Type: Uint64Type, Value: uint64(val)}
}

// Uint8 creates a uint8 field.
func Uint8(key string, val uint8) Field {
	return Field{Key: key, Type: Uint64Type, Value: uint64(val)}
}

// Uint16 creates a uint16 field.
func Uint16(key string, val uint16) Field {
	return Field{Key: key, Type: Uint64Type, Value: uint64(val)}
}

// Uint32 creates a uint32 field.
func Uint32(key string, val uint32) Field {
	return Field{Key: key, Type: Uint64Type, Value: uint64(val)}
}

// Uint64 creates a uint64 field.
func Uint64(key string, val uint64) Field {
	return Field{Key: key, Type: Uint64Type, Value: val}
}

// Float32 creates a float32 field.
func Float32(key string, val float32) Field {
	return Field{Key: key, Type: Float64Type, Value: float64(val)}
}

// Float64 creates a float64 field.
func Float64(key string, val float64) Field {
	return Field{Key: key, Type: Float64Type, Value: val}
}

// String creates a string field.
func String(key string, val string) Field {
	return Field{Key: key, Type: StringType, Value: val}
}

// Duration creates a duration field.
func Duration(key string, val time.Duration) Field {
	return Field{Key: key, Type: DurationType, Value: val}
}

// Time creates a time field.
func Time(key string, val time.Time) Field {
	return Field{Key: key, Type: TimeType, Value: val}
}

// Error creates an error field.
func Error(err error) Field {
	return Field{Key: "error", Type: ErrorType, Value: err}
}

// NamedError creates an error field with a custom key.
func NamedError(key string, err error) Field {
	return Field{Key: key, Type: ErrorType, Value: err}
}

// Any creates a field with any type value.
func Any(key string, val interface{}) Field {
	return Field{Key: key, Type: AnyType, Value: val}
}

// Fields is a collection of Field values.
type Fields []Field

// ToAttributes converts Fields to OpenTelemetry attributes.
func (fs Fields) ToAttributes() []attribute.KeyValue {
	if len(fs) == 0 {
		return nil
	}
	attrs := make([]attribute.KeyValue, len(fs))
	for i, f := range fs {
		attrs[i] = f.ToAttribute()
	}
	return attrs
}

// Map converts Fields to a map[string]interface{}.
func (fs Fields) Map() map[string]interface{} {
	m := make(map[string]interface{}, len(fs))
	for _, f := range fs {
		m[f.Key] = f.Value
	}
	return m
}

// Len returns the number of fields.
func (fs Fields) Len() int {
	return len(fs)
}

// Add appends fields to the collection.
func (fs *Fields) Add(fields ...Field) {
	*fs = append(*fs, fields...)
}

// Merge merges multiple Fields into one.
func Merge(fields ...Fields) Fields {
	var totalLen int
	for _, fs := range fields {
		totalLen += len(fs)
	}
	merged := make(Fields, 0, totalLen)
	for _, fs := range fields {
		merged = append(merged, fs...)
	}
	return merged
}

// FieldEncoder encodes fields to various formats.
type FieldEncoder interface {
	EncodeBool(key string, val bool)
	EncodeInt64(key string, val int64)
	EncodeUint64(key string, val uint64)
	EncodeFloat64(key string, val float64)
	EncodeString(key string, val string)
	EncodeDuration(key string, val time.Duration)
	EncodeTime(key string, val time.Time)
	EncodeError(key string, val error)
	EncodeAny(key string, val interface{})
}

// JSONEncoder encodes fields to JSON format.
type JSONEncoder struct {
	buffer []byte
	first  bool
}

// NewJSONEncoder creates a new JSON encoder.
func NewJSONEncoder() *JSONEncoder {
	return &JSONEncoder{
		buffer: make([]byte, 0, 1024),
		first:  true,
	}
}

// Reset resets the encoder state.
func (e *JSONEncoder) Reset() {
	e.buffer = e.buffer[:0]
	e.first = true
}

// Bytes returns the encoded bytes.
func (e *JSONEncoder) Bytes() []byte {
	return e.buffer
}

// String returns the encoded string.
func (e *JSONEncoder) String() string {
	return string(e.buffer)
}

func (e *JSONEncoder) writeKey(key string) {
	if !e.first {
		e.buffer = append(e.buffer, ',')
	}
	e.first = false
	e.buffer = append(e.buffer, '"')
	e.buffer = append(e.buffer, key...)
	e.buffer = append(e.buffer, '"', ':')
}

// EncodeBool encodes a boolean value.
func (e *JSONEncoder) EncodeBool(key string, val bool) {
	e.writeKey(key)
	if val {
		e.buffer = append(e.buffer, "true"...)
	} else {
		e.buffer = append(e.buffer, "false"...)
	}
}

// EncodeInt64 encodes an int64 value.
func (e *JSONEncoder) EncodeInt64(key string, val int64) {
	e.writeKey(key)
	e.buffer = strconv.AppendInt(e.buffer, val, 10)
}

// EncodeUint64 encodes a uint64 value.
func (e *JSONEncoder) EncodeUint64(key string, val uint64) {
	e.writeKey(key)
	e.buffer = strconv.AppendUint(e.buffer, val, 10)
}

// EncodeFloat64 encodes a float64 value.
func (e *JSONEncoder) EncodeFloat64(key string, val float64) {
	e.writeKey(key)
	switch {
	case math.IsNaN(val):
		e.buffer = append(e.buffer, `"NaN"`...)
	case math.IsInf(val, 1):
		e.buffer = append(e.buffer, `"+Inf"`...)
	case math.IsInf(val, -1):
		e.buffer = append(e.buffer, `"-Inf"`...)
	default:
		e.buffer = strconv.AppendFloat(e.buffer, val, 'f', -1, 64)
	}
}

// EncodeString encodes a string value.
func (e *JSONEncoder) EncodeString(key string, val string) {
	e.writeKey(key)
	e.buffer = append(e.buffer, '"')
	for _, r := range val {
		switch r {
		case '"':
			e.buffer = append(e.buffer, `\"`...)
		case '\\':
			e.buffer = append(e.buffer, `\\`...)
		case '\b':
			e.buffer = append(e.buffer, `\b`...)
		case '\f':
			e.buffer = append(e.buffer, `\f`...)
		case '\n':
			e.buffer = append(e.buffer, `\n`...)
		case '\r':
			e.buffer = append(e.buffer, `\r`...)
		case '\t':
			e.buffer = append(e.buffer, `\t`...)
		default:
			if r < 0x20 {
				e.buffer = append(e.buffer, fmt.Sprintf(`\u%04x`, r)...)
			} else {
				e.buffer = append(e.buffer, string(r)...)
			}
		}
	}
	e.buffer = append(e.buffer, '"')
}

// EncodeDuration encodes a duration value.
func (e *JSONEncoder) EncodeDuration(key string, val time.Duration) {
	e.EncodeString(key, val.String())
}

// EncodeTime encodes a time value.
func (e *JSONEncoder) EncodeTime(key string, val time.Time) {
	e.EncodeString(key, val.Format(time.RFC3339Nano))
}

// EncodeError encodes an error value.
func (e *JSONEncoder) EncodeError(key string, val error) {
	if val == nil {
		e.EncodeString(key, "null")
	} else {
		e.EncodeString(key, val.Error())
	}
}

// EncodeAny encodes any value.
func (e *JSONEncoder) EncodeAny(key string, val interface{}) {
	if val == nil {
		e.EncodeString(key, "null")
		return
	}
	switch v := val.(type) {
	case bool:
		e.EncodeBool(key, v)
	case int:
		e.EncodeInt64(key, int64(v))
	case int8:
		e.EncodeInt64(key, int64(v))
	case int16:
		e.EncodeInt64(key, int64(v))
	case int32:
		e.EncodeInt64(key, int64(v))
	case int64:
		e.EncodeInt64(key, v)
	case uint:
		e.EncodeUint64(key, uint64(v))
	case uint8:
		e.EncodeUint64(key, uint64(v))
	case uint16:
		e.EncodeUint64(key, uint64(v))
	case uint32:
		e.EncodeUint64(key, uint64(v))
	case uint64:
		e.EncodeUint64(key, v)
	case float32:
		e.EncodeFloat64(key, float64(v))
	case float64:
		e.EncodeFloat64(key, v)
	case string:
		e.EncodeString(key, v)
	case time.Duration:
		e.EncodeDuration(key, v)
	case time.Time:
		e.EncodeTime(key, v)
	case error:
		e.EncodeError(key, v)
	default:
		e.EncodeString(key, fmt.Sprintf("%v", v))
	}
}

// EncodeField encodes a Field using the appropriate method.
func (e *JSONEncoder) EncodeField(f Field) {
	switch f.Type {
	case BoolType:
		e.EncodeBool(f.Key, f.Value.(bool))
	case Int64Type:
		e.EncodeInt64(f.Key, f.Value.(int64))
	case Uint64Type:
		e.EncodeUint64(f.Key, f.Value.(uint64))
	case Float64Type:
		e.EncodeFloat64(f.Key, f.Value.(float64))
	case StringType:
		e.EncodeString(f.Key, f.Value.(string))
	case DurationType:
		e.EncodeDuration(f.Key, f.Value.(time.Duration))
	case TimeType:
		e.EncodeTime(f.Key, f.Value.(time.Time))
	case ErrorType:
		e.EncodeError(f.Key, f.Value.(error))
	default:
		e.EncodeAny(f.Key, f.Value)
	}
}

// EncodeFields encodes multiple fields.
func (e *JSONEncoder) EncodeFields(fields Fields) {
	for _, f := range fields {
		e.EncodeField(f)
	}
}

// Package types provides attribute types and utilities for OpenTelemetry compatible telemetry data.
package types

import (
	"encoding/json"
	"fmt"
)

// Attribute represents a key-value pair that can be attached to telemetry data.
// Attributes are used to add metadata to spans, resources, logs, and metrics.
//
// Example:
//
//	attr := types.NewAttribute("http.method", "GET")
//	intAttr := types.NewIntAttribute("http.status_code", 200)
//	boolAttr := types.NewBoolAttribute("error", true)
type Attribute struct {
	// Key is the attribute name. Keys must be non-empty and unique within a set.
	Key string `json:"key"`

	// Value holds the attribute value with type information.
	Value Value `json:"value"`
}

// Value represents a typed attribute value.
type Value struct {
	// Type indicates the type of value stored.
	Type ValueType `json:"type"`

	// StringVal holds the value when Type is ValueTypeString.
	StringVal string `json:"string_val,omitempty"`

	// IntVal holds the value when Type is ValueTypeInt.
	IntVal int64 `json:"int_val,omitempty"`

	// DoubleVal holds the value when Type is ValueTypeDouble.
	DoubleVal float64 `json:"double_val,omitempty"`

	// BoolVal holds the value when Type is ValueTypeBool.
	BoolVal bool `json:"bool_val,omitempty"`

	// BytesVal holds the value when Type is ValueTypeBytes.
	BytesVal []byte `json:"bytes_val,omitempty"`

	// ArrayVal holds the value when Type is ValueTypeArray.
	ArrayVal []Value `json:"array_val,omitempty"`

	// MapVal holds the value when Type is ValueTypeMap.
	MapVal map[string]Value `json:"map_val,omitempty"`
}

// NewAttribute creates a new string attribute.
func NewAttribute(key, value string) Attribute {
	return Attribute{
		Key:   key,
		Value: StringValue(value),
	}
}

// NewIntAttribute creates a new integer attribute.
func NewIntAttribute(key string, value int64) Attribute {
	return Attribute{
		Key:   key,
		Value: IntValue(value),
	}
}

// NewFloatAttribute creates a new float64 attribute.
func NewFloatAttribute(key string, value float64) Attribute {
	return Attribute{
		Key:   key,
		Value: DoubleValue(value),
	}
}

// NewBoolAttribute creates a new boolean attribute.
func NewBoolAttribute(key string, value bool) Attribute {
	return Attribute{
		Key:   key,
		Value: BoolValue(value),
	}
}

// NewBytesAttribute creates a new bytes attribute.
func NewBytesAttribute(key string, value []byte) Attribute {
	return Attribute{
		Key:   key,
		Value: BytesValue(value),
	}
}

// NewArrayAttribute creates a new array attribute.
func NewArrayAttribute(key string, values []Value) Attribute {
	return Attribute{
		Key:   key,
		Value: ArrayValue(values),
	}
}

// NewMapAttribute creates a new map attribute.
func NewMapAttribute(key string, value map[string]Value) Attribute {
	return Attribute{
		Key:   key,
		Value: MapValue(value),
	}
}

// StringValue creates a new string Value.
func StringValue(v string) Value {
	return Value{Type: ValueTypeString, StringVal: v}
}

// IntValue creates a new int64 Value.
func IntValue(v int64) Value {
	return Value{Type: ValueTypeInt, IntVal: v}
}

// DoubleValue creates a new float64 Value.
func DoubleValue(v float64) Value {
	return Value{Type: ValueTypeDouble, DoubleVal: v}
}

// BoolValue creates a new bool Value.
func BoolValue(v bool) Value {
	return Value{Type: ValueTypeBool, BoolVal: v}
}

// BytesValue creates a new bytes Value.
func BytesValue(v []byte) Value {
	return Value{Type: ValueTypeBytes, BytesVal: v}
}

// ArrayValue creates a new array Value.
func ArrayValue(v []Value) Value {
	return Value{Type: ValueTypeArray, ArrayVal: v}
}

// MapValue creates a new map Value.
func MapValue(v map[string]Value) Value {
	return Value{Type: ValueTypeMap, MapVal: v}
}

// AsString returns the value as a string, or empty string if not a string type.
func (v Value) AsString() string {
	if v.Type == ValueTypeString {
		return v.StringVal
	}
	return ""
}

// AsInt returns the value as an int64, or 0 if not an int type.
func (v Value) AsInt() int64 {
	if v.Type == ValueTypeInt {
		return v.IntVal
	}
	return 0
}

// AsFloat returns the value as a float64, or 0 if not a float type.
func (v Value) AsFloat() float64 {
	if v.Type == ValueTypeDouble {
		return v.DoubleVal
	}
	return 0
}

// AsBool returns the value as a bool, or false if not a bool type.
func (v Value) AsBool() bool {
	if v.Type == ValueTypeBool {
		return v.BoolVal
	}
	return false
}

// AsBytes returns the value as a byte slice, or nil if not a bytes type.
func (v Value) AsBytes() []byte {
	if v.Type == ValueTypeBytes {
		return v.BytesVal
	}
	return nil
}

// AsArray returns the value as an array, or nil if not an array type.
func (v Value) AsArray() []Value {
	if v.Type == ValueTypeArray {
		return v.ArrayVal
	}
	return nil
}

// AsMap returns the value as a map, or nil if not a map type.
func (v Value) AsMap() map[string]Value {
	if v.Type == ValueTypeMap {
		return v.MapVal
	}
	return nil
}

// String returns a string representation of the value.
func (v Value) String() string {
	switch v.Type {
	case ValueTypeEmpty:
		return ""
	case ValueTypeString:
		return v.StringVal
	case ValueTypeInt:
		return fmt.Sprintf("%d", v.IntVal)
	case ValueTypeDouble:
		return fmt.Sprintf("%g", v.DoubleVal)
	case ValueTypeBool:
		return fmt.Sprintf("%t", v.BoolVal)
	case ValueTypeBytes:
		return fmt.Sprintf("%d bytes", len(v.BytesVal))
	case ValueTypeArray:
		return fmt.Sprintf("[%d items]", len(v.ArrayVal))
	case ValueTypeMap:
		return fmt.Sprintf("{%d entries}", len(v.MapVal))
	default:
		return fmt.Sprintf("unknown(%d)", v.Type)
	}
}

// IsEmpty returns true if the value is empty.
func (v Value) IsEmpty() bool {
	return v.Type == ValueTypeEmpty
}

// Equal compares two values for equality.
func (v Value) Equal(other Value) bool {
	if v.Type != other.Type {
		return false
	}

	switch v.Type {
	case ValueTypeEmpty:
		return true
	case ValueTypeString:
		return v.StringVal == other.StringVal
	case ValueTypeInt:
		return v.IntVal == other.IntVal
	case ValueTypeDouble:
		return v.DoubleVal == other.DoubleVal
	case ValueTypeBool:
		return v.BoolVal == other.BoolVal
	case ValueTypeBytes:
		if len(v.BytesVal) != len(other.BytesVal) {
			return false
		}
		for i := range v.BytesVal {
			if v.BytesVal[i] != other.BytesVal[i] {
				return false
			}
		}
		return true
	case ValueTypeArray:
		if len(v.ArrayVal) != len(other.ArrayVal) {
			return false
		}
		for i := range v.ArrayVal {
			if !v.ArrayVal[i].Equal(other.ArrayVal[i]) {
				return false
			}
		}
		return true
	case ValueTypeMap:
		if len(v.MapVal) != len(other.MapVal) {
			return false
		}
		for k, v1 := range v.MapVal {
			v2, ok := other.MapVal[k]
			if !ok || !v1.Equal(v2) {
				return false
			}
		}
		return true
	default:
		return false
	}
}

// Attributes is a collection of Attribute values.
type Attributes []Attribute

// NewAttributes creates an Attributes collection from key-value pairs.
// Keys must be strings, values can be: string, int64, float64, bool, []byte, []Value, or map[string]Value.
//
// Example:
//
//	attrs := types.NewAttributes(
//	    "service.name", "my-service",
//	    "service.version", "1.0.0",
//	    "http.port", 8080,
//	)
func NewAttributes(kvs ...any) Attributes {
	if len(kvs)%2 != 0 {
		panic("NewAttributes requires even number of arguments")
	}

	attrs := make(Attributes, 0, len(kvs)/2)
	for i := 0; i < len(kvs); i += 2 {
		key, ok := kvs[i].(string)
		if !ok {
			continue
		}

		var value Value
		switch v := kvs[i+1].(type) {
		case string:
			value = StringValue(v)
		case int:
			value = IntValue(int64(v))
		case int8:
			value = IntValue(int64(v))
		case int16:
			value = IntValue(int64(v))
		case int32:
			value = IntValue(int64(v))
		case int64:
			value = IntValue(v)
		case uint:
			value = IntValue(int64(v))
		case uint8:
			value = IntValue(int64(v))
		case uint16:
			value = IntValue(int64(v))
		case uint32:
			value = IntValue(int64(v))
		case uint64:
			value = IntValue(int64(v))
		case float32:
			value = DoubleValue(float64(v))
		case float64:
			value = DoubleValue(v)
		case bool:
			value = BoolValue(v)
		case []byte:
			value = BytesValue(v)
		case []Value:
			value = ArrayValue(v)
		case map[string]Value:
			value = MapValue(v)
		default:
			value = StringValue(fmt.Sprintf("%v", v))
		}

		attrs = append(attrs, Attribute{Key: key, Value: value})
	}

	return attrs
}

// Get returns the attribute with the given key, or false if not found.
func (a Attributes) Get(key string) (Attribute, bool) {
	for _, attr := range a {
		if attr.Key == key {
			return attr, true
		}
	}
	return Attribute{}, false
}

// Value returns the value for the given key, or empty Value if not found.
func (a Attributes) Value(key string) Value {
	if attr, ok := a.Get(key); ok {
		return attr.Value
	}
	return Value{Type: ValueTypeEmpty}
}

// StringValue returns the string value for the given key, or empty string if not found.
func (a Attributes) StringValue(key string) string {
	return a.Value(key).AsString()
}

// IntValue returns the int64 value for the given key, or 0 if not found.
func (a Attributes) IntValue(key string) int64 {
	return a.Value(key).AsInt()
}

// FloatValue returns the float64 value for the given key, or 0 if not found.
func (a Attributes) FloatValue(key string) float64 {
	return a.Value(key).AsFloat()
}

// BoolValue returns the bool value for the given key, or false if not found.
func (a Attributes) BoolValue(key string) bool {
	return a.Value(key).AsBool()
}

// Len returns the number of attributes.
func (a Attributes) Len() int {
	return len(a)
}

// IsEmpty returns true if there are no attributes.
func (a Attributes) IsEmpty() bool {
	return len(a) == 0
}

// Clone creates a deep copy of the attributes.
func (a Attributes) Clone() Attributes {
	if len(a) == 0 {
		return nil
	}

	cloned := make(Attributes, len(a))
	copy(cloned, a)
	return cloned
}

// ToMap converts attributes to a map.
func (a Attributes) ToMap() map[string]Value {
	m := make(map[string]Value, len(a))
	for _, attr := range a {
		m[attr.Key] = attr.Value
	}
	return m
}

// Merge combines two attribute sets. Values from 'other' take precedence.
func (a Attributes) Merge(other Attributes) Attributes {
	if len(other) == 0 {
		return a
	}
	if len(a) == 0 {
		return other
	}

	result := make(Attributes, 0, len(a)+len(other))
	seen := make(map[string]bool, len(a)+len(other))

	// Add attributes from 'other' first (takes precedence)
	for _, attr := range other {
		result = append(result, attr)
		seen[attr.Key] = true
	}

	// Add attributes from 'a' that aren't already in the result
	for _, attr := range a {
		if !seen[attr.Key] {
			result = append(result, attr)
		}
	}

	return result
}

// Filter returns a new Attributes containing only attributes where the predicate returns true.
func (a Attributes) Filter(predicate func(Attribute) bool) Attributes {
	result := make(Attributes, 0, len(a))
	for _, attr := range a {
		if predicate(attr) {
			result = append(result, attr)
		}
	}
	return result
}

// Keys returns all attribute keys.
func (a Attributes) Keys() []string {
	keys := make([]string, len(a))
	for i, attr := range a {
		keys[i] = attr.Key
	}
	return keys
}

// Validate checks if all attributes are valid.
func (a Attributes) Validate() error {
	seen := make(map[string]bool)
	for _, attr := range a {
		if attr.Key == "" {
			return fmt.Errorf("%w: empty key", ErrInvalidAttribute)
		}
		if seen[attr.Key] {
			return fmt.Errorf("%w: duplicate key %q", ErrInvalidAttribute, attr.Key)
		}
		seen[attr.Key] = true
	}
	return nil
}

// MarshalJSON implements json.Marshaler.
func (a Attributes) MarshalJSON() ([]byte, error) {
	m := a.ToMap()
	return json.Marshal(m)
}

// UnmarshalJSON implements json.Unmarshaler.
func (a *Attributes) UnmarshalJSON(data []byte) error {
	var m map[string]json.RawMessage
	if err := json.Unmarshal(data, &m); err != nil {
		return err
	}

	attrs := make(Attributes, 0, len(m))
	for key, raw := range m {
		var value Value
		if err := json.Unmarshal(raw, &value); err != nil {
			// Try to unmarshal as simple types
			var s string
			if err := json.Unmarshal(raw, &s); err == nil {
				value = StringValue(s)
			} else {
				var n float64
				if err := json.Unmarshal(raw, &n); err == nil {
					value = DoubleValue(n)
				} else {
					var b bool
					if err := json.Unmarshal(raw, &b); err == nil {
						value = BoolValue(b)
					} else {
						value = StringValue(string(raw))
					}
				}
			}
		}
		attrs = append(attrs, Attribute{Key: key, Value: value})
	}

	*a = attrs
	return nil
}

package logs

import (
	"encoding/json"
	"errors"
	"math"
	"strings"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

func TestFieldType_String(t *testing.T) {
	tests := []struct {
		ft       FieldType
		expected string
	}{
		{BoolType, "bool"},
		{Int64Type, "int64"},
		{Uint64Type, "uint64"},
		{Float64Type, "float64"},
		{StringType, "string"},
		{DurationType, "duration"},
		{TimeType, "time"},
		{ErrorType, "error"},
		{AnyType, "any"},
		{UnknownType, "unknown"},
		{FieldType(999), "unknown"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			if got := tt.ft.String(); got != tt.expected {
				t.Errorf("FieldType.String() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestField_String(t *testing.T) {
	f := Field{Key: "test", Type: StringType, Value: "value"}
	expected := "test=value"
	if got := f.String(); got != expected {
		t.Errorf("Field.String() = %v, want %v", got, expected)
	}
}

func TestField_ToAttribute(t *testing.T) {
	tests := []struct {
		name     string
		field    Field
		expected attribute.KeyValue
	}{
		{
			name:     "bool",
			field:    Bool("enabled", true),
			expected: attribute.Bool("enabled", true),
		},
		{
			name:     "int64",
			field:    Int64("count", 42),
			expected: attribute.Int64("count", 42),
		},
		{
			name:     "uint64",
			field:    Uint64("size", 100),
			expected: attribute.Int64("size", 100),
		},
		{
			name:     "float64",
			field:    Float64("ratio", 3.14),
			expected: attribute.Float64("ratio", 3.14),
		},
		{
			name:     "string",
			field:    String("name", "test"),
			expected: attribute.String("name", "test"),
		},
		{
			name:     "duration",
			field:    Duration("elapsed", time.Second),
			expected: attribute.String("elapsed", "1s"),
		},
		{
			name:     "time",
			field:    Time("created", time.Date(2024, 1, 1, 0, 0, 0, 0, time.UTC)),
			expected: attribute.String("created", "2024-01-01T00:00:00Z"),
		},
		{
			name:     "error",
			field:    Error(errors.New("test error")),
			expected: attribute.String("error", "test error"),
		},
		{
			name:     "nil error",
			field:    Error(nil),
			expected: attribute.String("error", "null"),
		},
		{
			name:     "any",
			field:    Any("data", map[string]int{"key": 1}),
			expected: attribute.String("data", "map[key:1]"),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := tt.field.ToAttribute()
			if got.Key != tt.expected.Key {
				t.Errorf("Key = %v, want %v", got.Key, tt.expected.Key)
			}
			if got.Value.Type() != tt.expected.Value.Type() {
				t.Errorf("Value.Type() = %v, want %v", got.Value.Type(), tt.expected.Value.Type())
			}
		})
	}
}

func TestFieldConstructors(t *testing.T) {
	tests := []struct {
		name     string
		field    Field
		expected Field
	}{
		{"Bool", Bool("b", true), Field{Key: "b", Type: BoolType, Value: true}},
		{"Int", Int("i", 42), Field{Key: "i", Type: Int64Type, Value: int64(42)}},
		{"Int8", Int8("i8", 8), Field{Key: "i8", Type: Int64Type, Value: int64(8)}},
		{"Int16", Int16("i16", 16), Field{Key: "i16", Type: Int64Type, Value: int64(16)}},
		{"Int32", Int32("i32", 32), Field{Key: "i32", Type: Int64Type, Value: int64(32)}},
		{"Int64", Int64("i64", 64), Field{Key: "i64", Type: Int64Type, Value: int64(64)}},
		{"Uint", Uint("u", 42), Field{Key: "u", Type: Uint64Type, Value: uint64(42)}},
		{"Uint8", Uint8("u8", 8), Field{Key: "u8", Type: Uint64Type, Value: uint64(8)}},
		{"Uint16", Uint16("u16", 16), Field{Key: "u16", Type: Uint64Type, Value: uint64(16)}},
		{"Uint32", Uint32("u32", 32), Field{Key: "u32", Type: Uint64Type, Value: uint64(32)}},
		{"Uint64", Uint64("u64", 64), Field{Key: "u64", Type: Uint64Type, Value: uint64(64)}},
		{"Float32", Float32("f32", 3.14), Field{Key: "f32", Type: Float64Type, Value: float64(3.14)}},
		{"Float64", Float64("f64", 3.14), Field{Key: "f64", Type: Float64Type, Value: float64(3.14)}},
		{"String", String("s", "test"), Field{Key: "s", Type: StringType, Value: "test"}},
		{"Duration", Duration("d", time.Second), Field{Key: "d", Type: DurationType, Value: time.Second}},
		{"Error", Error(errors.New("err")), Field{Key: "error", Type: ErrorType, Value: errors.New("err")}},
		{"NamedError", NamedError("err_key", errors.New("err")), Field{Key: "err_key", Type: ErrorType, Value: errors.New("err")}},
		{"Any", Any("a", "any"), Field{Key: "a", Type: AnyType, Value: "any"}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if tt.field.Key != tt.expected.Key {
				t.Errorf("Key = %v, want %v", tt.field.Key, tt.expected.Key)
			}
			if tt.field.Type != tt.expected.Type {
				t.Errorf("Type = %v, want %v", tt.field.Type, tt.expected.Type)
			}
		})
	}
}

func TestFields_ToAttributes(t *testing.T) {
	fields := Fields{
		Bool("enabled", true),
		Int("count", 42),
		String("name", "test"),
	}

	attrs := fields.ToAttributes()
	if len(attrs) != len(fields) {
		t.Errorf("ToAttributes() returned %d attributes, want %d", len(attrs), len(fields))
	}

	// Test nil fields
	var nilFields Fields
	if attrs := nilFields.ToAttributes(); attrs != nil {
		t.Error("ToAttributes() on nil Fields should return nil")
	}

	// Test empty fields
	emptyFields := Fields{}
	if attrs := emptyFields.ToAttributes(); len(attrs) != 0 {
		t.Error("ToAttributes() on empty Fields should return empty slice")
	}
}

func TestFields_Map(t *testing.T) {
	fields := Fields{
		String("key1", "value1"),
		Int("key2", 42),
		Bool("key3", true),
	}

	m := fields.Map()
	if len(m) != 3 {
		t.Errorf("Map() returned %d entries, want 3", len(m))
	}
	if m["key1"] != "value1" {
		t.Errorf("Map()[\"key1\"] = %v, want value1", m["key1"])
	}
	if m["key2"] != int64(42) {
		t.Errorf("Map()[\"key2\"] = %v, want 42", m["key2"])
	}
}

func TestFields_Len(t *testing.T) {
	fields := Fields{
		String("a", "1"),
		String("b", "2"),
	}
	if fields.Len() != 2 {
		t.Errorf("Len() = %v, want 2", fields.Len())
	}
}

func TestFields_Add(t *testing.T) {
	fields := Fields{String("a", "1")}
	fields.Add(String("b", "2"), String("c", "3"))

	if len(fields) != 3 {
		t.Errorf("After Add(), len = %v, want 3", len(fields))
	}
}

func TestMerge(t *testing.T) {
	fields1 := Fields{String("a", "1")}
	fields2 := Fields{Int("b", 2)}
	fields3 := Fields{Bool("c", true)}

	merged := Merge(fields1, fields2, fields3)
	if len(merged) != 3 {
		t.Errorf("Merge() returned %d fields, want 3", len(merged))
	}
}

func TestJSONEncoder(t *testing.T) {
	enc := NewJSONEncoder()

	t.Run("EncodeBool", func(t *testing.T) {
		enc.Reset()
		enc.EncodeBool("enabled", true)
		if !strings.Contains(enc.String(), `"enabled":true`) {
			t.Errorf("EncodeBool() = %v", enc.String())
		}
	})

	t.Run("EncodeInt64", func(t *testing.T) {
		enc.Reset()
		enc.EncodeInt64("count", 42)
		if !strings.Contains(enc.String(), `"count":42`) {
			t.Errorf("EncodeInt64() = %v", enc.String())
		}
	})

	t.Run("EncodeUint64", func(t *testing.T) {
		enc.Reset()
		enc.EncodeUint64("size", 100)
		if !strings.Contains(enc.String(), `"size":100`) {
			t.Errorf("EncodeUint64() = %v", enc.String())
		}
	})

	t.Run("EncodeFloat64", func(t *testing.T) {
		enc.Reset()
		enc.EncodeFloat64("ratio", 3.14)
		if !strings.Contains(enc.String(), `"ratio":3.14`) {
			t.Errorf("EncodeFloat64() = %v", enc.String())
		}
	})

	t.Run("EncodeFloat64_NaN", func(t *testing.T) {
		enc.Reset()
		enc.EncodeFloat64("nan", math.NaN())
		if !strings.Contains(enc.String(), `"nan":"NaN"`) {
			t.Errorf("EncodeFloat64(NaN) = %v", enc.String())
		}
	})

	t.Run("EncodeFloat64_Inf", func(t *testing.T) {
		enc.Reset()
		enc.EncodeFloat64("inf", math.Inf(1))
		if !strings.Contains(enc.String(), `"inf":"+Inf"`) {
			t.Errorf("EncodeFloat64(Inf) = %v", enc.String())
		}
	})

	t.Run("EncodeString", func(t *testing.T) {
		enc.Reset()
		enc.EncodeString("name", "test")
		if !strings.Contains(enc.String(), `"name":"test"`) {
			t.Errorf("EncodeString() = %v", enc.String())
		}
	})

	t.Run("EncodeString_Quotes", func(t *testing.T) {
		enc.Reset()
		enc.EncodeString("text", `hello "world"`)
		if !strings.Contains(enc.String(), `"text":"hello \"world\""`) {
			t.Errorf("EncodeString() with quotes = %v", enc.String())
		}
	})

	t.Run("EncodeDuration", func(t *testing.T) {
		enc.Reset()
		enc.EncodeDuration("elapsed", time.Second)
		if !strings.Contains(enc.String(), `"elapsed":"1s"`) {
			t.Errorf("EncodeDuration() = %v", enc.String())
		}
	})

	t.Run("EncodeTime", func(t *testing.T) {
		enc.Reset()
		enc.EncodeTime("created", time.Date(2024, 1, 1, 0, 0, 0, 0, time.UTC))
		if !strings.Contains(enc.String(), `"created":"2024-01-01T00:00:00Z"`) {
			t.Errorf("EncodeTime() = %v", enc.String())
		}
	})

	t.Run("EncodeError", func(t *testing.T) {
		enc.Reset()
		enc.EncodeError("err", errors.New("test error"))
		if !strings.Contains(enc.String(), `"err":"test error"`) {
			t.Errorf("EncodeError() = %v", enc.String())
		}
	})

	t.Run("EncodeError_Nil", func(t *testing.T) {
		enc.Reset()
		enc.EncodeError("err", nil)
		if !strings.Contains(enc.String(), `"err":"null"`) {
			t.Errorf("EncodeError(nil) = %v", enc.String())
		}
	})

	t.Run("EncodeAny", func(t *testing.T) {
		enc.Reset()
		enc.EncodeAny("val", 42)
		if !strings.Contains(enc.String(), `"val":42`) {
			t.Errorf("EncodeAny() = %v", enc.String())
		}
	})

	t.Run("EncodeAny_Nil", func(t *testing.T) {
		enc.Reset()
		enc.EncodeAny("val", nil)
		if !strings.Contains(enc.String(), `"val":"null"`) {
			t.Errorf("EncodeAny(nil) = %v", enc.String())
		}
	})

	t.Run("EncodeField", func(t *testing.T) {
		enc.Reset()
		enc.EncodeField(String("key", "value"))
		if !strings.Contains(enc.String(), `"key":"value"`) {
			t.Errorf("EncodeField() = %v", enc.String())
		}
	})

	t.Run("EncodeFields", func(t *testing.T) {
		enc.Reset()
		enc.EncodeFields(Fields{
			String("a", "1"),
			Int("b", 2),
		})
		result := enc.String()
		if !strings.Contains(result, `"a":"1"`) || !strings.Contains(result, `"b":2`) {
			t.Errorf("EncodeFields() = %v", result)
		}
	})
}

func TestJSONEncoder_MultipleFields(t *testing.T) {
	enc := NewJSONEncoder()
	enc.EncodeString("first", "value1")
	enc.EncodeString("second", "value2")

	result := enc.String()
	if !strings.Contains(result, `","`) {
		t.Error("Multiple fields should be separated by comma")
	}
}

func TestJSONEncoder_ThreadSafety(t *testing.T) {
	// Each encoder should be independent
	enc1 := NewJSONEncoder()
	enc2 := NewJSONEncoder()

	enc1.EncodeString("key1", "value1")
	enc2.EncodeString("key2", "value2")

	if strings.Contains(enc1.String(), "key2") {
		t.Error("enc1 should not contain key2")
	}
	if strings.Contains(enc2.String(), "key1") {
		t.Error("enc2 should not contain key1")
	}
}

func TestJSONEncoder_ValidJSON(t *testing.T) {
	enc := NewJSONEncoder()
	enc.EncodeString("name", "test")
	enc.EncodeInt64("count", 42)
	enc.EncodeBool("enabled", true)

	// Verify the output is valid JSON
	jsonStr := "{" + enc.String() + "}"
	var result map[string]interface{}
	if err := json.Unmarshal([]byte(jsonStr), &result); err != nil {
		t.Errorf("Encoder output is not valid JSON: %v\nOutput: %s", err, jsonStr)
	}
}

func BenchmarkJSONEncoder_EncodeString(b *testing.B) {
	enc := NewJSONEncoder()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			enc.Reset()
			enc.EncodeString("key", "value")
		}
	})
}

func BenchmarkJSONEncoder_EncodeInt64(b *testing.B) {
	enc := NewJSONEncoder()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			enc.Reset()
			enc.EncodeInt64("count", 42)
		}
	})
}

func BenchmarkFields_ToAttributes(b *testing.B) {
	fields := Fields{
		String("a", "1"),
		Int("b", 2),
		Bool("c", true),
		Float64("d", 3.14),
	}
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_ = fields.ToAttributes()
		}
	})
}

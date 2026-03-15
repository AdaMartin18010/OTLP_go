package types

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewAttribute(t *testing.T) {
	t.Run("NewAttribute string", func(t *testing.T) {
		attr := NewAttribute("key", "value")
		assert.Equal(t, "key", attr.Key)
		assert.Equal(t, ValueTypeString, attr.Value.Type)
		assert.Equal(t, "value", attr.Value.AsString())
	})

	t.Run("NewIntAttribute", func(t *testing.T) {
		attr := NewIntAttribute("count", 42)
		assert.Equal(t, "count", attr.Key)
		assert.Equal(t, ValueTypeInt, attr.Value.Type)
		assert.Equal(t, int64(42), attr.Value.AsInt())
	})

	t.Run("NewFloatAttribute", func(t *testing.T) {
		attr := NewFloatAttribute("temperature", 98.6)
		assert.Equal(t, "temperature", attr.Key)
		assert.Equal(t, ValueTypeDouble, attr.Value.Type)
		assert.Equal(t, 98.6, attr.Value.AsFloat())
	})

	t.Run("NewBoolAttribute", func(t *testing.T) {
		attr := NewBoolAttribute("enabled", true)
		assert.Equal(t, "enabled", attr.Key)
		assert.Equal(t, ValueTypeBool, attr.Value.Type)
		assert.True(t, attr.Value.AsBool())
	})

	t.Run("NewBytesAttribute", func(t *testing.T) {
		data := []byte{0x01, 0x02, 0x03}
		attr := NewBytesAttribute("raw", data)
		assert.Equal(t, "raw", attr.Key)
		assert.Equal(t, ValueTypeBytes, attr.Value.Type)
		assert.Equal(t, data, attr.Value.AsBytes())
	})

	t.Run("NewArrayAttribute", func(t *testing.T) {
		values := []Value{StringValue("a"), StringValue("b")}
		attr := NewArrayAttribute("list", values)
		assert.Equal(t, "list", attr.Key)
		assert.Equal(t, ValueTypeArray, attr.Value.Type)
		assert.Len(t, attr.Value.AsArray(), 2)
	})

	t.Run("NewMapAttribute", func(t *testing.T) {
		m := map[string]Value{
			"a": StringValue("1"),
			"b": IntValue(2),
		}
		attr := NewMapAttribute("dict", m)
		assert.Equal(t, "dict", attr.Key)
		assert.Equal(t, ValueTypeMap, attr.Value.Type)
		assert.Len(t, attr.Value.AsMap(), 2)
	})
}

func TestValueHelpers(t *testing.T) {
	t.Run("StringValue", func(t *testing.T) {
		v := StringValue("test")
		assert.Equal(t, ValueTypeString, v.Type)
		assert.Equal(t, "test", v.AsString())
	})

	t.Run("IntValue", func(t *testing.T) {
		v := IntValue(42)
		assert.Equal(t, ValueTypeInt, v.Type)
		assert.Equal(t, int64(42), v.AsInt())
	})

	t.Run("DoubleValue", func(t *testing.T) {
		v := DoubleValue(3.14)
		assert.Equal(t, ValueTypeDouble, v.Type)
		assert.Equal(t, 3.14, v.AsFloat())
	})

	t.Run("BoolValue", func(t *testing.T) {
		v := BoolValue(true)
		assert.Equal(t, ValueTypeBool, v.Type)
		assert.True(t, v.AsBool())
	})

	t.Run("BytesValue", func(t *testing.T) {
		data := []byte{0x01, 0x02}
		v := BytesValue(data)
		assert.Equal(t, ValueTypeBytes, v.Type)
		assert.Equal(t, data, v.AsBytes())
	})

	t.Run("ArrayValue", func(t *testing.T) {
		arr := []Value{StringValue("a")}
		v := ArrayValue(arr)
		assert.Equal(t, ValueTypeArray, v.Type)
		assert.Equal(t, arr, v.AsArray())
	})

	t.Run("MapValue", func(t *testing.T) {
		m := map[string]Value{"key": StringValue("value")}
		v := MapValue(m)
		assert.Equal(t, ValueTypeMap, v.Type)
		assert.Equal(t, m, v.AsMap())
	})
}

func TestValueAccessors(t *testing.T) {
	t.Run("AsString", func(t *testing.T) {
		assert.Equal(t, "test", StringValue("test").AsString())
		assert.Equal(t, "", IntValue(42).AsString())
	})

	t.Run("AsInt", func(t *testing.T) {
		assert.Equal(t, int64(42), IntValue(42).AsInt())
		assert.Equal(t, int64(0), StringValue("test").AsInt())
	})

	t.Run("AsFloat", func(t *testing.T) {
		assert.Equal(t, 3.14, DoubleValue(3.14).AsFloat())
		assert.Equal(t, 0.0, StringValue("test").AsFloat())
	})

	t.Run("AsBool", func(t *testing.T) {
		assert.True(t, BoolValue(true).AsBool())
		assert.False(t, StringValue("test").AsBool())
	})

	t.Run("AsBytes", func(t *testing.T) {
		data := []byte{0x01}
		assert.Equal(t, data, BytesValue(data).AsBytes())
		assert.Nil(t, StringValue("test").AsBytes())
	})

	t.Run("AsArray", func(t *testing.T) {
		arr := []Value{StringValue("a")}
		assert.Equal(t, arr, ArrayValue(arr).AsArray())
		assert.Nil(t, StringValue("test").AsArray())
	})

	t.Run("AsMap", func(t *testing.T) {
		m := map[string]Value{"key": StringValue("value")}
		assert.Equal(t, m, MapValue(m).AsMap())
		assert.Nil(t, StringValue("test").AsMap())
	})
}

func TestValueString(t *testing.T) {
	t.Run("Empty", func(t *testing.T) {
		v := Value{Type: ValueTypeEmpty}
		assert.Equal(t, "", v.String())
	})

	t.Run("String", func(t *testing.T) {
		assert.Equal(t, "test", StringValue("test").String())
	})

	t.Run("Int", func(t *testing.T) {
		assert.Equal(t, "42", IntValue(42).String())
	})

	t.Run("Double", func(t *testing.T) {
		assert.Equal(t, "3.14", DoubleValue(3.14).String())
	})

	t.Run("Bool", func(t *testing.T) {
		assert.Equal(t, "true", BoolValue(true).String())
		assert.Equal(t, "false", BoolValue(false).String())
	})

	t.Run("Bytes", func(t *testing.T) {
		assert.Equal(t, "3 bytes", BytesValue([]byte{0x01, 0x02, 0x03}).String())
	})

	t.Run("Array", func(t *testing.T) {
		assert.Equal(t, "[2 items]", ArrayValue([]Value{StringValue("a"), StringValue("b")}).String())
	})

	t.Run("Map", func(t *testing.T) {
		assert.Equal(t, "{2 entries}", MapValue(map[string]Value{"a": StringValue("1"), "b": StringValue("2")}).String())
	})

	t.Run("Unknown", func(t *testing.T) {
		v := Value{Type: ValueType(99)}
		assert.Equal(t, "unknown(99)", v.String())
	})
}

func TestValueIsEmpty(t *testing.T) {
	assert.True(t, Value{Type: ValueTypeEmpty}.IsEmpty())
	assert.False(t, StringValue("test").IsEmpty())
}

func TestValueEqual(t *testing.T) {
	t.Run("Same type", func(t *testing.T) {
		assert.True(t, StringValue("test").Equal(StringValue("test")))
		assert.False(t, StringValue("test").Equal(StringValue("other")))
	})

	t.Run("Different type", func(t *testing.T) {
		assert.False(t, StringValue("42").Equal(IntValue(42)))
	})

	t.Run("Empty", func(t *testing.T) {
		v1 := Value{Type: ValueTypeEmpty}
		v2 := Value{Type: ValueTypeEmpty}
		assert.True(t, v1.Equal(v2))
	})

	t.Run("Int", func(t *testing.T) {
		assert.True(t, IntValue(42).Equal(IntValue(42)))
		assert.False(t, IntValue(42).Equal(IntValue(43)))
	})

	t.Run("Double", func(t *testing.T) {
		assert.True(t, DoubleValue(3.14).Equal(DoubleValue(3.14)))
		assert.False(t, DoubleValue(3.14).Equal(DoubleValue(2.71)))
	})

	t.Run("Bool", func(t *testing.T) {
		assert.True(t, BoolValue(true).Equal(BoolValue(true)))
		assert.False(t, BoolValue(true).Equal(BoolValue(false)))
	})

	t.Run("Bytes", func(t *testing.T) {
		assert.True(t, BytesValue([]byte{0x01}).Equal(BytesValue([]byte{0x01})))
		assert.False(t, BytesValue([]byte{0x01}).Equal(BytesValue([]byte{0x02})))
	})

	t.Run("Array", func(t *testing.T) {
		arr1 := []Value{StringValue("a"), StringValue("b")}
		arr2 := []Value{StringValue("a"), StringValue("b")}
		arr3 := []Value{StringValue("a")}
		assert.True(t, ArrayValue(arr1).Equal(ArrayValue(arr2)))
		assert.False(t, ArrayValue(arr1).Equal(ArrayValue(arr3)))
	})

	t.Run("Map", func(t *testing.T) {
		m1 := map[string]Value{"a": StringValue("1")}
		m2 := map[string]Value{"a": StringValue("1")}
		m3 := map[string]Value{"b": StringValue("1")}
		assert.True(t, MapValue(m1).Equal(MapValue(m2)))
		assert.False(t, MapValue(m1).Equal(MapValue(m3)))
	})
}

func TestNewAttributes(t *testing.T) {
	t.Run("Valid pairs", func(t *testing.T) {
		attrs := NewAttributes(
			"str", "value",
			"int", 42,
			"float", 3.14,
			"bool", true,
		)

		require.Len(t, attrs, 4)
		assert.Equal(t, "value", attrs.StringValue("str"))
		assert.Equal(t, int64(42), attrs.IntValue("int"))
		assert.Equal(t, 3.14, attrs.FloatValue("float"))
		assert.True(t, attrs.BoolValue("bool"))
	})

	t.Run("Various int types", func(t *testing.T) {
		attrs := NewAttributes(
			"int8", int8(1),
			"int16", int16(2),
			"int32", int32(3),
			"int64", int64(4),
			"uint", uint(5),
			"uint8", uint8(6),
			"uint16", uint16(7),
			"uint32", uint32(8),
			"uint64", uint64(9),
		)

		assert.Equal(t, int64(1), attrs.IntValue("int8"))
		assert.Equal(t, int64(2), attrs.IntValue("int16"))
		assert.Equal(t, int64(3), attrs.IntValue("int32"))
		assert.Equal(t, int64(4), attrs.IntValue("int64"))
		assert.Equal(t, int64(5), attrs.IntValue("uint"))
		assert.Equal(t, int64(6), attrs.IntValue("uint8"))
		assert.Equal(t, int64(7), attrs.IntValue("uint16"))
		assert.Equal(t, int64(8), attrs.IntValue("uint32"))
		assert.Equal(t, int64(9), attrs.IntValue("uint64"))
	})

	t.Run("Float32", func(t *testing.T) {
		attrs := NewAttributes("f", float32(3.14))
		assert.InDelta(t, 3.14, attrs.FloatValue("f"), 0.01)
	})

	t.Run("Panics on odd arguments", func(t *testing.T) {
		assert.Panics(t, func() {
			NewAttributes("key")
		})
	})

	t.Run("Skips non-string keys", func(t *testing.T) {
		attrs := NewAttributes(123, "value")
		assert.Empty(t, attrs)
	})
}

func TestAttributesGet(t *testing.T) {
	attrs := NewAttributes("key1", "value1", "key2", 42)

	t.Run("Get existing", func(t *testing.T) {
		attr, ok := attrs.Get("key1")
		assert.True(t, ok)
		assert.Equal(t, "value1", attr.Value.AsString())
	})

	t.Run("Get non-existing", func(t *testing.T) {
		_, ok := attrs.Get("nonexistent")
		assert.False(t, ok)
	})

	t.Run("Value", func(t *testing.T) {
		v := attrs.Value("key2")
		assert.Equal(t, int64(42), v.AsInt())
	})

	t.Run("StringValue", func(t *testing.T) {
		assert.Equal(t, "value1", attrs.StringValue("key1"))
		assert.Equal(t, "", attrs.StringValue("nonexistent"))
	})

	t.Run("IntValue", func(t *testing.T) {
		assert.Equal(t, int64(42), attrs.IntValue("key2"))
		assert.Equal(t, int64(0), attrs.IntValue("nonexistent"))
	})

	t.Run("FloatValue", func(t *testing.T) {
		assert.Equal(t, 0.0, attrs.FloatValue("key2"))
	})

	t.Run("BoolValue", func(t *testing.T) {
		assert.False(t, attrs.BoolValue("key2"))
	})
}

func TestAttributesLen(t *testing.T) {
	attrs := NewAttributes("a", 1, "b", 2)
	assert.Equal(t, 2, attrs.Len())
	assert.False(t, attrs.IsEmpty())

	empty := Attributes{}
	assert.Equal(t, 0, empty.Len())
	assert.True(t, empty.IsEmpty())
}

func TestAttributesClone(t *testing.T) {
	t.Run("Non-empty", func(t *testing.T) {
		attrs := NewAttributes("key", "value")
		cloned := attrs.Clone()

		assert.Equal(t, attrs.Len(), cloned.Len())
		assert.Equal(t, attrs.StringValue("key"), cloned.StringValue("key"))
	})

	t.Run("Empty", func(t *testing.T) {
		empty := Attributes{}
		cloned := empty.Clone()
		assert.Nil(t, cloned)
	})

	t.Run("Nil", func(t *testing.T) {
		var nilAttrs Attributes
		cloned := nilAttrs.Clone()
		assert.Nil(t, cloned)
	})
}

func TestAttributesToMap(t *testing.T) {
	attrs := NewAttributes("key1", "value1", "key2", 42)
	m := attrs.ToMap()

	assert.Len(t, m, 2)
	assert.Equal(t, StringValue("value1"), m["key1"])
	assert.Equal(t, IntValue(42), m["key2"])
}

func TestAttributesMerge(t *testing.T) {
	t.Run("Both non-empty", func(t *testing.T) {
		a := NewAttributes("key1", "a", "shared", "a")
		b := NewAttributes("key2", "b", "shared", "b")

		merged := a.Merge(b)

		assert.Equal(t, "a", merged.StringValue("key1"))
		assert.Equal(t, "b", merged.StringValue("key2"))
		assert.Equal(t, "b", merged.StringValue("shared")) // b takes precedence
	})

	t.Run("Empty other", func(t *testing.T) {
		a := NewAttributes("key", "value")
		merged := a.Merge(nil)
		assert.Equal(t, "value", merged.StringValue("key"))
	})

	t.Run("Empty receiver", func(t *testing.T) {
		b := NewAttributes("key", "value")
		var empty Attributes
		merged := empty.Merge(b)
		assert.Equal(t, "value", merged.StringValue("key"))
	})
}

func TestAttributesFilter(t *testing.T) {
	attrs := NewAttributes("a", 1, "b", 2, "c", 3)

	filtered := attrs.Filter(func(attr Attribute) bool {
		return attr.Key != "b"
	})

	assert.Len(t, filtered, 2)
	assert.Equal(t, int64(1), filtered.IntValue("a"))
	assert.Equal(t, int64(3), filtered.IntValue("c"))
}

func TestAttributesKeys(t *testing.T) {
	attrs := NewAttributes("b", 1, "a", 2)
	keys := attrs.Keys()

	assert.Len(t, keys, 2)
	assert.Contains(t, keys, "a")
	assert.Contains(t, keys, "b")
}

func TestAttributesValidate(t *testing.T) {
	t.Run("Valid", func(t *testing.T) {
		attrs := NewAttributes("key", "value")
		assert.NoError(t, attrs.Validate())
	})

	t.Run("Empty key", func(t *testing.T) {
		attrs := Attributes{{Key: "", Value: StringValue("value")}}
		err := attrs.Validate()
		assert.ErrorIs(t, err, ErrInvalidAttribute)
	})

	t.Run("Duplicate key", func(t *testing.T) {
		attrs := Attributes{
			{Key: "key", Value: StringValue("value1")},
			{Key: "key", Value: StringValue("value2")},
		}
		err := attrs.Validate()
		assert.ErrorIs(t, err, ErrInvalidAttribute)
	})
}

func TestAttributesJSON(t *testing.T) {
	t.Run("Marshal", func(t *testing.T) {
		attrs := NewAttributes("str", "value", "num", 42)
		data, err := json.Marshal(attrs)
		require.NoError(t, err)

		var m map[string]map[string]any
		err = json.Unmarshal(data, &m)
		require.NoError(t, err)

		// Check the Value structure for "str"
		strVal, ok := m["str"]
		require.True(t, ok)
		assert.Equal(t, float64(ValueTypeString), strVal["type"])
		assert.Equal(t, "value", strVal["string_val"])

		// Check the Value structure for "num"
		numVal, ok := m["num"]
		require.True(t, ok)
		assert.Equal(t, float64(ValueTypeInt), numVal["type"])
		assert.Equal(t, float64(42), numVal["int_val"])
	})

	t.Run("Unmarshal string", func(t *testing.T) {
		data := []byte(`{"key":"value"}`)
		var attrs Attributes
		err := json.Unmarshal(data, &attrs)
		require.NoError(t, err)

		assert.Equal(t, "value", attrs.StringValue("key"))
	})

	t.Run("Unmarshal number", func(t *testing.T) {
		data := []byte(`{"count":42}`)
		var attrs Attributes
		err := json.Unmarshal(data, &attrs)
		require.NoError(t, err)

		// Numbers are unmarshaled as float64
		assert.InDelta(t, 42, attrs.FloatValue("count"), 0.1)
	})

	t.Run("Unmarshal bool", func(t *testing.T) {
		data := []byte(`{"enabled":true}`)
		var attrs Attributes
		err := json.Unmarshal(data, &attrs)
		require.NoError(t, err)

		assert.True(t, attrs.BoolValue("enabled"))
	})
}

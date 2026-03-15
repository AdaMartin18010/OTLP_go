package types

import (
	"encoding/json"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestTraceID(t *testing.T) {
	t.Run("NewTraceID generates valid ID", func(t *testing.T) {
		id := NewTraceID()
		assert.True(t, id.IsValid())
		assert.Len(t, id.String(), 32)
	})

	t.Run("TraceID string representation", func(t *testing.T) {
		id := TraceID{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
			0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10}
		assert.Equal(t, "0102030405060708090a0b0c0d0e0f10", id.String())
	})

	t.Run("ParseTraceID valid", func(t *testing.T) {
		id, err := ParseTraceID("0102030405060708090a0b0c0d0e0f10")
		require.NoError(t, err)
		assert.Equal(t, "0102030405060708090a0b0c0d0e0f10", id.String())
	})

	t.Run("ParseTraceID invalid length", func(t *testing.T) {
		_, err := ParseTraceID("01020304")
		assert.ErrorIs(t, err, ErrInvalidID)
	})

	t.Run("ParseTraceID invalid hex", func(t *testing.T) {
		_, err := ParseTraceID("0102030405060708090a0b0c0d0e0g10")
		assert.Error(t, err)
	})

	t.Run("TraceID IsValid", func(t *testing.T) {
		valid := TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
		assert.True(t, valid.IsValid())

		invalid := TraceID{}
		assert.False(t, invalid.IsValid())
	})

	t.Run("TraceID JSON marshal/unmarshal", func(t *testing.T) {
		id := TraceID{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
			0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10}

		data, err := json.Marshal(id)
		require.NoError(t, err)
		assert.Equal(t, `"0102030405060708090a0b0c0d0e0f10"`, string(data))

		var parsed TraceID
		err = json.Unmarshal(data, &parsed)
		require.NoError(t, err)
		assert.Equal(t, id, parsed)
	})

	t.Run("TraceID Text marshal/unmarshal", func(t *testing.T) {
		id := TraceID{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
			0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10}

		text, err := id.MarshalText()
		require.NoError(t, err)
		assert.Equal(t, "0102030405060708090a0b0c0d0e0f10", string(text))

		var parsed TraceID
		err = parsed.UnmarshalText(text)
		require.NoError(t, err)
		assert.Equal(t, id, parsed)
	})
}

func TestSpanID(t *testing.T) {
	t.Run("NewSpanID generates valid ID", func(t *testing.T) {
		id := NewSpanID()
		assert.True(t, id.IsValid())
		assert.Len(t, id.String(), 16)
	})

	t.Run("SpanID string representation", func(t *testing.T) {
		id := SpanID{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08}
		assert.Equal(t, "0102030405060708", id.String())
	})

	t.Run("ParseSpanID valid", func(t *testing.T) {
		id, err := ParseSpanID("0102030405060708")
		require.NoError(t, err)
		assert.Equal(t, "0102030405060708", id.String())
	})

	t.Run("ParseSpanID invalid length", func(t *testing.T) {
		_, err := ParseSpanID("0102")
		assert.ErrorIs(t, err, ErrInvalidID)
	})

	t.Run("SpanID IsValid", func(t *testing.T) {
		valid := SpanID{1, 2, 3, 4, 5, 6, 7, 8}
		assert.True(t, valid.IsValid())

		invalid := SpanID{}
		assert.False(t, invalid.IsValid())
	})

	t.Run("SpanID JSON marshal/unmarshal", func(t *testing.T) {
		id := SpanID{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08}

		data, err := json.Marshal(id)
		require.NoError(t, err)
		assert.Equal(t, `"0102030405060708"`, string(data))

		var parsed SpanID
		err = json.Unmarshal(data, &parsed)
		require.NoError(t, err)
		assert.Equal(t, id, parsed)
	})
}

func TestFlags(t *testing.T) {
	t.Run("IsSampled", func(t *testing.T) {
		flags := FlagSampled
		assert.True(t, flags.IsSampled())

		flags = 0
		assert.False(t, flags.IsSampled())
	})

	t.Run("WithSampled", func(t *testing.T) {
		flags := Flags(0)
		flags = flags.WithSampled(true)
		assert.True(t, flags.IsSampled())

		flags = flags.WithSampled(false)
		assert.False(t, flags.IsSampled())
	})

	t.Run("String", func(t *testing.T) {
		flags := FlagSampled
		assert.Equal(t, "01", flags.String())
	})
}

func TestTimestamp(t *testing.T) {
	t.Run("NewTimestamp", func(t *testing.T) {
		now := time.Now().UTC()
		ts := NewTimestamp(now)
		assert.Equal(t, now.UnixNano(), ts.UnixNano())
	})

	t.Run("Now", func(t *testing.T) {
		before := time.Now().UTC().Add(-time.Second)
		ts := Now()
		after := time.Now().UTC().Add(time.Second)

		assert.True(t, ts.Time.After(before) || ts.Time.Equal(before))
		assert.True(t, ts.Time.Before(after) || ts.Time.Equal(after))
	})

	t.Run("UnixNano", func(t *testing.T) {
		now := time.Now().UTC()
		ts := NewTimestamp(now)
		assert.Equal(t, now.UnixNano(), ts.UnixNano())
	})

	t.Run("Add", func(t *testing.T) {
		ts := NewTimestamp(time.Unix(1000, 0).UTC())
		later := ts.Add(time.Hour)
		assert.Equal(t, time.Unix(1000, 0).Add(time.Hour).UTC(), later.Time)
	})

	t.Run("Sub", func(t *testing.T) {
		ts1 := NewTimestamp(time.Unix(1000, 0).UTC())
		ts2 := NewTimestamp(time.Unix(1001, 0).UTC())
		diff := ts2.Sub(ts1)
		assert.Equal(t, time.Second, diff)
	})

	t.Run("JSON marshal/unmarshal", func(t *testing.T) {
		ts := NewTimestamp(time.Unix(0, 1234567890123456789).UTC())

		data, err := json.Marshal(ts)
		require.NoError(t, err)
		assert.Equal(t, "1234567890123456789", string(data))

		var parsed Timestamp
		err = json.Unmarshal(data, &parsed)
		require.NoError(t, err)
		assert.Equal(t, ts.UnixNano(), parsed.UnixNano())
	})
}

func TestDuration(t *testing.T) {
	t.Run("NewDuration", func(t *testing.T) {
		d := NewDuration(5 * time.Second)
		assert.Equal(t, 5*time.Second, d.Duration)
	})

	t.Run("Millis", func(t *testing.T) {
		d := NewDuration(1500 * time.Millisecond)
		assert.Equal(t, int64(1500), d.Millis())
	})

	t.Run("Micros", func(t *testing.T) {
		d := NewDuration(1500 * time.Microsecond)
		assert.Equal(t, int64(1500), d.Micros())
	})

	t.Run("Nanos", func(t *testing.T) {
		d := NewDuration(1500 * time.Nanosecond)
		assert.Equal(t, int64(1500), d.Nanos())
	})

	t.Run("JSON marshal/unmarshal", func(t *testing.T) {
		d := NewDuration(5 * time.Second)

		data, err := json.Marshal(d)
		require.NoError(t, err)
		assert.Equal(t, "5000000000", string(data))

		var parsed Duration
		err = json.Unmarshal(data, &parsed)
		require.NoError(t, err)
		assert.Equal(t, d.Duration, parsed.Duration)
	})
}

func TestStatusCode(t *testing.T) {
	t.Run("String", func(t *testing.T) {
		assert.Equal(t, "Unset", StatusUnset.String())
		assert.Equal(t, "Ok", StatusOK.String())
		assert.Equal(t, "Error", StatusError.String())
		assert.Equal(t, "StatusCode(99)", StatusCode(99).String())
	})

	t.Run("IsError", func(t *testing.T) {
		assert.False(t, StatusUnset.IsError())
		assert.False(t, StatusOK.IsError())
		assert.True(t, StatusError.IsError())
	})
}

func TestSpanKind(t *testing.T) {
	t.Run("String", func(t *testing.T) {
		assert.Equal(t, "Unspecified", SpanKindUnspecified.String())
		assert.Equal(t, "Internal", SpanKindInternal.String())
		assert.Equal(t, "Server", SpanKindServer.String())
		assert.Equal(t, "Client", SpanKindClient.String())
		assert.Equal(t, "Producer", SpanKindProducer.String())
		assert.Equal(t, "Consumer", SpanKindConsumer.String())
		assert.Equal(t, "SpanKind(99)", SpanKind(99).String())
	})

	t.Run("IsValid", func(t *testing.T) {
		assert.True(t, SpanKindUnspecified.IsValid())
		assert.True(t, SpanKindInternal.IsValid())
		assert.True(t, SpanKindServer.IsValid())
		assert.True(t, SpanKindClient.IsValid())
		assert.True(t, SpanKindProducer.IsValid())
		assert.True(t, SpanKindConsumer.IsValid())
		assert.False(t, SpanKind(-1).IsValid())
		assert.False(t, SpanKind(99).IsValid())
	})
}

func TestLogLevel(t *testing.T) {
	t.Run("String", func(t *testing.T) {
		assert.Equal(t, "UNSPECIFIED", LogLevelUnspecified.String())
		assert.Equal(t, "TRACE", LogLevelTrace.String())
		assert.Equal(t, "DEBUG", LogLevelDebug.String())
		assert.Equal(t, "INFO", LogLevelInfo.String())
		assert.Equal(t, "WARN", LogLevelWarn.String())
		assert.Equal(t, "ERROR", LogLevelError.String())
		assert.Equal(t, "FATAL", LogLevelFatal.String())
		assert.Equal(t, "LogLevel(99)", LogLevel(99).String())
	})

	t.Run("IsValid", func(t *testing.T) {
		assert.True(t, LogLevelUnspecified.IsValid())
		assert.True(t, LogLevelTrace.IsValid())
		assert.True(t, LogLevelDebug.IsValid())
		assert.True(t, LogLevelInfo.IsValid())
		assert.True(t, LogLevelWarn.IsValid())
		assert.True(t, LogLevelError.IsValid())
		assert.True(t, LogLevelFatal.IsValid())
		assert.False(t, LogLevel(-1).IsValid())
		assert.False(t, LogLevel(99).IsValid())
	})

	t.Run("SeverityNumber", func(t *testing.T) {
		assert.Equal(t, int32(0), LogLevelUnspecified.SeverityNumber())
		assert.Equal(t, int32(1), LogLevelTrace.SeverityNumber())
		assert.Equal(t, int32(5), LogLevelDebug.SeverityNumber())
		assert.Equal(t, int32(9), LogLevelInfo.SeverityNumber())
		assert.Equal(t, int32(13), LogLevelWarn.SeverityNumber())
		assert.Equal(t, int32(17), LogLevelError.SeverityNumber())
		assert.Equal(t, int32(21), LogLevelFatal.SeverityNumber())
	})
}

func TestValueType(t *testing.T) {
	t.Run("String", func(t *testing.T) {
		assert.Equal(t, "Empty", ValueTypeEmpty.String())
		assert.Equal(t, "String", ValueTypeString.String())
		assert.Equal(t, "Int", ValueTypeInt.String())
		assert.Equal(t, "Double", ValueTypeDouble.String())
		assert.Equal(t, "Bool", ValueTypeBool.String())
		assert.Equal(t, "Bytes", ValueTypeBytes.String())
		assert.Equal(t, "Array", ValueTypeArray.String())
		assert.Equal(t, "Map", ValueTypeMap.String())
		assert.Equal(t, "ValueType(99)", ValueType(99).String())
	})
}

func TestErrors(t *testing.T) {
	t.Run("Error constants", func(t *testing.T) {
		assert.NotNil(t, ErrInvalidID)
		assert.NotNil(t, ErrNilResource)
		assert.NotNil(t, ErrInvalidAttribute)
		assert.NotNil(t, ErrEmptyTelemetry)
	})
}

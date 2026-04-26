// Package types provides shared types and interfaces
// for the OTLP Go SDK.
//
// This package defines:
//   - Core SDK interfaces
//   - Type aliases for common patterns
//   - Generic type constraints
//   - Common data structures
//
// Example usage:
//
//	attr := types.NewAttribute("service.name", "my-service")
//	resource := types.NewResource(types.Attributes{attr})
//
//	span := types.Span{
//	    TraceID: types.NewTraceID(),
//	    SpanID:  types.NewSpanID(),
//	    Name:    "process-request",
//	}
package types

import (
	"crypto/rand"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"fmt"
	"time"
)

var (
	// ErrInvalidID is returned when an ID is malformed.
	ErrInvalidID = errors.New("invalid ID format")
	// ErrNilResource is returned when a nil resource is used where required.
	ErrNilResource = errors.New("resource is nil")
	// ErrInvalidAttribute is returned when an attribute is invalid.
	ErrInvalidAttribute = errors.New("invalid attribute")
	// ErrEmptyTelemetry is returned when telemetry data is empty.
	ErrEmptyTelemetry = errors.New("telemetry data is empty")
)

// TraceID is a 16-byte unique identifier for a trace.
type TraceID [16]byte

// String returns the hex string representation of the TraceID.
func (t TraceID) String() string {
	return hex.EncodeToString(t[:])
}

// IsValid returns true if the TraceID is valid (non-zero).
func (t TraceID) IsValid() bool {
	return t != [16]byte{}
}

// MarshalJSON implements json.Marshaler.
func (t TraceID) MarshalJSON() ([]byte, error) {
	return []byte(fmt.Sprintf("%q", t.String())), nil
}

// UnmarshalJSON implements json.Unmarshaler.
func (t *TraceID) UnmarshalJSON(data []byte) error {
	if len(data) < 2 || data[0] != '"' || data[len(data)-1] != '"' {
		return ErrInvalidID
	}
	return t.UnmarshalText(data[1 : len(data)-1])
}

// MarshalText implements encoding.TextMarshaler.
func (t TraceID) MarshalText() ([]byte, error) {
	return []byte(t.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (t *TraceID) UnmarshalText(data []byte) error {
	if len(data) != 32 {
		return ErrInvalidID
	}
	_, err := hex.Decode(t[:], data)
	return err
}

// SpanID is an 8-byte unique identifier for a span.
type SpanID [8]byte

// String returns the hex string representation of the SpanID.
func (s SpanID) String() string {
	return hex.EncodeToString(s[:])
}

// IsValid returns true if the SpanID is valid (non-zero).
func (s SpanID) IsValid() bool {
	return s != [8]byte{}
}

// MarshalJSON implements json.Marshaler.
func (s SpanID) MarshalJSON() ([]byte, error) {
	return []byte(fmt.Sprintf("%q", s.String())), nil
}

// UnmarshalJSON implements json.Unmarshaler.
func (s *SpanID) UnmarshalJSON(data []byte) error {
	if len(data) < 2 || data[0] != '"' || data[len(data)-1] != '"' {
		return ErrInvalidID
	}
	return s.UnmarshalText(data[1 : len(data)-1])
}

// MarshalText implements encoding.TextMarshaler.
func (s SpanID) MarshalText() ([]byte, error) {
	return []byte(s.String()), nil
}

// UnmarshalText implements encoding.TextUnmarshaler.
func (s *SpanID) UnmarshalText(data []byte) error {
	if len(data) != 16 {
		return ErrInvalidID
	}
	_, err := hex.Decode(s[:], data)
	return err
}

// NewTraceID generates a new random TraceID compliant with W3C Trace Context Level 2.
// The rightmost 7 bytes (bytes 9-15) are guaranteed to be truly random,
// satisfying the random-trace-id requirement.
func NewTraceID() TraceID {
	var id TraceID
	if _, err := rand.Read(id[:]); err != nil {
		// Fallback: timestamp in first 8 bytes, pseudo-random in remaining bytes.
		now := uint64(time.Now().UnixNano())
		binary.BigEndian.PutUint64(id[:8], now)
		binary.BigEndian.PutUint64(id[8:], now)
	}

	// Explicitly ensure the rightmost 7 bytes (indices 9-15) are random
	// per W3C Trace Context Level 2 specification.
	if _, err := rand.Read(id[9:]); err != nil {
		// If crypto/rand fails for the second read, use timestamp-based
		// pseudo-random for the remaining bytes as a last resort.
		now := uint64(time.Now().UnixNano())
		binary.BigEndian.PutUint64(id[8:], now)
	}

	return id
}

// NewSpanID generates a new random SpanID.
func NewSpanID() SpanID {
	var id SpanID
	if _, err := rand.Read(id[:]); err != nil {
		// Fallback to timestamp-based ID if crypto/rand fails
		binary.BigEndian.PutUint64(id[:], uint64(time.Now().UnixNano()))
	}
	return id
}

// ParseTraceID parses a hex string into a TraceID.
func ParseTraceID(s string) (TraceID, error) {
	var id TraceID
	if err := id.UnmarshalText([]byte(s)); err != nil {
		return TraceID{}, err
	}
	return id, nil
}

// ParseSpanID parses a hex string into a SpanID.
func ParseSpanID(s string) (SpanID, error) {
	var id SpanID
	if err := id.UnmarshalText([]byte(s)); err != nil {
		return SpanID{}, err
	}
	return id, nil
}

// Flags represents trace flags as defined in W3C Trace Context.
type Flags byte

const (
	// FlagSampled indicates the trace is sampled.
	FlagSampled Flags = 1 << 0
	// FlagRandom indicates the trace ID was randomly generated.
	FlagRandom Flags = 1 << 1
)

// IsSampled returns true if the sampled flag is set.
func (f Flags) IsSampled() bool {
	return f&FlagSampled != 0
}

// IsRandom returns true if the random trace ID flag is set.
func (f Flags) IsRandom() bool {
	return f&FlagRandom != 0
}

// WithSampled returns a new Flags with the sampled flag set or cleared.
func (f Flags) WithSampled(sampled bool) Flags {
	if sampled {
		return f | FlagSampled
	}
	return f & ^FlagSampled
}

// String returns the hex string representation of the flags.
func (f Flags) String() string {
	return fmt.Sprintf("%02x", byte(f))
}

// Timestamp represents a point in time with nanosecond precision.
type Timestamp struct {
	time.Time
}

// NewTimestamp creates a new Timestamp from a time.Time.
func NewTimestamp(t time.Time) Timestamp {
	return Timestamp{t}
}

// Now returns the current time as a Timestamp.
func Now() Timestamp {
	return Timestamp{time.Now().UTC()}
}

// UnixNano returns the timestamp as Unix nanoseconds.
func (t Timestamp) UnixNano() int64 {
	return t.Time.UnixNano()
}

// Add returns a new Timestamp with the given duration added.
func (t Timestamp) Add(d time.Duration) Timestamp {
	return Timestamp{t.Time.Add(d)}
}

// Sub returns the duration between two timestamps.
func (t Timestamp) Sub(other Timestamp) time.Duration {
	return t.Time.Sub(other.Time)
}

// MarshalJSON implements json.Marshaler.
func (t Timestamp) MarshalJSON() ([]byte, error) {
	return []byte(fmt.Sprintf("%d", t.UnixNano())), nil
}

// UnmarshalJSON implements json.Unmarshaler.
func (t *Timestamp) UnmarshalJSON(data []byte) error {
	var nanos int64
	if _, err := fmt.Sscanf(string(data), "%d", &nanos); err != nil {
		return err
	}
	t.Time = time.Unix(0, nanos).UTC()
	return nil
}

// Duration represents a time duration for telemetry data.
type Duration struct {
	time.Duration
}

// NewDuration creates a new Duration from a time.Duration.
func NewDuration(d time.Duration) Duration {
	return Duration{d}
}

// Millis returns the duration in milliseconds.
func (d Duration) Millis() int64 {
	return d.Milliseconds()
}

// Micros returns the duration in microseconds.
func (d Duration) Micros() int64 {
	return d.Microseconds()
}

// Nanos returns the duration in nanoseconds.
func (d Duration) Nanos() int64 {
	return d.Nanoseconds()
}

// MarshalJSON implements json.Marshaler.
func (d Duration) MarshalJSON() ([]byte, error) {
	return []byte(fmt.Sprintf("%d", d.Nanoseconds())), nil
}

// UnmarshalJSON implements json.Unmarshaler.
func (d *Duration) UnmarshalJSON(data []byte) error {
	var nanos int64
	if _, err := fmt.Sscanf(string(data), "%d", &nanos); err != nil {
		return err
	}
	d.Duration = time.Duration(nanos)
	return nil
}

// StatusCode represents the status code of a span.
type StatusCode uint32

const (
	// StatusUnset is the default status code.
	StatusUnset StatusCode = 0
	// StatusOK indicates the operation completed successfully.
	StatusOK StatusCode = 1
	// StatusError indicates an error occurred.
	StatusError StatusCode = 2
)

// String returns the string representation of the status code.
func (s StatusCode) String() string {
	switch s {
	case StatusUnset:
		return "Unset"
	case StatusOK:
		return "Ok"
	case StatusError:
		return "Error"
	default:
		return fmt.Sprintf("StatusCode(%d)", s)
	}
}

// IsError returns true if the status indicates an error.
func (s StatusCode) IsError() bool {
	return s == StatusError
}

// SpanKind represents the kind of span.
type SpanKind int32

const (
	// SpanKindUnspecified indicates the span kind was not specified.
	SpanKindUnspecified SpanKind = 0
	// SpanKindInternal indicates an internal operation.
	SpanKindInternal SpanKind = 1
	// SpanKindServer indicates a server operation.
	SpanKindServer SpanKind = 2
	// SpanKindClient indicates a client operation.
	SpanKindClient SpanKind = 3
	// SpanKindProducer indicates a producer operation.
	SpanKindProducer SpanKind = 4
	// SpanKindConsumer indicates a consumer operation.
	SpanKindConsumer SpanKind = 5
)

// String returns the string representation of the span kind.
func (k SpanKind) String() string {
	switch k {
	case SpanKindUnspecified:
		return "Unspecified"
	case SpanKindInternal:
		return "Internal"
	case SpanKindServer:
		return "Server"
	case SpanKindClient:
		return "Client"
	case SpanKindProducer:
		return "Producer"
	case SpanKindConsumer:
		return "Consumer"
	default:
		return fmt.Sprintf("SpanKind(%d)", k)
	}
}

// IsValid returns true if the span kind is valid.
func (k SpanKind) IsValid() bool {
	return k >= SpanKindUnspecified && k <= SpanKindConsumer
}

// SeverityNumber represents the OpenTelemetry severity number (1-24).
type SeverityNumber = int32

const (
	// SeverityNumberTrace1 is the lowest trace severity.
	SeverityNumberTrace1 SeverityNumber = 1
	// SeverityNumberTrace2 is trace severity level 2.
	SeverityNumberTrace2 SeverityNumber = 2
	// SeverityNumberTrace3 is trace severity level 3.
	SeverityNumberTrace3 SeverityNumber = 3
	// SeverityNumberTrace4 is the highest trace severity.
	SeverityNumberTrace4 SeverityNumber = 4
	// SeverityNumberDebug1 is the lowest debug severity.
	SeverityNumberDebug1 SeverityNumber = 5
	// SeverityNumberDebug2 is debug severity level 2.
	SeverityNumberDebug2 SeverityNumber = 6
	// SeverityNumberDebug3 is debug severity level 3.
	SeverityNumberDebug3 SeverityNumber = 7
	// SeverityNumberDebug4 is the highest debug severity.
	SeverityNumberDebug4 SeverityNumber = 8
	// SeverityNumberInfo1 is the lowest info severity.
	SeverityNumberInfo1 SeverityNumber = 9
	// SeverityNumberInfo2 is info severity level 2.
	SeverityNumberInfo2 SeverityNumber = 10
	// SeverityNumberInfo3 is info severity level 3.
	SeverityNumberInfo3 SeverityNumber = 11
	// SeverityNumberInfo4 is the highest info severity.
	SeverityNumberInfo4 SeverityNumber = 12
	// SeverityNumberWarn1 is the lowest warn severity.
	SeverityNumberWarn1 SeverityNumber = 13
	// SeverityNumberWarn2 is warn severity level 2.
	SeverityNumberWarn2 SeverityNumber = 14
	// SeverityNumberWarn3 is warn severity level 3.
	SeverityNumberWarn3 SeverityNumber = 15
	// SeverityNumberWarn4 is the highest warn severity.
	SeverityNumberWarn4 SeverityNumber = 16
	// SeverityNumberError1 is the lowest error severity.
	SeverityNumberError1 SeverityNumber = 17
	// SeverityNumberError2 is error severity level 2.
	SeverityNumberError2 SeverityNumber = 18
	// SeverityNumberError3 is error severity level 3.
	SeverityNumberError3 SeverityNumber = 19
	// SeverityNumberError4 is the highest error severity.
	SeverityNumberError4 SeverityNumber = 20
	// SeverityNumberFatal1 is the lowest fatal severity.
	SeverityNumberFatal1 SeverityNumber = 21
	// SeverityNumberFatal2 is fatal severity level 2.
	SeverityNumberFatal2 SeverityNumber = 22
	// SeverityNumberFatal3 is fatal severity level 3.
	SeverityNumberFatal3 SeverityNumber = 23
	// SeverityNumberFatal4 is the highest fatal severity.
	SeverityNumberFatal4 SeverityNumber = 24
)

// ValidateSeverityNumber validates that a severity number is in the valid range 1-24.
func ValidateSeverityNumber(n int32) error {
	if n < 1 || n > 24 {
		return fmt.Errorf("invalid severity number %d: must be between 1 and 24", n)
	}
	return nil
}

// SeverityText returns the severity text for a given severity number.
func SeverityText(n SeverityNumber) string {
	switch n {
	case SeverityNumberTrace1:
		return "TRACE"
	case SeverityNumberTrace2:
		return "TRACE2"
	case SeverityNumberTrace3:
		return "TRACE3"
	case SeverityNumberTrace4:
		return "TRACE4"
	case SeverityNumberDebug1:
		return "DEBUG"
	case SeverityNumberDebug2:
		return "DEBUG2"
	case SeverityNumberDebug3:
		return "DEBUG3"
	case SeverityNumberDebug4:
		return "DEBUG4"
	case SeverityNumberInfo1:
		return "INFO"
	case SeverityNumberInfo2:
		return "INFO2"
	case SeverityNumberInfo3:
		return "INFO3"
	case SeverityNumberInfo4:
		return "INFO4"
	case SeverityNumberWarn1:
		return "WARN"
	case SeverityNumberWarn2:
		return "WARN2"
	case SeverityNumberWarn3:
		return "WARN3"
	case SeverityNumberWarn4:
		return "WARN4"
	case SeverityNumberError1:
		return "ERROR"
	case SeverityNumberError2:
		return "ERROR2"
	case SeverityNumberError3:
		return "ERROR3"
	case SeverityNumberError4:
		return "ERROR4"
	case SeverityNumberFatal1:
		return "FATAL"
	case SeverityNumberFatal2:
		return "FATAL2"
	case SeverityNumberFatal3:
		return "FATAL3"
	case SeverityNumberFatal4:
		return "FATAL4"
	default:
		return fmt.Sprintf("SeverityNumber(%d)", n)
	}
}

// LogLevel represents the severity level of a log record.
type LogLevel int32

const (
	// LogLevelUnspecified indicates the log level was not specified.
	LogLevelUnspecified LogLevel = 0
	// LogLevelTrace indicates trace level logging.
	LogLevelTrace LogLevel = 1
	// LogLevelDebug indicates debug level logging.
	LogLevelDebug LogLevel = 2
	// LogLevelInfo indicates info level logging.
	LogLevelInfo LogLevel = 3
	// LogLevelWarn indicates warn level logging.
	LogLevelWarn LogLevel = 4
	// LogLevelError indicates error level logging.
	LogLevelError LogLevel = 5
	// LogLevelFatal indicates fatal level logging.
	LogLevelFatal LogLevel = 6
)

// String returns the string representation of the log level.
func (l LogLevel) String() string {
	switch l {
	case LogLevelUnspecified:
		return "UNSPECIFIED"
	case LogLevelTrace:
		return "TRACE"
	case LogLevelDebug:
		return "DEBUG"
	case LogLevelInfo:
		return "INFO"
	case LogLevelWarn:
		return "WARN"
	case LogLevelError:
		return "ERROR"
	case LogLevelFatal:
		return "FATAL"
	default:
		return fmt.Sprintf("LogLevel(%d)", l)
	}
}

// IsValid returns true if the log level is valid.
func (l LogLevel) IsValid() bool {
	return l >= LogLevelUnspecified && l <= LogLevelFatal
}

// SeverityNumber returns the OpenTelemetry severity number (1-24).
func (l LogLevel) SeverityNumber() SeverityNumber {
	// Map our levels to OpenTelemetry severity numbers
	// https://opentelemetry.io/docs/specs/otel/logs/data-model/#severity-fields
	switch l {
	case LogLevelTrace:
		return SeverityNumberTrace1
	case LogLevelDebug:
		return SeverityNumberDebug1
	case LogLevelInfo:
		return SeverityNumberInfo1
	case LogLevelWarn:
		return SeverityNumberWarn1
	case LogLevelError:
		return SeverityNumberError1
	case LogLevelFatal:
		return SeverityNumberFatal1
	default:
		return 0
	}
}

// ValueType represents the type of an attribute value.
type ValueType int32

const (
	// ValueTypeEmpty indicates an empty value.
	ValueTypeEmpty ValueType = 0
	// ValueTypeString indicates a string value.
	ValueTypeString ValueType = 1
	// ValueTypeInt indicates an int64 value.
	ValueTypeInt ValueType = 2
	// ValueTypeDouble indicates a float64 value.
	ValueTypeDouble ValueType = 3
	// ValueTypeBool indicates a bool value.
	ValueTypeBool ValueType = 4
	// ValueTypeBytes indicates a byte slice value.
	ValueTypeBytes ValueType = 5
	// ValueTypeArray indicates an array value.
	ValueTypeArray ValueType = 6
	// ValueTypeMap indicates a map value.
	ValueTypeMap ValueType = 7
)

// String returns the string representation of the value type.
func (v ValueType) String() string {
	switch v {
	case ValueTypeEmpty:
		return "Empty"
	case ValueTypeString:
		return "String"
	case ValueTypeInt:
		return "Int"
	case ValueTypeDouble:
		return "Double"
	case ValueTypeBool:
		return "Bool"
	case ValueTypeBytes:
		return "Bytes"
	case ValueTypeArray:
		return "Array"
	case ValueTypeMap:
		return "Map"
	default:
		return fmt.Sprintf("ValueType(%d)", v)
	}
}

// Package testing provides testing utilities for the OTLP Go SDK.
//
// Stability: Stable
// Compliance: OpenTelemetry Specification v1.42.0
package testing

import (
	"context"
	"fmt"
	"reflect"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// AssertSpanCount asserts that the expected number of spans was recorded.
func AssertSpanCount(t testing.TB, spans []ReadableSpan, expected int) {
	t.Helper()
	assert.Len(t, spans, expected, "Expected %d spans, got %d", expected, len(spans))
}

// RequireSpanCount requires that the expected number of spans was recorded.
func RequireSpanCount(t testing.TB, spans []ReadableSpan, expected int) {
	t.Helper()
	require.Len(t, spans, expected, "Expected %d spans, got %d", expected, len(spans))
}

// AssertSpanName asserts that a span has the expected name.
func AssertSpanName(t testing.TB, span ReadableSpan, expected string) {
	t.Helper()
	assert.Equal(t, expected, span.Name(), "Span name mismatch")
}

// RequireSpanName requires that a span has the expected name.
func RequireSpanName(t testing.TB, span ReadableSpan, expected string) {
	t.Helper()
	require.Equal(t, expected, span.Name(), "Span name mismatch")
}

// AssertSpanKind asserts that a span has the expected kind.
func AssertSpanKind(t testing.TB, span ReadableSpan, expected trace.SpanKind) {
	t.Helper()
	assert.Equal(t, expected, span.SpanKind(), "Span kind mismatch")
}

// RequireSpanKind requires that a span has the expected kind.
func RequireSpanKind(t testing.TB, span ReadableSpan, expected trace.SpanKind) {
	t.Helper()
	require.Equal(t, expected, span.SpanKind(), "Span kind mismatch")
}

// AssertSpanStatus asserts that a span has the expected status code and description.
func AssertSpanStatus(t testing.TB, span ReadableSpan, code StatusCode, description string) {
	t.Helper()
	status := span.Status()
	assert.Equal(t, code, status.Code, "Status code mismatch")
	if description != "" {
		assert.Equal(t, description, status.Description, "Status description mismatch")
	}
}

// RequireSpanStatus requires that a span has the expected status code and description.
func RequireSpanStatus(t testing.TB, span ReadableSpan, code StatusCode, description string) {
	t.Helper()
	status := span.Status()
	require.Equal(t, code, status.Code, "Status code mismatch")
	if description != "" {
		require.Equal(t, description, status.Description, "Status description mismatch")
	}
}

// AssertSpanHasAttribute asserts that a span has a specific attribute.
func AssertSpanHasAttribute(t testing.TB, span ReadableSpan, key string, expectedValue interface{}) {
	t.Helper()
	attrs := span.Attributes()

	for _, attr := range attrs {
		if string(attr.Key) == key {
			actualValue := attr.Value.AsInterface()
			assert.Equal(t, expectedValue, actualValue, "Attribute %s value mismatch", key)
			return
		}
	}

	assert.Fail(t, fmt.Sprintf("Attribute %s not found in span", key))
}

// RequireSpanHasAttribute requires that a span has a specific attribute.
func RequireSpanHasAttribute(t testing.TB, span ReadableSpan, key string, expectedValue interface{}) {
	t.Helper()
	attrs := span.Attributes()

	for _, attr := range attrs {
		if string(attr.Key) == key {
			actualValue := attr.Value.AsInterface()
			require.Equal(t, expectedValue, actualValue, "Attribute %s value mismatch", key)
			return
		}
	}

	t.Fatalf("Attribute %s not found in span", key)
}

// AssertSpanHasEvent asserts that a span has an event with the expected name.
func AssertSpanHasEvent(t testing.TB, span ReadableSpan, eventName string) bool {
	t.Helper()
	for _, event := range span.Events() {
		if event.Name == eventName {
			return true
		}
	}
	assert.Fail(t, fmt.Sprintf("Event %s not found in span", eventName))
	return false
}

// RequireSpanHasEvent requires that a span has an event with the expected name.
func RequireSpanHasEvent(t testing.TB, span ReadableSpan, eventName string) {
	t.Helper()
	for _, event := range span.Events() {
		if event.Name == eventName {
			return
		}
	}
	t.Fatalf("Event %s not found in span", eventName)
}

// AssertSpanContainsString asserts that a span's string representation contains a substring.
func AssertSpanContainsString(t testing.TB, span ReadableSpan, substr string) {
	t.Helper()
	spanStr := fmt.Sprintf("%+v", span)
	assert.Contains(t, spanStr, substr, "Span does not contain expected string")
}

// AssertSpansInOrder asserts that spans were recorded in the expected order.
func AssertSpansInOrder(t testing.TB, spans []ReadableSpan, names ...string) {
	t.Helper()
	if len(spans) != len(names) {
		assert.Fail(t, fmt.Sprintf("Expected %d spans, got %d", len(names), len(spans)))
		return
	}

	for i, span := range spans {
		if span.Name() != names[i] {
			assert.Fail(t, fmt.Sprintf("Expected span %d to be %s, got %s", i, names[i], span.Name()))
			return
		}
	}
}

// AssertError asserts that an error is not nil.
func AssertError(t testing.TB, err error, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Error(t, err, msgAndArgs...)
}

// AssertNoError asserts that an error is nil.
func AssertNoError(t testing.TB, err error, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NoError(t, err, msgAndArgs...)
}

// RequireNoError requires that an error is nil.
func RequireNoError(t testing.TB, err error, msgAndArgs ...interface{}) {
	t.Helper()
	require.NoError(t, err, msgAndArgs...)
}

// AssertErrorContains asserts that an error contains the expected substring.
func AssertErrorContains(t testing.TB, err error, substr string, msgAndArgs ...interface{}) bool {
	t.Helper()
	if err == nil {
		return assert.Fail(t, "Expected error to contain substring, but got nil", msgAndArgs...)
	}
	return assert.Contains(t, err.Error(), substr, msgAndArgs...)
}

// AssertContextCancelled asserts that a context is cancelled.
func AssertContextCancelled(t testing.TB, ctx context.Context, msgAndArgs ...interface{}) bool {
	t.Helper()
	select {
	case <-ctx.Done():
		return true
	default:
		return assert.Fail(t, "Expected context to be cancelled, but it was not", msgAndArgs...)
	}
}

// AssertContextNotCancelled asserts that a context is not cancelled.
func AssertContextNotCancelled(t testing.TB, ctx context.Context, msgAndArgs ...interface{}) bool {
	t.Helper()
	select {
	case <-ctx.Done():
		return assert.Fail(t, "Expected context to not be cancelled, but it was", msgAndArgs...)
	default:
		return true
	}
}

// AssertDeadlineSet asserts that a context has a deadline set.
func AssertDeadlineSet(t testing.TB, ctx context.Context, msgAndArgs ...interface{}) (time.Time, bool) {
	t.Helper()
	deadline, ok := ctx.Deadline()
	if !ok {
		assert.Fail(t, "Expected context to have deadline, but it does not", msgAndArgs...)
	}
	return deadline, ok
}

// AssertContains asserts that a string contains a substring.
func AssertContains(t testing.TB, s, substr string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Contains(t, s, substr, msgAndArgs...)
}

// AssertNotContains asserts that a string does not contain a substring.
func AssertNotContains(t testing.TB, s, substr string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotContains(t, s, substr, msgAndArgs...)
}

// AssertEqual asserts that two values are equal.
func AssertEqual(t testing.TB, expected, actual interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Equal(t, expected, actual, msgAndArgs...)
}

// AssertNotEqual asserts that two values are not equal.
func AssertNotEqual(t testing.TB, expected, actual interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotEqual(t, expected, actual, msgAndArgs...)
}

// AssertTrue asserts that a condition is true.
func AssertTrue(t testing.TB, condition bool, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.True(t, condition, msgAndArgs...)
}

// AssertFalse asserts that a condition is false.
func AssertFalse(t testing.TB, condition bool, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.False(t, condition, msgAndArgs...)
}

// AssertNil asserts that a value is nil.
func AssertNil(t testing.TB, object interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Nil(t, object, msgAndArgs...)
}

// AssertNotNil asserts that a value is not nil.
func AssertNotNil(t testing.TB, object interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotNil(t, object, msgAndArgs...)
}

// AssertEmpty asserts that a value is empty.
func AssertEmpty(t testing.TB, object interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Empty(t, object, msgAndArgs...)
}

// AssertNotEmpty asserts that a value is not empty.
func AssertNotEmpty(t testing.TB, object interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotEmpty(t, object, msgAndArgs...)
}

// AssertLen asserts that a collection has the expected length.
func AssertLen(t testing.TB, object interface{}, length int, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Len(t, object, length, msgAndArgs...)
}

// AssertType asserts that an object is of the expected type.
func AssertType(t testing.TB, expectedType, object interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.IsType(t, expectedType, object, msgAndArgs...)
}

// AssertPanics asserts that a function panics.
func AssertPanics(t testing.TB, f assert.PanicTestFunc, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Panics(t, f, msgAndArgs...)
}

// AssertNotPanics asserts that a function does not panic.
func AssertNotPanics(t testing.TB, f assert.PanicTestFunc, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotPanics(t, f, msgAndArgs...)
}

// AssertWithinDuration asserts that two times are within the specified duration.
func AssertWithinDuration(t testing.TB, expected, actual time.Time, delta time.Duration, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.WithinDuration(t, expected, actual, delta, msgAndArgs...)
}

// AssertInDelta asserts that two floats are within delta of each other.
func AssertInDelta(t testing.TB, expected, actual, delta float64, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.InDelta(t, expected, actual, delta, msgAndArgs...)
}

// AssertGreater asserts that the first value is greater than the second.
func AssertGreater(t testing.TB, e1, e2 interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Greater(t, e1, e2, msgAndArgs...)
}

// AssertLess asserts that the first value is less than the second.
func AssertLess(t testing.TB, e1, e2 interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Less(t, e1, e2, msgAndArgs...)
}

// AttributeEquals checks if an attribute has the expected value.
func AttributeEquals(t testing.TB, attr attribute.KeyValue, expectedValue interface{}) bool {
	t.Helper()
	actualValue := attr.Value.AsInterface()
	return assert.Equal(t, expectedValue, actualValue, "Attribute %s value mismatch", attr.Key)
}

// AttributesContain checks if a set of attributes contains a key with expected value.
func AttributesContain(t testing.TB, attrs []attribute.KeyValue, key string, expectedValue interface{}) bool {
	t.Helper()
	for _, attr := range attrs {
		if string(attr.Key) == key {
			return AttributeEquals(t, attr, expectedValue)
		}
	}
	return assert.Fail(t, fmt.Sprintf("Attribute %s not found", key))
}

// AssertSlicesEqual asserts that two slices are equal.
func AssertSlicesEqual[T comparable](t testing.TB, expected, actual []T, msgAndArgs ...interface{}) bool {
	t.Helper()
	if len(expected) != len(actual) {
		return assert.Fail(t, fmt.Sprintf("Slice lengths differ: expected %d, got %d", len(expected), len(actual)), msgAndArgs...)
	}
	for i := range expected {
		if expected[i] != actual[i] {
			return assert.Fail(t, fmt.Sprintf("Elements differ at index %d: expected %v, got %v", i, expected[i], actual[i]), msgAndArgs...)
		}
	}
	return true
}

// AssertMapsEqual asserts that two maps are equal.
func AssertMapsEqual[K comparable, V comparable](t testing.TB, expected, actual map[K]V, msgAndArgs ...interface{}) bool {
	t.Helper()
	if len(expected) != len(actual) {
		return assert.Fail(t, fmt.Sprintf("Map lengths differ: expected %d, got %d", len(expected), len(actual)), msgAndArgs...)
	}
	for key, expectedVal := range expected {
		actualVal, ok := actual[key]
		if !ok {
			return assert.Fail(t, fmt.Sprintf("Key %v not found in actual map", key), msgAndArgs...)
		}
		if expectedVal != actualVal {
			return assert.Fail(t, fmt.Sprintf("Values differ for key %v: expected %v, got %v", key, expectedVal, actualVal), msgAndArgs...)
		}
	}
	return true
}

// AssertErrorIs asserts that an error matches the expected error using errors.Is.
func AssertErrorIs(t testing.TB, err, target error, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.ErrorIs(t, err, target, msgAndArgs...)
}

// AssertErrorAs asserts that an error can be asserted to the target type.
func AssertErrorAs(t testing.TB, err error, target interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.ErrorAs(t, err, target, msgAndArgs...)
}

// AssertImplements asserts that an object implements an interface.
func AssertImplements(t testing.TB, interfaceObject, object interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Implements(t, interfaceObject, object, msgAndArgs...)
}

// AssertElementsMatch asserts that two slices contain the same elements regardless of order.
func AssertElementsMatch(t testing.TB, listA, listB interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.ElementsMatch(t, listA, listB, msgAndArgs...)
}

// AssertSubset asserts that the second slice is a subset of the first.
func AssertSubset(t testing.TB, list, subset interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Subset(t, list, subset, msgAndArgs...)
}

// AssertNotSubset asserts that the second slice is not a subset of the first.
func AssertNotSubset(t testing.TB, list, subset interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotSubset(t, list, subset, msgAndArgs...)
}

// AssertFileExists asserts that a file exists.
func AssertFileExists(t testing.TB, path string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.FileExists(t, path, msgAndArgs...)
}

// AssertNoFileExists asserts that a file does not exist.
func AssertNoFileExists(t testing.TB, path string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NoFileExists(t, path, msgAndArgs...)
}

// AssertDirExists asserts that a directory exists.
func AssertDirExists(t testing.TB, path string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.DirExists(t, path, msgAndArgs...)
}

// AssertJSONEq asserts that two JSON strings are equal.
func AssertJSONEq(t testing.TB, expected, actual string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.JSONEq(t, expected, actual, msgAndArgs...)
}

// AssertYAMLEq asserts that two YAML strings are equal.
func AssertYAMLEq(t testing.TB, expected, actual string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.YAMLEq(t, expected, actual, msgAndArgs...)
}

// AssertRegexp asserts that a string matches a regular expression.
func AssertRegexp(t testing.TB, rx interface{}, str string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Regexp(t, rx, str, msgAndArgs...)
}

// AssertNotRegexp asserts that a string does not match a regular expression.
func AssertNotRegexp(t testing.TB, rx interface{}, str string, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotRegexp(t, rx, str, msgAndArgs...)
}

// AssertZero asserts that a value is its zero value.
func AssertZero(t testing.TB, i interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Zero(t, i, msgAndArgs...)
}

// AssertNotZero asserts that a value is not its zero value.
func AssertNotZero(t testing.TB, i interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotZero(t, i, msgAndArgs...)
}

// EventuallyEquals asserts that a value eventually equals the expected value.
func EventuallyEquals[T comparable](t testing.TB, getter func() T, expected T, timeout, interval time.Duration, msgAndArgs ...interface{}) bool {
	t.Helper()

	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if getter() == expected {
			return true
		}
		time.Sleep(interval)
	}

	return assert.Fail(t, fmt.Sprintf("Value never became %v within %v", expected, timeout), msgAndArgs...)
}

// NotNilRequire is a generic helper that requires a pointer to be non-nil and returns it.
func NotNilRequire[T any](t testing.TB, ptr *T, msgAndArgs ...interface{}) *T {
	t.Helper()
	require.NotNil(t, ptr, msgAndArgs...)
	return ptr
}

// NotEmptyRequire is a generic helper that requires a slice to be non-empty and returns it.
func NotEmptyRequire[T any](t testing.TB, slice []T, msgAndArgs ...interface{}) []T {
	t.Helper()
	require.NotEmpty(t, slice, msgAndArgs...)
	return slice
}

// LenRequire is a generic helper that requires a slice to have the expected length and returns it.
func LenRequire[T any](t testing.TB, slice []T, length int, msgAndArgs ...interface{}) []T {
	t.Helper()
	require.Len(t, slice, length, msgAndArgs...)
	return slice
}

// FailImmediately fails the test immediately with the given message.
func FailImmediately(t testing.TB, failureMessage string, msgAndArgs ...interface{}) {
	t.Helper()
	if len(msgAndArgs) > 0 {
		failureMessage = fmt.Sprintf(failureMessage, msgAndArgs...)
	}
	require.FailNow(t, failureMessage)
}

// Fail fails the test with the given message but continues execution.
func Fail(t testing.TB, failureMessage string, msgAndArgs ...interface{}) bool {
	t.Helper()
	if len(msgAndArgs) > 0 {
		failureMessage = fmt.Sprintf(failureMessage, msgAndArgs...)
	}
	return assert.Fail(t, failureMessage)
}

// Reflection helpers

// AssertSame asserts that two pointers refer to the same object.
func AssertSame(t testing.TB, expected, actual interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.Same(t, expected, actual, msgAndArgs...)
}

// AssertNotSame asserts that two pointers do not refer to the same object.
func AssertNotSame(t testing.TB, expected, actual interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.NotSame(t, expected, actual, msgAndArgs...)
}

// AssertEqualValues asserts that two objects are equal or convertable to equal.
func AssertEqualValues(t testing.TB, expected, actual interface{}, msgAndArgs ...interface{}) bool {
	t.Helper()
	return assert.EqualValues(t, expected, actual, msgAndArgs...)
}

// AssertExactly asserts that two values are exactly equal using == operator.
func AssertExactly[T comparable](t testing.TB, expected, actual T, msgAndArgs ...interface{}) bool {
	t.Helper()
	if expected != actual {
		return assert.Fail(t, fmt.Sprintf("Expected exactly %v, got %v", expected, actual), msgAndArgs...)
	}
	return true
}

// TypeOf returns the reflect.Type of an interface{}.
func TypeOf(i interface{}) reflect.Type {
	return reflect.TypeOf(i)
}

// ValueOf returns the reflect.Value of an interface{}.
func ValueOf(i interface{}) reflect.Value {
	return reflect.ValueOf(i)
}

// IsNil checks if an interface{} value is nil (handles typed nils).
func IsNil(i interface{}) bool {
	if i == nil {
		return true
	}
	return reflect.ValueOf(i).IsNil()
}

// IsZero checks if a value is its zero value.
func IsZero(i interface{}) bool {
	return reflect.ValueOf(i).IsZero()
}

// DeepEqual checks if two values are deeply equal using reflect.DeepEqual.
func DeepEqual(a, b interface{}) bool {
	return reflect.DeepEqual(a, b)
}

// StrContains is a helper for checking string containment without importing strings.
func StrContains(s, substr string) bool {
	return strings.Contains(s, substr)
}

// StrHasPrefix checks if a string has a prefix.
func StrHasPrefix(s, prefix string) bool {
	return strings.HasPrefix(s, prefix)
}

// StrHasSuffix checks if a string has a suffix.
func StrHasSuffix(s, suffix string) bool {
	return strings.HasSuffix(s, suffix)
}

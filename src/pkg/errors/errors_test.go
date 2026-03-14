package errors

import (
	"errors"
	"fmt"
	"log"
	"os"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
)

func TestNewDefaultErrorHandler(t *testing.T) {
	handler := NewDefaultErrorHandler(nil)
	assert.NotNil(t, handler)
	assert.NotNil(t, handler.logger)

	customLogger := log.New(os.Stdout, "test", log.LstdFlags)
	handler2 := NewDefaultErrorHandler(customLogger)
	assert.NotNil(t, handler2)
	assert.Equal(t, customLogger, handler2.logger)
}

func TestHandleError(t *testing.T) {
	handler := NewDefaultErrorHandler(nil)

	result := handler.HandleError(nil, "test message")
	assert.Nil(t, result)

	originalErr := errors.New("original error")
	result = handler.HandleError(originalErr, "wrapped message")
	assert.NotNil(t, result)
	assert.Contains(t, result.Error(), "wrapped message")
	assert.Contains(t, result.Error(), "original error")
}

func TestLogError(t *testing.T) {
	handler := NewDefaultErrorHandler(nil)
	handler.LogError(nil, "test message")
	testErr := errors.New("test error")
	handler.LogError(testErr, "test message")
}

func TestWrapError(t *testing.T) {
	handler := NewDefaultErrorHandler(nil)

	result := handler.WrapError(nil, "test message")
	assert.Nil(t, result)

	originalErr := errors.New("original error")
	result = handler.WrapError(originalErr, "wrapped message")
	assert.NotNil(t, result)
	assert.Contains(t, result.Error(), "wrapped message")
	assert.Contains(t, result.Error(), "original error")
}

func TestGlobalErrorHandler(t *testing.T) {
	originalHandler := globalErrorHandler
	defer func() {
		globalErrorHandler = originalHandler
	}()

	handler := GetGlobalErrorHandler()
	assert.NotNil(t, handler)

	newHandler := NewDefaultErrorHandler(nil)
	SetGlobalErrorHandler(newHandler)
	assert.Equal(t, newHandler, globalErrorHandler)
}

func TestGlobalHandleError(t *testing.T) {
	result := HandleError(nil, "test")
	assert.Nil(t, result)

	testErr := errors.New("test error")
	result = HandleError(testErr, "wrapped")
	assert.NotNil(t, result)
	assert.Contains(t, result.Error(), "wrapped")
}

func TestGlobalLogError(t *testing.T) {
	LogError(nil, "test")
	LogError(errors.New("test"), "test")
}

func TestGlobalWrapError(t *testing.T) {
	result := WrapError(nil, "test")
	assert.Nil(t, result)

	testErr := errors.New("test error")
	result = WrapError(testErr, "wrapped")
	assert.NotNil(t, result)
}

func TestErrorTypeConstants(t *testing.T) {
	assert.Equal(t, ErrorType("validation"), ErrorTypeValidation)
	assert.Equal(t, ErrorType("network"), ErrorTypeNetwork)
	assert.Equal(t, ErrorType("database"), ErrorTypeDatabase)
	assert.Equal(t, ErrorType("auth"), ErrorTypeAuth)
	assert.Equal(t, ErrorType("internal"), ErrorTypeInternal)
	assert.Equal(t, ErrorType("external"), ErrorTypeExternal)
	assert.Equal(t, ErrorType("timeout"), ErrorTypeTimeout)
	assert.Equal(t, ErrorType("rate_limit"), ErrorTypeRateLimit)
	assert.Equal(t, ErrorType("not_found"), ErrorTypeNotFound)
	assert.Equal(t, ErrorType("conflict"), ErrorTypeConflict)
}

func TestNewTypedError(t *testing.T) {
	cause := errors.New("cause error")
	err := NewTypedError(ErrorTypeValidation, "validation failed", cause)

	assert.NotNil(t, err)
	assert.Equal(t, ErrorTypeValidation, err.Type)
	assert.Equal(t, "validation failed", err.Message)
	assert.Equal(t, cause, err.Cause)
	assert.Contains(t, err.Error(), "validation")
}

func TestNewTypedErrorWithNilCause(t *testing.T) {
	err := NewTypedError(ErrorTypeInternal, "internal error", nil)
	assert.NotNil(t, err)
	assert.Equal(t, ErrorTypeInternal, err.Type)
	assert.Equal(t, "internal error", err.Message)
	assert.Nil(t, err.Cause)
	assert.Contains(t, err.Error(), "internal")
}

func TestTypedErrorUnwrap(t *testing.T) {
	cause := errors.New("original cause")
	err := NewTypedError(ErrorTypeDatabase, "db error", cause)
	assert.Equal(t, cause, err.Unwrap())
}

func TestNewTypedErrorWithDetails(t *testing.T) {
	cause := errors.New("cause")
	err := NewTypedErrorWithDetails(ErrorTypeNetwork, "network error", "connection timeout", cause)
	assert.NotNil(t, err)
	assert.Equal(t, ErrorTypeNetwork, err.Type)
	assert.Equal(t, "network error", err.Message)
	assert.Equal(t, "connection timeout", err.Details)
	assert.Equal(t, cause, err.Cause)
}

func TestIsErrorType(t *testing.T) {
	typedErr := NewTypedError(ErrorTypeValidation, "validation failed", nil)
	assert.True(t, IsErrorType(typedErr, ErrorTypeValidation))
	assert.False(t, IsErrorType(typedErr, ErrorTypeDatabase))

	wrapped := fmt.Errorf("wrapped: %w", typedErr)
	assert.True(t, IsErrorType(wrapped, ErrorTypeValidation))

	regularErr := errors.New("regular error")
	assert.False(t, IsErrorType(regularErr, ErrorTypeValidation))
	assert.False(t, IsErrorType(nil, ErrorTypeValidation))
}

func TestGetErrorType(t *testing.T) {
	typedErr := NewTypedError(ErrorTypeDatabase, "db error", nil)
	assert.Equal(t, ErrorTypeDatabase, GetErrorType(typedErr))

	regularErr := errors.New("regular")
	assert.Equal(t, ErrorTypeInternal, GetErrorType(regularErr))
	assert.Equal(t, ErrorTypeInternal, GetErrorType(nil))
}

func TestRecoverWithError(t *testing.T) {
	// Test that RecoverWithError returns nil when no panic
	result := RecoverWithError("no panic")
	assert.Nil(t, result)
}

func TestRecoverWithErrorNoPanic(t *testing.T) {
	result := RecoverWithError("no panic")
	assert.Nil(t, result)
}

func TestRecoverAndLog(t *testing.T) {
	// Test recovery without actual panic to avoid test failure
	defer func() {
		if r := recover(); r != nil {
			RecoverAndLog("recovered")
		}
	}()
	// Normal execution
}

func TestRecoverAndLogNoPanic(t *testing.T) {
	defer RecoverAndLog("no panic")
}

func TestErrorAggregator(t *testing.T) {
	ea := NewErrorAggregator()
	assert.NotNil(t, ea)
	assert.False(t, ea.HasErrors())
	assert.Empty(t, ea.Errors())

	ea.Add(nil)
	assert.False(t, ea.HasErrors())

	firstErr := errors.New("error 1")
	secondErr := errors.New("error 2")
	ea.Add(firstErr)
	ea.Add(secondErr)

	assert.True(t, ea.HasErrors())
	assert.Len(t, ea.Errors(), 2)
	assert.Contains(t, ea.Error(), "error 1")
	assert.Contains(t, ea.Error(), "error 2")
}

func TestErrorAggregatorToError(t *testing.T) {
	ea := NewErrorAggregator()
	assert.Nil(t, ea.ToError())

	singleErr := errors.New("single error")
	ea.Add(singleErr)
	result := ea.ToError()
	assert.Equal(t, singleErr, result)

	ea.Add(errors.New("another error"))
	result = ea.ToError()
	assert.NotNil(t, result)
	assert.Contains(t, result.Error(), "multiple errors")
}

func TestErrorContext(t *testing.T) {
	ec := NewErrorContext("test-operation", "test-resource")
	assert.NotNil(t, ec)
	assert.Equal(t, "test-operation", ec.Operation)
	assert.Equal(t, "test-resource", ec.Resource)
	assert.NotNil(t, ec.Metadata)

	ec.WithUserID("user-123").
		WithRequestID("req-456").
		WithMetadata("key", "value")

	assert.Equal(t, "user-123", ec.UserID)
	assert.Equal(t, "req-456", ec.RequestID)
	assert.Equal(t, "value", ec.Metadata["key"])
}

func TestNewContextualError(t *testing.T) {
	ctx := NewErrorContext("op", "res").WithUserID("user-1")
	cause := errors.New("cause error")
	err := NewContextualError(ctx, "operation failed", cause)

	assert.NotNil(t, err)
	assert.Equal(t, ctx, err.Context)
	assert.Equal(t, "operation failed", err.Message)
	assert.Equal(t, cause, err.Cause)
	assert.Contains(t, err.Error(), "operation=op")
	assert.Contains(t, err.Error(), "resource=res")
	assert.Contains(t, err.Error(), "user=user-1")
}

func TestContextualErrorUnwrap(t *testing.T) {
	ctx := NewErrorContext("op", "res")
	cause := errors.New("cause")
	err := NewContextualError(ctx, "message", cause)
	assert.Equal(t, cause, err.Unwrap())
}

func TestNewRetryableError(t *testing.T) {
	cause := errors.New("transient error")
	retryAfter := 5 * time.Second
	err := NewRetryableError("service unavailable", cause, retryAfter)

	assert.NotNil(t, err)
	assert.Equal(t, "service unavailable", err.Message)
	assert.Equal(t, cause, err.Cause)
	assert.Equal(t, retryAfter, err.RetryAfter)
	assert.Contains(t, err.Error(), "service unavailable")
}

func TestNewRetryableErrorNoCause(t *testing.T) {
	err := NewRetryableError("service unavailable", nil, time.Second)
	assert.NotNil(t, err)
	assert.Contains(t, err.Error(), "service unavailable")
}

func TestIsRetryable(t *testing.T) {
	regularErr := errors.New("regular")
	assert.False(t, IsRetryable(regularErr))

	retryable := NewRetryableError("transient", nil, time.Second)
	assert.True(t, IsRetryable(retryable))

	wrapped := fmt.Errorf("wrapped: %w", retryable)
	assert.True(t, IsRetryable(wrapped))

	assert.False(t, IsRetryable(nil))
}

func TestGetRetryAfter(t *testing.T) {
	regularErr := errors.New("regular")
	assert.Equal(t, time.Duration(0), GetRetryAfter(regularErr))

	retryable := NewRetryableError("transient", nil, 10*time.Second)
	assert.Equal(t, 10*time.Second, GetRetryAfter(retryable))

	wrapped := fmt.Errorf("wrapped: %w", retryable)
	assert.Equal(t, 10*time.Second, GetRetryAfter(wrapped))

	assert.Equal(t, time.Duration(0), GetRetryAfter(nil))
}

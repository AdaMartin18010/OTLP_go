// Package errors provides error handling utilities for the OTLP Go SDK.
//
// This package offers:
//   - Structured error wrapping with error codes and categories
//   - Error chain traversal and inspection
//   - Stack trace capture
//   - Error retry detection
//   - Context-aware error handling
//
// Example usage:
//
//	if err != nil {
//	    return errors.Wrap(err, "failed to create exporter").
//	        WithCode(errors.CodeInternal).
//	        WithRetryable(true)
//	}
package errors

import (
	"context"
	"errors"
	"fmt"
	"runtime"
	"strings"
	"sync"
	"time"
)

// ErrorCode represents a structured error code for categorization.
type ErrorCode int

const (
	// CodeUnknown indicates an unknown or unspecified error.
	CodeUnknown ErrorCode = iota
	// CodeInvalidArgument indicates a client specified an invalid argument.
	CodeInvalidArgument
	// CodeDeadlineExceeded indicates the deadline expired before operation completed.
	CodeDeadlineExceeded
	// CodeNotFound indicates requested entity was not found.
	CodeNotFound
	// CodeAlreadyExists indicates entity already exists.
	CodeAlreadyExists
	// CodePermissionDenied indicates caller does not have permission.
	CodePermissionDenied
	// CodeResourceExhausted indicates resource has been exhausted.
	CodeResourceExhausted
	// CodeFailedPrecondition indicates operation was rejected.
	CodeFailedPrecondition
	// CodeAborted indicates operation was aborted.
	CodeAborted
	// CodeOutOfRange indicates operation attempted past valid range.
	CodeOutOfRange
	// CodeUnimplemented indicates operation is not implemented.
	CodeUnimplemented
	// CodeInternal indicates internal error.
	CodeInternal
	// CodeUnavailable indicates service is currently unavailable.
	CodeUnavailable
	// CodeDataLoss indicates unrecoverable data loss or corruption.
	CodeDataLoss
	// CodeUnauthenticated indicates request does not have valid authentication.
	CodeUnauthenticated
)

// String returns the string representation of the error code.
func (c ErrorCode) String() string {
	switch c {
	case CodeInvalidArgument:
		return "INVALID_ARGUMENT"
	case CodeDeadlineExceeded:
		return "DEADLINE_EXCEEDED"
	case CodeNotFound:
		return "NOT_FOUND"
	case CodeAlreadyExists:
		return "ALREADY_EXISTS"
	case CodePermissionDenied:
		return "PERMISSION_DENIED"
	case CodeResourceExhausted:
		return "RESOURCE_EXHAUSTED"
	case CodeFailedPrecondition:
		return "FAILED_PRECONDITION"
	case CodeAborted:
		return "ABORTED"
	case CodeOutOfRange:
		return "OUT_OF_RANGE"
	case CodeUnimplemented:
		return "UNIMPLEMENTED"
	case CodeInternal:
		return "INTERNAL"
	case CodeUnavailable:
		return "UNAVAILABLE"
	case CodeDataLoss:
		return "DATA_LOSS"
	case CodeUnauthenticated:
		return "UNAUTHENTICATED"
	default:
		return "UNKNOWN"
	}
}

// ErrorCategory represents the category of an error for grouping purposes.
type ErrorCategory int

const (
	// CategoryUnknown indicates an unknown category.
	CategoryUnknown ErrorCategory = iota
	// CategoryNetwork indicates a network-related error.
	CategoryNetwork
	// CategoryConfig indicates a configuration error.
	CategoryConfig
	// CategoryValidation indicates a validation error.
	CategoryValidation
	// CategorySystem indicates a system-level error.
	CategorySystem
	// CategoryExternal indicates an external service error.
	CategoryExternal
	// CategoryTimeout indicates a timeout error.
	CategoryTimeout
)

// String returns the string representation of the error category.
func (c ErrorCategory) String() string {
	switch c {
	case CategoryNetwork:
		return "NETWORK"
	case CategoryConfig:
		return "CONFIG"
	case CategoryValidation:
		return "VALIDATION"
	case CategorySystem:
		return "SYSTEM"
	case CategoryExternal:
		return "EXTERNAL"
	case CategoryTimeout:
		return "TIMEOUT"
	default:
		return "UNKNOWN"
	}
}

// StackFrame represents a single frame in a stack trace.
type StackFrame struct {
	Function string
	File     string
	Line     int
}

// String returns a formatted string representation of the stack frame.
func (f StackFrame) String() string {
	return fmt.Sprintf("%s\n\t%s:%d", f.Function, f.File, f.Line)
}

// StackTrace represents a collection of stack frames.
type StackTrace []StackFrame

// String returns a formatted string representation of the stack trace.
func (st StackTrace) String() string {
	var sb strings.Builder
	for i, frame := range st {
		if i > 0 {
			sb.WriteString("\n")
		}
		sb.WriteString(frame.String())
	}
	return sb.String()
}

// captureStackTrace captures the current stack trace.
func captureStackTrace(skip int) StackTrace {
	var frames []StackFrame
	for i := skip; ; i++ {
		pc, file, line, ok := runtime.Caller(i)
		if !ok {
			break
		}
		fn := runtime.FuncForPC(pc)
		var fnName string
		if fn != nil {
			fnName = fn.Name()
		}
		frames = append(frames, StackFrame{
			Function: fnName,
			File:     file,
			Line:     line,
		})
		if len(frames) >= 32 { // Limit stack trace depth
			break
		}
	}
	return frames
}

// OTLPError is the structured error type for the OTLP SDK.
type OTLPError struct {
	msg        string
	cause      error
	code       ErrorCode
	category   ErrorCategory
	retryable  bool
	timestamp  time.Time
	stackTrace StackTrace
	metadata   map[string]interface{}
	mu         sync.RWMutex
}

// Error implements the error interface.
func (e *OTLPError) Error() string {
	if e.cause != nil {
		return fmt.Sprintf("[%s:%s] %s: %v", e.code, e.category, e.msg, e.cause)
	}
	return fmt.Sprintf("[%s:%s] %s", e.code, e.category, e.msg)
}

// Unwrap returns the underlying error for error chain traversal.
func (e *OTLPError) Unwrap() error {
	return e.cause
}

// WithCode sets the error code.
func (e *OTLPError) WithCode(code ErrorCode) *OTLPError {
	e.code = code
	return e
}

// WithCategory sets the error category.
func (e *OTLPError) WithCategory(category ErrorCategory) *OTLPError {
	e.category = category
	return e
}

// WithRetryable marks the error as retryable or not.
func (e *OTLPError) WithRetryable(retryable bool) *OTLPError {
	e.retryable = retryable
	return e
}

// WithMetadata adds metadata to the error.
func (e *OTLPError) WithMetadata(key string, value interface{}) *OTLPError {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.metadata == nil {
		e.metadata = make(map[string]interface{})
	}
	e.metadata[key] = value
	return e
}

// Code returns the error code.
func (e *OTLPError) Code() ErrorCode {
	return e.code
}

// Category returns the error category.
func (e *OTLPError) Category() ErrorCategory {
	return e.category
}

// IsRetryable returns whether the error is retryable.
func (e *OTLPError) IsRetryable() bool {
	return e.retryable
}

// Timestamp returns when the error occurred.
func (e *OTLPError) Timestamp() time.Time {
	return e.timestamp
}

// StackTrace returns the captured stack trace.
func (e *OTLPError) StackTrace() StackTrace {
	return e.stackTrace
}

// Metadata returns a copy of the metadata map.
func (e *OTLPError) Metadata() map[string]interface{} {
	e.mu.RLock()
	defer e.mu.RUnlock()
	if e.metadata == nil {
		return nil
	}
	result := make(map[string]interface{}, len(e.metadata))
	for k, v := range e.metadata {
		result[k] = v
	}
	return result
}

// MetadataValue returns a specific metadata value.
func (e *OTLPError) MetadataValue(key string) (interface{}, bool) {
	e.mu.RLock()
	defer e.mu.RUnlock()
	if e.metadata == nil {
		return nil, false
	}
	val, ok := e.metadata[key]
	return val, ok
}

// Format implements fmt.Formatter for detailed error output.
func (e *OTLPError) Format(s fmt.State, verb rune) {
	switch verb {
	case 'v':
		if s.Flag('+') {
			fmt.Fprintf(s, "Error: %s\n", e.Error())
			fmt.Fprintf(s, "Code: %s\n", e.code)
			fmt.Fprintf(s, "Category: %s\n", e.category)
			fmt.Fprintf(s, "Retryable: %v\n", e.retryable)
			fmt.Fprintf(s, "Timestamp: %s\n", e.timestamp.Format(time.RFC3339))
			if len(e.stackTrace) > 0 {
				fmt.Fprintf(s, "Stack Trace:\n%s\n", e.stackTrace.String())
			}
			if e.metadata != nil && len(e.metadata) > 0 {
				fmt.Fprintf(s, "Metadata: %v\n", e.metadata)
			}
		} else {
			fmt.Fprint(s, e.Error())
		}
	case 's':
		fmt.Fprint(s, e.Error())
	case 'q':
		fmt.Fprintf(s, "%q", e.Error())
	}
}

// New creates a new OTLPError with the given message.
func New(msg string) *OTLPError {
	return &OTLPError{
		msg:        msg,
		code:       CodeUnknown,
		category:   CategoryUnknown,
		timestamp:  time.Now(),
		stackTrace: captureStackTrace(2),
	}
}

// Newf creates a new OTLPError with a formatted message.
func Newf(format string, args ...interface{}) *OTLPError {
	return New(fmt.Sprintf(format, args...))
}

// Wrap wraps an existing error with additional context.
func Wrap(err error, msg string) *OTLPError {
	if err == nil {
		return nil
	}
	return &OTLPError{
		msg:        msg,
		cause:      err,
		code:       CodeUnknown,
		category:   CategoryUnknown,
		timestamp:  time.Now(),
		stackTrace: captureStackTrace(2),
	}
}

// Wrapf wraps an existing error with a formatted message.
func Wrapf(err error, format string, args ...interface{}) *OTLPError {
	return Wrap(err, fmt.Sprintf(format, args...))
}
// Is reports whether any error in err's chain matches target.
func Is(err, target error) bool {
	return errors.Is(err, target)
}

// As finds the first error in err's chain that matches target, and if so, sets
// target to that error value and returns true. Otherwise, it returns false.
func As(err error, target interface{}) bool {
	return errors.As(err, target)
}

// Unwrap returns the result of calling the Unwrap method on err, if err's
// type contains an Unwrap method returning error. Otherwise, Unwrap returns nil.
func Unwrap(err error) error {
	return errors.Unwrap(err)
}

// Cause returns the root cause of an error chain.
func Cause(err error) error {
	for {
		cause := Unwrap(err)
		if cause == nil {
			return err
		}
		err = cause
	}
}

// GetCode extracts the error code from an error if it has one.
// Returns CodeUnknown if the error is not an OTLPError.
func GetCode(err error) ErrorCode {
	if err == nil {
		return CodeUnknown
	}
	var otlpErr *OTLPError
	if As(err, &otlpErr) {
		return otlpErr.Code()
	}
	return CodeUnknown
}

// GetCategory extracts the error category from an error if it has one.
// Returns CategoryUnknown if the error is not an OTLPError.
func GetCategory(err error) ErrorCategory {
	if err == nil {
		return CategoryUnknown
	}
	var otlpErr *OTLPError
	if As(err, &otlpErr) {
		return otlpErr.Category()
	}
	return CategoryUnknown
}

// IsRetryable checks if an error is marked as retryable.
// Defaults to false for non-OTLPError types.
func IsRetryable(err error) bool {
	if err == nil {
		return false
	}
	var otlpErr *OTLPError
	if As(err, &otlpErr) {
		return otlpErr.IsRetryable()
	}
	// Default retryable codes
	code := GetCode(err)
	switch code {
	case CodeUnavailable, CodeResourceExhausted, CodeAborted:
		return true
	default:
		return false
	}
}

// IsTimeout checks if an error is a timeout error.
func IsTimeout(err error) bool {
	if err == nil {
		return false
	}
	if GetCategory(err) == CategoryTimeout {
		return true
	}
	if GetCode(err) == CodeDeadlineExceeded {
		return true
	}
	// Check context errors
	if errors.Is(err, context.DeadlineExceeded) {
		return true
	}
	return false
}

// IsTemporary checks if an error is temporary (retryable).
func IsTemporary(err error) bool {
	return IsRetryable(err)
}

// ErrorList is a collection of errors that can be treated as a single error.
type ErrorList struct {
	errors []error
	mu     sync.RWMutex
}

// Error implements the error interface.
func (el *ErrorList) Error() string {
	el.mu.RLock()
	defer el.mu.RUnlock()
	
	if len(el.errors) == 0 {
		return "no errors"
	}
	if len(el.errors) == 1 {
		return el.errors[0].Error()
	}
	
	var sb strings.Builder
	fmt.Fprintf(&sb, "%d errors occurred:\n", len(el.errors))
	for i, err := range el.errors {
		fmt.Fprintf(&sb, "  [%d] %s\n", i+1, err.Error())
	}
	return sb.String()
}

// Add adds an error to the list.
func (el *ErrorList) Add(err error) {
	if err == nil {
		return
	}
	el.mu.Lock()
	defer el.mu.Unlock()
	el.errors = append(el.errors, err)
}

// Errors returns a copy of the error list.
func (el *ErrorList) Errors() []error {
	el.mu.RLock()
	defer el.mu.RUnlock()
	result := make([]error, len(el.errors))
	copy(result, el.errors)
	return result
}

// HasErrors returns true if the list contains any errors.
func (el *ErrorList) HasErrors() bool {
	el.mu.RLock()
	defer el.mu.RUnlock()
	return len(el.errors) > 0
}

// Len returns the number of errors in the list.
func (el *ErrorList) Len() int {
	el.mu.RLock()
	defer el.mu.RUnlock()
	return len(el.errors)
}

// NewErrorList creates a new error list.
func NewErrorList() *ErrorList {
	return &ErrorList{
		errors: make([]error, 0),
	}
}

// Combine combines multiple errors into a single error.
// Returns nil if no errors are provided.
func Combine(errs ...error) error {
	var nonNil []error
	for _, err := range errs {
		if err != nil {
			nonNil = append(nonNil, err)
		}
	}
	if len(nonNil) == 0 {
		return nil
	}
	if len(nonNil) == 1 {
		return nonNil[0]
	}
	return &ErrorList{errors: nonNil}
}

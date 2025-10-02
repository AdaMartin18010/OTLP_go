package errors

import (
	"errors"
	"fmt"
	"runtime"
)

// 标准错误类型
var (
	// ErrNotFound 资源未找到
	ErrNotFound = errors.New("not found")
	// ErrInvalidArgument 无效参数
	ErrInvalidArgument = errors.New("invalid argument")
	// ErrAlreadyExists 资源已存在
	ErrAlreadyExists = errors.New("already exists")
	// ErrPermissionDenied 权限拒绝
	ErrPermissionDenied = errors.New("permission denied")
	// ErrUnauthenticated 未认证
	ErrUnauthenticated = errors.New("unauthenticated")
	// ErrInternal 内部错误
	ErrInternal = errors.New("internal error")
	// ErrUnavailable 服务不可用
	ErrUnavailable = errors.New("unavailable")
	// ErrDeadlineExceeded 超时
	ErrDeadlineExceeded = errors.New("deadline exceeded")
	// ErrCancelled 已取消
	ErrCancelled = errors.New("cancelled")
)

// DetailedError 详细错误信息
type DetailedError struct {
	Code       string                 // 错误代码
	Message    string                 // 错误消息
	Details    map[string]interface{} // 详细信息
	Cause      error                  // 原始错误
	StackTrace string                 // 堆栈跟踪
}

// Error 实现 error 接口
func (e *DetailedError) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("%s: %s (caused by: %v)", e.Code, e.Message, e.Cause)
	}
	return fmt.Sprintf("%s: %s", e.Code, e.Message)
}

// Unwrap 支持 errors.Unwrap
func (e *DetailedError) Unwrap() error {
	return e.Cause
}

// NewDetailed 创建详细错误
func NewDetailed(code, message string, cause error) *DetailedError {
	return &DetailedError{
		Code:       code,
		Message:    message,
		Cause:      cause,
		Details:    make(map[string]interface{}),
		StackTrace: captureStackTrace(2),
	}
}

// WithDetail 添加详细信息
func (e *DetailedError) WithDetail(key string, value interface{}) *DetailedError {
	e.Details[key] = value
	return e
}

// captureStackTrace 捕获堆栈跟踪
func captureStackTrace(skip int) string {
	const maxDepth = 32
	var pcs [maxDepth]uintptr
	n := runtime.Callers(skip, pcs[:])

	frames := runtime.CallersFrames(pcs[:n])
	trace := ""

	for {
		frame, more := frames.Next()
		trace += fmt.Sprintf("%s\n\t%s:%d\n", frame.Function, frame.File, frame.Line)
		if !more {
			break
		}
	}

	return trace
}

// Is 检查错误类型
func Is(err, target error) bool {
	return errors.Is(err, target)
}

// As 转换错误类型
func As(err error, target interface{}) bool {
	return errors.As(err, target)
}

// Wrap 包装错误（添加上下文）
func Wrap(err error, message string) error {
	if err == nil {
		return nil
	}
	return fmt.Errorf("%s: %w", message, err)
}

// Wrapf 格式化包装错误
func Wrapf(err error, format string, args ...interface{}) error {
	if err == nil {
		return nil
	}
	return fmt.Errorf("%s: %w", fmt.Sprintf(format, args...), err)
}

// Join 合并多个错误
func Join(errs ...error) error {
	return errors.Join(errs...)
}

// ValidationError 验证错误
type ValidationError struct {
	Field   string
	Message string
	Value   interface{}
}

func (e *ValidationError) Error() string {
	return fmt.Sprintf("validation failed for field '%s': %s (value: %v)", e.Field, e.Message, e.Value)
}

// NewValidationError 创建验证错误
func NewValidationError(field, message string, value interface{}) *ValidationError {
	return &ValidationError{
		Field:   field,
		Message: message,
		Value:   value,
	}
}

// TimeoutError 超时错误
type TimeoutError struct {
	Operation string
	Duration  string
}

func (e *TimeoutError) Error() string {
	return fmt.Sprintf("operation '%s' timed out after %s", e.Operation, e.Duration)
}

func (e *TimeoutError) Timeout() bool {
	return true
}

// NewTimeoutError 创建超时错误
func NewTimeoutError(operation, duration string) *TimeoutError {
	return &TimeoutError{
		Operation: operation,
		Duration:  duration,
	}
}

// RetryableError 可重试错误
type RetryableError struct {
	Err        error
	Retryable  bool
	RetryAfter string
}

func (e *RetryableError) Error() string {
	if e.RetryAfter != "" {
		return fmt.Sprintf("%v (retryable: %v, retry after: %s)", e.Err, e.Retryable, e.RetryAfter)
	}
	return fmt.Sprintf("%v (retryable: %v)", e.Err, e.Retryable)
}

func (e *RetryableError) Unwrap() error {
	return e.Err
}

// NewRetryableError 创建可重试错误
func NewRetryableError(err error, retryAfter string) *RetryableError {
	return &RetryableError{
		Err:        err,
		Retryable:  true,
		RetryAfter: retryAfter,
	}
}

// IsRetryable 检查错误是否可重试
func IsRetryable(err error) bool {
	var retryErr *RetryableError
	if errors.As(err, &retryErr) {
		return retryErr.Retryable
	}
	return false
}

// MultiError 多错误聚合
type MultiError struct {
	Errors []error
}

func (e *MultiError) Error() string {
	if len(e.Errors) == 0 {
		return "no errors"
	}
	if len(e.Errors) == 1 {
		return e.Errors[0].Error()
	}
	return fmt.Sprintf("%d errors: %v", len(e.Errors), e.Errors[0])
}

func (e *MultiError) Add(err error) {
	if err != nil {
		e.Errors = append(e.Errors, err)
	}
}

func (e *MultiError) HasErrors() bool {
	return len(e.Errors) > 0
}

// NewMultiError 创建多错误
func NewMultiError() *MultiError {
	return &MultiError{
		Errors: make([]error, 0),
	}
}

// ErrorHandler 错误处理器接口
type ErrorHandler interface {
	Handle(error) error
}

// ErrorHandlerFunc 错误处理函数类型
type ErrorHandlerFunc func(error) error

// Handle 实现 ErrorHandler 接口
func (f ErrorHandlerFunc) Handle(err error) error {
	return f(err)
}

// ChainErrorHandlers 链式错误处理器
func ChainErrorHandlers(handlers ...ErrorHandler) ErrorHandler {
	return ErrorHandlerFunc(func(err error) error {
		for _, h := range handlers {
			if err = h.Handle(err); err == nil {
				return nil
			}
		}
		return err
	})
}

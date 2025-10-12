package errors

import (
	"errors"
	"fmt"
	"log"
	"runtime"
	"strings"
	"time"
)

// ErrorHandler 错误处理器接口
type ErrorHandler interface {
	HandleError(err error, message string) error
	LogError(err error, message string)
	WrapError(err error, message string) error
}

// DefaultErrorHandler 默认错误处理器
type DefaultErrorHandler struct {
	logger *log.Logger
}

// NewDefaultErrorHandler 创建默认错误处理器
func NewDefaultErrorHandler(logger *log.Logger) *DefaultErrorHandler {
	if logger == nil {
		logger = log.Default()
	}
	return &DefaultErrorHandler{logger: logger}
}

// HandleError 处理错误
func (h *DefaultErrorHandler) HandleError(err error, message string) error {
	if err != nil {
		h.LogError(err, message)
		return fmt.Errorf("%s: %w", message, err)
	}
	return nil
}

// LogError 记录错误
func (h *DefaultErrorHandler) LogError(err error, message string) {
	if err != nil {
		// 获取调用者信息
		_, file, line, ok := runtime.Caller(2)
		if ok {
			h.logger.Printf("[ERROR] %s:%d - %s: %v", file, line, message, err)
		} else {
			h.logger.Printf("[ERROR] %s: %v", message, err)
		}
	}
}

// WrapError 包装错误
func (h *DefaultErrorHandler) WrapError(err error, message string) error {
	if err != nil {
		return fmt.Errorf("%s: %w", message, err)
	}
	return nil
}

// 全局错误处理器
var globalErrorHandler ErrorHandler = NewDefaultErrorHandler(nil)

// SetGlobalErrorHandler 设置全局错误处理器
func SetGlobalErrorHandler(handler ErrorHandler) {
	globalErrorHandler = handler
}

// GetGlobalErrorHandler 获取全局错误处理器
func GetGlobalErrorHandler() ErrorHandler {
	return globalErrorHandler
}

// 便捷函数

// HandleError 处理错误（使用全局处理器）
func HandleError(err error, message string) error {
	return globalErrorHandler.HandleError(err, message)
}

// LogError 记录错误（使用全局处理器）
func LogError(err error, message string) {
	globalErrorHandler.LogError(err, message)
}

// WrapError 包装错误（使用全局处理器）
func WrapError(err error, message string) error {
	return globalErrorHandler.WrapError(err, message)
}

// 错误分类

// ErrorType 错误类型
type ErrorType string

const (
	ErrorTypeValidation ErrorType = "validation"
	ErrorTypeNetwork    ErrorType = "network"
	ErrorTypeDatabase   ErrorType = "database"
	ErrorTypeAuth       ErrorType = "auth"
	ErrorTypeInternal   ErrorType = "internal"
	ErrorTypeExternal   ErrorType = "external"
	ErrorTypeTimeout    ErrorType = "timeout"
	ErrorTypeRateLimit  ErrorType = "rate_limit"
	ErrorTypeNotFound   ErrorType = "not_found"
	ErrorTypeConflict   ErrorType = "conflict"
)

// TypedError 带类型的错误
type TypedError struct {
	Type    ErrorType
	Message string
	Details string
	Cause   error
}

func (e *TypedError) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("[%s] %s: %v", e.Type, e.Message, e.Cause)
	}
	return fmt.Sprintf("[%s] %s", e.Type, e.Message)
}

func (e *TypedError) Unwrap() error {
	return e.Cause
}

// NewTypedError 创建带类型的错误
func NewTypedError(errorType ErrorType, message string, cause error) *TypedError {
	return &TypedError{
		Type:    errorType,
		Message: message,
		Cause:   cause,
	}
}

// NewTypedErrorWithDetails 创建带详细信息的类型错误
func NewTypedErrorWithDetails(errorType ErrorType, message, details string, cause error) *TypedError {
	return &TypedError{
		Type:    errorType,
		Message: message,
		Details: details,
		Cause:   cause,
	}
}

// 错误检查工具

// IsErrorType 检查错误是否为指定类型
func IsErrorType(err error, errorType ErrorType) bool {
	var typedErr *TypedError
	if err != nil && errors.As(err, &typedErr) {
		return typedErr.Type == errorType
	}
	return false
}

// GetErrorType 获取错误类型
func GetErrorType(err error) ErrorType {
	var typedErr *TypedError
	if err != nil && errors.As(err, &typedErr) {
		return typedErr.Type
	}
	return ErrorTypeInternal
}

// 错误恢复

// RecoverWithError 从 panic 中恢复并返回错误
func RecoverWithError(message string) error {
	if r := recover(); r != nil {
		return NewTypedError(ErrorTypeInternal, message, fmt.Errorf("panic: %v", r))
	}
	return nil
}

// RecoverAndLog 从 panic 中恢复并记录日志
func RecoverAndLog(message string) {
	if r := recover(); r != nil {
		err := NewTypedError(ErrorTypeInternal, message, fmt.Errorf("panic: %v", r))
		LogError(err, "Recovered from panic")
	}
}

// 错误聚合

// ErrorAggregator 错误聚合器
type ErrorAggregator struct {
	errors []error
}

// NewErrorAggregator 创建错误聚合器
func NewErrorAggregator() *ErrorAggregator {
	return &ErrorAggregator{
		errors: make([]error, 0),
	}
}

// Add 添加错误
func (ea *ErrorAggregator) Add(err error) {
	if err != nil {
		ea.errors = append(ea.errors, err)
	}
}

// HasErrors 检查是否有错误
func (ea *ErrorAggregator) HasErrors() bool {
	return len(ea.errors) > 0
}

// Errors 获取所有错误
func (ea *ErrorAggregator) Errors() []error {
	return ea.errors
}

// Error 返回聚合错误的字符串表示
func (ea *ErrorAggregator) Error() string {
	if len(ea.errors) == 0 {
		return ""
	}

	var messages []string
	for _, err := range ea.errors {
		messages = append(messages, err.Error())
	}

	return fmt.Sprintf("Multiple errors: %s", strings.Join(messages, "; "))
}

// ToError 转换为单个错误
func (ea *ErrorAggregator) ToError() error {
	if len(ea.errors) == 0 {
		return nil
	}
	if len(ea.errors) == 1 {
		return ea.errors[0]
	}
	return fmt.Errorf("multiple errors: %s", ea.Error())
}

// 错误上下文

// ErrorContext 错误上下文
type ErrorContext struct {
	Operation string
	Resource  string
	UserID    string
	RequestID string
	Metadata  map[string]interface{}
}

// NewErrorContext 创建错误上下文
func NewErrorContext(operation, resource string) *ErrorContext {
	return &ErrorContext{
		Operation: operation,
		Resource:  resource,
		Metadata:  make(map[string]interface{}),
	}
}

// WithUserID 设置用户ID
func (ec *ErrorContext) WithUserID(userID string) *ErrorContext {
	ec.UserID = userID
	return ec
}

// WithRequestID 设置请求ID
func (ec *ErrorContext) WithRequestID(requestID string) *ErrorContext {
	ec.RequestID = requestID
	return ec
}

// WithMetadata 设置元数据
func (ec *ErrorContext) WithMetadata(key string, value interface{}) *ErrorContext {
	ec.Metadata[key] = value
	return ec
}

// ContextualError 带上下文的错误
type ContextualError struct {
	Context *ErrorContext
	Message string
	Cause   error
}

func (e *ContextualError) Error() string {
	var parts []string

	if e.Context.Operation != "" {
		parts = append(parts, fmt.Sprintf("operation=%s", e.Context.Operation))
	}
	if e.Context.Resource != "" {
		parts = append(parts, fmt.Sprintf("resource=%s", e.Context.Resource))
	}
	if e.Context.UserID != "" {
		parts = append(parts, fmt.Sprintf("user=%s", e.Context.UserID))
	}
	if e.Context.RequestID != "" {
		parts = append(parts, fmt.Sprintf("request=%s", e.Context.RequestID))
	}

	contextStr := strings.Join(parts, ", ")
	if contextStr != "" {
		contextStr = "[" + contextStr + "] "
	}

	if e.Cause != nil {
		return fmt.Sprintf("%s%s: %v", contextStr, e.Message, e.Cause)
	}
	return contextStr + e.Message
}

func (e *ContextualError) Unwrap() error {
	return e.Cause
}

// NewContextualError 创建带上下文的错误
func NewContextualError(context *ErrorContext, message string, cause error) *ContextualError {
	return &ContextualError{
		Context: context,
		Message: message,
		Cause:   cause,
	}
}

// 错误重试

// RetryableError 可重试错误
type RetryableError struct {
	Message    string
	Cause      error
	RetryAfter time.Duration
}

func (e *RetryableError) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("%s (retry after %v): %v", e.Message, e.RetryAfter, e.Cause)
	}
	return fmt.Sprintf("%s (retry after %v)", e.Message, e.RetryAfter)
}

func (e *RetryableError) Unwrap() error {
	return e.Cause
}

// NewRetryableError 创建可重试错误
func NewRetryableError(message string, cause error, retryAfter time.Duration) *RetryableError {
	return &RetryableError{
		Message:    message,
		Cause:      cause,
		RetryAfter: retryAfter,
	}
}

// IsRetryable 检查错误是否可重试
func IsRetryable(err error) bool {
	var retryableErr *RetryableError
	return err != nil && errors.As(err, &retryableErr)
}

// GetRetryAfter 获取重试间隔
func GetRetryAfter(err error) time.Duration {
	var retryableErr *RetryableError
	if err != nil && errors.As(err, &retryableErr) {
		return retryableErr.RetryAfter
	}
	return 0
}

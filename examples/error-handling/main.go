package main

import (
	"context"
	"errors"
	"fmt"
	"log"
	"math/rand"
	"strings"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	"go.opentelemetry.io/otel/trace"
)

// ============================
// 1. 自定义错误类型
// ============================

// ErrorCategory 错误分类
type ErrorCategory string

const (
	ErrCategoryNetwork    ErrorCategory = "network"
	ErrCategoryDatabase   ErrorCategory = "database"
	ErrCategoryBusiness   ErrorCategory = "business"
	ErrCategoryValidation ErrorCategory = "validation"
)

// TracedError 可追踪的错误
type TracedError struct {
	Category   ErrorCategory
	Operation  string
	Message    string
	Underlying error
	StackTrace string
	Timestamp  time.Time
}

func (e *TracedError) Error() string {
	if e.Underlying != nil {
		return fmt.Sprintf("[%s] %s: %s (caused by: %v)", e.Category, e.Operation, e.Message, e.Underlying)
	}
	return fmt.Sprintf("[%s] %s: %s", e.Category, e.Operation, e.Message)
}

func (e *TracedError) Unwrap() error {
	return e.Underlying
}

// NewTracedError 创建可追踪错误
func NewTracedError(category ErrorCategory, operation, message string, underlying error) *TracedError {
	return &TracedError{
		Category:   category,
		Operation:  operation,
		Message:    message,
		Underlying: underlying,
		Timestamp:  time.Now(),
	}
}

// RecordToSpan 将错误记录到 Span
func (e *TracedError) RecordToSpan(span trace.Span) {
	span.RecordError(e)
	span.SetStatus(codes.Error, e.Message)
	span.SetAttributes(
		attribute.String("error.category", string(e.Category)),
		attribute.String("error.operation", e.Operation),
		attribute.String("error.message", e.Message),
		attribute.String("error.timestamp", e.Timestamp.Format(time.RFC3339)),
	)
	if e.Underlying != nil {
		span.SetAttributes(attribute.String("error.underlying", e.Underlying.Error()))
	}
}

// ============================
// 2. errors.Join 多错误收集
// ============================

// MultiOperationError 多操作错误收集器
type MultiOperationError struct {
	errors []error
}

func (m *MultiOperationError) Add(err error) {
	if err != nil {
		m.errors = append(m.errors, err)
	}
}

func (m *MultiOperationError) Join() error {
	if len(m.errors) == 0 {
		return nil
	}
	return errors.Join(m.errors...)
}

func (m *MultiOperationError) Count() int {
	return len(m.errors)
}

// demonstrateErrorsJoin 演示 errors.Join 用法
func demonstrateErrorsJoin(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-errors-join")
	defer span.End()

	log.Println("\n--- errors.Join Demo ---")

	// 模拟批量操作
	collector := &MultiOperationError{}

	operations := []struct {
		name       string
		shouldFail bool
	}{
		{"validate-input", true},
		{"check-permission", false},
		{"query-database", true},
		{"send-notification", true},
	}

	for _, op := range operations {
		_, opSpan := tracer.Start(ctx, op.name)

		if op.shouldFail {
			err := NewTracedError(ErrCategoryBusiness, op.name, fmt.Sprintf("%s failed", op.name), nil)
			err.RecordToSpan(opSpan)
			collector.Add(err)
		}

		opSpan.End()
	}

	// 合并所有错误
	if joinedErr := collector.Join(); joinedErr != nil {
		span.RecordError(joinedErr)
		span.SetAttributes(attribute.Int("error.total_count", collector.Count()))
		log.Printf("❌ %d operations failed:\n%v\n", collector.Count(), joinedErr)
	} else {
		span.AddEvent("All operations succeeded")
		log.Println("✅ All operations succeeded")
	}
}

// ============================
// 3. 错误链分析
// ============================

// demonstrateErrorChain 演示错误链分析
func demonstrateErrorChain(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-error-chain")
	defer span.End()

	log.Println("\n--- Error Chain Analysis Demo ---")

	// 构建错误链
	baseErr := errors.New("connection refused")
	dbErr := NewTracedError(ErrCategoryDatabase, "connect", "failed to connect to database", baseErr)
	serviceErr := NewTracedError(ErrCategoryNetwork, "initialize", "service initialization failed", dbErr)

	// 记录到 Span
	serviceErr.RecordToSpan(span)

	// 分析错误链
	log.Println("📋 Error chain analysis:")
	log.Printf("  Top error: %v", serviceErr)

	// 展开错误链
	depth := 0
	currentErr := error(serviceErr)
	for currentErr != nil {
		log.Printf("  [Depth %d] %v", depth, currentErr)

		// 检查是否是 TracedError
		var tracedErr *TracedError
		if errors.As(currentErr, &tracedErr) {
			span.AddEvent(fmt.Sprintf("Error at depth %d", depth),
				trace.WithAttributes(
					attribute.String("error.category", string(tracedErr.Category)),
					attribute.String("error.operation", tracedErr.Operation),
				),
			)
		}

		currentErr = errors.Unwrap(currentErr)
		depth++
	}

	log.Printf("  Total depth: %d\n", depth)
}

// ============================
// 4. 重试机制与指数退避
// ============================

// RetryConfig 重试配置
type RetryConfig struct {
	MaxAttempts  int
	InitialDelay time.Duration
	MaxDelay     time.Duration
	Multiplier   float64
}

// DefaultRetryConfig 默认重试配置
func DefaultRetryConfig() RetryConfig {
	return RetryConfig{
		MaxAttempts:  5,
		InitialDelay: 100 * time.Millisecond,
		MaxDelay:     5 * time.Second,
		Multiplier:   2.0,
	}
}

// RetryWithBackoff 带指数退避的重试
func RetryWithBackoff(ctx context.Context, tracer trace.Tracer, cfg RetryConfig, operation func() error) error {
	ctx, span := tracer.Start(ctx, "retry-with-backoff")
	defer span.End()

	span.SetAttributes(
		attribute.Int("retry.max_attempts", cfg.MaxAttempts),
		attribute.String("retry.initial_delay", cfg.InitialDelay.String()),
	)

	var lastErr error
	delay := cfg.InitialDelay

	for attempt := 1; attempt <= cfg.MaxAttempts; attempt++ {
		_, attemptSpan := tracer.Start(ctx, fmt.Sprintf("attempt-%d", attempt))
		attemptSpan.SetAttributes(attribute.Int("retry.attempt", attempt))

		// 执行操作
		err := operation()
		if err == nil {
			attemptSpan.SetStatus(codes.Ok, "Success")
			attemptSpan.End()
			span.SetAttributes(attribute.Int("retry.successful_attempt", attempt))
			log.Printf("✅ Operation succeeded on attempt %d", attempt)
			return nil
		}

		lastErr = err
		attemptSpan.RecordError(err)
		attemptSpan.SetStatus(codes.Error, err.Error())
		attemptSpan.End()

		log.Printf("⚠️  Attempt %d failed: %v", attempt, err)

		// 最后一次尝试不需要等待
		if attempt < cfg.MaxAttempts {
			// 添加随机抖动 (±25%)
			jitter := time.Duration(float64(delay) * (0.75 + rand.Float64()*0.5))
			log.Printf("⏳ Waiting %v before retry...", jitter)

			select {
			case <-time.After(jitter):
			case <-ctx.Done():
				return ctx.Err()
			}

			// 指数退避
			delay = time.Duration(float64(delay) * cfg.Multiplier)
			if delay > cfg.MaxDelay {
				delay = cfg.MaxDelay
			}
		}
	}

	span.RecordError(lastErr)
	span.SetStatus(codes.Error, "All retry attempts failed")
	return fmt.Errorf("operation failed after %d attempts: %w", cfg.MaxAttempts, lastErr)
}

// demonstrateRetry 演示重试机制
func demonstrateRetry(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-retry")
	defer span.End()

	log.Println("\n--- Retry with Exponential Backoff Demo ---")

	attemptCount := 0
	err := RetryWithBackoff(ctx, tracer, DefaultRetryConfig(), func() error {
		attemptCount++
		// 模拟前3次失败,第4次成功
		if attemptCount < 4 {
			return fmt.Errorf("temporary failure (attempt %d)", attemptCount)
		}
		return nil
	})

	if err != nil {
		log.Printf("❌ Operation failed: %v\n", err)
	} else {
		log.Println("✅ Operation succeeded after retries")
	}
}

// ============================
// 5. Panic 恢复与追踪
// ============================

// RecoverWithTrace 捕获 panic 并记录到追踪
func RecoverWithTrace(ctx context.Context, tracer trace.Tracer) {
	if r := recover(); r != nil {
		_, span := tracer.Start(ctx, "panic-recovery")
		defer span.End()

		panicErr := fmt.Errorf("panic occurred: %v", r)
		span.RecordError(panicErr)
		span.SetStatus(codes.Error, "Panic recovered")
		span.SetAttributes(
			attribute.String("panic.value", fmt.Sprint(r)),
			attribute.String("panic.recovered_at", time.Now().Format(time.RFC3339)),
		)

		log.Printf("🚨 Panic recovered: %v", r)
	}
}

// SafeOperation 安全执行操作(捕获 panic)
func SafeOperation(ctx context.Context, tracer trace.Tracer, name string, fn func() error) (err error) {
	ctx, span := tracer.Start(ctx, name)
	defer span.End()

	defer RecoverWithTrace(ctx, tracer)

	err = fn()
	if err != nil {
		span.RecordError(err)
	}
	return err
}

// demonstratePanicRecovery 演示 panic 恢复
func demonstratePanicRecovery(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-panic-recovery")
	defer span.End()

	log.Println("\n--- Panic Recovery Demo ---")

	// 正常操作
	err := SafeOperation(ctx, tracer, "normal-operation", func() error {
		log.Println("✅ Normal operation completed")
		return nil
	})
	if err != nil {
		log.Printf("Error: %v", err)
	}

	// 会触发 panic 的操作
	err = SafeOperation(ctx, tracer, "panic-operation", func() error {
		panic("something went terribly wrong!")
	})
	if err != nil {
		log.Printf("Error: %v", err)
	}

	log.Println("✅ Panic was caught and traced")
}

// ============================
// 6. 错误分类与结构化
// ============================

// ErrorClassifier 错误分类器
type ErrorClassifier struct {
	tracer trace.Tracer
}

// Classify 分类错误
func (ec *ErrorClassifier) Classify(ctx context.Context, err error) ErrorCategory {
	_, span := ec.tracer.Start(ctx, "classify-error")
	defer span.End()

	var tracedErr *TracedError
	if errors.As(err, &tracedErr) {
		span.SetAttributes(attribute.String("error.category", string(tracedErr.Category)))
		return tracedErr.Category
	}

	// 基于错误消息分类
	errMsg := err.Error()
	var category ErrorCategory
	switch {
	case containsAny(errMsg, "connection", "timeout", "network"):
		category = ErrCategoryNetwork
	case containsAny(errMsg, "database", "sql", "query"):
		category = ErrCategoryDatabase
	case containsAny(errMsg, "invalid", "validation"):
		category = ErrCategoryValidation
	default:
		category = ErrCategoryBusiness
	}

	span.SetAttributes(attribute.String("error.category", string(category)))
	return category
}

func containsAny(s string, substrs ...string) bool {
	lower := strings.ToLower(s)
	for _, substr := range substrs {
		if strings.Contains(lower, substr) {
			return true
		}
	}
	return false
}

// demonstrateErrorClassification 演示错误分类
func demonstrateErrorClassification(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-error-classification")
	defer span.End()

	log.Println("\n--- Error Classification Demo ---")

	classifier := &ErrorClassifier{tracer: tracer}

	testErrors := []error{
		errors.New("connection timeout"),
		NewTracedError(ErrCategoryDatabase, "query", "database query failed", nil),
		errors.New("invalid input format"),
		errors.New("business logic violation"),
	}

	for i, err := range testErrors {
		category := classifier.Classify(ctx, err)
		log.Printf("  [%d] Error: %v -> Category: %s", i+1, err, category)
	}
	log.Println()
}

// ============================
// Main
// ============================

func main() {
	// 初始化 TracerProvider
	exporter, err := stdouttrace.New(stdouttrace.WithPrettyPrint())
	if err != nil {
		log.Fatalf("Failed to create exporter: %v", err)
	}

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("error-handling-demo"),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
	)
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Fatalf("Failed to shutdown tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)
	tracer := tp.Tracer("error-handling")

	ctx := context.Background()

	log.Println("\n" + strings.Repeat("=", 80))
	log.Println("🚀 Error Handling with OTLP Demo")
	log.Println(strings.Repeat("=", 80))

	// 1. errors.Join
	demonstrateErrorsJoin(ctx, tracer)

	// 2. 错误链分析
	demonstrateErrorChain(ctx, tracer)

	// 3. 重试机制
	demonstrateRetry(ctx, tracer)

	// 4. Panic 恢复
	demonstratePanicRecovery(ctx, tracer)

	// 5. 错误分类
	demonstrateErrorClassification(ctx, tracer)

	log.Println(strings.Repeat("=", 80))
	log.Println("✅ All demos completed successfully")
	log.Println(strings.Repeat("=", 80))
}

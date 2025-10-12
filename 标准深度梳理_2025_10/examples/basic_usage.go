// Package examples provides comprehensive usage examples for OTLP Go project.
// This file demonstrates basic usage patterns and best practices.
package main

import (
	"context"
	"fmt"
	"log"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"

	"otlp-go-monitoring/src/pkg/config"
	otelmanager "otlp-go-monitoring/src/pkg/otel"
	"otlp-go-monitoring/src/pkg/types"
)

// BasicUsageExample demonstrates basic OpenTelemetry usage
func BasicUsageExample() {
	log.Println("=== Basic Usage Example ===")

	// 1. 初始化配置
	cfg := &config.OTLPConfig{
		Endpoint:       "http://localhost:4317",
		ServiceName:    "basic-usage-example",
		ServiceVersion: "1.0.0",
		Environment:    "development",
	}

	// 2. 验证配置
	if err := config.ValidateOTLPConfig(cfg); err != nil {
		log.Fatalf("Invalid configuration: %v", err)
	}

	// 3. 初始化OpenTelemetry
	ctx := context.Background()
	if err := otelmanager.InitializeGlobalOTel(ctx, cfg); err != nil {
		log.Fatalf("Failed to initialize OpenTelemetry: %v", err)
	}
	defer otelmanager.ShutdownGlobalOTel(ctx)

	// 4. 获取追踪器
	tracer := otelmanager.GetTracer("basic-usage-example")

	// 5. 创建追踪span
	ctx, span := tracer.Start(ctx, "basic-operation")
	defer span.End()

	// 6. 设置span属性
	span.SetAttributes(
		attribute.String("operation.type", "basic"),
		attribute.Int("operation.id", 12345),
		attribute.Bool("operation.success", true),
	)

	// 7. 执行业务逻辑
	result := performBasicOperation(ctx)

	// 8. 记录结果
	span.SetAttributes(
		attribute.String("operation.result", result),
		attribute.Int("operation.duration_ms", 100),
	)

	log.Printf("Basic operation completed: %s", result)
}

// performBasicOperation simulates a basic business operation
func performBasicOperation(ctx context.Context) string {
	// 模拟一些处理时间
	time.Sleep(100 * time.Millisecond)
	return "success"
}

// MetricsExample demonstrates metrics collection
func MetricsExample() {
	log.Println("=== Metrics Example ===")

	ctx := context.Background()

	// 获取指标器
	meter := otelmanager.GetMeter("metrics-example")

	// 创建计数器
	counter, err := meter.Int64Counter(
		"requests_total",
		metric.WithDescription("Total number of requests"),
		metric.WithUnit("1"),
	)
	if err != nil {
		log.Printf("Failed to create counter: %v", err)
		return
	}

	// 创建直方图
	histogram, err := meter.Float64Histogram(
		"request_duration_seconds",
		metric.WithDescription("Request duration in seconds"),
		metric.WithUnit("s"),
	)
	if err != nil {
		log.Printf("Failed to create histogram: %v", err)
		return
	}

	// 记录指标
	for i := 0; i < 10; i++ {
		start := time.Now()

		// 模拟请求处理
		time.Sleep(time.Duration(i*10) * time.Millisecond)

		duration := time.Since(start).Seconds()

		// 记录计数器
		counter.Add(ctx, 1, metric.WithAttributes(
			attribute.String("method", "GET"),
			attribute.String("endpoint", "/api/example"),
			attribute.Int("status_code", 200),
		))

		// 记录直方图
		histogram.Record(ctx, duration, metric.WithAttributes(
			attribute.String("method", "GET"),
			attribute.String("endpoint", "/api/example"),
		))

		log.Printf("Request %d completed in %.3f seconds", i+1, duration)
	}
}

// ErrorHandlingExample demonstrates error handling with OpenTelemetry
func ErrorHandlingExample() {
	log.Println("=== Error Handling Example ===")

	ctx := context.Background()
	tracer := otelmanager.GetTracer("error-handling-example")

	// 成功操作示例
	ctx, span := tracer.Start(ctx, "successful-operation")
	defer span.End()

	span.SetAttributes(
		attribute.String("operation.type", "successful"),
	)

	// 模拟成功操作
	time.Sleep(50 * time.Millisecond)
	span.SetStatus(codes.Ok, "Operation completed successfully")

	log.Println("Successful operation completed")

	// 错误操作示例
	ctx, errorSpan := tracer.Start(ctx, "error-operation")
	defer errorSpan.End()

	errorSpan.SetAttributes(
		attribute.String("operation.type", "error"),
	)

	// 模拟错误操作
	time.Sleep(50 * time.Millisecond)
	err := fmt.Errorf("simulated error: operation failed")
	errorSpan.RecordError(err)
	errorSpan.SetStatus(codes.Error, err.Error())

	log.Printf("Error operation failed: %v", err)
}

// ContextPropagationExample demonstrates context propagation
func ContextPropagationExample() {
	log.Println("=== Context Propagation Example ===")

	ctx := context.Background()
	tracer := otelmanager.GetTracer("context-propagation-example")

	// 创建根span
	ctx, rootSpan := tracer.Start(ctx, "root-operation")
	defer rootSpan.End()

	rootSpan.SetAttributes(
		attribute.String("operation.level", "root"),
		attribute.Int("operation.id", 1),
	)

	log.Println("Root operation started")

	// 调用子操作
	childOperation1(ctx, tracer)
	childOperation2(ctx, tracer)

	log.Println("Root operation completed")
}

// childOperation1 demonstrates child span creation
func childOperation1(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "child-operation-1")
	defer span.End()

	span.SetAttributes(
		attribute.String("operation.level", "child"),
		attribute.Int("operation.id", 2),
		attribute.String("operation.name", "child-1"),
	)

	// 模拟子操作
	time.Sleep(100 * time.Millisecond)
	log.Println("Child operation 1 completed")
}

// childOperation2 demonstrates another child span
func childOperation2(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "child-operation-2")
	defer span.End()

	span.SetAttributes(
		attribute.String("operation.level", "child"),
		attribute.Int("operation.id", 3),
		attribute.String("operation.name", "child-2"),
	)

	// 模拟子操作
	time.Sleep(150 * time.Millisecond)
	log.Println("Child operation 2 completed")
}

// CustomAttributesExample demonstrates custom attributes
func CustomAttributesExample() {
	log.Println("=== Custom Attributes Example ===")

	ctx := context.Background()
	tracer := otelmanager.GetTracer("custom-attributes-example")

	ctx, span := tracer.Start(ctx, "custom-attributes-operation")
	defer span.End()

	// 设置各种类型的属性
	span.SetAttributes(
		// 字符串属性
		attribute.String("user.id", "user-12345"),
		attribute.String("user.email", "user@example.com"),
		attribute.String("request.method", "POST"),
		attribute.String("request.path", "/api/users"),

		// 数值属性
		attribute.Int("request.size", 1024),
		attribute.Int64("user.age", 25),
		attribute.Float64("request.duration_ms", 123.45),

		// 布尔属性
		attribute.Bool("user.verified", true),
		attribute.Bool("request.cached", false),

		// 数组属性
		attribute.StringSlice("user.roles", []string{"admin", "user"}),
		attribute.Int64Slice("request.tags", []int64{1, 2, 3}),
	)

	// 模拟操作
	time.Sleep(200 * time.Millisecond)

	log.Println("Custom attributes operation completed")
}

// BusinessLogicExample demonstrates business logic with OpenTelemetry
func BusinessLogicExample() {
	log.Println("=== Business Logic Example ===")

	ctx := context.Background()
	tracer := otelmanager.GetTracer("business-logic-example")

	// 模拟用户注册流程
	ctx, span := tracer.Start(ctx, "user-registration")
	defer span.End()

	span.SetAttributes(
		attribute.String("business.operation", "user-registration"),
		attribute.String("business.domain", "user-management"),
	)

	// 1. 验证用户输入
	ctx, validationSpan := tracer.Start(ctx, "input-validation")
	userData := &types.User{
		ID:    "user-12345",
		Name:  "John Doe",
		Email: "john@example.com",
		Phone: "+1234567890",
		Level: "normal",
	}

	if err := validateUserInput(userData); err != nil {
		validationSpan.RecordError(err)
		validationSpan.SetStatus(codes.Error, "Validation failed")
		validationSpan.End()
		span.RecordError(err)
		span.SetStatus(codes.Error, "User registration failed")
		log.Printf("User validation failed: %v", err)
		return
	}

	validationSpan.SetStatus(codes.Ok, "Validation passed")
	validationSpan.End()

	// 2. 保存用户数据
	ctx, saveSpan := tracer.Start(ctx, "save-user-data")
	if err := saveUserData(ctx, userData); err != nil {
		saveSpan.RecordError(err)
		saveSpan.SetStatus(codes.Error, "Save failed")
		saveSpan.End()
		span.RecordError(err)
		span.SetStatus(codes.Error, "User registration failed")
		log.Printf("User save failed: %v", err)
		return
	}

	saveSpan.SetStatus(codes.Ok, "User saved successfully")
	saveSpan.End()

	// 3. 发送欢迎邮件
	ctx, emailSpan := tracer.Start(ctx, "send-welcome-email")
	if err := sendWelcomeEmail(ctx, userData.Email); err != nil {
		emailSpan.RecordError(err)
		emailSpan.SetStatus(codes.Error, "Email failed")
		emailSpan.End()
		// 邮件失败不影响注册流程
		log.Printf("Welcome email failed: %v", err)
	} else {
		emailSpan.SetStatus(codes.Ok, "Email sent successfully")
		emailSpan.End()
	}

	span.SetStatus(codes.Ok, "User registration completed")
	log.Printf("User registration completed for: %s", userData.Name)
}

// validateUserInput validates user input data
func validateUserInput(user *types.User) error {
	if user.Name == "" {
		return fmt.Errorf("name is required")
	}
	if user.Email == "" {
		return fmt.Errorf("email is required")
	}
	if user.Phone == "" {
		return fmt.Errorf("phone is required")
	}
	return nil
}

// saveUserData simulates saving user data
func saveUserData(ctx context.Context, user *types.User) error {
	// 模拟数据库操作
	time.Sleep(100 * time.Millisecond)

	// 模拟随机失败
	if time.Now().UnixNano()%10 == 0 {
		return fmt.Errorf("database connection failed")
	}

	return nil
}

// sendWelcomeEmail simulates sending welcome email
func sendWelcomeEmail(ctx context.Context, email string) error {
	// 模拟邮件发送
	time.Sleep(200 * time.Millisecond)

	// 模拟随机失败
	if time.Now().UnixNano()%5 == 0 {
		return fmt.Errorf("email service unavailable")
	}

	return nil
}

// PerformanceExample demonstrates performance monitoring
func PerformanceExample() {
	log.Println("=== Performance Example ===")

	ctx := context.Background()
	tracer := otelmanager.GetTracer("performance-example")

	// 性能测试函数
	testFunction := func(name string, fn func()) {
		_, span := tracer.Start(ctx, name)
		defer span.End()

		start := time.Now()
		fn()
		duration := time.Since(start)

		span.SetAttributes(
			attribute.String("performance.test", name),
			attribute.Float64("performance.duration_ms", float64(duration.Nanoseconds())/1e6),
		)

		log.Printf("Performance test '%s' completed in %v", name, duration)
	}

	// 测试各种操作
	testFunction("fast-operation", func() {
		time.Sleep(10 * time.Millisecond)
	})

	testFunction("medium-operation", func() {
		time.Sleep(100 * time.Millisecond)
	})

	testFunction("slow-operation", func() {
		time.Sleep(500 * time.Millisecond)
	})

	// 批量操作测试
	ctx, batchSpan := tracer.Start(ctx, "batch-operations")
	defer batchSpan.End()

	batchSpan.SetAttributes(
		attribute.String("performance.test", "batch"),
		attribute.Int("performance.count", 100),
	)

	start := time.Now()
	for i := 0; i < 100; i++ {
		// 模拟批量操作
		time.Sleep(1 * time.Millisecond)
	}
	duration := time.Since(start)

	batchSpan.SetAttributes(
		attribute.Float64("performance.total_duration_ms", float64(duration.Nanoseconds())/1e6),
		attribute.Float64("performance.avg_duration_ms", float64(duration.Nanoseconds())/1e6/100),
	)

	log.Printf("Batch operations completed in %v (avg: %v per operation)", duration, duration/100)
}

// main function demonstrates all examples
func main() {
	log.Println("OTLP Go Basic Usage Examples")
	log.Println("=============================")

	// 运行所有示例
	BasicUsageExample()
	MetricsExample()
	ErrorHandlingExample()
	ContextPropagationExample()
	CustomAttributesExample()
	BusinessLogicExample()
	PerformanceExample()

	log.Println("=============================")
	log.Println("All examples completed successfully!")
	log.Println("Check your OpenTelemetry Collector for traces and metrics.")
}

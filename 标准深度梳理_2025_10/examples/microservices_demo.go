// Package examples provides microservices demonstration for OTLP Go project.
// This file demonstrates microservices architecture with OpenTelemetry integration.
package main

import (
	"context"
	"fmt"
	"log"
	"net/http"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"

	"otlp-go-monitoring/src/microservices"
	"otlp-go-monitoring/src/pkg/config"
	otelmanager "otlp-go-monitoring/src/pkg/otel"
	"otlp-go-monitoring/src/pkg/types"
)

// MicroservicesDemo demonstrates microservices architecture
func MicroservicesDemo() {
	log.Println("=== Microservices Demo ===")

	// 1. 初始化OpenTelemetry
	cfg := &config.OTLPConfig{
		Endpoint:       "http://localhost:4317",
		ServiceName:    "microservices-demo",
		ServiceVersion: "1.0.0",
		Environment:    "development",
	}

	ctx := context.Background()
	if err := otelmanager.InitializeGlobalOTel(ctx, cfg); err != nil {
		log.Fatalf("Failed to initialize OpenTelemetry: %v", err)
	}
	defer otelmanager.ShutdownGlobalOTel(ctx)

	// 2. 创建微服务实例
	orderService := microservices.NewOrderService()
	paymentService := microservices.NewPaymentService()
	userService := microservices.NewUserService()

	// 3. 创建API网关
	gateway := microservices.NewAPIGateway(orderService, paymentService, userService)

	// 4. 启动服务（模拟启动）
	log.Println("Starting microservices...")
	time.Sleep(100 * time.Millisecond)

	// 5. 运行测试场景
	runTestScenarios(ctx, gateway)

	log.Println("Microservices demo completed")
}

// runTestScenarios runs various test scenarios
func runTestScenarios(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("Running test scenarios...")

	// 场景1: 用户注册
	scenario1_UserRegistration(ctx, gateway)

	// 场景2: 创建订单
	scenario2_CreateOrder(ctx, gateway)

	// 场景3: 处理支付
	scenario3_ProcessPayment(ctx, gateway)

	// 场景4: 查询订单状态
	scenario4_QueryOrderStatus(ctx, gateway)

	// 场景5: 错误处理
	scenario5_ErrorHandling(ctx, gateway)

	// 场景6: 性能测试
	scenario6_PerformanceTest(ctx, gateway)
}

// scenario1_UserRegistration demonstrates user registration flow
func scenario1_UserRegistration(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("--- Scenario 1: User Registration ---")

	tracer := otelmanager.GetTracer("scenario-user-registration")
	ctx, span := tracer.Start(ctx, "user-registration-scenario")
	defer span.End()

	// 创建用户数据
	user := &types.User{
		ID:    "user-" + generateID(),
		Name:  "Demo User",
		Email: "demo@example.com",
		Phone: "+1234567890",
		Level: "normal",
	}

	span.SetAttributes(
		attribute.String("scenario", "user-registration"),
		attribute.String("user.id", user.ID),
		attribute.String("user.email", user.Email),
	)

	// 模拟用户注册请求
	_, err := createUserRegistrationRequest(user)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "Failed to create request")
		log.Printf("Failed to create user registration request: %v", err)
		return
	}

	// 发送请求（模拟）
	log.Printf("Simulating user registration for user: %s", user.Name)
	time.Sleep(50 * time.Millisecond)

	span.SetStatus(codes.Ok, "User registration successful")
	log.Printf("User registration successful for user: %s", user.Name)
}

// scenario2_CreateOrder demonstrates order creation flow
func scenario2_CreateOrder(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("--- Scenario 2: Create Order ---")

	tracer := otelmanager.GetTracer("scenario-create-order")
	ctx, span := tracer.Start(ctx, "create-order-scenario")
	defer span.End()

	// 创建订单数据
	orderReq := &types.CreateOrderRequest{
		UserID: "user-12345",
		Items: []types.OrderItem{
			{
				ProductID: "product-001",
				Quantity:  2,
				Price:     29.99,
			},
			{
				ProductID: "product-002",
				Quantity:  1,
				Price:     19.99,
			},
		},
		TotalAmount:   79.97,
		PaymentMethod: "credit_card",
	}

	span.SetAttributes(
		attribute.String("scenario", "create-order"),
		attribute.String("user.id", orderReq.UserID),
		attribute.Int("items.count", len(orderReq.Items)),
		attribute.Float64("order.total", orderReq.TotalAmount),
	)

	// 发送创建订单请求（模拟）
	log.Printf("Simulating order creation for user: %s", orderReq.UserID)
	time.Sleep(100 * time.Millisecond)

	span.SetStatus(codes.Ok, "Order creation successful")
	log.Printf("Order creation successful for user: %s", orderReq.UserID)
}

// scenario3_ProcessPayment demonstrates payment processing flow
func scenario3_ProcessPayment(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("--- Scenario 3: Process Payment ---")

	tracer := otelmanager.GetTracer("scenario-process-payment")
	ctx, span := tracer.Start(ctx, "process-payment-scenario")
	defer span.End()

	// 创建支付数据
	paymentReq := &types.PaymentRequest{
		OrderID: "order-12345",
		Amount:  79.97,
		Method:  "credit_card",
	}

	span.SetAttributes(
		attribute.String("scenario", "process-payment"),
		attribute.String("order.id", paymentReq.OrderID),
		attribute.Float64("payment.amount", paymentReq.Amount),
		attribute.String("payment.method", paymentReq.Method),
	)

	// 发送支付请求（模拟）
	log.Printf("Simulating payment processing for order: %s", paymentReq.OrderID)
	time.Sleep(150 * time.Millisecond)

	span.SetStatus(codes.Ok, "Payment processing successful")
	log.Printf("Payment processing successful for order: %s", paymentReq.OrderID)
}

// scenario4_QueryOrderStatus demonstrates order status query
func scenario4_QueryOrderStatus(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("--- Scenario 4: Query Order Status ---")

	tracer := otelmanager.GetTracer("scenario-query-order")
	ctx, span := tracer.Start(ctx, "query-order-scenario")
	defer span.End()

	orderID := "order-12345"

	span.SetAttributes(
		attribute.String("scenario", "query-order"),
		attribute.String("order.id", orderID),
	)

	// 查询订单状态（模拟）
	log.Printf("Simulating order query for order: %s", orderID)
	time.Sleep(50 * time.Millisecond)

	span.SetAttributes(
		attribute.String("order.status", "completed"),
		attribute.String("order.user_id", "user-12345"),
		attribute.Float64("order.total", 79.97),
	)

	span.SetStatus(codes.Ok, "Order query successful")
	log.Printf("Order query successful for order: %s", orderID)
}

// scenario5_ErrorHandling demonstrates error handling
func scenario5_ErrorHandling(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("--- Scenario 5: Error Handling ---")

	tracer := otelmanager.GetTracer("scenario-error-handling")
	ctx, span := tracer.Start(ctx, "error-handling-scenario")
	defer span.End()

	span.SetAttributes(
		attribute.String("scenario", "error-handling"),
	)

	// 测试1: 无效用户ID
	log.Println("Testing invalid user ID...")
	invalidOrderReq := &types.CreateOrderRequest{
		UserID:        "invalid-user",
		Items:         []types.OrderItem{},
		TotalAmount:   0,
		PaymentMethod: "credit_card",
	}

	log.Printf("Simulating invalid order creation for user: %s", invalidOrderReq.UserID)
	time.Sleep(50 * time.Millisecond)

	// 测试2: 无效订单ID
	log.Println("Testing invalid order ID...")
	log.Printf("Simulating invalid order query for order: invalid-order")
	time.Sleep(50 * time.Millisecond)

	// 测试3: 无效支付金额
	log.Println("Testing invalid payment amount...")
	invalidPaymentReq := &types.PaymentRequest{
		OrderID: "order-12345",
		Amount:  -10.0, // 负数金额
		Method:  "credit_card",
	}

	log.Printf("Simulating invalid payment processing for order: %s", invalidPaymentReq.OrderID)
	time.Sleep(50 * time.Millisecond)

	span.SetStatus(codes.Ok, "Error handling test completed")
	log.Println("Error handling test completed")
}

// scenario6_PerformanceTest demonstrates performance testing
func scenario6_PerformanceTest(ctx context.Context, gateway *microservices.APIGateway) {
	log.Println("--- Scenario 6: Performance Test ---")

	tracer := otelmanager.GetTracer("scenario-performance-test")
	ctx, span := tracer.Start(ctx, "performance-test-scenario")
	defer span.End()

	span.SetAttributes(
		attribute.String("scenario", "performance-test"),
		attribute.Int("test.iterations", 100),
	)

	// 性能测试: 并发创建订单
	log.Println("Running concurrent order creation test...")

	start := time.Now()
	successCount := 0
	errorCount := 0

	for i := 0; i < 100; i++ {
		_ = &types.CreateOrderRequest{
			UserID: "user-" + generateID(),
			Items: []types.OrderItem{
				{
					ProductID: "product-" + generateID(),
					Quantity:  1,
					Price:     10.0,
				},
			},
			TotalAmount:   10.0,
			PaymentMethod: "credit_card",
		}

		// 模拟订单创建
		time.Sleep(1 * time.Millisecond)
		successCount++
	}

	duration := time.Since(start)

	span.SetAttributes(
		attribute.Int("test.success_count", successCount),
		attribute.Int("test.error_count", errorCount),
		attribute.Float64("test.duration_ms", float64(duration.Nanoseconds())/1e6),
		attribute.Float64("test.throughput_ops_per_sec", float64(100)/duration.Seconds()),
	)

	span.SetStatus(codes.Ok, "Performance test completed")
	log.Printf("Performance test completed:")
	log.Printf("  Duration: %v", duration)
	log.Printf("  Success: %d", successCount)
	log.Printf("  Errors: %d", errorCount)
	log.Printf("  Throughput: %.2f ops/sec", float64(100)/duration.Seconds())
}

// Helper functions

// createUserRegistrationRequest creates a user registration request
func createUserRegistrationRequest(user *types.User) (*http.Request, error) {
	// 这里应该创建实际的HTTP请求
	// 为了演示，我们返回一个模拟请求
	return &http.Request{}, nil
}

// generateID generates a random ID
func generateID() string {
	return fmt.Sprintf("%d", time.Now().UnixNano()%1000000)
}

// main function runs the microservices demo
func mainMicroservicesDemo() {
	log.Println("OTLP Go Microservices Demo")
	log.Println("===========================")

	// 运行微服务演示
	MicroservicesDemo()

	log.Println("===========================")
	log.Println("Microservices demo completed!")
	log.Println("Check your OpenTelemetry Collector for distributed traces.")
}

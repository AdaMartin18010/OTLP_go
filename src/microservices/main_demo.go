package microservices

import (
	"context"
	"fmt"
	"log"
	"os"
	"os/signal"
	"syscall"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/sdk/resource"
	"go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials/insecure"
)

// RunMicroservicesDemo 运行完整的微服务演示
func RunMicroservicesDemo() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// 初始化 OpenTelemetry
	if err := initOpenTelemetry(ctx); err != nil {
		log.Fatalf("Failed to initialize OpenTelemetry: %v", err)
	}

	// 启动各个服务（在实际场景中应该在不同的进程/容器中运行）
	go startUserService()
	go startOrderService()
	go startPaymentService()
	go startAPIGateway()

	// 等待服务启动
	time.Sleep(2 * time.Second)

	// 运行测试场景
	runTestScenarios(ctx)

	// 优雅关闭
	waitForShutdown()
}

// initOpenTelemetry 初始化 OpenTelemetry
func initOpenTelemetry(ctx context.Context) error {
	endpoint := os.Getenv("OTLP_GRPC_ENDPOINT")
	if endpoint == "" {
		endpoint = "127.0.0.1:4317"
	}

	// 创建 OTLP gRPC Exporter
	exporter, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint(endpoint),
		otlptracegrpc.WithTLSCredentials(insecure.NewCredentials()),
		otlptracegrpc.WithDialOption(grpc.WithBlock()),
	)
	if err != nil {
		return fmt.Errorf("failed to create exporter: %w", err)
	}

	// 创建 Resource
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName("microservices-demo"),
			semconv.ServiceVersion("1.0.0"),
			semconv.DeploymentEnvironment("dev"),
		),
	)
	if err != nil {
		return fmt.Errorf("failed to create resource: %w", err)
	}

	// 创建 TracerProvider
	tp := trace.NewTracerProvider(
		trace.WithBatcher(exporter,
			trace.WithMaxQueueSize(2048),
			trace.WithMaxExportBatchSize(512),
			trace.WithBatchTimeout(5*time.Second),
		),
		trace.WithResource(res),
		trace.WithSampler(trace.AlwaysSample()),
	)

	// 设置全局 TracerProvider
	otel.SetTracerProvider(tp)

	// 设置全局 Propagator（W3C Trace Context）
	otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
		propagation.TraceContext{},
		propagation.Baggage{},
	))

	log.Println("OpenTelemetry initialized successfully")
	return nil
}

// startUserService 启动用户服务
func startUserService() {
	service := NewUserService()
	log.Println("Starting User Service on :8081")
	if err := service.StartServer(":8081"); err != nil {
		log.Printf("User Service error: %v\n", err)
	}
}

// startOrderService 启动订单服务
func startOrderService() {
	service := NewOrderService()
	log.Println("Starting Order Service on :8082")
	if err := service.StartServer(":8082"); err != nil {
		log.Printf("Order Service error: %v\n", err)
	}
}

// startPaymentService 启动支付服务
func startPaymentService() {
	service := NewPaymentService()
	log.Println("Starting Payment Service on :8083")
	if err := service.StartServer(":8083"); err != nil {
		log.Printf("Payment Service error: %v\n", err)
	}
}

// startAPIGateway 启动 API 网关
func startAPIGateway() {
	gateway := NewAPIGateway(
		"http://localhost:8082", // Order Service
		"http://localhost:8083", // Payment Service
		"http://localhost:8081", // User Service
	)
	log.Println("Starting API Gateway on :8080")
	if err := gateway.StartServer(":8080"); err != nil {
		log.Printf("API Gateway error: %v\n", err)
	}
}

// runTestScenarios 运行测试场景
func runTestScenarios(ctx context.Context) {
	tracer := otel.Tracer("test-scenarios")

	log.Println("=== Running Test Scenarios ===")

	// 场景 1: 成功的订单创建流程
	func() {
		ctx, span := tracer.Start(ctx, "scenario.successful_order")
		defer span.End()

		log.Println("Scenario 1: Successful Order Creation")

		gateway := NewAPIGateway(
			"http://localhost:8082",
			"http://localhost:8083",
			"http://localhost:8081",
		)

		req := &CreateOrderRequest{
			UserID: "user-001",
			Items: []OrderItem{
				{ProductID: "prod-001", Quantity: 2, Price: 29.99},
				{ProductID: "prod-002", Quantity: 1, Price: 49.99},
			},
			TotalAmount:   109.97,
			PaymentMethod: "credit_card",
		}

		// 模拟创建订单（实际应该通过 HTTP 调用）
		order, err := gateway.orderService.CreateOrder(ctx, req)
		if err != nil {
			log.Printf("  ❌ Failed: %v\n", err)
			return
		}

		log.Printf("  ✅ Order Created: ID=%s, Total=$%.2f\n", order.ID, order.TotalAmount)

		// 处理支付
		payment, err := gateway.paymentService.ProcessPayment(ctx, &PaymentRequest{
			OrderID: order.ID,
			Amount:  order.TotalAmount,
			Method:  "credit_card",
		})
		if err != nil {
			log.Printf("  ❌ Payment Failed: %v\n", err)
			return
		}

		log.Printf("  ✅ Payment Processed: ID=%s, Status=%s\n", payment.ID, payment.Status)
	}()

	time.Sleep(1 * time.Second)

	// 场景 2: 用户验证失败
	func() {
		ctx, span := tracer.Start(ctx, "scenario.invalid_user")
		defer span.End()

		log.Println("\nScenario 2: Invalid User")

		gateway := NewAPIGateway(
			"http://localhost:8082",
			"http://localhost:8083",
			"http://localhost:8081",
		)

		// 尝试使用不存在的用户
		user, err := gateway.userService.GetUser(ctx, "user-999")
		if err != nil {
			log.Printf("  ✅ Expected Error: %v\n", err)
		} else {
			log.Printf("  ❌ Unexpected Success: %+v\n", user)
		}
	}()

	time.Sleep(1 * time.Second)

	// 场景 3: 查询用户统计信息
	func() {
		ctx, span := tracer.Start(ctx, "scenario.user_stats")
		defer span.End()

		log.Println("\nScenario 3: User Stats Query")

		client := NewUserServiceClient("http://localhost:8081")

		user, err := client.GetUser(ctx, "user-001")
		if err != nil {
			log.Printf("  ❌ Failed to get user: %v\n", err)
			return
		}

		log.Printf("  ✅ User Found: %s (%s) - Level: %s\n", user.Name, user.Email, user.Level)

		stats, err := client.GetUserStats(ctx, "user-001")
		if err != nil {
			log.Printf("  ❌ Failed to get stats: %v\n", err)
			return
		}

		log.Printf("  ✅ Stats Retrieved: Orders=%v, Spent=$%.2f, Points=%v\n",
			stats["total_orders"], stats["total_spent"], stats["loyalty_points"])
	}()

	time.Sleep(1 * time.Second)

	// 场景 4: 订单取消流程
	func() {
		ctx, span := tracer.Start(ctx, "scenario.order_cancellation")
		defer span.End()

		log.Println("\nScenario 4: Order Cancellation")

		orderClient := NewOrderServiceClient("http://localhost:8082")

		// 创建订单
		order, err := orderClient.CreateOrder(ctx, &CreateOrderRequest{
			UserID: "user-002",
			Items: []OrderItem{
				{ProductID: "prod-003", Quantity: 1, Price: 99.99},
			},
			TotalAmount:   99.99,
			PaymentMethod: "paypal",
		})
		if err != nil {
			log.Printf("  ❌ Failed to create order: %v\n", err)
			return
		}

		log.Printf("  ✅ Order Created: ID=%s\n", order.ID)

		// 取消订单
		if err := orderClient.CancelOrder(ctx, order.ID); err != nil {
			log.Printf("  ❌ Failed to cancel: %v\n", err)
			return
		}

		log.Printf("  ✅ Order Cancelled: ID=%s\n", order.ID)

		// 验证状态
		updatedOrder, err := orderClient.GetOrder(ctx, order.ID)
		if err != nil {
			log.Printf("  ❌ Failed to verify: %v\n", err)
			return
		}

		log.Printf("  ✅ Status Verified: %s\n", updatedOrder.Status)
	}()

	time.Sleep(1 * time.Second)

	// 场景 5: 并发订单处理
	func() {
		ctx, span := tracer.Start(ctx, "scenario.concurrent_orders")
		defer span.End()

		log.Println("\nScenario 5: Concurrent Order Processing")

		gateway := NewAPIGateway(
			"http://localhost:8082",
			"http://localhost:8083",
			"http://localhost:8081",
		)

		// 并发创建多个订单
		numOrders := 5
		results := make(chan string, numOrders)

		for i := 0; i < numOrders; i++ {
			go func(orderNum int) {
				ctx, span := tracer.Start(ctx, fmt.Sprintf("order.%d", orderNum))
				defer span.End()

				order, err := gateway.orderService.CreateOrder(ctx, &CreateOrderRequest{
					UserID: "user-003",
					Items: []OrderItem{
						{ProductID: fmt.Sprintf("prod-%03d", orderNum), Quantity: 1, Price: 19.99},
					},
					TotalAmount:   19.99,
					PaymentMethod: "credit_card",
				})

				if err != nil {
					results <- fmt.Sprintf("Order %d: Failed - %v", orderNum, err)
				} else {
					results <- fmt.Sprintf("Order %d: Success - ID=%s", orderNum, order.ID)
				}
			}(i)
		}

		// 收集结果
		for i := 0; i < numOrders; i++ {
			log.Printf("  ✅ %s\n", <-results)
		}
	}()

	log.Println("=== All Test Scenarios Completed ===")
}

// waitForShutdown 等待关闭信号
func waitForShutdown() {
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)

	sig := <-sigCh
	log.Printf("\nReceived signal: %v, shutting down gracefully...\n", sig)

	// 给服务一些时间完成处理
	time.Sleep(2 * time.Second)

	log.Println("Shutdown complete")
}

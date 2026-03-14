package microservices

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"os/signal"
	"syscall"
	"time"

	"go.opentelemetry.io/otel"

	"OTLP_go/pkg/config"
	otelmanager "OTLP_go/pkg/otel"
	"OTLP_go/pkg/types"
)

// RunMicroservicesDemo 运行完整的微服务演示
func RunMicroservicesDemo() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// 初始化 OpenTelemetry
	if err := initOpenTelemetry(ctx); err != nil {
		slog.Error("Failed to initialize OpenTelemetry", slog.Any("error", err))
		os.Exit(1)
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
	// 使用新的 OTel 管理器
	cfg := &config.OTLPConfig{
		Endpoint:       os.Getenv("OTLP_GRPC_ENDPOINT"),
		Insecure:       true,
		SamplingRate:   1.0, // 开发环境使用全采样
		ServiceName:    "microservices-demo",
		ServiceVersion: "1.0.0",
		Environment:    "dev",
	}

	if cfg.Endpoint == "" {
		cfg.Endpoint = "127.0.0.1:4317"
	}

	// 初始化全局 OTel 管理器
	return otelmanager.InitializeGlobalOTel(ctx, cfg)
}

// startUserService 启动用户服务
func startUserService() {
	service := NewUserService()
	slog.Info("Starting User Service", slog.String("address", ":8081"))
	if err := service.StartServer(":8081"); err != nil {
		slog.Error("User Service error", slog.Any("error", err))
	}
}

// startOrderService 启动订单服务
func startOrderService() {
	service := NewOrderService()
	slog.Info("Starting Order Service", slog.String("address", ":8082"))
	if err := service.StartServer(":8082"); err != nil {
		slog.Error("Order Service error", slog.Any("error", err))
	}
}

// startPaymentService 启动支付服务
func startPaymentService() {
	service := NewPaymentService()
	slog.Info("Starting Payment Service", slog.String("address", ":8083"))
	if err := service.StartServer(":8083"); err != nil {
		slog.Error("Payment Service error", slog.Any("error", err))
	}
}

// startAPIGateway 启动 API 网关
func startAPIGateway() {
	gateway := NewAPIGateway(
		"http://localhost:8082", // Order Service
		"http://localhost:8083", // Payment Service
		"http://localhost:8081", // User Service
	)
	slog.Info("Starting API Gateway", slog.String("address", ":8080"))
	if err := gateway.StartServer(":8080"); err != nil {
		slog.Error("API Gateway error", slog.Any("error", err))
	}
}

// runTestScenarios 运行测试场景
func runTestScenarios(ctx context.Context) {
	tracer := otel.Tracer("test-scenarios")

	slog.Info("=== Running Test Scenarios ===")

	// 场景 1: 成功的订单创建流程
	func() {
		ctx, span := tracer.Start(ctx, "scenario.successful_order")
		defer span.End()

		slog.Info("Scenario 1: Successful Order Creation")

		gateway := NewAPIGateway(
			"http://localhost:8082",
			"http://localhost:8083",
			"http://localhost:8081",
		)

		req := &types.CreateOrderRequest{
			UserID: "user-001",
			Items: []types.OrderItem{
				{ProductID: "prod-001", Quantity: 2, Price: 29.99},
				{ProductID: "prod-002", Quantity: 1, Price: 49.99},
			},
			TotalAmount:   109.97,
			PaymentMethod: "credit_card",
		}

		// 模拟创建订单（实际应该通过 HTTP 调用）
		order, err := gateway.orderService.CreateOrder(ctx, req)
		if err != nil {
			slog.Info("  ❌ Failed", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ Order Created",
			slog.String("id", order.ID),
			slog.Float64("total", order.TotalAmount))

		// 处理支付
		payment, err := gateway.paymentService.ProcessPayment(ctx, &types.PaymentRequest{
			OrderID: order.ID,
			Amount:  order.TotalAmount,
			Method:  "credit_card",
		})
		if err != nil {
			slog.Info("  ❌ Payment Failed", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ Payment Processed",
			slog.String("id", payment.ID),
			slog.String("status", payment.Status))
	}()

	time.Sleep(1 * time.Second)

	// 场景 2: 用户验证失败
	func() {
		ctx, span := tracer.Start(ctx, "scenario.invalid_user")
		defer span.End()

		slog.Info("Scenario 2: Invalid User")

		gateway := NewAPIGateway(
			"http://localhost:8082",
			"http://localhost:8083",
			"http://localhost:8081",
		)

		// 尝试使用不存在的用户
		user, err := gateway.userService.GetUser(ctx, "user-999")
		if err != nil {
			slog.Info("  ✅ Expected Error", slog.Any("error", err))
		} else {
			slog.Info("  ❌ Unexpected Success", slog.Any("user", user))
		}
	}()

	time.Sleep(1 * time.Second)

	// 场景 3: 查询用户统计信息
	func() {
		ctx, span := tracer.Start(ctx, "scenario.user_stats")
		defer span.End()

		slog.Info("Scenario 3: User Stats Query")

		client := NewUserServiceClient("http://localhost:8081")

		user, err := client.GetUser(ctx, "user-001")
		if err != nil {
			slog.Info("  ❌ Failed to get user", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ User Found",
			slog.String("name", user.Name),
			slog.String("email", user.Email),
			slog.String("level", user.Level))

		stats, err := client.GetUserStats(ctx, "user-001")
		if err != nil {
			slog.Info("  ❌ Failed to get stats", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ Stats Retrieved",
			slog.Any("total_orders", stats["total_orders"]),
			slog.Float64("total_spent", stats["total_spent"].(float64)),
			slog.Any("loyalty_points", stats["loyalty_points"]))
	}()

	time.Sleep(1 * time.Second)

	// 场景 4: 订单取消流程
	func() {
		ctx, span := tracer.Start(ctx, "scenario.order_cancellation")
		defer span.End()

		slog.Info("Scenario 4: Order Cancellation")

		orderClient := NewOrderServiceClient("http://localhost:8082")

		// 创建订单
		order, err := orderClient.CreateOrder(ctx, &types.CreateOrderRequest{
			UserID: "user-002",
			Items: []types.OrderItem{
				{ProductID: "prod-003", Quantity: 1, Price: 99.99},
			},
			TotalAmount:   99.99,
			PaymentMethod: "paypal",
		})
		if err != nil {
			slog.Info("  ❌ Failed to create order", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ Order Created", slog.String("id", order.ID))

		// 取消订单
		if err := orderClient.CancelOrder(ctx, order.ID); err != nil {
			slog.Info("  ❌ Failed to cancel", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ Order Cancelled", slog.String("id", order.ID))

		// 验证状态
		updatedOrder, err := orderClient.GetOrder(ctx, order.ID)
		if err != nil {
			slog.Info("  ❌ Failed to verify", slog.Any("error", err))
			return
		}

		slog.Info("  ✅ Status Verified", slog.String("status", updatedOrder.Status))
	}()

	time.Sleep(1 * time.Second)

	// 场景 5: 并发订单处理
	func() {
		ctx, span := tracer.Start(ctx, "scenario.concurrent_orders")
		defer span.End()

		slog.Info("Scenario 5: Concurrent Order Processing")

		gateway := NewAPIGateway(
			"http://localhost:8082",
			"http://localhost:8083",
			"http://localhost:8081",
		)

		// 并发创建多个订单
		numOrders := 5
		results := make(chan string, numOrders)

		for i := range numOrders {
			go func(orderNum int) {
				ctx, span := tracer.Start(ctx, fmt.Sprintf("order.%d", orderNum))
				defer span.End()

				order, err := gateway.orderService.CreateOrder(ctx, &types.CreateOrderRequest{
					UserID: "user-003",
					Items: []types.OrderItem{
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
		for range numOrders {
			slog.Info("  ✅ " + <-results)
		}
	}()

	slog.Info("=== All Test Scenarios Completed ===")
}

// waitForShutdown 等待关闭信号
func waitForShutdown() {
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)

	sig := <-sigCh
	slog.Info("Received signal, shutting down gracefully", slog.String("signal", sig.String()))

	// 优雅关闭 OpenTelemetry
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	if err := otelmanager.ShutdownGlobalOTel(ctx); err != nil {
		slog.Error("Error shutting down OpenTelemetry", slog.Any("error", err))
	}

	// 给服务一些时间完成处理
	time.Sleep(2 * time.Second)

	slog.Info("Shutdown complete")
}

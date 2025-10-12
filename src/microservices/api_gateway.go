package microservices

import (
	"encoding/json"
	"fmt"
	"net/http"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"

	"OTLP_go/src/pkg/types"
)

// APIGateway 微服务 API 网关实现
// 负责路由请求、统一认证、追踪传播

type APIGateway struct {
	orderService   *OrderServiceClient
	paymentService *PaymentServiceClient
	userService    *UserServiceClient
	tracer         trace.Tracer
	propagator     propagation.TextMapPropagator
}

// NewAPIGateway 创建 API 网关
func NewAPIGateway(orderURL, paymentURL, userURL string) *APIGateway {
	return &APIGateway{
		orderService:   NewOrderServiceClient(orderURL),
		paymentService: NewPaymentServiceClient(paymentURL),
		userService:    NewUserServiceClient(userURL),
		tracer:         otel.Tracer("api-gateway"),
		propagator:     otel.GetTextMapPropagator(),
	}
}

// CreateOrder 处理创建订单请求
func (gw *APIGateway) CreateOrder(w http.ResponseWriter, r *http.Request) {
	// 从 HTTP Headers 中提取 Trace Context
	ctx := gw.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := gw.tracer.Start(ctx, "APIGateway.CreateOrder",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			attribute.String("http.method", r.Method),
			attribute.String("http.url", r.URL.String()),
			attribute.String("http.client_ip", r.RemoteAddr),
		),
	)
	defer span.End()

	// 解析请求
	var req types.CreateOrderRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "invalid request body")
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	span.SetAttributes(
		attribute.String("order.user_id", req.UserID),
		attribute.Int("order.items_count", len(req.Items)),
		attribute.Float64("order.total_amount", req.TotalAmount),
	)

	// 1. 验证用户
	ctx, userSpan := gw.tracer.Start(ctx, "verify_user")
	user, err := gw.userService.GetUser(ctx, req.UserID)
	if err != nil {
		userSpan.RecordError(err)
		userSpan.SetStatus(codes.Error, "user verification failed")
		userSpan.End()
		span.RecordError(err)
		span.SetStatus(codes.Error, "user verification failed")
		http.Error(w, "User not found", http.StatusUnauthorized)
		return
	}
	userSpan.SetAttributes(
		attribute.String("user.name", user.Name),
		attribute.String("user.email", user.Email),
	)
	userSpan.End()

	// 2. 创建订单
	ctx, orderSpan := gw.tracer.Start(ctx, "create_order")
	order, err := gw.orderService.CreateOrder(ctx, &req)
	if err != nil {
		orderSpan.RecordError(err)
		orderSpan.SetStatus(codes.Error, "order creation failed")
		orderSpan.End()
		span.RecordError(err)
		span.SetStatus(codes.Error, "order creation failed")
		http.Error(w, "Failed to create order", http.StatusInternalServerError)
		return
	}
	orderSpan.SetAttributes(
		attribute.String("order.id", order.ID),
		attribute.String("order.status", order.Status),
	)
	orderSpan.End()

	// 3. 处理支付
	ctx, paymentSpan := gw.tracer.Start(ctx, "process_payment")
	payment, err := gw.paymentService.ProcessPayment(ctx, &types.PaymentRequest{
		OrderID: order.ID,
		Amount:  req.TotalAmount,
		Method:  req.PaymentMethod,
	})
	if err != nil {
		paymentSpan.RecordError(err)
		paymentSpan.SetStatus(codes.Error, "payment failed")
		paymentSpan.End()

		// 支付失败，取消订单
		gw.orderService.CancelOrder(ctx, order.ID)

		span.RecordError(err)
		span.SetStatus(codes.Error, "payment processing failed")
		http.Error(w, "Payment failed", http.StatusPaymentRequired)
		return
	}
	paymentSpan.SetAttributes(
		attribute.String("payment.id", payment.ID),
		attribute.String("payment.status", payment.Status),
	)
	paymentSpan.End()

	// 4. 返回响应
	response := types.CreateOrderResponse{
		OrderID:   order.ID,
		PaymentID: payment.ID,
		Status:    "completed",
		CreatedAt: time.Now(),
	}

	span.SetAttributes(
		attribute.String("response.order_id", response.OrderID),
		attribute.String("response.status", response.Status),
	)
	span.SetStatus(codes.Ok, "order created successfully")

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(response)
}

// GetOrder 查询订单详情
func (gw *APIGateway) GetOrder(w http.ResponseWriter, r *http.Request) {
	ctx := gw.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := gw.tracer.Start(ctx, "APIGateway.GetOrder",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	orderID := r.URL.Query().Get("id")
	if orderID == "" {
		span.SetStatus(codes.Error, "missing order_id")
		http.Error(w, "Missing order_id", http.StatusBadRequest)
		return
	}

	span.SetAttributes(attribute.String("order.id", orderID))

	// 查询订单
	order, err := gw.orderService.GetOrder(ctx, orderID)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "order not found")
		http.Error(w, "Order not found", http.StatusNotFound)
		return
	}

	span.SetStatus(codes.Ok, "order retrieved")

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(order)
}

// HealthCheck 健康检查
func (gw *APIGateway) HealthCheck(w http.ResponseWriter, r *http.Request) {
	_, span := gw.tracer.Start(r.Context(), "APIGateway.HealthCheck")
	defer span.End()

	health := map[string]string{
		"status": "healthy",
		"time":   time.Now().Format(time.RFC3339),
	}

	// 检查下游服务健康状态
	services := []string{"order", "payment", "user"}
	for _, service := range services {
		health[service] = "ok" // 简化示例，实际应调用健康检查接口
	}

	span.SetStatus(codes.Ok, "healthy")

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(health)
}

// 注意：数据结构已移至 pkg/types 包中

// StartServer 启动 API 网关服务器
func (gw *APIGateway) StartServer(addr string) error {
	mux := http.NewServeMux()

	// 注册路由
	mux.HandleFunc("/api/orders", gw.CreateOrder)
	mux.HandleFunc("/api/orders/get", gw.GetOrder)
	mux.HandleFunc("/health", gw.HealthCheck)

	// 添加追踪中间件
	handler := gw.tracingMiddleware(mux)

	server := &http.Server{
		Addr:         addr,
		Handler:      handler,
		ReadTimeout:  10 * time.Second,
		WriteTimeout: 10 * time.Second,
	}

	fmt.Printf("API Gateway listening on %s\n", addr)
	return server.ListenAndServe()
}

// tracingMiddleware 追踪中间件
func (gw *APIGateway) tracingMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ctx := gw.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

		ctx, span := gw.tracer.Start(ctx, fmt.Sprintf("%s %s", r.Method, r.URL.Path),
			trace.WithSpanKind(trace.SpanKindServer),
			trace.WithAttributes(
				attribute.String("http.method", r.Method),
				attribute.String("http.url", r.URL.String()),
				attribute.String("http.user_agent", r.UserAgent()),
			),
		)
		defer span.End()

		// 包装 ResponseWriter 以捕获状态码
		wrapped := &responseWriter{ResponseWriter: w, statusCode: http.StatusOK}

		next.ServeHTTP(wrapped, r.WithContext(ctx))

		span.SetAttributes(
			attribute.Int("http.status_code", wrapped.statusCode),
		)

		if wrapped.statusCode >= 400 {
			span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", wrapped.statusCode))
		} else {
			span.SetStatus(codes.Ok, "request completed")
		}
	})
}

type responseWriter struct {
	http.ResponseWriter
	statusCode int
}

func (rw *responseWriter) WriteHeader(code int) {
	rw.statusCode = code
	rw.ResponseWriter.WriteHeader(code)
}

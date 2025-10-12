package microservices

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"

	"OTLP_go/src/pkg/types"
)

// OrderService 订单服务实现
type OrderService struct {
	tracer     trace.Tracer
	propagator propagation.TextMapPropagator
	orders     sync.Map // 简单的内存存储，实际应用中使用数据库
}

// NewOrderService 创建订单服务
func NewOrderService() *OrderService {
	return &OrderService{
		tracer:     otel.Tracer("order-service"),
		propagator: otel.GetTextMapPropagator(),
	}
}

// 注意：Order 数据结构已移至 pkg/types 包中

// CreateOrderHandler HTTP 处理器
func (os *OrderService) CreateOrderHandler(w http.ResponseWriter, r *http.Request) {
	ctx := os.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := os.tracer.Start(ctx, "OrderService.CreateOrder",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			attribute.String("service.name", "order-service"),
		),
	)
	defer span.End()

	var req types.CreateOrderRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "invalid request")
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	// 创建订单
	order, err := os.createOrder(ctx, &req)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetAttributes(
		attribute.String("order.id", order.ID),
		attribute.String("order.status", order.Status),
		attribute.Float64("order.amount", order.TotalAmount),
	)
	span.SetStatus(codes.Ok, "order created")

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(order)
}

// createOrder 创建订单业务逻辑
func (os *OrderService) createOrder(ctx context.Context, req *types.CreateOrderRequest) (*types.Order, error) {
	ctx, span := os.tracer.Start(ctx, "OrderService.createOrder")
	defer span.End()

	// 1. 验证请求
	ctx, validateSpan := os.tracer.Start(ctx, "validate_order")
	if err := os.validateOrder(ctx, req); err != nil {
		validateSpan.RecordError(err)
		validateSpan.SetStatus(codes.Error, "validation failed")
		validateSpan.End()
		return nil, err
	}
	validateSpan.SetStatus(codes.Ok, "validated")
	validateSpan.End()

	// 2. 检查库存（模拟）
	ctx, inventorySpan := os.tracer.Start(ctx, "check_inventory")
	if err := os.checkInventory(ctx, req.Items); err != nil {
		inventorySpan.RecordError(err)
		inventorySpan.SetStatus(codes.Error, "insufficient inventory")
		inventorySpan.End()
		return nil, err
	}
	inventorySpan.SetAttributes(attribute.Int("items.count", len(req.Items)))
	inventorySpan.SetStatus(codes.Ok, "inventory available")
	inventorySpan.End()

	// 3. 创建订单记录
	order := &types.Order{
		ID:          generateOrderID(),
		UserID:      req.UserID,
		Items:       req.Items,
		TotalAmount: req.TotalAmount,
		Status:      "pending",
		CreatedAt:   time.Now(),
		UpdatedAt:   time.Now(),
	}

	// 4. 保存到存储
	_, saveSpan := os.tracer.Start(ctx, "save_order")
	os.orders.Store(order.ID, order)
	saveSpan.AddEvent("order.saved", trace.WithAttributes(
		attribute.String("order.id", order.ID),
	))
	saveSpan.SetStatus(codes.Ok, "saved")
	saveSpan.End()

	span.AddEvent("order.created", trace.WithAttributes(
		attribute.String("order.id", order.ID),
		attribute.String("user.id", order.UserID),
	))

	return order, nil
}

// GetOrderHandler 查询订单处理器
func (os *OrderService) GetOrderHandler(w http.ResponseWriter, r *http.Request) {
	ctx := os.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := os.tracer.Start(ctx, "OrderService.GetOrder",
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

	order, err := os.getOrder(ctx, orderID)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "order not found")
		http.Error(w, "Order not found", http.StatusNotFound)
		return
	}

	span.SetStatus(codes.Ok, "order found")

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(order)
}

// getOrder 查询订单
func (os *OrderService) getOrder(ctx context.Context, orderID string) (*types.Order, error) {
	_, span := os.tracer.Start(ctx, "OrderService.getOrder")
	defer span.End()

	// 从存储中查询
	value, ok := os.orders.Load(orderID)
	if !ok {
		err := fmt.Errorf("order not found: %s", orderID)
		span.RecordError(err)
		return nil, err
	}

	order := value.(*types.Order)
	span.SetAttributes(
		attribute.String("order.id", order.ID),
		attribute.String("order.status", order.Status),
	)

	return order, nil
}

// UpdateOrderStatusHandler 更新订单状态
func (os *OrderService) UpdateOrderStatusHandler(w http.ResponseWriter, r *http.Request) {
	ctx := os.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := os.tracer.Start(ctx, "OrderService.UpdateOrderStatus",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	var req struct {
		OrderID string `json:"order_id"`
		Status  string `json:"status"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	if err := os.updateOrderStatus(ctx, req.OrderID, req.Status); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetAttributes(
		attribute.String("order.id", req.OrderID),
		attribute.String("order.new_status", req.Status),
	)
	span.SetStatus(codes.Ok, "status updated")

	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "Order status updated")
}

// updateOrderStatus 更新订单状态
func (os *OrderService) updateOrderStatus(ctx context.Context, orderID, status string) error {
	_, span := os.tracer.Start(ctx, "OrderService.updateOrderStatus")
	defer span.End()

	value, ok := os.orders.Load(orderID)
	if !ok {
		err := fmt.Errorf("order not found: %s", orderID)
		span.RecordError(err)
		return err
	}

	order := value.(*types.Order)
	oldStatus := order.Status
	order.Status = status
	order.UpdatedAt = time.Now()

	os.orders.Store(orderID, order)

	span.AddEvent("order.status.updated", trace.WithAttributes(
		attribute.String("order.id", orderID),
		attribute.String("old_status", oldStatus),
		attribute.String("new_status", status),
	))

	return nil
}

// CancelOrderHandler 取消订单
func (os *OrderService) CancelOrderHandler(w http.ResponseWriter, r *http.Request) {
	ctx := os.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := os.tracer.Start(ctx, "OrderService.CancelOrder",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	orderID := r.URL.Query().Get("id")
	if orderID == "" {
		span.SetStatus(codes.Error, "missing order_id")
		http.Error(w, "Missing order_id", http.StatusBadRequest)
		return
	}

	if err := os.cancelOrder(ctx, orderID); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetStatus(codes.Ok, "order cancelled")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "Order cancelled")
}

// cancelOrder 取消订单业务逻辑
func (os *OrderService) cancelOrder(ctx context.Context, orderID string) error {
	ctx, span := os.tracer.Start(ctx, "OrderService.cancelOrder")
	defer span.End()

	// 1. 查询订单
	order, err := os.getOrder(ctx, orderID)
	if err != nil {
		return err
	}

	// 2. 检查订单状态
	if order.Status == "completed" || order.Status == "cancelled" {
		err := fmt.Errorf("cannot cancel order in status: %s", order.Status)
		span.RecordError(err)
		return err
	}

	// 3. 更新状态
	if err := os.updateOrderStatus(ctx, orderID, "cancelled"); err != nil {
		return err
	}

	// 4. 恢复库存（模拟）
	ctx, restoreSpan := os.tracer.Start(ctx, "restore_inventory")
	os.restoreInventory(ctx, order.Items)
	restoreSpan.SetStatus(codes.Ok, "inventory restored")
	restoreSpan.End()

	span.AddEvent("order.cancelled", trace.WithAttributes(
		attribute.String("order.id", orderID),
	))

	return nil
}

// Helper methods
func (os *OrderService) validateOrder(ctx context.Context, req *types.CreateOrderRequest) error {
	if req.UserID == "" {
		return fmt.Errorf("user_id is required")
	}
	if len(req.Items) == 0 {
		return fmt.Errorf("items cannot be empty")
	}
	if req.TotalAmount <= 0 {
		return fmt.Errorf("total_amount must be positive")
	}
	return nil
}

func (os *OrderService) checkInventory(ctx context.Context, items []types.OrderItem) error {
	// 模拟库存检查
	time.Sleep(10 * time.Millisecond)
	return nil
}

func (os *OrderService) restoreInventory(ctx context.Context, items []types.OrderItem) {
	// 模拟库存恢复
	time.Sleep(10 * time.Millisecond)
}

func generateOrderID() string {
	return fmt.Sprintf("ORD-%d", time.Now().UnixNano())
}

// StartServer 启动订单服务
func (os *OrderService) StartServer(addr string) error {
	mux := http.NewServeMux()

	mux.HandleFunc("/orders/create", os.CreateOrderHandler)
	mux.HandleFunc("/orders/get", os.GetOrderHandler)
	mux.HandleFunc("/orders/update-status", os.UpdateOrderStatusHandler)
	mux.HandleFunc("/orders/cancel", os.CancelOrderHandler)

	server := &http.Server{
		Addr:         addr,
		Handler:      mux,
		ReadTimeout:  10 * time.Second,
		WriteTimeout: 10 * time.Second,
	}

	fmt.Printf("Order Service listening on %s\n", addr)
	return server.ListenAndServe()
}

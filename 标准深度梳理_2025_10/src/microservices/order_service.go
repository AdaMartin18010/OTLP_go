package microservices

import (
	"context"
	"fmt"
	"log"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"

	"otlp-go-monitoring/src/pkg/types"
)

// OrderService handles order-related operations
type OrderService struct {
	tracer trace.Tracer
	orders map[string]*types.Order
}

// NewOrderService creates a new OrderService instance
func NewOrderService() *OrderService {
	return &OrderService{
		tracer: otel.Tracer("order-service"),
		orders: make(map[string]*types.Order),
	}
}

// CreateOrder creates a new order
func (os *OrderService) CreateOrder(ctx context.Context, req *types.CreateOrderRequest) (*types.Order, error) {
	ctx, span := os.tracer.Start(ctx, "create-order")
	defer span.End()

	span.SetAttributes(
		attribute.String("order.user_id", req.UserID),
		attribute.Int("order.items_count", len(req.Items)),
		attribute.Float64("order.total_amount", req.TotalAmount),
	)

	// Simulate order creation
	time.Sleep(100 * time.Millisecond)

	order := &types.Order{
		ID:          fmt.Sprintf("order-%d", time.Now().UnixNano()),
		UserID:      req.UserID,
		Items:       req.Items,
		TotalAmount: req.TotalAmount,
		Status:      types.OrderStatusPending,
		CreatedAt:   time.Now(),
		UpdatedAt:   time.Now(),
	}

	os.orders[order.ID] = order

	span.SetAttributes(
		attribute.String("order.id", order.ID),
		attribute.String("order.status", order.Status),
	)

	span.SetStatus(codes.Ok, "Order created successfully")
	log.Printf("Order created: %s", order.ID)

	return order, nil
}

// GetOrder retrieves an order by ID
func (os *OrderService) GetOrder(ctx context.Context, orderID string) (*types.Order, error) {
	ctx, span := os.tracer.Start(ctx, "get-order")
	defer span.End()

	span.SetAttributes(
		attribute.String("order.id", orderID),
	)

	// Simulate order retrieval
	time.Sleep(50 * time.Millisecond)

	order, exists := os.orders[orderID]
	if !exists {
		span.SetStatus(codes.Error, "Order not found")
		return nil, fmt.Errorf("order not found: %s", orderID)
	}

	span.SetAttributes(
		attribute.String("order.status", order.Status),
		attribute.String("order.user_id", order.UserID),
		attribute.Float64("order.total_amount", order.TotalAmount),
	)

	span.SetStatus(codes.Ok, "Order retrieved successfully")
	log.Printf("Order retrieved: %s", orderID)

	return order, nil
}

// CancelOrder cancels an order
func (os *OrderService) CancelOrder(ctx context.Context, orderID string) error {
	ctx, span := os.tracer.Start(ctx, "cancel-order")
	defer span.End()

	span.SetAttributes(
		attribute.String("order.id", orderID),
	)

	// Simulate order cancellation
	time.Sleep(50 * time.Millisecond)

	order, exists := os.orders[orderID]
	if !exists {
		span.SetStatus(codes.Error, "Order not found")
		return fmt.Errorf("order not found: %s", orderID)
	}

	order.Status = types.OrderStatusCancelled
	order.UpdatedAt = time.Now()

	span.SetAttributes(
		attribute.String("order.status", order.Status),
	)

	span.SetStatus(codes.Ok, "Order cancelled successfully")
	log.Printf("Order cancelled: %s", orderID)

	return nil
}

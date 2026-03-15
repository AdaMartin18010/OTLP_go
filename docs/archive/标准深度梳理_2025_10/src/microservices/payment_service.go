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

// PaymentService handles payment-related operations
type PaymentService struct {
	tracer   trace.Tracer
	payments map[string]*types.Payment
}

// NewPaymentService creates a new PaymentService instance
func NewPaymentService() *PaymentService {
	return &PaymentService{
		tracer:   otel.Tracer("payment-service"),
		payments: make(map[string]*types.Payment),
	}
}

// ProcessPayment processes a payment
func (ps *PaymentService) ProcessPayment(ctx context.Context, req *types.PaymentRequest) (*types.Payment, error) {
	ctx, span := ps.tracer.Start(ctx, "process-payment")
	defer span.End()

	span.SetAttributes(
		attribute.String("payment.order_id", req.OrderID),
		attribute.Float64("payment.amount", req.Amount),
		attribute.String("payment.method", req.Method),
	)

	// Simulate payment processing
	time.Sleep(150 * time.Millisecond)

	payment := &types.Payment{
		ID:            fmt.Sprintf("payment-%d", time.Now().UnixNano()),
		OrderID:       req.OrderID,
		Amount:        req.Amount,
		Method:        req.Method,
		Status:        types.PaymentStatusCompleted,
		TransactionID: fmt.Sprintf("txn-%d", time.Now().UnixNano()),
		CreatedAt:     time.Now(),
		CompletedAt:   time.Now(),
	}

	ps.payments[payment.ID] = payment

	span.SetAttributes(
		attribute.String("payment.id", payment.ID),
		attribute.String("payment.status", payment.Status),
		attribute.String("payment.transaction_id", payment.TransactionID),
	)

	span.SetStatus(codes.Ok, "Payment processed successfully")
	log.Printf("Payment processed: %s", payment.ID)

	return payment, nil
}

// GetPayment retrieves a payment by ID
func (ps *PaymentService) GetPayment(ctx context.Context, paymentID string) (*types.Payment, error) {
	ctx, span := ps.tracer.Start(ctx, "get-payment")
	defer span.End()

	span.SetAttributes(
		attribute.String("payment.id", paymentID),
	)

	// Simulate payment retrieval
	time.Sleep(50 * time.Millisecond)

	payment, exists := ps.payments[paymentID]
	if !exists {
		span.SetStatus(codes.Error, "Payment not found")
		return nil, fmt.Errorf("payment not found: %s", paymentID)
	}

	span.SetAttributes(
		attribute.String("payment.status", payment.Status),
		attribute.String("payment.order_id", payment.OrderID),
		attribute.Float64("payment.amount", payment.Amount),
	)

	span.SetStatus(codes.Ok, "Payment retrieved successfully")
	log.Printf("Payment retrieved: %s", paymentID)

	return payment, nil
}

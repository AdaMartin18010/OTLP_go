package microservices

import (
	"OTLP_go/src/pkg/types"
	"context"
	"encoding/json"
	"fmt"
	"math/rand"
	"net/http"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
)

// PaymentService 支付服务实现
type PaymentService struct {
	tracer     trace.Tracer
	propagator propagation.TextMapPropagator
	payments   sync.Map
}

// NewPaymentService 创建支付服务
func NewPaymentService() *PaymentService {
	return &PaymentService{
		tracer:     otel.Tracer("payment-service"),
		propagator: otel.GetTextMapPropagator(),
	}
}

// PaymentService 使用 types 包中的类型定义

// ProcessPaymentHandler 处理支付请求
func (ps *PaymentService) ProcessPaymentHandler(w http.ResponseWriter, r *http.Request) {
	ctx := ps.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := ps.tracer.Start(ctx, "PaymentService.ProcessPayment",
		trace.WithSpanKind(trace.SpanKindServer),
		trace.WithAttributes(
			attribute.String("service.name", "payment-service"),
		),
	)
	defer span.End()

	var req types.PaymentRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "invalid request")
		http.Error(w, "Invalid request", http.StatusBadRequest)
		return
	}

	// 处理支付
	payment, err := ps.processPayment(ctx, &req)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetAttributes(
		attribute.String("payment.id", payment.ID),
		attribute.String("payment.status", payment.Status),
		attribute.Float64("payment.amount", payment.Amount),
	)
	span.SetStatus(codes.Ok, "payment processed")

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(payment)
}

// processPayment 处理支付业务逻辑
func (ps *PaymentService) processPayment(ctx context.Context, req *types.PaymentRequest) (*types.Payment, error) {
	ctx, span := ps.tracer.Start(ctx, "PaymentService.processPayment")
	defer span.End()

	span.SetAttributes(
		attribute.String("order.id", req.OrderID),
		attribute.Float64("amount", req.Amount),
		attribute.String("method", req.Method),
	)

	// 1. 验证支付请求
	ctx, validateSpan := ps.tracer.Start(ctx, "validate_payment")
	if err := ps.validatePayment(ctx, req); err != nil {
		validateSpan.RecordError(err)
		validateSpan.SetStatus(codes.Error, "validation failed")
		validateSpan.End()
		return nil, err
	}
	validateSpan.SetStatus(codes.Ok, "validated")
	validateSpan.End()

	// 2. 风险检查
	ctx, riskSpan := ps.tracer.Start(ctx, "risk_check")
	if err := ps.performRiskCheck(ctx, req); err != nil {
		riskSpan.RecordError(err)
		riskSpan.SetStatus(codes.Error, "risk check failed")
		riskSpan.End()
		return nil, err
	}
	riskSpan.SetAttributes(attribute.String("risk.level", "low"))
	riskSpan.SetStatus(codes.Ok, "risk check passed")
	riskSpan.End()

	// 3. 调用支付网关
	ctx, gatewaySpan := ps.tracer.Start(ctx, "payment_gateway")
	transactionID, err := ps.callPaymentGateway(ctx, req)
	if err != nil {
		gatewaySpan.RecordError(err)
		gatewaySpan.SetStatus(codes.Error, "gateway error")
		gatewaySpan.End()
		return nil, err
	}
	gatewaySpan.SetAttributes(attribute.String("transaction.id", transactionID))
	gatewaySpan.SetStatus(codes.Ok, "transaction completed")
	gatewaySpan.End()

	// 4. 创建支付记录
	payment := &types.Payment{
		ID:            generatePaymentID(),
		OrderID:       req.OrderID,
		Amount:        req.Amount,
		Method:        req.Method,
		Status:        "completed",
		TransactionID: transactionID,
		CreatedAt:     time.Now(),
		CompletedAt:   time.Now(),
	}

	// 5. 保存到存储
	ps.payments.Store(payment.ID, payment)

	span.AddEvent("payment.completed", trace.WithAttributes(
		attribute.String("payment.id", payment.ID),
		attribute.String("transaction.id", transactionID),
	))

	return payment, nil
}

// GetPaymentHandler 查询支付信息
func (ps *PaymentService) GetPaymentHandler(w http.ResponseWriter, r *http.Request) {
	ctx := ps.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := ps.tracer.Start(ctx, "PaymentService.GetPayment",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	paymentID := r.URL.Query().Get("id")
	if paymentID == "" {
		span.SetStatus(codes.Error, "missing payment_id")
		http.Error(w, "Missing payment_id", http.StatusBadRequest)
		return
	}

	payment, err := ps.getPayment(ctx, paymentID)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "payment not found")
		http.Error(w, "Payment not found", http.StatusNotFound)
		return
	}

	span.SetStatus(codes.Ok, "payment found")

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(payment)
}

// getPayment 查询支付
func (ps *PaymentService) getPayment(ctx context.Context, paymentID string) (*types.Payment, error) {
	_, span := ps.tracer.Start(ctx, "PaymentService.getPayment")
	defer span.End()

	value, ok := ps.payments.Load(paymentID)
	if !ok {
		err := fmt.Errorf("payment not found: %s", paymentID)
		span.RecordError(err)
		return nil, err
	}

	payment := value.(*types.Payment)
	return payment, nil
}

// RefundPaymentHandler 退款处理
func (ps *PaymentService) RefundPaymentHandler(w http.ResponseWriter, r *http.Request) {
	ctx := ps.propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

	ctx, span := ps.tracer.Start(ctx, "PaymentService.RefundPayment",
		trace.WithSpanKind(trace.SpanKindServer),
	)
	defer span.End()

	paymentID := r.URL.Query().Get("id")
	if paymentID == "" {
		span.SetStatus(codes.Error, "missing payment_id")
		http.Error(w, "Missing payment_id", http.StatusBadRequest)
		return
	}

	if err := ps.refundPayment(ctx, paymentID); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	span.SetStatus(codes.Ok, "refund completed")
	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "Refund completed")
}

// refundPayment 退款业务逻辑
func (ps *PaymentService) refundPayment(ctx context.Context, paymentID string) error {
	ctx, span := ps.tracer.Start(ctx, "PaymentService.refundPayment")
	defer span.End()

	// 1. 查询支付记录
	payment, err := ps.getPayment(ctx, paymentID)
	if err != nil {
		return err
	}

	// 2. 检查支付状态
	if payment.Status != "completed" {
		err := fmt.Errorf("cannot refund payment in status: %s", payment.Status)
		span.RecordError(err)
		return err
	}

	// 3. 调用支付网关退款
	ctx, gatewaySpan := ps.tracer.Start(ctx, "payment_gateway.refund")
	if err := ps.callPaymentGatewayRefund(ctx, payment.TransactionID); err != nil {
		gatewaySpan.RecordError(err)
		gatewaySpan.SetStatus(codes.Error, "refund failed")
		gatewaySpan.End()
		return err
	}
	gatewaySpan.SetStatus(codes.Ok, "refund completed")
	gatewaySpan.End()

	// 4. 更新状态
	payment.Status = "refunded"
	ps.payments.Store(paymentID, payment)

	span.AddEvent("payment.refunded", trace.WithAttributes(
		attribute.String("payment.id", paymentID),
		attribute.Float64("amount", payment.Amount),
	))

	return nil
}

// Helper methods
func (ps *PaymentService) validatePayment(ctx context.Context, req *types.PaymentRequest) error {
	if req.OrderID == "" {
		return fmt.Errorf("order_id is required")
	}
	if req.Amount <= 0 {
		return fmt.Errorf("amount must be positive")
	}
	if req.Method == "" {
		return fmt.Errorf("payment method is required")
	}
	return nil
}

func (ps *PaymentService) performRiskCheck(ctx context.Context, req *types.PaymentRequest) error {
	_, span := ps.tracer.Start(ctx, "risk_check.analysis")
	defer span.End()

	// 模拟风险检查
	time.Sleep(20 * time.Millisecond)

	// 模拟随机风险评估
	riskScore := rand.Float64()
	span.SetAttributes(attribute.Float64("risk.score", riskScore))

	if riskScore > 0.9 {
		err := fmt.Errorf("high risk transaction detected")
		span.RecordError(err)
		return err
	}

	return nil
}

func (ps *PaymentService) callPaymentGateway(ctx context.Context, req *types.PaymentRequest) (string, error) {
	_, span := ps.tracer.Start(ctx, "payment_gateway.charge")
	defer span.End()

	// 模拟支付网关调用
	time.Sleep(100 * time.Millisecond)

	// 模拟90%成功率
	if rand.Float64() < 0.1 {
		err := fmt.Errorf("payment gateway error")
		span.RecordError(err)
		return "", err
	}

	transactionID := fmt.Sprintf("TXN-%d", time.Now().UnixNano())
	span.SetAttributes(attribute.String("transaction.id", transactionID))

	return transactionID, nil
}

func (ps *PaymentService) callPaymentGatewayRefund(ctx context.Context, transactionID string) error {
	_, span := ps.tracer.Start(ctx, "payment_gateway.refund_call")
	defer span.End()

	span.SetAttributes(attribute.String("transaction.id", transactionID))

	// 模拟退款调用
	time.Sleep(80 * time.Millisecond)

	return nil
}

func generatePaymentID() string {
	return fmt.Sprintf("PAY-%d", time.Now().UnixNano())
}

// StartServer 启动支付服务
func (ps *PaymentService) StartServer(addr string) error {
	mux := http.NewServeMux()

	mux.HandleFunc("/payments/process", ps.ProcessPaymentHandler)
	mux.HandleFunc("/payments/get", ps.GetPaymentHandler)
	mux.HandleFunc("/payments/refund", ps.RefundPaymentHandler)

	server := &http.Server{
		Addr:         addr,
		Handler:      mux,
		ReadTimeout:  10 * time.Second,
		WriteTimeout: 10 * time.Second,
	}

	fmt.Printf("Payment Service listening on %s\n", addr)
	return server.ListenAndServe()
}

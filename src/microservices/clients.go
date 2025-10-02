package microservices

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/propagation"
	"go.opentelemetry.io/otel/trace"
)

// OrderServiceClient 订单服务客户端
type OrderServiceClient struct {
	baseURL    string
	httpClient *http.Client
	tracer     trace.Tracer
	propagator propagation.TextMapPropagator
}

// NewOrderServiceClient 创建订单服务客户端
func NewOrderServiceClient(baseURL string) *OrderServiceClient {
	return &OrderServiceClient{
		baseURL: baseURL,
		httpClient: &http.Client{
			Timeout: 10 * time.Second,
		},
		tracer:     otel.Tracer("order-service-client"),
		propagator: otel.GetTextMapPropagator(),
	}
}

// CreateOrder 创建订单
func (c *OrderServiceClient) CreateOrder(ctx context.Context, req *CreateOrderRequest) (*Order, error) {
	ctx, span := c.tracer.Start(ctx, "OrderServiceClient.CreateOrder",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("peer.service", "order-service"),
		),
	)
	defer span.End()

	body, err := json.Marshal(req)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	httpReq, err := http.NewRequestWithContext(ctx, "POST", c.baseURL+"/orders/create", bytes.NewBuffer(body))
	if err != nil {
		span.RecordError(err)
		return nil, err
	}
	httpReq.Header.Set("Content-Type", "application/json")

	// 注入 Trace Context
	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "http request failed")
		return nil, err
	}
	defer resp.Body.Close()

	span.SetAttributes(attribute.Int("http.status_code", resp.StatusCode))

	if resp.StatusCode != http.StatusCreated {
		body, _ := io.ReadAll(resp.Body)
		err := fmt.Errorf("create order failed: %s", string(body))
		span.RecordError(err)
		span.SetStatus(codes.Error, "order creation failed")
		return nil, err
	}

	var order Order
	if err := json.NewDecoder(resp.Body).Decode(&order); err != nil {
		span.RecordError(err)
		return nil, err
	}

	span.SetStatus(codes.Ok, "order created")
	return &order, nil
}

// GetOrder 查询订单
func (c *OrderServiceClient) GetOrder(ctx context.Context, orderID string) (*Order, error) {
	ctx, span := c.tracer.Start(ctx, "OrderServiceClient.GetOrder",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("order.id", orderID),
		),
	)
	defer span.End()

	httpReq, err := http.NewRequestWithContext(ctx, "GET",
		fmt.Sprintf("%s/orders/get?id=%s", c.baseURL, orderID), nil)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		err := fmt.Errorf("order not found: %s", orderID)
		span.RecordError(err)
		return nil, err
	}

	var order Order
	if err := json.NewDecoder(resp.Body).Decode(&order); err != nil {
		span.RecordError(err)
		return nil, err
	}

	span.SetStatus(codes.Ok, "order retrieved")
	return &order, nil
}

// CancelOrder 取消订单
func (c *OrderServiceClient) CancelOrder(ctx context.Context, orderID string) error {
	ctx, span := c.tracer.Start(ctx, "OrderServiceClient.CancelOrder",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("order.id", orderID),
		),
	)
	defer span.End()

	httpReq, err := http.NewRequestWithContext(ctx, "POST",
		fmt.Sprintf("%s/orders/cancel?id=%s", c.baseURL, orderID), nil)
	if err != nil {
		span.RecordError(err)
		return err
	}

	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		err := fmt.Errorf("cancel order failed")
		span.RecordError(err)
		return err
	}

	span.SetStatus(codes.Ok, "order cancelled")
	return nil
}

// PaymentServiceClient 支付服务客户端
type PaymentServiceClient struct {
	baseURL    string
	httpClient *http.Client
	tracer     trace.Tracer
	propagator propagation.TextMapPropagator
}

// NewPaymentServiceClient 创建支付服务客户端
func NewPaymentServiceClient(baseURL string) *PaymentServiceClient {
	return &PaymentServiceClient{
		baseURL: baseURL,
		httpClient: &http.Client{
			Timeout: 15 * time.Second, // 支付可能需要更长时间
		},
		tracer:     otel.Tracer("payment-service-client"),
		propagator: otel.GetTextMapPropagator(),
	}
}

// ProcessPayment 处理支付
func (c *PaymentServiceClient) ProcessPayment(ctx context.Context, req *PaymentRequest) (*Payment, error) {
	ctx, span := c.tracer.Start(ctx, "PaymentServiceClient.ProcessPayment",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("peer.service", "payment-service"),
			attribute.Float64("amount", req.Amount),
		),
	)
	defer span.End()

	body, err := json.Marshal(req)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	httpReq, err := http.NewRequestWithContext(ctx, "POST", c.baseURL+"/payments/process", bytes.NewBuffer(body))
	if err != nil {
		span.RecordError(err)
		return nil, err
	}
	httpReq.Header.Set("Content-Type", "application/json")

	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "payment request failed")
		return nil, err
	}
	defer resp.Body.Close()

	span.SetAttributes(attribute.Int("http.status_code", resp.StatusCode))

	if resp.StatusCode != http.StatusCreated {
		body, _ := io.ReadAll(resp.Body)
		err := fmt.Errorf("payment failed: %s", string(body))
		span.RecordError(err)
		span.SetStatus(codes.Error, "payment processing failed")
		return nil, err
	}

	var payment Payment
	if err := json.NewDecoder(resp.Body).Decode(&payment); err != nil {
		span.RecordError(err)
		return nil, err
	}

	span.SetAttributes(
		attribute.String("payment.id", payment.ID),
		attribute.String("payment.status", payment.Status),
	)
	span.SetStatus(codes.Ok, "payment processed")

	return &payment, nil
}

// GetPayment 查询支付
func (c *PaymentServiceClient) GetPayment(ctx context.Context, paymentID string) (*Payment, error) {
	ctx, span := c.tracer.Start(ctx, "PaymentServiceClient.GetPayment",
		trace.WithSpanKind(trace.SpanKindClient),
	)
	defer span.End()

	httpReq, err := http.NewRequestWithContext(ctx, "GET",
		fmt.Sprintf("%s/payments/get?id=%s", c.baseURL, paymentID), nil)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		err := fmt.Errorf("payment not found: %s", paymentID)
		span.RecordError(err)
		return nil, err
	}

	var payment Payment
	if err := json.NewDecoder(resp.Body).Decode(&payment); err != nil {
		span.RecordError(err)
		return nil, err
	}

	span.SetStatus(codes.Ok, "payment retrieved")
	return &payment, nil
}

// UserServiceClient 用户服务客户端
type UserServiceClient struct {
	baseURL    string
	httpClient *http.Client
	tracer     trace.Tracer
	propagator propagation.TextMapPropagator
}

// NewUserServiceClient 创建用户服务客户端
func NewUserServiceClient(baseURL string) *UserServiceClient {
	return &UserServiceClient{
		baseURL: baseURL,
		httpClient: &http.Client{
			Timeout: 5 * time.Second,
		},
		tracer:     otel.Tracer("user-service-client"),
		propagator: otel.GetTextMapPropagator(),
	}
}

// GetUser 查询用户
func (c *UserServiceClient) GetUser(ctx context.Context, userID string) (*User, error) {
	ctx, span := c.tracer.Start(ctx, "UserServiceClient.GetUser",
		trace.WithSpanKind(trace.SpanKindClient),
		trace.WithAttributes(
			attribute.String("peer.service", "user-service"),
			attribute.String("user.id", userID),
		),
	)
	defer span.End()

	httpReq, err := http.NewRequestWithContext(ctx, "GET",
		fmt.Sprintf("%s/users/get?id=%s", c.baseURL, userID), nil)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, "user request failed")
		return nil, err
	}
	defer resp.Body.Close()

	span.SetAttributes(attribute.Int("http.status_code", resp.StatusCode))

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		err := fmt.Errorf("user not found: %s, response: %s", userID, string(body))
		span.RecordError(err)
		span.SetStatus(codes.Error, "user not found")
		return nil, err
	}

	var user User
	if err := json.NewDecoder(resp.Body).Decode(&user); err != nil {
		span.RecordError(err)
		return nil, err
	}

	span.SetAttributes(
		attribute.String("user.name", user.Name),
		attribute.String("user.level", user.Level),
	)
	span.SetStatus(codes.Ok, "user retrieved")

	return &user, nil
}

// GetUserStats 获取用户统计信息
func (c *UserServiceClient) GetUserStats(ctx context.Context, userID string) (map[string]interface{}, error) {
	ctx, span := c.tracer.Start(ctx, "UserServiceClient.GetUserStats",
		trace.WithSpanKind(trace.SpanKindClient),
	)
	defer span.End()

	httpReq, err := http.NewRequestWithContext(ctx, "GET",
		fmt.Sprintf("%s/users/stats?id=%s", c.baseURL, userID), nil)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	c.propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		err := fmt.Errorf("failed to get user stats")
		span.RecordError(err)
		return nil, err
	}

	var stats map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&stats); err != nil {
		span.RecordError(err)
		return nil, err
	}

	span.SetStatus(codes.Ok, "stats retrieved")
	return stats, nil
}

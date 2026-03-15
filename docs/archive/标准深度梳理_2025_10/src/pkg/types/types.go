package types

import (
	"time"
)

// 基础数据结构定义

// User 用户数据结构
type User struct {
	ID        string    `json:"id"`
	Name      string    `json:"name"`
	Email     string    `json:"email"`
	Phone     string    `json:"phone"`
	Level     string    `json:"level"` // normal, vip, premium
	CreatedAt time.Time `json:"created_at"`
}

// Order 订单数据结构
type Order struct {
	ID          string      `json:"id"`
	UserID      string      `json:"user_id"`
	Items       []OrderItem `json:"items"`
	TotalAmount float64     `json:"total_amount"`
	Status      string      `json:"status"`
	CreatedAt   time.Time   `json:"created_at"`
	UpdatedAt   time.Time   `json:"updated_at"`
}

// OrderItem 订单项数据结构
type OrderItem struct {
	ProductID string  `json:"product_id"`
	Quantity  int     `json:"quantity"`
	Price     float64 `json:"price"`
}

// Payment 支付数据结构
type Payment struct {
	ID            string    `json:"id"`
	OrderID       string    `json:"order_id"`
	Amount        float64   `json:"amount"`
	Method        string    `json:"method"`
	Status        string    `json:"status"`
	TransactionID string    `json:"transaction_id"`
	CreatedAt     time.Time `json:"created_at"`
	CompletedAt   time.Time `json:"completed_at,omitempty"`
}

// 请求/响应数据结构

// CreateOrderRequest 创建订单请求
type CreateOrderRequest struct {
	UserID        string      `json:"user_id"`
	Items         []OrderItem `json:"items"`
	TotalAmount   float64     `json:"total_amount"`
	PaymentMethod string      `json:"payment_method"`
}

// CreateOrderResponse 创建订单响应
type CreateOrderResponse struct {
	OrderID   string    `json:"order_id"`
	PaymentID string    `json:"payment_id"`
	Status    string    `json:"status"`
	CreatedAt time.Time `json:"created_at"`
}

// PaymentRequest 支付请求
type PaymentRequest struct {
	OrderID string  `json:"order_id"`
	Amount  float64 `json:"amount"`
	Method  string  `json:"method"`
}

// 服务接口定义

// UserServiceInterface 用户服务接口
type UserServiceInterface interface {
	GetUser(ctx interface{}, userID string) (*User, error)
	GetUserStats(ctx interface{}, userID string) (map[string]interface{}, error)
}

// OrderServiceInterface 订单服务接口
type OrderServiceInterface interface {
	CreateOrder(ctx interface{}, req *CreateOrderRequest) (*Order, error)
	GetOrder(ctx interface{}, orderID string) (*Order, error)
	CancelOrder(ctx interface{}, orderID string) error
}

// PaymentServiceInterface 支付服务接口
type PaymentServiceInterface interface {
	ProcessPayment(ctx interface{}, req *PaymentRequest) (*Payment, error)
	GetPayment(ctx interface{}, paymentID string) (*Payment, error)
}

// 配置结构定义

// OTLPConfig OpenTelemetry 配置
type OTLPConfig struct {
	Endpoint       string  `env:"OTEL_ENDPOINT" default:"localhost:4317"`
	Insecure       bool    `env:"OTEL_INSECURE" default:"true"`
	SamplingRate   float64 `env:"SAMPLING_RATE" default:"0.1"`
	ServiceName    string  `env:"SERVICE_NAME" default:"microservices-demo"`
	ServiceVersion string  `env:"SERVICE_VERSION" default:"1.0.0"`
	Environment    string  `env:"ENVIRONMENT" default:"dev"`
}

// ServiceConfig 服务配置
type ServiceConfig struct {
	Port         string        `env:"PORT" default:"8080"`
	ReadTimeout  time.Duration `env:"READ_TIMEOUT" default:"10s"`
	WriteTimeout time.Duration `env:"WRITE_TIMEOUT" default:"10s"`
	IdleTimeout  time.Duration `env:"IDLE_TIMEOUT" default:"60s"`
}

// 错误类型定义

// ServiceError 服务错误
type ServiceError struct {
	Code    string `json:"code"`
	Message string `json:"message"`
	Details string `json:"details,omitempty"`
}

func (e *ServiceError) Error() string {
	return e.Message
}

// 预定义错误
var (
	ErrUserNotFound       = &ServiceError{Code: "USER_NOT_FOUND", Message: "User not found"}
	ErrOrderNotFound      = &ServiceError{Code: "ORDER_NOT_FOUND", Message: "Order not found"}
	ErrPaymentFailed      = &ServiceError{Code: "PAYMENT_FAILED", Message: "Payment processing failed"}
	ErrInvalidRequest     = &ServiceError{Code: "INVALID_REQUEST", Message: "Invalid request"}
	ErrServiceUnavailable = &ServiceError{Code: "SERVICE_UNAVAILABLE", Message: "Service unavailable"}
)

// 健康检查结构

// HealthStatus 健康状态
type HealthStatus struct {
	Status   string            `json:"status"`
	Time     time.Time         `json:"time"`
	Services map[string]string `json:"services,omitempty"`
	Version  string            `json:"version,omitempty"`
	Uptime   time.Duration     `json:"uptime,omitempty"`
}

// 常量定义

const (
	// 订单状态
	OrderStatusPending   = "pending"
	OrderStatusConfirmed = "confirmed"
	OrderStatusCancelled = "cancelled"
	OrderStatusCompleted = "completed"

	// 支付状态
	PaymentStatusPending    = "pending"
	PaymentStatusProcessing = "processing"
	PaymentStatusCompleted  = "completed"
	PaymentStatusFailed     = "failed"
	PaymentStatusCancelled  = "cancelled"

	// 用户等级
	UserLevelNormal  = "normal"
	UserLevelVIP     = "vip"
	UserLevelPremium = "premium"

	// 支付方式
	PaymentMethodCreditCard   = "credit_card"
	PaymentMethodPayPal       = "paypal"
	PaymentMethodBankTransfer = "bank_transfer"
)

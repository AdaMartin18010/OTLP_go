# 41. 实战案例：API Gateway 与完整服务集成

## 📚 目录

- [1. API Gateway 架构](#1-api-gateway-架构)
- [2. 中间件实现](#2-中间件实现)
- [3. 路由配置](#3-路由配置)
- [4. 服务集成](#4-服务集成)
- [5. 负载均衡与熔断](#5-负载均衡与熔断)
- [6. Docker Compose 部署](#6-docker-compose-部署)
- [7. 测试与监控](#7-测试与监控)
- [8. 总结](#8-总结)

---

## 1. API Gateway 架构

### 1.1 职责

- **统一入口**: 所有客户端请求的单一入口
- **路由转发**: 将请求路由到对应的后端服务
- **认证授权**: JWT 令牌验证和权限检查
- **限流熔断**: 保护后端服务
- **日志追踪**: 完整的请求链路追踪
- **协议转换**: HTTP → gRPC

### 1.2 技术选型

- **Web 框架**: Gin
- **服务发现**: Consul / etcd（本示例使用静态配置）
- **限流**: golang.org/x/time/rate
- **熔断**: sony/gobreaker
- **追踪**: OpenTelemetry

---

## 2. 中间件实现

### 2.1 OTLP 追踪中间件

```go
package middleware

import (
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/metric"
    "go.opentelemetry.io/otel/trace"
)

// TracingMiddleware OTLP 追踪中间件
func TracingMiddleware() gin.HandlerFunc {
    return otelgin.Middleware("api-gateway",
        otelgin.WithSpanNameFormatter(func(r *http.Request) string {
            return r.Method + " " + r.URL.Path
        }),
    )
}

// MetricsMiddleware 指标中间件
func MetricsMiddleware(meter metric.Meter) gin.HandlerFunc {
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("HTTP server requests"),
    )
    
    requestDuration, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP server request duration"),
        metric.WithUnit("ms"),
    )
    
    return func(c *gin.Context) {
        start := time.Now()
        
        c.Next()
        
        duration := time.Since(start)
        
        attrs := []attribute.KeyValue{
            attribute.String("http.method", c.Request.Method),
            attribute.String("http.route", c.FullPath()),
            attribute.Int("http.status_code", c.Writer.Status()),
        }
        
        requestCounter.Add(c.Request.Context(), 1, metric.WithAttributes(attrs...))
        requestDuration.Record(c.Request.Context(), float64(duration.Milliseconds()), metric.WithAttributes(attrs...))
    }
}
```

### 2.2 JWT 认证中间件

```go
package middleware

import (
    "net/http"
    "strings"
    
    "github.com/gin-gonic/gin"
    "github.com/golang-jwt/jwt/v5"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// JWTAuthMiddleware JWT 认证中间件
func JWTAuthMiddleware(secretKey string) gin.HandlerFunc {
    tracer := otel.Tracer("jwt-auth")
    
    return func(c *gin.Context) {
        ctx, span := tracer.Start(c.Request.Context(), "jwt.authenticate")
        defer span.End()
        
        // 从 Header 获取 Token
        authHeader := c.GetHeader("Authorization")
        if authHeader == "" {
            span.SetStatus(codes.Error, "missing authorization header")
            c.JSON(http.StatusUnauthorized, gin.H{"error": "missing authorization header"})
            c.Abort()
            return
        }
        
        // 检查格式
        parts := strings.SplitN(authHeader, " ", 2)
        if len(parts) != 2 || parts[0] != "Bearer" {
            span.SetStatus(codes.Error, "invalid authorization header format")
            c.JSON(http.StatusUnauthorized, gin.H{"error": "invalid authorization header format"})
            c.Abort()
            return
        }
        
        tokenString := parts[1]
        
        // 解析 Token
        token, err := jwt.Parse(tokenString, func(token *jwt.Token) (interface{}, error) {
            if _, ok := token.Method.(*jwt.SigningMethodHMAC); !ok {
                return nil, fmt.Errorf("unexpected signing method: %v", token.Header["alg"])
            }
            return []byte(secretKey), nil
        })
        
        if err != nil || !token.Valid {
            span.RecordError(err)
            span.SetStatus(codes.Error, "invalid token")
            c.JSON(http.StatusUnauthorized, gin.H{"error": "invalid token"})
            c.Abort()
            return
        }
        
        // 提取 Claims
        claims, ok := token.Claims.(jwt.MapClaims)
        if !ok {
            span.SetStatus(codes.Error, "invalid token claims")
            c.JSON(http.StatusUnauthorized, gin.H{"error": "invalid token claims"})
            c.Abort()
            return
        }
        
        userID, ok := claims["user_id"].(string)
        if !ok {
            span.SetStatus(codes.Error, "missing user_id in token")
            c.JSON(http.StatusUnauthorized, gin.H{"error": "invalid token"})
            c.Abort()
            return
        }
        
        // 设置用户信息到 Context
        c.Set("user_id", userID)
        
        span.SetAttributes(attribute.String("user.id", userID))
        span.SetStatus(codes.Ok, "")
        
        c.Request = c.Request.WithContext(ctx)
        c.Next()
    }
}
```

### 2.3 限流中间件

```go
package middleware

import (
    "net/http"
    
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/metric"
    "golang.org/x/time/rate"
)

// RateLimiter 限流器
type RateLimiter struct {
    limiter *rate.Limiter
    tracer  trace.Tracer
    meter   metric.Meter
    
    rejectedCounter metric.Int64Counter
}

// NewRateLimiter 创建限流器
func NewRateLimiter(requestsPerSecond int) (*RateLimiter, error) {
    tracer := otel.Tracer("rate-limiter")
    meter := otel.Meter("rate-limiter")
    
    rl := &RateLimiter{
        limiter: rate.NewLimiter(rate.Limit(requestsPerSecond), requestsPerSecond*2),
        tracer:  tracer,
        meter:   meter,
    }
    
    var err error
    rl.rejectedCounter, err = meter.Int64Counter(
        "rate_limiter.rejected.count",
        metric.WithDescription("Rate limiter rejected requests"),
    )
    if err != nil {
        return nil, err
    }
    
    return rl, nil
}

// Middleware 限流中间件
func (rl *RateLimiter) Middleware() gin.HandlerFunc {
    return func(c *gin.Context) {
        ctx, span := rl.tracer.Start(c.Request.Context(), "rate_limiter.check")
        defer span.End()
        
        if !rl.limiter.Allow() {
            span.SetStatus(codes.Error, "rate limit exceeded")
            rl.rejectedCounter.Add(ctx, 1)
            
            c.JSON(http.StatusTooManyRequests, gin.H{
                "error": "rate limit exceeded",
            })
            c.Abort()
            return
        }
        
        span.SetStatus(codes.Ok, "")
        c.Request = c.Request.WithContext(ctx)
        c.Next()
    }
}
```

### 2.4 熔断中间件

```go
package middleware

import (
    "net/http"
    "time"
    
    "github.com/gin-gonic/gin"
    "github.com/sony/gobreaker"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/metric"
)

// CircuitBreaker 熔断器
type CircuitBreaker struct {
    breaker *gobreaker.CircuitBreaker
    tracer  trace.Tracer
    meter   metric.Meter
    
    stateGauge metric.Int64ObservableGauge
    openCounter metric.Int64Counter
}

// NewCircuitBreaker 创建熔断器
func NewCircuitBreaker(name string) (*CircuitBreaker, error) {
    tracer := otel.Tracer("circuit-breaker")
    meter := otel.Meter("circuit-breaker")
    
    cb := &CircuitBreaker{
        tracer: tracer,
        meter:  meter,
    }
    
    settings := gobreaker.Settings{
        Name:        name,
        MaxRequests: 3,
        Interval:    time.Minute,
        Timeout:     10 * time.Second,
        ReadyToTrip: func(counts gobreaker.Counts) bool {
            failureRatio := float64(counts.TotalFailures) / float64(counts.Requests)
            return counts.Requests >= 3 && failureRatio >= 0.6
        },
        OnStateChange: func(name string, from gobreaker.State, to gobreaker.State) {
            if to == gobreaker.StateOpen {
                cb.openCounter.Add(context.Background(), 1)
            }
        },
    }
    
    cb.breaker = gobreaker.NewCircuitBreaker(settings)
    
    var err error
    
    // 熔断器状态
    cb.stateGauge, err = meter.Int64ObservableGauge(
        "circuit_breaker.state",
        metric.WithDescription("Circuit breaker state (0=closed, 1=half-open, 2=open)"),
        metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
            state := cb.breaker.State()
            observer.Observe(int64(state),
                metric.WithAttributes(attribute.String("name", name)),
            )
            return nil
        }),
    )
    if err != nil {
        return nil, err
    }
    
    // 熔断次数
    cb.openCounter, err = meter.Int64Counter(
        "circuit_breaker.open.count",
        metric.WithDescription("Circuit breaker opened count"),
    )
    if err != nil {
        return nil, err
    }
    
    return cb, nil
}

// Middleware 熔断中间件
func (cb *CircuitBreaker) Middleware() gin.HandlerFunc {
    return func(c *gin.Context) {
        ctx, span := cb.tracer.Start(c.Request.Context(), "circuit_breaker.check")
        defer span.End()
        
        _, err := cb.breaker.Execute(func() (interface{}, error) {
            c.Next()
            
            // 根据状态码判断是否失败
            if c.Writer.Status() >= 500 {
                return nil, fmt.Errorf("server error: %d", c.Writer.Status())
            }
            
            return nil, nil
        })
        
        if err != nil {
            if err == gobreaker.ErrOpenState {
                span.SetStatus(codes.Error, "circuit breaker open")
                c.JSON(http.StatusServiceUnavailable, gin.H{
                    "error": "service temporarily unavailable",
                })
                c.Abort()
                return
            }
            
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
        } else {
            span.SetStatus(codes.Ok, "")
        }
        
        c.Request = c.Request.WithContext(ctx)
    }
}
```

---

## 3. 路由配置

### 3.1 API Gateway 主程序

```go
package main

import (
    "context"
    "log"
    "net/http"
    "os"
    "os/signal"
    "syscall"
    "time"
    
    "github.com/gin-gonic/gin"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/propagation"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

func main() {
    // 初始化 OTLP
    ctx := context.Background()
    
    shutdown, err := initOTLP(ctx)
    if err != nil {
        log.Fatalf("Failed to initialize OTLP: %v", err)
    }
    defer shutdown(ctx)
    
    // 创建 Gin 引擎
    r := gin.New()
    
    // 全局中间件
    r.Use(gin.Recovery())
    r.Use(middleware.TracingMiddleware())
    r.Use(middleware.MetricsMiddleware(otel.Meter("api-gateway")))
    
    // 限流中间件
    rateLimiter, _ := middleware.NewRateLimiter(100) // 100 req/s
    r.Use(rateLimiter.Middleware())
    
    // 健康检查（无需认证）
    r.GET("/health", healthCheck)
    r.GET("/ready", readyCheck)
    
    // 公开 API（无需认证）
    public := r.Group("/api/v1")
    {
        // 用户相关
        public.POST("/users/register", registerHandler)
        public.POST("/users/login", loginHandler)
        
        // 商品相关
        public.GET("/products", listProductsHandler)
        public.GET("/products/:id", getProductHandler)
    }
    
    // 需要认证的 API
    secretKey := os.Getenv("JWT_SECRET_KEY")
    if secretKey == "" {
        secretKey = "your-secret-key"
    }
    
    authenticated := r.Group("/api/v1")
    authenticated.Use(middleware.JWTAuthMiddleware(secretKey))
    {
        // 用户相关
        authenticated.GET("/users/me", getUserProfileHandler)
        
        // 订单相关
        authenticated.POST("/orders", createOrderHandler)
        authenticated.GET("/orders/:id", getOrderHandler)
        authenticated.GET("/orders", listOrdersHandler)
        
        // 支付相关
        authenticated.POST("/payments", processPaymentHandler)
    }
    
    // 启动服务器
    srv := &http.Server{
        Addr:    ":8080",
        Handler: r,
    }
    
    // 优雅关闭
    go func() {
        if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
            log.Fatalf("Server failed: %v", err)
        }
    }()
    
    log.Println("API Gateway started on :8080")
    
    // 等待中断信号
    quit := make(chan os.Signal, 1)
    signal.Notify(quit, os.Interrupt, syscall.SIGTERM)
    <-quit
    
    log.Println("Shutting down server...")
    
    ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
    defer cancel()
    
    if err := srv.Shutdown(ctx); err != nil {
        log.Printf("Server forced to shutdown: %v", err)
    }
    
    log.Println("Server exited")
}

// initOTLP 初始化 OpenTelemetry
func initOTLP(ctx context.Context) (func(context.Context) error, error) {
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("api-gateway"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }
    
    // Trace Exporter
    traceExporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // Trace Provider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(traceExporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.ParentBased(sdktrace.TraceIDRatioBased(1.0))),
    )
    otel.SetTracerProvider(tp)
    
    // Metric Exporter
    metricExporter, err := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithEndpoint("localhost:4317"),
        otlpmetricgrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // Metric Provider
    mp := metric.NewMeterProvider(
        metric.WithReader(metric.NewPeriodicReader(metricExporter)),
        metric.WithResource(res),
    )
    otel.SetMeterProvider(mp)
    
    // Propagator
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    
    return func(ctx context.Context) error {
        if err := tp.Shutdown(ctx); err != nil {
            return err
        }
        if err := mp.Shutdown(ctx); err != nil {
            return err
        }
        return nil
    }, nil
}

// healthCheck 健康检查
func healthCheck(c *gin.Context) {
    c.JSON(http.StatusOK, gin.H{
        "status": "healthy",
        "timestamp": time.Now().Unix(),
    })
}

// readyCheck 就绪检查
func readyCheck(c *gin.Context) {
    // 这里可以检查依赖服务的健康状态
    c.JSON(http.StatusOK, gin.H{
        "status": "ready",
        "timestamp": time.Now().Unix(),
    })
}
```

---

## 4. 服务集成

### 4.1 gRPC 客户端封装

```go
package client

import (
    "context"
    "time"
    
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
    "google.golang.org/grpc/credentials/insecure"
)

// NewGRPCClient 创建 gRPC 客户端
func NewGRPCClient(target string) (*grpc.ClientConn, error) {
    ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
    defer cancel()
    
    conn, err := grpc.DialContext(ctx, target,
        grpc.WithTransportCredentials(insecure.NewCredentials()),
        grpc.WithStatsHandler(otelgrpc.NewClientHandler()),
        grpc.WithDefaultCallOptions(
            grpc.WaitForReady(true),
        ),
    )
    
    if err != nil {
        return nil, err
    }
    
    return conn, nil
}

// 服务客户端管理
type ServiceClients struct {
    UserClient      userpb.UserServiceClient
    ProductClient   productpb.ProductServiceClient
    OrderClient     orderpb.OrderServiceClient
    PaymentClient   paymentpb.PaymentServiceClient
    InventoryClient inventorypb.InventoryServiceClient
}

// NewServiceClients 创建所有服务客户端
func NewServiceClients() (*ServiceClients, error) {
    // 用户服务
    userConn, err := NewGRPCClient("localhost:9001")
    if err != nil {
        return nil, err
    }
    
    // 商品服务
    productConn, err := NewGRPCClient("localhost:9002")
    if err != nil {
        return nil, err
    }
    
    // 订单服务
    orderConn, err := NewGRPCClient("localhost:9003")
    if err != nil {
        return nil, err
    }
    
    // 支付服务
    paymentConn, err := NewGRPCClient("localhost:9004")
    if err != nil {
        return nil, err
    }
    
    // 库存服务
    inventoryConn, err := NewGRPCClient("localhost:9005")
    if err != nil {
        return nil, err
    }
    
    return &ServiceClients{
        UserClient:      userpb.NewUserServiceClient(userConn),
        ProductClient:   productpb.NewProductServiceClient(productConn),
        OrderClient:     orderpb.NewOrderServiceClient(orderConn),
        PaymentClient:   paymentpb.NewPaymentServiceClient(paymentConn),
        InventoryClient: inventorypb.NewInventoryServiceClient(inventoryConn),
    }, nil
}
```

### 4.2 Handler 实现示例

```go
package handler

import (
    "net/http"
    
    "github.com/gin-gonic/gin"
    "github.com/google/uuid"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

var (
    serviceClients *client.ServiceClients
    tracer         = otel.Tracer("api-handlers")
)

// InitHandlers 初始化 Handlers
func InitHandlers(clients *client.ServiceClients) {
    serviceClients = clients
}

// createOrderHandler 创建订单
func createOrderHandler(c *gin.Context) {
    ctx, span := tracer.Start(c.Request.Context(), "handler.create_order")
    defer span.End()
    
    // 获取用户 ID
    userID, _ := c.Get("user_id")
    userIDStr := userID.(string)
    
    span.SetAttributes(attribute.String("user.id", userIDStr))
    
    // 解析请求
    var req CreateOrderRequest
    if err := c.ShouldBindJSON(&req); err != nil {
        span.RecordError(err)
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }
    
    // 调用订单服务
    orderResp, err := serviceClients.OrderClient.CreateOrder(ctx, &orderpb.CreateOrderRequest{
        UserId:        userIDStr,
        Items:         convertOrderItems(req.Items),
        PaymentMethod: req.PaymentMethod,
    })
    
    if err != nil {
        span.RecordError(err)
        c.JSON(http.StatusInternalServerError, gin.H{"error": "failed to create order"})
        return
    }
    
    span.SetAttributes(attribute.String("order.id", orderResp.OrderId))
    
    c.JSON(http.StatusCreated, gin.H{
        "order_id": orderResp.OrderId,
        "status":   orderResp.Status,
    })
}

// getOrderHandler 获取订单
func getOrderHandler(c *gin.Context) {
    ctx, span := tracer.Start(c.Request.Context(), "handler.get_order")
    defer span.End()
    
    orderID := c.Param("id")
    span.SetAttributes(attribute.String("order.id", orderID))
    
    // 验证权限（确保订单属于当前用户）
    userID, _ := c.Get("user_id")
    
    orderResp, err := serviceClients.OrderClient.GetOrder(ctx, &orderpb.GetOrderRequest{
        OrderId: orderID,
        UserId:  userID.(string),
    })
    
    if err != nil {
        span.RecordError(err)
        c.JSON(http.StatusNotFound, gin.H{"error": "order not found"})
        return
    }
    
    c.JSON(http.StatusOK, orderResp)
}

// listProductsHandler 列出商品
func listProductsHandler(c *gin.Context) {
    ctx, span := tracer.Start(c.Request.Context(), "handler.list_products")
    defer span.End()
    
    // 解析查询参数
    var req ListProductsRequest
    if err := c.ShouldBindQuery(&req); err != nil {
        span.RecordError(err)
        c.JSON(http.StatusBadRequest, gin.H{"error": err.Error()})
        return
    }
    
    span.SetAttributes(
        attribute.Int("page", req.Page),
        attribute.Int("page_size", req.PageSize),
    )
    
    // 调用商品服务
    productsResp, err := serviceClients.ProductClient.ListProducts(ctx, &productpb.ListProductsRequest{
        Page:     int32(req.Page),
        PageSize: int32(req.PageSize),
        Category: req.Category,
    })
    
    if err != nil {
        span.RecordError(err)
        c.JSON(http.StatusInternalServerError, gin.H{"error": "failed to list products"})
        return
    }
    
    c.JSON(http.StatusOK, productsResp)
}

// Request/Response 类型
type CreateOrderRequest struct {
    Items         []OrderItem `json:"items" binding:"required,min=1"`
    PaymentMethod string      `json:"payment_method" binding:"required"`
}

type OrderItem struct {
    ProductID string `json:"product_id" binding:"required"`
    Quantity  int    `json:"quantity" binding:"required,min=1"`
}

type ListProductsRequest struct {
    Page     int    `form:"page" binding:"required,min=1"`
    PageSize int    `form:"page_size" binding:"required,min=1,max=100"`
    Category string `form:"category"`
}
```

---

## 5. 负载均衡与熔断

### 5.1 gRPC 负载均衡

```go
// 使用 gRPC 内置的负载均衡
conn, err := grpc.DialContext(ctx, "dns:///product-service:9002",
    grpc.WithDefaultServiceConfig(`{"loadBalancingPolicy":"round_robin"}`),
    // ... 其他选项
)
```

### 5.2 服务健康检查

```go
package health

import (
    "context"
    "time"
    
    "google.golang.org/grpc/health/grpc_health_v1"
)

// CheckServiceHealth 检查服务健康
func CheckServiceHealth(client grpc_health_v1.HealthClient) error {
    ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
    defer cancel()
    
    resp, err := client.Check(ctx, &grpc_health_v1.HealthCheckRequest{
        Service: "",
    })
    
    if err != nil {
        return err
    }
    
    if resp.Status != grpc_health_v1.HealthCheckResponse_SERVING {
        return fmt.Errorf("service not healthy: %v", resp.Status)
    }
    
    return nil
}
```

---

## 6. Docker Compose 部署

### 6.1 docker-compose.yml

```yaml
version: '3.8'

services:
  # API Gateway
  api-gateway:
    build:
      context: .
      dockerfile: Dockerfile.gateway
    ports:
      - "8080:8080"
    environment:
      - JWT_SECRET_KEY=your-secret-key
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - user-service
      - product-service
      - order-service
      - payment-service
      - inventory-service
      - otel-collector
    networks:
      - ecommerce-network
    restart: unless-stopped

  # User Service
  user-service:
    build:
      context: .
      dockerfile: Dockerfile.user
    ports:
      - "9001:9001"
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/users?sslmode=disable
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - otel-collector
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Product Service
  product-service:
    build:
      context: .
      dockerfile: Dockerfile.product
    ports:
      - "9002:9002"
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/products?sslmode=disable
      - REDIS_URL=redis:6379
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - redis
      - otel-collector
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Order Service
  order-service:
    build:
      context: .
      dockerfile: Dockerfile.order
    ports:
      - "9003:9003"
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/orders?sslmode=disable
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - otel-collector
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Payment Service
  payment-service:
    build:
      context: .
      dockerfile: Dockerfile.payment
    ports:
      - "9004:9004"
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/payments?sslmode=disable
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - otel-collector
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Inventory Service
  inventory-service:
    build:
      context: .
      dockerfile: Dockerfile.inventory
    ports:
      - "9005:9005"
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/inventory?sslmode=disable
      - OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317
    depends_on:
      - postgres
      - otel-collector
    networks:
      - ecommerce-network
    restart: unless-stopped

  # PostgreSQL
  postgres:
    image: postgres:16-alpine
    ports:
      - "5432:5432"
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
      - POSTGRES_MULTIPLE_DATABASES=users,products,orders,payments,inventory
    volumes:
      - postgres-data:/var/lib/postgresql/data
      - ./scripts/init-databases.sh:/docker-entrypoint-initdb.d/init-databases.sh
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Redis
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    networks:
      - ecommerce-network
    restart: unless-stopped

  # OTLP Collector
  otel-collector:
    image: otel/opentelemetry-collector-contrib:latest
    command: ["--config=/etc/otel-collector-config.yaml"]
    ports:
      - "4317:4317"   # OTLP gRPC
      - "4318:4318"   # OTLP HTTP
      - "8888:8888"   # Prometheus metrics
    volumes:
      - ./configs/otel-collector-config.yaml:/etc/otel-collector-config.yaml
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Jaeger
  jaeger:
    image: jaegertracing/all-in-one:latest
    ports:
      - "16686:16686"  # Jaeger UI
      - "14268:14268"  # Jaeger collector
    environment:
      - COLLECTOR_OTLP_ENABLED=true
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Prometheus
  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./configs/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
    networks:
      - ecommerce-network
    restart: unless-stopped

  # Grafana
  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_USER=admin
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - ./configs/grafana-datasources.yml:/etc/grafana/provisioning/datasources/datasources.yml
      - grafana-data:/var/lib/grafana
    networks:
      - ecommerce-network
    restart: unless-stopped

volumes:
  postgres-data:
  redis-data:
  prometheus-data:
  grafana-data:

networks:
  ecommerce-network:
    driver: bridge
```

---

## 7. 测试与监控

### 7.1 集成测试脚本

```bash
#!/bin/bash

# test-e2e.sh

BASE_URL="http://localhost:8080/api/v1"

echo "=== E2E Testing ==="

# 1. 注册用户
echo "1. Registering user..."
REGISTER_RESP=$(curl -s -X POST "$BASE_URL/users/register" \
  -H "Content-Type: application/json" \
  -d '{
    "email": "test@example.com",
    "username": "testuser",
    "password": "password123",
    "full_name": "Test User",
    "phone": "1234567890"
  }')

echo "Register response: $REGISTER_RESP"

# 2. 登录
echo "2. Logging in..."
LOGIN_RESP=$(curl -s -X POST "$BASE_URL/users/login" \
  -H "Content-Type: application/json" \
  -d '{
    "email": "test@example.com",
    "password": "password123"
  }')

TOKEN=$(echo $LOGIN_RESP | jq -r '.token')
echo "Token: $TOKEN"

# 3. 查询商品
echo "3. Listing products..."
PRODUCTS_RESP=$(curl -s "$BASE_URL/products?page=1&page_size=10")
echo "Products: $PRODUCTS_RESP"

PRODUCT_ID=$(echo $PRODUCTS_RESP | jq -r '.products[0].id')
echo "First product ID: $PRODUCT_ID"

# 4. 创建订单
echo "4. Creating order..."
ORDER_RESP=$(curl -s -X POST "$BASE_URL/orders" \
  -H "Authorization: Bearer $TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "items": [
      {
        "product_id": "'$PRODUCT_ID'",
        "quantity": 2
      }
    ],
    "payment_method": "credit_card"
  }')

echo "Order response: $ORDER_RESP"
ORDER_ID=$(echo $ORDER_RESP | jq -r '.order_id')

# 5. 查询订单
echo "5. Getting order..."
GET_ORDER_RESP=$(curl -s "$BASE_URL/orders/$ORDER_ID" \
  -H "Authorization: Bearer $TOKEN")

echo "Get order response: $GET_ORDER_RESP"

echo "=== Testing Complete ==="
```

### 7.2 监控面板

访问：
- **Jaeger UI**: http://localhost:16686
- **Prometheus**: http://localhost:9090
- **Grafana**: http://localhost:3000 (admin/admin)

---

## 8. 总结

本文档展示了完整的 API Gateway 实现和微服务集成方案，包括：

### 核心特性

✅ **完整的中间件栈**
- 追踪：OpenTelemetry 自动插桩
- 指标：请求计数、延迟、成功率
- 认证：JWT 令牌验证
- 限流：基于令牌桶算法
- 熔断：自动故障保护

✅ **服务集成**
- gRPC 客户端管理
- 自动负载均衡
- 健康检查
- 超时控制

✅ **生产就绪**
- Docker Compose 一键部署
- 完整的可观测性栈
- 优雅关闭
- E2E 测试

### 相关文档

- [39_实战案例_电商微服务系统](./39_实战案例_电商微服务系统.md)
- [40_实战案例_订单支付库存集成](./40_实战案例_订单支付库存集成.md)
- [35_Go生产级部署模式与反模式](./35_Go生产级部署模式与反模式.md)
- [36_Go微服务间通信与分布式追踪](./36_Go微服务间通信与分布式追踪.md)


# 分布式追踪实现

## 目录

- [分布式追踪实现](#分布式追踪实现)
  - [目录](#目录)
  - [1. 完整微服务示例](#1-完整微服务示例)
    - [1.1 系统架构](#11-系统架构)
    - [1.2 API Gateway](#12-api-gateway)
    - [1.3 订单服务](#13-订单服务)
    - [1.4 库存服务](#14-库存服务)
    - [1.5 支付服务](#15-支付服务)
  - [2. CSP 模式应用](#2-csp-模式应用)
    - [2.1 Pipeline 模式](#21-pipeline-模式)
    - [2.2 Fan-Out/Fan-In 模式](#22-fan-outfan-in-模式)
  - [3. OTLP 插桩实践](#3-otlp-插桩实践)
    - [3.1 自动插桩](#31-自动插桩)
    - [3.2 手动插桩最佳实践](#32-手动插桩最佳实践)
  - [4. 性能分析与调优](#4-性能分析与调优)
    - [4.1 识别慢请求](#41-识别慢请求)
    - [4.2 优化策略](#42-优化策略)
  - [5. 故障排查案例](#5-故障排查案例)
    - [5.1 案例：订单创建失败](#51-案例订单创建失败)
  - [6. 参考资料](#6-参考资料)

## 1. 完整微服务示例

### 1.1 系统架构

```text
┌─────────┐      ┌──────────┐      ┌─────────┐      ┌─────────┐
│ API     │─────>│ Order    │─────>│Inventory│      │ Payment │
│ Gateway │      │ Service  │      │ Service │      │ Service │
└─────────┘      └──────────┘      └─────────┘      └─────────┘
     │                │                  │                │
     └────────────────┴──────────────────┴────────────────┘
                           │
                    ┌──────▼──────┐
                    │ OTLP        │
                    │ Collector   │
                    └──────┬──────┘
                           │
                    ┌──────▼──────┐
                    │ Jaeger /    │
                    │ Tempo       │
                    └─────────────┘
```

### 1.2 API Gateway

```go
package main

import (
    "context"
    "net/http"
    
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

var tracer = otel.Tracer("api-gateway")

type APIGateway struct {
    orderClient *OrderClient
}

func (gw *APIGateway) HandleCreateOrder(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    ctx, span := tracer.Start(ctx, "api_gateway.create_order")
    defer span.End()
    
    // 解析请求
    var req CreateOrderRequest
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "invalid request")
        http.Error(w, err.Error(), http.StatusBadRequest)
        return
    }
    
    span.SetAttributes(
        attribute.String("user.id", req.UserID),
        attribute.Int("items.count", len(req.Items)),
        attribute.String("request.id", req.RequestID),
    )
    
    // 调用订单服务
    order, err := gw.orderClient.CreateOrder(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "order creation failed")
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
        attribute.String("order.status", order.Status),
    )
    span.SetStatus(codes.Ok, "order created successfully")
    
    // 返回响应
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(order)
}

func main() {
    // 初始化 OTLP
    shutdown := initTracer()
    defer shutdown()
    
    gateway := &APIGateway{
        orderClient: NewOrderClient("http://order-service:8080"),
    }
    
    // 使用 otelhttp middleware
    handler := otelhttp.NewHandler(
        http.HandlerFunc(gateway.HandleCreateOrder),
        "create_order",
    )
    
    http.Handle("/api/orders", handler)
    http.ListenAndServe(":8080", nil)
}
```

### 1.3 订单服务

```go
package main

import (
    "context"
    "fmt"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

var tracer = otel.Tracer("order-service")

type OrderService struct {
    inventoryClient *InventoryClient
    paymentClient   *PaymentClient
    db              *Database
}

func (os *OrderService) CreateOrder(ctx context.Context, req CreateOrderRequest) (*Order, error) {
    ctx, span := tracer.Start(ctx, "order_service.create_order")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("user.id", req.UserID),
        attribute.Int("items.count", len(req.Items)),
    )
    
    // 1. 验证库存
    if err := os.checkInventory(ctx, req.Items); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "inventory check failed")
        return nil, err
    }
    
    // 2. 创建订单记录
    order, err := os.createOrderRecord(ctx, req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "order creation failed")
        return nil, err
    }
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
    )
    
    // 3. 预留库存
    if err := os.reserveInventory(ctx, order); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "inventory reservation failed")
        
        // 回滚订单
        os.cancelOrder(ctx, order.ID)
        return nil, err
    }
    
    // 4. 创建支付
    payment, err := os.createPayment(ctx, order)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "payment creation failed")
        
        // 回滚库存和订单
        os.releaseInventory(ctx, order)
        os.cancelOrder(ctx, order.ID)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.String("payment.id", payment.ID),
    )
    
    // 5. 更新订单状态
    order.Status = "pending_payment"
    order.PaymentID = payment.ID
    
    if err := os.db.UpdateOrder(ctx, order); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "order update failed")
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "order created successfully")
    span.AddEvent("order_created", attribute.String("order.id", order.ID))
    
    return order, nil
}

func (os *OrderService) checkInventory(ctx context.Context, items []Item) error {
    ctx, span := tracer.Start(ctx, "check_inventory")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("items.count", len(items)),
    )
    
    resp, err := os.inventoryClient.CheckAvailability(ctx, items)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    if !resp.Available {
        err := fmt.Errorf("insufficient inventory")
        span.RecordError(err)
        span.SetAttributes(
            attribute.StringSlice("unavailable.items", resp.UnavailableItems),
        )
        return err
    }
    
    span.SetStatus(codes.Ok, "inventory available")
    return nil
}

func (os *OrderService) createOrderRecord(ctx context.Context, req CreateOrderRequest) (*Order, error) {
    ctx, span := tracer.Start(ctx, "create_order_record")
    defer span.End()
    
    order := &Order{
        ID:          generateOrderID(),
        UserID:      req.UserID,
        Items:       req.Items,
        TotalAmount: calculateTotal(req.Items),
        Status:      "created",
        CreatedAt:   time.Now(),
    }
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
        attribute.Float64("order.total", order.TotalAmount),
    )
    
    if err := os.db.InsertOrder(ctx, order); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "order record created")
    return order, nil
}

func (os *OrderService) reserveInventory(ctx context.Context, order *Order) error {
    ctx, span := tracer.Start(ctx, "reserve_inventory")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
    )
    
    if err := os.inventoryClient.Reserve(ctx, order.ID, order.Items); err != nil {
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "inventory reserved")
    return nil
}

func (os *OrderService) createPayment(ctx context.Context, order *Order) (*Payment, error) {
    ctx, span := tracer.Start(ctx, "create_payment")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
        attribute.Float64("amount", order.TotalAmount),
    )
    
    payment, err := os.paymentClient.CreatePayment(ctx, PaymentRequest{
        OrderID: order.ID,
        Amount:  order.TotalAmount,
        UserID:  order.UserID,
    })
    
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.String("payment.id", payment.ID),
    )
    span.SetStatus(codes.Ok, "payment created")
    
    return payment, nil
}
```

### 1.4 库存服务

```go
package main

import (
    "context"
    "sync"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

var tracer = otel.Tracer("inventory-service")

type InventoryService struct {
    inventory map[string]int
    reserved  map[string]map[string]int  // orderID -> itemID -> quantity
    mu        sync.RWMutex
}

func (is *InventoryService) CheckAvailability(ctx context.Context, items []Item) (*AvailabilityResponse, error) {
    ctx, span := tracer.Start(ctx, "inventory.check_availability")
    defer span.End()
    
    is.mu.RLock()
    defer is.mu.RUnlock()
    
    resp := &AvailabilityResponse{
        Available:        true,
        UnavailableItems: make([]string, 0),
    }
    
    for _, item := range items {
        available := is.inventory[item.ID]
        
        span.AddEvent("check_item", attribute.String("item.id", item.ID),
            attribute.Int("available", available),
            attribute.Int("requested", item.Quantity))
        
        if available < item.Quantity {
            resp.Available = false
            resp.UnavailableItems = append(resp.UnavailableItems, item.ID)
        }
    }
    
    span.SetAttributes(
        attribute.Bool("available", resp.Available),
        attribute.Int("unavailable.count", len(resp.UnavailableItems)),
    )
    
    return resp, nil
}

func (is *InventoryService) Reserve(ctx context.Context, orderID string, items []Item) error {
    ctx, span := tracer.Start(ctx, "inventory.reserve")
    defer span.End()
    
    is.mu.Lock()
    defer is.mu.Unlock()
    
    span.SetAttributes(
        attribute.String("order.id", orderID),
        attribute.Int("items.count", len(items)),
    )
    
    // 预留库存
    if is.reserved[orderID] == nil {
        is.reserved[orderID] = make(map[string]int)
    }
    
    for _, item := range items {
        is.inventory[item.ID] -= item.Quantity
        is.reserved[orderID][item.ID] = item.Quantity
        
        span.AddEvent("item_reserved",
            attribute.String("item.id", item.ID),
            attribute.Int("quantity", item.Quantity))
    }
    
    return nil
}
```

### 1.5 支付服务

```go
package main

import (
    "context"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

var tracer = otel.Tracer("payment-service")

type PaymentService struct {
    gateway *PaymentGateway
}

func (ps *PaymentService) CreatePayment(ctx context.Context, req PaymentRequest) (*Payment, error) {
    ctx, span := tracer.Start(ctx, "payment.create")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", req.OrderID),
        attribute.Float64("amount", req.Amount),
        attribute.String("user.id", req.UserID),
    )
    
    // 创建支付记录
    payment := &Payment{
        ID:      generatePaymentID(),
        OrderID: req.OrderID,
        Amount:  req.Amount,
        Status:  "pending",
    }
    
    // 调用支付网关
    if err := ps.gateway.Charge(ctx, payment); err != nil {
        span.RecordError(err)
        payment.Status = "failed"
        return payment, err
    }
    
    payment.Status = "completed"
    
    span.SetAttributes(
        attribute.String("payment.id", payment.ID),
        attribute.String("payment.status", payment.Status),
    )
    
    return payment, nil
}
```

## 2. CSP 模式应用

### 2.1 Pipeline 模式

```go
// CSP: STAGE1 -> STAGE2 -> STAGE3
func OrderProcessingPipeline(ctx context.Context, orders <-chan Order) <-chan OrderResult {
    // Stage 1: 验证
    validated := validateOrders(ctx, orders)
    
    // Stage 2: 处理
    processed := processOrders(ctx, validated)
    
    // Stage 3: 通知
    notified := notifyOrders(ctx, processed)
    
    return notified
}

func validateOrders(ctx context.Context, orders <-chan Order) <-chan Order {
    output := make(chan Order)
    
    go func() {
        defer close(output)
        
        for order := range orders {
            ctx, span := tracer.Start(ctx, "validate_order")
            span.SetAttributes(attribute.String("order.id", order.ID))
            
            if isValid(order) {
                select {
                case output <- order:
                case <-ctx.Done():
                    span.End()
                    return
                }
            }
            
            span.End()
        }
    }()
    
    return output
}
```

### 2.2 Fan-Out/Fan-In 模式

```go
// CSP: 并行处理多个订单项
func ProcessOrderItems(ctx context.Context, order Order) ([]ItemResult, error) {
    ctx, span := tracer.Start(ctx, "process_order_items")
    defer span.End()
    
    // Fan-out: 为每个订单项创建 goroutine
    results := make(chan ItemResult, len(order.Items))
    var wg sync.WaitGroup
    
    for _, item := range order.Items {
        wg.Add(1)
        go func(item Item) {
            defer wg.Done()
            
            ctx, span := tracer.Start(ctx, "process_item")
            span.SetAttributes(
                attribute.String("item.id", item.ID),
                attribute.String("order.id", order.ID),
            )
            defer span.End()
            
            result := processItem(ctx, item)
            
            select {
            case results <- result:
            case <-ctx.Done():
                return
            }
        }(item)
    }
    
    // Fan-in: 收集所有结果
    go func() {
        wg.Wait()
        close(results)
    }()
    
    // 聚合结果
    var allResults []ItemResult
    for result := range results {
        allResults = append(allResults, result)
    }
    
    return allResults, nil
}
```

## 3. OTLP 插桩实践

### 3.1 自动插桩

```go
import (
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"
)

// HTTP 自动插桩
httpClient := &http.Client{
    Transport: otelhttp.NewTransport(http.DefaultTransport),
}

// gRPC 自动插桩
conn, err := grpc.Dial(
    address,
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
    grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
)

// 数据库自动插桩
db, err := otelsql.Open("postgres", dsn,
    otelsql.WithAttributes(
        semconv.DBSystemPostgreSQL,
    ),
)
```

### 3.2 手动插桩最佳实践

```go
func ProcessOrder(ctx context.Context, order Order) error {
    // 1. 创建 Span
    ctx, span := tracer.Start(ctx, "process_order",
        trace.WithSpanKind(trace.SpanKindInternal),
        trace.WithAttributes(
            attribute.String("order.id", order.ID),
            attribute.String("user.id", order.UserID),
        ),
    )
    defer span.End()
    
    // 2. 记录关键事件
    span.AddEvent("validation_started")
    
    if err := validateOrder(order); err != nil {
        // 3. 记录错误
        span.RecordError(err)
        span.SetStatus(codes.Error, "validation failed")
        return err
    }
    
    span.AddEvent("validation_completed")
    
    // 4. 添加业务指标
    span.SetAttributes(
        attribute.Float64("order.total", order.TotalAmount),
        attribute.Int("order.items", len(order.Items)),
    )
    
    // 5. 处理业务逻辑
    if err := saveOrder(ctx, order); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "save failed")
        return err
    }
    
    // 6. 设置成功状态
    span.SetStatus(codes.Ok, "order processed")
    
    return nil
}
```

## 4. 性能分析与调优

### 4.1 识别慢请求

```go
// 使用 Jaeger 查询慢 Trace
// Query: duration > 1s

// 分析 Span 持续时间
func AnalyzeSlowTraces(traces []Trace) {
    for _, trace := range traces {
        totalDuration := trace.Duration()
        
        fmt.Printf("Trace %s: %v\n", trace.ID, totalDuration)
        
        // 找出最慢的 Span
        slowestSpan := findSlowestSpan(trace)
        fmt.Printf("  Slowest: %s (%v)\n", 
            slowestSpan.Name, 
            slowestSpan.Duration())
        
        // 计算每个 Span 的占比
        for _, span := range trace.Spans {
            percentage := float64(span.Duration()) / float64(totalDuration) * 100
            if percentage > 10 {
                fmt.Printf("  %s: %.1f%%\n", span.Name, percentage)
            }
        }
    }
}
```

### 4.2 优化策略

```go
// 优化前：顺序调用
func CreateOrderSlow(ctx context.Context, req CreateOrderRequest) (*Order, error) {
    // 1. 检查库存 (200ms)
    inventory, _ := checkInventory(ctx, req.Items)
    
    // 2. 验证用户 (150ms)
    user, _ := validateUser(ctx, req.UserID)
    
    // 3. 计算价格 (100ms)
    price, _ := calculatePrice(ctx, req.Items)
    
    // 总耗时: 450ms
    return createOrder(ctx, inventory, user, price)
}

// 优化后：并行调用
func CreateOrderFast(ctx context.Context, req CreateOrderRequest) (*Order, error) {
    ctx, span := tracer.Start(ctx, "create_order_fast")
    defer span.End()
    
    var (
        inventory InventoryResponse
        user      User
        price     float64
        wg        sync.WaitGroup
        errChan   = make(chan error, 3)
    )
    
    // 并行执行
    wg.Add(3)
    
    go func() {
        defer wg.Done()
        var err error
        inventory, err = checkInventory(ctx, req.Items)
        if err != nil {
            errChan <- err
        }
    }()
    
    go func() {
        defer wg.Done()
        var err error
        user, err = validateUser(ctx, req.UserID)
        if err != nil {
            errChan <- err
        }
    }()
    
    go func() {
        defer wg.Done()
        var err error
        price, err = calculatePrice(ctx, req.Items)
        if err != nil {
            errChan <- err
        }
    }()
    
    wg.Wait()
    close(errChan)
    
    // 检查错误
    if err := <-errChan; err != nil {
        return nil, err
    }
    
    // 总耗时: ~200ms (最慢的调用)
    return createOrder(ctx, inventory, user, price)
}
```

## 5. 故障排查案例

### 5.1 案例：订单创建失败

**问题**：用户报告订单创建失败率突然升高

**排查步骤**：

1. **查看 Trace**：

    ```text
    Trace ID: abc123
    Duration: 5.2s
    Status: ERROR

    Spans:
    ├── api_gateway.create_order (5.2s) ✓
    │   ├── order_service.create_order (5.1s) ✗
    │   │   ├── check_inventory (0.1s) ✓
    │   │   ├── create_order_record (0.2s) ✓
    │   │   ├── reserve_inventory (0.1s) ✓
    │   │   └── create_payment (4.7s) ✗ TIMEOUT
    ```

2. **定位问题**：支付服务超时

3. **查看支付服务 Span**：

    ```go
    Span: payment.create
    Duration: 4.7s
    Status: ERROR
    Error: context deadline exceeded

    Attributes:
    - order.id: order-123
    - amount: 99.99
    - payment.gateway: stripe

    Events:
    - 00:00.000: payment_started
    - 00:04.700: timeout_error
    ```

4. **根因分析**：支付网关响应慢

5. **解决方案**：

```go
// 添加重试和超时控制
func (ps *PaymentService) CreatePayment(ctx context.Context, req PaymentRequest) (*Payment, error) {
    ctx, cancel := context.WithTimeout(ctx, 3*time.Second)
    defer cancel()
    
    ctx, span := tracer.Start(ctx, "payment.create")
    defer span.End()
    
    // 添加重试
    var payment *Payment
    err := retry.Do(
        func() error {
            var err error
            payment, err = ps.gateway.Charge(ctx, req)
            return err
        },
        retry.Attempts(3),
        retry.Delay(100*time.Millisecond),
        retry.OnRetry(func(n uint, err error) {
            span.AddEvent("retry_attempt",
                attribute.Int("attempt", int(n)),
                attribute.String("error", err.Error()))
        }),
    )
    
    return payment, err
}
```

## 6. 参考资料

- **示例代码**：`examples/microservices/`
- **CSP 模式**：`02-golang-csp-implementation.md`
- **性能优化**：`06-performance-optimization.md`
- **微服务通信**：`05-microservices-communication.md`

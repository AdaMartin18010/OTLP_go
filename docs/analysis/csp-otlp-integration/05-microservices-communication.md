# 微服务通信模式

## 目录

- [微服务通信模式](#微服务通信模式)
  - [目录](#目录)
  - [1. 请求-响应模式](#1-请求-响应模式)
    - [1.1 同步请求-响应](#11-同步请求-响应)
    - [1.2 异步请求-响应](#12-异步请求-响应)
  - [2. 发布-订阅模式](#2-发布-订阅模式)
    - [2.1 基本发布-订阅](#21-基本发布-订阅)
    - [2.2 事件驱动架构](#22-事件驱动架构)
  - [3. 流式处理模式](#3-流式处理模式)
    - [3.1 gRPC 流式通信](#31-grpc-流式通信)
    - [3.2 WebSocket 流式通信](#32-websocket-流式通信)
  - [4. 跨服务 Context 传播](#4-跨服务-context-传播)
    - [4.1 HTTP Header 传播](#41-http-header-传播)
    - [4.2 gRPC Metadata 传播](#42-grpc-metadata-传播)
    - [4.3 消息队列传播](#43-消息队列传播)
  - [5. 服务网格集成](#5-服务网格集成)
    - [5.1 Istio + OTLP](#51-istio--otlp)
  - [6. 完整微服务示例](#6-完整微服务示例)
  - [7. 参考资料](#7-参考资料)

## 1. 请求-响应模式

### 1.1 同步请求-响应

**CSP 模型**：

```csp
CLIENT = request!msg -> response?reply -> CLIENT
SERVER = request?msg -> process(msg) -> response!reply -> SERVER
SYSTEM = CLIENT || SERVER
```

**HTTP 实现**：

```go
package main

import (
    "context"
    "encoding/json"
    "net/http"
    
    "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/propagation"
)

var (
    tracer     = otel.Tracer("microservice")
    propagator = otel.GetTextMapPropagator()
)

// Client 端
type Client struct {
    httpClient *http.Client
    baseURL    string
}

func NewClient(baseURL string) *Client {
    return &Client{
        httpClient: &http.Client{
            Transport: otelhttp.NewTransport(http.DefaultTransport),
        },
        baseURL: baseURL,
    }
}

func (c *Client) SendRequest(ctx context.Context, req Request) (*Response, error) {
    ctx, span := tracer.Start(ctx, "client_send_request")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("request.id", req.ID),
        attribute.String("request.type", req.Type),
    )
    
    // 序列化请求
    body, err := json.Marshal(req)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    // 创建 HTTP 请求
    httpReq, err := http.NewRequestWithContext(ctx, "POST", c.baseURL+"/api/process", bytes.NewReader(body))
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    httpReq.Header.Set("Content-Type", "application/json")
    
    // 注入 Trace Context
    propagator.Inject(ctx, propagation.HeaderCarrier(httpReq.Header))
    
    // 发送请求
    span.AddEvent("sending_request")
    httpResp, err := c.httpClient.Do(httpReq)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    defer httpResp.Body.Close()
    
    // 解析响应
    var resp Response
    if err := json.NewDecoder(httpResp.Body).Decode(&resp); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.AddEvent("response_received")
    span.SetAttributes(
        attribute.String("response.id", resp.ID),
        attribute.Int("response.status", httpResp.StatusCode),
    )
    
    return &resp, nil
}

// Server 端
type Server struct {
    processor *Processor
}

func NewServer(processor *Processor) *Server {
    return &Server{
        processor: processor,
    }
}

func (s *Server) HandleRequest(w http.ResponseWriter, r *http.Request) {
    // Context 已经包含从 Header 提取的 Trace Context（通过 otelhttp middleware）
    ctx := r.Context()
    ctx, span := tracer.Start(ctx, "server_handle_request")
    defer span.End()
    
    // 解析请求
    var req Request
    if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusBadRequest)
        return
    }
    
    span.SetAttributes(
        attribute.String("request.id", req.ID),
        attribute.String("request.type", req.Type),
    )
    
    // 处理请求
    resp, err := s.processor.Process(ctx, req)
    if err != nil {
        span.RecordError(err)
        http.Error(w, err.Error(), http.StatusInternalServerError)
        return
    }
    
    // 返回响应
    w.Header().Set("Content-Type", "application/json")
    json.NewEncoder(w).Encode(resp)
    
    span.AddEvent("response_sent")
}

func (s *Server) Start(addr string) error {
    mux := http.NewServeMux()
    
    // 使用 otelhttp middleware 自动提取 Trace Context
    handler := otelhttp.NewHandler(
        http.HandlerFunc(s.HandleRequest),
        "process",
    )
    
    mux.Handle("/api/process", handler)
    
    return http.ListenAndServe(addr, mux)
}
```

### 1.2 异步请求-响应

**使用消息队列**：

```go
type AsyncClient struct {
    publisher  *Publisher
    subscriber *Subscriber
    responses  map[string]chan Response
    mu         sync.Mutex
}

func (c *AsyncClient) SendRequestAsync(ctx context.Context, req Request) (<-chan Response, error) {
    ctx, span := tracer.Start(ctx, "async_send_request")
    defer span.End()
    
    // 生成关联 ID
    correlationID := uuid.New().String()
    req.CorrelationID = correlationID
    
    // 创建响应 channel
    respChan := make(chan Response, 1)
    c.mu.Lock()
    c.responses[correlationID] = respChan
    c.mu.Unlock()
    
    // 注入 Trace Context 到消息
    carrier := propagation.MapCarrier{}
    propagator.Inject(ctx, carrier)
    req.TraceContext = carrier
    
    // 发布请求
    if err := c.publisher.Publish(ctx, "requests", req); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.AddEvent("request_published", trace.WithAttributes(
        attribute.String("correlation.id", correlationID),
    ))
    
    return respChan, nil
}

func (c *AsyncClient) StartResponseListener(ctx context.Context) {
    c.subscriber.Subscribe(ctx, "responses", func(ctx context.Context, msg Message) error {
        var resp Response
        if err := json.Unmarshal(msg.Data, &resp); err != nil {
            return err
        }
        
        // 提取 Trace Context
        ctx = propagator.Extract(ctx, propagation.MapCarrier(resp.TraceContext))
        ctx, span := tracer.Start(ctx, "response_received")
        defer span.End()
        
        span.SetAttributes(
            attribute.String("correlation.id", resp.CorrelationID),
        )
        
        // 发送到对应的 channel
        c.mu.Lock()
        if ch, ok := c.responses[resp.CorrelationID]; ok {
            ch <- resp
            close(ch)
            delete(c.responses, resp.CorrelationID)
        }
        c.mu.Unlock()
        
        return nil
    })
}
```

## 2. 发布-订阅模式

### 2.1 基本发布-订阅

**CSP 模型**：

```csp
PUBLISHER = publish!event -> PUBLISHER
SUBSCRIBER1 = subscribe?event -> process1(event) -> SUBSCRIBER1
SUBSCRIBER2 = subscribe?event -> process2(event) -> SUBSCRIBER2
```

**实现**：

```go
type PubSub struct {
    topics map[string][]chan Message
    mu     sync.RWMutex
}

func NewPubSub() *PubSub {
    return &PubSub{
        topics: make(map[string][]chan Message),
    }
}

func (ps *PubSub) Publish(ctx context.Context, topic string, msg Message) error {
    ctx, span := tracer.Start(ctx, "pubsub_publish")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("topic", topic),
        attribute.String("message.id", msg.ID),
    )
    
    // 注入 Trace Context
    carrier := propagation.MapCarrier{}
    propagator.Inject(ctx, carrier)
    msg.TraceContext = carrier
    
    ps.mu.RLock()
    subscribers := ps.topics[topic]
    ps.mu.RUnlock()
    
    span.SetAttributes(
        attribute.Int("subscribers.count", len(subscribers)),
    )
    
    // 发送到所有订阅者
    for i, ch := range subscribers {
        select {
        case ch <- msg:
            span.AddEvent("message_sent", trace.WithAttributes(
                attribute.Int("subscriber.index", i),
            ))
        case <-ctx.Done():
            return ctx.Err()
        default:
            span.AddEvent("subscriber_full", trace.WithAttributes(
                attribute.Int("subscriber.index", i),
            ))
        }
    }
    
    return nil
}

func (ps *PubSub) Subscribe(ctx context.Context, topic string, handler func(context.Context, Message) error) {
    ch := make(chan Message, 100)
    
    ps.mu.Lock()
    ps.topics[topic] = append(ps.topics[topic], ch)
    ps.mu.Unlock()
    
    go func() {
        for {
            select {
            case msg := <-ch:
                // 提取 Trace Context
                msgCtx := propagator.Extract(context.Background(), propagation.MapCarrier(msg.TraceContext))
                msgCtx, span := tracer.Start(msgCtx, "subscriber_handle")
                
                span.SetAttributes(
                    attribute.String("topic", topic),
                    attribute.String("message.id", msg.ID),
                )
                
                if err := handler(msgCtx, msg); err != nil {
                    span.RecordError(err)
                }
                
                span.End()
                
            case <-ctx.Done():
                return
            }
        }
    }()
}
```

### 2.2 事件驱动架构

```go
type EventBus struct {
    pubsub *PubSub
}

func NewEventBus() *EventBus {
    return &EventBus{
        pubsub: NewPubSub(),
    }
}

// 订单服务发布事件
func (eb *EventBus) PublishOrderCreated(ctx context.Context, order Order) error {
    ctx, span := tracer.Start(ctx, "publish_order_created")
    defer span.End()
    
    event := Event{
        Type:      "order.created",
        Timestamp: time.Now(),
        Data:      order,
    }
    
    return eb.pubsub.Publish(ctx, "orders", Message{
        ID:   uuid.New().String(),
        Type: event.Type,
        Data: event,
    })
}

// 库存服务订阅事件
func (eb *EventBus) SubscribeInventoryService(ctx context.Context) {
    eb.pubsub.Subscribe(ctx, "orders", func(ctx context.Context, msg Message) error {
        ctx, span := tracer.Start(ctx, "inventory_handle_order")
        defer span.End()
        
        var event Event
        // 解析事件...
        
        if event.Type == "order.created" {
            // 扣减库存
            return reserveInventory(ctx, event.Data.(Order))
        }
        
        return nil
    })
}

// 支付服务订阅事件
func (eb *EventBus) SubscribePaymentService(ctx context.Context) {
    eb.pubsub.Subscribe(ctx, "orders", func(ctx context.Context, msg Message) error {
        ctx, span := tracer.Start(ctx, "payment_handle_order")
        defer span.End()
        
        var event Event
        // 解析事件...
        
        if event.Type == "order.created" {
            // 创建支付
            return createPayment(ctx, event.Data.(Order))
        }
        
        return nil
    })
}
```

## 3. 流式处理模式

### 3.1 gRPC 流式通信

**CSP 模型**：

```csp
CLIENT = send!msg1 -> send!msg2 -> ... -> receive?result -> CLIENT
SERVER = receive?msg1 -> receive?msg2 -> ... -> send!result -> SERVER
```

**gRPC 实现**：

```go
// proto 定义
// service StreamService {
//   rpc BidirectionalStream(stream Request) returns (stream Response);
// }

type StreamServer struct {
    pb.UnimplementedStreamServiceServer
}

func (s *StreamServer) BidirectionalStream(stream pb.StreamService_BidirectionalStreamServer) error {
    ctx := stream.Context()
    ctx, span := tracer.Start(ctx, "bidirectional_stream")
    defer span.End()
    
    // 接收 goroutine
    recvChan := make(chan *pb.Request)
    errChan := make(chan error, 1)
    
    go func() {
        for {
            req, err := stream.Recv()
            if err == io.EOF {
                close(recvChan)
                return
            }
            if err != nil {
                errChan <- err
                return
            }
            
            select {
            case recvChan <- req:
            case <-ctx.Done():
                return
            }
        }
    }()
    
    // 处理和发送
    for {
        select {
        case req, ok := <-recvChan:
            if !ok {
                return nil
            }
            
            ctx, span := tracer.Start(ctx, "process_stream_request")
            span.SetAttributes(
                attribute.String("request.id", req.Id),
            )
            
            // 处理请求
            resp := processRequest(ctx, req)
            
            // 发送响应
            if err := stream.Send(resp); err != nil {
                span.RecordError(err)
                span.End()
                return err
            }
            
            span.End()
            
        case err := <-errChan:
            span.RecordError(err)
            return err
            
        case <-ctx.Done():
            return ctx.Err()
        }
    }
}

// Client 端
type StreamClient struct {
    client pb.StreamServiceClient
}

func (c *StreamClient) Stream(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "client_stream")
    defer span.End()
    
    // 创建流
    stream, err := c.client.BidirectionalStream(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    // 发送 goroutine
    go func() {
        for i := 0; i < 10; i++ {
            req := &pb.Request{
                Id:   fmt.Sprintf("req-%d", i),
                Data: fmt.Sprintf("data-%d", i),
            }
            
            if err := stream.Send(req); err != nil {
                return
            }
            
            time.Sleep(100 * time.Millisecond)
        }
        stream.CloseSend()
    }()
    
    // 接收响应
    for {
        resp, err := stream.Recv()
        if err == io.EOF {
            break
        }
        if err != nil {
            span.RecordError(err)
            return err
        }
        
        span.AddEvent("response_received", trace.WithAttributes(
            attribute.String("response.id", resp.Id),
        ))
    }
    
    return nil
}
```

### 3.2 WebSocket 流式通信

```go
type WebSocketHandler struct {
    upgrader websocket.Upgrader
}

func (h *WebSocketHandler) HandleConnection(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    ctx, span := tracer.Start(ctx, "websocket_connection")
    defer span.End()
    
    // 升级到 WebSocket
    conn, err := h.upgrader.Upgrade(w, r, nil)
    if err != nil {
        span.RecordError(err)
        return
    }
    defer conn.Close()
    
    // 读取消息
    for {
        var msg Message
        if err := conn.ReadJSON(&msg); err != nil {
            if websocket.IsUnexpectedCloseError(err) {
                span.AddEvent("connection_closed")
            } else {
                span.RecordError(err)
            }
            break
        }
        
        // 提取 Trace Context
        msgCtx := propagator.Extract(ctx, propagation.MapCarrier(msg.TraceContext))
        msgCtx, msgSpan := tracer.Start(msgCtx, "websocket_message")
        
        msgSpan.SetAttributes(
            attribute.String("message.id", msg.ID),
            attribute.String("message.type", msg.Type),
        )
        
        // 处理消息
        resp := processMessage(msgCtx, msg)
        
        // 注入 Trace Context 到响应
        carrier := propagation.MapCarrier{}
        propagator.Inject(msgCtx, carrier)
        resp.TraceContext = carrier
        
        // 发送响应
        if err := conn.WriteJSON(resp); err != nil {
            msgSpan.RecordError(err)
            msgSpan.End()
            break
        }
        
        msgSpan.End()
    }
}
```

## 4. 跨服务 Context 传播

### 4.1 HTTP Header 传播

```go
// W3C Trace Context 格式
// traceparent: 00-{trace-id}-{parent-id}-{trace-flags}
// tracestate: vendor1=value1,vendor2=value2

func InjectTraceContext(ctx context.Context, header http.Header) {
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(header))
}

func ExtractTraceContext(ctx context.Context, header http.Header) context.Context {
    propagator := otel.GetTextMapPropagator()
    return propagator.Extract(ctx, propagation.HeaderCarrier(header))
}

// 使用示例
func makeRequest(ctx context.Context, url string) (*http.Response, error) {
    ctx, span := tracer.Start(ctx, "make_request")
    defer span.End()
    
    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        return nil, err
    }
    
    // 注入 Trace Context
    InjectTraceContext(ctx, req.Header)
    
    return http.DefaultClient.Do(req)
}

func handleRequest(w http.ResponseWriter, r *http.Request) {
    // 提取 Trace Context
    ctx := ExtractTraceContext(r.Context(), r.Header)
    ctx, span := tracer.Start(ctx, "handle_request")
    defer span.End()
    
    // 处理请求...
}
```

### 4.2 gRPC Metadata 传播

```go
import (
    "google.golang.org/grpc/metadata"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
)

// Server 端自动提取（使用 interceptor）
server := grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
    grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
)

// Client 端自动注入（使用 interceptor）
conn, err := grpc.Dial(
    address,
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
    grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
)
```

### 4.3 消息队列传播

```go
type MessageWithContext struct {
    ID           string
    Data         []byte
    TraceContext map[string]string
}

// 发布消息时注入
func PublishWithContext(ctx context.Context, topic string, data []byte) error {
    ctx, span := tracer.Start(ctx, "publish_message")
    defer span.End()
    
    // 注入 Trace Context
    carrier := propagation.MapCarrier{}
    propagator.Inject(ctx, carrier)
    
    msg := MessageWithContext{
        ID:           uuid.New().String(),
        Data:         data,
        TraceContext: carrier,
    }
    
    return publisher.Publish(topic, msg)
}

// 消费消息时提取
func ConsumeWithContext(msg MessageWithContext) error {
    // 提取 Trace Context
    ctx := propagator.Extract(context.Background(), propagation.MapCarrier(msg.TraceContext))
    ctx, span := tracer.Start(ctx, "consume_message")
    defer span.End()
    
    return processMessage(ctx, msg.Data)
}
```

## 5. 服务网格集成

### 5.1 Istio + OTLP

```yaml
# Istio Telemetry 配置
apiVersion: telemetry.istio.io/v1alpha1
kind: Telemetry
metadata:
  name: otel-demo
spec:
  tracing:
  - providers:
    - name: otel-collector
    randomSamplingPercentage: 100.0
    customTags:
      service.name:
        literal:
          value: "my-service"
```

**应用代码**：

```go
// Istio 会自动注入 Trace Headers (b3, x-request-id 等)
// 应用只需要传播这些 headers

func proxyRequest(ctx context.Context, r *http.Request, targetURL string) (*http.Response, error) {
    ctx, span := tracer.Start(ctx, "proxy_request")
    defer span.End()
    
    // 创建新请求
    proxyReq, err := http.NewRequestWithContext(ctx, r.Method, targetURL, r.Body)
    if err != nil {
        return nil, err
    }
    
    // 复制所有 tracing headers
    tracingHeaders := []string{
        "x-request-id",
        "x-b3-traceid",
        "x-b3-spanid",
        "x-b3-parentspanid",
        "x-b3-sampled",
        "x-b3-flags",
        "traceparent",
        "tracestate",
    }
    
    for _, header := range tracingHeaders {
        if val := r.Header.Get(header); val != "" {
            proxyReq.Header.Set(header, val)
        }
    }
    
    return http.DefaultClient.Do(proxyReq)
}
```

## 6. 完整微服务示例

```go
// 订单服务
type OrderService struct {
    inventoryClient *InventoryClient
    paymentClient   *PaymentClient
    eventBus        *EventBus
}

func (s *OrderService) CreateOrder(ctx context.Context, req CreateOrderRequest) (*Order, error) {
    ctx, span := tracer.Start(ctx, "create_order")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("user.id", req.UserID),
        attribute.Int("items.count", len(req.Items)),
    )
    
    // 1. 检查库存
    inventoryResp, err := s.inventoryClient.CheckInventory(ctx, req.Items)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    if !inventoryResp.Available {
        return nil, errors.New("insufficient inventory")
    }
    
    // 2. 创建订单
    order := &Order{
        ID:     uuid.New().String(),
        UserID: req.UserID,
        Items:  req.Items,
        Status: "pending",
    }
    
    // 3. 发布事件
    if err := s.eventBus.PublishOrderCreated(ctx, *order); err != nil {
        span.RecordError(err)
        return nil, err
    }
    
    span.AddEvent("order_created", trace.WithAttributes(
        attribute.String("order.id", order.ID),
    ))
    
    return order, nil
}

// 库存服务
type InventoryService struct{}

func (s *InventoryService) CheckInventory(ctx context.Context, items []Item) (*InventoryResponse, error) {
    ctx, span := tracer.Start(ctx, "check_inventory")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("items.count", len(items)),
    )
    
    // 检查库存逻辑...
    
    return &InventoryResponse{Available: true}, nil
}

// 支付服务
type PaymentService struct{}

func (s *PaymentService) CreatePayment(ctx context.Context, order Order) error {
    ctx, span := tracer.Start(ctx, "create_payment")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("order.id", order.ID),
        attribute.Float64("amount", order.TotalAmount),
    )
    
    // 创建支付逻辑...
    
    return nil
}
```

## 7. 参考资料

- **W3C Trace Context**：<https://www.w3.org/TR/trace-context/>
- **gRPC Instrumentation**：<https://opentelemetry.io/docs/languages/go/instrumentation/#grpc>
- **Microservices Patterns**：`docs/design/distributed-model.md`
- **CSP Communication**：`01-csp-otlp-isomorphism.md`

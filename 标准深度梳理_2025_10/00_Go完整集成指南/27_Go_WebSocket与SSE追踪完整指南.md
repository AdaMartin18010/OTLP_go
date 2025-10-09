# Go WebSocket 与 SSE 追踪完整指南

> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **gorilla/websocket**: v1.5.3  
> **最后更新**: 2025年10月9日

---

## 📋 目录

- [Go WebSocket 与 SSE 追踪完整指南](#go-websocket-与-sse-追踪完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [WebSocket 追踪](#websocket-追踪)
    - [1. WebSocket Server](#1-websocket-server)
    - [2. WebSocket Client](#2-websocket-client)
    - [3. 消息追踪](#3-消息追踪)
    - [4. 连接管理](#4-连接管理)
  - [Server-Sent Events (SSE) 追踪](#server-sent-events-sse-追踪)
    - [1. SSE Server](#1-sse-server)
    - [2. SSE Client](#2-sse-client)
    - [3. 事件流管理](#3-事件流管理)
  - [实时聊天应用示例](#实时聊天应用示例)
  - [性能优化](#性能优化)
  - [最佳实践](#最佳实践)
    - [1. 连接追踪](#1-连接追踪)
    - [2. 消息采样](#2-消息采样)
    - [3. 错误处理](#3-错误处理)

---

## 概述

WebSocket 和 SSE 是实时通信的两种主要技术。OpenTelemetry 可以帮助追踪连接生命周期、消息流和性能。

**技术对比**:

```text
✅ WebSocket
   - 全双工通信
   - 二进制和文本数据
   - 更低延迟
   - 更复杂的协议

✅ Server-Sent Events (SSE)
   - 单向推送 (服务器→客户端)
   - 仅文本数据
   - 自动重连
   - 基于 HTTP,更简单
```

---

## WebSocket 追踪

### 1. WebSocket Server

```go
package websocket

import (
    "context"
    "encoding/json"
    "log"
    "net/http"
    "sync"
    "time"

    "github.com/gorilla/websocket"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// WSServer WebSocket 服务器
type WSServer struct {
    upgrader websocket.Upgrader
    clients  map[*Client]bool
    mu       sync.RWMutex
    tracer   trace.Tracer
    meter    metric.Meter
    
    // Metrics
    activeConnections metric.Int64UpDownCounter
    messagesSent      metric.Int64Counter
    messagesReceived  metric.Int64Counter
}

// NewWSServer 创建 WebSocket 服务器
func NewWSServer() (*WSServer, error) {
    tracer := otel.Tracer("websocket-server")
    meter := otel.Meter("websocket-server")

    // 活跃连接数
    activeConnections, err := meter.Int64UpDownCounter("ws.connections.active",
        metric.WithDescription("Number of active WebSocket connections"),
    )
    if err != nil {
        return nil, err
    }

    // 发送的消息数
    messagesSent, err := meter.Int64Counter("ws.messages.sent",
        metric.WithDescription("Number of messages sent"),
    )
    if err != nil {
        return nil, err
    }

    // 接收的消息数
    messagesReceived, err := meter.Int64Counter("ws.messages.received",
        metric.WithDescription("Number of messages received"),
    )
    if err != nil {
        return nil, err
    }

    return &WSServer{
        upgrader: websocket.Upgrader{
            ReadBufferSize:  1024,
            WriteBufferSize: 1024,
            CheckOrigin: func(r *http.Request) bool {
                return true // 生产环境应该验证 origin
            },
        },
        clients:           make(map[*Client]bool),
        tracer:            tracer,
        meter:             meter,
        activeConnections: activeConnections,
        messagesSent:      messagesSent,
        messagesReceived:  messagesReceived,
    }, nil
}

// Client WebSocket 客户端连接
type Client struct {
    conn      *websocket.Conn
    send      chan []byte
    server    *WSServer
    id        string
    createdAt time.Time
    tracer    trace.Tracer
}

// HandleWS 处理 WebSocket 连接
func (s *WSServer) HandleWS(w http.ResponseWriter, r *http.Request) {
    // 提取追踪上下文
    ctx := r.Context()
    ctx, span := s.tracer.Start(ctx, "websocket.upgrade",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("http.method", r.Method),
            attribute.String("http.url", r.URL.String()),
            attribute.String("http.remote_addr", r.RemoteAddr),
        ),
    )
    defer span.End()

    // 升级连接
    conn, err := s.upgrader.Upgrade(w, r, nil)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "upgrade failed")
        log.Printf("Upgrade error: %v", err)
        return
    }

    span.AddEvent("connection_upgraded")

    // 创建客户端
    client := &Client{
        conn:      conn,
        send:      make(chan []byte, 256),
        server:    s,
        id:        generateClientID(),
        createdAt: time.Now(),
        tracer:    s.tracer,
    }

    // 注册客户端
    s.registerClient(ctx, client)

    // 启动读写 goroutine
    go client.readPump(ctx)
    go client.writePump(ctx)

    span.SetAttributes(
        attribute.String("client.id", client.id),
        attribute.Int("clients.total", s.clientCount()),
    )

    // 记录连接数
    s.activeConnections.Add(ctx, 1)
}

// registerClient 注册客户端
func (s *WSServer) registerClient(ctx context.Context, client *Client) {
    ctx, span := s.tracer.Start(ctx, "websocket.register_client",
        trace.WithAttributes(
            attribute.String("client.id", client.id),
        ),
    )
    defer span.End()

    s.mu.Lock()
    s.clients[client] = true
    s.mu.Unlock()

    span.AddEvent("client_registered")
}

// unregisterClient 注销客户端
func (s *WSServer) unregisterClient(ctx context.Context, client *Client) {
    ctx, span := s.tracer.Start(ctx, "websocket.unregister_client",
        trace.WithAttributes(
            attribute.String("client.id", client.id),
            attribute.Int64("connection_duration_ms", time.Since(client.createdAt).Milliseconds()),
        ),
    )
    defer span.End()

    s.mu.Lock()
    if _, ok := s.clients[client]; ok {
        delete(s.clients, client)
        close(client.send)
    }
    s.mu.Unlock()

    span.AddEvent("client_unregistered")
    s.activeConnections.Add(ctx, -1)
}

// clientCount 获取客户端数量
func (s *WSServer) clientCount() int {
    s.mu.RLock()
    defer s.mu.RUnlock()
    return len(s.clients)
}

// Broadcast 广播消息
func (s *WSServer) Broadcast(ctx context.Context, message []byte) {
    ctx, span := s.tracer.Start(ctx, "websocket.broadcast",
        trace.WithAttributes(
            attribute.Int("clients.count", s.clientCount()),
            attribute.Int("message.size", len(message)),
        ),
    )
    defer span.End()

    s.mu.RLock()
    clients := make([]*Client, 0, len(s.clients))
    for client := range s.clients {
        clients = append(clients, client)
    }
    s.mu.RUnlock()

    sentCount := 0
    for _, client := range clients {
        select {
        case client.send <- message:
            sentCount++
        default:
            // 发送缓冲区满,关闭连接
            go s.unregisterClient(ctx, client)
        }
    }

    span.SetAttributes(
        attribute.Int("messages.sent", sentCount),
    )

    s.messagesSent.Add(ctx, int64(sentCount))
}

// readPump 读取消息
func (c *Client) readPump(ctx context.Context) {
    defer func() {
        c.server.unregisterClient(ctx, c)
        c.conn.Close()
    }()

    // 设置读取超时
    c.conn.SetReadDeadline(time.Now().Add(60 * time.Second))
    c.conn.SetPongHandler(func(string) error {
        c.conn.SetReadDeadline(time.Now().Add(60 * time.Second))
        return nil
    })

    for {
        messageType, message, err := c.conn.ReadMessage()
        if err != nil {
            if websocket.IsUnexpectedCloseError(err, websocket.CloseGoingAway, websocket.CloseAbnormalClosure) {
                ctx, span := c.tracer.Start(ctx, "websocket.read_error",
                    trace.WithAttributes(
                        attribute.String("client.id", c.id),
                        attribute.String("error", err.Error()),
                    ),
                )
                span.RecordError(err)
                span.End()
            }
            break
        }

        // 处理消息
        c.handleMessage(ctx, messageType, message)
    }
}

// handleMessage 处理消息
func (c *Client) handleMessage(ctx context.Context, messageType int, message []byte) {
    ctx, span := c.tracer.Start(ctx, "websocket.handle_message",
        trace.WithAttributes(
            attribute.String("client.id", c.id),
            attribute.Int("message.type", messageType),
            attribute.Int("message.size", len(message)),
        ),
    )
    defer span.End()

    // 记录接收的消息
    c.server.messagesReceived.Add(ctx, 1)

    // 解析消息
    var msg Message
    if err := json.Unmarshal(message, &msg); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "invalid message format")
        return
    }

    span.SetAttributes(
        attribute.String("message.action", msg.Action),
    )

    // 根据消息类型处理
    switch msg.Action {
    case "chat":
        // 广播聊天消息
        c.server.Broadcast(ctx, message)
    case "ping":
        // 响应 ping
        c.send <- []byte(`{"action":"pong"}`)
    default:
        span.AddEvent("unknown_action")
    }
}

// writePump 写入消息
func (c *Client) writePump(ctx context.Context) {
    ticker := time.NewTicker(54 * time.Second)
    defer func() {
        ticker.Stop()
        c.conn.Close()
    }()

    for {
        select {
        case message, ok := <-c.send:
            c.conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
            if !ok {
                // Channel 关闭
                c.conn.WriteMessage(websocket.CloseMessage, []byte{})
                return
            }

            // 写入消息
            ctx, span := c.tracer.Start(ctx, "websocket.write_message",
                trace.WithAttributes(
                    attribute.String("client.id", c.id),
                    attribute.Int("message.size", len(message)),
                ),
            )

            err := c.conn.WriteMessage(websocket.TextMessage, message)
            if err != nil {
                span.RecordError(err)
                span.End()
                return
            }

            span.End()

        case <-ticker.C:
            // 发送 ping
            c.conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
            if err := c.conn.WriteMessage(websocket.PingMessage, nil); err != nil {
                return
            }
        }
    }
}

// Message 消息结构
type Message struct {
    Action string `json:"action"`
    Data   string `json:"data"`
}

func generateClientID() string {
    return fmt.Sprintf("client-%d", time.Now().UnixNano())
}
```

### 2. WebSocket Client

```go
package websocket

import (
    "context"
    "time"

    "github.com/gorilla/websocket"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// WSClient WebSocket 客户端
type WSClient struct {
    conn    *websocket.Conn
    url     string
    tracer  trace.Tracer
    done    chan struct{}
    onMessage func([]byte)
}

// NewWSClient 创建 WebSocket 客户端
func NewWSClient(url string) *WSClient {
    return &WSClient{
        url:    url,
        tracer: otel.Tracer("websocket-client"),
        done:   make(chan struct{}),
    }
}

// Connect 连接到服务器
func (c *WSClient) Connect(ctx context.Context) error {
    ctx, span := c.tracer.Start(ctx, "websocket.connect",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("ws.url", c.url),
        ),
    )
    defer span.End()

    // 创建 WebSocket 连接
    dialer := websocket.Dialer{
        HandshakeTimeout: 10 * time.Second,
    }

    conn, resp, err := dialer.DialContext(ctx, c.url, nil)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "connection failed")
        return err
    }
    defer resp.Body.Close()

    c.conn = conn

    span.SetAttributes(
        attribute.Int("http.status_code", resp.StatusCode),
    )
    span.AddEvent("connected")

    // 启动读取 goroutine
    go c.readLoop(ctx)

    return nil
}

// Send 发送消息
func (c *WSClient) Send(ctx context.Context, message []byte) error {
    ctx, span := c.tracer.Start(ctx, "websocket.send",
        trace.WithAttributes(
            attribute.Int("message.size", len(message)),
        ),
    )
    defer span.End()

    err := c.conn.WriteMessage(websocket.TextMessage, message)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "send failed")
        return err
    }

    return nil
}

// readLoop 读取循环
func (c *WSClient) readLoop(ctx context.Context) {
    defer close(c.done)

    for {
        messageType, message, err := c.conn.ReadMessage()
        if err != nil {
            ctx, span := c.tracer.Start(ctx, "websocket.read_error")
            span.RecordError(err)
            span.End()
            break
        }

        // 追踪消息接收
        ctx, span := c.tracer.Start(ctx, "websocket.receive",
            trace.WithAttributes(
                attribute.Int("message.type", messageType),
                attribute.Int("message.size", len(message)),
            ),
        )

        // 调用回调
        if c.onMessage != nil {
            c.onMessage(message)
        }

        span.End()
    }
}

// Close 关闭连接
func (c *WSClient) Close(ctx context.Context) error {
    ctx, span := c.tracer.Start(ctx, "websocket.close")
    defer span.End()

    err := c.conn.WriteMessage(websocket.CloseMessage, websocket.FormatCloseMessage(websocket.CloseNormalClosure, ""))
    if err != nil {
        span.RecordError(err)
    }

    c.conn.Close()
    <-c.done

    span.AddEvent("closed")
    return nil
}

// OnMessage 设置消息回调
func (c *WSClient) OnMessage(handler func([]byte)) {
    c.onMessage = handler
}
```

### 3. 消息追踪

```go
package websocket

import (
    "context"
    "encoding/json"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/propagation"
)

// TracedMessage 带追踪的消息
type TracedMessage struct {
    Action     string            `json:"action"`
    Data       interface{}       `json:"data"`
    TraceID    string            `json:"trace_id,omitempty"`
    SpanID     string            `json:"span_id,omitempty"`
    TraceFlags map[string]string `json:"trace_flags,omitempty"`
}

// InjectTraceContext 注入追踪上下文
func InjectTraceContext(ctx context.Context, msg *TracedMessage) {
    span := trace.SpanFromContext(ctx)
    if !span.SpanContext().IsValid() {
        return
    }

    sc := span.SpanContext()
    msg.TraceID = sc.TraceID().String()
    msg.SpanID = sc.SpanID().String()

    // 注入 W3C Trace Context
    carrier := propagation.MapCarrier{}
    otel.GetTextMapPropagator().Inject(ctx, carrier)
    msg.TraceFlags = carrier
}

// ExtractTraceContext 提取追踪上下文
func ExtractTraceContext(msg *TracedMessage) context.Context {
    if msg.TraceFlags == nil {
        return context.Background()
    }

    // 提取 W3C Trace Context
    carrier := propagation.MapCarrier(msg.TraceFlags)
    ctx := otel.GetTextMapPropagator().Extract(context.Background(), carrier)

    return ctx
}

// SendTracedMessage 发送带追踪的消息
func (c *Client) SendTracedMessage(ctx context.Context, action string, data interface{}) error {
    ctx, span := c.tracer.Start(ctx, "websocket.send_traced_message",
        trace.WithAttributes(
            attribute.String("message.action", action),
        ),
    )
    defer span.End()

    // 创建消息
    msg := &TracedMessage{
        Action: action,
        Data:   data,
    }

    // 注入追踪上下文
    InjectTraceContext(ctx, msg)

    // 序列化
    payload, err := json.Marshal(msg)
    if err != nil {
        span.RecordError(err)
        return err
    }

    // 发送
    c.send <- payload

    return nil
}

// HandleTracedMessage 处理带追踪的消息
func (c *Client) HandleTracedMessage(message []byte) {
    var msg TracedMessage
    if err := json.Unmarshal(message, &msg); err != nil {
        return
    }

    // 提取追踪上下文
    ctx := ExtractTraceContext(&msg)

    // 在提取的上下文中处理消息
    ctx, span := c.tracer.Start(ctx, "websocket.handle_traced_message",
        trace.WithAttributes(
            attribute.String("message.action", msg.Action),
            attribute.String("trace.id", msg.TraceID),
            attribute.String("span.id", msg.SpanID),
        ),
    )
    defer span.End()

    // 处理消息...
}
```

### 4. 连接管理

```go
package websocket

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// ConnectionManager 连接管理器
type ConnectionManager struct {
    clients map[string]*Client
    mu      sync.RWMutex
    tracer  trace.Tracer
    meter   metric.Meter
}

// NewConnectionManager 创建连接管理器
func NewConnectionManager() *ConnectionManager {
    return &ConnectionManager{
        clients: make(map[string]*Client),
        tracer:  otel.Tracer("connection-manager"),
        meter:   otel.Meter("connection-manager"),
    }
}

// Add 添加连接
func (cm *ConnectionManager) Add(ctx context.Context, client *Client) {
    ctx, span := cm.tracer.Start(ctx, "connection_manager.add",
        trace.WithAttributes(
            attribute.String("client.id", client.id),
        ),
    )
    defer span.End()

    cm.mu.Lock()
    cm.clients[client.id] = client
    cm.mu.Unlock()

    span.SetAttributes(attribute.Int("clients.total", len(cm.clients)))
}

// Remove 移除连接
func (cm *ConnectionManager) Remove(ctx context.Context, clientID string) {
    ctx, span := cm.tracer.Start(ctx, "connection_manager.remove",
        trace.WithAttributes(
            attribute.String("client.id", clientID),
        ),
    )
    defer span.End()

    cm.mu.Lock()
    delete(cm.clients, clientID)
    cm.mu.Unlock()

    span.SetAttributes(attribute.Int("clients.total", len(cm.clients)))
}

// GetStats 获取统计信息
func (cm *ConnectionManager) GetStats(ctx context.Context) map[string]interface{} {
    ctx, span := cm.tracer.Start(ctx, "connection_manager.stats")
    defer span.End()

    cm.mu.RLock()
    defer cm.mu.RUnlock()

    stats := map[string]interface{}{
        "total_connections": len(cm.clients),
        "timestamp":         time.Now(),
    }

    span.SetAttributes(
        attribute.Int("connections.total", len(cm.clients)),
    )

    return stats
}
```

---

## Server-Sent Events (SSE) 追踪

### 1. SSE Server

```go
package sse

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
)

// SSEServer SSE 服务器
type SSEServer struct {
    clients map[chan []byte]bool
    mu      sync.RWMutex
    tracer  trace.Tracer
    meter   metric.Meter
}

// NewSSEServer 创建 SSE 服务器
func NewSSEServer() *SSEServer {
    return &SSEServer{
        clients: make(map[chan []byte]bool),
        tracer:  otel.Tracer("sse-server"),
        meter:   otel.Meter("sse-server"),
    }
}

// HandleSSE 处理 SSE 连接
func (s *SSEServer) HandleSSE(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    ctx, span := s.tracer.Start(ctx, "sse.handle_connection",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("http.method", r.Method),
            attribute.String("http.url", r.URL.String()),
        ),
    )
    defer span.End()

    // 设置 SSE 头
    w.Header().Set("Content-Type", "text/event-stream")
    w.Header().Set("Cache-Control", "no-cache")
    w.Header().Set("Connection", "keep-alive")
    w.Header().Set("Access-Control-Allow-Origin", "*")

    flusher, ok := w.(http.Flusher)
    if !ok {
        span.SetStatus(codes.Error, "streaming unsupported")
        http.Error(w, "Streaming unsupported", http.StatusInternalServerError)
        return
    }

    // 创建客户端 channel
    clientChan := make(chan []byte, 256)

    // 注册客户端
    s.addClient(ctx, clientChan)
    defer s.removeClient(ctx, clientChan)

    span.AddEvent("client_connected")

    // 发送心跳
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()

    for {
        select {
        case <-ctx.Done():
            span.AddEvent("client_disconnected")
            return

        case message := <-clientChan:
            // 发送消息
            ctx, msgSpan := s.tracer.Start(ctx, "sse.send_message",
                trace.WithAttributes(
                    attribute.Int("message.size", len(message)),
                ),
            )

            fmt.Fprintf(w, "data: %s\n\n", message)
            flusher.Flush()

            msgSpan.End()

        case <-ticker.C:
            // 发送心跳
            fmt.Fprintf(w, ": heartbeat\n\n")
            flusher.Flush()
        }
    }
}

// addClient 添加客户端
func (s *SSEServer) addClient(ctx context.Context, client chan []byte) {
    ctx, span := s.tracer.Start(ctx, "sse.add_client")
    defer span.End()

    s.mu.Lock()
    s.clients[client] = true
    s.mu.Unlock()

    span.SetAttributes(attribute.Int("clients.total", len(s.clients)))
}

// removeClient 移除客户端
func (s *SSEServer) removeClient(ctx context.Context, client chan []byte) {
    ctx, span := s.tracer.Start(ctx, "sse.remove_client")
    defer span.End()

    s.mu.Lock()
    delete(s.clients, client)
    close(client)
    s.mu.Unlock()

    span.SetAttributes(attribute.Int("clients.total", len(s.clients)))
}

// Broadcast 广播消息
func (s *SSEServer) Broadcast(ctx context.Context, event string, data interface{}) {
    ctx, span := s.tracer.Start(ctx, "sse.broadcast",
        trace.WithAttributes(
            attribute.String("event.type", event),
            attribute.Int("clients.count", len(s.clients)),
        ),
    )
    defer span.End()

    // 序列化数据
    payload, err := json.Marshal(data)
    if err != nil {
        span.RecordError(err)
        return
    }

    message := []byte(fmt.Sprintf("event: %s\ndata: %s", event, payload))

    s.mu.RLock()
    clients := make([]chan []byte, 0, len(s.clients))
    for client := range s.clients {
        clients = append(clients, client)
    }
    s.mu.RUnlock()

    sentCount := 0
    for _, client := range clients {
        select {
        case client <- message:
            sentCount++
        default:
            // Channel 满,跳过
        }
    }

    span.SetAttributes(attribute.Int("messages.sent", sentCount))
}
```

### 2. SSE Client

```go
package sse

import (
    "bufio"
    "context"
    "net/http"
    "strings"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

// SSEClient SSE 客户端
type SSEClient struct {
    url       string
    client    *http.Client
    tracer    trace.Tracer
    onMessage func(event, data string)
}

// NewSSEClient 创建 SSE 客户端
func NewSSEClient(url string) *SSEClient {
    return &SSEClient{
        url:    url,
        client: &http.Client{},
        tracer: otel.Tracer("sse-client"),
    }
}

// Connect 连接到服务器
func (c *SSEClient) Connect(ctx context.Context) error {
    ctx, span := c.tracer.Start(ctx, "sse.connect",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("sse.url", c.url),
        ),
    )
    defer span.End()

    req, err := http.NewRequestWithContext(ctx, "GET", c.url, nil)
    if err != nil {
        span.RecordError(err)
        return err
    }

    req.Header.Set("Accept", "text/event-stream")

    resp, err := c.client.Do(req)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "connection failed")
        return err
    }

    if resp.StatusCode != http.StatusOK {
        span.SetStatus(codes.Error, "unexpected status code")
        return fmt.Errorf("unexpected status: %d", resp.StatusCode)
    }

    span.AddEvent("connected")

    // 启动读取 goroutine
    go c.readLoop(ctx, resp)

    return nil
}

// readLoop 读取循环
func (c *SSEClient) readLoop(ctx context.Context, resp *http.Response) {
    defer resp.Body.Close()

    scanner := bufio.NewScanner(resp.Body)
    var event, data string

    for scanner.Scan() {
        line := scanner.Text()

        if line == "" {
            // 空行表示消息结束
            if data != "" {
                ctx, span := c.tracer.Start(ctx, "sse.receive",
                    trace.WithAttributes(
                        attribute.String("event.type", event),
                        attribute.Int("data.size", len(data)),
                    ),
                )

                if c.onMessage != nil {
                    c.onMessage(event, data)
                }

                span.End()

                event = ""
                data = ""
            }
            continue
        }

        if strings.HasPrefix(line, "event:") {
            event = strings.TrimSpace(line[6:])
        } else if strings.HasPrefix(line, "data:") {
            data = strings.TrimSpace(line[5:])
        }
    }

    if err := scanner.Err(); err != nil {
        ctx, span := c.tracer.Start(ctx, "sse.read_error")
        span.RecordError(err)
        span.End()
    }
}

// OnMessage 设置消息回调
func (c *SSEClient) OnMessage(handler func(event, data string)) {
    c.onMessage = handler
}
```

### 3. 事件流管理

```go
package sse

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// EventStream 事件流
type EventStream struct {
    id        string
    clients   []chan []byte
    mu        sync.RWMutex
    tracer    trace.Tracer
    createdAt time.Time
}

// NewEventStream 创建事件流
func NewEventStream(id string) *EventStream {
    return &EventStream{
        id:        id,
        clients:   make([]chan []byte, 0),
        tracer:    otel.Tracer("event-stream"),
        createdAt: time.Now(),
    }
}

// Subscribe 订阅事件流
func (es *EventStream) Subscribe(ctx context.Context) chan []byte {
    ctx, span := es.tracer.Start(ctx, "event_stream.subscribe",
        trace.WithAttributes(
            attribute.String("stream.id", es.id),
        ),
    )
    defer span.End()

    client := make(chan []byte, 256)

    es.mu.Lock()
    es.clients = append(es.clients, client)
    es.mu.Unlock()

    span.SetAttributes(attribute.Int("subscribers.count", len(es.clients)))

    return client
}

// Unsubscribe 取消订阅
func (es *EventStream) Unsubscribe(ctx context.Context, client chan []byte) {
    ctx, span := es.tracer.Start(ctx, "event_stream.unsubscribe",
        trace.WithAttributes(
            attribute.String("stream.id", es.id),
        ),
    )
    defer span.End()

    es.mu.Lock()
    defer es.mu.Unlock()

    for i, c := range es.clients {
        if c == client {
            es.clients = append(es.clients[:i], es.clients[i+1:]...)
            close(client)
            break
        }
    }

    span.SetAttributes(attribute.Int("subscribers.count", len(es.clients)))
}

// Publish 发布事件
func (es *EventStream) Publish(ctx context.Context, message []byte) {
    ctx, span := es.tracer.Start(ctx, "event_stream.publish",
        trace.WithAttributes(
            attribute.String("stream.id", es.id),
            attribute.Int("message.size", len(message)),
            attribute.Int("subscribers.count", len(es.clients)),
        ),
    )
    defer span.End()

    es.mu.RLock()
    defer es.mu.RUnlock()

    sentCount := 0
    for _, client := range es.clients {
        select {
        case client <- message:
            sentCount++
        default:
            // Channel 满
        }
    }

    span.SetAttributes(attribute.Int("messages.sent", sentCount))
}
```

---

## 实时聊天应用示例

```go
package chat

import (
    "context"
    "encoding/json"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// ChatRoom 聊天室
type ChatRoom struct {
    id      string
    server  *WSServer
    tracer  trace.Tracer
    history []ChatMessage
}

// ChatMessage 聊天消息
type ChatMessage struct {
    ID        string    `json:"id"`
    RoomID    string    `json:"room_id"`
    UserID    string    `json:"user_id"`
    Username  string    `json:"username"`
    Content   string    `json:"content"`
    Timestamp time.Time `json:"timestamp"`
}

// NewChatRoom 创建聊天室
func NewChatRoom(id string, server *WSServer) *ChatRoom {
    return &ChatRoom{
        id:      id,
        server:  server,
        tracer:  otel.Tracer("chat-room"),
        history: make([]ChatMessage, 0),
    }
}

// SendMessage 发送消息
func (cr *ChatRoom) SendMessage(ctx context.Context, msg ChatMessage) error {
    ctx, span := cr.tracer.Start(ctx, "chat_room.send_message",
        trace.WithAttributes(
            attribute.String("room.id", cr.id),
            attribute.String("user.id", msg.UserID),
            attribute.String("user.name", msg.Username),
            attribute.Int("content.length", len(msg.Content)),
        ),
    )
    defer span.End()

    // 添加到历史
    msg.Timestamp = time.Now()
    cr.history = append(cr.history, msg)

    // 序列化消息
    payload, err := json.Marshal(msg)
    if err != nil {
        span.RecordError(err)
        return err
    }

    // 广播消息
    cr.server.Broadcast(ctx, payload)

    span.AddEvent("message_broadcasted")

    return nil
}

// GetHistory 获取历史消息
func (cr *ChatRoom) GetHistory(ctx context.Context, limit int) []ChatMessage {
    ctx, span := cr.tracer.Start(ctx, "chat_room.get_history",
        trace.WithAttributes(
            attribute.String("room.id", cr.id),
            attribute.Int("limit", limit),
        ),
    )
    defer span.End()

    start := len(cr.history) - limit
    if start < 0 {
        start = 0
    }

    history := cr.history[start:]

    span.SetAttributes(attribute.Int("messages.count", len(history)))

    return history
}
```

---

## 性能优化

```go
package performance

// 连接池配置
var OptimalWSConfig = struct {
    ReadBufferSize  int
    WriteBufferSize int
    MaxMessageSize  int64
    PingInterval    time.Duration
    PongWait        time.Duration
}{
    ReadBufferSize:  1024,
    WriteBufferSize: 1024,
    MaxMessageSize:  512 * 1024, // 512KB
    PingInterval:    54 * time.Second,
    PongWait:        60 * time.Second,
}

// SSE 优化配置
var OptimalSSEConfig = struct {
    HeartbeatInterval time.Duration
    BufferSize        int
}{
    HeartbeatInterval: 30 * time.Second,
    BufferSize:        256,
}
```

---

## 最佳实践

### 1. 连接追踪

```go
✅ DO: 追踪连接生命周期
- 连接建立
- 消息收发
- 连接关闭
- 异常断开

✅ DO: 记录连接统计
- 活跃连接数
- 消息吞吐量
- 平均延迟

❌ DON'T: 追踪每条消息的完整内容
- 使用消息 ID 和大小即可
```

### 2. 消息采样

```go
// 高频消息采样
type MessageSampler struct {
    rate float64
}

func (ms *MessageSampler) ShouldTrace() bool {
    return rand.Float64() < ms.rate
}

// 使用
sampler := &MessageSampler{rate: 0.1} // 10% 采样

if sampler.ShouldTrace() {
    // 创建 Span
}
```

### 3. 错误处理

```go
✅ DO: 区分错误类型
- 连接错误 (网络问题)
- 协议错误 (格式错误)
- 业务错误 (逻辑错误)

✅ DO: 记录错误上下文
span.SetAttributes(
    attribute.String("error.type", "connection"),
    attribute.String("error.code", "timeout"),
)

❌ DON'T: 忽略客户端主动断开
if websocket.IsCloseError(err, websocket.CloseNormalClosure) {
    // 正常关闭,不记录为错误
}
```

---

**相关文档**:

- [Go HTTP/2 和 HTTP/3 追踪](./25_Go_HTTP2_HTTP3追踪完整指南.md)
- [Go 并发原语集成](./24_Go并发原语与OTLP深度集成.md)
- [Go 性能优化](./03_Go性能优化与最佳实践.md)


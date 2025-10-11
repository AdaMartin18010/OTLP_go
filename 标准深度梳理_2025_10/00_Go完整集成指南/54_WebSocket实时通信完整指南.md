# 54. WebSocket 实时通信完整指南

## 📚 目录

- [54. WebSocket 实时通信完整指南](#54-websocket-实时通信完整指南)
  - [📚 目录](#-目录)
  - [1. WebSocket 概述](#1-websocket-概述)
    - [1.1 什么是 WebSocket](#11-什么是-websocket)
    - [1.2 依赖版本](#12-依赖版本)
  - [2. gorilla/websocket 集成](#2-gorillawebsocket-集成)
    - [2.1 基础服务器](#21-基础服务器)
  - [3. 连接管理](#3-连接管理)
    - [3.1 Hub（连接管理器）](#31-hub连接管理器)
    - [3.2 房间管理](#32-房间管理)
  - [4. 消息处理](#4-消息处理)
    - [4.1 HTTP 处理器](#41-http-处理器)
  - [5. OTLP 追踪集成](#5-otlp-追踪集成)
    - [5.1 追踪消息流](#51-追踪消息流)
  - [6. 实时应用场景](#6-实时应用场景)
    - [6.1 实时聊天](#61-实时聊天)
    - [6.2 实时通知](#62-实时通知)
    - [6.3 实时数据流](#63-实时数据流)
  - [7. 生产级实践](#7-生产级实践)
    - [7.1 完整服务器](#71-完整服务器)
    - [7.2 客户端示例](#72-客户端示例)
  - [8. 总结](#8-总结)
    - [核心优势](#核心优势)
    - [最佳实践](#最佳实践)
    - [相关文档](#相关文档)

---

## 1. WebSocket 概述

### 1.1 什么是 WebSocket

WebSocket 是一种在单个 TCP 连接上进行全双工通信的协议，实现客户端和服务器之间的实时双向数据传输。

**核心优势**:

- ✅ **全双工通信** - 服务器主动推送
- ✅ **低延迟** - 持久连接
- ✅ **高效** - 减少 HTTP 开销
- ✅ **实时性** - 即时消息传递
- ✅ **跨平台** - 浏览器原生支持

### 1.2 依赖版本

```go
// go.mod
module github.com/yourorg/websocket-service

go 1.25.1

require (
    // WebSocket
    github.com/gorilla/websocket v1.5.3
    
    // OTLP
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/otel/metric v1.32.0
    
    // 工具
    github.com/go-chi/chi/v5 v5.1.0
    github.com/google/uuid v1.6.0
)
```

---

## 2. gorilla/websocket 集成

### 2.1 基础服务器

```go
// internal/websocket/server.go
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
    "go.opentelemetry.io/otel/trace"
)

// Upgrader WebSocket 升级器
var upgrader = websocket.Upgrader{
    ReadBufferSize:  1024,
    WriteBufferSize: 1024,
    CheckOrigin: func(r *http.Request) bool {
        // 生产环境应该验证 Origin
        return true
    },
}

// Message 消息
type Message struct {
    Type      string                 `json:"type"`
    Payload   map[string]interface{} `json:"payload"`
    Timestamp time.Time              `json:"timestamp"`
    TraceID   string                 `json:"trace_id,omitempty"`
    SpanID    string                 `json:"span_id,omitempty"`
}

// Client WebSocket 客户端
type Client struct {
    ID       string
    Conn     *websocket.Conn
    Send     chan *Message
    Hub      *Hub
    UserID   string
    metadata map[string]string
    tracer   trace.Tracer
}

// NewClient 创建客户端
func NewClient(conn *websocket.Conn, hub *Hub, userID string) *Client {
    return &Client{
        ID:       uuid.New().String(),
        Conn:     conn,
        Send:     make(chan *Message, 256),
        Hub:      hub,
        UserID:   userID,
        metadata: make(map[string]string),
        tracer:   otel.Tracer("websocket-client"),
    }
}

// ReadPump 读取消息
func (c *Client) ReadPump(ctx context.Context) {
    defer func() {
        c.Hub.unregister <- c
        c.Conn.Close()
    }()
    
    c.Conn.SetReadDeadline(time.Now().Add(60 * time.Second))
    c.Conn.SetPongHandler(func(string) error {
        c.Conn.SetReadDeadline(time.Now().Add(60 * time.Second))
        return nil
    })
    
    for {
        var msg Message
        err := c.Conn.ReadJSON(&msg)
        if err != nil {
            if websocket.IsUnexpectedCloseError(err, websocket.CloseGoingAway, websocket.CloseAbnormalClosure) {
                log.Printf("Error: %v", err)
            }
            break
        }
        
        // 创建追踪 Span
        ctx, span := c.tracer.Start(ctx, "websocket.receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                attribute.String("client.id", c.ID),
                attribute.String("message.type", msg.Type),
            ),
        )
        
        // 处理消息
        c.Hub.handleMessage <- &ClientMessage{
            Client:  c,
            Message: &msg,
            Context: ctx,
        }
        
        span.End()
    }
}

// WritePump 发送消息
func (c *Client) WritePump(ctx context.Context) {
    ticker := time.NewTicker(54 * time.Second)
    defer func() {
        ticker.Stop()
        c.Conn.Close()
    }()
    
    for {
        select {
        case message, ok := <-c.Send:
            c.Conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
            if !ok {
                c.Conn.WriteMessage(websocket.CloseMessage, []byte{})
                return
            }
            
            // 创建追踪 Span
            _, span := c.tracer.Start(ctx, "websocket.send",
                trace.WithSpanKind(trace.SpanKindProducer),
                trace.WithAttributes(
                    attribute.String("client.id", c.ID),
                    attribute.String("message.type", message.Type),
                ),
            )
            
            // 注入追踪信息
            spanCtx := span.SpanContext()
            message.TraceID = spanCtx.TraceID().String()
            message.SpanID = spanCtx.SpanID().String()
            
            err := c.Conn.WriteJSON(message)
            if err != nil {
                span.RecordError(err)
                span.End()
                return
            }
            
            span.End()
            
        case <-ticker.C:
            c.Conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
            if err := c.Conn.WriteMessage(websocket.PingMessage, nil); err != nil {
                return
            }
        }
    }
}
```

---

## 3. 连接管理

### 3.1 Hub（连接管理器）

```go
// Hub WebSocket 连接管理器
type Hub struct {
    // 注册的客户端
    clients map[*Client]bool
    
    // 按用户 ID 索引
    clientsByUser map[string]map[*Client]bool
    
    // 按房间索引
    rooms map[string]map[*Client]bool
    
    // 注册请求
    register chan *Client
    
    // 注销请求
    unregister chan *Client
    
    // 广播消息
    broadcast chan *Message
    
    // 处理消息
    handleMessage chan *ClientMessage
    
    // 互斥锁
    mu     sync.RWMutex
    tracer trace.Tracer
    meter  metric.Meter
    
    // 指标
    activeConnections metric.Int64UpDownCounter
    messagesReceived  metric.Int64Counter
    messagesSent      metric.Int64Counter
}

// ClientMessage 客户端消息
type ClientMessage struct {
    Client  *Client
    Message *Message
    Context context.Context
}

// NewHub 创建 Hub
func NewHub() (*Hub, error) {
    tracer := otel.Tracer("websocket-hub")
    meter := otel.Meter("websocket-hub")
    
    activeConnections, err := meter.Int64UpDownCounter(
        "websocket.active_connections",
        metric.WithDescription("Active WebSocket connections"),
    )
    if err != nil {
        return nil, err
    }
    
    messagesReceived, err := meter.Int64Counter(
        "websocket.messages.received",
        metric.WithDescription("WebSocket messages received"),
    )
    if err != nil {
        return nil, err
    }
    
    messagesSent, err := meter.Int64Counter(
        "websocket.messages.sent",
        metric.WithDescription("WebSocket messages sent"),
    )
    if err != nil {
        return nil, err
    }
    
    return &Hub{
        clients:           make(map[*Client]bool),
        clientsByUser:     make(map[string]map[*Client]bool),
        rooms:             make(map[string]map[*Client]bool),
        register:          make(chan *Client),
        unregister:        make(chan *Client),
        broadcast:         make(chan *Message),
        handleMessage:     make(chan *ClientMessage),
        tracer:            tracer,
        meter:             meter,
        activeConnections: activeConnections,
        messagesReceived:  messagesReceived,
        messagesSent:      messagesSent,
    }, nil
}

// Run 运行 Hub
func (h *Hub) Run(ctx context.Context) {
    for {
        select {
        case client := <-h.register:
            h.mu.Lock()
            h.clients[client] = true
            
            // 按用户 ID 索引
            if _, ok := h.clientsByUser[client.UserID]; !ok {
                h.clientsByUser[client.UserID] = make(map[*Client]bool)
            }
            h.clientsByUser[client.UserID][client] = true
            
            h.mu.Unlock()
            
            // 记录指标
            h.activeConnections.Add(ctx, 1)
            
            log.Printf("Client registered: %s (user: %s)", client.ID, client.UserID)
            
        case client := <-h.unregister:
            h.mu.Lock()
            if _, ok := h.clients[client]; ok {
                delete(h.clients, client)
                close(client.Send)
                
                // 从用户索引删除
                if clients, ok := h.clientsByUser[client.UserID]; ok {
                    delete(clients, client)
                    if len(clients) == 0 {
                        delete(h.clientsByUser, client.UserID)
                    }
                }
                
                // 从所有房间删除
                for roomID, clients := range h.rooms {
                    if _, ok := clients[client]; ok {
                        delete(clients, client)
                        if len(clients) == 0 {
                            delete(h.rooms, roomID)
                        }
                    }
                }
            }
            h.mu.Unlock()
            
            // 记录指标
            h.activeConnections.Add(ctx, -1)
            
            log.Printf("Client unregistered: %s", client.ID)
            
        case message := <-h.broadcast:
            h.mu.RLock()
            for client := range h.clients {
                select {
                case client.Send <- message:
                    h.messagesSent.Add(ctx, 1)
                default:
                    close(client.Send)
                    delete(h.clients, client)
                }
            }
            h.mu.RUnlock()
            
        case clientMsg := <-h.handleMessage:
            h.messagesReceived.Add(ctx, 1)
            h.processMessage(clientMsg)
            
        case <-ctx.Done():
            return
        }
    }
}

// processMessage 处理消息
func (h *Hub) processMessage(clientMsg *ClientMessage) {
    ctx := clientMsg.Context
    
    ctx, span := h.tracer.Start(ctx, "hub.process_message",
        trace.WithAttributes(
            attribute.String("message.type", clientMsg.Message.Type),
        ),
    )
    defer span.End()
    
    switch clientMsg.Message.Type {
    case "join_room":
        roomID := clientMsg.Message.Payload["room_id"].(string)
        h.JoinRoom(clientMsg.Client, roomID)
        
    case "leave_room":
        roomID := clientMsg.Message.Payload["room_id"].(string)
        h.LeaveRoom(clientMsg.Client, roomID)
        
    case "send_to_room":
        roomID := clientMsg.Message.Payload["room_id"].(string)
        h.SendToRoom(roomID, clientMsg.Message)
        
    case "send_to_user":
        userID := clientMsg.Message.Payload["user_id"].(string)
        h.SendToUser(userID, clientMsg.Message)
    }
}
```

### 3.2 房间管理

```go
// JoinRoom 加入房间
func (h *Hub) JoinRoom(client *Client, roomID string) {
    h.mu.Lock()
    defer h.mu.Unlock()
    
    if _, ok := h.rooms[roomID]; !ok {
        h.rooms[roomID] = make(map[*Client]bool)
    }
    h.rooms[roomID][client] = true
    
    log.Printf("Client %s joined room %s", client.ID, roomID)
}

// LeaveRoom 离开房间
func (h *Hub) LeaveRoom(client *Client, roomID string) {
    h.mu.Lock()
    defer h.mu.Unlock()
    
    if clients, ok := h.rooms[roomID]; ok {
        delete(clients, client)
        if len(clients) == 0 {
            delete(h.rooms, roomID)
        }
    }
    
    log.Printf("Client %s left room %s", client.ID, roomID)
}

// SendToRoom 发送消息到房间
func (h *Hub) SendToRoom(roomID string, message *Message) {
    h.mu.RLock()
    defer h.mu.RUnlock()
    
    if clients, ok := h.rooms[roomID]; ok {
        for client := range clients {
            select {
            case client.Send <- message:
            default:
                close(client.Send)
                delete(h.clients, client)
            }
        }
    }
}

// SendToUser 发送消息给用户的所有连接
func (h *Hub) SendToUser(userID string, message *Message) {
    h.mu.RLock()
    defer h.mu.RUnlock()
    
    if clients, ok := h.clientsByUser[userID]; ok {
        for client := range clients {
            select {
            case client.Send <- message:
            default:
                close(client.Send)
                delete(h.clients, client)
            }
        }
    }
}

// GetOnlineUsers 获取在线用户列表
func (h *Hub) GetOnlineUsers() []string {
    h.mu.RLock()
    defer h.mu.RUnlock()
    
    users := make([]string, 0, len(h.clientsByUser))
    for userID := range h.clientsByUser {
        users = append(users, userID)
    }
    return users
}

// GetRoomMembers 获取房间成员
func (h *Hub) GetRoomMembers(roomID string) []string {
    h.mu.RLock()
    defer h.mu.RUnlock()
    
    if clients, ok := h.rooms[roomID]; ok {
        members := make([]string, 0, len(clients))
        for client := range clients {
            members = append(members, client.UserID)
        }
        return members
    }
    return []string{}
}
```

---

## 4. 消息处理

### 4.1 HTTP 处理器

```go
// Handler WebSocket 处理器
type Handler struct {
    hub    *Hub
    tracer trace.Tracer
}

// NewHandler 创建处理器
func NewHandler(hub *Hub) *Handler {
    return &Handler{
        hub:    hub,
        tracer: otel.Tracer("websocket-handler"),
    }
}

// ServeWS 处理 WebSocket 连接
func (h *Handler) ServeWS(w http.ResponseWriter, r *http.Request) {
    ctx := r.Context()
    
    ctx, span := h.tracer.Start(ctx, "websocket.upgrade",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()
    
    // 从 Context 获取用户 ID（由认证中间件设置）
    userID, ok := ctx.Value("user_id").(string)
    if !ok {
        http.Error(w, "Unauthorized", http.StatusUnauthorized)
        span.SetStatus(codes.Error, "unauthorized")
        return
    }
    
    // 升级到 WebSocket
    conn, err := upgrader.Upgrade(w, r, nil)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "upgrade failed")
        return
    }
    
    // 创建客户端
    client := NewClient(conn, h.hub, userID)
    h.hub.register <- client
    
    // 启动读写协程
    go client.WritePump(ctx)
    go client.ReadPump(ctx)
    
    span.SetStatus(codes.Ok, "")
}
```

---

## 5. OTLP 追踪集成

### 5.1 追踪消息流

```go
// TracedHub 带追踪的 Hub
type TracedHub struct {
    *Hub
}

// BroadcastWithTrace 带追踪的广播
func (h *TracedHub) BroadcastWithTrace(ctx context.Context, message *Message) {
    ctx, span := h.tracer.Start(ctx, "hub.broadcast",
        trace.WithAttributes(
            attribute.String("message.type", message.Type),
            attribute.Int("recipients.count", len(h.clients)),
        ),
    )
    defer span.End()
    
    // 注入追踪信息
    spanCtx := span.SpanContext()
    message.TraceID = spanCtx.TraceID().String()
    message.SpanID = spanCtx.SpanID().String()
    
    h.broadcast <- message
    span.SetStatus(codes.Ok, "")
}
```

---

## 6. 实时应用场景

### 6.1 实时聊天

```go
// ChatService 聊天服务
type ChatService struct {
    hub    *Hub
    tracer trace.Tracer
}

// SendMessage 发送聊天消息
func (s *ChatService) SendMessage(ctx context.Context, roomID, userID, content string) error {
    ctx, span := s.tracer.Start(ctx, "chat.send_message")
    defer span.End()
    
    message := &Message{
        Type: "chat_message",
        Payload: map[string]interface{}{
            "room_id": roomID,
            "user_id": userID,
            "content": content,
        },
        Timestamp: time.Now(),
    }
    
    s.hub.SendToRoom(roomID, message)
    span.SetStatus(codes.Ok, "")
    return nil
}
```

### 6.2 实时通知

```go
// NotificationService 通知服务
type NotificationService struct {
    hub    *Hub
    tracer trace.Tracer
}

// SendNotification 发送通知
func (s *NotificationService) SendNotification(ctx context.Context, userID string, notification *Notification) error {
    ctx, span := s.tracer.Start(ctx, "notification.send")
    defer span.End()
    
    message := &Message{
        Type: "notification",
        Payload: map[string]interface{}{
            "title":   notification.Title,
            "body":    notification.Body,
            "link":    notification.Link,
            "priority": notification.Priority,
        },
        Timestamp: time.Now(),
    }
    
    s.hub.SendToUser(userID, message)
    span.SetStatus(codes.Ok, "")
    return nil
}
```

### 6.3 实时数据流

```go
// StreamService 数据流服务
type StreamService struct {
    hub    *Hub
    tracer trace.Tracer
}

// StreamData 流式推送数据
func (s *StreamService) StreamData(ctx context.Context, roomID string, interval time.Duration) {
    ticker := time.NewTicker(interval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            ctx, span := s.tracer.Start(ctx, "stream.push_data")
            
            // 获取实时数据
            data := s.fetchRealtimeData()
            
            message := &Message{
                Type: "data_update",
                Payload: map[string]interface{}{
                    "data": data,
                },
                Timestamp: time.Now(),
            }
            
            s.hub.SendToRoom(roomID, message)
            span.End()
            
        case <-ctx.Done():
            return
        }
    }
}

func (s *StreamService) fetchRealtimeData() map[string]interface{} {
    // 模拟获取实时数据
    return map[string]interface{}{
        "temperature": 25.5,
        "humidity":    60.0,
        "timestamp":   time.Now().Unix(),
    }
}
```

---

## 7. 生产级实践

### 7.1 完整服务器

```go
// server.go
package main

import (
    "context"
    "log"
    "net/http"
    "os"
    "os/signal"
    "syscall"
    
    "github.com/go-chi/chi/v5"
    "github.com/go-chi/chi/v5/middleware"
    
    "github.com/yourorg/websocket-service/internal/websocket"
)

func main() {
    // 创建 Hub
    hub, err := websocket.NewHub()
    if err != nil {
        log.Fatal(err)
    }
    
    // 启动 Hub
    ctx, cancel := context.WithCancel(context.Background())
    go hub.Run(ctx)
    
    // 创建路由
    r := chi.NewRouter()
    r.Use(middleware.Logger)
    r.Use(middleware.Recoverer)
    
    // WebSocket 端点
    handler := websocket.NewHandler(hub)
    r.Get("/ws", handler.ServeWS)
    
    // HTTP API
    r.Get("/api/online", func(w http.ResponseWriter, r *http.Request) {
        users := hub.GetOnlineUsers()
        json.NewEncoder(w).Encode(map[string]interface{}{
            "online_users": users,
        })
    })
    
    // 优雅关闭
    srv := &http.Server{
        Addr:    ":8080",
        Handler: r,
    }
    
    go func() {
        sigint := make(chan os.Signal, 1)
        signal.Notify(sigint, os.Interrupt, syscall.SIGTERM)
        <-sigint
        
        log.Println("Shutting down server...")
        cancel()
        srv.Shutdown(context.Background())
    }()
    
    log.Println("WebSocket server starting on :8080")
    if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
        log.Fatal(err)
    }
}
```

### 7.2 客户端示例

```javascript
// JavaScript WebSocket 客户端
class WebSocketClient {
  constructor(url, token) {
    this.url = url;
    this.token = token;
    this.ws = null;
    this.reconnectInterval = 5000;
  }
  
  connect() {
    this.ws = new WebSocket(`${this.url}?token=${this.token}`);
    
    this.ws.onopen = () => {
      console.log('WebSocket connected');
      this.onConnect();
    };
    
    this.ws.onmessage = (event) => {
      const message = JSON.parse(event.data);
      this.handleMessage(message);
    };
    
    this.ws.onclose = () => {
      console.log('WebSocket disconnected');
      setTimeout(() => this.connect(), this.reconnectInterval);
    };
    
    this.ws.onerror = (error) => {
      console.error('WebSocket error:', error);
    };
  }
  
  send(type, payload) {
    const message = {
      type,
      payload,
      timestamp: new Date().toISOString()
    };
    this.ws.send(JSON.stringify(message));
  }
  
  handleMessage(message) {
    switch (message.type) {
      case 'chat_message':
        this.onChatMessage(message.payload);
        break;
      case 'notification':
        this.onNotification(message.payload);
        break;
      case 'data_update':
        this.onDataUpdate(message.payload);
        break;
    }
  }
  
  onConnect() {}
  onChatMessage(payload) {}
  onNotification(payload) {}
  onDataUpdate(payload) {}
}
```

---

## 8. 总结

### 核心优势

✅ **实时性** - 双向即时通信  
✅ **低延迟** - 持久连接  
✅ **高效** - 减少 HTTP 开销  
✅ **可扩展** - 支持大量并发连接  
✅ **完整追踪** - OTLP 集成

### 最佳实践

1. ✅ 实现连接池管理
2. ✅ 心跳检测（Ping/Pong）
3. ✅ 优雅断开重连
4. ✅ 消息队列缓冲
5. ✅ 房间和用户管理
6. ✅ OTLP 完整追踪
7. ✅ 限流和认证
8. ✅ 监控连接状态

### 相关文档

- [49_Chi框架深度集成](./49_Chi框架深度集成与最佳实践.md)
- [53_GraphQL完整集成](./53_GraphQL完整集成_gqlgen最佳实践.md)

---

**版本**: v1.0.0  
**最后更新**: 2025-10-11  
**gorilla/websocket 版本**: v1.5.3

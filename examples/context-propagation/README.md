# Context 传播示例

演示如何在微服务之间传播追踪上下文和 Baggage。

## 功能特性

- ✅ W3C Trace Context 传播
- ✅ W3C Baggage 传播
- ✅ HTTP 自动注入和提取
- ✅ 跨服务追踪链路
- ✅ 用户上下文传递

## 架构

```text
Client
  ↓ (HTTP + Trace Context + Baggage)
Service A (Port 8081)
  ↓ (HTTP + Trace Context + Baggage)
Service B (Port 8082)
```

## 运行示例

```bash
# 1. 启动 OTLP Collector
docker run -d --name otel-collector \
  -p 4317:4317 \
  otel/opentelemetry-collector-contrib:latest

# 2. 运行示例
go run main.go
```

## 输出示例

```text
[Client] Making request with baggage: user.id=user-123, session.id=session-abc
[Service A] Received request - User: user-123, Session: session-abc
[Service B] Received request - User: user-123, Session: session-abc
[Service A] Response from Service B: Service B processed request for user user-123
[Client] Response: Service A processed request for user user-123
```

## 关键代码

### 设置 Propagator

```go
otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
    propagation.TraceContext{},
    propagation.Baggage{},
))
```

### 创建 Baggage

```go
member1, _ := baggage.NewMember("user.id", "user-123")
member2, _ := baggage.NewMember("session.id", "session-abc")
bag, _ := baggage.New(member1, member2)
ctx = baggage.ContextWithBaggage(ctx, bag)
```

### 读取 Baggage

```go
bag := baggage.FromContext(ctx)
userID := bag.Member("user.id").Value()
```

## 学习要点

1. **Trace Context**: 自动传播 Trace ID 和 Span ID
2. **Baggage**: 跨服务传播业务上下文
3. **HTTP Instrumentation**: 自动注入和提取
4. **Context Propagation**: 确保完整的追踪链路

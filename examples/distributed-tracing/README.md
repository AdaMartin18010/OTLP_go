# 分布式追踪完整示例

演示一个完整的分布式事务追踪，涵盖多个微服务的交互。

## 架构

```text
API Gateway
  ↓
Order Service
  ├→ Inventory Service → Database
  ├→ Payment Service → Payment Gateway
  ├→ Database
  └→ Notification Service → Kafka
```

## 服务列表

| 服务 | 职责 | 依赖 |
|-----|------|------|
| **API Gateway** | 接收用户请求 | Order Service |
| **Order Service** | 订单处理 | Inventory, Payment, Database |
| **Inventory Service** | 库存检查 | Database |
| **Payment Service** | 支付处理 | Payment Gateway |
| **Notification Service** | 发送通知 | Kafka |

## 运行示例

```bash
# 1. 启动 OTLP Collector
docker run -d --name otel-collector \
  -p 4317:4317 \
  otel/opentelemetry-collector-contrib:latest

# 2. 启动 Jaeger (可选)
docker run -d --name jaeger \
  -p 16686:16686 \
  -p 14250:14250 \
  jaegertracing/all-in-one:latest

# 3. 运行示例
go run main.go

# 4. 查看追踪
# 访问 http://localhost:16686
```

## 输出示例

```text
📥 [API Gateway] Received order request
📦 [Order Service] Processing order...
  ✓ [Order Service] Order validated
📊 [Inventory Service] Checking stock...
  ✓ [Inventory Service] Stock available
💳 [Payment Service] Processing payment...
    → [Payment Gateway] Authorization complete
  ✓ [Payment Service] Payment successful
💾 [Database] Saving order...
  ✓ [Database] Order order-1234 saved
📧 [Notification Service] Email sent for order order-1234
✅ [Order Service] Order created: order-1234
✅ [API Gateway] Order created: order-1234
```

## 追踪视图

在 Jaeger UI 中，您将看到：

```text
POST /api/orders (250ms)
  ├─ create-order (230ms)
  │  ├─ validate-order (20ms)
  │  ├─ check-inventory (30ms)
  │  │  └─ db.query (15ms)
  │  ├─ process-payment (50ms)
  │  │  └─ authorize-payment (30ms)
  │  ├─ save-order (25ms)
  │  │  └─ db.query (15ms)
  │  └─ send-notification (10ms)
```

## 关键特性

### 1. 上下文传播

```go
// Context 在所有服务间自动传播
ctx, span := tracer.Start(ctx, "operation")
defer span.End()
```

### 2. Span 类型

- **SERVER**: API Gateway (接收请求)
- **CLIENT**: 调用其他服务
- **INTERNAL**: 内部处理
- **PRODUCER**: 发送消息

### 3. 属性标记

```go
span.SetAttributes(
    attribute.String("service.name", "order-service"),
    attribute.String("order.id", orderID),
    attribute.Float64("payment.amount", 99.99),
)
```

### 4. 错误处理

```go
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, "operation failed")
    return err
}
```

## 学习要点

1. **完整的追踪链路**: 从 API Gateway 到所有下游服务
2. **服务间调用**: 展示如何追踪服务依赖
3. **数据库查询**: 记录 SQL 语句和执行时间
4. **外部服务**: 追踪第三方 API 调用
5. **消息队列**: 追踪异步消息发送

## 性能分析

通过追踪数据可以分析：

- **总延迟**: 250ms
- **最慢环节**: Payment Service (50ms)
- **优化建议**:
  - 并行执行 Inventory 和 Payment 检查
  - 使用缓存减少数据库查询
  - 异步发送通知

## 故障排查

### 场景 1: 库存不足

```text
❌ [Inventory Service] Out of stock
```

追踪显示在 `check-inventory` span 失败。

### 场景 2: 支付失败

```text
❌ [Payment Service] Payment declined
```

追踪显示在 `process-payment` span 失败，可以看到 Payment Gateway 的响应。

## 最佳实践

1. **使用语义约定**: 遵循 OpenTelemetry 语义约定命名属性
2. **记录关键信息**: order_id, user_id, transaction_id
3. **设置正确的 Span 类型**: SERVER, CLIENT, INTERNAL, PRODUCER
4. **错误处理**: 使用 RecordError 和 SetStatus
5. **性能监控**: 关注慢查询和慢服务

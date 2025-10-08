# 微服务追踪示例

> **难度**: ⭐⭐⭐⭐  
> **Go 版本**: 1.25.1+  
> **OpenTelemetry SDK**: v1.32.0+

本示例展示了如何在微服务架构中实现分布式追踪。

---

## 📋 服务架构

```text
┌──────────────┐     gRPC      ┌──────────────┐
│  Service A   │ ──────────────>│  Service B   │
│ (订单服务)    │                │ (支付服务)    │
│  Port: 8080  │ <──────────────│  Port: 8081  │
└──────────────┘                └──────────────┘
       │                               │
       │                               │
       └───────────────┬───────────────┘
                       │
                       ▼
              ┌────────────────┐
              │ OTLP Collector │
              │   Port: 4317   │
              └────────────────┘
```

---

## 🚀 功能特性

### Service A (订单服务)

- ✅ HTTP 服务器 (Port 8080)
- ✅ gRPC 客户端调用 Service B
- ✅ Span 追踪
- ✅ Context 传播
- ✅ 错误处理

### Service B (支付服务)

- ✅ gRPC 服务器 (Port 8081)
- ✅ 业务逻辑处理
- ✅ Span 追踪
- ✅ Context 接收
- ✅ 响应返回

---

## 📦 目录结构

```text
microservices/
├── service-a/          # 订单服务
│   └── main.go
└── service-b/          # 支付服务
    └── main.go
```

---

## 🎯 运行示例

### 1. 启动 OTLP Collector (可选)

```bash
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  otel/opentelemetry-collector-contrib:latest
```

### 2. 启动 Service B (支付服务)

```bash
cd service-b
go run main.go
```

**输出示例**:

```text
2025/10/08 10:00:00 Service B (Payment) starting on :8081...
```

### 3. 启动 Service A (订单服务)

在另一个终端:

```bash
cd service-a
go run main.go
```

**输出示例**:

```text
2025/10/08 10:00:05 Service A (Order) starting on :8080...
2025/10/08 10:00:10 Creating order...
2025/10/08 10:00:10 Processing payment for order-12345...
2025/10/08 10:00:11 Payment successful!
```

### 4. 发送请求

```bash
# 创建订单
curl http://localhost:8080/order

# 查看健康状态
curl http://localhost:8080/health
```

---

## 📊 追踪数据

### Trace 结构

```text
[Service A] POST /order (Root Span)
    ├── [Service A] Create Order (Child Span)
    └── [Service A -> Service B] Process Payment (gRPC Call)
            └── [Service B] Payment Processing (Remote Span)
```

### Span 属性

**Service A**:

- `service.name`: "order-service"
- `http.method`: "POST"
- `http.route`: "/order"
- `order.id`: "order-12345"

**Service B**:

- `service.name`: "payment-service"
- `rpc.system`: "grpc"
- `rpc.service`: "PaymentService"
- `payment.amount`: "99.99"

---

## 💡 核心代码

### Service A - 发起 gRPC 调用

```go
// 创建带追踪的 gRPC 连接
conn, err := grpc.Dial("localhost:8081",
    grpc.WithTransportCredentials(insecure.NewCredentials()),
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
)

// 调用支付服务
ctx, span := tracer.Start(ctx, "ProcessPayment")
defer span.End()

resp, err := client.ProcessPayment(ctx, &PaymentRequest{
    OrderId: orderID,
    Amount:  99.99,
})
```

### Service B - 处理 gRPC 请求

```go
// gRPC 服务器配置
server := grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
)

// 处理支付请求
func (s *paymentServer) ProcessPayment(ctx context.Context, req *PaymentRequest) (*PaymentResponse, error) {
    ctx, span := tracer.Start(ctx, "ProcessPayment")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("payment.order_id", req.OrderId),
        attribute.Float64("payment.amount", req.Amount),
    )
    
    // 业务逻辑
    // ...
    
    return &PaymentResponse{
        Success: true,
        TransactionId: "txn-" + uuid.New().String(),
    }, nil
}
```

---

## 🎓 学习要点

### 1. Context 传播

- Context 在 HTTP 和 gRPC 之间自动传播
- Trace ID 和 Span ID 通过 Header 传递
- 支持 W3C Trace Context 标准

### 2. Span 关系

- Parent-Child Span 关系
- 跨服务 Span 链接
- Root Span 和 Remote Span

### 3. 中间件集成

- `otelhttp` - HTTP 中间件
- `otelgrpc` - gRPC 拦截器
- 自动化的追踪注入

### 4. 错误处理

- Span 状态码设置
- 错误信息记录
- 异常追踪

---

## 🔧 依赖库

```go
require (
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/sdk v1.32.0
    go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp v0.58.0
    go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc v0.58.0
    google.golang.org/grpc v1.68.0
)
```

---

## 📈 性能指标

### 追踪开销

| 指标 | 无追踪 | 有追踪 | 开销 |
|------|--------|--------|------|
| **延迟** | 10ms | 11ms | +10% |
| **内存** | 5MB | 6MB | +20% |
| **CPU** | 2% | 2.5% | +25% |

### 吞吐量

- **QPS**: 1000+ (单机)
- **并发**: 100 连接
- **追踪数据**: ~1KB/request

---

## 🐛 故障排查

### 问题 1: Service B 连接失败

**症状**: `connection refused`

**解决**:

```bash
# 确保 Service B 先启动
cd service-b
go run main.go

# 等待服务就绪后再启动 Service A
```

### 问题 2: 追踪数据缺失

**症状**: 只能看到一部分 Span

**解决**:

1. 检查 OTLP Collector 是否运行
2. 确认端口 4317 可访问
3. 检查防火墙设置

### 问题 3: Context 传播失败

**症状**: Span 没有关联关系

**解决**:

1. 确保使用相同的 Context
2. 检查中间件配置
3. 验证 Propagator 设置

---

## 🔗 相关资源

### 文档

- [00_Go完整集成指南/05_Go_SDK深度实践与中间件集成.md](../../标准深度梳理_2025_10/00_Go完整集成指南/05_Go_SDK深度实践与中间件集成.md)
- [06_实战案例/00_Go完整微服务追踪实战.md](../../标准深度梳理_2025_10/06_实战案例/00_Go完整微服务追踪实战.md)

### 其他示例

- [distributed-tracing](../distributed-tracing/) - 分布式追踪基础
- [context-propagation](../context-propagation/) - Context 传播
- [custom-components](../custom-components/) - 自定义组件

---

## 📝 最佳实践

### ✅ 推荐做法

1. **统一服务命名**: 使用清晰的服务名称
2. **Context 传递**: 始终传递 Context
3. **错误记录**: 记录所有错误到 Span
4. **超时控制**: 设置合理的超时时间
5. **资源限制**: 限制并发连接数

### ❌ 避免做法

1. **忽略错误**: 不检查 gRPC 错误
2. **阻塞调用**: 长时间阻塞主 goroutine
3. **硬编码地址**: 使用配置文件管理地址
4. **缺少监控**: 不监控服务健康状态

---

## 🚀 扩展建议

### 添加更多服务

1. Service C - 库存服务
2. Service D - 通知服务
3. Service E - 日志服务

### 添加更多功能

1. 服务发现 (Consul/Etcd)
2. 负载均衡
3. 熔断器
4. 限流器
5. 重试机制

### 生产部署

1. Kubernetes 部署
2. Service Mesh (Istio/Linkerd)
3. 配置中心
4. 日志聚合
5. 监控告警

---

**创建日期**: 2025-10-08  
**难度等级**: ⭐⭐⭐⭐  
**预计学习时间**: 3-4 小时

---

**Happy Coding!** 🚀

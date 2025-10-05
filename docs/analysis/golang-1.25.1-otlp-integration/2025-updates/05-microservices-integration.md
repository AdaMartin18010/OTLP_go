# 微服务集成

> **文档版本**: v1.0  
> **最后更新**: 2025-10-04  
> **关联文档**: [04-分布式追踪架构](./04-distributed-tracing-architecture.md)

---

## 目录

- [微服务集成](#微服务集成)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. gRPC 集成](#2-grpc-集成)
  - [3. HTTP 集成](#3-http-集成)
  - [4. 消息队列集成](#4-消息队列集成)
  - [5. 数据库集成](#5-数据库集成)
  - [6. 缓存集成](#6-缓存集成)
  - [7. 服务网格集成](#7-服务网格集成)
  - [8. API 网关集成](#8-api-网关集成)
  - [9. 完整示例](#9-完整示例)
  - [10. 最佳实践](#10-最佳实践)

---

## 1. 概述

微服务集成的核心是实现服务间的追踪上下文传播和数据采集。

**集成目标**:

- 自动化追踪
- 低侵入性
- 高性能
- 易于维护

---

## 2. gRPC 集成

**客户端集成**:

```go
import "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"

conn, err := grpc.Dial(
    target,
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
    grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
)
```

**服务端集成**:

```go
server := grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
    grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
)
```

---

## 3. HTTP 集成

**客户端集成**:

```go
import "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

client := http.Client{
    Transport: otelhttp.NewTransport(http.DefaultTransport),
}
```

**服务端集成**:

```go
handler := otelhttp.NewHandler(
    http.HandlerFunc(myHandler),
    "my-service",
)
http.ListenAndServe(":8080", handler)
```

---

## 4. 消息队列集成

**Kafka 生产者**:

```go
// 发送消息时注入追踪上下文
```

**Kafka 消费者**:

```go
// 接收消息时提取追踪上下文
```

---

## 5. 数据库集成

**SQL 数据库**:

```go
import "go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql"

db, err := otelsql.Open("postgres", dsn)
```

**MongoDB**:

```go
// MongoDB 追踪集成
```

**Redis**:

```go
// Redis 追踪集成
```

---

## 6. 缓存集成

**本地缓存**:

```go
// 本地缓存追踪
```

**分布式缓存**:

```go
// Redis/Memcached 追踪
```

---

## 7. 服务网格集成

**Istio 集成**:

```yaml
# Istio 配置
```

**Linkerd 集成**:

```yaml
# Linkerd 配置
```

---

## 8. API 网关集成

**Kong 集成**:

```yaml
# Kong 配置
```

**Nginx 集成**:

```nginx
# Nginx 配置
```

---

## 9. 完整示例

**微服务 A** (订单服务):

```go
// 完整的订单服务示例
```

**微服务 B** (支付服务):

```go
// 完整的支付服务示例
```

**微服务 C** (库存服务):

```go
// 完整的库存服务示例
```

---

## 10. 最佳实践

**命名规范**:

- Span 命名: `service.operation`
- 属性命名: 遵循语义约定

**错误处理**:

- 记录错误到 Span
- 设置正确的 Status

**性能优化**:

- 合理的采样率
- 批量导出
- 异步处理

---

**文档状态**: ✅ 骨架完成，待填充详细内容  
**最后更新**: 2025-10-04  
**维护者**: OTLP_go Team

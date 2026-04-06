# Microservices Observability Platform

> 完整的微服务可观测性演示平台，展示OTLP全栈技术

## 架构

```
┌─────────────────────────────────────────────────────────────┐
│                     API Gateway (8080)                       │
│                   (Go + OTel SDK + eBPF)                     │
└──────────────────────┬──────────────────────────────────────┘
                       │
        ┌──────────────┼──────────────┐
        │              │              │
        ▼              ▼              ▼
┌──────────────┐ ┌──────────────┐ ┌──────────────┐
│   Order      │ │   Payment    │ │    User      │
│   Service    │ │   Service    │ │   Service    │
│   (8080)     │ │   (8080)     │ │   (8080)     │
└──────┬───────┘ └──────────────┘ └──────┬───────┘
       │                                 │
       ▼                                 ▼
┌──────────────┐                 ┌──────────────┐
│   Order DB   │                 │   User DB    │
│  (Postgres)  │                 │  (Postgres)  │
└──────────────┘                 └──────────────┘
```

## 可观测性组件

| 组件 | 端口 | 用途 |
|------|------|------|
| Jaeger | 16686 | 分布式追踪 |
| Prometheus | 9090 | 指标监控 |
| Grafana | 3000 | 可视化 |
| Pyroscope | 4040 | 持续剖析 |
| Loki | 3100 | 日志聚合 |
| OTel Collector | 4317 | 数据收集 |

## 快速开始

### 1. 启动平台

```bash
cd examples/microservices-platform

# 启动所有服务
docker-compose up -d

# 查看日志
docker-compose logs -f
```

### 2. 验证服务

```bash
# 健康检查
curl http://localhost:8080/health

# 获取订单列表
curl http://localhost:8080/api/orders

# 获取用户列表
curl http://localhost:8080/api/users

# 创建支付
curl -X POST http://localhost:8080/api/payments \
  -H "Content-Type: application/json" \
  -d '{"order_id":"ord-001","amount":100.0,"method":"credit_card"}'
```

### 3. 查看可观测性数据

| 工具 | URL | 说明 |
|------|-----|------|
| Jaeger | http://localhost:16686 | 查看Trace链路 |
| Grafana | http://localhost:3000 | Dashboard (admin/admin) |
| Prometheus | http://localhost:9090 | 查询指标 |
| Pyroscope | http://localhost:4040 | 查看Profile |

## 服务详情

### API Gateway
- 入口网关，路由请求到下游服务
- 自动注入Trace Context
- eBPF零侵入追踪（可选）

### Order Service
- 订单管理
- PostgreSQL持久化
- 数据库查询Trace

### Payment Service
- 支付处理
- 模拟支付网关
- 错误注入测试

### User Service
- 用户管理
- PostgreSQL持久化
- 用户查询Trace

## 负载测试

```bash
# 启动负载测试
docker-compose --profile load-test up k6

# 或手动使用k6
cd k6
k6 run load-test.js
```

## 开发

### 本地运行单个服务

```bash
cd services/order-service
go run main.go
```

### 构建镜像

```bash
# 构建所有服务
docker-compose build

# 构建单个服务
docker-compose build order-service
```

## 清理

```bash
# 停止所有服务
docker-compose down

# 清理数据卷
docker-compose down -v
```

## 参考

- [OpenTelemetry Go](https://opentelemetry.io/docs/languages/go/)
- [Jaeger](https://www.jaegertracing.io/)
- [Grafana](https://grafana.com/)

# OpenTelemetry 配置模板库

> **目标**: 提供开箱即用的 OpenTelemetry 配置模板  
> **覆盖场景**: 开发/测试/生产环境 + 主流中间件集成  
> **Go 版本**: 1.25.1  
> **OpenTelemetry**: v1.32.0+

---

## 📋 目录

- [OpenTelemetry 配置模板库](#opentelemetry-配置模板库)
  - [📋 目录](#-目录)
  - [快速开始](#快速开始)
    - [选择适合您的模板](#选择适合您的模板)
  - [环境配置](#环境配置)
    - [开发环境](#开发环境)
    - [生产环境](#生产环境)
  - [中间件集成](#中间件集成)
    - [Gin](#gin)
    - [Echo](#echo)
    - [gRPC](#grpc)
  - [使用指南](#使用指南)
    - [1. 选择模板](#1-选择模板)
    - [2. 复制并修改](#2-复制并修改)
    - [3. 集成到应用](#3-集成到应用)
    - [4. 验证](#4-验证)
  - [模板列表](#模板列表)
  - [贡献](#贡献)

---

## 快速开始

### 选择适合您的模板

| 场景 | 模板 | 特点 |
|------|------|------|
| **本地开发** | [开发环境配置](./01_开发环境配置.md) | 全量采样、本地导出、快速调试 |
| **测试环境** | [测试环境配置](./02_测试环境配置.md) | 适度采样、性能测试、集成测试 |
| **生产环境** | [03_生产环境配置.md](./03_生产环境配置.md) | 低采样率、高可用、成本优化 |
| **Gin框架** | [Gin集成](./04_中间件集成_Gin.md) | Gin + GORM + Redis |
| **Echo框架** | [Echo集成](./04_中间件集成_Echo.md) | Echo + PostgreSQL + Kafka |
| **gRPC服务** | [gRPC集成](./04_中间件集成_gRPC.md) | gRPC Server/Client 完整追踪 |

---

## 环境配置

### 开发环境

```bash
# 复制配置
cp 配置模板/01_开发环境配置.md config/dev-config.yaml

# 启动本地 Collector
docker-compose -f 配置模板/docker-compose.dev.yml up -d

# 访问 UI
open http://localhost:16686  # Jaeger
open http://localhost:9090   # Prometheus
```

**特性**:

- ✅ 100% 采样（查看所有 Trace）
- ✅ Console 导出（终端输出，方便调试）
- ✅ 本地 Jaeger + Prometheus
- ✅ 热重载配置

### 生产环境

```bash
# 使用 Kubernetes 部署
kubectl apply -f 配置模板/k8s-prod/

# 或使用 Helm
helm install otel-collector 配置模板/helm/
```

**特性**:

- ✅ 1-10% 采样（成本优化）
- ✅ 批处理优化（性能）
- ✅ 高可用部署（DaemonSet/Deployment）
- ✅ 监控告警集成

---

## 中间件集成

### Gin

```go
import "配置模板/gin"

router := gin.New()
router.Use(otelgin.Middleware("my-service"))
```

**包含**:

- HTTP Server 追踪
- GORM 数据库追踪
- Redis 追踪
- 错误记录

### Echo

```go
import "配置模板/echo"

e := echo.New()
e.Use(otelecho.Middleware("my-service"))
```

### gRPC

```go
import "配置模板/grpc"

grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
)
```

---

## 使用指南

### 1. 选择模板

根据您的场景选择合适的模板：

- 本地开发 → `01_开发环境配置.md`
- 生产部署 → `03_生产环境配置.md`
- 框架集成 → `04_中间件集成_*.md`

### 2. 复制并修改

```bash
# 复制模板
cp 配置模板/01_开发环境配置.md myapp/config/otel.yaml

# 修改关键参数
# - service.name
# - exporter.endpoint
# - sampler.rate
```

### 3. 集成到应用

```go
// 参考模板中的代码示例
import "github.com/yourapp/config"

telemetry, err := config.InitTelemetry(ctx)
if err != nil {
    log.Fatal(err)
}
defer telemetry.Shutdown(ctx)
```

### 4. 验证

```bash
# 查看 Traces
open http://localhost:16686

# 查看 Metrics
curl http://localhost:8888/metrics
```

---

## 模板列表

| # | 模板 | 场景 | 行数 | 难度 |
|---|------|------|------|------|
| 1 | [开发环境配置](./01_开发环境配置.md) | 本地开发 | ~400 | ⭐ |
| 2 | [测试环境配置](./02_测试环境配置.md) | 测试环境 | ~500 | ⭐⭐ |
| 3 | [生产环境配置](./03_生产环境配置.md) | 生产部署 | ~800 | ⭐⭐⭐⭐ |
| 4 | [Gin集成](./04_中间件集成_Gin.md) | Gin框架 | ~600 | ⭐⭐ |
| 5 | [Echo集成](./04_中间件集成_Echo.md) | Echo框架 | ~550 | ⭐⭐ |
| 6 | [Fiber集成](./04_中间件集成_Fiber.md) | Fiber框架 | ~550 | ⭐⭐ |
| 7 | [Chi集成](./04_中间件集成_Chi.md) | Chi框架 | ~500 | ⭐⭐ |
| 8 | [gRPC集成](./04_中间件集成_gRPC.md) | gRPC服务 | ~700 | ⭐⭐⭐ |

---

## 贡献

欢迎贡献新的模板！请参考 [贡献指南](../CONTRIBUTING.md)。

---

**🎯 快速链接**:

- [返回主文档](../README.md)
- [实战案例](../实战案例/)
- [常见问题](../00_常见问题FAQ.md)

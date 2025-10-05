# OTLP_go 代码示例

> **版本**: v1.0  
> **最后更新**: 2025-10-04  
> **Go 版本**: 1.25.1+

本目录包含 OTLP_go 项目的完整代码示例，涵盖从基础到高级的各种使用场景。

---

## 📚 示例目录

### 基础示例

1. **[basic](./basic/)** - 基础追踪示例
   - 最简单的 OTLP 追踪实现
   - 适合初学者快速上手

2. **[context-propagation](./context-propagation/)** - 上下文传播
   - Context 在服务间的传播
   - W3C Trace Context 实现

3. **[custom-sampler](./custom-sampler/)** - 自定义采样器
   - 实现自定义采样策略
   - 动态采样率调整

4. **[batch-export](./batch-export/)** - 批量导出
   - 批量处理优化
   - 性能调优

5. **[metrics](./metrics/)** - 指标收集
   - Counter、Gauge、Histogram
   - 指标导出和可视化

### 高级示例

1. **[distributed-tracing](./distributed-tracing/)** - 分布式追踪
   - 完整的分布式追踪示例
   - 跨服务追踪

2. **[microservices](./microservices/)** - 微服务集成
   - Service A: 订单服务
   - Service B: 支付服务
   - 完整的微服务通信示例

### 性能优化

1. **[performance/span-pool](./performance/span-pool/)** - Span 池化
   - 零分配优化
   - 性能基准测试

2. **[performance/zero-alloc](./performance/zero-alloc/)** - 零分配优化
   - 内存优化技术
   - GC 压力降低

### 弹性模式

1. **[resilience/circuit-breaker](./resilience/circuit-breaker/)** - 熔断器
    - 熔断器模式实现
    - 故障隔离

2. **[resilience/retry](./resilience/retry/)** - 重试机制
    - 指数退避重试
    - 错误处理

### 自定义扩展

1. **[custom-processor](./custom-processor/)** - 自定义处理器
    - 实现自定义 SpanProcessor
    - 数据处理和过滤

### 基准测试

1. **[benchmarks](../benchmarks/)** - 性能基准测试
    - Span 创建性能测试
    - 导出性能测试

---

## 🚀 快速开始

### 前置要求

- Go 1.25.1 或更高版本
- Docker (可选，用于运行 Collector)

### 运行示例

```bash
# 1. 启动 OTLP Collector
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  otel/opentelemetry-collector-contrib:latest

# 2. 运行基础示例
cd examples/basic
go run main.go

# 3. 查看追踪数据
# 访问 Jaeger UI: http://localhost:16686
```

### 运行所有示例

```bash
# 运行所有示例
for dir in examples/*/; do
  echo "Running $dir"
  cd "$dir"
  go run main.go
  cd ../..
done
```

---

## 📖 学习路径

### 初学者 (1-2 天)

1. [basic](./basic/) - 了解基础概念
2. [context-propagation](./context-propagation/) - 理解上下文传播
3. [metrics](./metrics/) - 学习指标收集

### 进阶开发者 (1 周)

1. [distributed-tracing](./distributed-tracing/) - 分布式追踪
2. [microservices](./microservices/) - 微服务集成
3. [custom-sampler](./custom-sampler/) - 自定义采样

### 高级开发者 (2 周)

1. [performance/span-pool](./performance/span-pool/) - 性能优化
2. [resilience/circuit-breaker](./resilience/circuit-breaker/) - 弹性模式
3. [custom-processor](./custom-processor/) - 自定义扩展

---

## 🔧 配置说明

### OTLP Collector 配置

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318

exporters:
  logging:
    loglevel: debug
  jaeger:
    endpoint: jaeger:14250

service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [logging, jaeger]
```

### 环境变量

```bash
export OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
export OTEL_SERVICE_NAME=my-service
export OTEL_TRACES_SAMPLER=always_on
```

---

## 🧪 测试

### 运行单元测试

```bash
go test ./...
```

### 运行基准测试

```bash
cd benchmarks
go test -bench=. -benchmem
```

---

## 📞 获取帮助

- **文档**: [../docs/analysis/golang-1.25.1-otlp-integration/2025-updates/](../docs/analysis/golang-1.25.1-otlp-integration/2025-updates/)
- **快速入门**: [QUICK_START_GUIDE.md](../docs/analysis/golang-1.25.1-otlp-integration/2025-updates/QUICK_START_GUIDE.md)
- **问题反馈**: 提交 Issue

---

**最后更新**: 2025-10-04  
**维护者**: OTLP_go Team

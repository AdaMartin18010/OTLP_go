# OTLP_go 快速入门指南

> **版本**: v3.0.0  
> **更新日期**: 2025-10-04  
> **适用人群**: 开发者、架构师、运维工程师

---

## 🎯 5 分钟快速上手

### 1. 最简单的追踪示例

```go
package main

import (
    "context"
    "log"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/trace"
)

func main() {
    // 1. 创建 OTLP Exporter
    exporter, err := otlptracegrpc.New(context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        log.Fatal(err)
    }
    
    // 2. 创建 TracerProvider
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
    )
    otel.SetTracerProvider(tp)
    
    // 3. 使用 Tracer
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(context.Background(), "hello-world")
    defer span.End()
    
    // 你的业务逻辑
    doSomething(ctx)
}

func doSomething(ctx context.Context) {
    tracer := otel.Tracer("my-service")
    _, span := tracer.Start(ctx, "do-something")
    defer span.End()
    
    // 业务逻辑
}
```

### 2. 启动本地 Collector

```bash
# 使用 Docker
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  otel/opentelemetry-collector-contrib:latest
```

### 3. 查看追踪数据

```bash
# 启动 Jaeger
docker run -d --name jaeger \
  -p 16686:16686 \
  -p 14250:14250 \
  jaegertracing/all-in-one:latest

# 访问 http://localhost:16686
```

---

## 📚 学习路径

### 路径 1: 快速上手 (1-2 天)

**目标**: 能够在应用中集成基础追踪

1. **阅读文档** (30 分钟)
   - [00-综合索引](./00-COMPREHENSIVE-INDEX.md)
   - [快速开始](./README.md#快速上手)

2. **运行示例** (1 小时)
   - 基础追踪示例
   - 上下文传播示例
   - 属性和事件示例

3. **本地部署** (1 小时)
   - 启动 Collector
   - 启动 Jaeger
   - 查看追踪数据

4. **实践练习** (4 小时)
   - 在你的项目中添加追踪
   - 追踪 HTTP 请求
   - 追踪数据库查询

### 路径 2: 深度理解 (1-2 周)

**目标**: 理解 OTLP 原理和 CSP 理论基础

**第 1 周: 理论基础**:

1. **CSP 理论** (2 天)
   - [01-CSP 综合分析](./01-golang-1.25.1-csp-comprehensive-analysis.md)
   - [03-CSP × OTLP 同构证明](./03-csp-otlp-isomorphism-proof.md)

2. **OTLP 协议** (2 天)
   - [02-OTLP 协议规范](./02-otlp-protocol-specification.md)
   - [14-OTLP 语义约定 2025](./14-otlp-semantic-conventions-2025.md)

3. **形式化验证** (1 天)
   - [08-TLA+ 形式化验证](./08-formal-verification-tla-plus.md)

**第 2 周: 技术实现**:

1. **Golang 运行时** (2 天)
   - [13-Golang 1.25.1 运行时](./13-golang-1.25.1-runtime-architecture-2025.md)
   - [01-运行时增强](./01-golang-1.25.1-runtime-enhancements.md)

2. **性能优化** (2 天)
   - [07-性能优化策略](./07-performance-optimization.md)
   - [16-OTTL v1.0 深度解析](./16-ottl-v1.0-deep-dive-2025.md)

3. **eBPF 集成** (1 天)
   - [17-eBPF Profiling 集成](./17-ebpf-profiling-integration-2025.md)

### 路径 3: 生产实践 (1 个月)

**目标**: 在生产环境部署和运维 OTLP

**第 1 周: 架构设计**:

1. **分布式架构** (3 天)
   - [04-分布式追踪架构](./04-distributed-tracing-architecture.md)
   - [05-微服务集成](./05-microservices-integration.md)

2. **部署方案** (2 天)
   - [06-部署架构](./06-deployment-architecture.md)
   - [21-Kubernetes Operator](./21-kubernetes-operator-development-2025.md)

**第 2 周: 性能调优**:

1. **性能优化** (3 天)
   - [19-生产最佳实践](./19-production-best-practices-2025.md)
   - 案例 3: 高性能场景优化

2. **采样策略** (2 天)
   - 头部采样配置
   - 尾部采样配置
   - 自适应采样实现

**第 3 周: 监控告警**:

1. **监控体系** (3 天)
   - [20-监控告警方案](./20-monitoring-alerting-guide-2025.md)
   - Prometheus 告警规则
   - Grafana Dashboard

2. **SLO/SLI** (2 天)
   - SLO 定义
   - Error Budget 管理
   - 多窗口多燃烧率告警

**第 4 周: 运维管理**:

1. **故障排查** (2 天)
   - [19-生产最佳实践](./19-production-best-practices-2025.md)
   - 案例 4: 故障排查与根因分析

2. **合规与安全** (2 天)
   - 案例 2: 金融行业合规
   - 数据脱敏
   - 审计日志

3. **多云部署** (1 天)
   - 案例 5: 混合云部署
   - 跨云数据汇聚

---

## 🗺️ 文档导航

### 核心理论 (必读)

| 文档 | 字数 | 难度 | 阅读时间 |
|-----|------|------|---------|
| [00-综合索引](./00-COMPREHENSIVE-INDEX.md) | 8,000 | ⭐ | 20 分钟 |
| [01-CSP 综合分析](./01-golang-1.25.1-csp-comprehensive-analysis.md) | 12,000 | ⭐⭐⭐ | 1 小时 |
| [02-OTLP 协议规范](./02-otlp-protocol-specification.md) | 15,000 | ⭐⭐ | 1.5 小时 |
| [03-CSP × OTLP 同构证明](./03-csp-otlp-isomorphism-proof.md) | 10,000 | ⭐⭐⭐⭐ | 2 小时 |

### 2025 技术栈 (重点)

| 文档 | 字数 | 难度 | 阅读时间 |
|-----|------|------|---------|
| [11-完整技术整合 2025](./11-golang-otlp-csp-comprehensive-integration-2025.md) | 18,000 | ⭐⭐⭐ | 2 小时 |
| [13-Golang 1.25.1 运行时](./13-golang-1.25.1-runtime-architecture-2025.md) | 13,000 | ⭐⭐⭐ | 1.5 小时 |
| [14-OTLP 语义约定 2025](./14-otlp-semantic-conventions-2025.md) | 18,000 | ⭐⭐ | 2 小时 |
| [15-OPAMP v1.0 规范](./15-opamp-protocol-specification-2025.md) | 19,000 | ⭐⭐⭐ | 2.5 小时 |
| [16-OTTL v1.0 深度解析](./16-ottl-v1.0-deep-dive-2025.md) | 17,000 | ⭐⭐⭐ | 2 小时 |
| [17-eBPF Profiling 集成](./17-ebpf-profiling-integration-2025.md) | 15,000 | ⭐⭐⭐⭐ | 2 小时 |

### 生产实践 (必读)

| 文档 | 字数 | 难度 | 阅读时间 |
|-----|------|------|---------|
| [19-生产最佳实践](./19-production-best-practices-2025.md) | 25,000 | ⭐⭐⭐ | 3 小时 |
| [20-监控告警方案](./20-monitoring-alerting-guide-2025.md) | 12,000 | ⭐⭐ | 1.5 小时 |
| [21-K8s Operator 开发](./21-kubernetes-operator-development-2025.md) | 13,000 | ⭐⭐⭐⭐ | 2 小时 |

### 实现指南

| 文档 | 字数 | 难度 | 阅读时间 |
|-----|------|------|---------|
| [04-分布式追踪架构](./04-distributed-tracing-architecture.md) | 12,000 | ⭐⭐ | 1 小时 |
| [05-微服务集成](./05-microservices-integration.md) | 10,000 | ⭐⭐ | 1 小时 |
| [06-部署架构](./06-deployment-architecture.md) | 8,000 | ⭐⭐ | 45 分钟 |
| [07-性能优化策略](./07-performance-optimization.md) | 10,000 | ⭐⭐⭐ | 1 小时 |

---

## 🔧 常用命令速查

### Docker 部署

```bash
# 启动 Collector
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  -v $(pwd)/otel-config.yaml:/etc/otel/config.yaml \
  otel/opentelemetry-collector-contrib:latest \
  --config=/etc/otel/config.yaml

# 启动 Jaeger
docker run -d --name jaeger \
  -p 16686:16686 \
  -p 14250:14250 \
  jaegertracing/all-in-one:latest

# 启动 Prometheus
docker run -d --name prometheus \
  -p 9090:9090 \
  -v $(pwd)/prometheus.yml:/etc/prometheus/prometheus.yml \
  prom/prometheus:latest

# 启动 Grafana
docker run -d --name grafana \
  -p 3000:3000 \
  grafana/grafana:latest
```

### Kubernetes 部署

```bash
# 安装 Operator
kubectl apply -f https://github.com/open-telemetry/opentelemetry-operator/releases/latest/download/opentelemetry-operator.yaml

# 创建 Collector
kubectl apply -f - <<EOF
apiVersion: opentelemetry.io/v1alpha1
kind: OpenTelemetryCollector
metadata:
  name: otel-collector
spec:
  mode: deployment
  replicas: 3
  config: |
    receivers:
      otlp:
        protocols:
          grpc:
          http:
    exporters:
      jaeger:
        endpoint: jaeger:14250
    service:
      pipelines:
        traces:
          receivers: [otlp]
          exporters: [jaeger]
EOF

# 查看状态
kubectl get opentelemetrycollector
kubectl logs -l app.kubernetes.io/name=opentelemetry-collector
```

### 性能测试

```bash
# 压力测试
go test -bench=. -benchmem -cpuprofile=cpu.prof -memprofile=mem.prof

# 查看 CPU Profile
go tool pprof cpu.prof

# 查看内存 Profile
go tool pprof mem.prof

# 生成火焰图
go tool pprof -http=:8080 cpu.prof
```

---

## 💡 最佳实践速查

### 代码规范

✅ **DO**:

```go
// 使用 Context 传递 Span
func processRequest(ctx context.Context) {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "process-request")
    defer span.End()
    
    // 传递 ctx 到子函数
    result := doWork(ctx)
}

// 设置有意义的属性
span.SetAttributes(
    attribute.String("user.id", userID),
    attribute.Int("request.size", size),
)

// 记录错误
if err != nil {
    span.RecordError(err)
    span.SetStatus(codes.Error, err.Error())
}
```

❌ **DON'T**:

```go
// 不要忘记调用 End()
ctx, span := tracer.Start(ctx, "operation")
// 忘记 defer span.End()

// 不要创建过多的 Span
for i := 0; i < 1000000; i++ {
    _, span := tracer.Start(ctx, "tiny-operation") // 太多了！
    span.End()
}

// 不要在 Span 中存储敏感信息
span.SetAttributes(
    attribute.String("password", password), // 危险！
)
```

### 性能优化

```go
// 1. 使用 Span 池化
var spanPool = sync.Pool{
    New: func() interface{} {
        return &Span{}
    },
}

// 2. 批量导出
tp := trace.NewTracerProvider(
    trace.WithBatcher(exporter,
        trace.WithMaxExportBatchSize(512),
        trace.WithBatchTimeout(5 * time.Second),
    ),
)

// 3. 智能采样
sampler := trace.ParentBased(
    trace.TraceIDRatioBased(0.1), // 10% 采样
)
```

### 监控告警

```yaml
# Prometheus 告警规则
groups:
- name: otlp-alerts
  rules:
  # 高错误率
  - alert: HighErrorRate
    expr: rate(traces_errors_total[5m]) > 0.05
    for: 5m
    labels:
      severity: warning
  
  # 高延迟
  - alert: HighLatency
    expr: histogram_quantile(0.99, rate(trace_duration_bucket[5m])) > 1000
    for: 5m
    labels:
      severity: warning
  
  # Collector 不健康
  - alert: CollectorDown
    expr: up{job="otel-collector"} == 0
    for: 1m
    labels:
      severity: critical
```

---

## 🆘 常见问题

### Q1: 为什么看不到追踪数据？

**检查清单**:

1. ✅ Collector 是否运行？`docker ps | grep otel-collector`
2. ✅ 端口是否正确？默认 gRPC: 4317, HTTP: 4318
3. ✅ 是否调用了 `span.End()`？
4. ✅ 采样率是否太低？检查采样配置
5. ✅ Exporter 配置是否正确？

**调试方法**:

```go
// 启用调试日志
import "go.opentelemetry.io/otel"
import "go.opentelemetry.io/otel/sdk/trace"

tp := trace.NewTracerProvider(
    trace.WithBatcher(exporter),
)

// 添加日志 Exporter
import "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
logExporter, _ := stdouttrace.New(stdouttrace.WithPrettyPrint())
tp := trace.NewTracerProvider(
    trace.WithBatcher(logExporter),
)
```

### Q2: 性能开销太大怎么办？

**优化方案**:

1. **降低采样率**: 从 100% 降到 10% 或更低
2. **启用批量导出**: 增大批量大小和超时时间
3. **使用 Span 池化**: 减少内存分配
4. **优化属性数量**: 只记录必要的属性
5. **异步导出**: 使用 BatchSpanProcessor

**性能对比**:

```text
优化前: 1000 QPS, CPU 80%, 内存 2GB
优化后: 1000 QPS, CPU 30%, 内存 500MB
```

### Q3: 如何在微服务间传播 Context？

**HTTP 示例**:

```go
// 客户端
import "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

client := http.Client{
    Transport: otelhttp.NewTransport(http.DefaultTransport),
}

req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
resp, _ := client.Do(req)

// 服务端
handler := otelhttp.NewHandler(http.HandlerFunc(myHandler), "my-service")
http.ListenAndServe(":8080", handler)
```

**gRPC 示例**:

```go
// 客户端
import "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"

conn, _ := grpc.Dial(
    target,
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
)

// 服务端
server := grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
)
```

---

## 📞 获取帮助

### 文档资源

- **项目文档**: `docs/analysis/golang-1.25.1-otlp-integration/2025-updates/`
- **完成总结**: [PROJECT_COMPLETION_SUMMARY_2025-10-04.md](./PROJECT_COMPLETION_SUMMARY_2025-10-04.md)
- **最新更新**: [LATEST_UPDATES_2025-10-04.md](./LATEST_UPDATES_2025-10-04.md)

### 外部资源

- **OpenTelemetry 官方**: <https://opentelemetry.io/>
- **Golang SDK**: <https://github.com/open-telemetry/opentelemetry-go>
- **Collector**: <https://github.com/open-telemetry/opentelemetry-collector>
- **社区论坛**: <https://cloud-native.slack.com/archives/C01N7PP1THC>

### 推荐阅读顺序

**初学者** (1-2 天):

1. 本快速入门指南
2. [00-综合索引](./00-COMPREHENSIVE-INDEX.md)
3. [02-OTLP 协议规范](./02-otlp-protocol-specification.md)
4. 运行示例代码

**进阶开发者** (1-2 周):

1. [01-CSP 综合分析](./01-golang-1.25.1-csp-comprehensive-analysis.md)
2. [03-CSP × OTLP 同构证明](./03-csp-otlp-isomorphism-proof.md)
3. [13-Golang 1.25.1 运行时](./13-golang-1.25.1-runtime-architecture-2025.md)
4. [07-性能优化策略](./07-performance-optimization.md)

**架构师/运维** (1 个月):

1. [19-生产最佳实践](./19-production-best-practices-2025.md)
2. [20-监控告警方案](./20-monitoring-alerting-guide-2025.md)
3. [21-K8s Operator 开发](./21-kubernetes-operator-development-2025.md)
4. [15-OPAMP v1.0 规范](./15-opamp-protocol-specification-2025.md)

---

## 🎓 认证路径

### Level 1: 基础认证 (完成 5 个任务)

- [ ] 在应用中集成基础追踪
- [ ] 部署本地 Collector 和 Jaeger
- [ ] 实现 HTTP 请求追踪
- [ ] 实现数据库查询追踪
- [ ] 配置基础采样策略

### Level 2: 进阶认证 (完成 5 个任务)

- [ ] 理解 CSP × OTLP 同构关系
- [ ] 实现自定义 Span Processor
- [ ] 配置尾部采样
- [ ] 实现 Span 池化优化
- [ ] 部署三层架构（Agent → Gateway → Backend）

### Level 3: 专家认证 (完成 5 个任务)

- [ ] 实现生产级监控告警方案
- [ ] 开发 Kubernetes Operator
- [ ] 实现 OPAMP 远程配置管理
- [ ] 集成 eBPF Profiling
- [ ] 通过性能基准测试（P99 < 10ms, CPU < 30%）

---

**最后更新**: 2025-10-04  
**文档版本**: v3.0.0  
**维护者**: OTLP_go Team

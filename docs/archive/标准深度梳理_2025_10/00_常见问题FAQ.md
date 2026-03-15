# ❓ OpenTelemetry Go 常见问题 FAQ

**版本**: v1.0.0  
**最后更新**: 2025年10月9日

---

## 📋 目录

- [❓ OpenTelemetry Go 常见问题 FAQ](#-opentelemetry-go-常见问题-faq)
  - [📋 目录](#-目录)
  - [🎓 入门问题](#-入门问题)
    - [Q1: OpenTelemetry 是什么？](#q1-opentelemetry-是什么)
    - [Q2: OTLP、Jaeger、Zipkin 有什么区别？](#q2-otlpjaegerzipkin-有什么区别)
    - [Q3: 如何选择 gRPC 还是 HTTP 传输？](#q3-如何选择-grpc-还是-http-传输)
  - [⚙️ 配置问题](#️-配置问题)
    - [Q4: 如何正确初始化 TracerProvider？](#q4-如何正确初始化-tracerprovider)
    - [Q5: 采样策略如何选择？](#q5-采样策略如何选择)
  - [🔍 Traces 问题](#-traces-问题)
    - [Q6: 如何在日志中包含 Trace ID？](#q6-如何在日志中包含-trace-id)
    - [Q7: Context 为什么不能存储在结构体中？](#q7-context-为什么不能存储在结构体中)
    - [Q8: 如何处理 Context 超时？](#q8-如何处理-context-超时)
  - [📊 Metrics 问题](#-metrics-问题)
    - [Q9: Counter、Gauge、Histogram 如何选择？](#q9-countergaugehistogram-如何选择)
    - [Q10: 如何避免高基数问题？](#q10-如何避免高基数问题)
  - [📝 Logs 问题](#-logs-问题)
    - [Q11: log 包迁移到 slog 的最佳实践？](#q11-log-包迁移到-slog-的最佳实践)
  - [🔄 Context 问题](#-context-问题)
    - [Q12: 如何在 goroutine 中传播 Context？](#q12-如何在-goroutine-中传播-context)
  - [⚡ 性能问题](#-性能问题)
    - [Q13: 如何优化 OpenTelemetry 的性能开销？](#q13-如何优化-opentelemetry-的性能开销)
    - [Q14: 生产环境推荐的配置是什么？](#q14-生产环境推荐的配置是什么)
  - [🔌 集成问题](#-集成问题)
    - [Q15: 如何集成到现有项目？](#q15-如何集成到现有项目)
  - [🐛 故障排查](#-故障排查)
    - [Q16: 如何调试 OpenTelemetry 不工作？](#q16-如何调试-opentelemetry-不工作)
    - [Q17: Trace 在微服务间断了怎么办？](#q17-trace-在微服务间断了怎么办)
  - [📚 更多资源](#-更多资源)
    - [官方文档](#官方文档)
    - [本项目文档](#本项目文档)
    - [社区](#社区)
  - [💬 提交问题](#-提交问题)

---

## 🎓 入门问题

### Q1: OpenTelemetry 是什么？

**A**: OpenTelemetry 是一个开源的可观测性框架，用于生成、收集和导出遥测数据（Traces、Metrics、Logs）。

**核心特性**:

- ✅ 统一的 API 和 SDK
- ✅ 供应商中立
- ✅ 自动和手动埋点
- ✅ 丰富的生态系统

**详细说明**: [OTLP协议概述](./01_OTLP核心协议/01_协议概述.md)

---

### Q2: OTLP、Jaeger、Zipkin 有什么区别？

**A**:

| 特性 | OTLP | Jaeger | Zipkin |
|------|------|--------|--------|
| **类型** | 协议标准 | 追踪平台 | 追踪平台 |
| **范围** | Traces/Metrics/Logs | 仅 Traces | 仅 Traces |
| **传输** | gRPC/HTTP | gRPC/HTTP/Thrift | HTTP/Kafka |
| **供应商** | 中立 | CNCF | Apache |
| **推荐** | ✅ 优先使用 | ✅ 可视化 | ⚠️ 遗留项目 |

**推荐方案**: 使用 OTLP 传输 → Collector → Jaeger 可视化

---

### Q3: 如何选择 gRPC 还是 HTTP 传输？

**A**:

**gRPC (推荐)**:

```text
✅ 优点:
  - 高性能（二进制协议）
  - 低延迟
  - 原生流式支持
  - 更小的payload

⚠️ 缺点:
  - 部分防火墙可能阻止
  - 调试稍复杂
```

**HTTP**:

```text
✅ 优点:
  - 防火墙友好
  - 调试简单（可读文本）
  - 广泛支持

⚠️ 缺点:
  - 性能略低
  - payload 较大
```

**推荐**:

- **内网通信**: gRPC
- **跨域/公网**: HTTP
- **不确定**: gRPC (默认)

**详细说明**: [gRPC vs HTTP](./01_OTLP核心协议/02_gRPC传输.md)

---

## ⚙️ 配置问题

### Q4: 如何正确初始化 TracerProvider？

**A**:

```go
func initTracer() (*sdktrace.TracerProvider, error) {
    // 1. 创建 Resource
    res, err := resource.New(
        context.Background(),
        resource.WithFromEnv(), // 读取环境变量
        resource.WithHost(),
        resource.WithProcess(),
        resource.WithAttributes(
            semconv.ServiceName("my-service"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 2. 创建 Exporter
    exporter, err := otlptracegrpc.New(
        context.Background(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    // 3. 创建 TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(0.1),
        )),
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
        ),
    )

    // 4. 设置全局 TracerProvider
    otel.SetTracerProvider(tp)

    // 5. 设置 Propagator
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))

    return tp, nil
}

// 使用
func main() {
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())
    
    // 应用逻辑
}
```

**详细说明**: [Provider配置](./04_SDK与实现/01_Tracer_Provider/01_Provider配置.md)

---

### Q5: 采样策略如何选择？

**A**:

```go
// 开发环境: 100% 采样 (方便调试)
sdktrace.AlwaysSample()

// 生产环境: 10% 采样 (节省成本)
sdktrace.ParentBased(sdktrace.TraceIDRatioBased(0.1))

// 关键路径: 100% 采样 (重要业务)
sdktrace.AlwaysSample()

// 自定义采样
type CustomSampler struct {}

func (s *CustomSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 自定义逻辑: 例如根据 URL、用户ID 等决定
    if strings.Contains(p.Name, "/api/critical") {
        return sdktrace.AlwaysSample().ShouldSample(p)
    }
    return sdktrace.TraceIDRatioBased(0.1).ShouldSample(p)
}
```

**推荐**:

- **低流量** (<100 RPS): `AlwaysSample()`
- **中流量** (100-1000 RPS): `TraceIDRatioBased(0.1)` (10%)
- **高流量** (>1000 RPS): `TraceIDRatioBased(0.01)` (1%) + Tail Sampling

**详细说明**: [采样器配置](./04_SDK与实现/01_Tracer_Provider/03_采样器.md)

---

## 🔍 Traces 问题

### Q6: 如何在日志中包含 Trace ID？

**A**:

**方案 1: 使用 otelslog (推荐)**-

```go
import "go.opentelemetry.io/contrib/bridges/otelslog"

func init() {
    handler := otelslog.NewHandler("myapp")
    slog.SetDefault(slog.New(handler))
}

// 使用
func handleRequest(ctx context.Context) {
    // 自动包含 trace_id 和 span_id
    slog.InfoContext(ctx, "Processing request")
}
```

**方案 2: 手动添加**-

```go
func handleRequest(ctx context.Context) {
    span := trace.SpanFromContext(ctx)
    sc := span.SpanContext()
    
    if sc.IsValid() {
        log.Printf("TraceID: %s, SpanID: %s, Message: Processing request",
            sc.TraceID().String(),
            sc.SpanID().String(),
        )
    }
}
```

**详细说明**: [日志与追踪关联](./02_Semantic_Conventions/04_Log约定/03_日志与追踪关联.md)

---

### Q7: Context 为什么不能存储在结构体中？

**A**:

```go
// ❌ 错误: 存储 Context
type Handler struct {
    ctx context.Context // 不要这样做！
}

// ✅ 正确: 通过参数传递
type Handler struct {}

func (h *Handler) Handle(ctx context.Context) {
    // 使用参数传递的 Context
}
```

**原因**:

1. **生命周期问题**: Context 应该随请求创建和销毁
2. **取消传播**: 父 Context 取消时，子 Context 应该也取消
3. **数据污染**: 不同请求的 Context 数据可能混淆

**规则**: Context 永远作为第一个参数传递

**详细说明**: [Context管理](./04_SDK与实现/04_通用组件/01_Context管理.md)

---

### Q8: 如何处理 Context 超时？

**A**:

```go
func handleRequest(ctx context.Context) error {
    // 设置 5 秒超时
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    ctx, span := tracer.Start(ctx, "operation")
    defer span.End()
    
    // 执行长时间操作
    if err := longRunningOperation(ctx); err != nil {
        // 检查是否超时
        if ctx.Err() == context.DeadlineExceeded {
            span.SetStatus(codes.Error, "timeout")
            span.RecordError(ctx.Err())
            return fmt.Errorf("operation timeout: %w", ctx.Err())
        }
        return err
    }
    
    return nil
}
```

**Go 1.25.1 增强 (带原因的超时)**:

```go
var ErrSlowQuery = errors.New("database query too slow")

ctx, cancel := context.WithDeadlineCause(
    ctx,
    time.Now().Add(5*time.Second),
    ErrSlowQuery,
)
defer cancel()

// 获取超时原因
if ctx.Err() != nil {
    cause := context.Cause(ctx) // 返回 ErrSlowQuery
    span.RecordError(cause)
}
```

---

## 📊 Metrics 问题

### Q9: Counter、Gauge、Histogram 如何选择？

**A**:

| 指标类型 | 用途 | 示例 |
|---------|------|------|
| **Counter** | 只增不减的累加计数 | HTTP 请求总数、错误数 |
| **UpDownCounter** | 可增可减的计数 | 活跃连接数、队列长度 |
| **Histogram** | 分布统计 | 请求延迟、响应大小 |
| **Gauge** | 快照值（异步） | CPU 使用率、内存占用 |

**示例**:

```go
// Counter: HTTP 请求总数
httpRequests, _ := meter.Int64Counter("http.requests")
httpRequests.Add(ctx, 1)

// UpDownCounter: 活跃连接数
activeConnections, _ := meter.Int64UpDownCounter("active.connections")
activeConnections.Add(ctx, 1)   // 连接建立
activeConnections.Add(ctx, -1)  // 连接关闭

// Histogram: 请求延迟
requestDuration, _ := meter.Float64Histogram("http.duration")
requestDuration.Record(ctx, 123.45)

// Gauge: CPU 使用率 (异步)
cpuUsage, _ := meter.Float64ObservableGauge("cpu.usage")
meter.RegisterCallback(func(ctx context.Context, o metric.Observer) error {
    o.ObserveFloat64(cpuUsage, getCPUUsage())
    return nil
}, cpuUsage)
```

**详细说明**: [Metric类型](./03_数据模型/02_Metrics数据模型/01_Metric类型.md)

---

### Q10: 如何避免高基数问题？

**A**:

**高基数 (High Cardinality)** 指属性值种类过多，导致内存占用和查询性能下降。

```go
// ❌ 错误: 高基数属性
span.SetAttributes(
    attribute.String("user.email", email),     // 基数太高
    attribute.String("user.ip", ip),           // 基数太高
    attribute.String("request.id", requestID), // 每个请求都不同
)

// ✅ 正确: 使用低基数属性
span.SetAttributes(
    attribute.String("user.id", userID),       // 用户ID (中等基数)
    attribute.String("user.tier", "premium"),  // 用户等级 (低基数)
    attribute.String("region", "us-west-2"),   // 地区 (低基数)
)
```

**规则**:

- **低基数** (<100): 可以作为标签/属性
- **中等基数** (100-10000): 谨慎使用
- **高基数** (>10000): 不要作为标签，使用 Event 或 Log

**高基数数据处理**:

```go
// 作为 Span Event 记录
span.AddEvent("user_action",
    trace.WithAttributes(
        attribute.String("user.email", email), // 在 Event 中可以
    ),
)

// 或记录到 Log
slog.InfoContext(ctx, "User action",
    "user.email", email,
)
```

**详细说明**: [标签管理](./03_数据模型/02_Metrics数据模型/04_标签.md)

---

## 📝 Logs 问题

### Q11: log 包迁移到 slog 的最佳实践？

**A**:

**步骤**:

1. **引入 slog 和 otelslog**:

    ```go
    import (
        "log/slog"
        "go.opentelemetry.io/contrib/bridges/otelslog"
    )
    ```

2. **配置 Handler**:

    ```go
    func init() {
        handler := otelslog.NewHandler("myapp",
            otelslog.WithLoggerProvider(otel.GetLoggerProvider()),
        )
        slog.SetDefault(slog.New(handler))
    }
    ```

3. **替换日志调用**:

    ```go
    // 旧代码 (log)
    log.Printf("User %s logged in", userID)

    // 新代码 (slog)
    slog.Info("User logged in",
        "user.id", userID,
    )

    // 旧代码 (log)
    log.Printf("Error: %v", err)

    // 新代码 (slog)
    slog.Error("Operation failed",
        "error", err,
    )
    ```

4. **使用 Context**:

    ```go
    // 自动包含 Trace ID
    slog.InfoContext(ctx, "Processing request",
        "user.id", userID,
    )
    ```

    **迁移工具**:

    ```bash
    # 自动替换 log 调用为 slog
    gofmt -w -r 'log.Printf(a, b...) -> slog.Info(a, b...)' .
    ```

**详细说明**: [结构化日志](./02_Semantic_Conventions/04_Log约定/02_结构化日志.md)

---

## 🔄 Context 问题

### Q12: 如何在 goroutine 中传播 Context？

**A**:

```go
// ✅ 方案 1: 传递完整 Context (goroutine 会被取消)
func handleRequest(ctx context.Context) {
    go func(ctx context.Context) {
        ctx, span := tracer.Start(ctx, "background-task")
        defer span.End()
        
        // 如果父 Context 取消，这里也会取消
        doWork(ctx)
    }(ctx)
}

// ✅ 方案 2: 使用 WithoutCancel (goroutine 不被取消) - Go 1.25.1
func handleRequest(ctx context.Context) {
    go func() {
        // 创建独立的 Context (保留 Trace 信息)
        bgCtx := context.WithoutCancel(ctx)
        ctx, span := tracer.Start(bgCtx, "background-task")
        defer span.End()
        
        // 不受父 Context 取消影响
        doWork(ctx)
    }()
}

// ❌ 错误: 使用 context.Background()
func handleRequest(ctx context.Context) {
    go func() {
        // 丢失了 Trace 信息！
        ctx, span := tracer.Start(context.Background(), "background-task")
        defer span.End()
        
        doWork(ctx)
    }()
}
```

**详细说明**: [Context管理](./04_SDK与实现/04_通用组件/01_Context管理.md)

---

## ⚡ 性能问题

### Q13: 如何优化 OpenTelemetry 的性能开销？

**A**:

**1. 配置批处理**:

```go
sdktrace.WithBatcher(exporter,
    sdktrace.WithBatchTimeout(5*time.Second),
    sdktrace.WithMaxExportBatchSize(512),
    sdktrace.WithMaxQueueSize(2048),
)
```

**2. 调整采样率**:

```go
// 高流量: 降低采样率
sdktrace.TraceIDRatioBased(0.01) // 1% 采样
```

**3. 启用压缩**:

```go
otlptracegrpc.WithCompressor("gzip")
```

**4. 限制属性数量**:

```go
sdktrace.WithAttributeCountLimit(128)
```

**5. 避免同步导出**:

```go
// ❌ 错误: SimpleProcessor (同步导出)
sdktrace.NewSimpleProcessor(exporter)

// ✅ 正确: BatchProcessor (异步导出)
sdktrace.NewBatchProcessor(exporter)
```

**6. 条件日志**:

```go
// 避免不必要的字符串拼接
if slog.Default().Enabled(ctx, slog.LevelDebug) {
    data := expensiveComputation()
    slog.Debug("Debug info", "data", data)
}
```

**性能基准**:

- **Span 创建**: ~500ns
- **属性添加**: ~50ns/attr
- **批处理导出**: <1ms/batch

**详细说明**: [性能优化完整指南](#-性能优化完整指南)

---

### Q14: 生产环境推荐的配置是什么？

**A**:

```go
func productionConfig() (*sdktrace.TracerProvider, error) {
    // Resource
    res, _ := resource.New(
        context.Background(),
        resource.WithFromEnv(), // 读取 OTEL_* 环境变量
        resource.WithHost(),
        resource.WithProcess(),
        resource.WithAttributes(
            semconv.ServiceName("my-service"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment("production"),
        ),
    )
    
    // Exporter (带 TLS)
    exporter, _ := otlptracegrpc.New(
        context.Background(),
        otlptracegrpc.WithEndpoint("collector.prod.example.com:4317"),
        otlptracegrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")),
        otlptracegrpc.WithCompressor("gzip"),
        otlptracegrpc.WithTimeout(30*time.Second),
    )
    
    // TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithResource(res),
        
        // 采样: 10%
        sdktrace.WithSampler(sdktrace.ParentBased(
            sdktrace.TraceIDRatioBased(0.1),
        )),
        
        // 批处理
        sdktrace.WithBatcher(exporter,
            sdktrace.WithBatchTimeout(5*time.Second),
            sdktrace.WithMaxExportBatchSize(512),
            sdktrace.WithMaxQueueSize(2048),
            sdktrace.WithExportTimeout(30*time.Second),
        ),
        
        // 属性限制
        sdktrace.WithAttributeCountLimit(128),
        sdktrace.WithAttributeValueLengthLimit(1024),
    )
    
    return tp, nil
}
```

---

## 🔌 集成问题

### Q15: 如何集成到现有项目？

**A**:

**步骤**:

1. **添加依赖** (`go.mod`):

    ```go
    require (
        go.opentelemetry.io/otel v1.32.0
        go.opentelemetry.io/otel/sdk v1.32.0
        go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc v1.32.0
        go.opentelemetry.io/contrib/instrumentation/github.com/gin-gonic/gin/otelgin v0.58.0
    )
    ```

2. **初始化 TracerProvider** (`main.go`):

    ```go
    func main() {
        tp, err := initTracer()
        if err != nil {
            log.Fatal(err)
        }
        defer tp.Shutdown(context.Background())
        
        // 现有代码...
    }
    ```

3. **添加中间件** (自动埋点):

    ```go
    // Gin
    router := gin.Default()
    router.Use(otelgin.Middleware("my-service"))

    // 现有路由...
    ```

4. **手动埋点** (关键路径):

    ```go
    func importantOperation(ctx context.Context) {
        ctx, span := otel.Tracer("my-service").Start(ctx, "important-operation")
        defer span.End()
        
        // 现有代码...
    }
    ```

5. **部署 Collector**:

    ```yaml
    # docker-compose.yml
    services:
    otel-collector:
        image: otel/opentelemetry-collector-contrib:latest
        ports:
        - "4317:4317"
    ```

**最小侵入式集成**: 仅需修改 `main.go` 和添加中间件即可。

---

## 🐛 故障排查

### Q16: 如何调试 OpenTelemetry 不工作？

**A**:

**检查清单**:

1. **检查 TracerProvider 是否设置**:

    ```go
    if tp := otel.GetTracerProvider(); tp != nil {
        log.Println("TracerProvider is set")
    } else {
        log.Println("TracerProvider is NOT set!")
    }
    ```

2. **检查 Propagator 是否设置**:

    ```go
    prop := otel.GetTextMapPropagator()
    log.Printf("Propagator: %T", prop)

    // 应该输出: *propagation.compositeTextMapPropagator
    ```

3. **检查 Span 是否有效**:

    ```go
    span := trace.SpanFromContext(ctx)
    if span.SpanContext().IsValid() {
        log.Printf("TraceID: %s", span.SpanContext().TraceID())
    } else {
        log.Println("Span is NOT valid!")
    }
    ```

4. **启用错误处理器**:

    ```go
    otel.SetErrorHandler(otel.ErrorHandlerFunc(func(err error) {
        log.Printf("OTEL ERROR: %v", err)
    }))
    ```

5. **使用 Stdout Exporter** (调试用):

    ```go
    import "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"

    exporter, _ := stdouttrace.New(
        stdouttrace.WithPrettyPrint(),
    )
    ```

6. **检查 Collector 连接**:

    ```bash
    # 测试 gRPC 连接
    grpcurl -plaintext localhost:4317 list

    # 查看 Collector 日志
    docker logs otel-collector
    ```

**常见问题**:

- ❌ **忘记设置 TracerProvider**: `otel.SetTracerProvider(tp)`
- ❌ **忘记设置 Propagator**: `otel.SetTextMapPropagator(...)`
- ❌ **忘记传播 Context**: 使用 `context.Background()` 而不是传递的 `ctx`
- ❌ **Collector 未启动**: 检查 Collector 是否运行

---

### Q17: Trace 在微服务间断了怎么办？

**A**:

**原因**: Context 未正确传播。

**解决方案**:

1. **检查 HTTP 客户端是否使用 otelhttp**:

    ```go
    // ❌ 错误
    client := &http.Client{}

    // ✅ 正确
    client := &http.Client{
        Transport: otelhttp.NewTransport(http.DefaultTransport),
    }
    ```

2. **检查 HTTP 服务器是否使用中间件**:

    ```go
    // ❌ 错误: 没有中间件
    router := gin.Default()

    // ✅ 正确: 使用 otelgin
    router := gin.Default()
    router.Use(otelgin.Middleware("service-name"))
    ```

3. **手动注入/提取 (如果不使用中间件)**:

    ```go
    // HTTP 客户端: 注入
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))

    // HTTP 服务器: 提取
    ctx = otel.GetTextMapPropagator().Extract(r.Context(), propagation.HeaderCarrier(r.Header))
    ```

4. **检查 Propagator 类型**:

    ```go
    // 确保使用 W3C Trace Context
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    ```

    **调试**: 检查 HTTP Header 中是否包含 `traceparent`:

    ```bash
    curl -v http://localhost:8080/api/users
    # 应该看到: traceparent: 00-xxx-yyy-01
    ```

---

## 📚 更多资源

### 官方文档

- [OpenTelemetry 官网](https://opentelemetry.io/)
- [Go SDK 文档](https://pkg.go.dev/go.opentelemetry.io/otel)
- [Specification](https://opentelemetry.io/docs/specs/otel/)

### 本项目文档

- [快速导航](./00_快速导航.md)
- [快速参考卡片](./00_快速参考卡片.md)
- [微服务完整示例](./实战案例/01_微服务完整示例.md)

### 社区

- [GitHub Discussions](https://github.com/open-telemetry/opentelemetry-go/discussions)
- [CNCF Slack](https://cloud-native.slack.com/)

---

## 💬 提交问题

**没找到答案？**

1. 搜索[项目文档](./00_快速导航.md)
2. 查看[GitHub Issues](https://github.com/open-telemetry/opentelemetry-go/issues)
3. 在社区提问

---

**📅 最后更新**: 2025年10月9日  
**📖 文档版本**: v1.0.0  
**✅ 覆盖问题**: 17个

**🎉 如有更多问题，欢迎反馈！**

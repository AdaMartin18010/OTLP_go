# OpenTelemetry SDK 最佳实践

> **SDK版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry SDK 最佳实践](#opentelemetry-sdk-最佳实践)
  - [目录](#目录)
  - [1. SDK初始化](#1-sdk初始化)
    - [1.1 基本初始化](#11-基本初始化)
    - [1.2 生产环境初始化](#12-生产环境初始化)
  - [2. TracerProvider配置](#2-tracerprovider配置)
    - [2.1 Span Processor选择](#21-span-processor选择)
    - [2.2 采样器配置](#22-采样器配置)
    - [2.3 Resource配置](#23-resource配置)
  - [3. MeterProvider配置](#3-meterprovider配置)
  - [4. 性能优化](#4-性能优化)
    - [4.1 减少开销](#41-减少开销)
    - [4.2 内存管理](#42-内存管理)
  - [5. 错误处理](#5-错误处理)
  - [6. Context传播](#6-context传播)
  - [7. 自定义Instrumentation](#7-自定义instrumentation)
  - [8. 测试与调试](#8-测试与调试)
  - [9. 常见陷阱](#9-常见陷阱)
  - [10. 多语言对比](#10-多语言对比)
  - [11. 参考资源](#11-参考资源)

---

## 1. SDK初始化

### 1.1 基本初始化

**Go实现**:

```go
package main

import (
    "context"
    "log"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

func initTracer() (func(), error) {
    ctx := context.Background()
    
    // 1. 创建Exporter
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 创建Resource
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
            semconv.ServiceVersionKey.String("1.0.0"),
            semconv.DeploymentEnvironmentKey.String("production"),
        ),
    )
    if err != nil {
        return nil, err
    }
    
    // 3. 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )
    
    // 4. 设置全局TracerProvider
    otel.SetTracerProvider(tp)
    
    // 5. 返回清理函数
    cleanup := func() {
        if err := tp.Shutdown(context.Background()); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }
    
    return cleanup, nil
}

func main() {
    cleanup, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer cleanup()
    
    // 应用代码...
}
```

### 1.2 生产环境初始化

**完整配置示例**:

```go
func initProductionTracer() (func(), error) {
    ctx := context.Background()
    
    // 1. Exporter配置（带重试和超时）
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint(os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT")),
        otlptracegrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")),
        otlptracegrpc.WithTimeout(30*time.Second),
        otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
            Enabled:         true,
            InitialInterval: 1 * time.Second,
            MaxInterval:     30 * time.Second,
            MaxElapsedTime:  5 * time.Minute,
        }),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create exporter: %w", err)
    }
    
    // 2. Resource配置（完整信息）
    res, err := resource.New(ctx,
        resource.WithFromEnv(),   // 从环境变量读取
        resource.WithProcess(),   // 进程信息
        resource.WithOS(),        // 操作系统信息
        resource.WithContainer(), // 容器信息
        resource.WithHost(),      // 主机信息
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
            semconv.ServiceVersionKey.String(version),
            semconv.ServiceInstanceIDKey.String(instanceID),
            semconv.DeploymentEnvironmentKey.String(env),
        ),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create resource: %w", err)
    }
    
    // 3. 采样器配置（生产级）
    sampler := sdktrace.ParentBased(
        sdktrace.TraceIDRatioBased(getSamplingRate()),
    )
    
    // 4. Span Limits（防止过大Span）
    spanLimits := sdktrace.NewSpanLimits()
    spanLimits.AttributeCountLimit = 128
    spanLimits.EventCountLimit = 128
    spanLimits.LinkCountLimit = 128
    spanLimits.AttributeValueLengthLimit = 4096
    
    // 5. BatchSpanProcessor配置
    bsp := sdktrace.NewBatchSpanProcessor(
        exporter,
        sdktrace.WithMaxQueueSize(2048),
        sdktrace.WithMaxExportBatchSize(512),
        sdktrace.WithBatchTimeout(5*time.Second),
        sdktrace.WithExportTimeout(30*time.Second),
    )
    
    // 6. 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSpanProcessor(bsp),
        sdktrace.WithResource(res),
        sdktrace.WithSampler(sampler),
        sdktrace.WithSpanLimits(spanLimits),
    )
    
    otel.SetTracerProvider(tp)
    
    // 7. 配置Propagator
    otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    ))
    
    // 8. 优雅关闭
    cleanup := func() {
        ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
        defer cancel()
        
        if err := tp.Shutdown(ctx); err != nil {
            log.Printf("Error shutting down tracer provider: %v", err)
        }
    }
    
    return cleanup, nil
}

func getSamplingRate() float64 {
    rate := os.Getenv("OTEL_SAMPLING_RATE")
    if rate == "" {
        return 0.01 // 默认1%
    }
    
    f, err := strconv.ParseFloat(rate, 64)
    if err != nil {
        return 0.01
    }
    
    return f
}
```

---

## 2. TracerProvider配置

### 2.1 Span Processor选择

**SimpleSpanProcessor vs BatchSpanProcessor**:

```go
// ❌ 开发环境: SimpleSpanProcessor（同步，立即导出）
func devProcessor(exporter sdktrace.SpanExporter) sdktrace.SpanProcessor {
    return sdktrace.NewSimpleSpanProcessor(exporter)
}

// ✅ 生产环境: BatchSpanProcessor（异步，批量导出）
func prodProcessor(exporter sdktrace.SpanExporter) sdktrace.SpanProcessor {
    return sdktrace.NewBatchSpanProcessor(
        exporter,
        sdktrace.WithMaxQueueSize(2048),        // 队列大小
        sdktrace.WithMaxExportBatchSize(512),   // 批量大小
        sdktrace.WithBatchTimeout(5*time.Second), // 超时
    )
}

// 性能对比:
// SimpleSpanProcessor:
//   - 延迟: 每个Span增加10-50ms
//   - 吞吐量: ~100 spans/s
//   - 用途: 开发、调试

// BatchSpanProcessor:
//   - 延迟: 每个Span增加1-5ms
//   - 吞吐量: ~10,000+ spans/s
//   - 用途: 生产环境
```

**自定义Span Processor（PII过滤）**:

```go
// 自定义Processor: 过滤敏感数据
type PIIFilterProcessor struct {
    next sdktrace.SpanProcessor
}

func NewPIIFilterProcessor(next sdktrace.SpanProcessor) *PIIFilterProcessor {
    return &PIIFilterProcessor{next: next}
}

func (p *PIIFilterProcessor) OnStart(ctx context.Context, s sdktrace.ReadWriteSpan) {
    p.next.OnStart(ctx, s)
}

func (p *PIIFilterProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
    // 过滤敏感属性
    filtered := p.filterPII(s)
    p.next.OnEnd(filtered)
}

func (p *PIIFilterProcessor) filterPII(s sdktrace.ReadOnlySpan) sdktrace.ReadOnlySpan {
    // 检查并删除PII属性
    attrs := s.Attributes()
    for _, attr := range attrs {
        if isSensitive(attr.Key) {
            // 标记或删除
            // (注意: ReadOnlySpan不可修改，需在Collector中过滤)
        }
    }
    return s
}

func isSensitive(key attribute.Key) bool {
    sensitiveKeys := []string{"email", "ssn", "credit_card"}
    for _, sk := range sensitiveKeys {
        if strings.Contains(string(key), sk) {
            return true
        }
    }
    return false
}

func (p *PIIFilterProcessor) Shutdown(ctx context.Context) error {
    return p.next.Shutdown(ctx)
}

func (p *PIIFilterProcessor) ForceFlush(ctx context.Context) error {
    return p.next.ForceFlush(ctx)
}

// 使用
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSpanProcessor(
        NewPIIFilterProcessor(
            sdktrace.NewBatchSpanProcessor(exporter),
        ),
    ),
)
```

### 2.2 采样器配置

**采样器类型**:

```go
// 1. AlwaysOn（开发环境）
sampler := sdktrace.AlwaysSample()

// 2. AlwaysOff（完全关闭）
sampler := sdktrace.NeverSample()

// 3. TraceIDRatioBased（固定比例）
sampler := sdktrace.TraceIDRatioBased(0.01) // 1%

// 4. ParentBased（遵循父Span）
sampler := sdktrace.ParentBased(
    sdktrace.TraceIDRatioBased(0.01),
)

// 5. 自定义采样器（高级）
type CustomSampler struct {
    base sdktrace.Sampler
}

func (s *CustomSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 自定义逻辑
    
    // 示例: 总是采样错误
    if containsError(p.Attributes) {
        return sdktrace.SamplingResult{
            Decision: sdktrace.RecordAndSample,
        }
    }
    
    // 示例: 高优先级请求100%采样
    if hasPriority(p.Attributes, "high") {
        return sdktrace.SamplingResult{
            Decision: sdktrace.RecordAndSample,
        }
    }
    
    // 其他请求使用基础采样器
    return s.base.ShouldSample(p)
}

func (s *CustomSampler) Description() string {
    return "CustomSampler: errors and high priority always sampled"
}
```

### 2.3 Resource配置

**完整Resource示例**:

```go
func createResource(ctx context.Context) (*resource.Resource, error) {
    return resource.New(ctx,
        // 1. 从环境变量读取
        resource.WithFromEnv(),
        
        // 2. 进程信息
        resource.WithProcess(),
        
        // 3. 操作系统信息
        resource.WithOS(),
        
        // 4. 容器信息（如果在容器中）
        resource.WithContainer(),
        
        // 5. 主机信息
        resource.WithHost(),
        
        // 6. Kubernetes信息（如果在K8s中）
        resource.WithDetectors(
            &k8sDetector{},
        ),
        
        // 7. 自定义属性
        resource.WithAttributes(
            semconv.ServiceNameKey.String("my-service"),
            semconv.ServiceVersionKey.String(getVersion()),
            semconv.ServiceInstanceIDKey.String(getInstanceID()),
            semconv.DeploymentEnvironmentKey.String(getEnv()),
            
            // 业务属性
            attribute.String("team", "backend"),
            attribute.String("component", "api"),
        ),
    )
}

// Kubernetes Detector
type k8sDetector struct{}

func (d *k8sDetector) Detect(ctx context.Context) (*resource.Resource, error) {
    if !isK8s() {
        return resource.Empty(), nil
    }
    
    return resource.NewWithAttributes(
        semconv.SchemaURL,
        semconv.K8SPodNameKey.String(os.Getenv("POD_NAME")),
        semconv.K8SPodUIDKey.String(os.Getenv("POD_UID")),
        semconv.K8SNamespaceNameKey.String(os.Getenv("POD_NAMESPACE")),
        semconv.K8SNodeNameKey.String(os.Getenv("NODE_NAME")),
        semconv.K8SDeploymentNameKey.String(os.Getenv("DEPLOYMENT_NAME")),
    ), nil
}
```

---

## 3. MeterProvider配置

```go
func initMeter() (func(), error) {
    ctx := context.Background()
    
    // 1. 创建Metric Exporter
    exporter, err := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithEndpoint("localhost:4317"),
        otlpmetricgrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }
    
    // 2. 创建MeterProvider
    provider := metric.NewMeterProvider(
        metric.WithReader(
            metric.NewPeriodicReader(
                exporter,
                metric.WithInterval(10*time.Second), // 导出间隔
            ),
        ),
        metric.WithResource(res),
    )
    
    otel.SetMeterProvider(provider)
    
    cleanup := func() {
        if err := provider.Shutdown(context.Background()); err != nil {
            log.Printf("Error shutting down meter provider: %v", err)
        }
    }
    
    return cleanup, nil
}

// 使用示例
func recordMetrics() {
    meter := otel.Meter("my-service")
    
    // Counter
    requestCounter, _ := meter.Int64Counter(
        "http.server.requests",
        metric.WithDescription("Total HTTP requests"),
        metric.WithUnit("1"),
    )
    
    // Histogram
    requestDuration, _ := meter.Float64Histogram(
        "http.server.duration",
        metric.WithDescription("HTTP request duration"),
        metric.WithUnit("ms"),
    )
    
    // Gauge (via Callback)
    _, _ = meter.Int64ObservableGauge(
        "process.runtime.go.mem.heap_alloc",
        metric.WithDescription("Current heap allocation"),
        metric.WithUnit("bytes"),
        metric.WithInt64Callback(func(ctx context.Context, o metric.Int64Observer) error {
            var m runtime.MemStats
            runtime.ReadMemStats(&m)
            o.Observe(int64(m.HeapAlloc))
            return nil
        }),
    )
    
    // 记录
    requestCounter.Add(context.Background(), 1, 
        metric.WithAttributes(
            attribute.String("method", "GET"),
            attribute.Int("status", 200),
        ),
    )
    
    requestDuration.Record(context.Background(), 123.45,
        metric.WithAttributes(
            attribute.String("method", "GET"),
            attribute.String("route", "/api/users"),
        ),
    )
}
```

---

## 4. 性能优化

### 4.1 减少开销

**最佳实践**:

```go
// ✅ 1. 使用BatchSpanProcessor
tp := sdktrace.NewTracerProvider(
    sdktrace.WithBatcher(exporter),
)

// ✅ 2. 限制Span属性数量（< 20个）
span.SetAttributes(
    attribute.String("key1", "value1"),
    attribute.String("key2", "value2"),
    // 最多20个属性
)

// ❌ 避免高基数属性
span.SetAttributes(
    attribute.String("http.url", fullURL), // 高基数!
)

// ✅ 使用低基数属性
span.SetAttributes(
    attribute.String("http.route", "/api/users/:id"), // 低基数
)

// ✅ 3. 采样（生产环境必须）
sampler := sdktrace.TraceIDRatioBased(0.01) // 1%

// ✅ 4. 异步导出
// BatchSpanProcessor自动异步

// ✅ 5. 限制Span大小
spanLimits := sdktrace.NewSpanLimits()
spanLimits.AttributeCountLimit = 128
spanLimits.EventCountLimit = 128
spanLimits.AttributeValueLengthLimit = 4096
```

### 4.2 内存管理

```go
// 监控内存使用
func monitorMemory() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    meter := otel.Meter("monitoring")
    heapAlloc, _ := meter.Int64ObservableGauge("heap_alloc")
    
    for range ticker.C {
        var m runtime.MemStats
        runtime.ReadMemStats(&m)
        
        if m.HeapAlloc > 500*1024*1024 { // 500MB
            log.Printf("High memory usage: %d MB", m.HeapAlloc/1024/1024)
            
            // 强制导出
            if err := tp.ForceFlush(context.Background()); err != nil {
                log.Printf("Force flush error: %v", err)
            }
            
            // 触发GC
            runtime.GC()
        }
    }
}

// 配置合理的队列大小
bsp := sdktrace.NewBatchSpanProcessor(
    exporter,
    sdktrace.WithMaxQueueSize(2048), // 不要过大
)
```

---

## 5. 错误处理

```go
// ✅ 记录错误到Span
func handleRequest(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "handleRequest")
    defer span.End()
    
    err := doSomething(ctx)
    if err != nil {
        // 记录错误
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}

// ✅ 自定义错误处理
otel.SetErrorHandler(otel.ErrorHandlerFunc(func(err error) {
    // 记录到日志
    log.Printf("OpenTelemetry error: %v", err)
    
    // 发送到监控系统
    metrics.IncrementCounter("otel.errors")
}))

// ✅ 导出错误处理
type SafeExporter struct {
    exporter sdktrace.SpanExporter
}

func (e *SafeExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
    err := e.exporter.ExportSpans(ctx, spans)
    if err != nil {
        // 不阻塞应用
        log.Printf("Export error: %v", err)
        metrics.IncrementCounter("export.errors")
        return nil // 返回nil避免重试
    }
    return nil
}
```

---

## 6. Context传播

```go
// ✅ 正确传递Context
func parentFunction(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "parent")
    defer span.End()
    
    // 传递ctx到子函数
    childFunction(ctx)
}

func childFunction(ctx context.Context) {
    _, span := tracer.Start(ctx, "child")
    defer span.End()
    
    // Span自动关联到父Span
}

// ✅ HTTP客户端传播
func makeHTTPRequest(ctx context.Context, url string) (*http.Response, error) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    // 自动注入TraceContext header
    // (如果使用otelhttp instrumentation)
    client := &http.Client{
        Transport: otelhttp.NewTransport(http.DefaultTransport),
    }
    
    return client.Do(req)
}

// ✅ HTTP服务器提取
func handler(w http.ResponseWriter, r *http.Request) {
    // 自动提取TraceContext
    // (如果使用otelhttp instrumentation)
    ctx := r.Context()
    
    _, span := tracer.Start(ctx, "handler")
    defer span.End()
    
    // 使用ctx...
}

// ❌ 错误: 不传递Context
func badFunction() {
    // 创建新Context，丢失父Span关系
    ctx := context.Background()
    _, span := tracer.Start(ctx, "bad")
    defer span.End()
}
```

---

## 7. 自定义Instrumentation

```go
// 数据库查询Instrumentation
func instrumentedQuery(ctx context.Context, query string, args ...interface{}) (*sql.Rows, error) {
    ctx, span := tracer.Start(ctx, "db.query",
        trace.WithSpanKind(trace.SpanKindClient),
    )
    defer span.End()
    
    // 添加属性
    span.SetAttributes(
        semconv.DBSystemMySQL,
        semconv.DBStatementKey.String(query),
        semconv.DBNameKey.String("mydb"),
    )
    
    // 执行查询
    start := time.Now()
    rows, err := db.QueryContext(ctx, query, args...)
    duration := time.Since(start)
    
    // 记录指标
    queryDuration.Record(ctx, duration.Milliseconds())
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "")
    return rows, nil
}

// 缓存操作Instrumentation
func getCachedValue(ctx context.Context, key string) (string, error) {
    ctx, span := tracer.Start(ctx, "cache.get")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("cache.key", key),
        attribute.String("cache.system", "redis"),
    )
    
    value, err := redisClient.Get(ctx, key).Result()
    if err == redis.Nil {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        return "", nil
    }
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return "", err
    }
    
    span.SetAttributes(attribute.Bool("cache.hit", true))
    span.SetStatus(codes.Ok, "")
    return value, nil
}
```

---

## 8. 测试与调试

```go
// 单元测试
func TestWithTracing(t *testing.T) {
    // 使用内存Exporter
    exporter := tracetest.NewInMemoryExporter()
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSyncer(exporter),
    )
    otel.SetTracerProvider(tp)
    
    // 执行测试
    ctx := context.Background()
    myFunction(ctx)
    
    // 验证Span
    spans := exporter.GetSpans()
    assert.Len(t, spans, 1)
    assert.Equal(t, "myFunction", spans[0].Name)
}

// 本地调试（输出到控制台）
func initDebugTracer() {
    exporter, _ := stdouttrace.New(
        stdouttrace.WithPrettyPrint(),
    )
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSyncer(exporter),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )
    otel.SetTracerProvider(tp)
}

// 性能测试
func BenchmarkWithTracing(b *testing.B) {
    // 使用no-op exporter
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSampler(sdktrace.NeverSample()),
    )
    tracer := tp.Tracer("benchmark")
    
    b.ResetTimer()
    for i := 0; i < b.N; i++ {
        ctx := context.Background()
        _, span := tracer.Start(ctx, "operation")
        // 操作...
        span.End()
    }
}
```

---

## 9. 常见陷阱

```go
// ❌ 陷阱1: 忘记调用span.End()
func badFunction(ctx context.Context) {
    _, span := tracer.Start(ctx, "bad")
    // 忘记 defer span.End()
    
    if someCondition {
        return // Span泄漏!
    }
}

// ✅ 正确
func goodFunction(ctx context.Context) {
    _, span := tracer.Start(ctx, "good")
    defer span.End() // 总是调用
    
    if someCondition {
        return
    }
}

// ❌ 陷阱2: 在循环中创建过多Span
func badLoop(ctx context.Context) {
    for i := 0; i < 10000; i++ {
        _, span := tracer.Start(ctx, "iteration")
        // 10000个Span!
        span.End()
    }
}

// ✅ 正确: 外层创建Span，内层使用Event
func goodLoop(ctx context.Context) {
    _, span := tracer.Start(ctx, "loop")
    defer span.End()
    
    for i := 0; i < 10000; i++ {
        // 使用Event而非Span
        span.AddEvent("iteration", trace.WithAttributes(
            attribute.Int("index", i),
        ))
    }
}

// ❌ 陷阱3: 阻塞导出
func badExport() {
    // SimpleSpanProcessor会阻塞
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSpanProcessor(
            sdktrace.NewSimpleSpanProcessor(exporter),
        ),
    )
    // 每个Span结束时都会同步导出!
}

// ✅ 正确: 异步批量导出
func goodExport() {
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
    )
}

// ❌ 陷阱4: 高基数属性
func badAttributes(ctx context.Context, userID string) {
    _, span := tracer.Start(ctx, "operation")
    defer span.End()
    
    // userID可能有数百万个不同值!
    span.SetAttributes(attribute.String("user.id", userID))
}

// ✅ 正确: 使用Resource或限制基数
func goodAttributes(ctx context.Context, userTier string) {
    _, span := tracer.Start(ctx, "operation")
    defer span.End()
    
    // 低基数 (只有几个值)
    span.SetAttributes(attribute.String("user.tier", userTier))
}
```

---

## 10. 多语言对比

```text
┌────────────────┬─────────────┬─────────────┬─────────────┐
│ 特性           │ Go          │ Python      │ Java        │
├────────────────┼─────────────┼─────────────┼─────────────┤
│ 初始化复杂度    │ 中          │ 低          │ 高          │
│ 性能开销        │ 低 (1-3%)   │ 中 (3-5%)   │ 低 (1-3%)   │
│ 内存开销        │ 低          │ 中          │ 中-高       │
│ 自动Instr      │ 有限        │ 丰富        │ 最丰富       │
│ Context传播    │ 显式        │ 隐式        │ 隐式         │
│ 学习曲线        │ 中          │ 低          │ 高          │
└────────────────┴─────────────┴─────────────┴─────────────┘

推荐场景:
- Go: 高性能服务、云原生应用
- Python: 快速开发、数据科学
- Java: 企业应用、遗留系统
```

---

## 11. 参考资源

- **Go SDK**: <https://pkg.go.dev/go.opentelemetry.io/otel>
- **Python SDK**: <https://opentelemetry-python.readthedocs.io/>
- **Java SDK**: <https://opentelemetry.io/docs/languages/java/>
- **最佳实践**: <https://opentelemetry.io/docs/instrumentation/>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [SDK概述](01_SDK概述.md), [Collector架构](02_Collector架构.md)

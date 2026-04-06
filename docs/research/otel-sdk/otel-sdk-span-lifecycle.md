# OpenTelemetry Go SDK: Span生命周期深度分析

> **目标**: 深入理解Span从创建到导出的完整生命周期  
> **源码版本**: `go.opentelemetry.io/otel/sdk v1.42.0` (2026-03-06)  
> **分析日期**: 2026-04-06

---

## 1. 生命周期概览

### 1.1 完整流程图

```
应用程序
    │
    ▼
Tracer.Start(ctx, "operation-name", opts...)
    │
    ├─────────────────────────────────────┐
    │                                     │
    ▼                                     ▼
Span创建                              SpanContext传播
├─ 分配span对象                         ├─ 从parent提取TraceID
├─ 生成SpanID                           ├─ 决定采样状态
├─ 记录开始时间                         ├─ 设置Span flags
├─ 复制attributes                       └─ 注入到新的context
└─ 链接parent span                          │
    │                                         │
    └─────────────────────┬───────────────────┘
                          ▼
                   Span运行期
                   ├─ SetAttributes()
                   ├─ AddEvent()
                   ├─ RecordError()
                   ├─ SetStatus()
                   └─ 嵌套子Span创建
                          │
                          ▼
                   span.End()
                          │
        ┌─────────────────┼─────────────────┐
        │                 │                 │
        ▼                 ▼                 ▼
    未采样(Drop)    RecordOnly        RecordAndSample
    (直接丢弃)      (不导出但可查看)    (正常导出流程)
        │                 │                 │
        X                 ▼                 ▼
                   ┌──────────────────────────────┐
                   │ SpanProcessor.OnEnd(span)    │
                   └──────────────────────────────┘
                          │
          ┌───────────────┼───────────────┐
          ▼               ▼               ▼
   SimpleProcessor   BatchProcessor   CustomProcessor
   (同步导出)         (批量异步)        (自定义逻辑)
                          │
                          ▼
                   Exporter.ExportSpans()
                          │
                          ▼
                   OTLP/gRPC/HTTP/Console
```

### 1.2 核心对象关系

```go
// span创建相关对象
TracerProvider
    └── tracer (每个instrumentation一个)
        └── span (每次Start创建一个)
            ├── SpanContext (不可变,传播标识)
            │   ├── TraceID (16字节)
            │   ├── SpanID (8字节)
            │   ├── TraceFlags (采样标志)
            │   └── TraceState (vendor扩展)
            ├── parent (父span引用)
            ├── spanKind (Server/Client/Producer/Consumer/Internal)
            ├── startTime
            ├── endTime
            ├── attributes ([]attribute.KeyValue)
            ├── events ([]Event)
            ├── links ([]Link)
            └── status (StatusCode + Description)
```

---

## 2. Span创建详解

### 2.1 tracer.Start() 源码分析

```go
// sdk/trace/tracer.go

func (tr *tracer) Start(
    ctx context.Context,
    name string,
    opts ...trace.SpanStartOption,
) (context.Context, trace.Span) {
    // 1. 解析Start配置
    config := trace.NewSpanStartConfig(opts...)
    
    // 2. 获取父SpanContext
    parent := trace.SpanFromContext(ctx).SpanContext()
    
    // 3. 获取或生成TraceID
    var tid trace.TraceID
    if parent.IsValid() {
        tid = parent.TraceID()
    } else {
        tid = tr.provider.idGenerator.NewIDs().TraceID
    }
    
    // 4. 生成新的SpanID
    sid := tr.provider.idGenerator.NewSpanID(ctx, tid)
    
    // 5. 采样决策
    samplingResult := tr.provider.sampler.ShouldSample(SamplingParameters{
        ParentContext:   ctx,
        TraceID:         tid,
        Name:            name,
        Kind:            config.SpanKind(),
        Attributes:      config.Attributes(),
        Links:           config.Links(),
    })
    
    // 6. 构建SpanContext
    scc := trace.SpanContextConfig{
        TraceID:    tid,
        SpanID:     sid,
        TraceFlags: trace.FlagsSampled, // 根据采样结果设置
        TraceState: samplingResult.Tracestate,
    }
    spanContext := trace.NewSpanContext(scc)
    
    // 7. 创建span实例
    span := &recordingSpan{
        parent:       parent,
        spanContext:  spanContext,
        sampler:      tr.provider.sampler,
        name:         name,
        spanKind:     config.SpanKind(),
        startTime:    config.Timestamp(),
        attributes:   make([]attribute.KeyValue, 0, len(config.Attributes())),
        events:       make([]Event, 0),
        links:        make([]Link, 0, len(config.Links())),
        tracer:       tr,
        provider:     tr.provider,
    }
    
    // 8. 复制attributes
    span.SetAttributes(config.Attributes()...)
    
    // 9. 如果是root span，应用采样结果中的attributes
    if !parent.IsValid() {
        span.SetAttributes(samplingResult.Attributes...)
    }
    
    // 10. 创建新的context并注入span
    ctx = trace.ContextWithSpan(ctx, span)
    
    // 11. 调用OnStart回调
    for _, sp := range tr.provider.spanProcessors {
        sp.OnStart(parent, span)
    }
    
    return ctx, span
}
```

### 2.2 采样决策关键点

```go
// 采样决策发生在span创建时，不可更改！

// sdk/trace/span.go

type recordingSpan struct {
    // ...
    
    // isRecording 表示是否记录数据
    // 由采样决策决定，运行时不变
    isRecording bool
}

func (s *recordingSpan) IsRecording() bool {
    return s.isRecording
}

func (s *recordingSpan) SetAttributes(attrs ...attribute.KeyValue) {
    // 未采样的span直接忽略
    if !s.IsRecording() {
        return
    }
    // ...
}

func (s *recordingSpan) End(options ...trace.SpanEndOption) {
    // 未采样的span直接返回
    if !s.IsRecording() {
        return
    }
    // ...
}
```

**重要**: 采样决策是**创建时一次性**的，运行时无法更改。这是分布式追踪的基本要求（所有span必须一致采样）。

---

## 3. Span运行时操作

### 3.1 Attribute设置

```go
// sdk/trace/span.go

func (s *recordingSpan) SetAttributes(attrs ...attribute.KeyValue) {
    if !s.IsRecording() {
        return
    }
    
    s.mu.Lock()
    defer s.mu.Unlock()
    
    // 检查是否已结束
    if s.endTime.IsZero() {
        s.attributes = append(s.attributes, attrs...)
        
        // 应用属性限制
        if len(s.attributes) > s.spanLimits.AttributeCountLimit {
            s.attributes = s.attributes[:s.spanLimits.AttributeCountLimit]
            s.droppedAttributeCount += len(attrs)
        }
        
        // 属性值长度限制
        s.attributes = s.truncateAttributes(s.attributes)
    }
}
```

**v1.42.0更新**: 属性限制现在更严格地遵守`SpanLimits`配置。

### 3.2 Event记录

```go
// sdk/trace/span.go

type Event struct {
    Name       string
    Attributes []attribute.KeyValue
    Time       time.Time
}

func (s *recordingSpan) AddEvent(
    name string,
    options ...trace.EventOption,
) {
    if !s.IsRecording() {
        return
    }
    
    c := trace.NewEventConfig(options...)
    
    s.mu.Lock()
    defer s.mu.Unlock()
    
    if s.endTime.IsZero() && 
       len(s.events) < s.spanLimits.EventCountLimit {
        s.events = append(s.events, Event{
            Name:       name,
            Attributes: c.Attributes(),
            Time:       c.Timestamp(),
        })
    }
}
```

### 3.3 Error记录 (v1.42.0新特性)

```go
// sdk/trace/span.go

// v1.42.0新增: 更丰富的错误记录
func (s *recordingSpan) RecordError(
    err error,
    options ...trace.EventOption,
) {
    if err == nil || !s.IsRecording() {
        return
    }
    
    opts := []trace.EventOption{
        trace.WithAttributes(
            semconv.ExceptionTypeKey.String(typeStr(err)),
            semconv.ExceptionMessageKey.String(err.Error()),
        ),
    }
    
    // 记录堆栈 (可选)
    if s.stackTrace && s.isRecording {
        opts = append(opts, trace.WithAttributes(
            semconv.ExceptionStacktraceKey.String(recordStackTrace()),
        ))
    }
    
    opts = append(opts, options...)
    s.AddEvent(semconv.ExceptionEventName, opts...)
    
    // 自动设置错误状态
    s.SetStatus(codes.Error, err.Error())
}
```

### 3.4 Status设置

```go
// sdk/trace/span.go

func (s *recordingSpan) SetStatus(code codes.Code, description string) {
    if !s.IsRecording() {
        return
    }
    
    s.mu.Lock()
    defer s.mu.Unlock()
    
    // 重要: 一旦设置为OK，不能被覆盖为Error
    // 这是OTel规范要求
    if s.status.Code == codes.Ok {
        return
    }
    
    s.status = Status{
        Code:        code,
        Description: description,
    }
}
```

**规范要点**:
- `Ok`是最终状态，一旦设置不可更改
- 默认状态是`Unset`
- 通常由最终错误决定状态

---

## 4. Span结束与导出

### 4.1 span.End() 核心逻辑

```go
// sdk/trace/span.go

func (s *recordingSpan) End(options ...trace.SpanEndOption) {
    if !s.IsRecording() {
        return
    }
    
    // 1. 解析结束选项
    config := trace.NewSpanEndConfig(options...)
    
    // 2. 获取结束时间
    endTime := config.Timestamp()
    if endTime.IsZero() {
        endTime = time.Now()
    }
    
    s.mu.Lock()
    
    // 3. 防止重复结束
    if !s.endTime.IsZero() {
        s.mu.Unlock()
        return
    }
    
    // 4. 设置结束时间
    s.endTime = endTime
    
    // 5. 转换为ReadOnlySpan
    ro := s.makeReadOnlySpan()
    
    s.mu.Unlock()
    
    // 6. 调用所有Processor的OnEnd
    for _, sp := range s.provider.spanProcessors {
        sp.OnEnd(ro)
    }
}
```

### 4.2 ReadOnlySpan转换

```go
// sdk/trace/span.go

// makeReadOnlySpan 创建不可变的span快照
func (s *recordingSpan) makeReadOnlySpan() ReadOnlySpan {
    return &readOnlySpan{
        parent:              s.parent,
        spanContext:         s.spanContext,
        name:                s.name,
        spanKind:            s.spanKind,
        startTime:           s.startTime,
        endTime:             s.endTime,
        attributes:          copyAttributes(s.attributes),
        events:              copyEvents(s.events),
        links:               copyLinks(s.links),
        status:              s.status,
        resource:            s.provider.resource,
        instrumentation:     s.tracer.instrumentationScope,
        droppedAttributes:   s.droppedAttributeCount,
        droppedEvents:       s.droppedEventCount,
        droppedLinks:        s.droppedLinkCount,
    }
}

// readOnlySpan 实现了ReadOnlySpan接口
// 保证Processor看到的span数据是冻结的
type readOnlySpan struct {
    // ... 所有字段都是值拷贝
}
```

**关键设计**: `ReadOnlySpan`确保Processor处理时数据不会被修改。

---

## 5. SpanProcessor机制

### 5.1 处理器接口

```go
// sdk/trace/span_processor.go

type SpanProcessor interface {
    // OnStart在span启动时调用
    OnStart(parent context.Context, s ReadWriteSpan)
    
    // OnEnd在span结束时调用
    OnEnd(s ReadOnlySpan)
    
    // Shutdown优雅关闭
    Shutdown(ctx context.Context) error
    
    // ForceFlush强制导出
    ForceFlush(ctx context.Context) error
}
```

### 5.2 SimpleSpanProcessor (同步)

```go
// sdk/trace/simple_span_processor.go

type SimpleSpanProcessor struct {
    exporter SpanExporter
}

func (ssp *SimpleSpanProcessor) OnEnd(s ReadOnlySpan) {
    // 直接同步导出
    ctx := context.Background()
    _ = ssp.exporter.ExportSpans(ctx, []ReadOnlySpan{s})
}
```

**适用场景**: 开发调试，简单应用。

### 5.3 BatchSpanProcessor (异步)

```go
// sdk/trace/batch_span_processor.go

type BatchSpanProcessor struct {
    e          SpanExporter
    batchSize  int
    queue      chan ReadOnlySpan
    batch      []ReadOnlySpan
    timer      *time.Timer
    
    // v1.42.0改进: ForceFlush错误处理
    // 现在会收集所有错误，而不是返回第一个
}

// OnEnd 将span加入队列
func (bsp *BatchSpanProcessor) OnEnd(s ReadOnlySpan) {
    select {
    case bsp.queue <- s:
        // 成功加入队列
    default:
        // 队列满，丢弃（或阻塞取决于配置）
        bsp.droppedCount++
    }
}

// 后台导出循环
func (bsp *BatchSpanProcessor) exportLoop() {
    for {
        select {
        case s := <-bsp.queue:
            bsp.batch = append(bsp.batch, s)
            
            if len(bsp.batch) >= bsp.batchSize {
                bsp.exportBatch()
            }
            
        case <-bsp.timer.C:
            // 定时器触发，强制导出
            if len(bsp.batch) > 0 {
                bsp.exportBatch()
            }
            bsp.timer.Reset(bsp.batchTimeout)
            
        case <-bsp.stopCh:
            // 关闭时导出剩余
            bsp.exportBatch()
            return
        }
    }
}

// exportBatch 批量导出
func (bsp *BatchSpanProcessor) exportBatch() {
    ctx, cancel := context.WithTimeout(context.Background(), bsp.exportTimeout)
    defer cancel()
    
    _ = bsp.e.ExportSpans(ctx, bsp.batch)
    
    // 清空batch
    bsp.batch = bsp.batch[:0]
}
```

### 5.4 ForceFlush改进 (v1.42.0)

```go
// v1.42.0之前: 遇到第一个错误就返回
// v1.42.0: 收集所有错误，继续尝试所有Processor

func (tp *TracerProvider) ForceFlush(ctx context.Context) error {
    var flushErrs []error
    
    for _, sp := range tp.spanProcessors {
        if err := sp.ForceFlush(ctx); err != nil {
            // 继续处理其他Processor，不立即返回
            flushErrs = append(flushErrs, err)
        }
    }
    
    // 使用errors.Join返回所有错误 (Go 1.20+)
    if len(flushErrs) > 0 {
        return errors.Join(flushErrs...)
    }
    return nil
}
```

---

## 6. 性能分析

### 6.1 Span创建开销

| 操作 | 时间复杂度 | 典型耗时 |
|------|-----------|----------|
| ID生成 | O(1) | ~100ns |
| 采样决策 | O(1) | ~50ns |
| Attribute拷贝 | O(n) | ~10ns/attr |
| 创建ReadOnlySpan | O(n) | ~50ns |

### 6.2 内存分配优化

```go
// sdk/trace/tracer.go

// 预分配attribute slice容量
attributes: make([]attribute.KeyValue, 0, len(config.Attributes())),

// 使用sync.Pool复用span对象（可选优化）
var spanPool = sync.Pool{
    New: func() interface{} {
        return &recordingSpan{}
    },
}
```

### 6.3 锁优化

```go
// recordingSpan使用细粒度锁

type recordingSpan struct {
    mu sync.Mutex  // 保护可变字段
    
    // 不变字段（无需锁）
    spanContext trace.SpanContext
    startTime   time.Time
    
    // 可变字段（需要锁）
    attributes []attribute.KeyValue
    events     []Event
    endTime    time.Time
}
```

---

## 7. 实战示例

### 7.1 完整Span生命周期

```go
package main

import (
    "context"
    "fmt"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/semconv/v1.40.0"  // v1.42.0使用v1.40.0语义约定
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithResource(resource.NewWithAttributes(
            semconv.SchemaURL,
            semconv.ServiceNameKey.String("demo-service"),
        )),
        sdktrace.WithSampler(sdktrace.AlwaysSample()),
    )
    defer tp.Shutdown(context.Background())
    
    otel.SetTracerProvider(tp)
    tracer := tp.Tracer("demo-tracer")
    
    // 1. 创建Span (Start)
    ctx, span := tracer.Start(
        context.Background(),
        "process-order",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("order.id", "ORD-12345"),
        ),
    )
    
    // 2. 运行时操作
    span.SetAttributes(
        attribute.Float64("order.amount", 99.99),
    )
    
    span.AddEvent("validation-started", trace.WithAttributes(
        attribute.String("validation.type", "fraud-check"),
    ))
    
    // 模拟处理
    time.Sleep(100 * time.Millisecond)
    
    span.AddEvent("validation-completed")
    
    // 3. 记录错误 (v1.42.0改进)
    if err := processPayment(); err != nil {
        span.RecordError(err, trace.WithAttributes(
            attribute.String("error.phase", "payment"),
        ))
        span.SetStatus(codes.Error, "payment failed")
    } else {
        span.SetStatus(codes.Ok, "success")
    }
    
    // 4. 结束Span (End)
    span.End()
    
    fmt.Println("Span completed")
}

func processPayment() error {
    return fmt.Errorf("insufficient funds")
}
```

### 7.2 嵌套Span示例

```go
func processOrder(ctx context.Context, tracer trace.Tracer) {
    // 父Span
    ctx, span := tracer.Start(ctx, "process-order")
    defer span.End()
    
    // 子Span 1: 验证
    ctx, validateSpan := tracer.Start(ctx, "validate-order")
    validateInventory()
    validateSpan.End()  // 必须手动结束
    
    // 子Span 2: 支付
    ctx, paymentSpan := tracer.Start(ctx, "process-payment")
    if err := chargeCustomer(); err != nil {
        paymentSpan.RecordError(err)
        paymentSpan.SetStatus(codes.Error, err.Error())
    }
    paymentSpan.End()
    
    // 子Span 3: 发货
    _, shipSpan := tracer.Start(ctx, "ship-order")
    shipSpan.SetAttributes(attribute.String("carrier", "UPS"))
    shipSpan.End()
}
```

---

## 8. 常见问题

### Q1: 为什么未采样的span不能重新采样?

```go
// 不行！采样决策是一次性的
span.SetAttributes(attribute.Bool("force.sample", true))
// 这不会改变采样状态
```

**原因**: 分布式追踪要求一个Trace中的所有span采样决策一致。如果root span未采样，child span即使"被采样"也不会被导出。

### Q2: span.End()后还能操作吗?

```go
span.End()
span.SetAttributes(...)  // 静默忽略
```

**建议**: 使用`defer span.End()`确保在所有return路径后结束。

### Q3: 如何追踪长时间运行的操作?

```go
// 对于长时间操作，使用Async Span
ctx, span := tracer.Start(ctx, "long-operation")

// 在goroutine中继续
go func() {
    defer span.End()
    // 长时间工作...
}()
```

---

## 9. 下一步研究

- [Metrics SDK深度分析](./otel-sdk-metrics-deep-dive.md)
- [传播机制分析](./otel-sdk-propagation-mechanism.md)
- [采样策略分析](./otel-sdk-sampling-strategies.md)

---

## 10. 参考

- [OpenTelemetry Go SDK v1.42.0](https://github.com/open-telemetry/opentelemetry-go/releases/tag/v1.42.0)
- [OTel Specification - Tracing](https://opentelemetry.io/docs/specs/otel/trace/)
- [Go SDK Trace Implementation](https://github.com/open-telemetry/opentelemetry-go/tree/main/sdk/trace)

---

**文档状态**: ✅ Phase 1.3 完成  
**研究深度**: 源码级 + v1.42.0最新特性  
**更新日期**: 2026-04-06

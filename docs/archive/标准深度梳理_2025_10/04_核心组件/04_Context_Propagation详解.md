# Context Propagation 详解

> **规范版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [Context Propagation 详解](#context-propagation-详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是Context Propagation](#11-什么是context-propagation)
    - [1.2 为什么需要](#12-为什么需要)
  - [2. W3C Trace Context](#2-w3c-trace-context)
    - [2.1 规范详解](#21-规范详解)
    - [2.2 Header格式](#22-header格式)
  - [3. Propagator实现](#3-propagator实现)
    - [3.1 TextMapPropagator](#31-textmappropagator)
    - [3.2 CompositeTextMapPropagator](#32-compositetextmappropagator)
  - [4. HTTP传播](#4-http传播)
  - [5. gRPC传播](#5-grpc传播)
  - [6. 消息队列传播](#6-消息队列传播)
  - [7. 自定义Propagator](#7-自定义propagator)
  - [8. 跨语言传播](#8-跨语言传播)
  - [9. 性能优化](#9-性能优化)
  - [10. 故障排查](#10-故障排查)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 参考资源](#12-参考资源)

---

## 1. 概述

### 1.1 什么是Context Propagation

```text
Context Propagation (上下文传播):
在分布式系统中传递追踪上下文

传播内容:
1. Trace Context
   - trace_id (追踪ID)
   - span_id (Span ID)
   - trace_flags (追踪标志)
   - trace_state (追踪状态)

2. Baggage
   - 业务上下文
   - 用户信息
   - 实验标志

传播方式:
1. HTTP Headers
   - traceparent
   - tracestate
   - baggage

2. gRPC Metadata
   - 类似HTTP Headers

3. 消息队列
   - Kafka Headers
   - RabbitMQ Headers
   - SQS Message Attributes

4. 自定义协议
   - 自定义Propagator
```

### 1.2 为什么需要

```text
分布式追踪核心:
┌─────────┐     ┌─────────┐     ┌─────────┐
│Service A│────>│Service B│────>│Service C│
└─────────┘     └─────────┘     └─────────┘
  trace_id=123   trace_id=123   trace_id=123
  span_id=001    span_id=002    span_id=003
  parent=000     parent=001     parent=002

没有传播:
- 每个服务独立trace_id
- 无法关联请求
- 无法完整追踪

有传播:
- 相同trace_id
- 父子Span关系
- 完整链路追踪

示例场景:
用户请求 → API Gateway → Order Service → Payment Service → Database

期望:
- 看到完整请求链路
- 每个服务的延迟
- 发现性能瓶颈

需要:
- Context Propagation在每个服务间传递
```

---

## 2. W3C Trace Context

### 2.1 规范详解

```text
W3C Trace Context:
标准化的追踪上下文传播协议

核心Headers:
1. traceparent (必需)
   - 唯一标识追踪
   - 包含trace_id, span_id, flags

2. tracestate (可选)
   - 供应商特定状态
   - 键值对列表

优势:
- 标准化 (W3C标准)
- 互操作性 (跨工具/语言)
- 向后兼容
```

### 2.2 Header格式

**traceparent格式**:

```text
格式:
traceparent: {version}-{trace-id}-{parent-id}-{trace-flags}

字段:
version:     2位16进制 (固定"00")
trace-id:    32位16进制 (16字节)
parent-id:   16位16进制 (8字节)
trace-flags: 2位16进制 (1字节)

示例:
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01

解析:
version: 00
trace_id: 4bf92f3577b34da6a3ce929d0e0e4736
span_id (parent_id): 00f067aa0ba902b7
trace_flags: 01 (采样)

trace_flags位:
- 00000001 (0x01): sampled (采样)
- 00000000 (0x00): not sampled (不采样)
- 其他位: 保留

验证规则:
1. trace_id ≠ 00000000000000000000000000000000
2. span_id ≠ 0000000000000000
3. 格式必须正确
```

**tracestate格式**:

```text
格式:
tracestate: vendor1=value1,vendor2=value2

规则:
- 键值对用逗号分隔
- 最多32个键值对
- 键: [a-z0-9_-*/]
- 值: 打印ASCII字符
- 顺序保留
- 总长度 < 512字节

示例:
tracestate: congo=t61rcWkgMzE,rojo=00f067aa0ba902b7

用途:
- 供应商特定追踪信息
- A/B测试标志
- 采样决策信息
- 其他元数据

OpenTelemetry使用:
- ot=sampling_priority:1
- ot=user_id:abc123
```

---

## 3. Propagator实现

### 3.1 TextMapPropagator

**Go实现**:

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

func setupPropagation() {
    // 1. TraceContext Propagator (W3C标准)
    tc := propagation.TraceContext{}
    
    // 2. Baggage Propagator
    bg := propagation.Baggage{}
    
    // 3. Composite Propagator (组合多个)
    propagator := propagation.NewCompositeTextMapPropagator(tc, bg)
    
    // 4. 设置全局Propagator
    otel.SetTextMapPropagator(propagator)
}

// Inject: 注入上下文到Carrier
func injectContext(ctx context.Context, headers map[string]string) {
    propagator := otel.GetTextMapPropagator()
    
    // 使用MapCarrier
    carrier := propagation.MapCarrier(headers)
    
    // 注入
    propagator.Inject(ctx, carrier)
    
    // headers现在包含:
    // - traceparent: 00-...
    // - tracestate: ...
    // - baggage: key1=value1,...
}

// Extract: 从Carrier提取上下文
func extractContext(headers map[string]string) context.Context {
    propagator := otel.GetTextMapPropagator()
    
    carrier := propagation.MapCarrier(headers)
    
    // 提取
    ctx := propagator.Extract(context.Background(), carrier)
    
    // ctx现在包含:
    // - Span Context (trace_id, span_id)
    // - Baggage
    
    return ctx
}
```

### 3.2 CompositeTextMapPropagator

```go
// 自定义Propagator组合
func customPropagator() propagation.TextMapPropagator {
    return propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},  // W3C Trace Context
        propagation.Baggage{},        // W3C Baggage
        // 可添加更多自定义Propagator
    )
}

// Fields方法: 返回需要的Header名称
func (p *CompositeTextMapPropagator) Fields() []string {
    // 返回所有Propagator的Fields
    return []string{
        "traceparent",
        "tracestate",
        "baggage",
    }
}

// Inject方法: 注入所有Propagator
func (p *CompositeTextMapPropagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    // 依次调用每个Propagator的Inject
    for _, propagator := range p.propagators {
        propagator.Inject(ctx, carrier)
    }
}

// Extract方法: 提取所有Propagator
func (p *CompositeTextMapPropagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
    // 依次调用每个Propagator的Extract
    for _, propagator := range p.propagators {
        ctx = propagator.Extract(ctx, carrier)
    }
    return ctx
}
```

---

## 4. HTTP传播

**客户端 (发送请求)**:

```go
func makeHTTPRequest(ctx context.Context, url string) (*http.Response, error) {
    // 1. 创建请求
    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        return nil, err
    }
    
    // 2. 注入上下文到Headers
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    // req.Header现在包含traceparent, tracestate, baggage
    
    // 3. 发送请求
    client := &http.Client{}
    return client.Do(req)
}

// 使用示例
func clientExample(ctx context.Context) {
    tracer := otel.Tracer("client")
    ctx, span := tracer.Start(ctx, "http.request")
    defer span.End()
    
    // 发送请求 (自动传播Context)
    resp, err := makeHTTPRequest(ctx, "http://api.example.com/data")
    if err != nil {
        span.RecordError(err)
        return
    }
    defer resp.Body.Close()
    
    // 处理响应
}
```

**服务器 (接收请求)**:

```go
func handleHTTPRequest(w http.ResponseWriter, r *http.Request) {
    // 1. 提取上下文从Headers
    propagator := otel.GetTextMapPropagator()
    ctx := propagator.Extract(context.Background(), propagation.HeaderCarrier(r.Header))
    
    // ctx现在包含上游的Span Context和Baggage
    
    // 2. 创建Span (自动关联到父Span)
    tracer := otel.Tracer("server")
    ctx, span := tracer.Start(ctx, "http.handler",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()
    
    // 3. 业务逻辑
    handleBusiness(ctx)
    
    w.WriteHeader(http.StatusOK)
}

// 使用中间件自动化
func tracingMiddleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 提取Context
        propagator := otel.GetTextMapPropagator()
        ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))
        
        // 创建Span
        tracer := otel.Tracer("http.server")
        ctx, span := tracer.Start(ctx, r.URL.Path,
            trace.WithSpanKind(trace.SpanKindServer),
        )
        defer span.End()
        
        // 记录HTTP属性
        span.SetAttributes(
            semconv.HTTPMethodKey.String(r.Method),
            semconv.HTTPRouteKey.String(r.URL.Path),
        )
        
        // 传递Context到下一个Handler
        next.ServeHTTP(w, r.WithContext(ctx))
        
        // 记录响应状态
        // (需要ResponseWriter wrapper)
    })
}
```

**使用otelhttp (官方instrumentation)**:

```go
import "go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp"

// 客户端
func clientWithOtelhttp(ctx context.Context) {
    client := &http.Client{
        Transport: otelhttp.NewTransport(http.DefaultTransport),
    }
    
    req, _ := http.NewRequestWithContext(ctx, "GET", "http://api.example.com", nil)
    
    // 自动注入Context + 创建Client Span
    resp, _ := client.Do(req)
    defer resp.Body.Close()
}

// 服务器
func serverWithOtelhttp() {
    handler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 业务逻辑
        w.Write([]byte("Hello"))
    })
    
    // 包装Handler (自动提取Context + 创建Server Span)
    wrappedHandler := otelhttp.NewHandler(handler, "my-handler")
    
    http.ListenAndServe(":8080", wrappedHandler)
}
```

---

## 5. gRPC传播

**gRPC客户端**:

```go
import (
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
    "google.golang.org/grpc"
)

func grpcClient(ctx context.Context) {
    // 创建gRPC连接 (自动传播)
    conn, err := grpc.Dial("localhost:50051",
        grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
        grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
    )
    if err != nil {
        log.Fatal(err)
    }
    defer conn.Close()
    
    client := pb.NewGreeterClient(conn)
    
    // 调用 (自动注入Context到gRPC Metadata)
    resp, err := client.SayHello(ctx, &pb.HelloRequest{Name: "World"})
}
```

**gRPC服务器**:

```go
func grpcServer() {
    lis, _ := net.Listen("tcp", ":50051")
    
    s := grpc.NewServer(
        grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
        grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
    )
    
    pb.RegisterGreeterServer(s, &server{})
    
    s.Serve(lis)
}

type server struct {
    pb.UnimplementedGreeterServer
}

func (s *server) SayHello(ctx context.Context, req *pb.HelloRequest) (*pb.HelloReply, error) {
    // ctx自动包含上游Context
    
    tracer := otel.Tracer("greeter")
    ctx, span := tracer.Start(ctx, "SayHello")
    defer span.End()
    
    // 业务逻辑
    return &pb.HelloReply{Message: "Hello " + req.Name}, nil
}
```

---

## 6. 消息队列传播

**Kafka Producer**:

```go
func kafkaProducer(ctx context.Context) {
    producer, _ := kafka.NewWriter(kafka.WriterConfig{
        Brokers: []string{"localhost:9092"},
        Topic:   "my-topic",
    })
    defer producer.Close()
    
    // 准备消息
    msg := kafka.Message{
        Key:   []byte("key"),
        Value: []byte("value"),
    }
    
    // 注入Context到Kafka Headers
    propagator := otel.GetTextMapPropagator()
    carrier := NewKafkaHeaderCarrier(&msg.Headers)
    propagator.Inject(ctx, carrier)
    
    // 发送
    producer.WriteMessages(ctx, msg)
}

// Kafka Header Carrier
type KafkaHeaderCarrier struct {
    headers *[]kafka.Header
}

func NewKafkaHeaderCarrier(headers *[]kafka.Header) *KafkaHeaderCarrier {
    return &KafkaHeaderCarrier{headers: headers}
}

func (c *KafkaHeaderCarrier) Get(key string) string {
    for _, h := range *c.headers {
        if string(h.Key) == key {
            return string(h.Value)
        }
    }
    return ""
}

func (c *KafkaHeaderCarrier) Set(key, value string) {
    // 先删除已存在的
    headers := make([]kafka.Header, 0)
    for _, h := range *c.headers {
        if string(h.Key) != key {
            headers = append(headers, h)
        }
    }
    
    // 添加新Header
    headers = append(headers, kafka.Header{
        Key:   []byte(key),
        Value: []byte(value),
    })
    
    *c.headers = headers
}

func (c *KafkaHeaderCarrier) Keys() []string {
    keys := make([]string, len(*c.headers))
    for i, h := range *c.headers {
        keys[i] = string(h.Key)
    }
    return keys
}
```

**Kafka Consumer**:

```go
func kafkaConsumer() {
    reader := kafka.NewReader(kafka.ReaderConfig{
        Brokers: []string{"localhost:9092"},
        Topic:   "my-topic",
        GroupID: "my-group",
    })
    defer reader.Close()
    
    for {
        msg, err := reader.ReadMessage(context.Background())
        if err != nil {
            break
        }
        
        // 提取Context从Kafka Headers
        propagator := otel.GetTextMapPropagator()
        carrier := NewKafkaHeaderCarrier(&msg.Headers)
        ctx := propagator.Extract(context.Background(), carrier)
        
        // 处理消息 (ctx包含上游追踪信息)
        processMessage(ctx, msg)
    }
}

func processMessage(ctx context.Context, msg kafka.Message) {
    tracer := otel.Tracer("kafka.consumer")
    ctx, span := tracer.Start(ctx, "process.message",
        trace.WithSpanKind(trace.SpanKindConsumer),
    )
    defer span.End()
    
    span.SetAttributes(
        attribute.String("messaging.system", "kafka"),
        attribute.String("messaging.destination", "my-topic"),
        attribute.String("messaging.operation", "receive"),
    )
    
    // 业务逻辑
}
```

---

## 7. 自定义Propagator

```go
// 自定义Propagator示例
type CustomPropagator struct{}

func (p *CustomPropagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    sc := trace.SpanContextFromContext(ctx)
    if !sc.IsValid() {
        return
    }
    
    // 自定义格式
    carrier.Set("X-Custom-Trace-ID", sc.TraceID().String())
    carrier.Set("X-Custom-Span-ID", sc.SpanID().String())
    
    if sc.IsSampled() {
        carrier.Set("X-Custom-Sampled", "1")
    }
}

func (p *CustomPropagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
    traceID := carrier.Get("X-Custom-Trace-ID")
    spanID := carrier.Get("X-Custom-Span-ID")
    sampled := carrier.Get("X-Custom-Sampled") == "1"
    
    if traceID == "" || spanID == "" {
        return ctx
    }
    
    // 解析
    tid, _ := trace.TraceIDFromHex(traceID)
    sid, _ := trace.SpanIDFromHex(spanID)
    
    var flags trace.TraceFlags
    if sampled {
        flags = trace.FlagsSampled
    }
    
    sc := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    tid,
        SpanID:     sid,
        TraceFlags: flags,
        Remote:     true,
    })
    
    return trace.ContextWithRemoteSpanContext(ctx, sc)
}

func (p *CustomPropagator) Fields() []string {
    return []string{
        "X-Custom-Trace-ID",
        "X-Custom-Span-ID",
        "X-Custom-Sampled",
    }
}

// 使用
func useCustomPropagator() {
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            &CustomPropagator{},  // 添加自定义Propagator
        ),
    )
}
```

---

## 8. 跨语言传播

**Go → Python**:

```go
// Go Service (发送)
func goService(ctx context.Context) {
    req, _ := http.NewRequestWithContext(ctx, "GET", "http://python-service:8000", nil)
    
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    // req.Header:
    // traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
    
    http.DefaultClient.Do(req)
}
```

```python
# Python Service (接收)
from opentelemetry.propagate import extract
from flask import Flask, request

app = Flask(__name__)

@app.route('/')
def index():
    # 提取Context
    ctx = extract(request.headers)
    
    # ctx包含trace_id, span_id from Go Service
    
    tracer = trace.get_tracer(__name__)
    with tracer.start_as_current_span("python.handler", context=ctx):
        # 业务逻辑
        return "OK"
```

**跨语言保证**:

- W3C Trace Context标准
- 所有语言SDK支持
- 相同trace_id
- 正确父子关系

---

## 9. 性能优化

```text
性能考虑:
1. Header大小
   - traceparent: ~55字节
   - tracestate: 可变 (< 512字节)
   - baggage: 可变 (< 8KB)
   
   总计: 通常< 1KB

2. 序列化/反序列化
   - 快速hex解析
   - 无JSON开销
   - < 1μs per operation

3. 内存分配
   - 减少字符串分配
   - 复用Buffer

优化示例:
// ❌ 低效
func slowInject(ctx context.Context) map[string]string {
    headers := make(map[string]string)
    propagator.Inject(ctx, propagation.MapCarrier(headers))
    return headers
}

// ✅ 高效 (复用map)
var headerPool = sync.Pool{
    New: func() interface{} {
        return make(map[string]string, 8)
    },
}

func fastInject(ctx context.Context) map[string]string {
    headers := headerPool.Get().(map[string]string)
    defer func() {
        for k := range headers {
            delete(headers, k)
        }
        headerPool.Put(headers)
    }()
    
    propagator.Inject(ctx, propagation.MapCarrier(headers))
    return headers
}

基准测试:
BenchmarkInject-8    1000000    1247 ns/op    432 B/op    8 allocs/op
BenchmarkExtract-8   1000000    1156 ns/op    384 B/op    7 allocs/op
```

---

## 10. 故障排查

```text
常见问题:

问题1: Trace链路断裂
症状: 下游服务没有关联到上游
诊断:
  1. 检查Propagator是否设置
     otel.GetTextMapPropagator()
  
  2. 检查Header是否注入
     打印req.Header
  
  3. 检查Header是否提取
     打印span.SpanContext()

解决:
  - 确保设置全局Propagator
  - 使用中间件自动化

问题2: trace_id全为0
症状: trace_id=00000000000000000000000000000000
诊断:
  1. 检查是否创建了Span
  2. 检查Context是否正确传递

解决:
  ctx, span := tracer.Start(ctx, "operation")
  defer span.End()

问题3: 跨语言传播失败
症状: Go → Python链路断裂
诊断:
  1. 检查Header名称 (traceparent vs trace-parent)
  2. 检查格式是否正确
  3. 打印Headers

解决:
  - 统一使用W3C Trace Context
  - 验证Header格式

调试工具:
// 打印传播的Headers
func debugHeaders(headers http.Header) {
    log.Printf("traceparent: %s", headers.Get("traceparent"))
    log.Printf("tracestate: %s", headers.Get("tracestate"))
    log.Printf("baggage: %s", headers.Get("baggage"))
}

// 打印Span Context
func debugSpanContext(ctx context.Context) {
    sc := trace.SpanContextFromContext(ctx)
    log.Printf("TraceID: %s", sc.TraceID())
    log.Printf("SpanID: %s", sc.SpanID())
    log.Printf("Sampled: %v", sc.IsSampled())
}
```

---

## 11. 最佳实践

```text
✅ DO (推荐)
1. 使用标准Propagator
   - W3C Trace Context
   - 跨语言/工具兼容

2. 组合Propagators
   propagation.NewCompositeTextMapPropagator(
       propagation.TraceContext{},
       propagation.Baggage{},
   )

3. 使用官方Instrumentation
   - otelhttp
   - otelgrpc
   - 自动化传播

4. 传递Context
   - 始终传递ctx参数
   - 不创建新Context

5. 验证传播
   - 单元测试
   - 集成测试

❌ DON'T (避免)
1. 不要忘记设置Propagator
2. 不要手动拼接Header
3. 不要丢失Context
4. 不要使用非标准格式
5. 不要忽略错误

示例最佳配置:
// 初始化
func init() {
    otel.SetTextMapPropagator(
        propagation.NewCompositeTextMapPropagator(
            propagation.TraceContext{},
            propagation.Baggage{},
        ),
    )
}

// HTTP客户端
client := &http.Client{
    Transport: otelhttp.NewTransport(http.DefaultTransport),
}

// HTTP服务器
handler := otelhttp.NewHandler(businessHandler, "service")
http.ListenAndServe(":8080", handler)

// gRPC
conn, _ := grpc.Dial("localhost:50051",
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
)
```

---

## 12. 参考资源

- **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>
- **OpenTelemetry Context**: <https://opentelemetry.io/docs/specs/otel/context/>
- **Go Propagation**: <https://pkg.go.dev/go.opentelemetry.io/otel/propagation>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [SDK最佳实践](03_SDK最佳实践.md), [Baggage详解](../03_数据模型/05_Baggage/01_Baggage详解.md)

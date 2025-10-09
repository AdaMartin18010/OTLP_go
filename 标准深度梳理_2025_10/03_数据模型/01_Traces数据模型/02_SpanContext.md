# SpanContext 完整指南

## 📋 目录

- [概述](#概述)
- [SpanContext 定义](#spancontext-定义)
- [核心组件](#核心组件)
  - [TraceID](#traceid)
  - [SpanID](#spanid)
  - [TraceFlags](#traceflags)
  - [TraceState](#tracestate)
- [上下文传播](#上下文传播)
- [W3C Trace Context](#w3c-trace-context)
- [Go 完整实现](#go-完整实现)
- [最佳实践](#最佳实践)
- [常见问题](#常见问题)
- [参考资源](#参考资源)

---

## 概述

**SpanContext** 是 OpenTelemetry 追踪的核心概念，包含了在分布式系统中传播追踪信息所需的全部数据。它是不可变的，用于在服务边界之间传递追踪上下文。

### 关键特性

- ✅ **不可变**: SpanContext 创建后不能修改
- ✅ **可序列化**: 可以通过 HTTP 头、gRPC 元数据等传输
- ✅ **轻量级**: 只包含标识符和标志，不包含属性或事件
- ✅ **跨进程**: 支持在不同进程和服务之间传播

---

## SpanContext 定义

### 形式化定义

```text
SpanContext := {
    TraceID:    [16]byte    // 128-bit 追踪标识符
    SpanID:     [8]byte     // 64-bit Span 标识符
    TraceFlags: byte        // 8-bit 标志位
    TraceState: string      // 供应商特定的追踪状态
    Remote:     bool        // 是否来自远程进程
}
```

### OTLP Protocol Buffers 定义

```protobuf
message Span {
  bytes trace_id = 1;        // 16 bytes TraceID
  bytes span_id = 2;         // 8 bytes SpanID
  string trace_state = 3;    // W3C TraceState
  // TraceFlags 包含在 span_context 中
}
```

### Go 类型定义

```go
type SpanContext struct {
    traceID    TraceID    // [16]byte
    spanID     SpanID     // [8]byte
    traceFlags TraceFlags // byte
    traceState TraceState // string
    remote     bool
}
```

---

## 核心组件

### TraceID

#### 定义

**TraceID** 是 128-bit (16 bytes) 全局唯一标识符，用于标识整个分布式追踪。

#### 格式

- **长度**: 16 bytes (128 bits)
- **表示**: 32 个十六进制字符
- **示例**: `4bf92f3577b34da6a3ce929d0e0e4736`

#### 生成规则

```text
1. 必须是随机生成或伪随机生成
2. 必须是全局唯一的
3. 不能全为零 (00000000000000000000000000000000)
4. 建议使用加密安全的随机数生成器
```

#### Go 实现

```go
import (
    "crypto/rand"
    "encoding/hex"
    "go.opentelemetry.io/otel/trace"
)

// 生成 TraceID
func generateTraceID() trace.TraceID {
    var traceID trace.TraceID
    _, err := rand.Read(traceID[:])
    if err != nil {
        panic(err)
    }
    return traceID
}

// 从字符串解析
func parseTraceID(s string) (trace.TraceID, error) {
    return trace.TraceIDFromHex(s)
}

// 转换为字符串
func traceIDToString(traceID trace.TraceID) string {
    return traceID.String()
}

// 检查是否有效
func isValidTraceID(traceID trace.TraceID) bool {
    return traceID.IsValid()  // 检查是否全零
}

// 示例
func main() {
    // 生成
    traceID := generateTraceID()
    fmt.Printf("TraceID: %s\n", traceID.String())
    // Output: 4bf92f3577b34da6a3ce929d0e0e4736

    // 解析
    parsed, _ := parseTraceID("4bf92f3577b34da6a3ce929d0e0e4736")
    fmt.Printf("Parsed: %s\n", parsed.String())

    // 验证
    fmt.Printf("Valid: %v\n", isValidTraceID(traceID))
}
```

#### 高级用法

```go
// 从 bytes 创建
func traceIDFromBytes(b []byte) trace.TraceID {
    var traceID trace.TraceID
    copy(traceID[:], b)
    return traceID
}

// 转换为 bytes
func traceIDToBytes(traceID trace.TraceID) []byte {
    return traceID[:]
}

// 比较两个 TraceID
func compareTraceID(id1, id2 trace.TraceID) bool {
    return id1 == id2
}
```

---

### SpanID

#### 定义1

**SpanID** 是 64-bit (8 bytes) 标识符，在 Trace 内唯一标识一个 Span。

#### 格式1

- **长度**: 8 bytes (64 bits)
- **表示**: 16 个十六进制字符
- **示例**: `00f067aa0ba902b7`

#### 生成规则1

```text
1. 在同一个 Trace 内必须唯一
2. 不能全为零 (0000000000000000)
3. 建议使用随机生成
4. ParentSpanID 和 SpanID 不能相同
```

#### Go 实现1

```go
// 生成 SpanID
func generateSpanID() trace.SpanID {
    var spanID trace.SpanID
    _, err := rand.Read(spanID[:])
    if err != nil {
        panic(err)
    }
    return spanID
}

// 从字符串解析
func parseSpanID(s string) (trace.SpanID, error) {
    return trace.SpanIDFromHex(s)
}

// 转换为字符串
func spanIDToString(spanID trace.SpanID) string {
    return spanID.String()
}

// 检查是否有效
func isValidSpanID(spanID trace.SpanID) bool {
    return spanID.IsValid()
}

// 示例
func main() {
    spanID := generateSpanID()
    fmt.Printf("SpanID: %s\n", spanID.String())
    // Output: 00f067aa0ba902b7
}
```

---

### TraceFlags

#### 定义2

**TraceFlags** 是 8-bit 标志位，用于控制追踪行为。

#### 位定义2

```text
Bit 0 (0x01): Sampled    - 该 Trace 是否被采样
Bit 1-7:      Reserved   - 保留，必须为 0
```

#### 值2

```go
const (
    FlagsSampled = 0x01  // 0000 0001
)

// 示例值
0x00  // 未采样
0x01  // 已采样
```

#### Go 实现2

```go
import "go.opentelemetry.io/otel/trace"

// 检查是否采样
func isSampled(flags trace.TraceFlags) bool {
    return flags.IsSampled()
}

// 设置采样标志
func setSampled(flags trace.TraceFlags) trace.TraceFlags {
    return flags | trace.FlagsSampled
}

// 清除采样标志
func clearSampled(flags trace.TraceFlags) trace.TraceFlags {
    return flags &^ trace.FlagsSampled
}

// 示例
func main() {
    // 创建采样标志
    flags := trace.FlagsSampled
    fmt.Printf("Sampled: %v\n", isSampled(flags))  // true

    // 清除采样
    flags = clearSampled(flags)
    fmt.Printf("Sampled: %v\n", isSampled(flags))  // false
}
```

#### 采样决策

```go
// 基于采样决策创建 SpanContext
func createSpanContext(sampled bool) trace.SpanContext {
    var flags trace.TraceFlags
    if sampled {
        flags = trace.FlagsSampled
    }

    return trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    generateTraceID(),
        SpanID:     generateSpanID(),
        TraceFlags: flags,
    })
}

// 示例：采样器
type Sampler interface {
    ShouldSample(ctx context.Context, traceID trace.TraceID) bool
}

// 百分比采样器
type PercentageSampler struct {
    percentage float64
}

func (s *PercentageSampler) ShouldSample(ctx context.Context, traceID trace.TraceID) bool {
    // 使用 TraceID 的最后一个字节计算
    lastByte := traceID[15]
    threshold := uint8(s.percentage * 255)
    return lastByte < threshold
}
```

---

### TraceState

#### 定义3

**TraceState** 是 W3C Trace Context 规范的一部分，用于传递供应商特定的追踪信息。

#### 格式3

```text
TraceState := list-member *( "," list-member )
list-member := key "=" value
key         := vendor-key / system-key
value       := *CHR
```

#### 示例

```text
rojo=00f067aa0ba902b7,congo=t61rcWkgMzE
```

#### 规则

1. **最大长度**: 512 字符
2. **最大成员数**: 32 个
3. **键格式**: 小写字母、数字、下划线、连字符、@
4. **值格式**: 可打印 ASCII 字符（除逗号、等号）

#### Go 实现4

```go
import "go.opentelemetry.io/otel/trace"

// 创建 TraceState
func createTraceState() trace.TraceState {
    ts, err := trace.ParseTraceState("rojo=00f067aa0ba902b7,congo=t61rcWkgMzE")
    if err != nil {
        panic(err)
    }
    return ts
}

// 获取值
func getTraceStateValue(ts trace.TraceState, key string) string {
    return ts.Get(key)
}

// 插入新值 (返回新的 TraceState)
func insertTraceState(ts trace.TraceState, key, value string) (trace.TraceState, error) {
    return ts.Insert(key, value)
}

// 删除值
func deleteTraceState(ts trace.TraceState, key string) trace.TraceState {
    return ts.Delete(key)
}

// 示例
func main() {
    // 创建
    ts, _ := trace.ParseTraceState("vendor1=value1")
    fmt.Printf("TraceState: %s\n", ts.String())

    // 插入
    ts, _ = ts.Insert("vendor2", "value2")
    fmt.Printf("Updated: %s\n", ts.String())
    // Output: vendor2=value2,vendor1=value1

    // 获取
    value := ts.Get("vendor1")
    fmt.Printf("Value: %s\n", value)  // value1

    // 删除
    ts = ts.Delete("vendor1")
    fmt.Printf("After delete: %s\n", ts.String())
    // Output: vendor2=value2
}
```

#### 高级用法4

```go
// 验证 TraceState 键
func isValidKey(key string) bool {
    // 实现 W3C 规范的验证
    if len(key) == 0 || len(key) > 256 {
        return false
    }
    // ... 更多验证
    return true
}

// 限制 TraceState 大小
func limitTraceState(ts trace.TraceState, maxMembers int) trace.TraceState {
    if ts.Len() <= maxMembers {
        return ts
    }
    
    // 保留前 maxMembers 个
    // (TraceState 维护插入顺序)
    return ts  // SDK 自动处理
}

// 合并 TraceState
func mergeTraceState(ts1, ts2 trace.TraceState) (trace.TraceState, error) {
    result := ts1
    
    // 遍历 ts2，插入到 result
    // (具体实现依赖 SDK API)
    return result, nil
}
```

---

## 上下文传播

### Context 传播机制

#### 进程内传播

```go
import "context"

// 1. 创建 SpanContext 并注入到 Context
func injectSpanContext(ctx context.Context, spanCtx trace.SpanContext) context.Context {
    return trace.ContextWithSpanContext(ctx, spanCtx)
}

// 2. 从 Context 提取 SpanContext
func extractSpanContext(ctx context.Context) trace.SpanContext {
    return trace.SpanContextFromContext(ctx)
}

// 示例：进程内传播
func processRequest(ctx context.Context) {
    // 创建 Span
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()

    // SpanContext 自动通过 ctx 传播
    doSubTask(ctx)  // doSubTask 可以获取 SpanContext
}

func doSubTask(ctx context.Context) {
    // 提取 SpanContext
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        fmt.Printf("TraceID: %s\n", spanCtx.TraceID().String())
    }

    // 创建子 Span
    ctx, span := tracer.Start(ctx, "sub_task")
    defer span.End()
}
```

#### 跨进程传播 (HTTP)

```go
import (
    "net/http"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// 发送端：注入到 HTTP 头
func httpClientWithTracing(ctx context.Context, url string) (*http.Response, error) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)

    // 注入追踪上下文到 HTTP 头
    propagator := otel.GetTextMapPropagator()
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))

    return http.DefaultClient.Do(req)
}

// 接收端：从 HTTP 头提取
func httpServerWithTracing(w http.ResponseWriter, r *http.Request) {
    // 提取追踪上下文
    propagator := otel.GetTextMapPropagator()
    ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))

    // 创建服务器端 Span
    ctx, span := tracer.Start(ctx, "handle_request",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    // 处理请求
    handleRequest(ctx, r)
}
```

#### 跨进程传播 (gRPC)

```go
import (
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
)

// 客户端：自动注入
conn, err := grpc.Dial("localhost:50051",
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
    grpc.WithStreamInterceptor(otelgrpc.StreamClientInterceptor()),
)

// 服务器端：自动提取
server := grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
    grpc.StreamInterceptor(otelgrpc.StreamServerInterceptor()),
)

// 手动操作 (如果需要)
func manualGRPCInject(ctx context.Context) context.Context {
    propagator := otel.GetTextMapPropagator()
    
    // 创建 metadata carrier
    md := make(metadata.MD)
    propagator.Inject(ctx, metadataTextMapCarrier(md))
    
    return metadata.NewOutgoingContext(ctx, md)
}

func manualGRPCExtract(ctx context.Context) context.Context {
    propagator := otel.GetTextMapPropagator()
    
    // 从 metadata 提取
    md, ok := metadata.FromIncomingContext(ctx)
    if !ok {
        return ctx
    }
    
    return propagator.Extract(ctx, metadataTextMapCarrier(md))
}
```

---

## W3C Trace Context

### Traceparent Header

#### 格式5

```text
traceparent: {version}-{trace-id}-{parent-id}-{trace-flags}

version:     2 位十六进制 (00)
trace-id:    32 位十六进制 (16 bytes)
parent-id:   16 位十六进制 (8 bytes)
trace-flags: 2 位十六进制 (1 byte)
```

#### 示例5

```text
traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
```

#### 解析

```go
import "strings"

// 解析 traceparent header
func parseTraceparent(header string) (trace.SpanContext, error) {
    parts := strings.Split(header, "-")
    if len(parts) != 4 {
        return trace.SpanContext{}, fmt.Errorf("invalid format")
    }

    // 验证版本
    if parts[0] != "00" {
        return trace.SpanContext{}, fmt.Errorf("unsupported version")
    }

    // 解析 TraceID
    traceID, err := trace.TraceIDFromHex(parts[1])
    if err != nil {
        return trace.SpanContext{}, err
    }

    // 解析 SpanID
    spanID, err := trace.SpanIDFromHex(parts[2])
    if err != nil {
        return trace.SpanContext{}, err
    }

    // 解析 TraceFlags
    var flags trace.TraceFlags
    fmt.Sscanf(parts[3], "%02x", &flags)

    return trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    traceID,
        SpanID:     spanID,
        TraceFlags: flags,
        Remote:     true,
    }), nil
}

// 生成 traceparent header
func formatTraceparent(spanCtx trace.SpanContext) string {
    return fmt.Sprintf("00-%s-%s-%02x",
        spanCtx.TraceID().String(),
        spanCtx.SpanID().String(),
        spanCtx.TraceFlags(),
    )
}
```

### Tracestate Header

#### 格式6

```text
tracestate: {list-member}[,{list-member}]...
```

#### 示例6

```text
tracestate: rojo=00f067aa0ba902b7,congo=t61rcWkgMzE
```

#### 解析6

```go
// 解析 tracestate header
func parseTracestate(header string) (trace.TraceState, error) {
    return trace.ParseTraceState(header)
}

// 生成 tracestate header
func formatTracestate(ts trace.TraceState) string {
    return ts.String()
}
```

### 完整的 HTTP 传播示例

```go
// HTTP 客户端
func makeHTTPRequest(ctx context.Context, url string) (*http.Response, error) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)

    // 提取 SpanContext
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        // 设置 traceparent
        req.Header.Set("traceparent", formatTraceparent(spanCtx))
        
        // 设置 tracestate (如果有)
        if ts := spanCtx.TraceState(); ts.String() != "" {
            req.Header.Set("tracestate", ts.String())
        }
    }

    return http.DefaultClient.Do(req)
}

// HTTP 服务器
func handleHTTPRequest(w http.ResponseWriter, r *http.Request) {
    var ctx context.Context = r.Context()

    // 提取 traceparent
    if traceparent := r.Header.Get("traceparent"); traceparent != "" {
        if spanCtx, err := parseTraceparent(traceparent); err == nil {
            // 提取 tracestate
            if tracestate := r.Header.Get("tracestate"); tracestate != "" {
                if ts, err := parseTracestate(tracestate); err == nil {
                    spanCtx = spanCtx.WithTraceState(ts)
                }
            }
            
            ctx = trace.ContextWithRemoteSpanContext(ctx, spanCtx)
        }
    }

    // 创建服务器端 Span
    ctx, span := tracer.Start(ctx, "handle_request",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()

    // 处理请求
    processRequest(ctx, r)
}
```

---

## Go 完整实现

### SpanContext 创建

```go
package main

import (
    "crypto/rand"
    "fmt"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 1. 创建新的 SpanContext
    spanCtx := createNewSpanContext(true)
    printSpanContext(spanCtx)

    // 2. 从现有创建子 SpanContext
    childCtx := createChildSpanContext(spanCtx)
    printSpanContext(childCtx)

    // 3. 创建远程 SpanContext
    remoteCtx := createRemoteSpanContext()
    printSpanContext(remoteCtx)
}

// 创建新的 SpanContext
func createNewSpanContext(sampled bool) trace.SpanContext {
    var flags trace.TraceFlags
    if sampled {
        flags = trace.FlagsSampled
    }

    return trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    generateTraceID(),
        SpanID:     generateSpanID(),
        TraceFlags: flags,
    })
}

// 创建子 SpanContext (相同 TraceID)
func createChildSpanContext(parent trace.SpanContext) trace.SpanContext {
    return trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    parent.TraceID(),  // 继承 TraceID
        SpanID:     generateSpanID(),  // 新的 SpanID
        TraceFlags: parent.TraceFlags(),  // 继承 TraceFlags
        TraceState: parent.TraceState(),  // 继承 TraceState
    })
}

// 创建远程 SpanContext
func createRemoteSpanContext() trace.SpanContext {
    return trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    generateTraceID(),
        SpanID:     generateSpanID(),
        TraceFlags: trace.FlagsSampled,
        Remote:     true,  // 标记为远程
    })
}

// 工具函数
func generateTraceID() trace.TraceID {
    var id trace.TraceID
    rand.Read(id[:])
    return id
}

func generateSpanID() trace.SpanID {
    var id trace.SpanID
    rand.Read(id[:])
    return id
}

func printSpanContext(sc trace.SpanContext) {
    fmt.Printf("TraceID:    %s\n", sc.TraceID().String())
    fmt.Printf("SpanID:     %s\n", sc.SpanID().String())
    fmt.Printf("TraceFlags: %02x (Sampled: %v)\n", sc.TraceFlags(), sc.IsSampled())
    fmt.Printf("TraceState: %s\n", sc.TraceState().String())
    fmt.Printf("Remote:     %v\n", sc.IsRemote())
    fmt.Printf("Valid:      %v\n", sc.IsValid())
    fmt.Println()
}
```

### SpanContext 验证

```go
// 验证 SpanContext
func validateSpanContext(sc trace.SpanContext) error {
    // 1. 检查是否有效
    if !sc.IsValid() {
        return fmt.Errorf("invalid span context")
    }

    // 2. 检查 TraceID
    if !sc.TraceID().IsValid() {
        return fmt.Errorf("invalid trace ID")
    }

    // 3. 检查 SpanID
    if !sc.SpanID().IsValid() {
        return fmt.Errorf("invalid span ID")
    }

    // 4. 检查 TraceState 长度
    if len(sc.TraceState().String()) > 512 {
        return fmt.Errorf("tracestate too long")
    }

    return nil
}
```

### SpanContext 比较

```go
// 比较两个 SpanContext
func compareSpanContext(sc1, sc2 trace.SpanContext) bool {
    return sc1.TraceID() == sc2.TraceID() &&
           sc1.SpanID() == sc2.SpanID() &&
           sc1.TraceFlags() == sc2.TraceFlags() &&
           sc1.TraceState().String() == sc2.TraceState().String()
}

// 检查是否在同一个 Trace
func sameTrace(sc1, sc2 trace.SpanContext) bool {
    return sc1.TraceID() == sc2.TraceID()
}
```

---

## 最佳实践

### 1. 始终检查有效性

```go
// ✅ 推荐
spanCtx := trace.SpanContextFromContext(ctx)
if spanCtx.IsValid() {
    // 使用 SpanContext
    fmt.Printf("TraceID: %s\n", spanCtx.TraceID().String())
}

// ❌ 避免
spanCtx := trace.SpanContextFromContext(ctx)
fmt.Printf("TraceID: %s\n", spanCtx.TraceID().String())  // 可能是无效的
```

### 2. 正确传播 Context

```go
// ✅ 推荐：使用 Context 传播
func processRequest(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()
    
    doSubTask(ctx)  // 传递 ctx
}

// ❌ 避免：手动传递 SpanContext
func processRequest(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()
    
    spanCtx := span.SpanContext()
    doSubTask(spanCtx)  // 容易出错
}
```

### 3. 使用标准传播器

```go
// ✅ 推荐：使用 OpenTelemetry 的标准传播器
import "go.opentelemetry.io/otel"
import "go.opentelemetry.io/otel/propagation"

// 配置传播器
otel.SetTextMapPropagator(propagation.NewCompositeTextMapPropagator(
    propagation.TraceContext{},  // W3C Trace Context
    propagation.Baggage{},       // W3C Baggage
))

// 使用
propagator := otel.GetTextMapPropagator()
propagator.Inject(ctx, carrier)
```

### 4. 处理远程 SpanContext

```go
// ✅ 推荐：检查是否远程
spanCtx := trace.SpanContextFromContext(ctx)
if spanCtx.IsRemote() {
    // 这是从远程服务接收的
    // 创建服务器端 Span
    ctx, span := tracer.Start(ctx, "handle_remote_request",
        trace.WithSpanKind(trace.SpanKindServer),
    )
    defer span.End()
}
```

### 5. TraceState 管理

```go
// ✅ 推荐：谨慎修改 TraceState
func updateTraceState(sc trace.SpanContext, key, value string) trace.SpanContext {
    ts := sc.TraceState()
    
    // 插入新值
    ts, err := ts.Insert(key, value)
    if err != nil {
        // 处理错误（如超过限制）
        return sc
    }
    
    return sc.WithTraceState(ts)
}

// ❌ 避免：过度使用 TraceState
// TraceState 有大小限制 (512 字符)
```

---

## 常见问题

### Q1: SpanContext 可以修改吗？

**A**: 不可以。SpanContext 是不可变的。

```go
// SpanContext 创建后不能修改
spanCtx := trace.NewSpanContext(config)
// 无法修改 spanCtx 的任何字段

// 如果需要"修改"，创建新的 SpanContext
newSpanCtx := trace.NewSpanContext(trace.SpanContextConfig{
    TraceID:    spanCtx.TraceID(),
    SpanID:     generateSpanID(),  // 新的 SpanID
    TraceFlags: trace.FlagsSampled,  // 新的 Flags
})
```

---

### Q2: 如何在 HTTP 请求中传递 SpanContext？

**A**: 使用 W3C Trace Context 标准（traceparent 和 tracestate 头）。

```go
// 使用 OpenTelemetry 的传播器
propagator := otel.GetTextMapPropagator()

// 客户端：注入
propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))

// 服务器端：提取
ctx = propagator.Extract(ctx, propagation.HeaderCarrier(req.Header))
```

---

### Q3: TraceID 冲突怎么办？

**A**: 使用加密安全的随机数生成器，冲突概率极低（2^-128）。

```go
// 使用 crypto/rand 生成 TraceID
var traceID trace.TraceID
_, err := rand.Read(traceID[:])  // crypto/rand.Read
if err != nil {
    // 处理错误
}
```

---

### Q4: 如何判断 SpanContext 是否来自远程？

**A**: 使用 `IsRemote()` 方法。

```go
spanCtx := trace.SpanContextFromContext(ctx)
if spanCtx.IsRemote() {
    // 来自远程进程
    // 通常创建 SERVER 类型的 Span
    ctx, span := tracer.Start(ctx, "handle_request",
        trace.WithSpanKind(trace.SpanKindServer),
    )
}
```

---

### Q5: TraceState 有什么用途？

**A**: 用于传递供应商特定的追踪信息，不影响核心追踪功能。

```go
// 示例：传递采样决策
ts, _ := ts.Insert("sampling.priority", "1")

// 示例：传递租户信息
ts, _ := ts.Insert("tenant", "customer-123")

// 示例：传递请求特征
ts, _ := ts.Insert("feature.flag", "new_ui")
```

---

## 参考资源

### 官方文档

- [OpenTelemetry SpanContext](https://opentelemetry.io/docs/specs/otel/trace/api/#spancontext)
- [W3C Trace Context](https://www.w3.org/TR/trace-context/)
- [W3C Trace Context Level 2 (Draft)](https://w3c.github.io/trace-context/)

### Go 实现6

- [go.opentelemetry.io/otel/trace](https://pkg.go.dev/go.opentelemetry.io/otel/trace)
- [go.opentelemetry.io/otel/propagation](https://pkg.go.dev/go.opentelemetry.io/otel/propagation)

### 相关文档

- [01_Span结构.md](./01_Span结构.md) - Span 数据结构
- [03_SpanKind.md](./03_SpanKind.md) - Span 类型
- [../02_Context_Propagation/](../02_Context_Propagation/) - 上下文传播详解

---

**🎉 恭喜！你已经掌握了 SpanContext 的完整知识！**

下一步：学习 [SpanKind](./03_SpanKind.md) 了解不同类型的 Span。

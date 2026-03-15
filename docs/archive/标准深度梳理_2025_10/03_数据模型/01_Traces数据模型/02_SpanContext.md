# SpanContext 完整定义

> **OTLP版本**: v1.0.0 (Stable)  
> **最后更新**: 2025年10月8日

---

## 目录

- [SpanContext 完整定义](#spancontext-完整定义)
  - [目录](#目录)
  - [1. 概念定义](#1-概念定义)
    - [1.1 正式定义](#11-正式定义)
    - [1.2 核心职责](#12-核心职责)
    - [1.3 不可变性](#13-不可变性)
  - [2. 字段详解](#2-字段详解)
    - [2.1 trace\_id](#21-trace_id)
    - [2.2 span\_id](#22-span_id)
    - [2.3 trace\_flags](#23-trace_flags)
    - [2.4 trace\_state](#24-trace_state)
    - [2.5 is\_remote](#25-is_remote)
  - [3. W3C Trace Context 规范](#3-w3c-trace-context-规范)
    - [3.1 traceparent 头部](#31-traceparent-头部)
    - [3.2 tracestate 头部](#32-tracestate-头部)
  - [4. 传播机制](#4-传播机制)
    - [4.1 进程内传播](#41-进程内传播)
    - [4.2 跨进程传播](#42-跨进程传播)
    - [4.3 Baggage 传播](#43-baggage-传播)
  - [5. 形式化规范](#5-形式化规范)
    - [5.1 SpanContext 定义](#51-spancontext-定义)
    - [5.2 不变量](#52-不变量)
    - [5.3 等价关系](#53-等价关系)
  - [6. 实现示例](#6-实现示例)
    - [6.1 创建 SpanContext](#61-创建-spancontext)
    - [6.2 传播 SpanContext](#62-传播-spancontext)
    - [6.3 提取 SpanContext](#63-提取-spancontext)
  - [7. 采样决策](#7-采样决策)
    - [7.1 采样标志](#71-采样标志)
    - [7.2 采样策略](#72-采样策略)
  - [8. 安全性考虑](#8-安全性考虑)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 参考资源](#10-参考资源)

## 1. 概念定义

### 1.1 正式定义

**SpanContext** 形式化定义：

```text
SpanContext = (tid, sid, flags, state, remote)

其中:
- tid ∈ TraceID = {0,1}^128 \ {0^128}
  trace标识符 (16字节，非全零)
  
- sid ∈ SpanID = {0,1}^64 \ {0^64}
  span标识符 (8字节，非全零)
  
- flags ∈ TraceFlags = {0,1}^8
  追踪标志 (1字节)
  
- state ∈ TraceState = String
  W3C tracestate (最多512字节)
  
- remote ∈ Boolean
  是否来自远程上下文

约束:
1. tid ≠ 0^128 (trace_id非全零)
2. sid ≠ 0^64 (span_id非全零)
3. flags.sampled ∈ {0, 1}
4. |state| ≤ 512 bytes
5. remote = true ⟺ context从另一个进程传入
```

### 1.2 核心职责

**SpanContext的作用**：

```text
1. 唯一标识
   - trace_id: 标识整个请求链路
   - span_id: 标识当前操作

2. 上下文传播
   - 跨进程边界传递追踪信息
   - 通过HTTP头、gRPC metadata等

3. 采样决策
   - trace_flags.sampled标记是否采样
   - 传播采样决策

4. 厂商状态
   - tracestate携带厂商特定信息
   - 支持多厂商协作

5. 父子关联
   - parent_span_id引用SpanContext.span_id
   - 构建调用树
```

### 1.3 不可变性

**不可变性保证**：

```text
SpanContext是不可变的 (Immutable):

定理: SpanContext一旦创建，其字段不可修改

形式化:
∀ sc ∈ SpanContext, ∀ t1, t2 ∈ Time,
  tid(sc, t1) = tid(sc, t2) ∧
  sid(sc, t1) = sid(sc, t2) ∧
  flags(sc, t1) = flags(sc, t2) ∧
  state(sc, t1) = state(sc, t2)

原因:
1. 保证传播一致性
2. 线程安全
3. 简化实现

修改方式:
不能修改现有SpanContext，只能创建新的SpanContext
```

---

## 2. 字段详解

### 2.1 trace_id

**定义与格式**：

```text
字段名: trace_id
类型: bytes (16字节)
编码: 128位随机数

生成规则:
1. 使用加密安全随机数生成器
   - Go: crypto/rand
   - Java: SecureRandom
   - Python: secrets

2. 非全零
   00000000-0000-0000-0000-000000000000 无效

3. 全局唯一
   - 冲突概率: ~2^-128 (可忽略)

表示形式:
- 二进制: 16字节 bytes
- 十六进制: 32字符字符串
- 示例: 5b8efff798038103d269b633813fc60c

使用场景:
- 关联同一请求的所有spans
- 查询追踪数据的主键
- 跨系统传播
```

### 2.2 span_id

**定义与格式**：

```text
字段名: span_id
类型: bytes (8字节)
编码: 64位随机数

生成规则:
1. 使用加密安全随机数生成器
2. 非全零: 0000000000000000 无效
3. trace内唯一 (实际全局唯一)

表示形式:
- 二进制: 8字节 bytes
- 十六进制: 16字符字符串
- 示例: eee19b7ec3c1b174

使用场景:
- 唯一标识span
- 作为parent_span_id被子span引用
- Link引用
```

### 2.3 trace_flags

**标志位定义**：

```text
字段名: trace_flags
类型: uint8 (1字节)
位掩码: 8位标志

位定义:
Bit 0 (最低位): sampled
  - 0: 未采样
  - 1: 已采样
  
Bit 1-7: 保留 (目前未使用)

示例:
00000000 (0x00): 未采样
00000001 (0x01): 已采样
00000011 (0x03): 采样 + 未来扩展

访问方式:
sampled = (trace_flags & 0x01) != 0

设置方式:
trace_flags |= 0x01  // 设置采样
trace_flags &= ~0x01 // 清除采样
```

**采样标志语义**：

```text
sampled = 0 (未采样):
- Span不会被导出到后端
- 仅记录本地数据
- 减少系统开销

sampled = 1 (已采样):
- Span会被完整记录
- 导出到追踪后端
- 完整的调用链路

采样决策传播:
父Span的sampled标志通常传递给子Span
但子Span可以:
- 继承父Span决策 (通常)
- 强制采样 (特殊情况)
- 强制不采样 (极少)
```

### 2.4 trace_state

**W3C TraceState 定义**：

```text
字段名: trace_state
类型: string
最大长度: 512字节

格式:
key1=value1,key2=value2,...

键值对规则:
- 逗号分隔
- 每个键值对 ≤ 128字节
- 最多32个键值对

键 (key) 规则:
- 格式: [a-z0-9*/\-_]+
- 可包含vendor前缀: vendor@key
- 示例: rojo, congo@t61

值 (value) 规则:
- 可打印ASCII字符 (0x20-0x7E)
- 排除: , (逗号) 和 = (等号)
- 示例: 00f067aa0ba902b7

完整示例:
"rojo=00f067aa0ba902b7,congo@t61=rcWkgMzE"

用途:
1. 传播厂商特定信息
   - 采样决策参数
   - 路由信息
   - 优先级标记

2. 多厂商协作
   - 不同厂商添加自己的状态
   - 互不干扰
   - 按需解析

3. 采样参数
   - 采样率
   - 采样策略ID
   - 成本控制
```

### 2.5 is_remote

**远程标志**：

```text
字段名: is_remote
类型: bool
说明: SDK内部字段 (不在OTLP协议中)

语义:
is_remote = false:
  - SpanContext在当前进程创建
  - 本地span的上下文
  
is_remote = true:
  - SpanContext从另一个进程提取
  - 跨进程调用的上游上下文
  - 通过HTTP头、gRPC metadata传入

用途:
1. 区分本地和远程span
2. 确定span kind:
   - remote=true → 通常是SERVER/CONSUMER
   - remote=false → 通常是INTERNAL/CLIENT/PRODUCER

3. 性能优化:
   - 远程上下文可能需要特殊处理
   - 采样决策传播

示例:
// 本地创建span
ctx, span := tracer.Start(ctx, "local-op")
// span.SpanContext().IsRemote() == false

// HTTP请求处理
ctx := propagator.Extract(r.Context(), r.Header)
ctx, span := tracer.Start(ctx, "handle-request")
// span.SpanContext().IsRemote() == true
```

---

## 3. W3C Trace Context 规范

### 3.1 traceparent 头部

**格式定义**：

```text
HTTP头部名称: traceparent
格式: version-trace_id-span_id-trace_flags

version: 2位十六进制 (当前: 00)
trace_id: 32位十六进制 (16字节)
span_id: 16位十六进制 (8字节)
trace_flags: 2位十六进制 (1字节)

完整示例:
traceparent: 00-5b8efff798038103d269b633813fc60c-eee19b7ec3c1b174-01

解析:
version:     00
trace_id:    5b8efff798038103d269b633813fc60c
span_id:     eee19b7ec3c1b174
trace_flags: 01 (采样)

验证规则:
1. 必须4个字段，用 - 分隔
2. version必须是 00
3. trace_id非全零
4. span_id非全零
5. trace_flags是有效字节
```

**HTTP传播示例**：

```text
客户端发送:
GET /api/users HTTP/1.1
Host: example.com
traceparent: 00-5b8efff798038103d269b633813fc60c-eee19b7ec3c1b174-01
tracestate: rojo=00f067aa0ba902b7

服务器接收:
1. 解析traceparent
2. 提取trace_id, span_id, flags, state
3. 创建SpanContext
4. 作为父上下文创建新span
```

### 3.2 tracestate 头部

**格式定义**：

```text
HTTP头部名称: tracestate
格式: key1=value1,key2=value2

示例:
tracestate: rojo=00f067aa0ba902b7,congo@t61=rcWkgMzE

规则:
1. 最多32个键值对
2. 总长度 ≤ 512字节
3. 键值对用逗号分隔
4. 空格可选 (推荐无空格)

更新策略:
收到tracestate后:
1. 解析现有键值对
2. 添加/更新自己的键值对 (前置)
3. 保留其他厂商的键值对
4. 确保总长度 ≤ 512字节

示例:
收到: rojo=00f067aa0ba902b7
处理后: vendor=newvalue,rojo=00f067aa0ba902b7
```

---

## 4. 传播机制

### 4.1 进程内传播

**Context传播 (Go)**：

```go
import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// 在进程内传播
func handler(ctx context.Context) {
    // ctx包含SpanContext
    
    // 创建子span (自动继承SpanContext)
    ctx, span := tracer.Start(ctx, "child-operation")
    defer span.End()
    
    // 调用其他函数
    anotherFunction(ctx)  // 传递ctx
}

func anotherFunction(ctx context.Context) {
    // 可以访问父span的SpanContext
    spanContext := trace.SpanContextFromContext(ctx)
    
    if spanContext.IsValid() {
        fmt.Printf("Trace ID: %s\n", spanContext.TraceID())
        fmt.Printf("Span ID: %s\n", spanContext.SpanID())
    }
}
```

### 4.2 跨进程传播

**HTTP传播 (Go)**：

```go
import (
    "net/http"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/propagation"
)

// 客户端: 注入SpanContext到HTTP头
func makeHTTPRequest(ctx context.Context, url string) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    // 注入traceparent和tracestate头部
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    resp, _ := http.DefaultClient.Do(req)
    defer resp.Body.Close()
}

// 服务器: 提取SpanContext从HTTP头
func handleHTTPRequest(w http.ResponseWriter, r *http.Request) {
    // 提取SpanContext
    ctx := otel.GetTextMapPropagator().Extract(r.Context(), 
        propagation.HeaderCarrier(r.Header))
    
    // 创建span (作为远程span的子span)
    ctx, span := tracer.Start(ctx, "handle-request",
        trace.WithSpanKind(trace.SpanKindServer))
    defer span.End()
    
    // 处理请求
    handleRequest(ctx)
}
```

**gRPC传播 (Go)**：

```go
import (
    "google.golang.org/grpc"
    "google.golang.org/grpc/metadata"
    "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
)

// 客户端: 自动注入
conn, _ := grpc.Dial(addr,
    grpc.WithUnaryInterceptor(otelgrpc.UnaryClientInterceptor()),
)

// 服务器: 自动提取
server := grpc.NewServer(
    grpc.UnaryInterceptor(otelgrpc.UnaryServerInterceptor()),
)
```

### 4.3 Baggage 传播

**Baggage定义**：

```text
Baggage: 与SpanContext一起传播的键值对

特点:
- 随SpanContext跨进程传播
- 不属于span数据
- 用于传播应用级元数据

用途:
- 用户ID
- 租户ID
- 特性标志
- 请求优先级

W3C Baggage格式:
baggage: key1=value1,key2=value2

示例:
baggage: userId=12345,tier=premium
```

**Baggage使用 (Go)**：

```go
import (
    "go.opentelemetry.io/otel/baggage"
)

// 设置Baggage
member, _ := baggage.NewMember("userId", "12345")
bag, _ := baggage.New(member)
ctx = baggage.ContextWithBaggage(ctx, bag)

// 读取Baggage
bag = baggage.FromContext(ctx)
userID := bag.Member("userId").Value()
```

---

## 5. 形式化规范

### 5.1 SpanContext 定义

**集合论定义**：

```text
定义 (SpanContext):
SpanContext是一个五元组:
SC = (tid, sid, flags, state, remote)

其中:
- tid ∈ TraceID = {0,1}^128 \ {0^128}
- sid ∈ SpanID = {0,1}^64 \ {0^64}
- flags ∈ {0,...,255}
- state ∈ String, |state| ≤ 512
- remote ∈ {true, false}

有效性谓词:
IsValid(SC) ⟺ tid ≠ 0^128 ∧ sid ≠ 0^64

采样谓词:
IsSampled(SC) ⟺ (flags & 0x01) = 1
```

### 5.2 不变量

**SpanContext不变量**：

```text
定理1 (不可变性):
∀ SC ∈ SpanContext, ∀ t1, t2 ∈ Time,
  SC(t1) = SC(t2)

定理2 (有效性不变):
∀ SC, IsValid(SC) ⟺ (tid(SC) ≠ 0^128 ∧ sid(SC) ≠ 0^64)

定理3 (TraceID一致性):
∀ span S, child C,
  如果 parent_span_id(C) = span_id(S),
  则 trace_id(C) = trace_id(S)

定理4 (采样传播):
∀ parent P, child C,
  IsSampled(SpanContext(P)) → IsSampled(SpanContext(C))
  (通常情况,可被策略覆盖)
```

### 5.3 等价关系

**SpanContext等价**：

```text
定义 (等价):
SC1 ≡ SC2 ⟺
  tid(SC1) = tid(SC2) ∧
  sid(SC1) = sid(SC2) ∧
  flags(SC1) = flags(SC2) ∧
  state(SC1) = state(SC2)

注意: remote字段不参与等价判断
原因: remote是本地标记,不影响追踪语义

性质:
1. 自反性: SC ≡ SC
2. 对称性: SC1 ≡ SC2 → SC2 ≡ SC1
3. 传递性: SC1 ≡ SC2 ∧ SC2 ≡ SC3 → SC1 ≡ SC3
```

---

## 6. 实现示例

### 6.1 创建 SpanContext

**Go实现**：

```go
package main

import (
    "crypto/rand"
    "encoding/hex"
    "go.opentelemetry.io/otel/trace"
)

// 生成trace_id
func generateTraceID() trace.TraceID {
    var id [16]byte
    rand.Read(id[:])
    return trace.TraceID(id)
}

// 生成span_id
func generateSpanID() trace.SpanID {
    var id [8]byte
    rand.Read(id[:])
    return trace.SpanID(id)
}

// 创建SpanContext
func createSpanContext() trace.SpanContext {
    traceID := generateTraceID()
    spanID := generateSpanID()
    
    config := trace.SpanContextConfig{
        TraceID:    traceID,
        SpanID:     spanID,
        TraceFlags: trace.FlagsSampled, // 采样
        TraceState: trace.TraceState{},
        Remote:     false,
    }
    
    return trace.NewSpanContext(config)
}

// 使用示例
func main() {
    sc := createSpanContext()
    
    fmt.Printf("Trace ID: %s\n", sc.TraceID())
    fmt.Printf("Span ID: %s\n", sc.SpanID())
    fmt.Printf("Sampled: %v\n", sc.IsSampled())
    fmt.Printf("Valid: %v\n", sc.IsValid())
}
```

### 6.2 传播 SpanContext

**HTTP注入**：

```go
import (
    "net/http"
    "go.opentelemetry.io/otel/propagation"
)

type Propagator struct {
    tc propagation.TraceContext
}

func (p *Propagator) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
    sc := trace.SpanContextFromContext(ctx)
    if !sc.IsValid() {
        return
    }
    
    // 注入traceparent
    traceparent := fmt.Sprintf("00-%s-%s-%02x",
        sc.TraceID(),
        sc.SpanID(),
        sc.TraceFlags())
    carrier.Set("traceparent", traceparent)
    
    // 注入tracestate
    if ts := sc.TraceState(); ts.Len() > 0 {
        carrier.Set("tracestate", ts.String())
    }
}
```

### 6.3 提取 SpanContext

**HTTP提取**：

```go
func (p *Propagator) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
    // 提取traceparent
    traceparent := carrier.Get("traceparent")
    if traceparent == "" {
        return ctx
    }
    
    // 解析traceparent
    parts := strings.Split(traceparent, "-")
    if len(parts) != 4 || parts[0] != "00" {
        return ctx
    }
    
    // 解析trace_id
    traceID, _ := trace.TraceIDFromHex(parts[1])
    
    // 解析span_id
    spanID, _ := trace.SpanIDFromHex(parts[2])
    
    // 解析trace_flags
    flags, _ := hex.DecodeString(parts[3])
    
    // 提取tracestate
    tracestate := carrier.Get("tracestate")
    ts, _ := trace.ParseTraceState(tracestate)
    
    // 创建SpanContext
    config := trace.SpanContextConfig{
        TraceID:    traceID,
        SpanID:     spanID,
        TraceFlags: trace.TraceFlags(flags[0]),
        TraceState: ts,
        Remote:     true, // 远程上下文
    }
    
    sc := trace.NewSpanContext(config)
    
    return trace.ContextWithSpanContext(ctx, sc)
}
```

---

## 7. 采样决策

### 7.1 采样标志

**采样决策流程**：

```text
采样决策时机:
1. Span创建时
   - 检查父span的sampled标志
   - 应用采样策略
   - 设置trace_flags.sampled

2. 决策因素:
   - 父span采样状态
   - 采样率配置
   - trace_state中的参数
   - 应用规则 (如: 总是采样错误)

3. 决策传播:
   sampled标志随SpanContext跨进程传播

采样策略:
┌─────────────────┬──────────────────┐
│ 策略            │ 说明             │
├─────────────────┼──────────────────┤
│ AlwaysOn        │ 总是采样         │
│ AlwaysOff       │ 总是不采样       │
│ TraceIDRatioBased│ 基于trace_id采样 │
│ ParentBased     │ 基于父span       │
│ Custom          │ 自定义规则       │
└─────────────────┴──────────────────┘
```

### 7.2 采样策略

**TraceID比例采样**：

```go
type TraceIDRatioBasedSampler struct {
    traceIDUpperBound uint64
}

func NewTraceIDRatioBasedSampler(fraction float64) *TraceIDRatioBasedSampler {
    return &TraceIDRatioBasedSampler{
        traceIDUpperBound: uint64(fraction * (1 << 63)),
    }
}

func (s *TraceIDRatioBasedSampler) ShouldSample(p SamplingParameters) SamplingResult {
    // 使用trace_id的低8字节作为随机数
    traceIDBytes := p.TraceID[8:]
    x := binary.BigEndian.Uint64(traceIDBytes)
    
    if x < s.traceIDUpperBound {
        return SamplingResult{
            Decision:   RecordAndSample,
            TraceState: p.TraceState,
        }
    }
    
    return SamplingResult{
        Decision: Drop,
    }
}
```

---

## 8. 安全性考虑

**隐私与安全**：

```text
1. trace_id和span_id生成
   ✅ 使用加密安全随机数
   ❌ 不要使用时间戳、序列号

2. tracestate内容
   ✅ 不要放敏感信息
   ✅ 验证tracestate长度
   ❌ 不要信任未验证的tracestate

3. 传播安全
   ✅ HTTPS传输
   ✅ 验证traceparent格式
   ❌ 不要盲目接受所有头部

4. 注入攻击防护
   ✅ 验证trace_id和span_id格式
   ✅ 限制tracestate长度
   ❌ 不要执行tracestate中的代码
```

---

## 9. 最佳实践

```text
1. 生成ID
   ✅ 使用crypto/rand (Go)
   ✅ 使用SecureRandom (Java)
   ❌ 不要使用math/rand

2. 传播
   ✅ 使用标准Propagator
   ✅ 支持W3C Trace Context
   ✅ 处理tracestate

3. 采样
   ✅ 配置合理采样率
   ✅ 总是采样错误
   ✅ 传播采样决策

4. 验证
   ✅ 检查SpanContext.IsValid()
   ✅ 验证trace_id和span_id非零
   ✅ 限制tracestate大小

5. 性能
   ✅ 复用SpanContext (不可变)
   ✅ 避免频繁序列化
   ✅ 缓存Propagator
```

---

## 10. 参考资源

- **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>
- **W3C Baggage**: <https://www.w3.org/TR/baggage/>
- **OpenTelemetry Spec**: <https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/trace/api.md#spancontext>
- **Go SDK**: <https://pkg.go.dev/go.opentelemetry.io/otel/trace#SpanContext>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**下一步**: [03_SpanKind.md](./03_SpanKind.md)

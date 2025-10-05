# CSP-OTLP 同构映射

## 目录

- [CSP-OTLP 同构映射](#csp-otlp-同构映射)
  - [目录](#目录)
  - [1. 同构关系概述](#1-同构关系概述)
  - [2. 进程与 Span 的映射](#2-进程与-span-的映射)
    - [2.1 基本映射](#21-基本映射)
    - [2.2 进程组合](#22-进程组合)
  - [3. Channel 与 Context 传播](#3-channel-与-context-传播)
    - [3.1 通信语义](#31-通信语义)
    - [3.2 Context 传播](#32-context-传播)
  - [4. 并发模式映射](#4-并发模式映射)
    - [4.1 顺序组合](#41-顺序组合)
    - [4.2 并行组合](#42-并行组合)
    - [4.3 选择组合](#43-选择组合)
  - [5. 形式化证明](#5-形式化证明)
    - [5.1 结构保持](#51-结构保持)
    - [5.2 语义等价](#52-语义等价)
  - [6. 实践应用](#6-实践应用)
  - [7. 参考资料](#7-参考资料)

## 1. 同构关系概述

CSP（Communicating Sequential Processes）与 OTLP（OpenTelemetry Protocol）之间存在深刻的同构关系：

**定义**：存在双射 φ: CSP → OTLP，使得：

```text
φ(P₁ ; P₂) = Span(φ(P₁)) → Span(φ(P₂))  (顺序组合)
φ(P₁ || P₂) = Span(φ(P₁)) ⊗ Span(φ(P₂))  (并行组合)
φ(P₁ □ P₂) = Span(φ(P₁)) ⊕ Span(φ(P₂))  (选择组合)
```

其中：

- `;` 表示 CSP 顺序组合
- `||` 表示 CSP 并行组合
- `□` 表示 CSP 外部选择
- `→` 表示 Span 的父子关系
- `⊗` 表示 Span 的并行关系（通过 Links）
- `⊕` 表示 Span 的条件分支

## 2. 进程与 Span 的映射

### 2.1 基本映射

**CSP 进程**：

```csp
PROCESS = input?x -> compute(x) -> output!result -> PROCESS
```

**OTLP Span**：

```go
func process(ctx context.Context, input Input) Output {
    // 进程开始 → Span 开始
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()  // 进程结束 → Span 结束
    
    // input?x → Span Event
    span.AddEvent("input_received", trace.WithAttributes(
        attribute.String("input.id", input.ID),
    ))
    
    // compute(x) → Span 执行
    result := compute(input)
    
    // output!result → Span Event
    span.AddEvent("output_sent", trace.WithAttributes(
        attribute.String("result.id", result.ID),
    ))
    
    return result
}
```

**映射关系**：

| CSP 元素 | OTLP 元素 | 说明 |
|---------|----------|------|
| Process | Span | 进程对应一个 Span |
| input?x | Event | 输入事件 |
| compute(x) | Span Duration | 计算时间 |
| output!y | Event | 输出事件 |
| Process State | Span Attributes | 进程状态 |

### 2.2 进程组合

**顺序组合**（Sequential Composition）：

```csp
P = A ; B ; C
```

```go
func P(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "P")
    defer span.End()
    
    A(ctx)  // Child Span
    B(ctx)  // Child Span
    C(ctx)  // Child Span
}
```

**Span 树结构**：

```text
P (parent)
├── A (child)
├── B (child)
└── C (child)
```

## 3. Channel 与 Context 传播

### 3.1 通信语义

**CSP Channel**：

```csp
P = c!msg -> P'
Q = c?x -> Q'(x)

System = P || Q
```

**Go + OTLP 实现**：

```go
// Producer (P)
func producer(ctx context.Context, ch chan<- Message) {
    ctx, span := tracer.Start(ctx, "producer")
    defer span.End()
    
    msg := Message{
        Data:    "hello",
        TraceID: span.SpanContext().TraceID(),  // 传递 Trace 上下文
        SpanID:  span.SpanContext().SpanID(),
    }
    
    span.AddEvent("send_message")
    ch <- msg
}

// Consumer (Q)
func consumer(ctx context.Context, ch <-chan Message) {
    for msg := range ch {
        // 从消息中恢复 Trace 上下文
        ctx := trace.ContextWithSpanContext(context.Background(),
            trace.NewSpanContext(trace.SpanContextConfig{
                TraceID: msg.TraceID,
                SpanID:  msg.SpanID,
            }),
        )
        
        ctx, span := tracer.Start(ctx, "consumer")
        span.AddEvent("receive_message")
        
        process(ctx, msg.Data)
        span.End()
    }
}
```

### 3.2 Context 传播

**W3C Trace Context 映射**：

```text
CSP Channel Message:
  msg = (data, context)

OTLP Context:
  traceparent: 00-{trace_id}-{span_id}-{flags}
  tracestate: vendor1=value1,vendor2=value2
```

**实现**：

```go
type Message struct {
    Data      interface{}
    TraceID   trace.TraceID
    SpanID    trace.SpanID
    TraceFlags trace.TraceFlags
}

// 注入 Trace Context
func injectContext(msg *Message, span trace.Span) {
    sc := span.SpanContext()
    msg.TraceID = sc.TraceID()
    msg.SpanID = sc.SpanID()
    msg.TraceFlags = sc.TraceFlags()
}

// 提取 Trace Context
func extractContext(msg Message) context.Context {
    sc := trace.NewSpanContext(trace.SpanContextConfig{
        TraceID:    msg.TraceID,
        SpanID:     msg.SpanID,
        TraceFlags: msg.TraceFlags,
    })
    return trace.ContextWithSpanContext(context.Background(), sc)
}
```

## 4. 并发模式映射

### 4.1 顺序组合

**CSP**：`P = A ; B`

**OTLP**：

```go
func P(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "P")
    defer span.End()
    
    A(ctx)  // parent_span_id = span.SpanID()
    B(ctx)  // parent_span_id = span.SpanID()
}
```

**Trace 结构**：

```text
Trace
└── P
    ├── A
    └── B
```

### 4.2 并行组合

**CSP**：`P = A || B`

**OTLP**：

```go
func P(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "P")
    defer span.End()
    
    var wg sync.WaitGroup
    
    wg.Add(1)
    go func() {
        defer wg.Done()
        A(ctx)  // 并行 Span
    }()
    
    wg.Add(1)
    go func() {
        defer wg.Done()
        B(ctx)  // 并行 Span
    }()
    
    wg.Wait()
}
```

**Trace 结构**：

```text
Trace
└── P
    ├── A (parallel)
    └── B (parallel)
```

**使用 Links 表示并行关系**：

```go
func P(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "P")
    defer span.End()
    
    var wg sync.WaitGroup
    var spanA, spanB trace.Span
    
    wg.Add(1)
    go func() {
        defer wg.Done()
        _, spanA = tracer.Start(ctx, "A")
        defer spanA.End()
        
        // A 链接到 B（表示并行关系）
        if spanB != nil {
            spanA.AddLink(trace.Link{
                SpanContext: spanB.SpanContext(),
            })
        }
    }()
    
    wg.Add(1)
    go func() {
        defer wg.Done()
        _, spanB = tracer.Start(ctx, "B")
        defer spanB.End()
    }()
    
    wg.Wait()
}
```

### 4.3 选择组合

**CSP**：`P = (a -> A) □ (b -> B)`

**OTLP**：

```go
func P(ctx context.Context, chA, chB <-chan Message) {
    ctx, span := tracer.Start(ctx, "P")
    defer span.End()
    
    select {
    case msg := <-chA:
        span.SetAttributes(attribute.String("choice", "A"))
        A(ctx, msg)
        
    case msg := <-chB:
        span.SetAttributes(attribute.String("choice", "B"))
        B(ctx, msg)
    }
}
```

**Trace 结构**（条件分支）：

```text
Trace
└── P (choice=A)
    └── A

或

Trace
└── P (choice=B)
    └── B
```

## 5. 形式化证明

### 5.1 结构保持

**定理 1**（结构同态）：映射 φ: CSP → OTLP 保持进程结构

**证明**：

1. **顺序组合**：

   ```text
   φ(P ; Q) = Span_P → Span_Q
   其中 Span_Q.parent_span_id = Span_P.span_id
   ```

2. **并行组合**：

   ```text
   φ(P || Q) = Span_P ⊗ Span_Q
   其中 Span_P.parent_span_id = Span_Q.parent_span_id
   ```

3. **选择组合**：

   ```text
   φ(P □ Q) = Span_P ⊕ Span_Q
   其中只有一个 Span 被创建（根据运行时选择）
   ```

### 5.2 语义等价

**定理 2**（语义保持）：CSP 进程的行为语义在 OTLP 中得到保持

**证明要点**：

1. **因果关系**：CSP 的 happens-before 关系对应 OTLP 的 parent-child 关系
2. **时间序列**：CSP 事件序列对应 Span 的时间戳序列
3. **通信语义**：Channel 通信对应 Span Events 和 Context 传播

**形式化**：

```text
对于任意 CSP 进程 P 和事件序列 σ：
  P ⟹ σ  (P 可以产生事件序列 σ)
当且仅当
  φ(P) ⟹ τ(σ)  (φ(P) 产生对应的 Span 序列)

其中 τ 是事件到 Span Events 的映射
```

## 6. 实践应用

**完整示例**：

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("csp-otlp-example")

// CSP: PRODUCER = produce!item -> PRODUCER
func producer(ctx context.Context, ch chan<- Item) {
    ctx, span := tracer.Start(ctx, "producer")
    defer span.End()
    
    for i := 0; i < 10; i++ {
        item := Item{ID: i}
        
        span.AddEvent("produce", trace.WithAttributes(
            attribute.Int("item.id", i),
        ))
        
        ch <- item
    }
    close(ch)
}

// CSP: CONSUMER = consume?item -> process(item) -> CONSUMER
func consumer(ctx context.Context, ch <-chan Item) {
    ctx, span := tracer.Start(ctx, "consumer")
    defer span.End()
    
    for item := range ch {
        span.AddEvent("consume", trace.WithAttributes(
            attribute.Int("item.id", item.ID),
        ))
        
        process(ctx, item)
    }
}

// CSP: PROCESS = compute(item) -> PROCESS
func process(ctx context.Context, item Item) {
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("item.id", item.ID),
    )
    
    // 处理逻辑
    result := compute(item)
    
    span.AddEvent("processed", trace.WithAttributes(
        attribute.String("result", result),
    ))
}

// CSP: SYSTEM = PRODUCER || CONSUMER
func main() {
    ctx := context.Background()
    ctx, span := tracer.Start(ctx, "system")
    defer span.End()
    
    ch := make(chan Item, 10)
    
    go producer(ctx, ch)
    consumer(ctx, ch)
}
```

## 7. 参考资料

- **CSP 理论**：Hoare, C.A.R. "Communicating Sequential Processes" (1985)
- **OTLP 规范**：[OpenTelemetry Protocol Specification](https://github.com/open-telemetry/opentelemetry-proto)
- **W3C Trace Context**：[W3C Recommendation](https://www.w3.org/TR/trace-context/)
- **形式化证明**：`docs/design/formal-proof.md`
- **分布式模型**：`docs/design/distributed-model.md`

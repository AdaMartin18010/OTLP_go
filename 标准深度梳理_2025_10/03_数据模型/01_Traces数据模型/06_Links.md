# Span Links 完整指南

## 📋 目录

- [Span Links 完整指南](#span-links-完整指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [关键特性](#关键特性)
    - [Links vs 父子关系](#links-vs-父子关系)
  - [Link-定义1](#link-定义1)
    - [数据结构](#数据结构)
    - [OTLP Protocol Buffers](#otlp-protocol-buffers)
    - [形式化定义](#形式化定义)
  - [使用场景](#使用场景)
    - [1. 批处理场景](#1-批处理场景)
      - [场景描述](#场景描述)
      - [示例](#示例)
      - [Go 实现](#go-实现)
    - [2. 消息队列场景](#2-消息队列场景)
      - [场景描述2](#场景描述2)
      - [示例2](#示例2)
      - [Go 实现2](#go-实现2)
    - [3. 扇出/扇入场景](#3-扇出扇入场景)
      - [场景描述3](#场景描述3)
      - [示例3](#示例3)
      - [Go 实现3](#go-实现3)
    - [4. 重试和补偿场景](#4-重试和补偿场景)
      - [场景描述4](#场景描述4)
      - [Go 实现4](#go-实现4)
    - [5. 分布式事务场景](#5-分布式事务场景)
      - [场景描述5](#场景描述5)
      - [Go 实现5](#go-实现5)
  - [因果关系建模](#因果关系建模)
    - [Link 类型1](#link-类型1)
    - [因果关系图](#因果关系图)
  - [Go 完整实现](#go-完整实现)
    - [完整的批处理示例](#完整的批处理示例)
    - [Link 工具函数1](#link-工具函数1)
  - [最佳实践](#最佳实践)
    - [1. Links 必须在 Span 创建时指定](#1-links-必须在-span-创建时指定)
    - [2. 适度使用 Links](#2-适度使用-links)
    - [3. Link 属性应该有意义](#3-link-属性应该有意义)
    - [4. 使用标准的 Link 类型](#4-使用标准的-link-类型)
  - [常见问题](#常见问题)
    - [Q1: Links 和父子关系有什么区别？](#q1-links-和父子关系有什么区别)
    - [Q2: 一个 Span 可以有多少个 Links？](#q2-一个-span-可以有多少个-links)
    - [Q3: 可以链接到未来的 Span 吗？](#q3-可以链接到未来的-span-吗)
    - [Q4: Links 可以跨 Trace 吗？](#q4-links-可以跨-trace-吗)
    - [Q5: 如何在消息队列中传递 SpanContext 用于 Links？](#q5-如何在消息队列中传递-spancontext-用于-links)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [Go 实现6](#go-实现6)
    - [相关文档](#相关文档)

---

## 概述

**Span Links** 用于表示 Span 之间的因果关系，但这种关系不是简单的父子关系。
Links 允许一个 Span 关联多个其他 Span，支持复杂的分布式追踪场景。

### 关键特性

- ✅ **多对多关系**: 一个 Span 可以链接多个 Span
- ✅ **跨 Trace 关联**: 可以链接不同 Trace 中的 Span
- ✅ **因果关系**: 表达"由...触发"或"与...相关"
- ✅ **属性携带**: 每个 Link 可以附加属性

### Links vs 父子关系

| 特性 | 父子关系 | Links |
|------|---------|-------|
| **数量** | 单一父 Span | 多个链接 Span |
| **方向** | 单向（父→子） | 可双向 |
| **Trace** | 同一 Trace | 可跨 Trace |
| **时序** | 父先于子 | 无严格时序 |
| **用途** | 调用栈 | 因果关系 |

---

## Link-定义1

### 数据结构

```go
type Link struct {
    SpanContext trace.SpanContext     // 链接的 SpanContext
    Attributes  []attribute.KeyValue  // Link 属性
}
```

### OTLP Protocol Buffers

```protobuf
message Link {
  bytes trace_id = 1;                   // 16 bytes TraceID
  bytes span_id = 2;                    // 8 bytes SpanID
  string trace_state = 3;               // W3C TraceState
  repeated KeyValue attributes = 4;     // Link 属性
  uint32 dropped_attributes_count = 5;  // 丢弃的属性数
}
```

### 形式化定义

```text
Link := {
    SpanContext: {
        TraceID:    [16]byte
        SpanID:     [8]byte
        TraceState: string
    }
    Attributes: Map[string, Value]
}

Span := {
    ...
    Links: []Link  // 创建时指定，不可变
}
```

---

## 使用场景

### 1. 批处理场景

#### 场景描述

一个批处理 Span 处理多个独立的请求，每个请求都有自己的 Trace。

#### 示例

```text
[Request 1 Trace]    [Request 2 Trace]    [Request 3 Trace]
     Span A               Span B               Span C
       |                    |                    |
       +--------------------+--------------------+
                            |
                    [Batch Trace]
                      Batch Span
                    (Links to A, B, C)
```

#### Go 实现

```go
import (
    "context"
    "go.opentelemetry.io/otel/trace"
)

// 批量处理多个请求
func batchProcess(ctx context.Context, requests []*Request) error {
    // 提取所有请求的 SpanContext
    var links []trace.Link
    for _, req := range requests {
        if spanCtx := trace.SpanContextFromContext(req.Context); spanCtx.IsValid() {
            links = append(links, trace.Link{
                SpanContext: spanCtx,
                Attributes: []attribute.KeyValue{
                    attribute.String("request.id", req.ID),
                },
            })
        }
    }

    // 创建批处理 Span，链接所有请求
    ctx, span := tracer.Start(ctx, "batch_process",
        trace.WithLinks(links...),
        trace.WithAttributes(
            attribute.Int("batch.size", len(requests)),
        ),
    )
    defer span.End()

    // 处理批次
    for _, req := range requests {
        if err := processRequest(ctx, req); err != nil {
            span.AddEvent("request.failed",
                trace.WithAttributes(
                    attribute.String("request.id", req.ID),
                ),
            )
        }
    }

    return nil
}
```

---

### 2. 消息队列场景

#### 场景描述2

消息生产者和多个消费者之间的关系。

#### 示例2

```text
[Producer Trace]
   Producer Span
       |
       | (publish message with TraceContext)
       v
   [Message Queue]
       |
       +--- Consumer 1 Span (Links to Producer)
       +--- Consumer 2 Span (Links to Producer)
       +--- Consumer 3 Span (Links to Producer)
```

#### Go 实现2

```go
// 生产者：发送消息
func publishMessage(ctx context.Context, topic string, data []byte) error {
    ctx, span := tracer.Start(ctx, "kafka.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()

    // 将 SpanContext 注入消息头
    spanCtx := span.SpanContext()
    headers := map[string]string{
        "traceparent": formatTraceparent(spanCtx),
        "tracestate":  spanCtx.TraceState().String(),
    }

    // 发送消息
    return kafka.Publish(topic, data, headers)
}

// 消费者：接收消息并链接到生产者
func consumeMessage(msg *Message) {
    // 从消息头提取生产者的 SpanContext
    producerSpanCtx := extractSpanContext(msg.Headers)

    // 创建消费者 Span，链接到生产者
    ctx, span := tracer.Start(context.Background(), "kafka.consume",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithLinks(trace.Link{
            SpanContext: producerSpanCtx,
            Attributes: []attribute.KeyValue{
                attribute.String("link.type", "follows_from"),
                attribute.String("messaging.operation", "process"),
            },
        }),
    )
    defer span.End()

    // 处理消息
    processMessage(ctx, msg)
}
```

---

### 3. 扇出/扇入场景

#### 场景描述3

一个请求触发多个并行操作，然后聚合结果。

#### 示例3

```text
        [Main Trace]
          Main Span
             |
    +--------+--------+
    |        |        |
 Worker1  Worker2  Worker3
    |        |        |
    +--------+--------+
             |
        [Aggregation Trace]
         Aggregation Span
       (Links to Worker1, Worker2, Worker3)
```

#### Go 实现3

```go
// 主操作：扇出
func fanOutOperation(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "fan_out_operation")
    defer span.End()

    // 并发启动多个 worker
    var wg sync.WaitGroup
    workerSpanContexts := make([]trace.SpanContext, 3)

    for i := 0; i < 3; i++ {
        wg.Add(1)
        go func(index int) {
            defer wg.Done()
            
            // 创建 worker Span
            _, workerSpan := tracer.Start(ctx, fmt.Sprintf("worker_%d", index))
            defer workerSpan.End()

            // 保存 SpanContext 用于后续链接
            workerSpanContexts[index] = workerSpan.SpanContext()

            // 执行工作
            doWork(index)
        }(i)
    }

    wg.Wait()

    // 聚合结果
    return aggregateResults(ctx, workerSpanContexts)
}

// 扇入：聚合结果并链接所有 workers
func aggregateResults(ctx context.Context, workerSpanCtxs []trace.SpanContext) error {
    // 创建 Links
    var links []trace.Link
    for i, spanCtx := range workerSpanCtxs {
        if spanCtx.IsValid() {
            links = append(links, trace.Link{
                SpanContext: spanCtx,
                Attributes: []attribute.KeyValue{
                    attribute.Int("worker.index", i),
                },
            })
        }
    }

    // 创建聚合 Span，链接所有 workers
    _, span := tracer.Start(ctx, "aggregate_results",
        trace.WithLinks(links...),
    )
    defer span.End()

    // 聚合逻辑
    return nil
}
```

---

### 4. 重试和补偿场景

#### 场景描述4

追踪重试操作，链接到原始失败的 Span。

#### Go 实现4

```go
func operationWithRetry(ctx context.Context) error {
    var lastFailedSpanCtx trace.SpanContext

    for attempt := 1; attempt <= 3; attempt++ {
        // 创建 links（如果有之前失败的 Span）
        var links []trace.Link
        if lastFailedSpanCtx.IsValid() {
            links = append(links, trace.Link{
                SpanContext: lastFailedSpanCtx,
                Attributes: []attribute.KeyValue{
                    attribute.String("link.type", "retry"),
                    attribute.Int("original.attempt", attempt-1),
                },
            })
        }

        // 创建 Span
        ctx, span := tracer.Start(ctx, "operation_attempt",
            trace.WithLinks(links...),
            trace.WithAttributes(
                attribute.Int("attempt", attempt),
            ),
        )

        // 尝试操作
        if err := doOperation(); err != nil {
            lastFailedSpanCtx = span.SpanContext()
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            span.End()

            if attempt < 3 {
                time.Sleep(time.Duration(attempt) * time.Second)
                continue
            }
            return err
        }

        span.SetStatus(codes.Ok, "")
        span.End()
        return nil
    }

    return errors.New("all retries failed")
}
```

---

### 5. 分布式事务场景

#### 场景描述5

Saga 模式中的事务补偿。

#### Go 实现5

```go
// 分布式事务
func distributedTransaction(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "distributed_transaction")
    defer span.End()

    // 步骤1：创建订单
    orderSpanCtx, err := createOrder(ctx)
    if err != nil {
        return err
    }

    // 步骤2：扣减库存
    inventorySpanCtx, err := deductInventory(ctx)
    if err != nil {
        // 补偿：取消订单，链接到原始订单 Span
        cancelOrder(ctx, orderSpanCtx, "inventory_failed")
        return err
    }

    // 步骤3：处理支付
    _, err = processPayment(ctx)
    if err != nil {
        // 补偿：恢复库存并取消订单
        compensateInventory(ctx, inventorySpanCtx, "payment_failed")
        cancelOrder(ctx, orderSpanCtx, "payment_failed")
        return err
    }

    return nil
}

// 补偿操作：取消订单，链接到原始 Span
func cancelOrder(ctx context.Context, originalSpanCtx trace.SpanContext, reason string) error {
    _, span := tracer.Start(ctx, "cancel_order",
        trace.WithLinks(trace.Link{
            SpanContext: originalSpanCtx,
            Attributes: []attribute.KeyValue{
                attribute.String("link.type", "compensation"),
                attribute.String("compensation.reason", reason),
            },
        }),
    )
    defer span.End()

    // 取消逻辑
    return nil
}

func compensateInventory(ctx context.Context, originalSpanCtx trace.SpanContext, reason string) error {
    _, span := tracer.Start(ctx, "restore_inventory",
        trace.WithLinks(trace.Link{
            SpanContext: originalSpanCtx,
            Attributes: []attribute.KeyValue{
                attribute.String("link.type", "compensation"),
                attribute.String("compensation.reason", reason),
            },
        }),
    )
    defer span.End()

    // 恢复逻辑
    return nil
}
```

---

## 因果关系建模

### Link 类型1

虽然 OpenTelemetry 没有正式定义 Link 类型，但常用以下约定：

```go
const (
    LinkTypeFollowsFrom    = "follows_from"    // 弱因果关系
    LinkTypeChildOf        = "child_of"        // 强因果关系
    LinkTypeRetry          = "retry"           // 重试关系
    LinkTypeCompensation   = "compensation"    // 补偿关系
    LinkTypeBatchItem      = "batch_item"      // 批处理项
    LinkTypeAggregation    = "aggregation"     // 聚合关系
)

// 使用示例
func createLinkWithType(spanCtx trace.SpanContext, linkType string) trace.Link {
    return trace.Link{
        SpanContext: spanCtx,
        Attributes: []attribute.KeyValue{
            attribute.String("link.type", linkType),
        },
    }
}
```

### 因果关系图

```text
强因果关系（父子）:
  Parent Span
      |
      v
  Child Span

弱因果关系（Links）:
  Span A ----link----> Span B
  (Span B 由 Span A 触发，但不是直接子 Span)

批处理（Links）:
  Span A \
  Span B  +---links---> Batch Span
  Span C /

聚合（Links）:
  Worker1 \
  Worker2  +---links---> Aggregation Span
  Worker3 /
```

---

## Go 完整实现

### 完整的批处理示例

```go
package main

import (
    "context"
    "fmt"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

var tracer = otel.Tracer("batch-service")

type Request struct {
    ID      string
    Context context.Context
    Data    []byte
}

type BatchProcessor struct {
    batchSize int
    timeout   time.Duration
}

func NewBatchProcessor(batchSize int, timeout time.Duration) *BatchProcessor {
    return &BatchProcessor{
        batchSize: batchSize,
        timeout:   timeout,
    }
}

// 1. 收集请求
func (bp *BatchProcessor) Collect(ctx context.Context, requests chan *Request) ([]*Request, error) {
    ctx, span := tracer.Start(ctx, "collect_requests")
    defer span.End()

    batch := make([]*Request, 0, bp.batchSize)
    timer := time.NewTimer(bp.timeout)
    defer timer.Stop()

    for {
        select {
        case req := <-requests:
            batch = append(batch, req)
            span.AddEvent("request.collected",
                trace.WithAttributes(
                    attribute.String("request.id", req.ID),
                    attribute.Int("batch.current_size", len(batch)),
                ),
            )

            if len(batch) >= bp.batchSize {
                span.SetAttributes(
                    attribute.Int("batch.size", len(batch)),
                    attribute.String("batch.trigger", "size_limit"),
                )
                return batch, nil
            }

        case <-timer.C:
            if len(batch) > 0 {
                span.SetAttributes(
                    attribute.Int("batch.size", len(batch)),
                    attribute.String("batch.trigger", "timeout"),
                )
                return batch, nil
            }

        case <-ctx.Done():
            return nil, ctx.Err()
        }
    }
}

// 2. 批量处理（带 Links）
func (bp *BatchProcessor) Process(ctx context.Context, batch []*Request) error {
    // 提取所有请求的 SpanContext 并创建 Links
    var links []trace.Link
    for _, req := range batch {
        if spanCtx := trace.SpanContextFromContext(req.Context); spanCtx.IsValid() {
            links = append(links, trace.Link{
                SpanContext: spanCtx,
                Attributes: []attribute.KeyValue{
                    attribute.String("request.id", req.ID),
                    attribute.String("link.type", "batch_item"),
                },
            })
        }
    }

    // 创建批处理 Span，链接所有请求
    ctx, span := tracer.Start(ctx, "batch_process",
        trace.WithLinks(links...),
        trace.WithAttributes(
            attribute.Int("batch.size", len(batch)),
            attribute.Int("batch.links", len(links)),
        ),
    )
    defer span.End()

    // 统计结果
    var (
        succeeded int
        failed    int
    )

    // 处理每个请求
    for _, req := range batch {
        span.AddEvent("item.processing",
            trace.WithAttributes(
                attribute.String("request.id", req.ID),
            ),
        )

        if err := bp.processItem(ctx, req); err != nil {
            failed++
            span.AddEvent("item.failed",
                trace.WithAttributes(
                    attribute.String("request.id", req.ID),
                    attribute.String("error", err.Error()),
                ),
            )
        } else {
            succeeded++
            span.AddEvent("item.succeeded",
                trace.WithAttributes(
                    attribute.String("request.id", req.ID),
                ),
            )
        }
    }

    // 设置结果
    span.SetAttributes(
        attribute.Int("batch.succeeded", succeeded),
        attribute.Int("batch.failed", failed),
        attribute.Float64("batch.success_rate", float64(succeeded)/float64(len(batch))),
    )

    if failed > 0 {
        span.SetStatus(codes.Error, fmt.Sprintf("%d items failed", failed))
        return fmt.Errorf("%d/%d items failed", failed, len(batch))
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

func (bp *BatchProcessor) processItem(ctx context.Context, req *Request) error {
    _, span := tracer.Start(ctx, "process_item",
        trace.WithAttributes(
            attribute.String("request.id", req.ID),
        ),
    )
    defer span.End()

    // 模拟处理
    time.Sleep(10 * time.Millisecond)

    // 模拟随机失败
    if time.Now().Unix()%5 == 0 {
        err := fmt.Errorf("processing failed")
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// 3. 完整的批处理流程
func BatchProcessingWorkflow(ctx context.Context) error {
    ctx, span := tracer.Start(ctx, "batch_processing_workflow")
    defer span.End()

    processor := NewBatchProcessor(10, 5*time.Second)
    requests := make(chan *Request, 100)

    // 模拟生成请求
    go func() {
        for i := 0; i < 25; i++ {
            reqCtx, reqSpan := tracer.Start(ctx, fmt.Sprintf("request_%d", i),
                trace.WithAttributes(
                    attribute.String("request.id", fmt.Sprintf("req-%d", i)),
                ),
            )
            
            requests <- &Request{
                ID:      fmt.Sprintf("req-%d", i),
                Context: reqCtx,
                Data:    []byte(fmt.Sprintf("data-%d", i)),
            }
            
            reqSpan.End()
            time.Sleep(100 * time.Millisecond)
        }
        close(requests)
    }()

    // 批量处理
    batchCount := 0
    for {
        batch, err := processor.Collect(ctx, requests)
        if err != nil {
            if err == context.Canceled || err == context.DeadlineExceeded {
                break
            }
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            return err
        }

        if len(batch) == 0 {
            break
        }

        batchCount++
        span.AddEvent("batch.created",
            trace.WithAttributes(
                attribute.Int("batch.number", batchCount),
                attribute.Int("batch.size", len(batch)),
            ),
        )

        if err := processor.Process(ctx, batch); err != nil {
            span.AddEvent("batch.failed",
                trace.WithAttributes(
                    attribute.Int("batch.number", batchCount),
                ),
            )
            // 继续处理下一批
        } else {
            span.AddEvent("batch.completed",
                trace.WithAttributes(
                    attribute.Int("batch.number", batchCount),
                ),
            )
        }
    }

    span.SetAttributes(
        attribute.Int("batches.total", batchCount),
    )
    span.SetStatus(codes.Ok, "")
    return nil
}
```

### Link 工具函数1

```go
// 1. 创建不同类型的 Links
func CreateFollowsFromLink(spanCtx trace.SpanContext, reason string) trace.Link {
    return trace.Link{
        SpanContext: spanCtx,
        Attributes: []attribute.KeyValue{
            attribute.String("link.type", "follows_from"),
            attribute.String("link.reason", reason),
        },
    }
}

func CreateRetryLink(spanCtx trace.SpanContext, attempt int) trace.Link {
    return trace.Link{
        SpanContext: spanCtx,
        Attributes: []attribute.KeyValue{
            attribute.String("link.type", "retry"),
            attribute.Int("retry.attempt", attempt),
        },
    }
}

func CreateBatchItemLink(spanCtx trace.SpanContext, itemID string, index int) trace.Link {
    return trace.Link{
        SpanContext: spanCtx,
        Attributes: []attribute.KeyValue{
            attribute.String("link.type", "batch_item"),
            attribute.String("item.id", itemID),
            attribute.Int("item.index", index),
        },
    }
}

// 2. 从多个 SpanContext 创建 Links
func CreateLinksFromSpanContexts(spanCtxs []trace.SpanContext, linkType string) []trace.Link {
    links := make([]trace.Link, 0, len(spanCtxs))
    for i, spanCtx := range spanCtxs {
        if spanCtx.IsValid() {
            links = append(links, trace.Link{
                SpanContext: spanCtx,
                Attributes: []attribute.KeyValue{
                    attribute.String("link.type", linkType),
                    attribute.Int("link.index", i),
                },
            })
        }
    }
    return links
}

// 3. 验证 Links
func ValidateLinks(links []trace.Link) error {
    for i, link := range links {
        if !link.SpanContext.IsValid() {
            return fmt.Errorf("invalid link at index %d", i)
        }
    }
    return nil
}
```

---

## 最佳实践

### 1. Links 必须在 Span 创建时指定

```go
// ✅ 推荐
span := tracer.Start(ctx, "operation",
    trace.WithLinks(links...),
)

// ❌ 错误：Span 创建后不能添加 Links
span := tracer.Start(ctx, "operation")
// 无法添加 Links
```

### 2. 适度使用 Links

```go
// ✅ 推荐：合理数量（< 100）
links := createLinksFromBatch(batch)  // 10-50 个 links

// ⚠️ 注意：过多 Links 会影响性能
// 考虑采样或限制数量
```

### 3. Link 属性应该有意义

```go
// ✅ 推荐
trace.Link{
    SpanContext: spanCtx,
    Attributes: []attribute.KeyValue{
        attribute.String("link.type", "batch_item"),
        attribute.String("item.id", itemID),
        attribute.Int("item.index", index),
    },
}

// ❌ 避免：无意义的属性
trace.Link{
    SpanContext: spanCtx,
    Attributes: []attribute.KeyValue{
        attribute.String("data", "some data"),
    },
}
```

### 4. 使用标准的 Link 类型

```go
// ✅ 推荐：使用约定的类型名称
const (
    LinkTypeFollowsFrom  = "follows_from"
    LinkTypeRetry        = "retry"
    LinkTypeBatchItem    = "batch_item"
)

// ❌ 避免：随意命名
attribute.String("link.type", "some_random_type")
```

---

## 常见问题

### Q1: Links 和父子关系有什么区别？

**A**:

- **父子关系**: 强因果关系，单一父 Span，同一 Trace
- **Links**: 弱因果关系，多个链接，可跨 Trace

```go
// 父子关系
ctx, parent := tracer.Start(ctx, "parent")
ctx, child := tracer.Start(ctx, "child")  // child 的父是 parent

// Links
span := tracer.Start(ctx, "operation",
    trace.WithLinks(trace.Link{SpanContext: otherSpanCtx}),
)
```

---

### Q2: 一个 Span 可以有多少个 Links？

**A**: 理论上没有限制，但建议 < 100 个，避免性能问题。

---

### Q3: 可以链接到未来的 Span 吗？

**A**: 不可以。Links 必须在 Span 创建时指定，且只能链接已存在的 SpanContext。

---

### Q4: Links 可以跨 Trace 吗？

**A**: 可以！这是 Links 的主要用途之一。

```go
// Trace A
ctx, spanA := tracer.Start(ctx, "operation_a")
spanAContext := spanA.SpanContext()
spanA.End()

// Trace B，链接到 Trace A 的 Span
ctx, spanB := tracer.Start(context.Background(), "operation_b",
    trace.WithLinks(trace.Link{SpanContext: spanAContext}),
)
defer spanB.End()
```

---

### Q5: 如何在消息队列中传递 SpanContext 用于 Links？

**A**: 将 SpanContext 序列化到消息头。

```go
// 生产者
spanCtx := span.SpanContext()
headers := map[string]string{
    "traceparent": formatTraceparent(spanCtx),
    "tracestate":  spanCtx.TraceState().String(),
}
kafka.Publish(topic, data, headers)

// 消费者
spanCtx := extractSpanContext(msg.Headers)
span := tracer.Start(ctx, "consume",
    trace.WithLinks(trace.Link{SpanContext: spanCtx}),
)
```

---

## 参考资源

### 官方文档

- [OpenTelemetry Links](https://opentelemetry.io/docs/specs/otel/trace/api/#specifying-links)
- [Trace Semantic Conventions](https://opentelemetry.io/docs/specs/semconv/general/trace/)

### Go 实现6

- [go.opentelemetry.io/otel/trace](https://pkg.go.dev/go.opentelemetry.io/otel/trace)

### 相关文档

- [01_Span结构.md](./01_Span结构.md)
- [02_SpanContext.md](./02_SpanContext.md)
- [05_Events.md](./05_Events.md)

---

**🎉 恭喜！你已经掌握了 Span Links 的完整知识！**

下一步：学习 [形式化定义](./07_形式化定义.md) 了解 Traces 的数学模型。

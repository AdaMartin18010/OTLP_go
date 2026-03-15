# Span结构完整定义

> **OTLP版本**: v1.0.0 (Stable)  
> **最后更新**: 2025年10月8日

---

## 目录

- [Span结构完整定义](#span结构完整定义)
  - [目录](#目录)
  - [1. 概念定义](#1-概念定义)
    - [1.1 正式定义](#11-正式定义)
    - [1.2 Span生命周期](#12-span生命周期)
    - [1.3 核心职责](#13-核心职责)
  - [2. 字段详解](#2-字段详解)
    - [2.1 标识字段](#21-标识字段)
    - [2.2 时间字段](#22-时间字段)
    - [2.3 描述字段](#23-描述字段)
    - [2.4 状态字段](#24-状态字段)
    - [2.5 计数字段](#25-计数字段)
  - [3. Protocol Buffers定义](#3-protocol-buffers定义)
  - [4. 字段约束](#4-字段约束)
    - [4.1 必需性](#41-必需性)
    - [4.2 格式约束](#42-格式约束)
    - [4.3 语义约束](#43-语义约束)
  - [5. 形式化规范](#5-形式化规范)
    - [5.1 Span定义](#51-span定义)
    - [5.2 不变量](#52-不变量)
    - [5.3 关系属性](#53-关系属性)
  - [6. 字段大小分析](#6-字段大小分析)
  - [7. 实现示例](#7-实现示例)
    - [7.1 创建Span](#71-创建span)
    - [7.2 设置属性](#72-设置属性)
    - [7.3 添加事件](#73-添加事件)
    - [7.4 结束Span](#74-结束span)
  - [8. 最佳实践](#8-最佳实践)
  - [9. 参考资源](#9-参考资源)

## 1. 概念定义

### 1.1 正式定义

**Span** 形式化定义：

```text
Span = (ID, T, M, R, E, L, S)

其中:
- ID: Identification = (trace_id, span_id, parent_span_id)
  唯一标识
  
- T: Temporal = (start_time, end_time, duration)
  时间属性
  
- M: Metadata = (name, kind, attributes)
  元数据
  
- R: Relations = (parent_span_id, links)
  关系
  
- E: Events = ordered list of (timestamp, name, attributes)
  事件序列
  
- L: Links = list of (trace_id, span_id, trace_state, attributes)
  跨trace链接
  
- S: Status = (code, message)
  执行状态

约束:
1. trace_id, span_id必须全局唯一
2. start_time ≤ end_time
3. parent_span_id存在 → 父子关系
4. kind ∈ {INTERNAL, SERVER, CLIENT, PRODUCER, CONSUMER}
```

### 1.2 Span生命周期

**状态转换**：

```text
Span生命周期状态机:

CREATED (创建)
  │
  ├─ start() ──> ACTIVE (活跃)
  │                │
  │                ├─ addEvent()
  │                ├─ setAttribute()
  │                ├─ recordException()
  │                │
  │                └─ end() ──> ENDED (结束)
  │                                │
  │                                └─ export() ──> EXPORTED (已导出)
  │
  └─ end() (未start) ──> ENDED (空Span)
```

### 1.3 核心职责

```text
Span的职责:
1. 追踪单个操作
   - 记录开始/结束时间
   - 捕获操作元数据
   
2. 建立父子关系
   - parent_span_id链接父Span
   - 构建调用树
   
3. 携带上下文
   - trace_state传播状态
   - Baggage传播元数据
   
4. 记录事件
   - 时间点事件
   - 异常记录
   
5. 跨trace链接
   - Links关联其他trace
   - 批处理、异步场景
```

---

## 2. 字段详解

### 2.1 标识字段

**trace_id (bytes, 16字节)**:

```text
定义: 全局唯一的trace标识符
类型: bytes (16字节)
格式: 128位随机数

生成规则:
- 使用加密安全随机数生成器
- 非全零 (00000000-0000-0000-0000-000000000000 无效)
- 十六进制表示: 32字符

示例:
5B8EFFF798038103D269B633813FC60C

用途:
- 唯一标识一个trace
- 关联同一请求的所有spans
- 查询和过滤的主键
```

**span_id (bytes, 8字节)**:

```text
定义: Span的唯一标识符
类型: bytes (8字节)
格式: 64位随机数

生成规则:
- 使用加密安全随机数生成器
- 非全零 (0000000000000000 无效)
- trace内唯一
- 十六进制表示: 16字符

示例:
EEE19B7EC3C1B174

用途:
- 唯一标识trace中的一个span
- parent_span_id引用
- Links引用
```

**parent_span_id (bytes, 8字节, 可选)**:

```text
定义: 父Span的span_id
类型: bytes (8字节)
可选: 是 (根Span无父Span)

取值:
- 如果是根Span: 空bytes或全零
- 如果是子Span: 父Span的span_id

约束:
- 必须引用同一trace内的Span
- 不能循环引用
- 不能引用自己

示例:
根Span: parent_span_id = (empty)
子Span: parent_span_id = EEE19B7EC3C1B174

用途:
- 建立父子关系
- 构建调用树
- 依赖分析
```

**trace_state (string, 可选)**:

```text
定义: W3C Trace Context tracestate
类型: string
格式: key1=value1,key2=value2

规则:
- 最多512字节
- 每个键值对 ≤ 128字节
- 逗号分隔
- 支持vendor前缀

示例:
"rojo=00f067aa0ba902b7,congo=t61rcWkgMzE"

用途:
- 传播厂商特定状态
- 采样决策
- 路由信息
```

### 2.2 时间字段

**start_time_unix_nano (fixed64)**:

```text
定义: Span开始时间
类型: fixed64 (8字节)
单位: 纳秒 (自Unix Epoch)
精度: 纳秒级

计算:
start_time_unix_nano = seconds * 1,000,000,000 + nanos

示例:
1544712660000000000
= 2018-12-13T14:51:00.000000000Z

约束:
- 必须 ≤ end_time_unix_nano
- 通常使用单调时钟

用途:
- 计算持续时间
- 时序排序
- 性能分析
```

**end_time_unix_nano (fixed64)**:

```text
定义: Span结束时间
类型: fixed64 (8字节)
单位: 纳秒 (自Unix Epoch)

约束:
- 必须 ≥ start_time_unix_nano
- 如果未设置: Span未结束

计算持续时间:
duration = end_time_unix_nano - start_time_unix_nano

示例:
start: 1544712660000000000
end:   1544712661500000000
duration: 1,500,000,000 nanos = 1.5秒
```

### 2.3 描述字段

**name (string, 必需)**:

```text
定义: Span的简短描述
类型: string
长度建议: ≤ 64字符

命名规范:
- 使用通用名称 (不含具体值)
- HTTP: "HTTP {METHOD}"
- gRPC: "{package}.{service}/{method}"
- DB: "{operation} {table}"

示例:
✅ 好的命名:
- "HTTP GET"
- "grpc.health.v1.Health/Check"
- "SELECT users"
- "publish message"

❌ 不好的命名:
- "HTTP GET /api/users/123"  (含具体值)
- "query"                     (太笼统)
- "process_request_from_user_john_with_token_abc123"  (太长)

用途:
- Span分组
- 性能聚合
- 可视化展示
```

**kind (enum SpanKind, 必需)**:

```text
定义: Span的角色类型
类型: enum SpanKind

可能值:
- SPAN_KIND_UNSPECIFIED (0): 未指定
- SPAN_KIND_INTERNAL (1): 内部操作
- SPAN_KIND_SERVER (2): 服务器端span
- SPAN_KIND_CLIENT (3): 客户端span
- SPAN_KIND_PRODUCER (4): 消息生产者
- SPAN_KIND_CONSUMER (5): 消息消费者

语义:
INTERNAL:
- 内部逻辑、函数调用
- 不涉及网络通信
- 例: 数据处理、业务逻辑

SERVER:
- 同步请求的服务器端
- 父span通常是CLIENT
- 例: HTTP server, gRPC server

CLIENT:
- 同步请求的客户端
- 子span通常是SERVER
- 例: HTTP client, gRPC client

PRODUCER:
- 异步消息生产者
- 不等待消费
- 例: Kafka producer

CONSUMER:
- 异步消息消费者
- 父span通常是PRODUCER (通过Link)
- 例: Kafka consumer

选择规则:
kind = detect_span_kind(operation)

if operation.is_synchronous:
  if operation.is_outbound:
    return CLIENT
  else:
    return SERVER
elif operation.is_async_send:
  return PRODUCER
elif operation.is_async_receive:
  return CONSUMER
else:
  return INTERNAL
```

### 2.4 状态字段

**status (Status, 可选)**:

```text
定义: Span执行状态
类型: embedded message Status

Status结构:
message Status {
  string message = 2;
  StatusCode code = 3;
}

enum StatusCode {
  STATUS_CODE_UNSET = 0;   // 未设置
  STATUS_CODE_OK = 1;      // 成功
  STATUS_CODE_ERROR = 2;   // 错误
}

语义:
UNSET:
- 默认值
- 表示未显式设置状态
- SDK应根据其他信息推断

OK:
- 操作成功完成
- 无错误

ERROR:
- 操作失败
- message字段包含错误描述

设置规则:
- 只在需要时设置
- HTTP 200-399 → OK
- HTTP 400-599 → ERROR
- 异常 → ERROR + message
```

### 2.5 计数字段

**dropped_attributes_count (uint32)**:

```text
定义: 被丢弃的属性数量
类型: uint32
默认: 0

场景:
- 属性数量超过限制
- 内存压力导致丢弃

示例:
限制: 最多128个属性
实际: 150个属性被添加
结果: 保留128个, dropped_attributes_count = 22

用途:
- 数据完整性指示
- 监控采样策略
- 调试配置问题
```

**dropped_events_count (uint32)**:

```text
定义: 被丢弃的事件数量
类型: uint32
默认: 0

类似dropped_attributes_count
```

**dropped_links_count (uint32)**:

```text
定义: 被丢弃的链接数量
类型: uint32
默认: 0

类似dropped_attributes_count
```

---

## 3. Protocol Buffers定义

**完整定义**：

```protobuf
syntax = "proto3";

package opentelemetry.proto.trace.v1;

import "opentelemetry/proto/common/v1/common.proto";

message Span {
  // 唯一标识
  bytes trace_id = 1;                              // 16字节
  bytes span_id = 2;                               // 8字节
  string trace_state = 3;                          // W3C tracestate
  bytes parent_span_id = 4;                        // 8字节 (可选)
  
  // 描述
  string name = 5;                                 // Span名称
  SpanKind kind = 6;                               // Span类型
  
  // 时间
  fixed64 start_time_unix_nano = 7;               // 开始时间 (纳秒)
  fixed64 end_time_unix_nano = 8;                 // 结束时间 (纳秒)
  
  // 属性
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 9;
  uint32 dropped_attributes_count = 10;
  
  // 事件
  repeated Event events = 11;
  uint32 dropped_events_count = 12;
  
  // 链接
  repeated Link links = 13;
  uint32 dropped_links_count = 14;
  
  // 状态
  Status status = 15;
}

enum SpanKind {
  SPAN_KIND_UNSPECIFIED = 0;
  SPAN_KIND_INTERNAL = 1;
  SPAN_KIND_SERVER = 2;
  SPAN_KIND_CLIENT = 3;
  SPAN_KIND_PRODUCER = 4;
  SPAN_KIND_CONSUMER = 5;
}

message Status {
  reserved 1;  // 保留 (历史: deprecated_code)
  string message = 2;
  StatusCode code = 3;
}

enum StatusCode {
  STATUS_CODE_UNSET = 0;
  STATUS_CODE_OK = 1;
  STATUS_CODE_ERROR = 2;
}

message Event {
  fixed64 time_unix_nano = 1;
  string name = 2;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 3;
  uint32 dropped_attributes_count = 4;
}

message Link {
  bytes trace_id = 1;
  bytes span_id = 2;
  string trace_state = 3;
  repeated opentelemetry.proto.common.v1.KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
}
```

---

## 4. 字段约束

### 4.1 必需性

| 字段 | 必需性 | 说明 |
|------|-------|------|
| `trace_id` | **必需** | 非空，16字节 |
| `span_id` | **必需** | 非空，8字节 |
| `trace_state` | 可选 | W3C tracestate |
| `parent_span_id` | 条件必需 | 非根Span必需 |
| `name` | **必需** | 非空字符串 |
| `kind` | **必需** | 有效枚举值 |
| `start_time_unix_nano` | **必需** | > 0 |
| `end_time_unix_nano` | **必需** | ≥ start_time |
| `attributes` | 可选 | 建议提供 |
| `events` | 可选 | |
| `links` | 可选 | |
| `status` | 可选 | 建议在错误时设置 |

### 4.2 格式约束

```text
trace_id:
- 长度: 必须16字节
- 值: 非全零
- 格式: 128位随机数

span_id:
- 长度: 必须8字节
- 值: 非全零
- 格式: 64位随机数

parent_span_id:
- 长度: 0或8字节
- 值: 如果非空,非全零
- 约束: 必须引用同trace内的Span

trace_state:
- 长度: ≤ 512字节
- 格式: key1=value1,key2=value2
- 键: [a-z0-9*/\-]*, 最多256个字符
- 值: [可打印ASCII], 最多256个字符

name:
- 长度: 建议 ≤ 64字符
- 格式: UTF-8字符串
- 约束: 非空

时间:
- start_time: > 0 (Unix Epoch后)
- end_time: ≥ start_time
- 精度: 纳秒
```

### 4.3 语义约束

```text
1. 时间顺序:
   start_time_unix_nano ≤ end_time_unix_nano

2. 父子关系:
   如果 parent_span_id 非空:
     - 必须引用同一trace内的Span
     - 父Span的 start_time ≤ 子Span的 start_time
     - 子Span的 end_time ≤ 父Span的 end_time
     (理想情况,允许时钟漂移导致的小偏差)

3. SpanKind语义:
   CLIENT span → 通常有对应的 SERVER span (同trace或通过Link)
   PRODUCER span → 通常有对应的 CONSUMER span (通过Link)

4. Status设置:
   - 如果有异常: 应设置为 ERROR
   - 如果明确成功: 可设置为 OK
   - 默认: UNSET (由SDK推断)

5. Links:
   - 每个Link必须引用有效的trace_id和span_id
   - trace_id可以不同于当前Span的trace_id

6. 属性数量:
   - 建议 ≤ 128个
   - 超过限制的属性被丢弃,记录在dropped_attributes_count
```

---

## 5. 形式化规范

### 5.1 Span定义

**集合论定义**：

```text
定义1 (Span):
Span是一个14元组:
S = (tid, sid, psid, ts, n, k, t₀, t₁, A, E, L, dc, s)

其中:
- tid ∈ TraceID = {0,1}^128 \ {0^128}
  trace标识符,非全零的128位串
  
- sid ∈ SpanID = {0,1}^64 \ {0^64}
  span标识符,非全零的64位串
  
- psid ∈ SpanID ∪ {⊥}
  父span标识符,可能为空
  
- ts ∈ String
  trace状态
  
- n ∈ String \ {ε}
  span名称,非空字符串
  
- k ∈ SpanKind = {UNSPECIFIED, INTERNAL, SERVER, CLIENT, PRODUCER, CONSUMER}
  span类型
  
- t₀, t₁ ∈ ℕ⁺
  开始和结束时间戳(纳秒)
  
- A ⊆ Attribute
  属性集合
  
- E ∈ Event*
  事件序列
  
- L ⊆ Link
  链接集合
  
- dc ∈ ℕ × ℕ × ℕ
  丢弃计数 (属性, 事件, 链接)
  
- s ∈ Status
  状态
```

### 5.2 不变量

**Span不变量**：

```text
定理1 (时间顺序):
∀ span S, t₀(S) ≤ t₁(S)

定理2 (父子时间关系):
∀ span C, parent P,
  如果 psid(C) = sid(P) ∧ tid(C) = tid(P), 则:
    t₀(P) ≤ t₀(C) ∧ t₁(C) ≤ t₁(P)
  (允许小的时钟漂移)

定理3 (trace_id一致性):
∀ span C, parent P,
  如果 psid(C) = sid(P), 则 tid(C) = tid(P)

定理4 (span_id唯一性):
∀ span S₁, S₂,
  如果 tid(S₁) = tid(S₂) ∧ sid(S₁) = sid(S₂), 则 S₁ = S₂
  (在同一trace内span_id唯一)

定理5 (非循环性):
∀ span S,
  ¬∃路径 S → ... → S
  (Span不能是自己的祖先)
```

### 5.3 关系属性

**父子关系**：

```text
定义2 (父子关系):
ParentOf ⊆ Span × Span

(P, C) ∈ ParentOf ⟺
  psid(C) = sid(P) ∧
  tid(C) = tid(P)

性质:
1. 非自反: ∀S, (S, S) ∉ ParentOf
2. 非对称: ∀P,C, (P,C) ∈ ParentOf → (C,P) ∉ ParentOf
3. 非传递: ∃P,C,G, (P,C) ∈ ParentOf ∧ (C,G) ∈ ParentOf
            但不构成传递闭包的直接成员

定义3 (祖先关系):
AncestorOf = ParentOf⁺  (传递闭包)

性质:
1. 非自反
2. 非对称
3. 传递: ∀A,B,C, (A,B) ∈ AncestorOf ∧ (B,C) ∈ AncestorOf
                 → (A,C) ∈ AncestorOf
4. 非循环: ∀S, (S, S) ∉ AncestorOf
```

---

## 6. 字段大小分析

**编码大小估算**：

```text
最小Span (必需字段):
- trace_id: 18 bytes (tag 1 + len 1 + data 16)
- span_id: 10 bytes (tag 1 + len 1 + data 8)
- name: 10 bytes (tag 1 + len 1 + "HTTP GET" 8)
- kind: 2 bytes (tag 1 + varint 1)
- start_time: 10 bytes (tag 1 + fixed64 8 + 实际1字节tag)
- end_time: 10 bytes
总计: ~60 bytes

典型Span (含属性):
- 基础: 60 bytes
- parent_span_id: 10 bytes
- attributes (5个): ~150 bytes
- events (2个): ~100 bytes
- status: ~20 bytes
总计: ~340 bytes

大型Span:
- 基础: 60 bytes
- 属性 (20个): ~600 bytes
- 事件 (10个): ~500 bytes
- 链接 (5个): ~250 bytes
总计: ~1,410 bytes
```

---

## 7. 实现示例

### 7.1 创建Span

**Go示例**：

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
)

func processRequest(ctx context.Context, req *Request) error {
    tracer := otel.Tracer("my-service")
    
    // 创建Span
    ctx, span := tracer.Start(ctx, "processRequest",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            attribute.String("http.method", req.Method),
            attribute.String("http.url", req.URL),
        ),
    )
    defer span.End()  // 确保Span结束
    
    // 业务逻辑
    err := doWork(ctx)
    if err != nil {
        span.SetStatus(codes.Error, err.Error())
        span.RecordError(err)
        return err
    }
    
    span.SetStatus(codes.Ok, "")
    return nil
}
```

### 7.2 设置属性

```go
// 在创建时设置
span := tracer.Start(ctx, "operation",
    trace.WithAttributes(
        attribute.String("key", "value"),
        attribute.Int("count", 42),
    ),
)

// 运行时设置
span.SetAttributes(
    attribute.String("user.id", userID),
    attribute.Bool("cache.hit", true),
)
```

### 7.3 添加事件

```go
// 添加简单事件
span.AddEvent("cache miss")

// 添加带属性的事件
span.AddEvent("processing_complete",
    trace.WithAttributes(
        attribute.Int("items_processed", 100),
        attribute.Float64("duration_ms", 123.45),
    ),
)

// 记录异常
span.RecordError(err,
    trace.WithAttributes(
        attribute.String("error.type", "validation"),
    ),
)
```

### 7.4 结束Span

```go
// 自动结束 (推荐)
defer span.End()

// 手动结束
span.End()

// 使用特定时间结束
span.End(trace.WithTimestamp(customTime))
```

---

## 8. 最佳实践

```text
1. 命名
   ✅ 使用通用名称: "HTTP GET", "SELECT users"
   ❌ 避免具体值: "HTTP GET /users/123"
   ✅ 简短明了: ≤ 64字符

2. 时间
   ✅ 使用单调时钟 (Go: time.Now())
   ✅ 尽快调用End()
   ❌ 不要延迟太久

3. 属性
   ✅ 使用语义约定
   ✅ 合理数量: 建议 ≤ 20个
   ❌ 避免高基数: user_id作为属性OK, 作为name不OK

4. Status
   ✅ 错误时设置ERROR
   ✅ 包含有意义的message
   ⚠️ OK可选 (默认UNSET由SDK推断)

5. 事件
   ✅ 记录关键时间点
   ✅ 记录异常
   ❌ 不要过度使用 (考虑性能)

6. 父子关系
   ✅ 正确传递Context
   ✅ 确保parent_span_id正确
   ❌ 避免孤立Span
```

---

## 9. 参考资源

- **OTLP Trace Spec**: <https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/trace/api.md>
- **Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/>
- **Go SDK API**: <https://pkg.go.dev/go.opentelemetry.io/otel/trace>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**下一步**: [02_SpanContext.md](./02_SpanContext.md)

# OpenTelemetry Baggage 详解

> **规范版本**: v1.30.0  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry Baggage 详解](#opentelemetry-baggage-详解)
  - [目录](#目录)
  - [1. Baggage概述](#1-baggage概述)
    - [1.1 什么是Baggage](#11-什么是baggage)
    - [1.2 Baggage vs Resource vs Span Attributes](#12-baggage-vs-resource-vs-span-attributes)
  - [2. Baggage数据结构](#2-baggage数据结构)
    - [2.1 核心结构](#21-核心结构)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. Baggage传播](#3-baggage传播)
    - [3.1 W3C Baggage规范](#31-w3c-baggage规范)
    - [3.2 传播实现](#32-传播实现)
  - [4. Baggage API](#4-baggage-api)
    - [4.1 Go实现](#41-go实现)
    - [4.2 Python实现](#42-python实现)
    - [4.3 Java实现](#43-java实现)
  - [5. 使用场景](#5-使用场景)
  - [6. 性能考虑](#6-性能考虑)
  - [7. 安全考虑](#7-安全考虑)
  - [8. 最佳实践](#8-最佳实践)
  - [9. 参考资源](#9-参考资源)

---

## 1. Baggage概述

### 1.1 什么是Baggage

**定义**：

```text
Baggage (行李):
跨进程/跨服务传播的键值对集合

特点:
1. 分布式传播
   - 随请求传播
   - 跨服务边界
   - 跨语言边界

2. 上下文信息
   - 业务上下文
   - 用户信息
   - 实验标志

3. 独立于Trace
   - 不依赖TraceContext
   - 可单独使用
   - 与Span解耦

4. 自动传播
   - SDK自动注入
   - SDK自动提取
   - 透明传递

与Trace的区别:
- Trace: 请求链路追踪
- Baggage: 上下文数据传播
```

**使用场景**：

```text
1. 用户标识传播
   user.id: "user-123"
   user.tier: "premium"
   → 所有下游服务都能访问

2. A/B测试标志
   experiment.variant: "A"
   feature.flag: "new-checkout"
   → 一致的实验体验

3. 请求优先级
   request.priority: "high"
   → 下游服务优先处理

4. 租户标识
   tenant.id: "tenant-456"
   → 多租户隔离

5. 地理位置
   geo.region: "us-west"
   → 数据本地化

示例流程:
前端 (设置 user.id=123) 
  → API Gateway (传播)
  → Order Service (读取 user.id=123)
  → Payment Service (读取 user.id=123)
  → Notification Service (读取 user.id=123)
```

### 1.2 Baggage vs Resource vs Span Attributes

**三者对比**：

```text
┌─────────────────┬──────────────┬──────────────┬──────────────┐
│ 特性            │ Baggage      │ Resource     │ Span Attr    │
├─────────────────┼──────────────┼──────────────┼──────────────┤
│ 作用域          │ 请求级别      │ 进程级别     │ Span级别      │
│ 传播            │ ✅ 跨服务    │ ❌ 不传播    │ ❌ 不传播    │
│ 可变性          │ ✅ 可变      │ ❌ 不可变    │ ❌ 不可变    │
│ 用途            │ 上下文传播    │ 服务标识     │ 事件属性      │
│ 示例            │ user.id      │ service.name │ http.status  │
│ 数据量          │ 小 (< 10KB)  │ 小 (< 1KB)   │ 中 (< 10KB)   │
└─────────────────┴──────────────┴──────────────┴──────────────┘

使用选择:
- 跨服务传播 → Baggage
- 服务标识 → Resource
- 事件详情 → Span Attributes

示例:
Resource: {service.name: "order-service"}  // 所有Span共享
Baggage: {user.id: "123"}  // 跨服务传播
Span Attribute: {order.id: "ORD-456"}  // 单个Span
```

---

## 2. Baggage数据结构

### 2.1 核心结构

**Baggage Entry**：

```text
Baggage = Map<string, BaggageEntry>

BaggageEntry:
- Value: string (必需)
- Metadata: string (可选)

示例:
{
  "user.id": {
    "value": "user-123",
    "metadata": "opaque"
  },
  "experiment.variant": {
    "value": "A",
    "metadata": ""
  }
}
```

**限制**：

```text
键 (Key):
- 类型: string
- 最大长度: 不限制（但建议 < 256字符）
- 命名: 推荐使用点分隔 (user.id)
- 大小写: 不敏感（建议小写）

值 (Value):
- 类型: string
- 最大长度: 不限制（但建议 < 1KB）
- 编码: UTF-8

元数据 (Metadata):
- 类型: string
- 用途: 附加信息（如隐私标记）
- 可选

总大小:
- 推荐: < 8KB
- 硬限制: 由传输协议决定
  - HTTP: < 8KB (header限制)
  - gRPC: < 8KB (建议)
```

### 2.2 形式化定义

```text
Baggage定义:
B = {(k₁,v₁,m₁), (k₂,v₂,m₂), ..., (kₙ,vₙ,mₙ)}

其中:
kᵢ: string (键, 唯一)
vᵢ: string (值)
mᵢ: string (元数据, 可选)

约束:
1. 键唯一性: ∀i,j: i≠j → kᵢ≠kⱼ
2. 键非空: ∀i: kᵢ ≠ ""
3. 值非空: ∀i: vᵢ ≠ ""
4. 大小限制: |B| < 8KB

操作:
1. Set(key, value, metadata): 设置或更新
2. Get(key): 获取值
3. Remove(key): 删除
4. GetAll(): 获取所有条目

传播规则:
B(request) ⊆ B(parent) ∪ B(new)
- 继承父级Baggage
- 可添加新条目
- 可覆盖已有条目
```

---

## 3. Baggage传播

### 3.1 W3C Baggage规范

**HTTP Header格式**：

```text
Baggage Header:
baggage: key1=value1,key2=value2;metadata

格式规则:
1. 键值对: key=value
2. 分隔符: 逗号 (,)
3. 元数据: 分号 (;) 后跟metadata
4. URL编码: 特殊字符需编码

示例:
baggage: userId=123,experimentVariant=A,requestPriority=high

带元数据:
baggage: userId=123;opaque,sessionId=abc;private

URL编码:
baggage: user%20name=John%20Doe,email=user%40example.com

多行 (多个header):
baggage: userId=123
baggage: sessionId=abc
baggage: experimentVariant=A
```

### 3.2 传播实现

**Go实现**：

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel/baggage"
    "go.opentelemetry.io/otel/propagation"
)

// 设置Baggage
func setBaggage(ctx context.Context) context.Context {
    // 创建Baggage成员
    userID, _ := baggage.NewMember("user.id", "user-123")
    experiment, _ := baggage.NewMember("experiment.variant", "A")
    priority, _ := baggage.NewMember("request.priority", "high")
    
    // 创建Baggage
    bag, _ := baggage.New(userID, experiment, priority)
    
    // 将Baggage附加到Context
    ctx = baggage.ContextWithBaggage(ctx, bag)
    
    return ctx
}

// 获取Baggage
func getBaggage(ctx context.Context) {
    bag := baggage.FromContext(ctx)
    
    // 获取单个值
    userID := bag.Member("user.id").Value()
    fmt.Println("User ID:", userID)  // "user-123"
    
    // 遍历所有成员
    for _, member := range bag.Members() {
        fmt.Printf("%s = %s\n", member.Key(), member.Value())
    }
}

// HTTP客户端: 注入Baggage到Header
func makeHTTPRequest(ctx context.Context) {
    req, _ := http.NewRequest("GET", "http://api.example.com", nil)
    
    // 使用Propagator注入
    propagator := propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    )
    
    carrier := propagation.HeaderCarrier(req.Header)
    propagator.Inject(ctx, carrier)
    
    // req.Header现在包含baggage header
    resp, _ := http.DefaultClient.Do(req)
}

// HTTP服务器: 从Header提取Baggage
func handleHTTPRequest(w http.ResponseWriter, r *http.Request) {
    propagator := propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    )
    
    carrier := propagation.HeaderCarrier(r.Header)
    ctx := propagator.Extract(context.Background(), carrier)
    
    // 现在ctx包含Baggage
    bag := baggage.FromContext(ctx)
    userID := bag.Member("user.id").Value()
    
    // 使用userID...
}
```

**Python实现**：

```python
from opentelemetry import baggage
from opentelemetry.propagate import inject, extract

# 设置Baggage
ctx = baggage.set_baggage("user.id", "user-123")
ctx = baggage.set_baggage("experiment.variant", "A", context=ctx)

# 获取Baggage
user_id = baggage.get_baggage("user.id", context=ctx)
print(f"User ID: {user_id}")  # "user-123"

# 获取所有
all_baggage = baggage.get_all(context=ctx)
for key, value in all_baggage.items():
    print(f"{key} = {value}")

# HTTP客户端: 注入
headers = {}
inject(headers, context=ctx)
# headers现在包含 'baggage' header

# HTTP服务器: 提取
headers = request.headers
ctx = extract(headers)
user_id = baggage.get_baggage("user.id", context=ctx)
```

**Java实现**：

```java
import io.opentelemetry.api.baggage.Baggage;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.propagation.TextMapPropagator;

// 设置Baggage
Baggage baggage = Baggage.builder()
    .put("user.id", "user-123")
    .put("experiment.variant", "A")
    .put("request.priority", "high")
    .build();

Context ctx = Context.current().with(baggage);

// 获取Baggage
Baggage currentBaggage = Baggage.fromContext(ctx);
String userId = currentBaggage.getEntryValue("user.id");
System.out.println("User ID: " + userId);

// 遍历所有
currentBaggage.forEach((key, entry) -> {
    System.out.println(key + " = " + entry.getValue());
});

// HTTP注入
Map<String, String> headers = new HashMap<>();
TextMapPropagator propagator = GlobalOpenTelemetry.getPropagators().getTextMapPropagator();
propagator.inject(ctx, headers, Map::put);

// HTTP提取
Context extractedCtx = propagator.extract(Context.current(), headers, Map::get);
Baggage extractedBaggage = Baggage.fromContext(extractedCtx);
```

---

## 4. Baggage API

### 4.1 Go实现

```go
// 创建Baggage
func createBaggage() baggage.Baggage {
    member1, _ := baggage.NewMember("key1", "value1")
    member2, _ := baggage.NewMemberRaw("key2", "value2", "metadata")
    
    bag, _ := baggage.New(member1, member2)
    return bag
}

// 修改Baggage
func modifyBaggage(bag baggage.Baggage) baggage.Baggage {
    // 添加新成员
    newMember, _ := baggage.NewMember("key3", "value3")
    bag, _ = bag.SetMember(newMember)
    
    // 删除成员
    bag = bag.DeleteMember("key1")
    
    return bag
}

// Context集成
func useBaggageWithContext() {
    ctx := context.Background()
    
    // 设置
    member, _ := baggage.NewMember("user.id", "123")
    bag, _ := baggage.New(member)
    ctx = baggage.ContextWithBaggage(ctx, bag)
    
    // 传递ctx到其他函数
    processRequest(ctx)
}

func processRequest(ctx context.Context) {
    // 获取
    bag := baggage.FromContext(ctx)
    userID := bag.Member("user.id").Value()
    
    // 使用userID...
}
```

### 4.2 Python实现

```python
from opentelemetry import baggage, context

# 设置多个值
ctx = context.get_current()
ctx = baggage.set_baggage("user.id", "123", context=ctx)
ctx = baggage.set_baggage("session.id", "abc", context=ctx)

# 使用context manager
token = context.attach(ctx)
try:
    # 在这个作用域内，Baggage是激活的
    user_id = baggage.get_baggage("user.id")
    print(f"User: {user_id}")
finally:
    context.detach(token)

# 删除值
ctx = baggage.remove_baggage("session.id", context=ctx)

# 清空所有
ctx = baggage.clear(context=ctx)
```

### 4.3 Java实现

```java
// 构建器模式
Baggage baggage = Baggage.builder()
    .put("user.id", "123")
    .put("session.id", "abc")
    .build();

// 修改（不可变，返回新实例）
Baggage newBaggage = baggage.toBuilder()
    .put("request.id", "req-xyz")
    .remove("session.id")
    .build();

// Scope管理
try (Scope scope = baggage.makeCurrent()) {
    // 在这个作用域内，Baggage是激活的
    String userId = Baggage.current().getEntryValue("user.id");
    System.out.println("User: " + userId);
}
```

---

## 5. 使用场景

**场景1: 用户标识传播**:

```go
// 前端/API Gateway
func handleLogin(w http.ResponseWriter, r *http.Request) {
    userID := authenticateUser(r)
    
    // 设置Baggage
    member, _ := baggage.NewMember("user.id", userID)
    member2, _ := baggage.NewMember("user.tier", "premium")
    bag, _ := baggage.New(member, member2)
    ctx := baggage.ContextWithBaggage(r.Context(), bag)
    
    // 调用下游服务
    orderClient.CreateOrder(ctx, orderData)
}

// Order Service
func CreateOrder(ctx context.Context, data OrderData) {
    bag := baggage.FromContext(ctx)
    userID := bag.Member("user.id").Value()
    userTier := bag.Member("user.tier").Value()
    
    // 基于用户等级应用折扣
    if userTier == "premium" {
        applyPremiumDiscount()
    }
    
    // 记录日志时包含userID
    logger.Info("Creating order", "user.id", userID)
}
```

**场景2: A/B测试**:

```go
// 前端
func assignExperiment(ctx context.Context) context.Context {
    variant := selectVariant()  // "A" or "B"
    
    member, _ := baggage.NewMember("experiment.checkout", variant)
    bag, _ := baggage.New(member)
    
    return baggage.ContextWithBaggage(ctx, bag)
}

// 所有下游服务
func handleRequest(ctx context.Context) {
    bag := baggage.FromContext(ctx)
    variant := bag.Member("experiment.checkout").Value()
    
    if variant == "A" {
        useNewCheckoutFlow()
    } else {
        useOldCheckoutFlow()
    }
}
```

**场景3: 请求优先级**:

```go
// API Gateway
func setPriority(ctx context.Context, priority string) context.Context {
    member, _ := baggage.NewMember("request.priority", priority)
    bag, _ := baggage.New(member)
    return baggage.ContextWithBaggage(ctx, bag)
}

// 下游服务
func processWithPriority(ctx context.Context) {
    bag := baggage.FromContext(ctx)
    priority := bag.Member("request.priority").Value()
    
    if priority == "high" {
        // 使用高优先级队列
        highPriorityQueue.Add(task)
    } else {
        normalQueue.Add(task)
    }
}
```

---

## 6. 性能考虑

```text
1. 大小限制
   ✅ 保持 < 8KB
   ✅ 每个key-value < 1KB
   ✅ 总key数 < 50

2. 传播开销
   HTTP: ~1-2KB overhead per request
   gRPC: ~1-2KB overhead per request
   
   影响:
   - 网络带宽
   - 序列化/反序列化时间
   - Header大小限制

3. 性能测试
   无Baggage: 100 req/s, 10ms p99
   小Baggage (1KB): 99 req/s, 11ms p99 (1% overhead)
   大Baggage (8KB): 95 req/s, 15ms p99 (5% overhead)

4. 优化建议
   - 只传播必要数据
   - 使用短键名 (user.id vs user.identifier)
   - 避免传播大对象
   - 考虑使用引用 (传ID而非完整数据)

示例优化:
❌ 错误:
baggage.set("user.profile", json.dumps(user_profile))  // 可能10KB+

✅ 正确:
baggage.set("user.id", "123")  // 下游按需查询
```

---

## 7. 安全考虑

```text
1. 敏感数据
   ❌ 不要传播:
   - 密码
   - API密钥
   - 信用卡号
   - SSN
   - 完整邮箱

   ✅ 可以传播:
   - 用户ID (哈希)
   - 会话ID
   - 实验标志
   - 地理区域

2. 数据泄露风险
   Baggage在HTTP header中明文传输!
   - 使用HTTPS
   - 避免敏感信息
   - 使用metadata标记隐私级别

3. 注入攻击
   验证Baggage内容
   不要直接用于:
   - SQL查询
   - 命令执行
   - 文件路径

4. 隐私合规
   GDPR考虑:
   - 不传播PII
   - 使用假名化ID
   - 记录Baggage使用

示例:
// ❌ 危险
sql := "SELECT * FROM users WHERE id = " + baggage.get("user.id")

// ✅ 安全
userID := baggage.get("user.id")
sql := "SELECT * FROM users WHERE id = ?"
db.Query(sql, userID)
```

---

## 8. 最佳实践

```text
✅ DO (推荐)
1. 使用命名约定
   - user.id (不是 userId)
   - experiment.variant (不是 exp_var)
   
2. 保持小巧
   - < 8KB总大小
   - < 10个键值对
   
3. 使用短键名
   - user.id (不是 user.identifier)
   
4. 文档化键
   - 维护Baggage键列表
   - 说明用途和格式
   
5. 验证值
   - 检查格式
   - 检查长度

6. 监控大小
   - 记录Baggage大小指标
   - 告警超大Baggage

❌ DON'T (避免)
1. 不要传播敏感数据
2. 不要传播大对象
3. 不要无限制添加
4. 不要直接用于SQL
5. 不要忽略大小限制

命名约定:
✅ user.id
✅ experiment.variant
✅ request.priority
❌ userId
❌ exp-var
❌ PRIORITY

示例Baggage键注册表:
| Key | Type | Purpose | Example |
|-----|------|---------|---------|
| user.id | string | 用户标识 | "user-123" |
| user.tier | string | 用户等级 | "premium" |
| experiment.checkout | string | A/B测试 | "A" |
| request.priority | string | 请求优先级 | "high" |
| geo.region | string | 地理区域 | "us-west" |
```

---

## 9. 参考资源

- **W3C Baggage**: <https://www.w3.org/TR/baggage/>
- **OpenTelemetry Baggage**: <https://opentelemetry.io/docs/specs/otel/baggage/api/>
- **Go SDK**: <https://pkg.go.dev/go.opentelemetry.io/otel/baggage>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [SpanContext](../01_Traces数据模型/02_SpanContext.md), [Resource模型](../04_Resource/01_Resource模型.md)

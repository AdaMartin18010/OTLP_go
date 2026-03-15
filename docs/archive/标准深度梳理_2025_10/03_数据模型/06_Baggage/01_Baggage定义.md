# Baggage 定义

## 📋 目录

- [Baggage 定义](#baggage-定义)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [什么是 Baggage](#什么是-baggage)
    - [为什么需要 Baggage](#为什么需要-baggage)
  - [Baggage 数据结构](#baggage-数据结构)
    - [1. 完整定义](#1-完整定义)
    - [2. Protocol Buffers 定义](#2-protocol-buffers-定义)
    - [3. Go 结构体定义](#3-go-结构体定义)
  - [Baggage Entry](#baggage-entry)
    - [1. Entry 结构](#1-entry-结构)
    - [2. Metadata](#2-metadata)
  - [Baggage 操作](#baggage-操作)
    - [1. 创建和设置](#1-创建和设置)
    - [2. 获取和删除](#2-获取和删除)
    - [3. 合并操作](#3-合并操作)
  - [Go 1.25.1 实现](#go-1251-实现)
    - [1. 基本实现](#1-基本实现)
    - [2. Context 集成](#2-context-集成)
    - [3. 线程安全](#3-线程安全)
  - [使用场景](#使用场景)
    - [1. 用户标识传递](#1-用户标识传递)
    - [2. 租户信息传递](#2-租户信息传递)
    - [3. 功能标志传递](#3-功能标志传递)
  - [限制和约束](#限制和约束)
    - [1. 大小限制](#1-大小限制)
    - [2. 键值限制](#2-键值限制)
    - [3. 性能考虑](#3-性能考虑)
  - [最佳实践](#最佳实践)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

### 什么是 Baggage

**Baggage** 是 OpenTelemetry 中用于在分布式系统中传播键值对的机制。它允许跨服务边界传递上下文信息。

```text
Baggage = {
  "user.id": "12345",
  "tenant.id": "acme-corp",
  "feature.flag": "new-ui-enabled"
}
```

### 为什么需要 Baggage

```text
问题：
❌ 跨服务传递业务上下文困难
❌ 无法在下游服务中获取上游信息
❌ 日志和追踪缺少关键业务属性

Baggage 解决方案：
✅ 自动跨服务传播键值对
✅ 在整个调用链中可访问
✅ 不依赖特定的 RPC 框架
✅ 与追踪、度量、日志集成
```

**重要区别**:

```text
Baggage vs Span Attributes:
- Baggage: 跨服务传播，所有下游可见
- Span Attributes: 仅本地，不传播

Baggage vs Resource:
- Baggage: 动态，随请求变化
- Resource: 静态，描述服务本身
```

---

## Baggage 数据结构

### 1. 完整定义

Baggage 是一个键值对的集合：

```text
Baggage {
  Entries: map[string]Entry
}

Entry {
  Value:    string
  Metadata: string (可选)
}

示例:
{
  "user.id": Entry{Value: "12345", Metadata: ""},
  "tenant.id": Entry{Value: "acme-corp", Metadata: "propagate=true"}
}
```

### 2. Protocol Buffers 定义

```protobuf
// Baggage 在 W3C Baggage 头中传播
// 格式: key1=value1;metadata1,key2=value2;metadata2

// OpenTelemetry 没有直接的 Baggage protobuf 定义
// 因为 Baggage 通过 HTTP/gRPC 头传播
```

### 3. Go 结构体定义

```go
package baggage

import (
    "go.opentelemetry.io/otel/baggage"
)

// Baggage 是不可变的键值对集合
type Baggage struct {
    members map[string]baggage.Member
}

// Member 表示 Baggage 中的一个条目
type Member struct {
    key      string
    value    string
    metadata string
}

// NewMember 创建新的 Member
func NewMember(key, value string) (baggage.Member, error) {
    return baggage.NewMember(key, value)
}

// NewMemberWithMetadata 创建带元数据的 Member
func NewMemberWithMetadata(key, value, metadata string) (baggage.Member, error) {
    return baggage.NewMemberRaw(key, value, metadata)
}
```

---

## Baggage Entry

### 1. Entry 结构

每个 Baggage Entry 包含值和可选的元数据：

```go
// Entry 示例
entry1 := baggage.NewMember("user.id", "12345")
// key: "user.id"
// value: "12345"
// metadata: ""

entry2 := baggage.NewMemberRaw("tenant.id", "acme", "propagate=true")
// key: "tenant.id"
// value: "acme"
// metadata: "propagate=true"
```

**值的限制**:
- 必须是 UTF-8 字符串
- 不能包含某些特殊字符（如 `,`, `;`, `=`）
- 推荐进行 URL 编码

### 2. Metadata

Metadata 提供关于 Entry 的额外信息：

```go
// 常见 Metadata 用途
metadata := "propagate=true"     // 控制传播行为
metadata := "ttl=300"            // 生存时间（秒）
metadata := "privacy=sensitive"  // 隐私级别
```

**Metadata 格式**:
```text
key=value;key2=value2

示例:
propagate=true;ttl=300
```

---

## Baggage 操作

### 1. 创建和设置

```go
package main

import (
    "context"
    "go.opentelemetry.io/otel/baggage"
)

func CreateBaggage() baggage.Baggage {
    // 创建 Members
    userID, _ := baggage.NewMember("user.id", "12345")
    tenantID, _ := baggage.NewMember("tenant.id", "acme-corp")
    
    // 创建 Baggage
    bag, _ := baggage.New(userID, tenantID)
    
    return bag
}

// 添加到 Context
func AddBaggageToContext(ctx context.Context) context.Context {
    bag := CreateBaggage()
    return baggage.ContextWithBaggage(ctx, bag)
}

// 更新 Baggage
func UpdateBaggage(ctx context.Context, key, value string) context.Context {
    bag := baggage.FromContext(ctx)
    
    // 添加新成员
    member, _ := baggage.NewMember(key, value)
    newBag, _ := bag.SetMember(member)
    
    return baggage.ContextWithBaggage(ctx, newBag)
}
```

### 2. 获取和删除

```go
// 获取 Baggage
func GetBaggage(ctx context.Context) baggage.Baggage {
    return baggage.FromContext(ctx)
}

// 获取特定值
func GetValue(ctx context.Context, key string) string {
    bag := baggage.FromContext(ctx)
    member := bag.Member(key)
    return member.Value()
}

// 删除成员
func DeleteMember(ctx context.Context, key string) context.Context {
    bag := baggage.FromContext(ctx)
    newBag := bag.DeleteMember(key)
    return baggage.ContextWithBaggage(ctx, newBag)
}

// 检查是否存在
func HasMember(ctx context.Context, key string) bool {
    bag := baggage.FromContext(ctx)
    member := bag.Member(key)
    return member.Value() != ""
}
```

### 3. 合并操作

```go
// 合并两个 Baggage
func MergeBaggage(bag1, bag2 baggage.Baggage) (baggage.Baggage, error) {
    members := make([]baggage.Member, 0)
    
    // 添加 bag1 的成员
    for _, member := range bag1.Members() {
        members = append(members, member)
    }
    
    // 添加 bag2 的成员（会覆盖重复的键）
    for _, member := range bag2.Members() {
        members = append(members, member)
    }
    
    return baggage.New(members...)
}
```

---

## Go 1.25.1 实现

### 1. 基本实现

```go
package main

import (
    "context"
    "fmt"
    "go.opentelemetry.io/otel/baggage"
)

func main() {
    ctx := context.Background()
    
    // 创建 Baggage
    userID, _ := baggage.NewMember("user.id", "12345")
    tenantID, _ := baggage.NewMember("tenant.id", "acme-corp")
    
    bag, err := baggage.New(userID, tenantID)
    if err != nil {
        panic(err)
    }
    
    // 添加到 Context
    ctx = baggage.ContextWithBaggage(ctx, bag)
    
    // 在下游服务中读取
    processsRequest(ctx)
}

func processsRequest(ctx context.Context) {
    bag := baggage.FromContext(ctx)
    
    // 获取用户 ID
    userID := bag.Member("user.id").Value()
    fmt.Printf("User ID: %s\n", userID)
    
    // 获取租户 ID
    tenantID := bag.Member("tenant.id").Value()
    fmt.Printf("Tenant ID: %s\n", tenantID)
}
```

### 2. Context 集成

```go
package middleware

import (
    "context"
    "net/http"
    "go.opentelemetry.io/otel/baggage"
    "go.opentelemetry.io/otel/propagation"
)

// HTTP 中间件：自动传播 Baggage
func BaggageMiddleware(next http.Handler) http.Handler {
    propagator := propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    )
    
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 从 HTTP 头提取 Baggage
        ctx := propagator.Extract(r.Context(), propagation.HeaderCarrier(r.Header))
        
        // 处理请求
        next.ServeHTTP(w, r.WithContext(ctx))
    })
}

// HTTP 客户端：自动注入 Baggage
func MakeRequest(ctx context.Context, url string) (*http.Response, error) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    propagator := propagation.NewCompositeTextMapPropagator(
        propagation.TraceContext{},
        propagation.Baggage{},
    )
    
    // 注入 Baggage 到 HTTP 头
    propagator.Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    return http.DefaultClient.Do(req)
}
```

### 3. 线程安全

```go
// Baggage 是不可变的，天然线程安全
func ConcurrentAccess(ctx context.Context) {
    bag := baggage.FromContext(ctx)
    
    // 多个 goroutine 同时读取是安全的
    go func() {
        value := bag.Member("user.id").Value()
        fmt.Println(value)
    }()
    
    go func() {
        value := bag.Member("tenant.id").Value()
        fmt.Println(value)
    }()
}

// 更新操作创建新的 Baggage
func SafeUpdate(ctx context.Context) context.Context {
    bag := baggage.FromContext(ctx)
    
    // SetMember 返回新的 Baggage，不修改原有
    member, _ := baggage.NewMember("new.key", "new.value")
    newBag, _ := bag.SetMember(member)
    
    return baggage.ContextWithBaggage(ctx, newBag)
}
```

---

## 使用场景

### 1. 用户标识传递

```go
package auth

import (
    "context"
    "go.opentelemetry.io/otel/baggage"
)

// 在认证服务中设置用户 ID
func Authenticate(ctx context.Context, username string) context.Context {
    userID := lookupUserID(username)
    
    member, _ := baggage.NewMember("user.id", userID)
    bag, _ := baggage.FromContext(ctx).SetMember(member)
    
    return baggage.ContextWithBaggage(ctx, bag)
}

// 在下游服务中使用
func LogUserAction(ctx context.Context, action string) {
    bag := baggage.FromContext(ctx)
    userID := bag.Member("user.id").Value()
    
    log.Printf("User %s performed action: %s", userID, action)
}
```

### 2. 租户信息传递

```go
package tenant

// 多租户 SaaS 系统
func SetTenantContext(ctx context.Context, tenantID string) context.Context {
    member, _ := baggage.NewMember("tenant.id", tenantID)
    bag, _ := baggage.FromContext(ctx).SetMember(member)
    return baggage.ContextWithBaggage(ctx, bag)
}

// 数据库查询自动过滤租户
func QueryData(ctx context.Context, table string) ([]Record, error) {
    bag := baggage.FromContext(ctx)
    tenantID := bag.Member("tenant.id").Value()
    
    // 自动添加租户过滤条件
    query := fmt.Sprintf("SELECT * FROM %s WHERE tenant_id = ?", table)
    return db.Query(query, tenantID)
}
```

### 3. 功能标志传递

```go
package features

// A/B 测试或功能开关
func SetFeatureFlag(ctx context.Context, flag, value string) context.Context {
    key := "feature." + flag
    member, _ := baggage.NewMember(key, value)
    bag, _ := baggage.FromContext(ctx).SetMember(member)
    return baggage.ContextWithBaggage(ctx, bag)
}

// 根据标志返回不同逻辑
func RenderUI(ctx context.Context) string {
    bag := baggage.FromContext(ctx)
    newUI := bag.Member("feature.new-ui").Value()
    
    if newUI == "enabled" {
        return RenderNewUI()
    }
    return RenderOldUI()
}
```

---

## 限制和约束

### 1. 大小限制

```go
// W3C Baggage 规范限制
const (
    // 单个成员的最大大小
    MaxMemberSize = 4096 // bytes
    
    // Baggage 总大小限制
    MaxTotalSize = 8192 // bytes
    
    // 成员数量限制
    MaxMembers = 180
)

// 检查大小
func ValidateBaggageSize(bag baggage.Baggage) error {
    totalSize := 0
    for _, member := range bag.Members() {
        memberSize := len(member.Key()) + len(member.Value())
        if memberSize > MaxMemberSize {
            return fmt.Errorf("member too large: %d bytes", memberSize)
        }
        totalSize += memberSize
    }
    
    if totalSize > MaxTotalSize {
        return fmt.Errorf("baggage too large: %d bytes", totalSize)
    }
    
    return nil
}
```

### 2. 键值限制

```go
// 键的限制
// - 只能包含: a-z, 0-9, -, _
// - 不能以 - 开头

// 值的限制
// - URL 安全字符
// - 需要编码特殊字符

import "net/url"

// 安全的值编码
func SafeValue(value string) string {
    return url.QueryEscape(value)
}

// 解码
func DecodeValue(encoded string) string {
    decoded, _ := url.QueryUnescape(encoded)
    return decoded
}
```

### 3. 性能考虑

```text
性能影响:
✅ Baggage 是不可变的，读取开销小
⚠️  每次更新创建新对象
⚠️  传播增加网络开销
⚠️  过大的 Baggage 影响性能

优化建议:
✅ 限制 Baggage 大小 (< 4KB)
✅ 只传播必要信息
✅ 避免频繁更新
✅ 使用简短的键名
```

---

## 最佳实践

```go
// ✅ 正确：使用简短的键名
member, _ := baggage.NewMember("user.id", "12345")

// ❌ 错误：键名过长
member, _ := baggage.NewMember("application.user.identifier", "12345")

// ✅ 正确：只传播必要信息
bag, _ := baggage.New(
    userID,
    tenantID,
)

// ❌ 错误：传播过多信息
bag, _ := baggage.New(
    userID,
    userName,
    userEmail,
    userPhone,
    userAddress,
    // ... 20+ 个字段
)

// ✅ 正确：使用 URL 编码
value := url.QueryEscape("special@chars#here")
member, _ := baggage.NewMember("key", value)

// ❌ 错误：未编码特殊字符
member, _ := baggage.NewMember("key", "special@chars#here")

// ✅ 正确：检查 Baggage 是否存在
bag := baggage.FromContext(ctx)
if member := bag.Member("user.id"); member.Value() != "" {
    userID := member.Value()
    // 使用 userID
}

// ❌ 错误：直接使用可能为空的值
userID := baggage.FromContext(ctx).Member("user.id").Value()
// userID 可能是 ""
```

---

## 常见问题

**Q1: Baggage 和 Span Attributes 有什么区别？**

```text
Baggage:
- ✅ 跨服务传播
- ✅ 所有下游服务可见
- ✅ 适合传递业务上下文
- ⚠️  增加网络开销

Span Attributes:
- ✅ 本地存储
- ❌ 不跨服务传播
- ✅ 适合记录详细信息
- ✅ 无额外网络开销

使用建议:
- 用户/租户 ID → Baggage
- 请求详情 → Span Attributes
```

**Q2: Baggage 会自动添加到 Span 吗？**

```go
// 默认情况下，Baggage 不会自动添加到 Span
// 需要手动添加

func AddBaggageToSpan(ctx context.Context, span trace.Span) {
    bag := baggage.FromContext(ctx)
    for _, member := range bag.Members() {
        span.SetAttributes(attribute.String(
            "baggage."+member.Key(),
            member.Value(),
        ))
    }
}
```

**Q3: Baggage 的安全性如何？**

```text
安全考虑:
⚠️  Baggage 以明文传播
⚠️  可能被中间人读取
⚠️  不应传递敏感信息

最佳实践:
✅ 只传递非敏感标识符
✅ 避免传递密码、令牌
✅ 使用加密通道 (TLS)
✅ 考虑使用 Metadata 标记隐私级别
```

---

## 参考资源

- [W3C Baggage Specification](https://www.w3.org/TR/baggage/)
- [OpenTelemetry Baggage API](https://opentelemetry.io/docs/specs/otel/baggage/api/)
- [Go SDK Baggage Package](https://pkg.go.dev/go.opentelemetry.io/otel/baggage)
- [02_传播机制.md](./02_传播机制.md)
- [03_形式化定义.md](./03_形式化定义.md)

---

**🎉 恭喜！你已经掌握了 Baggage 的完整定义！**

现在你可以：
- ✅ 理解 Baggage 的作用和结构
- ✅ 创建和管理 Baggage
- ✅ 在分布式系统中传播上下文
- ✅ 遵循大小和安全最佳实践


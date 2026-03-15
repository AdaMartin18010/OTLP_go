# Body 与 Attributes

## 📋 目录

- [Body 与 Attributes](#body-与-attributes)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [Body (日志主体)](#body-日志主体)
    - [1. Body 类型](#1-body-类型)
    - [2. 字符串 Body](#2-字符串-body)
    - [3. 结构化 Body](#3-结构化-body)
    - [4. Body 最佳实践](#4-body-最佳实践)
  - [Attributes (属性)](#attributes-属性)
    - [1. Attributes 结构](#1-attributes-结构)
    - [2. 标准属性](#2-标准属性)
    - [3. 自定义属性](#3-自定义属性)
    - [4. 属性命名约定](#4-属性命名约定)
  - [AnyValue 类型系统](#anyvalue-类型系统)
    - [1. 基本类型](#1-基本类型)
    - [2. 复杂类型](#2-复杂类型)
    - [3. Go 实现](#3-go-实现)
  - [Body vs Attributes](#body-vs-attributes)
    - [设计原则](#设计原则)
  - [Go 1.25.1 完整实现](#go-1251-完整实现)
    - [1. Body 构建器](#1-body-构建器)
    - [2. Attributes 管理器](#2-attributes-管理器)
    - [3. slog 集成](#3-slog-集成)
  - [性能优化](#性能优化)
    - [1. 对象池](#1-对象池)
    - [2. 零分配技术](#2-零分配技术)
    - [3. 延迟序列化](#3-延迟序列化)
  - [最佳实践](#最佳实践)
    - [1. Body 设计](#1-body-设计)
    - [2. Attributes 设计](#2-attributes-设计)
    - [3. 安全性](#3-安全性)
  - [常见问题](#常见问题)
  - [参考资源](#参考资源)

---

## 概述

**Body** 和 **Attributes** 是 LogRecord 的核心内容字段：

```text
LogRecord
├── Body:       日志的主要内容 (消息或结构化数据)
└── Attributes: 日志的元数据 (键值对)
```

**设计原则**:

- Body: 记录"发生了什么"
- Attributes: 记录"相关的上下文"

---

## Body (日志主体)

### 1. Body 类型

Body 使用 **AnyValue** 类型，支持多种数据类型：

```go
type AnyValue struct {
    // 基本类型
    StringValue  *string
    BoolValue    *bool
    IntValue     *int64
    DoubleValue  *float64
    BytesValue   []byte
    
    // 复杂类型
    ArrayValue   *ArrayValue      // 数组
    KvListValue  *KeyValueList    // 键值对列表 (结构化)
}
```

### 2. 字符串 Body

**用途**: 简单的日志消息

```go
// 示例 1: 基本消息
record.Body = &AnyValue{
    StringValue: strPtr("User login successful"),
}

// 示例 2: 格式化消息
msg := fmt.Sprintf("Order %s processed in %v", orderID, duration)
record.Body = &AnyValue{
    StringValue: &msg,
}

// 示例 3: 多行消息
multiline := `Database migration completed:
  - Tables created: 5
  - Indexes created: 12
  - Duration: 2.5s`
record.Body = &AnyValue{
    StringValue: &multiline,
}

func strPtr(s string) *string { return &s }
```

### 3. 结构化 Body

**用途**: 机器可解析的结构化事件

```go
// 示例 1: 事件日志
record.Body = &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "event_name", Value: &AnyValue{StringValue: strPtr("user.login")}},
            {Key: "user_id", Value: &AnyValue{StringValue: strPtr("12345")}},
            {Key: "success", Value: &AnyValue{BoolValue: boolPtr(true)}},
            {Key: "timestamp", Value: &AnyValue{IntValue: int64Ptr(time.Now().Unix())}},
        },
    },
}

// 示例 2: API 请求日志
record.Body = &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "method", Value: &AnyValue{StringValue: strPtr("POST")}},
            {Key: "path", Value: &AnyValue{StringValue: strPtr("/api/users")}},
            {Key: "status", Value: &AnyValue{IntValue: int64Ptr(201)}},
            {Key: "duration_ms", Value: &AnyValue{DoubleValue: float64Ptr(45.2)}},
        },
    },
}

// 示例 3: 错误详情
record.Body = &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "error_type", Value: &AnyValue{StringValue: strPtr("DatabaseError")}},
            {Key: "error_message", Value: &AnyValue{StringValue: strPtr("Connection timeout")}},
            {Key: "error_code", Value: &AnyValue{IntValue: int64Ptr(1062)}},
            {Key: "retry_count", Value: &AnyValue{IntValue: int64Ptr(3)}},
        },
    },
}

func boolPtr(b bool) *bool { return &b }
func int64Ptr(i int64) *int64 { return &i }
func float64Ptr(f float64) *float64 { return &f }
```

### 4. Body 最佳实践

```go
// ✅ 正确：简洁清晰的消息
record.Body = &AnyValue{StringValue: strPtr("User login successful")}

// ✅ 正确：结构化事件
record.Body = &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "event", Value: &AnyValue{StringValue: strPtr("payment.completed")}},
            {Key: "amount", Value: &AnyValue{DoubleValue: float64Ptr(99.99)}},
        },
    },
}

// ❌ 错误：Body 过大
hugData := strings.Repeat("x", 1<<20) // 1 MB
record.Body = &AnyValue{StringValue: &hugData} // 避免

// ❌ 错误：包含敏感信息
record.Body = &AnyValue{StringValue: strPtr(fmt.Sprintf("Password: %s", password))}
```

---

## Attributes (属性)

### 1. Attributes 结构

Attributes 是键值对的映射：

```go
type Attributes map[string]*AnyValue

// 示例
record.Attributes = map[string]*AnyValue{
    "user.id":          {StringValue: strPtr("12345")},
    "http.method":      {StringValue: strPtr("GET")},
    "http.status_code": {IntValue: int64Ptr(200)},
    "duration_ms":      {DoubleValue: float64Ptr(123.45)},
}
```

### 2. 标准属性

**HTTP 属性**:

```go
record.Attributes = map[string]*AnyValue{
    "http.method":       {StringValue: strPtr("POST")},
    "http.url":          {StringValue: strPtr("https://api.example.com/users")},
    "http.status_code":  {IntValue: int64Ptr(201)},
    "http.request_size": {IntValue: int64Ptr(1024)},
    "http.response_size":{IntValue: int64Ptr(2048)},
    "http.user_agent":   {StringValue: strPtr("Mozilla/5.0...")},
}
```

**数据库属性**:

```go
record.Attributes = map[string]*AnyValue{
    "db.system":     {StringValue: strPtr("postgresql")},
    "db.name":       {StringValue: strPtr("users")},
    "db.statement":  {StringValue: strPtr("SELECT * FROM users WHERE id = $1")},
    "db.operation":  {StringValue: strPtr("SELECT")},
    "db.row_count":  {IntValue: int64Ptr(1)},
}
```

**错误属性**:

```go
record.Attributes = map[string]*AnyValue{
    "error.type":    {StringValue: strPtr("DatabaseError")},
    "error.message": {StringValue: strPtr("Connection timeout")},
    "error.stack":   {StringValue: strPtr(string(debug.Stack()))},
}
```

**用户属性**:

```go
record.Attributes = map[string]*AnyValue{
    "user.id":       {StringValue: strPtr("12345")},
    "user.email":    {StringValue: strPtr("user@example.com")},
    "user.role":     {StringValue: strPtr("admin")},
    "user.ip":       {StringValue: strPtr("192.168.1.1")},
}
```

### 3. 自定义属性

```go
// 业务属性
record.Attributes = map[string]*AnyValue{
    "order.id":       {StringValue: strPtr("ORD-12345")},
    "order.total":    {DoubleValue: float64Ptr(299.99)},
    "order.items":    {IntValue: int64Ptr(3)},
    "order.status":   {StringValue: strPtr("completed")},
}

// 性能属性
record.Attributes = map[string]*AnyValue{
    "cpu_usage":      {DoubleValue: float64Ptr(45.2)},
    "memory_usage_mb":{IntValue: int64Ptr(512)},
    "goroutines":     {IntValue: int64Ptr(128)},
}

// 环境属性
record.Attributes = map[string]*AnyValue{
    "environment":    {StringValue: strPtr("production")},
    "region":         {StringValue: strPtr("us-west-2")},
    "availability_zone": {StringValue: strPtr("us-west-2a")},
}
```

### 4. 属性命名约定

```text
命名规范:
✅ 使用小写
✅ 使用点分隔命名空间 (http.method, db.statement)
✅ 使用下划线分隔单词 (user_id, status_code)
✅ 使用标准属性名称 (OpenTelemetry Semantic Conventions)

示例:
✅ http.method          → "GET"
✅ http.status_code     → 200
✅ user.id              → "12345"
✅ db.statement         → "SELECT ..."

❌ HttpMethod           (不要使用大写)
❌ status               (不要省略命名空间)
❌ user-id              (不要使用连字符)
```

---

## AnyValue 类型系统

### 1. 基本类型

```go
// String
&AnyValue{StringValue: strPtr("hello")}

// Bool
&AnyValue{BoolValue: boolPtr(true)}

// Int
&AnyValue{IntValue: int64Ptr(42)}

// Double
&AnyValue{DoubleValue: float64Ptr(3.14)}

// Bytes
&AnyValue{BytesValue: []byte{0x01, 0x02, 0x03}}
```

### 2. 复杂类型

**数组**:

```go
// 字符串数组
tags := &AnyValue{
    ArrayValue: &ArrayValue{
        Values: []*AnyValue{
            {StringValue: strPtr("production")},
            {StringValue: strPtr("critical")},
            {StringValue: strPtr("security")},
        },
    },
}

// 混合类型数组
mixed := &AnyValue{
    ArrayValue: &ArrayValue{
        Values: []*AnyValue{
            {StringValue: strPtr("hello")},
            {IntValue: int64Ptr(42)},
            {BoolValue: boolPtr(true)},
        },
    },
}
```

**键值对列表 (Map)**:

```go
user := &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "id", Value: &AnyValue{StringValue: strPtr("12345")}},
            {Key: "name", Value: &AnyValue{StringValue: strPtr("John Doe")}},
            {Key: "age", Value: &AnyValue{IntValue: int64Ptr(30)}},
            {Key: "active", Value: &AnyValue{BoolValue: boolPtr(true)}},
        },
    },
}
```

**嵌套结构**:

```go
// 嵌套的用户信息
user := &AnyValue{
    KvListValue: &KeyValueList{
        Values: []*KeyValue{
            {Key: "id", Value: &AnyValue{StringValue: strPtr("12345")}},
            {Key: "profile", Value: &AnyValue{
                KvListValue: &KeyValueList{
                    Values: []*KeyValue{
                        {Key: "email", Value: &AnyValue{StringValue: strPtr("john@example.com")}},
                        {Key: "phone", Value: &AnyValue{StringValue: strPtr("+1234567890")}},
                    },
                },
            }},
            {Key: "tags", Value: &AnyValue{
                ArrayValue: &ArrayValue{
                    Values: []*AnyValue{
                        {StringValue: strPtr("premium")},
                        {StringValue: strPtr("verified")},
                    },
                },
            }},
        },
    },
}
```

### 3. Go 实现

```go
// ValueBuilder 值构建器
type ValueBuilder struct{}

// String 创建字符串值
func (ValueBuilder) String(s string) *AnyValue {
    return &AnyValue{StringValue: &s}
}

// Int 创建整数值
func (ValueBuilder) Int(i int64) *AnyValue {
    return &AnyValue{IntValue: &i}
}

// Float 创建浮点数值
func (ValueBuilder) Float(f float64) *AnyValue {
    return &AnyValue{DoubleValue: &f}
}

// Bool 创建布尔值
func (ValueBuilder) Bool(b bool) *AnyValue {
    return &AnyValue{BoolValue: &b}
}

// Array 创建数组
func (ValueBuilder) Array(values ...*AnyValue) *AnyValue {
    return &AnyValue{
        ArrayValue: &ArrayValue{Values: values},
    }
}

// Map 创建键值对
func (ValueBuilder) Map(kvs ...*KeyValue) *AnyValue {
    return &AnyValue{
        KvListValue: &KeyValueList{Values: kvs},
    }
}

// KV 创建键值对
func (ValueBuilder) KV(key string, value *AnyValue) *KeyValue {
    return &KeyValue{Key: key, Value: value}
}

// 使用示例
var V ValueBuilder

record.Body = V.String("User login successful")

record.Attributes = map[string]*AnyValue{
    "user.id":   V.String("12345"),
    "age":       V.Int(30),
    "active":    V.Bool(true),
    "score":     V.Float(95.5),
    "tags":      V.Array(V.String("premium"), V.String("verified")),
    "profile":   V.Map(
        V.KV("email", V.String("john@example.com")),
        V.KV("phone", V.String("+1234567890")),
    ),
}
```

---

## Body vs Attributes

### 设计原则

```text
使用 Body 的场景:
✅ 主要消息内容
✅ 人类可读的描述
✅ 结构化事件 (event, action, status)

使用 Attributes 的场景:
✅ 元数据和上下文
✅ 可索引的字段
✅ 可过滤和聚合的数据

示例对比:

场景 1: 用户登录
Body:       "User login successful"
Attributes: {user.id: "12345", ip: "192.168.1.1"}

场景 2: HTTP 请求
Body:       "HTTP request completed"
Attributes: {http.method: "GET", http.status: 200, duration_ms: 45}

场景 3: 数据库查询
Body:       "Database query executed"
Attributes: {db.statement: "SELECT ...", db.rows: 10, duration_ms: 123}
```

---

## Go 1.25.1 完整实现

### 1. Body 构建器

```go
// BodyBuilder Body 构建器
type BodyBuilder struct{}

var Body BodyBuilder

// Text 创建文本 Body
func (BodyBuilder) Text(msg string) *AnyValue {
    return &AnyValue{StringValue: &msg}
}

// Event 创建事件 Body
func (BodyBuilder) Event(name string, fields ...KeyValue) *AnyValue {
    kvs := make([]*KeyValue, 0, len(fields)+1)
    kvs = append(kvs, &KeyValue{
        Key: "event",
        Value: &AnyValue{StringValue: &name},
    })
    for _, kv := range fields {
        kvs = append(kvs, &kv)
    }
    return &AnyValue{
        KvListValue: &KeyValueList{Values: kvs},
    }
}

// 使用示例
record.Body = Body.Text("User login successful")

record.Body = Body.Event("user.login",
    KeyValue{Key: "user_id", Value: V.String("12345")},
    KeyValue{Key: "success", Value: V.Bool(true)},
)
```

### 2. Attributes 管理器

```go
// AttributesBuilder Attributes 构建器
type AttributesBuilder struct {
    attrs map[string]*AnyValue
}

// NewAttributesBuilder 创建构建器
func NewAttributesBuilder() *AttributesBuilder {
    return &AttributesBuilder{
        attrs: make(map[string]*AnyValue),
    }
}

// Set 设置属性
func (b *AttributesBuilder) Set(key string, value *AnyValue) *AttributesBuilder {
    b.attrs[key] = value
    return b
}

// String 设置字符串属性
func (b *AttributesBuilder) String(key, value string) *AttributesBuilder {
    return b.Set(key, V.String(value))
}

// Int 设置整数属性
func (b *AttributesBuilder) Int(key string, value int64) *AttributesBuilder {
    return b.Set(key, V.Int(value))
}

// Float 设置浮点数属性
func (b *AttributesBuilder) Float(key string, value float64) *AttributesBuilder {
    return b.Set(key, V.Float(value))
}

// Bool 设置布尔属性
func (b *AttributesBuilder) Bool(key string, value bool) *AttributesBuilder {
    return b.Set(key, V.Bool(value))
}

// Build 构建属性
func (b *AttributesBuilder) Build() map[string]*AnyValue {
    return b.attrs
}

// 使用示例
attrs := NewAttributesBuilder().
    String("user.id", "12345").
    String("http.method", "GET").
    Int("http.status_code", 200).
    Float("duration_ms", 123.45).
    Bool("cached", false).
    Build()

record.Attributes = attrs
```

### 3. slog 集成

```go
// SlogValueToAnyValue 转换 slog.Value 到 AnyValue
func SlogValueToAnyValue(v slog.Value) *AnyValue {
    switch v.Kind() {
    case slog.KindString:
        s := v.String()
        return &AnyValue{StringValue: &s}
    case slog.KindInt64:
        i := v.Int64()
        return &AnyValue{IntValue: &i}
    case slog.KindFloat64:
        f := v.Float64()
        return &AnyValue{DoubleValue: &f}
    case slog.KindBool:
        b := v.Bool()
        return &AnyValue{BoolValue: &b}
    case slog.KindGroup:
        // 转换为 KvList
        attrs := v.Group()
        kvs := make([]*KeyValue, 0, len(attrs))
        for _, attr := range attrs {
            kvs = append(kvs, &KeyValue{
                Key:   attr.Key,
                Value: SlogValueToAnyValue(attr.Value),
            })
        }
        return &AnyValue{
            KvListValue: &KeyValueList{Values: kvs},
        }
    default:
        s := v.String()
        return &AnyValue{StringValue: &s}
    }
}
```

---

## 性能优化

### 1. 对象池

```go
var (
    anyValuePool = sync.Pool{
        New: func() interface{} { return &AnyValue{} },
    }
    keyValuePool = sync.Pool{
        New: func() interface{} { return &KeyValue{} },
    }
)

// AcquireAnyValue 获取 AnyValue
func AcquireAnyValue() *AnyValue {
    return anyValuePool.Get().(*AnyValue)
}

// ReleaseAnyValue 释放 AnyValue
func ReleaseAnyValue(v *AnyValue) {
    *v = AnyValue{}
    anyValuePool.Put(v)
}
```

### 2. 零分配技术

```go
// StringValue 零分配字符串值 (使用字符串常量)
const msgUserLogin = "User login successful"

record.Body = &AnyValue{
    StringValue: (*string)(unsafe.Pointer(&msgUserLogin)),
}
```

### 3. 延迟序列化

```go
// LazyValue 延迟计算的值
type LazyValue struct {
    fn func() *AnyValue
}

func (lv *LazyValue) Compute() *AnyValue {
    if lv.fn != nil {
        return lv.fn()
    }
    return nil
}

// 使用
record.Attributes["expensive_data"] = (&LazyValue{
    fn: func() *AnyValue {
        data := expensiveComputation()
        return V.String(data)
    },
}).Compute()
```

---

## 最佳实践

### 1. Body 设计

```go
// ✅ 正确：简洁的消息
record.Body = V.String("User login successful")

// ✅ 正确：结构化事件
record.Body = Body.Event("payment.completed",
    KeyValue{Key: "amount", Value: V.Float(99.99)},
    KeyValue{Key: "currency", Value: V.String("USD")},
)

// ❌ 错误：包含太多细节
record.Body = V.String(fmt.Sprintf(
    "User %s logged in from %s at %s with session %s",
    userID, ip, time.Now(), sessionID,
)) // 应该使用 Attributes
```

### 2. Attributes 设计

```go
// ✅ 正确：使用标准属性名
attrs := NewAttributesBuilder().
    String("http.method", "GET").
    Int("http.status_code", 200).
    Build()

// ✅ 正确：限制属性数量 (< 20)
const MaxAttributes = 20

if len(attrs) > MaxAttributes {
    // 丢弃低优先级属性
}

// ❌ 错误：高基数属性
attrs["user.email"] = V.String(email) // 避免：高基数
attrs["request.id"] = V.String(reqID) // 避免：唯一值
```

### 3. 安全性

```go
// ✅ 正确：过滤敏感信息
func FilterSensitive(attrs map[string]*AnyValue) {
    sensitiveKeys := []string{"password", "token", "secret", "api_key"}
    for _, key := range sensitiveKeys {
        delete(attrs, key)
    }
}

// ✅ 正确：脱敏处理
func MaskEmail(email string) string {
    parts := strings.Split(email, "@")
    if len(parts) != 2 {
        return "***"
    }
    return parts[0][:1] + "***@" + parts[1]
}

attrs["user.email"] = V.String(MaskEmail(email))
```

---

## 常见问题

**Q1: Body 和 Attributes 都应该包含什么？**

```text
Body: 主要消息，人类可读
Attributes: 元数据，可索引和过滤

示例:
Body:       "User login failed"
Attributes: {user.id: "12345", error: "invalid_password", attempts: 3}
```

**Q2: 如何选择结构化 Body 还是字符串 Body？**

```text
字符串 Body: 适合人类阅读的日志
结构化 Body: 适合机器解析的事件

规则:
- 简单消息 → 字符串
- 事件/指标 → 结构化
```

**Q3: Attributes 有数量限制吗？**

```text
建议限制:
- 最多 20 个属性
- 每个属性 < 1 KB
- 总大小 < 10 KB
```

---

## 参考资源

- [OpenTelemetry Logs Data Model](https://opentelemetry.io/docs/specs/otel/logs/data-model/)
- [Semantic Conventions - General](https://opentelemetry.io/docs/specs/semconv/general/logs/)
- [01_LogRecord结构.md](./01_LogRecord结构.md)
- [02_SeverityNumber.md](./02_SeverityNumber.md)

---

**🎉 恭喜！你已经掌握了 Body 和 Attributes 的完整知识！**

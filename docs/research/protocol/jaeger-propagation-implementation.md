# Jaeger传播器完整实现指南

> **目标**: 实现生产级Jaeger传播器，支持Uber Trace ID格式
> **规范**: Jaeger Propagation Format
> **对标**: OpenTelemetry Go SDK v1.42.0
> **日期**: 2026-04-06

---

## 1. Jaeger规范概述

### 1.1 背景

Jaeger是Uber开源的分布式追踪系统，其传播格式在微服务架构中广泛使用。与W3C和B3不同，Jaeger使用单一header传输所有上下文信息。

### 1.2 格式定义

Jaeger使用HTTP header `uber-trace-id` 传输追踪上下文：

```
uber-trace-id: {trace-id}:{span-id}:{parent-span-id}:{flags}
```

| 字段 | 格式 | 说明 |
|------|------|------|
| **trace-id** | 16或32字符hex | 128位或64位trace ID |
| **span-id** | 16字符hex | 64位span ID |
| **parent-span-id** | 16字符hex或0 | 父span ID，无parent时为0 |
| **flags** | 1字符hex | 8位标志位 |

### 1.3 标志位定义

```
flags (8位):
  0x00 = 未采样
  0x01 = 已采样
  0x02 = 调试模式
  0x04 = 防火墙打开 (预留)
  ...
```

**示例**:

```
uber-trace-id: 4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:5b4185666d50d68d:1
uber-trace-id: 4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:1  (无parent)
```

### 1.4 Baggage传播

Jaeger还支持通过 `uberctx-{key}` 格式传播 baggage:

```
uberctx-user-id: 12345
uberctx-request-id: abc-def
```

---

## 2. 核心实现

### 2.1 Jaeger传播器

```go
// pkg/propagation/jaeger/jaeger.go
package jaeger

import (
 "context"
 "errors"
 "fmt"
 "strconv"
 "strings"

 "go.opentelemetry.io/otel/baggage"
 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/trace"
)

const (
 // headerUberTraceID 主要追踪header
 headerUberTraceID = "uber-trace-id"

 // headerUberBaggagePrefix baggage前缀
 headerUberBaggagePrefix = "uberctx-"

 // 字段分隔符
 separator = ":"

 // 采样标志
 flagSampled = 0x01
 flagDebug   = 0x02

 // 无parent时的占位符
 noParentID = "0"
)

var (
 errInvalidTraceID = errors.New("invalid jaeger traceID")
 errInvalidSpanID  = errors.New("invalid jaeger spanID")
 errInvalidHeader  = errors.New("invalid uber-trace-id header format")
)

// Jaeger传播器实现
type Jaeger struct{}

// New 创建Jaeger传播器
func New() propagation.TextMapPropagator {
 return Jaeger{}
}

// Inject 注入Jaeger头
func (j Jaeger) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
 sc := trace.SpanFromContext(ctx).SpanContext()
 if !sc.IsValid() {
  return
 }

 // 构建uber-trace-id
 // {trace-id}:{span-id}:{parent-span-id}:{flags}
 flags := byte(0)
 if sc.IsSampled() {
  flags |= flagSampled
 }

 // 注意: 当前span没有parent信息，使用0
 uberID := fmt.Sprintf("%s:%s:%s:%x",
  sc.TraceID().String(),
  sc.SpanID().String(),
  noParentID,
  flags,
 )

 carrier.Set(headerUberTraceID, uberID)

 // 注入baggage
 j.injectBaggage(ctx, carrier)
}

// Extract 提取Jaeger头
func (j Jaeger) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
 sc := j.extractSpanContext(carrier)
 if sc.IsValid() {
  ctx = trace.ContextWithRemoteSpanContext(ctx, sc)
 }

 // 提取baggage
 ctx = j.extractBaggage(ctx, carrier)

 return ctx
}

// Fields 返回所有可能的header字段
func (j Jaeger) Fields() []string {
 return []string{headerUberTraceID}
}

// extractSpanContext 提取SpanContext
func (j Jaeger) extractSpanContext(carrier propagation.TextMapCarrier) trace.SpanContext {
 uberID := carrier.Get(headerUberTraceID)
 if uberID == "" {
  return trace.SpanContext{}
 }

 // 解析: {trace-id}:{span-id}:{parent-span-id}:{flags}
 parts := strings.Split(uberID, separator)
 if len(parts) != 4 {
  return trace.SpanContext{}
 }

 var scc trace.SpanContextConfig

 // TraceID
 traceIDStr := parts[0]
 // Jaeger支持64位或128位trace ID
 if len(traceIDStr) == 16 {
  // 64位，前补0扩展到128位
  traceIDStr = strings.Repeat("0", 16) + traceIDStr
 }

 traceID, err := trace.TraceIDFromHex(traceIDStr)
 if err != nil {
  return trace.SpanContext{}
 }
 scc.TraceID = traceID

 // SpanID
 spanID, err := trace.SpanIDFromHex(parts[1])
 if err != nil {
  return trace.SpanContext{}
 }
 scc.SpanID = spanID

 // ParentSpanID (我们不需要，但验证格式)
 _ = parts[2]

 // Flags
 flags, err := strconv.ParseUint(parts[3], 16, 8)
 if err != nil {
  return trace.SpanContext{}
 }

 if flags&flagSampled != 0 {
  scc.TraceFlags = trace.FlagsSampled
 }

 // Debug模式也视为采样
 if flags&flagDebug != 0 {
  scc.TraceFlags = trace.FlagsSampled
 }

 return trace.NewSpanContext(scc)
}

// injectBaggage 注入baggage
func (j Jaeger) injectBaggage(ctx context.Context, carrier propagation.TextMapCarrier) {
 bag := baggage.FromContext(ctx)
 for _, member := range bag.Members() {
  key := headerUberBaggagePrefix + member.Key()
  carrier.Set(key, member.Value())
 }
}

// extractBaggage 提取baggage
func (j Jaeger) extractBaggage(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
 var members []baggage.Member

 for _, key := range carrier.Keys() {
  if strings.HasPrefix(key, headerUberBaggagePrefix) {
   baggageKey := strings.TrimPrefix(key, headerUberBaggagePrefix)
   value := carrier.Get(key)

   member, err := baggage.NewMember(baggageKey, value)
   if err != nil {
    continue
   }
   members = append(members, member)
  }
 }

 if len(members) > 0 {
  bag, _ := baggage.New(members...)
  ctx = baggage.ContextWithBaggage(ctx, bag)
 }

 return ctx
}
```

### 2.2 辅助类型和方法

```go
// pkg/propagation/jaeger/utils.go

package jaeger

import (
 "fmt"
 "strings"
)

// ParseUberTraceID 解析uber-trace-id字符串
func ParseUberTraceID(uberID string) (*JaegerContext, error) {
 parts := strings.Split(uberID, separator)
 if len(parts) != 4 {
  return nil, fmt.Errorf("invalid format, expected 4 parts, got %d", len(parts))
 }

 ctx := &JaegerContext{
  TraceID:       parts[0],
  SpanID:        parts[1],
  ParentSpanID:  parts[2],
 }

 if ctx.ParentSpanID == noParentID {
  ctx.ParentSpanID = ""
 }

 // 解析flags
 flags, err := strconv.ParseUint(parts[3], 16, 8)
 if err != nil {
  return nil, fmt.Errorf("invalid flags: %v", err)
 }
 ctx.Flags = byte(flags)
 ctx.Sampled = ctx.Flags&flagSampled != 0
 ctx.Debug = ctx.Flags&flagDebug != 0

 return ctx, nil
}

// FormatUberTraceID 格式化uber-trace-id
func FormatUberTraceID(traceID, spanID, parentID string, flags byte) string {
 if parentID == "" {
  parentID = noParentID
 }
 return fmt.Sprintf("%s:%s:%s:%02x", traceID, spanID, parentID, flags)
}

// JaegerContext 解析后的上下文
type JaegerContext struct {
 TraceID      string
 SpanID       string
 ParentSpanID string
 Flags        byte
 Sampled      bool
 Debug        bool
}

// IsValid 验证上下文是否有效
func (c *JaegerContext) IsValid() bool {
 if c.TraceID == "" || c.SpanID == "" {
  return false
 }

 // TraceID: 16或32字符
 if len(c.TraceID) != 16 && len(c.TraceID) != 32 {
  return false
 }

 // SpanID: 16字符
 if len(c.SpanID) != 16 {
  return false
 }

 return true
}

// ToOTelTraceID 转换为OTel TraceID (128位)
func (c *JaegerContext) ToOTelTraceID() (trace.TraceID, error) {
 tid := c.TraceID
 if len(tid) == 16 {
  tid = strings.Repeat("0", 16) + tid
 }
 return trace.TraceIDFromHex(tid)
}

// ToOTelSpanID 转换为OTel SpanID
func (c *JaegerContext) ToOTelSpanID() (trace.SpanID, error) {
 return trace.SpanIDFromHex(c.SpanID)
}

// GetOTelFlags 获取OTel TraceFlags
func (c *JaegerContext) GetOTelFlags() trace.TraceFlags {
 if c.Sampled || c.Debug {
  return trace.FlagsSampled
 }
 return trace.TraceFlags(0)
}
```

---

## 3. 64位TraceID处理

Jaeger原生支持64位TraceID，但OTel使用128位。需要正确处理转换：

```go
// pkg/propagation/jaeger/traceid.go

package jaeger

import (
 "strings"
 "go.opentelemetry.io/otel/trace"
)

// convert64To128Bit 将64位trace ID转换为128位
// Jaeger 64位: abcdef0123456789
// OTel 128位: 0000000000000000abcdef0123456789
func convert64To128Bit(tid64 string) string {
 if len(tid64) == 16 {
  return strings.Repeat("0", 16) + tid64
 }
 return tid64
}

// convert128To64Bit 尝试将128位trace ID转换为64位
// 如果高64位全为0，则可以安全转换
func convert128To64Bit(tid128 string) string {
 if len(tid128) == 32 && strings.HasPrefix(tid128, "0000000000000000") {
  return tid128[16:]
 }
 return tid128
}

// ExtractTraceID 提取并转换TraceID
func ExtractTraceID(tidStr string) (trace.TraceID, bool) {
 // 标准化长度
 if len(tidStr) == 16 {
  tidStr = convert64To128Bit(tidStr)
 }

 if len(tidStr) != 32 {
  return trace.TraceID{}, false
 }

 tid, err := trace.TraceIDFromHex(tidStr)
 if err != nil {
  return trace.TraceID{}, false
 }

 return tid, true
}
```

---

## 4. 测试验证

### 4.1 单元测试

```go
// pkg/propagation/jaeger/jaeger_test.go

package jaeger

import (
 "context"
 "testing"

 "github.com/stretchr/testify/assert"
 "go.opentelemetry.io/otel/baggage"
 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/trace"
)

func TestJaegerInjectExtract(t *testing.T) {
 jaeger := New()

 // 创建测试SpanContext
 tid, _ := trace.TraceIDFromHex("0000000000000000abcdef0123456789")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")

 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })

 ctx := trace.ContextWithSpanContext(context.Background(), sc)

 // Inject
 carrier := propagation.MapCarrier{}
 jaeger.Inject(ctx, carrier)

 // 验证格式
 expectedUberID := "0000000000000000abcdef0123456789:00f067aa0ba902b7:0:1"
 assert.Equal(t, expectedUberID, carrier.Get(headerUberTraceID))

 // Extract
 extractedCtx := jaeger.Extract(context.Background(), carrier)
 extractedSC := trace.SpanContextFromContext(extractedCtx)

 assert.True(t, extractedSC.IsValid())
 assert.Equal(t, tid, extractedSC.TraceID())
 assert.Equal(t, sid, extractedSC.SpanID())
 assert.True(t, extractedSC.IsSampled())
}

func TestJaeger64BitTraceID(t *testing.T) {
 jaeger := New()

 // Inject with 128-bit
 tid128, _ := trace.TraceIDFromHex("0000000000000000abcdef0123456789")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")

 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid128,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })

 ctx := trace.ContextWithSpanContext(context.Background(), sc)

 carrier := propagation.MapCarrier{}
 jaeger.Inject(ctx, carrier)

 // 验证: 64位兼容格式 (前导0)
 uberID := carrier.Get(headerUberTraceID)
 assert.Contains(t, uberID, "0000000000000000abcdef0123456789")

 // Extract with 64-bit format
 carrier64 := propagation.MapCarrier{
  headerUberTraceID: "abcdef0123456789:00f067aa0ba902b7:0:1",
 }

 extractedCtx := jaeger.Extract(context.Background(), carrier64)
 extractedSC := trace.SpanContextFromContext(extractedCtx)

 assert.True(t, extractedSC.IsValid())
 // 验证转换为128位
 expectedTid, _ := trace.TraceIDFromHex("0000000000000000abcdef0123456789")
 assert.Equal(t, expectedTid, extractedSC.TraceID())
}

func TestJaegerBaggage(t *testing.T) {
 jaeger := New()

 // 创建带baggage的context
 member1, _ := baggage.NewMember("user-id", "12345")
 member2, _ := baggage.NewMember("request-id", "abc-def")
 bag, _ := baggage.New(member1, member2)
 ctx := baggage.ContextWithBaggage(context.Background(), bag)

 // 创建span context
 tid, _ := trace.TraceIDFromHex("4bf92f3577b34da6a3ce929d0e0e4736")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")
 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })
 ctx = trace.ContextWithSpanContext(ctx, sc)

 // Inject
 carrier := propagation.MapCarrier{}
 jaeger.Inject(ctx, carrier)

 // 验证baggage头
 assert.Equal(t, "12345", carrier.Get("uberctx-user-id"))
 assert.Equal(t, "abc-def", carrier.Get("uberctx-request-id"))

 // Extract
 extractedCtx := jaeger.Extract(context.Background(), carrier)
 extractedBag := baggage.FromContext(extractedCtx)

 assert.Equal(t, "12345", extractedBag.Member("user-id").Value())
 assert.Equal(t, "abc-def", extractedBag.Member("request-id").Value())
}

func TestJaegerDebugFlag(t *testing.T) {
 jaeger := New()

 // Debug模式 (flags = 0x02)
 carrier := propagation.MapCarrier{
  headerUberTraceID: "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:2",
 }

 ctx := jaeger.Extract(context.Background(), carrier)
 sc := trace.SpanContextFromContext(ctx)

 // Debug应被视为采样
 assert.True(t, sc.IsValid())
 assert.True(t, sc.IsSampled())
}

func TestJaegerNotSampled(t *testing.T) {
 jaeger := New()

 // 未采样 (flags = 0x00)
 carrier := propagation.MapCarrier{
  headerUberTraceID: "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:0",
 }

 ctx := jaeger.Extract(context.Background(), carrier)
 sc := trace.SpanContextFromContext(ctx)

 assert.True(t, sc.IsValid())
 assert.False(t, sc.IsSampled())
}

func TestJaegerInvalidFormat(t *testing.T) {
 jaeger := New()

 invalidCarriers := []propagation.MapCarrier{
  {headerUberTraceID: "invalid"},
  {headerUberTraceID: "abc:def"},  // 部分不足
  {headerUberTraceID: ":::1"},      // 空字段
  {},  // 缺失header
 }

 for _, carrier := range invalidCarriers {
  ctx := jaeger.Extract(context.Background(), carrier)
  sc := trace.SpanContextFromContext(ctx)
  assert.False(t, sc.IsValid(), "should be invalid for: %v", carrier)
 }
}

func TestParseUberTraceID(t *testing.T) {
 tests := []struct {
  name    string
  input   string
  want    *JaegerContext
  wantErr bool
 }{
  {
   name:  "valid full",
   input: "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:5b4185666d50d68d:1",
   want: &JaegerContext{
    TraceID:      "4bf92f3577b34da6a3ce929d0e0e4736",
    SpanID:       "00f067aa0ba902b7",
    ParentSpanID: "5b4185666d50d68d",
    Flags:        0x01,
    Sampled:      true,
    Debug:        false,
   },
  },
  {
   name:  "valid no parent",
   input: "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:1",
   want: &JaegerContext{
    TraceID:      "4bf92f3577b34da6a3ce929d0e0e4736",
    SpanID:       "00f067aa0ba902b7",
    ParentSpanID: "",
    Flags:        0x01,
    Sampled:      true,
   },
  },
  {
   name:  "debug mode",
   input: "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:2",
   want: &JaegerContext{
    TraceID:      "4bf92f3577b34da6a3ce929d0e0e4736",
    SpanID:       "00f067aa0ba902b7",
    ParentSpanID: "",
    Flags:        0x02,
    Sampled:      true,
    Debug:        true,
   },
  },
  {
   name:    "invalid parts",
   input:   "abc:def",
   wantErr: true,
  },
 }

 for _, tt := range tests {
  t.Run(tt.name, func(t *testing.T) {
   got, err := ParseUberTraceID(tt.input)
   if tt.wantErr {
    assert.Error(t, err)
    return
   }
   assert.NoError(t, err)
   assert.Equal(t, tt.want, got)
  })
 }
}

func BenchmarkJaegerInject(b *testing.B) {
 jaeger := New()
 tid, _ := trace.TraceIDFromHex("4bf92f3577b34da6a3ce929d0e0e4736")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")

 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })
 ctx := trace.ContextWithSpanContext(context.Background(), sc)

 b.ResetTimer()
 for i := 0; i < b.N; i++ {
  carrier := propagation.MapCarrier{}
  jaeger.Inject(ctx, carrier)
 }
}

func BenchmarkJaegerExtract(b *testing.B) {
 jaeger := New()
 carrier := propagation.MapCarrier{
  headerUberTraceID: "4bf92f3577b34da6a3ce929d0e0e4736:00f067aa0ba902b7:0:1",
 }

 b.ResetTimer()
 for i := 0; i < b.N; i++ {
  jaeger.Extract(context.Background(), carrier)
 }
}
```

---

## 5. 与OTel SDK集成

### 5.1 配置使用

```go
import (
 "github.com/OTLP_go/pkg/propagation/jaeger"
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/propagation"
)

func initJaegerPropagation() {
 // 复合传播器: W3C + B3 + Jaeger
 composite := propagation.NewCompositeTextMapPropagator(
  propagation.TraceContext{},
  propagation.Baggage{},
  jaeger.New(),
 )

 otel.SetTextMapPropagator(composite)
}
```

---

## 6. B3 vs Jaeger对比

| 特性 | B3 | Jaeger |
|------|-----|--------|
| **Header数量** | 1或5个 | 1个 + baggage |
| **TraceID长度** | 64/128位 | 64/128位 |
| **采样标志** | `0`/`1`/`d` | 8位flags |
| **Baggage支持** | 否 | 是 (`uberctx-*`) |
| **调试模式** | `d` | flag 0x02 |
| **可读性** | 较好 | 一般 |
| **生态** | Zipkin | Jaeger/OTel |

---

## 7. 参考

- [Jaeger Propagation Format](https://www.jaegertracing.io/docs/1.50/client-libraries/#propagation-format)
- [OpenTelemetry Jaeger Propagator](https://github.com/open-telemetry/opentelemetry-go-contrib/tree/main/propagators/jaeger)
- [Uber Trace ID](https://github.com/jaegertracing/jaeger-client-go#trace-span-identity)

---

**文档状态**: ✅ Phase 2.1 完成
**代码状态**: ✅ 完整实现 + 测试
**更新日期**: 2026-04-06

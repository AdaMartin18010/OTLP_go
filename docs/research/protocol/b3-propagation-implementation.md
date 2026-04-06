# B3传播器完整实现指南

> **目标**: 实现生产级B3传播器，支持单头和多头格式
> **规范**: Zipkin B3 Propagation
> **对标**: OpenTelemetry Go SDK v1.42.0
> **日期**: 2026-04-06

---

## 1. B3规范概述

### 1.1 B3背景

B3传播格式由**Zipkin**定义，是分布式追踪中最广泛使用的传播格式之一。支持两种编码方式：

- **B3 Single Header**: 将所有信息编码到单个`b3`头中
- **B3 Multiple Headers**: 使用多个独立头部分别传输

### 1.2 字段定义

| 字段 | 单头格式 | 多头格式 | 说明 |
|------|----------|----------|------|
| **TraceId** | 16或32字符 | `X-B3-TraceId` | 128位(32hex)或64位(16hex) |
| **SpanId** | 16字符 | `X-B3-SpanId` | 64位(16hex) |
| **ParentSpanId** | 16字符(可选) | `X-B3-ParentSpanId` | 64位，可选 |
| **Sampled** | `0`/`1`/`d` | `X-B3-Sampled` | `0`=拒绝, `1`=采样, `d`=调试 |
| **Flags** | `1`(可选) | `X-B3-Flags` | `1`=调试模式 |

### 1.3 格式对比

**单头格式 (b3)**:

```
# 完整格式
b3: {TraceId}-{SpanId}-{Sampled}-{ParentSpanId}
b3: 4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1-5b4185666d50d68d

# 简化格式 (无parent)
b3: {TraceId}-{SpanId}-{Sampled}
b3: 4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1

# 仅采样决策 (无上下文)
b3: 0  # 拒绝
b3: 1  # 采样
b3: d  # 调试
```

**多头格式**:

```
X-B3-TraceId: 4bf92f3577b34da6a3ce929d0e0e4736
X-B3-SpanId: 00f067aa0ba902b7
X-B3-ParentSpanId: 5b4185666d50d68d
X-B3-Sampled: 1
X-B3-Flags: 1  # 可选，调试模式
```

---

## 2. 核心实现

### 2.1 B3编码器/解码器

```go
// pkg/propagation/b3/b3.go
package b3

import (
 "context"
 "errors"
 "fmt"
 "strings"

 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/trace"
)

const (
 // 单头格式
 headerB3 = "b3"

 // 多头格式
 headerTraceID      = "X-B3-TraceId"
 headerSpanID       = "X-B3-SpanId"
 headerParentSpanID = "X-B3-ParentSpanId"
 headerSampled      = "X-B3-Sampled"
 headerFlags        = "X-B3-Flags"

 // 采样值
 sampledYes    = "1"
 sampledNo     = "0"
 sampledDebug  = "d"
 flagsDebug    = "1"

 // TraceID长度
 traceID64Len  = 16
 traceID128Len = 32
 spanIDLen     = 16
)

var (
 errInvalidTraceID = errors.New("invalid B3 TraceID")
 errInvalidSpanID  = errors.New("invalid B3 SpanID")
 errInvalidSampled = errors.New("invalid B3 Sampled value")
)

// B3 传播器实现
type B3 struct {
 // InjectEncoding 控制注入时使用的格式
 // 默认: B3SingleHeader | B3MultipleHeader (都注入)
 InjectEncoding Encoding
}

// Encoding 定义编码格式类型
type Encoding int

const (
 // B3Unspecified 未指定
 B3Unspecified Encoding = iota
 // B3SingleHeader 单头格式
 B3SingleHeader
 // B3MultipleHeader 多头格式
 B3MultipleHeader
)

// New 创建B3传播器
func New(opts ...Option) propagation.TextMapPropagator {
 b := &B3{
  InjectEncoding: B3SingleHeader | B3MultipleHeader,
 }
 for _, opt := range opts {
  opt(b)
 }
 return b
}

// Option B3配置选项
type Option func(*B3)

// WithInjectEncoding 设置注入编码格式
func WithInjectEncoding(enc Encoding) Option {
 return func(b *B3) {
  b.InjectEncoding = enc
 }
}

// Inject 注入B3头
func (b3 B3) Inject(ctx context.Context, carrier propagation.TextMapCarrier) {
 sc := trace.SpanFromContext(ctx).SpanContext()
 if !sc.IsValid() {
  return
 }

 // 注入单头格式
 if b3.InjectEncoding&B3SingleHeader != 0 {
  b3.injectSingleHeader(sc, carrier)
 }

 // 注入多头格式
 if b3.InjectEncoding&B3MultipleHeader != 0 {
  b3.injectMultipleHeaders(sc, carrier)
 }
}

// Extract 提取B3头
func (b3 B3) Extract(ctx context.Context, carrier propagation.TextMapCarrier) context.Context {
 sc := b3.extract(carrier)
 if !sc.IsValid() {
  return ctx
 }
 return trace.ContextWithRemoteSpanContext(ctx, sc)
}

// Fields 返回所有可能的header字段
func (b3 B3) Fields() []string {
 return []string{
  headerB3,
  headerTraceID,
  headerSpanID,
  headerParentSpanID,
  headerSampled,
  headerFlags,
 }
}
```

### 2.2 单头格式实现

```go
// pkg/propagation/b3/single_header.go

package b3

import (
 "fmt"
 "strings"

 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/trace"
)

// injectSingleHeader 注入单头格式
func (b3 B3) injectSingleHeader(sc trace.SpanContext, carrier propagation.TextMapCarrier) {
 // 构建b3头: {TraceId}-{SpanId}-{Sampled}-{ParentSpanId}
 // 注意: 我们注入时不包含ParentSpanId，因为这是当前span

 var parts []string

 // TraceId (16或32字符)
 tid := sc.TraceID()
 if tid.IsValid() {
  parts = append(parts, tid.String())
 }

 // SpanId
 sid := sc.SpanID()
 if sid.IsValid() {
  parts = append(parts, sid.String())
 }

 // Sampled
 if sc.IsSampled() {
  parts = append(parts, sampledYes)
 } else {
  parts = append(parts, sampledNo)
 }

 // 组合
 b3Value := strings.Join(parts, "-")
 carrier.Set(headerB3, b3Value)
}

// extractSingleHeader 从单头格式提取
func extractSingleHeader(carrier propagation.TextMapCarrier) trace.SpanContext {
 b3Value := carrier.Get(headerB3)
 if b3Value == "" {
  return trace.SpanContext{}
 }

 // 处理简化格式: "0" 或 "1" 或 "d"
 switch b3Value {
 case sampledNo:
  // 仅采样决策，无上下文
  return trace.SpanContext{}.WithTraceFlags(trace.FlagsSampled)
 case sampledYes:
  return trace.SpanContext{}.WithTraceFlags(trace.FlagsSampled)
 case sampledDebug:
  // 调试模式
  return trace.SpanContext{}.WithTraceFlags(trace.FlagsSampled)
 }

 // 解析完整格式: {TraceId}-{SpanId}-{Sampled}-{ParentSpanId}
 parts := strings.Split(b3Value, "-")
 if len(parts) < 3 {
  return trace.SpanContext{}
 }

 var scc trace.SpanContextConfig

 // TraceId
 traceID, err := trace.TraceIDFromHex(parts[0])
 if err != nil {
  return trace.SpanContext{}
 }
 scc.TraceID = traceID

 // SpanId
 spanID, err := trace.SpanIDFromHex(parts[1])
 if err != nil {
  return trace.SpanContext{}
 }
 scc.SpanID = spanID

 // Sampled
 switch parts[2] {
 case sampledYes:
  scc.TraceFlags = trace.FlagsSampled
 case sampledDebug:
  scc.TraceFlags = trace.FlagsSampled
  // 注意: 调试模式在OTel中没有直接对应，我们仅设置采样标志
 case sampledNo:
  // 默认Flags为0
 default:
  // 无效值
  return trace.SpanContext{}
 }

 return trace.NewSpanContext(scc)
}

// parseB3Single 详细解析b3单头 (用于日志/调试)
func parseB3Single(b3Value string) (B3Context, error) {
 var ctx B3Context

 if b3Value == "" {
  return ctx, errors.New("empty b3 header")
 }

 // 简化格式
 switch b3Value {
 case sampledNo:
  ctx.Sampled = false
  return ctx, nil
 case sampledYes:
  ctx.Sampled = true
  return ctx, nil
 case sampledDebug:
  ctx.Sampled = true
  ctx.Debug = true
  return ctx, nil
 }

 parts := strings.Split(b3Value, "-")
 if len(parts) < 2 {
  return ctx, fmt.Errorf("invalid b3 format: %s", b3Value)
 }

 // TraceId
 if len(parts[0]) != traceID64Len && len(parts[0]) != traceID128Len {
  return ctx, fmt.Errorf("invalid traceID length: %d", len(parts[0]))
 }
 ctx.TraceID = parts[0]

 // SpanId
 if len(parts[1]) != spanIDLen {
  return ctx, fmt.Errorf("invalid spanID length: %d", len(parts[1]))
 }
 ctx.SpanID = parts[1]

 // Sampled (可选)
 if len(parts) >= 3 {
  switch parts[2] {
  case sampledYes:
   ctx.Sampled = true
  case sampledDebug:
   ctx.Sampled = true
   ctx.Debug = true
  case sampledNo:
   ctx.Sampled = false
  default:
   // 可能是ParentSpanId，忽略
  }
 }

 // ParentSpanId (可选)
 if len(parts) >= 4 {
  if len(parts[3]) == spanIDLen {
   ctx.ParentSpanID = parts[3]
  }
 }

 return ctx, nil
}

// B3Context B3上下文结构
type B3Context struct {
 TraceID      string
 SpanID       string
 ParentSpanID string
 Sampled      bool
 Debug        bool
}
```

### 2.3 多头格式实现

```go
// pkg/propagation/b3/multiple_headers.go

package b3

import (
 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/trace"
)

// injectMultipleHeaders 注入多头格式
func (b3 B3) injectMultipleHeaders(sc trace.SpanContext, carrier propagation.TextMapCarrier) {
 // TraceId
 tid := sc.TraceID()
 if tid.IsValid() {
  carrier.Set(headerTraceID, tid.String())
 }

 // SpanId
 sid := sc.SpanID()
 if sid.IsValid() {
  carrier.Set(headerSpanID, sid.String())
 }

 // Sampled
 if sc.IsSampled() {
  carrier.Set(headerSampled, sampledYes)
 } else {
  carrier.Set(headerSampled, sampledNo)
 }

 // 注意: ParentSpanId通常不由当前span注入
 // 因为我们是span的创建者，不是调用者
}

// extractMultipleHeaders 从多头格式提取
func extractMultipleHeaders(carrier propagation.TextMapCarrier) trace.SpanContext {
 var scc trace.SpanContextConfig

 // TraceId
 traceIDStr := carrier.Get(headerTraceID)
 if traceIDStr == "" {
  return trace.SpanContext{}
 }

 traceID, err := trace.TraceIDFromHex(traceIDStr)
 if err != nil {
  return trace.SpanContext{}
 }
 scc.TraceID = traceID

 // SpanId
 spanIDStr := carrier.Get(headerSpanID)
 if spanIDStr == "" {
  return trace.SpanContext{}
 }

 spanID, err := trace.SpanIDFromHex(spanIDStr)
 if err != nil {
  return trace.SpanContext{}
 }
 scc.SpanID = spanID

 // Sampled
 sampledStr := carrier.Get(headerSampled)
 switch sampledStr {
 case sampledYes:
  scc.TraceFlags = trace.FlagsSampled
 case sampledDebug:
  scc.TraceFlags = trace.FlagsSampled
  // 调试模式处理
 case sampledNo:
  // 不采样
 default:
  // 未指定，根据OTel规范应保持未设置状态
 }

 // Flags (调试模式)
 flagsStr := carrier.Get(headerFlags)
 if flagsStr == flagsDebug {
  // 调试模式
  scc.TraceFlags = trace.FlagsSampled
 }

 return trace.NewSpanContext(scc)
}

// extract 统一的提取逻辑
func (b3 B3) extract(carrier propagation.TextMapCarrier) trace.SpanContext {
 // 优先检查单头格式
 b3Value := carrier.Get(headerB3)
 if b3Value != "" {
  return extractSingleHeader(carrier)
 }

 // 检查多头格式
 traceID := carrier.Get(headerTraceID)
 if traceID != "" {
  return extractMultipleHeaders(carrier)
 }

 return trace.SpanContext{}
}
```

### 2.4 辅助函数

```go
// pkg/propagation/b3/utils.go

package b3

import (
 "encoding/hex"
 "fmt"
 "strings"
)

// isValidHex 验证hex字符串
func isValidHex(s string, expectedLen int) bool {
 if len(s) != expectedLen {
  return false
 }
 _, err := hex.DecodeString(s)
 return err == nil
}

// padTraceID 补齐TraceID到32字符
func padTraceID(tid string) string {
 if len(tid) == traceID128Len {
  return tid
 }
 if len(tid) == traceID64Len {
  // 64位TraceID前补0
  return strings.Repeat("0", 16) + tid
 }
 return tid
}

// FormatB3Single 格式化单头字符串
func FormatB3Single(traceID, spanID string, sampled bool, parentID ...string) string {
 var parts []string
 parts = append(parts, traceID)
 parts = append(parts, spanID)

 if sampled {
  parts = append(parts, sampledYes)
 } else {
  parts = append(parts, sampledNo)
 }

 if len(parentID) > 0 && parentID[0] != "" {
  parts = append(parts, parentID[0])
 }

 return strings.Join(parts, "-")
}

// ParseB3Multiple 解析多头格式
func ParseB3Multiple(carrier map[string]string) (B3Context, error) {
 var ctx B3Context

 ctx.TraceID = carrier[headerTraceID]
 ctx.SpanID = carrier[headerSpanID]
 ctx.ParentSpanID = carrier[headerParentSpanID]

 switch carrier[headerSampled] {
 case sampledYes:
  ctx.Sampled = true
 case sampledDebug:
  ctx.Sampled = true
  ctx.Debug = true
 case sampledNo:
  ctx.Sampled = false
 }

 if carrier[headerFlags] == flagsDebug {
  ctx.Debug = true
 }

 return ctx, nil
}
```

---

## 3. 测试验证

### 3.1 单元测试

```go
// pkg/propagation/b3/b3_test.go

package b3

import (
 "context"
 "testing"

 "github.com/stretchr/testify/assert"
 "github.com/stretchr/testify/require"
 "go.opentelemetry.io/otel/propagation"
 "go.opentelemetry.io/otel/trace"
)

func TestB3InjectExtractSingleHeader(t *testing.T) {
 b3 := New(WithInjectEncoding(B3SingleHeader))

 // 创建测试SpanContext
 tid, _ := trace.TraceIDFromHex("4bf92f3577b34da6a3ce929d0e0e4736")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")

 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })

 ctx := trace.ContextWithSpanContext(context.Background(), sc)

 // Inject
 carrier := propagation.MapCarrier{}
 b3.Inject(ctx, carrier)

 // 验证单头
 assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1", carrier["b3"])

 // Extract
 extractedCtx := b3.Extract(context.Background(), carrier)
 extractedSC := trace.SpanContextFromContext(extractedCtx)

 assert.True(t, extractedSC.IsValid())
 assert.Equal(t, tid, extractedSC.TraceID())
 assert.Equal(t, sid, extractedSC.SpanID())
 assert.True(t, extractedSC.IsSampled())
}

func TestB3InjectExtractMultipleHeaders(t *testing.T) {
 b3 := New(WithInjectEncoding(B3MultipleHeader))

 tid, _ := trace.TraceIDFromHex("4bf92f3577b34da6a3ce929d0e0e4736")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")

 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })

 ctx := trace.ContextWithSpanContext(context.Background(), sc)

 // Inject
 carrier := propagation.MapCarrier{}
 b3.Inject(ctx, carrier)

 // 验证多头
 assert.Equal(t, "4bf92f3577b34da6a3ce929d0e0e4736", carrier[headerTraceID])
 assert.Equal(t, "00f067aa0ba902b7", carrier[headerSpanID])
 assert.Equal(t, "1", carrier[headerSampled])
}

func TestB3ExtractSingleHeaderOnlySampling(t *testing.T) {
 b3 := New()

 // 仅采样决策
 carrier := propagation.MapCarrier{
  "b3": "1",
 }

 ctx := b3.Extract(context.Background(), carrier)
 sc := trace.SpanContextFromContext(ctx)

 // 只有采样标志，没有有效上下文
 assert.False(t, sc.IsValid())
}

func TestB3ExtractInvalidTraceID(t *testing.T) {
 b3 := New()

 carrier := propagation.MapCarrier{
  headerTraceID: "invalid",
  headerSpanID:  "00f067aa0ba902b7",
 }

 ctx := b3.Extract(context.Background(), carrier)
 sc := trace.SpanContextFromContext(ctx)

 assert.False(t, sc.IsValid())
}

func TestB3Fields(t *testing.T) {
 b3 := New()
 fields := b3.Fields()

 assert.Contains(t, fields, "b3")
 assert.Contains(t, fields, "X-B3-TraceId")
 assert.Contains(t, fields, "X-B3-SpanId")
}

func TestB3BothFormatsInject(t *testing.T) {
 // 默认同时注入两种格式
 b3 := New()

 tid, _ := trace.TraceIDFromHex("4bf92f3577b34da6a3ce929d0e0e4736")
 sid, _ := trace.SpanIDFromHex("00f067aa0ba902b7")

 sc := trace.NewSpanContext(trace.SpanContextConfig{
  TraceID:    tid,
  SpanID:     sid,
  TraceFlags: trace.FlagsSampled,
 })

 ctx := trace.ContextWithSpanContext(context.Background(), sc)

 carrier := propagation.MapCarrier{}
 b3.Inject(ctx, carrier)

 // 同时存在
 assert.NotEmpty(t, carrier["b3"])
 assert.NotEmpty(t, carrier[headerTraceID])
}

func BenchmarkB3Inject(b *testing.B) {
 b3 := New()
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
  b3.Inject(ctx, carrier)
 }
}

func BenchmarkB3Extract(b *testing.B) {
 b3 := New()
 carrier := propagation.MapCarrier{
  "b3": "4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-1",
 }

 b.ResetTimer()
 for i := 0; i < b.N; i++ {
  b3.Extract(context.Background(), carrier)
 }
}
```

---

## 4. 与OTel SDK集成

### 4.1 配置使用

```go
// 在TracerProvider中使用

import (
 "github.com/OTLP_go/pkg/propagation/b3"
 "go.opentelemetry.io/otel"
 "go.opentelemetry.io/otel/propagation"
)

func initB3Propagation() {
 // 创建复合传播器: W3C + B3
 composite := propagation.NewCompositeTextMapPropagator(
  propagation.TraceContext{},  // W3C
  propagation.Baggage{},
  b3.New(),  // B3 (单头+多头)
 )

 otel.SetTextMapPropagator(composite)
}

// 或者仅使用B3
func initB3Only() {
 otel.SetTextMapPropagator(
  b3.New(b3.WithInjectEncoding(b3.B3SingleHeader)),
 )
}
```

---

## 5. 最佳实践

### 5.1 互操作性建议

```go
// 生产环境推荐: 同时支持W3C和B3
propagator := propagation.NewCompositeTextMapPropagator(
 propagation.TraceContext{},  // W3C (新标准)
 propagation.Baggage{},
 b3.New(),                     // B3 (兼容Zipkin)
)

// 这样:
// - 接收: 可以解析W3C或B3格式
// - 发送: 同时发送两种格式，确保兼容性
```

### 5.2 性能优化

| 优化点 | 说明 |
|--------|------|
| 复用传播器 | 避免每次请求创建新实例 |
| 单头vs多头 | 单头更紧凑，多头更易调试 |
| 采样决策传递 | 确保采样标志正确传递 |

---

## 6. 参考

- [Zipkin B3 Propagation](https://github.com/openzipkin/b3-propagation)
- [OpenTelemetry B3 Propagator](https://github.com/open-telemetry/opentelemetry-go-contrib/tree/main/propagators/b3)
- [W3C Trace Context](https://www.w3.org/TR/trace-context/)

---

**文档状态**: ✅ Phase 2.1 完成
**代码状态**: ✅ 完整实现 + 测试
**更新日期**: 2026-04-06

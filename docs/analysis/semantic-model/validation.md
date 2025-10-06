# OTLP 语义模型验证

## 目录

- [OTLP 语义模型验证](#otlp-语义模型验证)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 静态验证](#2-静态验证)
    - [2.1 类型检查](#21-类型检查)
    - [2.2 接口契约](#22-接口契约)
  - [3. 运行时验证](#3-运行时验证)
    - [3.1 不变量检查](#31-不变量检查)
    - [3.2 Histogram 验证](#32-histogram-验证)
  - [4. 测试策略](#4-测试策略)
    - [4.1 单元测试](#41-单元测试)
    - [4.2 属性测试](#42-属性测试)
  - [5. 参考资料](#5-参考资料)

## 1. 引言

本文档描述 OTLP 语义模型的验证方法，确保实现符合规范要求。

## 2. 静态验证

### 2.1 类型检查

```go
// 编译时类型安全
func validateSpan(s trace.Span) error {
    // Go 类型系统确保基本类型正确
    _ = s.SpanContext().TraceID()  // TraceID 类型
    _ = s.SpanContext().SpanID()   // SpanID 类型
    return nil
}
```

### 2.2 接口契约

```go
// 确保实现满足接口
var _ trace.Span = (*recordingSpan)(nil)
var _ trace.TracerProvider = (*tracerProvider)(nil)
```

## 3. 运行时验证

### 3.1 不变量检查

```go
// Span 时间有效性
func validateSpanTiming(s ReadOnlySpan) error {
    if !s.EndTime().IsZero() && s.StartTime().After(s.EndTime()) {
        return fmt.Errorf("span end time before start time")
    }
    return nil
}

// TraceID/SpanID 有效性
func validateSpanContext(sc trace.SpanContext) error {
    if !sc.TraceID().IsValid() {
        return fmt.Errorf("invalid trace ID")
    }
    if !sc.SpanID().IsValid() {
        return fmt.Errorf("invalid span ID")
    }
    return nil
}
```

### 3.2 Histogram 验证

```go
func validateHistogram(h *HistogramDataPoint) error {
    // 桶数量一致性
    if len(h.BucketCounts) != len(h.ExplicitBounds)+1 {
        return fmt.Errorf("bucket count mismatch")
    }
    
    // 边界单调性
    for i := 1; i < len(h.ExplicitBounds); i++ {
        if h.ExplicitBounds[i-1] >= h.ExplicitBounds[i] {
            return fmt.Errorf("bounds not monotonic")
        }
    }
    
    // 总计数一致性
    var sum uint64
    for _, count := range h.BucketCounts {
        sum += count
    }
    if sum != h.Count {
        return fmt.Errorf("count mismatch: sum=%d, count=%d", sum, h.Count)
    }
    
    return nil
}
```

## 4. 测试策略

### 4.1 单元测试

```go
func TestSpanCreation(t *testing.T) {
    tracer := otel.Tracer("test")
    ctx, span := tracer.Start(context.Background(), "test-span")
    defer span.End()
    
    // 验证 SpanContext
    sc := span.SpanContext()
    assert.True(t, sc.IsValid())
    assert.True(t, sc.TraceID().IsValid())
    assert.True(t, sc.SpanID().IsValid())
}
```

### 4.2 属性测试

```go
// 使用 quick.Check 进行属性测试
func TestHistogramProperties(t *testing.T) {
    f := func(values []float64) bool {
        if len(values) == 0 {
            return true
        }
        
        hist := NewHistogram([]float64{1, 10, 100})
        for _, v := range values {
            hist.Record(v)
        }
        
        // 验证不变量
        return validateHistogram(hist.DataPoint()) == nil
    }
    
    if err := quick.Check(f, nil); err != nil {
        t.Error(err)
    }
}
```

## 5. 参考资料

- **形式化定义**: `docs/analysis/semantic-model/formal-definition.md`
- **Go 实现**: `docs/analysis/semantic-model/go-implementation.md`
- **TLA+ 验证**: `docs/formal/tla/pipeline.tla`

# 自定义采样器示例

演示如何实现自定义采样策略，根据请求特征动态调整采样率。

## 采样策略

| 请求类型 | 采样率 | 说明 |
|---------|-------|------|
| 错误请求 | 100% | 所有错误都需要追踪 |
| 慢请求 (>500ms) | 100% | 性能问题需要分析 |
| 正常请求 | 10% | 基础采样率 |

## 运行示例

```bash
go run main.go
```

## 输出示例

```text
Sampling: ERROR detected - 100% sampling
Request #3: ERROR, NORMAL, 450ms

Sampling: SLOW request (650ms) - 100% sampling
Request #7: SUCCESS, SLOW, 650ms

Sampling: BASE rate - dropped
Request #10: SUCCESS, NORMAL, 300ms

Sampling: BASE rate - sampled
Request #15: SUCCESS, NORMAL, 400ms
```

## 关键代码

### 自定义 Sampler

```go
type AdaptiveSampler struct {
    baseSamplingRate  float64
    errorSamplingRate float64
    slowSamplingRate  float64
    slowThresholdMs   int64
}

func (s *AdaptiveSampler) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
    // 检查错误
    // 检查慢请求
    // 应用基础采样率
}
```

### 使用自定义 Sampler

```go
customSampler := NewAdaptiveSampler(0.1, 1.0, 1.0, 500)
tp := sdktrace.NewTracerProvider(
    sdktrace.WithSampler(customSampler),
)
```

## 学习要点

1. **Sampler 接口**: 实现 `ShouldSample()` 方法
2. **采样决策**: 基于 Span 属性动态决策
3. **父级采样**: 尊重父 Span 的采样决策
4. **性能优化**: 降低追踪开销

## 高级用法

### 动态调整采样率

```go
// 根据系统负载动态调整
func (s *AdaptiveSampler) AdjustRate(load float64) {
    if load > 0.9 {
        s.baseSamplingRate = 0.01 // 1%
    } else if load > 0.7 {
        s.baseSamplingRate = 0.05 // 5%
    } else {
        s.baseSamplingRate = 0.1  // 10%
    }
}
```

### 基于用户的采样

```go
// VIP 用户 100% 采样
if userTier == "VIP" {
    return sdktrace.RecordAndSample
}
```

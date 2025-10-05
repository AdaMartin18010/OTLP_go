# 熔断器模式示例

演示如何使用熔断器模式提高系统容错能力。

## 熔断器状态

```text
CLOSED → (failures >= threshold) → OPEN
   ↑                                  ↓
   └── (success) ← HALF_OPEN ← (timeout)
```

| 状态 | 说明 | 行为 |
|-----|------|------|
| **CLOSED** | 正常状态 | 允许所有请求通过 |
| **OPEN** | 熔断状态 | 拒绝所有请求 |
| **HALF_OPEN** | 半开状态 | 允许少量请求测试服务是否恢复 |

## 运行示例

```bash
go run main.go
```

## 输出示例

```text
Request #1: SUCCESS
Request #2: SUCCESS
Request #3: SUCCESS
Request #4: SUCCESS
Request #5: FAILED (service unavailable)
Request #6: FAILED (service unavailable)
Request #7: FAILED (service unavailable)
[Circuit Breaker] Opening circuit (failures: 3)
Request #8: REJECTED (circuit open)
Request #9: REJECTED (circuit open)
Request #10: REJECTED (circuit open)
[Circuit Breaker] Transitioning to HALF_OPEN
Request #11: SUCCESS
[Circuit Breaker] Closing circuit (recovered)
Request #12: SUCCESS
```

## 关键参数

```go
cb := NewCircuitBreaker(
    3,             // maxFailures: 最大失败次数
    5*time.Second, // timeout: 熔断超时时间
)
```

## 最佳实践

### 1. 合理设置阈值

- **maxFailures**: 3-5 次
- **timeout**: 5-30 秒

### 2. 监控熔断器状态

```go
span.SetAttributes(
    attribute.String("circuit.state", state.String()),
    attribute.Int("circuit.failures", failures),
)
```

### 3. 提供降级方案

```go
err := cb.Call(ctx, func() error {
    return callRemoteService()
})
if err != nil {
    // 使用缓存或默认值
    return getFallbackData()
}
```

## 适用场景

- 远程服务调用
- 数据库查询
- 第三方 API 集成
- 微服务通信

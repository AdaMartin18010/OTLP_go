# 重试机制示例

演示如何实现带指数退避的重试机制。

## 重试策略

```text
Attempt 1: Wait 1s
Attempt 2: Wait 2s  (1s × 2)
Attempt 3: Wait 4s  (2s × 2)
Attempt 4: Wait 8s  (4s × 2)
Attempt 5: Wait 16s (8s × 2)
```

## 配置参数

```go
RetryConfig{
    InitialInterval: 1 * time.Second,  // 初始间隔
    MaxInterval:     30 * time.Second, // 最大间隔
    MaxElapsedTime:  5 * time.Minute,  // 最大总时间
    Multiplier:      2.0,               // 倍数
    MaxRetries:      5,                 // 最大重试次数
}
```

## 运行示例

```bash
go run main.go
```

## 输出示例

```text
=== Example 1: Successful Retry ===
✗ Attempt 1 failed: service temporarily unavailable
⏳ Waiting 1s before retry...
✗ Attempt 2 failed: service temporarily unavailable
⏳ Waiting 2s before retry...
✓ Success on attempt 3
Final result: SUCCESS

=== Example 2: Max Retries Exceeded ===
✗ Attempt 1 failed: service temporarily unavailable
⏳ Waiting 1s before retry...
✗ Attempt 2 failed: service temporarily unavailable
⏳ Waiting 2s before retry...
✗ Attempt 3 failed: service temporarily unavailable
✗ Max retries (3) exceeded
Final result: FAILED (expected)
```

## 最佳实践

### 1. 幂等性

确保操作可以安全重试：

```go
// ✓ 幂等操作
GET /api/users/123
PUT /api/users/123 {"name": "John"}

// ✗ 非幂等操作
POST /api/orders (创建订单)
```

### 2. 可重试的错误

只重试临时性错误：

```go
func isRetryable(err error) bool {
    // 网络错误、超时、503 等
    return errors.Is(err, ErrTemporary)
}
```

### 3. 添加抖动

避免惊群效应：

```go
jitter := time.Duration(rand.Int63n(int64(interval * 0.1)))
time.Sleep(interval + jitter)
```

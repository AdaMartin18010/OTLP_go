# 弹性模式示例

> **难度**: ⭐⭐⭐  
> **Go 版本**: 1.25.1+  
> **OpenTelemetry SDK**: v1.32.0+

本目录包含弹性设计模式的示例代码，帮助构建健壮的分布式系统。

---

## 📚 示例列表

### 1. [circuit-breaker](./circuit-breaker/) - 熔断器模式

**难度**: ⭐⭐⭐  
**用途**: 故障隔离、快速失败

**功能**:

- 三态熔断器 (关闭/打开/半开)
- 失败计数和阈值
- 自动恢复机制
- 监控和告警

**适用场景**:

- 依赖服务不稳定
- 需要快速失败
- 防止级联故障
- 保护系统资源

**运行**:

```bash
cd circuit-breaker
go run main.go
```

**核心概念**:

```text
┌──────────────────────────────────────┐
│         熔断器状态机                  │
├──────────────────────────────────────┤
│                                      │
│  [Closed] ──失败超阈值──> [Open]      │
│     ↑                        │       │
│     │                        │       │
│     └──成功──[Half-Open]<────┘       │
│              超时后尝试               │
│                                      │
└──────────────────────────────────────┘
```

---

### 2. [retry](./retry/) - 重试机制

**难度**: ⭐⭐⭐  
**用途**: 临时故障恢复

**功能**:

- 指数退避重试
- 最大重试次数
- Jitter (抖动)
- 错误分类

**适用场景**:

- 网络抖动
- 临时性故障
- 服务重启
- 资源争用

**运行**:

```bash
cd retry
go run main.go
```

**重试策略**:

```text
尝试次数    延迟时间      累计时间
   1        0ms          0ms
   2        100ms        100ms
   3        200ms        300ms
   4        400ms        700ms
   5        800ms        1500ms
```

---

## 🎯 弹性模式对比

| 模式 | 用途 | 优点 | 缺点 | 适用场景 |
|------|------|------|------|---------|
| **熔断器** | 快速失败 | 保护系统 | 可能过早熔断 | 依赖不稳定 |
| **重试** | 故障恢复 | 自动恢复 | 增加延迟 | 临时故障 |
| **超时** | 资源保护 | 防止阻塞 | 可能中断正常请求 | 长时间操作 |
| **限流** | 流量控制 | 防止过载 | 丢弃请求 | 高并发 |
| **降级** | 保证核心 | 部分可用 | 功能受限 | 容量不足 |

---

## 🚀 快速开始

### 运行所有示例

```bash
# 熔断器模式
cd circuit-breaker
go run main.go

# 重试机制
cd ../retry
go run main.go
```

### 测试不同场景

```bash
# 测试熔断器
cd circuit-breaker
go test -v

# 测试重试机制
cd ../retry
go test -v
```

---

## 📖 学习路径

### 初学者路径

1. 理解弹性设计概念
2. 运行 [circuit-breaker](./circuit-breaker/)
3. 运行 [retry](./retry/)
4. 对比两种模式

### 进阶路径

1. 结合 [error-handling](../error-handling/)
2. 学习错误分类
3. 实现自定义策略
4. 生产环境应用

### 高级路径

1. 多模式组合
2. 动态配置调整
3. 监控和告警
4. 性能优化

---

## 💡 核心概念

### 1. 熔断器 (Circuit Breaker)

**三种状态**:

**Closed (关闭)**: 正常状态

- 请求正常通过
- 记录失败次数
- 失败超阈值 → Open

**Open (打开)**: 熔断状态

- 直接返回错误
- 不执行实际调用
- 超时后 → Half-Open

**Half-Open (半开)**: 试探状态

- 允许少量请求
- 成功 → Closed
- 失败 → Open

**代码示例**:

```go
type CircuitBreaker struct {
    state         State
    failures      int
    threshold     int
    timeout       time.Duration
    lastFailTime  time.Time
}

func (cb *CircuitBreaker) Call(fn func() error) error {
    switch cb.state {
    case Closed:
        err := fn()
        if err != nil {
            cb.failures++
            if cb.failures >= cb.threshold {
                cb.state = Open
            }
        } else {
            cb.failures = 0
        }
        return err
        
    case Open:
        if time.Since(cb.lastFailTime) > cb.timeout {
            cb.state = HalfOpen
            return cb.Call(fn)
        }
        return ErrCircuitOpen
        
    case HalfOpen:
        err := fn()
        if err != nil {
            cb.state = Open
        } else {
            cb.state = Closed
            cb.failures = 0
        }
        return err
    }
}
```

### 2. 重试机制 (Retry)

**指数退避**:

- 第1次: 100ms
- 第2次: 200ms
- 第3次: 400ms
- 第4次: 800ms

**Jitter (抖动)**:

- 添加随机延迟
- 避免惊群效应
- 分散重试时间

**代码示例**:

```go
func RetryWithBackoff(fn func() error, maxRetries int) error {
    var err error
    for i := 0; i < maxRetries; i++ {
        err = fn()
        if err == nil {
            return nil
        }
        
        if !shouldRetry(err) {
            return err
        }
        
        backoff := time.Duration(1<<uint(i)) * 100 * time.Millisecond
        jitter := time.Duration(rand.Intn(100)) * time.Millisecond
        time.Sleep(backoff + jitter)
    }
    return err
}
```

---

## 🔧 最佳实践

### 熔断器配置

```go
breaker := &CircuitBreaker{
    Threshold: 5,           // 5次失败后熔断
    Timeout:   30 * time.Second,  // 30秒后尝试恢复
    OnOpen:    logCircuitOpen,    // 熔断时记录日志
}
```

### 重试配置

```go
retryConfig := &RetryConfig{
    MaxRetries:   3,              // 最多重试3次
    InitialDelay: 100 * time.Millisecond,
    MaxDelay:     5 * time.Second,
    Multiplier:   2.0,            // 指数因子
    Jitter:       true,           // 启用抖动
}
```

### 错误分类

```go
func shouldRetry(err error) bool {
    // 可重试的错误
    switch err {
    case context.DeadlineExceeded:
        return true
    case io.EOF:
        return true
    }
    
    // 不可重试的错误
    if errors.Is(err, ErrBadRequest) {
        return false
    }
    
    return false
}
```

---

## 📊 性能影响

### 熔断器开销

| 指标 | 无熔断器 | 有熔断器 | 增加 |
|------|---------|---------|------|
| **延迟** | 10ms | 10.1ms | +1% |
| **内存** | 5MB | 5.1MB | +2% |
| **CPU** | 2% | 2.1% | +5% |

### 重试影响

| 场景 | 成功率 | 平均延迟 | P99延迟 |
|------|--------|---------|---------|
| **无重试** | 90% | 10ms | 15ms |
| **1次重试** | 99% | 20ms | 120ms |
| **3次重试** | 99.9% | 40ms | 1.5s |

---

## 🐛 常见问题

### Q1: 何时使用熔断器?

A: 当依赖服务:

- 响应时间不稳定
- 经常出现故障
- 可能导致级联失败
- 需要快速失败

### Q2: 何时使用重试?

A: 当错误:

- 是临时性的
- 有较高成功率
- 可以接受延迟增加
- 不会导致数据不一致

### Q3: 如何避免重试风暴?

A: 策略:

1. 使用指数退避
2. 添加 Jitter
3. 设置最大重试次数
4. 区分可重试错误

### Q4: 熔断器阈值如何设置?

A: 考虑因素:

1. 服务 SLA
2. 错误率
3. 恢复时间
4. 业务影响

**推荐值**:

- 阈值: 5-10 次失败
- 超时: 30-60 秒
- 半开测试: 1-3 次

---

## 🔗 相关资源

### 文档

- [13_Go错误处理与OTLP集成.md](../../标准深度梳理_2025_10/00_Go完整集成指南/13_Go错误处理与OTLP集成.md)
- [06_实战案例/04_生产环境最佳实践.md](../../标准深度梳理_2025_10/06_实战案例/04_生产环境最佳实践.md)

### 示例

- [error-handling](../error-handling/) - 错误处理基础
- [microservices](../microservices/) - 微服务集成
- [distributed-tracing](../distributed-tracing/) - 分布式追踪

### 第三方库

- [go-resilience/breaker](https://github.com/eapache/go-resiliency) - 熔断器实现
- [cenkalti/backoff](https://github.com/cenkalti/backoff) - 退避算法
- [sony/gobreaker](https://github.com/sony/gobreaker) - 熔断器库

---

## 📝 设计建议

### ✅ 推荐做法

1. **组合使用**: 熔断器 + 重试
2. **监控**: 记录所有状态变化
3. **告警**: 熔断时发送告警
4. **配置**: 支持动态调整
5. **测试**: 模拟各种故障场景

### ❌ 避免做法

1. **盲目重试**: 所有错误都重试
2. **忽略超时**: 没有超时控制
3. **全局熔断**: 不区分不同依赖
4. **固定延迟**: 使用固定重试间隔
5. **缺少监控**: 不记录状态

---

## 🚀 生产部署

### 监控指标

```go
// 熔断器指标
metrics.RecordCircuitBreakerState(state)
metrics.RecordCircuitBreakerTrips(count)

// 重试指标
metrics.RecordRetryAttempts(count)
metrics.RecordRetrySuccess(bool)
```

### 告警规则

```yaml
alerts:
  - name: CircuitBreakerOpen
    condition: circuit_breaker_state == "open"
    duration: 5m
    severity: warning
    
  - name: HighRetryRate
    condition: retry_rate > 0.3
    duration: 5m
    severity: warning
```

### 配置管理

```yaml
circuit_breaker:
  threshold: 5
  timeout: 30s
  metrics_enabled: true
  
retry:
  max_retries: 3
  initial_delay: 100ms
  max_delay: 5s
  jitter: true
```

---

## 🎓 进阶学习

### 下一步

1. 实现超时控制
2. 添加限流器
3. 实现降级策略
4. 集成监控系统

### 推荐阅读

1. "Release It!" - Michael Nygard
2. "Site Reliability Engineering" - Google
3. "Building Microservices" - Sam Newman

---

**创建日期**: 2025-10-08  
**更新频率**: 随项目更新  
**维护状态**: ✅ 活跃维护

---

**构建弹性系统!** 💪

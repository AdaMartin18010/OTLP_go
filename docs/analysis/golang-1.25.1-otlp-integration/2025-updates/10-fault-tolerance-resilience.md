# 容错与弹性

> **文档版本**: v1.0  
> **最后更新**: 2025-10-04  
> **关联文档**: [04-分布式追踪架构](./04-distributed-tracing-architecture.md), [19-生产最佳实践](./19-production-best-practices-2025.md)

---

## 目录

- [容错与弹性](#容错与弹性)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 重试机制](#2-重试机制)
  - [3. 熔断器模式](#3-熔断器模式)
  - [4. 限流策略](#4-限流策略)
  - [5. 降级方案](#5-降级方案)
  - [6. 超时控制](#6-超时控制)
  - [7. 故障隔离](#7-故障隔离)
  - [8. 健康检查](#8-健康检查)
  - [9. 故障恢复](#9-故障恢复)
  - [10. 最佳实践](#10-最佳实践)

---

## 1. 概述

容错与弹性设计确保系统在部分组件失败时仍能正常运行。

**设计原则**:

- 故障隔离
- 快速失败
- 优雅降级
- 自动恢复

---

## 2. 重试机制

**指数退避重试**:

```go
type RetryConfig struct {
    InitialInterval time.Duration
    MaxInterval     time.Duration
    MaxElapsedTime  time.Duration
    Multiplier      float64
}

func RetryWithBackoff(fn func() error, config RetryConfig) error {
    interval := config.InitialInterval
    elapsed := time.Duration(0)
    
    for {
        err := fn()
        if err == nil {
            return nil
        }
        
        if elapsed >= config.MaxElapsedTime {
            return err
        }
        
        time.Sleep(interval)
        elapsed += interval
        interval = time.Duration(float64(interval) * config.Multiplier)
        if interval > config.MaxInterval {
            interval = config.MaxInterval
        }
    }
}
```

---

## 3. 熔断器模式

**实现**:

```go
type CircuitBreaker struct {
    maxFailures  int
    timeout      time.Duration
    state        State
    failures     int
    lastFailTime time.Time
    mu           sync.Mutex
}

func (cb *CircuitBreaker) Call(fn func() error) error {
    cb.mu.Lock()
    defer cb.mu.Unlock()
    
    if cb.state == StateOpen {
        if time.Since(cb.lastFailTime) > cb.timeout {
            cb.state = StateHalfOpen
        } else {
            return ErrCircuitOpen
        }
    }
    
    err := fn()
    if err != nil {
        cb.failures++
        cb.lastFailTime = time.Now()
        if cb.failures >= cb.maxFailures {
            cb.state = StateOpen
        }
        return err
    }
    
    cb.failures = 0
    cb.state = StateClosed
    return nil
}
```

---

## 4. 限流策略

**令牌桶算法**:

```go
type TokenBucket struct {
    capacity int
    tokens   int
    rate     time.Duration
    mu       sync.Mutex
}

func (tb *TokenBucket) Allow() bool {
    tb.mu.Lock()
    defer tb.mu.Unlock()
    
    if tb.tokens > 0 {
        tb.tokens--
        return true
    }
    return false
}
```

**漏桶算法**:

```go
// 漏桶实现
```

---

## 5. 降级方案

**采样率降级**:

```go
func AdaptiveSampling(load float64) float64 {
    if load > 0.9 {
        return 0.01 // 1% 采样
    } else if load > 0.7 {
        return 0.1  // 10% 采样
    }
    return 1.0 // 100% 采样
}
```

**功能降级**:

```go
// 禁用非关键功能
```

---

## 6. 超时控制

**Context 超时**:

```go
ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
defer cancel()

_, span := tracer.Start(ctx, "operation")
defer span.End()

select {
case <-ctx.Done():
    return ctx.Err()
case result := <-doWork():
    return result
}
```

---

## 7. 故障隔离

**Bulkhead 模式**:

```go
type Bulkhead struct {
    semaphore chan struct{}
}

func NewBulkhead(maxConcurrent int) *Bulkhead {
    return &Bulkhead{
        semaphore: make(chan struct{}, maxConcurrent),
    }
}

func (b *Bulkhead) Execute(fn func() error) error {
    select {
    case b.semaphore <- struct{}{}:
        defer func() { <-b.semaphore }()
        return fn()
    default:
        return ErrBulkheadFull
    }
}
```

---

## 8. 健康检查

**Liveness Probe**:

```go
func LivenessHandler(w http.ResponseWriter, r *http.Request) {
    w.WriteHeader(http.StatusOK)
    w.Write([]byte("OK"))
}
```

**Readiness Probe**:

```go
func ReadinessHandler(w http.ResponseWriter, r *http.Request) {
    if isReady() {
        w.WriteHeader(http.StatusOK)
    } else {
        w.WriteHeader(http.StatusServiceUnavailable)
    }
}
```

---

## 9. 故障恢复

**自动重启**:

```yaml
apiVersion: v1
kind: Pod
spec:
  containers:
  - name: app
    restartPolicy: Always
```

**数据恢复**:

```go
// 从持久化队列恢复数据
```

---

## 10. 最佳实践

**设计原则**:

- 假设一切都会失败
- 快速失败，快速恢复
- 监控所有组件
- 定期演练

**监控指标**:

- 错误率
- 重试次数
- 熔断器状态
- 队列深度

---

**文档状态**: ✅ 骨架完成，待填充详细内容  
**最后更新**: 2025-10-04  
**维护者**: OTLP_go Team

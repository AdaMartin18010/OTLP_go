# Redis 高级集成与 OTLP 完整集成（2025版）

> **Redis 版本**: v7.2+  
> **Go Redis 客户端**: go-redis/redis/v9  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Redis 高级集成与 OTLP 完整集成（2025版）](#redis-高级集成与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Redis 概述](#1-redis-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 性能优势](#12-性能优势)
    - [1.3 适用场景](#13-适用场景)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础集成](#22-基础集成)
    - [2.3 OTLP 钩子实现](#23-otlp-钩子实现)
  - [3. 完整集成示例](#3-完整集成示例)
    - [3.1 缓存管理器](#31-缓存管理器)
    - [3.2 分布式锁](#32-分布式锁)
    - [3.3 限流器](#33-限流器)
  - [4. 高级特性](#4-高级特性)
    - [4.1 Pipeline 优化](#41-pipeline-优化)
    - [4.2 发布订阅](#42-发布订阅)
    - [4.3 Lua 脚本](#43-lua-脚本)
  - [5. Redis 集群](#5-redis-集群)
    - [5.1 集群配置](#51-集群配置)
    - [5.2 Sentinel 高可用](#52-sentinel-高可用)
  - [6. 性能优化](#6-性能优化)
  - [7. 生产部署](#7-生产部署)
  - [8. 最佳实践](#8-最佳实践)
  - [总结](#总结)

---

## 1. Redis 概述

### 1.1 核心特性

**Redis** 是一个开源的内存数据结构存储系统，可用作数据库、缓存和消息代理。

```text
🚀 核心特性:
  ✅ 内存存储 - 极致性能
  ✅ 数据结构 - String, Hash, List, Set, Sorted Set
  ✅ 持久化 - RDB + AOF
  ✅ 主从复制 - 高可用
  ✅ 集群模式 - 水平扩展
  ✅ 发布订阅 - 实时消息
  
⚡ 性能数据:
  - 读写: 100K+ ops/s
  - 延迟: P99 < 1ms
  - 内存: 高效压缩
  - 持久化: 可配置
```

### 1.2 性能优势

```text
┌─────────────┬──────────────┬─────────────┬─────────────┐
│   指标      │  Redis       │  Memcached  │  Local      │
├─────────────┼──────────────┼─────────────┼─────────────┤
│ 读性能      │  100K ops/s  │  200K ops/s │  1M ops/s   │
│ 写性能      │  80K ops/s   │  150K ops/s │  500K ops/s │
│ 延迟(P99)   │  1ms         │  0.5ms      │  0.1ms      │
│ 数据结构    │  丰富        │  简单       │  自定义     │
│ 持久化      │  ✅          │  ❌         │  取决实现   │
│ 分布式      │  ✅          │  客户端     │  ❌         │
│ 适用场景    │  通用        │  简单缓存   │  单机       │
└─────────────┴──────────────┴─────────────┴─────────────┘
```

### 1.3 适用场景

```text
✅ 适合场景:
  - 缓存层（热点数据）
  - 会话存储
  - 排行榜/计数器
  - 分布式锁
  - 限流器
  - 消息队列
  - 实时分析

❌ 不适合场景:
  - 大数据量存储（>100GB）
  - 复杂关系查询
  - 强一致性要求
  - 需要 SQL 查询
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 go-redis
go get -u github.com/redis/go-redis/v9@latest

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u go.opentelemetry.io/contrib/instrumentation/github.com/redis/go-redis/v9/redisotel@v0.56.0
```

**go.mod 示例**：

```go
module github.com/yourorg/redis-otlp-demo

go 1.25.1

require (
    github.com/redis/go-redis/v9 v9.7.0
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/contrib/instrumentation/github.com/redis/go-redis/v9/redisotel v0.56.0
)
```

### 2.2 基础集成

```go
package main

import (
    "context"
    "fmt"
    "log"
    "time"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
    "go.opentelemetry.io/contrib/instrumentation/github.com/redis/go-redis/v9/redisotel"
)

// 初始化追踪
func initTracer() (*sdktrace.TracerProvider, error) {
    ctx := context.Background()

    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithEndpoint("localhost:4317"),
        otlptracegrpc.WithInsecure(),
    )
    if err != nil {
        return nil, err
    }

    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("redis-cache"),
            semconv.ServiceVersion("1.0.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}

// 创建 Redis 客户端
func newRedisClient() *redis.Client {
    rdb := redis.NewClient(&redis.Options{
        Addr:         "localhost:6379",
        Password:     "",
        DB:           0,
        PoolSize:     100,
        MinIdleConns: 10,
        MaxRetries:   3,
        DialTimeout:  5 * time.Second,
        ReadTimeout:  3 * time.Second,
        WriteTimeout: 3 * time.Second,
    })

    // 启用 OTLP 追踪
    if err := redisotel.InstrumentTracing(rdb); err != nil {
        log.Fatalf("failed to instrument tracing: %v", err)
    }

    // 启用指标收集
    if err := redisotel.InstrumentMetrics(rdb); err != nil {
        log.Fatalf("failed to instrument metrics: %v", err)
    }

    return rdb
}

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 创建 Redis 客户端
    rdb := newRedisClient()
    defer rdb.Close()

    ctx := context.Background()

    // 基本操作
    err = rdb.Set(ctx, "key", "value", time.Hour).Err()
    if err != nil {
        log.Fatal(err)
    }

    val, err := rdb.Get(ctx, "key").Result()
    if err != nil {
        log.Fatal(err)
    }
    fmt.Println("key:", val)
}
```

### 2.3 OTLP 钩子实现

```go
package redis

import (
    "context"
    "fmt"
    "time"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TracingHook Redis 追踪钩子
type TracingHook struct {
    tracer trace.Tracer
}

func NewTracingHook(serviceName string) *TracingHook {
    return &TracingHook{
        tracer: otel.Tracer(serviceName),
    }
}

// DialHook 连接钩子
func (h *TracingHook) DialHook(next redis.DialHook) redis.DialHook {
    return func(ctx context.Context, network, addr string) (net.Conn, error) {
        ctx, span := h.tracer.Start(ctx, "redis.dial",
            trace.WithSpanKind(trace.SpanKindClient),
            trace.WithAttributes(
                attribute.String("db.system", "redis"),
                attribute.String("network.type", network),
                attribute.String("server.address", addr),
            ),
        )
        defer span.End()

        conn, err := next(ctx, network, addr)
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            return nil, err
        }

        span.SetStatus(codes.Ok, "")
        return conn, nil
    }
}

// ProcessHook 命令处理钩子
func (h *TracingHook) ProcessHook(next redis.ProcessHook) redis.ProcessHook {
    return func(ctx context.Context, cmd redis.Cmder) error {
        cmdName := cmd.Name()
        
        ctx, span := h.tracer.Start(ctx, fmt.Sprintf("redis.%s", cmdName),
            trace.WithSpanKind(trace.SpanKindClient),
            trace.WithAttributes(
                attribute.String("db.system", "redis"),
                attribute.String("db.operation", cmdName),
                attribute.String("db.statement", cmd.String()),
            ),
        )
        defer span.End()

        start := time.Now()
        err := next(ctx, cmd)
        duration := time.Since(start)

        span.SetAttributes(
            attribute.Float64("db.duration_ms", float64(duration.Microseconds())/1000.0),
        )

        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            return err
        }

        span.SetStatus(codes.Ok, "")
        return nil
    }
}

// ProcessPipelineHook Pipeline 钩子
func (h *TracingHook) ProcessPipelineHook(next redis.ProcessPipelineHook) redis.ProcessPipelineHook {
    return func(ctx context.Context, cmds []redis.Cmder) error {
        ctx, span := h.tracer.Start(ctx, "redis.pipeline",
            trace.WithSpanKind(trace.SpanKindClient),
            trace.WithAttributes(
                attribute.String("db.system", "redis"),
                attribute.Int("db.pipeline.commands", len(cmds)),
            ),
        )
        defer span.End()

        // 记录所有命令
        for i, cmd := range cmds {
            span.SetAttributes(
                attribute.String(fmt.Sprintf("db.pipeline.cmd.%d", i), cmd.Name()),
            )
        }

        start := time.Now()
        err := next(ctx, cmds)
        duration := time.Since(start)

        span.SetAttributes(
            attribute.Float64("db.duration_ms", float64(duration.Microseconds())/1000.0),
        )

        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            return err
        }

        span.SetStatus(codes.Ok, "")
        return nil
    }
}

// 使用示例
func ExampleWithCustomHook() {
    rdb := redis.NewClient(&redis.Options{
        Addr: "localhost:6379",
    })

    // 添加自定义钩子
    hook := NewTracingHook("redis-service")
    rdb.AddHook(hook)

    ctx := context.Background()
    rdb.Set(ctx, "key", "value", time.Hour)
}
```

---

## 3. 完整集成示例

### 3.1 缓存管理器

```go
package cache

import (
    "context"
    "encoding/json"
    "fmt"
    "time"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// CacheManager 缓存管理器
type CacheManager struct {
    client *redis.Client
    tracer trace.Tracer
    prefix string
}

func NewCacheManager(client *redis.Client, prefix string) *CacheManager {
    return &CacheManager{
        client: client,
        tracer: otel.Tracer("cache-manager"),
        prefix: prefix,
    }
}

// Get 获取缓存
func (m *CacheManager) Get(ctx context.Context, key string, dest interface{}) error {
    ctx, span := m.tracer.Start(ctx, "CacheManager.Get",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    fullKey := m.prefix + key
    val, err := m.client.Get(ctx, fullKey).Result()
    if err == redis.Nil {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        return ErrCacheMiss
    }
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("cache.value.size", len(val)),
    )

    if err := json.Unmarshal([]byte(val), dest); err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// Set 设置缓存
func (m *CacheManager) Set(ctx context.Context, key string, value interface{}, ttl time.Duration) error {
    ctx, span := m.tracer.Start(ctx, "CacheManager.Set",
        trace.WithAttributes(
            attribute.String("cache.key", key),
            attribute.Float64("cache.ttl_seconds", ttl.Seconds()),
        ),
    )
    defer span.End()

    data, err := json.Marshal(value)
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(attribute.Int("cache.value.size", len(data)))

    fullKey := m.prefix + key
    return m.client.Set(ctx, fullKey, data, ttl).Err()
}

// Delete 删除缓存
func (m *CacheManager) Delete(ctx context.Context, keys ...string) error {
    ctx, span := m.tracer.Start(ctx, "CacheManager.Delete",
        trace.WithAttributes(
            attribute.Int("cache.keys.count", len(keys)),
        ),
    )
    defer span.End()

    fullKeys := make([]string, len(keys))
    for i, key := range keys {
        fullKeys[i] = m.prefix + key
    }

    return m.client.Del(ctx, fullKeys...).Err()
}

// GetOrLoad 获取或加载
func (m *CacheManager) GetOrLoad(ctx context.Context, key string, ttl time.Duration, loader func(context.Context) (interface{}, error)) (interface{}, error) {
    ctx, span := m.tracer.Start(ctx, "CacheManager.GetOrLoad",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    // 尝试从缓存获取
    var result interface{}
    err := m.Get(ctx, key, &result)
    if err == nil {
        span.SetAttributes(attribute.Bool("cache.loaded_from_cache", true))
        return result, nil
    }

    if err != ErrCacheMiss {
        span.RecordError(err)
        return nil, err
    }

    // 缓存未命中，调用加载器
    span.SetAttributes(attribute.Bool("cache.loaded_from_cache", false))
    result, err = loader(ctx)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    // 写入缓存
    if err := m.Set(ctx, key, result, ttl); err != nil {
        // 记录错误但不影响返回
        span.RecordError(fmt.Errorf("failed to set cache: %w", err))
    }

    return result, nil
}

var ErrCacheMiss = fmt.Errorf("cache miss")

// 使用示例
func ExampleCacheManager() {
    ctx := context.Background()
    rdb := newRedisClient()
    cache := NewCacheManager(rdb, "myapp:")

    // 获取或加载用户数据
    type User struct {
        ID   int    `json:"id"`
        Name string `json:"name"`
    }

    user, err := cache.GetOrLoad(ctx, "user:123", time.Hour, func(ctx context.Context) (interface{}, error) {
        // 从数据库加载
        return &User{ID: 123, Name: "Alice"}, nil
    })
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("User: %+v\n", user)
}
```

### 3.2 分布式锁

```go
package lock

import (
    "context"
    "fmt"
    "time"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// DistributedLock 分布式锁
type DistributedLock struct {
    client *redis.Client
    tracer trace.Tracer
    key    string
    value  string
    ttl    time.Duration
}

func NewDistributedLock(client *redis.Client, key string, ttl time.Duration) *DistributedLock {
    return &DistributedLock{
        client: client,
        tracer: otel.Tracer("distributed-lock"),
        key:    fmt.Sprintf("lock:%s", key),
        value:  fmt.Sprintf("%d", time.Now().UnixNano()),
        ttl:    ttl,
    }
}

// Lock 获取锁
func (l *DistributedLock) Lock(ctx context.Context) (bool, error) {
    ctx, span := l.tracer.Start(ctx, "DistributedLock.Lock",
        trace.WithAttributes(
            attribute.String("lock.key", l.key),
            attribute.Float64("lock.ttl_seconds", l.ttl.Seconds()),
        ),
    )
    defer span.End()

    ok, err := l.client.SetNX(ctx, l.key, l.value, l.ttl).Result()
    if err != nil {
        span.RecordError(err)
        return false, err
    }

    span.SetAttributes(attribute.Bool("lock.acquired", ok))
    return ok, nil
}

// Unlock 释放锁
func (l *DistributedLock) Unlock(ctx context.Context) error {
    ctx, span := l.tracer.Start(ctx, "DistributedLock.Unlock",
        trace.WithAttributes(
            attribute.String("lock.key", l.key),
        ),
    )
    defer span.End()

    // Lua 脚本确保只删除自己的锁
    script := `
        if redis.call("get", KEYS[1]) == ARGV[1] then
            return redis.call("del", KEYS[1])
        else
            return 0
        end
    `

    result, err := l.client.Eval(ctx, script, []string{l.key}, l.value).Result()
    if err != nil {
        span.RecordError(err)
        return err
    }

    deleted := result.(int64) == 1
    span.SetAttributes(attribute.Bool("lock.released", deleted))

    return nil
}

// TryLockWithRetry 带重试的获取锁
func (l *DistributedLock) TryLockWithRetry(ctx context.Context, maxRetries int, retryInterval time.Duration) (bool, error) {
    ctx, span := l.tracer.Start(ctx, "DistributedLock.TryLockWithRetry",
        trace.WithAttributes(
            attribute.String("lock.key", l.key),
            attribute.Int("lock.max_retries", maxRetries),
        ),
    )
    defer span.End()

    for i := 0; i < maxRetries; i++ {
        ok, err := l.Lock(ctx)
        if err != nil {
            span.RecordError(err)
            return false, err
        }

        if ok {
            span.SetAttributes(attribute.Int("lock.retries", i))
            return true, nil
        }

        time.Sleep(retryInterval)
    }

    span.SetAttributes(attribute.Bool("lock.acquired", false))
    return false, nil
}

// WithLock 使用锁执行函数
func (l *DistributedLock) WithLock(ctx context.Context, fn func(context.Context) error) error {
    ctx, span := l.tracer.Start(ctx, "DistributedLock.WithLock")
    defer span.End()

    // 获取锁
    ok, err := l.Lock(ctx)
    if err != nil {
        return err
    }
    if !ok {
        return ErrLockNotAcquired
    }

    // 确保释放锁
    defer l.Unlock(ctx)

    // 执行函数
    return fn(ctx)
}

var ErrLockNotAcquired = fmt.Errorf("lock not acquired")

// 使用示例
func ExampleDistributedLock() {
    ctx := context.Background()
    rdb := newRedisClient()

    lock := NewDistributedLock(rdb, "resource:123", 10*time.Second)

    // 方式1: 手动加锁/解锁
    ok, err := lock.Lock(ctx)
    if err != nil {
        log.Fatal(err)
    }
    if !ok {
        log.Println("Failed to acquire lock")
        return
    }
    defer lock.Unlock(ctx)

    // 执行临界区代码
    fmt.Println("Critical section")

    // 方式2: 使用 WithLock
    err = lock.WithLock(ctx, func(ctx context.Context) error {
        fmt.Println("Critical section with auto-unlock")
        return nil
    })
    if err != nil {
        log.Fatal(err)
    }
}
```

### 3.3 限流器

```go
package ratelimit

import (
    "context"
    "fmt"
    "time"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// RateLimiter 限流器
type RateLimiter struct {
    client *redis.Client
    tracer trace.Tracer
}

func NewRateLimiter(client *redis.Client) *RateLimiter {
    return &RateLimiter{
        client: client,
        tracer: otel.Tracer("rate-limiter"),
    }
}

// Allow 检查是否允许（固定窗口）
func (r *RateLimiter) Allow(ctx context.Context, key string, limit int, window time.Duration) (bool, error) {
    ctx, span := r.tracer.Start(ctx, "RateLimiter.Allow",
        trace.WithAttributes(
            attribute.String("ratelimit.key", key),
            attribute.Int("ratelimit.limit", limit),
            attribute.Float64("ratelimit.window_seconds", window.Seconds()),
        ),
    )
    defer span.End()

    fullKey := fmt.Sprintf("ratelimit:%s", key)

    // 增加计数器
    count, err := r.client.Incr(ctx, fullKey).Result()
    if err != nil {
        span.RecordError(err)
        return false, err
    }

    // 第一次设置过期时间
    if count == 1 {
        r.client.Expire(ctx, fullKey, window)
    }

    allowed := count <= int64(limit)
    span.SetAttributes(
        attribute.Int64("ratelimit.current_count", count),
        attribute.Bool("ratelimit.allowed", allowed),
    )

    return allowed, nil
}

// AllowSlidingWindow 滑动窗口限流
func (r *RateLimiter) AllowSlidingWindow(ctx context.Context, key string, limit int, window time.Duration) (bool, error) {
    ctx, span := r.tracer.Start(ctx, "RateLimiter.AllowSlidingWindow",
        trace.WithAttributes(
            attribute.String("ratelimit.key", key),
            attribute.Int("ratelimit.limit", limit),
        ),
    )
    defer span.End()

    fullKey := fmt.Sprintf("ratelimit:sliding:%s", key)
    now := time.Now().UnixNano()
    windowStart := now - window.Nanoseconds()

    // Lua 脚本实现滑动窗口
    script := `
        local key = KEYS[1]
        local now = tonumber(ARGV[1])
        local window = tonumber(ARGV[2])
        local limit = tonumber(ARGV[3])
        local window_start = now - window

        -- 删除过期的记录
        redis.call('ZREMRANGEBYSCORE', key, 0, window_start)

        -- 获取当前计数
        local count = redis.call('ZCARD', key)

        if count < limit then
            redis.call('ZADD', key, now, now)
            redis.call('EXPIRE', key, math.ceil(window / 1000000000))
            return 1
        else
            return 0
        end
    `

    result, err := r.client.Eval(ctx, script,
        []string{fullKey},
        now, window.Nanoseconds(), limit,
    ).Result()

    if err != nil {
        span.RecordError(err)
        return false, err
    }

    allowed := result.(int64) == 1
    span.SetAttributes(attribute.Bool("ratelimit.allowed", allowed))

    return allowed, nil
}

// AllowTokenBucket 令牌桶限流
func (r *RateLimiter) AllowTokenBucket(ctx context.Context, key string, rate, burst int) (bool, error) {
    ctx, span := r.tracer.Start(ctx, "RateLimiter.AllowTokenBucket",
        trace.WithAttributes(
            attribute.String("ratelimit.key", key),
            attribute.Int("ratelimit.rate", rate),
            attribute.Int("ratelimit.burst", burst),
        ),
    )
    defer span.End()

    fullKey := fmt.Sprintf("ratelimit:tokenbucket:%s", key)
    now := time.Now().Unix()

    // Lua 脚本实现令牌桶
    script := `
        local key = KEYS[1]
        local rate = tonumber(ARGV[1])
        local burst = tonumber(ARGV[2])
        local now = tonumber(ARGV[3])

        local bucket = redis.call('HMGET', key, 'tokens', 'last_update')
        local tokens = tonumber(bucket[1]) or burst
        local last_update = tonumber(bucket[2]) or now

        -- 计算新增的令牌
        local elapsed = now - last_update
        local new_tokens = math.min(burst, tokens + elapsed * rate)

        if new_tokens >= 1 then
            new_tokens = new_tokens - 1
            redis.call('HMSET', key, 'tokens', new_tokens, 'last_update', now)
            redis.call('EXPIRE', key, 3600)
            return 1
        else
            return 0
        end
    `

    result, err := r.client.Eval(ctx, script,
        []string{fullKey},
        rate, burst, now,
    ).Result()

    if err != nil {
        span.RecordError(err)
        return false, err
    }

    allowed := result.(int64) == 1
    span.SetAttributes(attribute.Bool("ratelimit.allowed", allowed))

    return allowed, nil
}

// 使用示例
func ExampleRateLimiter() {
    ctx := context.Background()
    rdb := newRedisClient()
    limiter := NewRateLimiter(rdb)

    // 固定窗口: 每分钟最多100次
    userID := "user:123"
    allowed, err := limiter.Allow(ctx, userID, 100, time.Minute)
    if err != nil {
        log.Fatal(err)
    }
    if !allowed {
        log.Println("Rate limit exceeded")
        return
    }

    // 滑动窗口: 每秒最多10次
    allowed, err = limiter.AllowSlidingWindow(ctx, userID, 10, time.Second)
    if err != nil {
        log.Fatal(err)
    }

    // 令牌桶: 每秒10个令牌，最多20个
    allowed, err = limiter.AllowTokenBucket(ctx, userID, 10, 20)
    if err != nil {
        log.Fatal(err)
    }

    fmt.Println("Request allowed:", allowed)
}
```

---

## 4. 高级特性

### 4.1 Pipeline 优化

```go
package redis

import (
    "context"
    "fmt"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// BatchOperations 批量操作
func BatchOperations(ctx context.Context, rdb *redis.Client) error {
    ctx, span := otel.Tracer("redis").Start(ctx, "BatchOperations")
    defer span.End()

    // 创建 Pipeline
    pipe := rdb.Pipeline()

    // 批量添加命令
    for i := 0; i < 100; i++ {
        key := fmt.Sprintf("key:%d", i)
        pipe.Set(ctx, key, fmt.Sprintf("value:%d", i), 0)
    }

    span.SetAttributes(attribute.Int("pipeline.commands", 100))

    // 执行所有命令
    cmds, err := pipe.Exec(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(attribute.Int("pipeline.executed", len(cmds)))
    return nil
}

// TxPipeline 事务 Pipeline
func TxPipelineExample(ctx context.Context, rdb *redis.Client) error {
    ctx, span := otel.Tracer("redis").Start(ctx, "TxPipeline")
    defer span.End()

    // 创建事务 Pipeline
    pipe := rdb.TxPipeline()

    // 原子操作
    pipe.Incr(ctx, "counter")
    pipe.Expire(ctx, "counter", time.Hour)

    // 执行事务
    _, err := pipe.Exec(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}
```

### 4.2 发布订阅

```go
package pubsub

import (
    "context"
    "fmt"
    "time"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Publisher 发布者
type Publisher struct {
    client *redis.Client
    tracer trace.Tracer
}

func NewPublisher(client *redis.Client) *Publisher {
    return &Publisher{
        client: client,
        tracer: otel.Tracer("redis-publisher"),
    }
}

// Publish 发布消息
func (p *Publisher) Publish(ctx context.Context, channel string, message interface{}) error {
    ctx, span := p.tracer.Start(ctx, "Publisher.Publish",
        trace.WithAttributes(
            attribute.String("pubsub.channel", channel),
        ),
    )
    defer span.End()

    return p.client.Publish(ctx, channel, message).Err()
}

// Subscriber 订阅者
type Subscriber struct {
    client *redis.Client
    tracer trace.Tracer
}

func NewSubscriber(client *redis.Client) *Subscriber {
    return &Subscriber{
        client: client,
        tracer: otel.Tracer("redis-subscriber"),
    }
}

// Subscribe 订阅频道
func (s *Subscriber) Subscribe(ctx context.Context, channels []string, handler func(string, string) error) error {
    ctx, span := s.tracer.Start(ctx, "Subscriber.Subscribe",
        trace.WithAttributes(
            attribute.StringSlice("pubsub.channels", channels),
        ),
    )
    defer span.End()

    pubsub := s.client.Subscribe(ctx, channels...)
    defer pubsub.Close()

    // 等待订阅确认
    _, err := pubsub.Receive(ctx)
    if err != nil {
        span.RecordError(err)
        return err
    }

    // 处理消息
    ch := pubsub.Channel()
    for {
        select {
        case <-ctx.Done():
            return ctx.Err()
        case msg := <-ch:
            if msg == nil {
                return nil
            }

            messageSpan := trace.SpanFromContext(ctx).TracerProvider().Tracer("redis-subscriber").
                Start(ctx, "ProcessMessage",
                    trace.WithAttributes(
                        attribute.String("pubsub.channel", msg.Channel),
                    ),
                )

            if err := handler(msg.Channel, msg.Payload); err != nil {
                messageSpan.RecordError(err)
            }

            messageSpan.End()
        }
    }
}

// 使用示例
func ExamplePubSub() {
    ctx := context.Background()
    rdb := newRedisClient()

    // 发布者
    pub := NewPublisher(rdb)
    go func() {
        for i := 0; i < 10; i++ {
            pub.Publish(ctx, "notifications", fmt.Sprintf("Message %d", i))
            time.Sleep(time.Second)
        }
    }()

    // 订阅者
    sub := NewSubscriber(rdb)
    sub.Subscribe(ctx, []string{"notifications"}, func(channel, message string) error {
        fmt.Printf("Received from %s: %s\n", channel, message)
        return nil
    })
}
```

### 4.3 Lua 脚本

```go
package lua

import (
    "context"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// LuaScriptExecutor Lua 脚本执行器
type LuaScriptExecutor struct {
    client *redis.Client
    tracer trace.Tracer
}

func NewLuaScriptExecutor(client *redis.Client) *LuaScriptExecutor {
    return &LuaScriptExecutor{
        client: client,
        tracer: otel.Tracer("lua-script"),
    }
}

// AtomicIncrement 原子递增（带限制）
func (e *LuaScriptExecutor) AtomicIncrement(ctx context.Context, key string, maxValue int64) (int64, error) {
    ctx, span := e.tracer.Start(ctx, "LuaScript.AtomicIncrement",
        trace.WithAttributes(
            attribute.String("lua.key", key),
            attribute.Int64("lua.max_value", maxValue),
        ),
    )
    defer span.End()

    script := `
        local current = redis.call('GET', KEYS[1])
        if current == false then
            current = 0
        else
            current = tonumber(current)
        end

        local max_value = tonumber(ARGV[1])
        if current < max_value then
            redis.call('INCR', KEYS[1])
            return current + 1
        else
            return -1
        end
    `

    result, err := e.client.Eval(ctx, script, []string{key}, maxValue).Result()
    if err != nil {
        span.RecordError(err)
        return 0, err
    }

    value := result.(int64)
    span.SetAttributes(attribute.Int64("lua.result", value))

    return value, nil
}

// CompareAndSwap CAS 操作
func (e *LuaScriptExecutor) CompareAndSwap(ctx context.Context, key, oldValue, newValue string) (bool, error) {
    ctx, span := e.tracer.Start(ctx, "LuaScript.CompareAndSwap",
        trace.WithAttributes(
            attribute.String("lua.key", key),
        ),
    )
    defer span.End()

    script := `
        local current = redis.call('GET', KEYS[1])
        if current == ARGV[1] then
            redis.call('SET', KEYS[1], ARGV[2])
            return 1
        else
            return 0
        end
    `

    result, err := e.client.Eval(ctx, script, []string{key}, oldValue, newValue).Result()
    if err != nil {
        span.RecordError(err)
        return false, err
    }

    success := result.(int64) == 1
    span.SetAttributes(attribute.Bool("lua.success", success))

    return success, nil
}
```

---

## 5. Redis 集群

### 5.1 集群配置

```go
package cluster

import (
    "context"

    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/contrib/instrumentation/github.com/redis/go-redis/v9/redisotel"
)

// NewClusterClient 创建集群客户端
func NewClusterClient() *redis.ClusterClient {
    rdb := redis.NewClusterClient(&redis.ClusterOptions{
        Addrs: []string{
            "localhost:7000",
            "localhost:7001",
            "localhost:7002",
        },
        Password:     "",
        PoolSize:     100,
        MinIdleConns: 10,
        MaxRetries:   3,

        // 集群特定配置
        MaxRedirects:   3,
        ReadOnly:       false,
        RouteByLatency: true,
        RouteRandomly:  true,
    })

    // 启用 OTLP 追踪
    if err := redisotel.InstrumentTracing(rdb); err != nil {
        panic(err)
    }

    return rdb
}

// ClusterHealthCheck 集群健康检查
func ClusterHealthCheck(ctx context.Context, rdb *redis.ClusterClient) error {
    // 检查所有节点
    err := rdb.ForEachShard(ctx, func(ctx context.Context, shard *redis.Client) error {
        return shard.Ping(ctx).Err()
    })

    return err
}
```

### 5.2 Sentinel 高可用

```go
package sentinel

import (
    "github.com/redis/go-redis/v9"
    "go.opentelemetry.io/contrib/instrumentation/github.com/redis/go-redis/v9/redisotel"
)

// NewFailoverClient 创建 Sentinel 客户端
func NewFailoverClient() *redis.Client {
    rdb := redis.NewFailoverClient(&redis.FailoverOptions{
        MasterName:    "mymaster",
        SentinelAddrs: []string{
            "localhost:26379",
            "localhost:26380",
            "localhost:26381",
        },
        Password:     "",
        DB:           0,
        PoolSize:     100,
        MinIdleConns: 10,

        // Sentinel 特定配置
        SentinelPassword: "",
        RouteByLatency:   true,
        RouteRandomly:    false,
    })

    // 启用 OTLP 追踪
    if err := redisotel.InstrumentTracing(rdb); err != nil {
        panic(err)
    }

    return rdb
}
```

---

## 6. 性能优化

```text
✅ 连接池优化:
  - PoolSize: CPU核心数 * 2
  - MinIdleConns: 10-20
  - MaxRetries: 3
  - DialTimeout: 5s
  - ReadTimeout: 3s
  - WriteTimeout: 3s

✅ Pipeline 使用:
  - 批量操作使用 Pipeline
  - 减少网络往返
  - 注意内存使用

✅ 键设计:
  - 使用前缀区分业务
  - 避免过长的键名
  - 使用 Hash 代替多个键

✅ 过期策略:
  - 设置合理的 TTL
  - 使用 EXPIRE 而非 EXPIREAT
  - 避免大量键同时过期

✅ 内存优化:
  - 使用 Hash/List 减少内存
  - 压缩大值
  - 定期清理过期键
```

---

## 7. 生产部署

**Docker Compose**:

```yaml
version: '3.8'

services:
  redis:
    image: redis:7.2-alpine
    ports:
      - "6379:6379"
    command: >
      redis-server
      --maxmemory 512mb
      --maxmemory-policy allkeys-lru
      --save 900 1
      --save 300 10
      --appendonly yes
    volumes:
      - redis-data:/data
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 30s
      timeout: 3s
      retries: 3

volumes:
  redis-data:
```

**Kubernetes**:

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: redis
spec:
  serviceName: redis
  replicas: 1
  selector:
    matchLabels:
      app: redis
  template:
    metadata:
      labels:
        app: redis
    spec:
      containers:
      - name: redis
        image: redis:7.2-alpine
        ports:
        - containerPort: 6379
        resources:
          requests:
            cpu: "500m"
            memory: "512Mi"
          limits:
            cpu: "1000m"
            memory: "1Gi"
        volumeMounts:
        - name: data
          mountPath: /data
  volumeClaimTemplates:
  - metadata:
      name: data
    spec:
      accessModes: ["ReadWriteOnce"]
      resources:
        requests:
          storage: 10Gi
```

---

## 8. 最佳实践

```text
✅ 连接管理:
  - 复用 Redis 客户端实例
  - 使用连接池
  - 正确关闭连接

✅ 错误处理:
  - 区分 redis.Nil 和其他错误
  - 实现重试机制
  - 记录错误日志

✅ 数据一致性:
  - 使用事务保证原子性
  - 使用 Lua 脚本
  - 实现分布式锁

✅ 监控指标:
  - 命中率
  - 延迟
  - 连接数
  - 内存使用

✅ 安全:
  - 启用密码认证
  - 使用 TLS 连接
  - 限制网络访问
  - 定期备份
```

---

## 总结

Redis 与 OTLP 的完整集成提供了强大的缓存能力和完整的可观测性。

**关键要点**：

1. **高性能** - 100K+ ops/s
2. **丰富数据结构** - String/Hash/List/Set/ZSet
3. **完整的 OTLP 集成** - 追踪每个操作
4. **分布式特性** - 锁/限流/发布订阅
5. **生产就绪** - 集群/哨兵/持久化

**参考资源**：

- [Redis 官方文档](https://redis.io/docs/)
- [go-redis GitHub](https://github.com/redis/go-redis)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

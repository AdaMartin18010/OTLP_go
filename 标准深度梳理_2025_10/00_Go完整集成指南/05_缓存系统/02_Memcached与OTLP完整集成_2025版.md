# Memcached 与 OTLP 完整集成（2025版）

> **Memcached 版本**: v1.6+  
> **Go 客户端**: gomemcache  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [Memcached 与 OTLP 完整集成（2025版）](#memcached-与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. Memcached 概述](#1-memcached-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 与 Redis 对比](#12-与-redis-对比)
    - [1.3 适用场景](#13-适用场景)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础集成](#22-基础集成)
    - [2.3 OTLP 包装器](#23-otlp-包装器)
  - [3. 完整集成示例](#3-完整集成示例)
    - [3.1 缓存管理器](#31-缓存管理器)
    - [3.2 会话存储](#32-会话存储)
    - [3.3 页面缓存](#33-页面缓存)
  - [4. 高级特性](#4-高级特性)
    - [4.1 一致性哈希](#41-一致性哈希)
    - [4.2 缓存预热](#42-缓存预热)
    - [4.3 多级缓存](#43-多级缓存)
  - [5. 性能优化](#5-性能优化)
  - [6. 生产部署](#6-生产部署)
  - [7. 最佳实践](#7-最佳实践)
  - [总结](#总结)

---

## 1. Memcached 概述

### 1.1 核心特性

**Memcached** 是一个高性能的分布式内存对象缓存系统。

```text
🚀 核心特性:
  ✅ 简单设计 - 键值存储
  ✅ 高性能 - 极低延迟
  ✅ 分布式 - 客户端分片
  ✅ LRU 淘汰 - 自动清理
  ✅ 多线程 - 充分利用 CPU
  
⚡ 性能数据:
  - 读写: 200K+ ops/s (单节点)
  - 延迟: P99 < 0.5ms
  - 内存: 高效使用
  - 网络: 优化传输
```

### 1.2 与 Redis 对比

```text
┌─────────────┬──────────────┬─────────────┐
│   特性      │  Memcached   │   Redis     │
├─────────────┼──────────────┼─────────────┤
│ 数据结构    │  键值        │  丰富       │
│ 持久化      │  ❌          │  ✅         │
│ 复制        │  ❌          │  ✅         │
│ 事务        │  ❌          │  ✅         │
│ Lua 脚本    │  ❌          │  ✅         │
│ 发布订阅    │  ❌          │  ✅         │
│ 多线程      │  ✅          │  部分       │
│ 内存效率    │  高          │  中         │
│ 读性能      │  200K/s      │  100K/s     │
│ 写性能      │  150K/s      │  80K/s      │
│ 学习曲线    │  低          │  中         │
│ 适用场景    │  简单缓存    │  复杂场景   │
└─────────────┴──────────────┴─────────────┘
```

### 1.3 适用场景

```text
✅ 适合场景:
  - 简单键值缓存
  - 会话存储
  - 页面片段缓存
  - API 响应缓存
  - 数据库查询缓存
  - 高性能读写

❌ 不适合场景:
  - 需要持久化
  - 复杂数据结构
  - 需要事务
  - 数据复制
  - 发布订阅
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 gomemcache
go get -u github.com/bradfitz/gomemcache/memcache

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u go.opentelemetry.io/otel/sdk@v1.32.0
```

**go.mod 示例**：

```go
module github.com/yourorg/memcached-otlp-demo

go 1.25.1

require (
    github.com/bradfitz/gomemcache v0.0.0-20230905024940-24af94b03874
    go.opentelemetry.io/otel v1.32.0
    go.opentelemetry.io/otel/trace v1.32.0
    go.opentelemetry.io/otel/sdk v1.32.0
)
```

### 2.2 基础集成

```go
package main

import (
    "context"
    "fmt"
    "log"

    "github.com/bradfitz/gomemcache/memcache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
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
            semconv.ServiceName("memcached-cache"),
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

func main() {
    // 初始化追踪
    tp, err := initTracer()
    if err != nil {
        log.Fatal(err)
    }
    defer tp.Shutdown(context.Background())

    // 创建 Memcached 客户端
    mc := memcache.New("localhost:11211")

    ctx := context.Background()
    tracer := otel.Tracer("memcached-example")

    // Set 操作
    ctx, span := tracer.Start(ctx, "memcache.Set")
    err = mc.Set(&memcache.Item{
        Key:   "mykey",
        Value: []byte("myvalue"),
    })
    span.End()
    if err != nil {
        log.Fatal(err)
    }

    // Get 操作
    ctx, span = tracer.Start(ctx, "memcache.Get")
    item, err := mc.Get("mykey")
    span.End()
    if err != nil {
        log.Fatal(err)
    }

    fmt.Println("Value:", string(item.Value))
}
```

### 2.3 OTLP 包装器

```go
package memcached

import (
    "context"
    "fmt"
    "time"

    "github.com/bradfitz/gomemcache/memcache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TracedClient 带追踪的 Memcached 客户端
type TracedClient struct {
    *memcache.Client
    tracer trace.Tracer
}

func NewTracedClient(servers ...string) *TracedClient {
    return &TracedClient{
        Client: memcache.New(servers...),
        tracer: otel.Tracer("memcached"),
    }
}

// Get 获取键值
func (c *TracedClient) GetWithContext(ctx context.Context, key string) (*memcache.Item, error) {
    ctx, span := c.tracer.Start(ctx, "memcache.Get",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "memcached"),
            attribute.String("db.operation", "GET"),
            attribute.String("db.key", key),
        ),
    )
    defer span.End()

    start := time.Now()
    item, err := c.Client.Get(key)
    duration := time.Since(start)

    span.SetAttributes(
        attribute.Float64("db.duration_ms", float64(duration.Microseconds())/1000.0),
    )

    if err == memcache.ErrCacheMiss {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        span.SetStatus(codes.Ok, "cache miss")
        return nil, err
    }

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("cache.value.size", len(item.Value)),
    )
    span.SetStatus(codes.Ok, "")

    return item, nil
}

// Set 设置键值
func (c *TracedClient) SetWithContext(ctx context.Context, item *memcache.Item) error {
    ctx, span := c.tracer.Start(ctx, "memcache.Set",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "memcached"),
            attribute.String("db.operation", "SET"),
            attribute.String("db.key", item.Key),
            attribute.Int("cache.value.size", len(item.Value)),
        ),
    )
    defer span.End()

    if item.Expiration > 0 {
        span.SetAttributes(attribute.Int64("cache.ttl_seconds", int64(item.Expiration)))
    }

    start := time.Now()
    err := c.Client.Set(item)
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

// Delete 删除键
func (c *TracedClient) DeleteWithContext(ctx context.Context, key string) error {
    ctx, span := c.tracer.Start(ctx, "memcache.Delete",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "memcached"),
            attribute.String("db.operation", "DELETE"),
            attribute.String("db.key", key),
        ),
    )
    defer span.End()

    err := c.Client.Delete(key)
    if err != nil && err != memcache.ErrCacheMiss {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// GetMulti 批量获取
func (c *TracedClient) GetMultiWithContext(ctx context.Context, keys []string) (map[string]*memcache.Item, error) {
    ctx, span := c.tracer.Start(ctx, "memcache.GetMulti",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "memcached"),
            attribute.String("db.operation", "GET_MULTI"),
            attribute.Int("cache.keys.count", len(keys)),
        ),
    )
    defer span.End()

    start := time.Now()
    items, err := c.Client.GetMulti(keys)
    duration := time.Since(start)

    span.SetAttributes(
        attribute.Float64("db.duration_ms", float64(duration.Microseconds())/1000.0),
        attribute.Int("cache.items.found", len(items)),
        attribute.Float64("cache.hit_rate", float64(len(items))/float64(len(keys))),
    )

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetStatus(codes.Ok, "")
    return items, nil
}

// Increment 原子递增
func (c *TracedClient) IncrementWithContext(ctx context.Context, key string, delta uint64) (uint64, error) {
    ctx, span := c.tracer.Start(ctx, "memcache.Increment",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "memcached"),
            attribute.String("db.operation", "INCR"),
            attribute.String("db.key", key),
            attribute.Int64("cache.delta", int64(delta)),
        ),
    )
    defer span.End()

    newValue, err := c.Client.Increment(key, delta)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return 0, err
    }

    span.SetAttributes(attribute.Int64("cache.new_value", int64(newValue)))
    span.SetStatus(codes.Ok, "")

    return newValue, nil
}

// Decrement 原子递减
func (c *TracedClient) DecrementWithContext(ctx context.Context, key string, delta uint64) (uint64, error) {
    ctx, span := c.tracer.Start(ctx, "memcache.Decrement",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "memcached"),
            attribute.String("db.operation", "DECR"),
            attribute.String("db.key", key),
            attribute.Int64("cache.delta", int64(delta)),
        ),
    )
    defer span.End()

    newValue, err := c.Client.Decrement(key, delta)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return 0, err
    }

    span.SetAttributes(attribute.Int64("cache.new_value", int64(newValue)))
    span.SetStatus(codes.Ok, "")

    return newValue, nil
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

    "github.com/bradfitz/gomemcache/memcache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// MemcacheManager 缓存管理器
type MemcacheManager struct {
    client *TracedClient
    tracer trace.Tracer
    prefix string
}

func NewMemcacheManager(servers []string, prefix string) *MemcacheManager {
    return &MemcacheManager{
        client: NewTracedClient(servers...),
        tracer: otel.Tracer("memcache-manager"),
        prefix: prefix,
    }
}

// Get 获取缓存
func (m *MemcacheManager) Get(ctx context.Context, key string, dest interface{}) error {
    ctx, span := m.tracer.Start(ctx, "MemcacheManager.Get",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    fullKey := m.prefix + key
    item, err := m.client.GetWithContext(ctx, fullKey)
    if err == memcache.ErrCacheMiss {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        return ErrCacheMiss
    }
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("cache.value.size", len(item.Value)),
    )

    if err := json.Unmarshal(item.Value, dest); err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// Set 设置缓存
func (m *MemcacheManager) Set(ctx context.Context, key string, value interface{}, ttl time.Duration) error {
    ctx, span := m.tracer.Start(ctx, "MemcacheManager.Set",
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
    return m.client.SetWithContext(ctx, &memcache.Item{
        Key:        fullKey,
        Value:      data,
        Expiration: int32(ttl.Seconds()),
    })
}

// Delete 删除缓存
func (m *MemcacheManager) Delete(ctx context.Context, key string) error {
    ctx, span := m.tracer.Start(ctx, "MemcacheManager.Delete",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    fullKey := m.prefix + key
    return m.client.DeleteWithContext(ctx, fullKey)
}

// GetOrLoad 获取或加载
func (m *MemcacheManager) GetOrLoad(ctx context.Context, key string, ttl time.Duration, loader func(context.Context) (interface{}, error)) (interface{}, error) {
    ctx, span := m.tracer.Start(ctx, "MemcacheManager.GetOrLoad")
    defer span.End()

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

    span.SetAttributes(attribute.Bool("cache.loaded_from_cache", false))
    result, err = loader(ctx)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    if err := m.Set(ctx, key, result, ttl); err != nil {
        span.RecordError(fmt.Errorf("failed to set cache: %w", err))
    }

    return result, nil
}

// GetMulti 批量获取
func (m *MemcacheManager) GetMulti(ctx context.Context, keys []string) (map[string]interface{}, error) {
    ctx, span := m.tracer.Start(ctx, "MemcacheManager.GetMulti",
        trace.WithAttributes(
            attribute.Int("cache.keys.count", len(keys)),
        ),
    )
    defer span.End()

    fullKeys := make([]string, len(keys))
    for i, key := range keys {
        fullKeys[i] = m.prefix + key
    }

    items, err := m.client.GetMultiWithContext(ctx, fullKeys)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    result := make(map[string]interface{})
    for origKey, fullKey := range keys {
        if item, ok := items[m.prefix+fullKey]; ok {
            var value interface{}
            if err := json.Unmarshal(item.Value, &value); err == nil {
                result[keys[origKey]] = value
            }
        }
    }

    span.SetAttributes(
        attribute.Int("cache.items.found", len(result)),
        attribute.Float64("cache.hit_rate", float64(len(result))/float64(len(keys))),
    )

    return result, nil
}

var ErrCacheMiss = fmt.Errorf("cache miss")
```

### 3.2 会话存储

```go
package session

import (
    "context"
    "encoding/json"
    "fmt"
    "time"

    "github.com/bradfitz/gomemcache/memcache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// Session 会话数据
type Session struct {
    ID        string                 `json:"id"`
    UserID    int                    `json:"user_id"`
    Data      map[string]interface{} `json:"data"`
    CreatedAt time.Time              `json:"created_at"`
    ExpiresAt time.Time              `json:"expires_at"`
}

// SessionStore 会话存储
type SessionStore struct {
    client *TracedClient
    tracer trace.Tracer
    ttl    time.Duration
}

func NewSessionStore(servers []string, ttl time.Duration) *SessionStore {
    return &SessionStore{
        client: NewTracedClient(servers...),
        tracer: otel.Tracer("session-store"),
        ttl:    ttl,
    }
}

// Create 创建会话
func (s *SessionStore) Create(ctx context.Context, session *Session) error {
    ctx, span := s.tracer.Start(ctx, "SessionStore.Create",
        trace.WithAttributes(
            attribute.String("session.id", session.ID),
            attribute.Int("session.user_id", session.UserID),
        ),
    )
    defer span.End()

    session.CreatedAt = time.Now()
    session.ExpiresAt = time.Now().Add(s.ttl)

    data, err := json.Marshal(session)
    if err != nil {
        span.RecordError(err)
        return err
    }

    key := fmt.Sprintf("session:%s", session.ID)
    return s.client.SetWithContext(ctx, &memcache.Item{
        Key:        key,
        Value:      data,
        Expiration: int32(s.ttl.Seconds()),
    })
}

// Get 获取会话
func (s *SessionStore) Get(ctx context.Context, sessionID string) (*Session, error) {
    ctx, span := s.tracer.Start(ctx, "SessionStore.Get",
        trace.WithAttributes(
            attribute.String("session.id", sessionID),
        ),
    )
    defer span.End()

    key := fmt.Sprintf("session:%s", sessionID)
    item, err := s.client.GetWithContext(ctx, key)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    var session Session
    if err := json.Unmarshal(item.Value, &session); err != nil {
        span.RecordError(err)
        return nil, err
    }

    // 检查是否过期
    if time.Now().After(session.ExpiresAt) {
        span.SetAttributes(attribute.Bool("session.expired", true))
        s.client.DeleteWithContext(ctx, key)
        return nil, ErrSessionExpired
    }

    span.SetAttributes(
        attribute.Int("session.user_id", session.UserID),
        attribute.Bool("session.valid", true),
    )

    return &session, nil
}

// Update 更新会话
func (s *SessionStore) Update(ctx context.Context, session *Session) error {
    ctx, span := s.tracer.Start(ctx, "SessionStore.Update",
        trace.WithAttributes(
            attribute.String("session.id", session.ID),
        ),
    )
    defer span.End()

    // 延长过期时间
    session.ExpiresAt = time.Now().Add(s.ttl)

    data, err := json.Marshal(session)
    if err != nil {
        span.RecordError(err)
        return err
    }

    key := fmt.Sprintf("session:%s", session.ID)
    return s.client.SetWithContext(ctx, &memcache.Item{
        Key:        key,
        Value:      data,
        Expiration: int32(s.ttl.Seconds()),
    })
}

// Delete 删除会话
func (s *SessionStore) Delete(ctx context.Context, sessionID string) error {
    ctx, span := s.tracer.Start(ctx, "SessionStore.Delete",
        trace.WithAttributes(
            attribute.String("session.id", sessionID),
        ),
    )
    defer span.End()

    key := fmt.Sprintf("session:%s", sessionID)
    return s.client.DeleteWithContext(ctx, key)
}

var ErrSessionExpired = fmt.Errorf("session expired")

// 使用示例
func ExampleSessionStore() {
    ctx := context.Background()
    store := NewSessionStore([]string{"localhost:11211"}, 30*time.Minute)

    // 创建会话
    session := &Session{
        ID:     "session-123",
        UserID: 456,
        Data: map[string]interface{}{
            "username": "alice",
            "role":     "admin",
        },
    }

    if err := store.Create(ctx, session); err != nil {
        log.Fatal(err)
    }

    // 获取会话
    retrieved, err := store.Get(ctx, "session-123")
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("Session: %+v\n", retrieved)

    // 更新会话
    retrieved.Data["last_activity"] = time.Now()
    if err := store.Update(ctx, retrieved); err != nil {
        log.Fatal(err)
    }

    // 删除会话
    if err := store.Delete(ctx, "session-123"); err != nil {
        log.Fatal(err)
    }
}
```

### 3.3 页面缓存

```go
package pagecache

import (
    "context"
    "crypto/md5"
    "fmt"
    "net/http"
    "time"

    "github.com/bradfitz/gomemcache/memcache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// PageCache 页面缓存
type PageCache struct {
    client *TracedClient
    tracer trace.Tracer
    ttl    time.Duration
}

func NewPageCache(servers []string, ttl time.Duration) *PageCache {
    return &PageCache{
        client: NewTracedClient(servers...),
        tracer: otel.Tracer("page-cache"),
        ttl:    ttl,
    }
}

// CacheKey 生成缓存键
func (p *PageCache) CacheKey(r *http.Request) string {
    // 基于 URL 和查询参数生成键
    key := fmt.Sprintf("%s?%s", r.URL.Path, r.URL.RawQuery)
    hash := md5.Sum([]byte(key))
    return fmt.Sprintf("page:%x", hash)
}

// Get 获取缓存的页面
func (p *PageCache) Get(ctx context.Context, r *http.Request) ([]byte, bool) {
    ctx, span := p.tracer.Start(ctx, "PageCache.Get",
        trace.WithAttributes(
            attribute.String("http.url", r.URL.String()),
        ),
    )
    defer span.End()

    key := p.CacheKey(r)
    item, err := p.client.GetWithContext(ctx, key)
    if err != nil {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        return nil, false
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("cache.page.size", len(item.Value)),
    )

    return item.Value, true
}

// Set 设置页面缓存
func (p *PageCache) Set(ctx context.Context, r *http.Request, content []byte) error {
    ctx, span := p.tracer.Start(ctx, "PageCache.Set",
        trace.WithAttributes(
            attribute.String("http.url", r.URL.String()),
            attribute.Int("cache.page.size", len(content)),
        ),
    )
    defer span.End()

    key := p.CacheKey(r)
    return p.client.SetWithContext(ctx, &memcache.Item{
        Key:        key,
        Value:      content,
        Expiration: int32(p.ttl.Seconds()),
    })
}

// Middleware 缓存中间件
func (p *PageCache) Middleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        ctx, span := p.tracer.Start(ctx, "PageCache.Middleware",
            trace.WithAttributes(
                attribute.String("http.method", r.Method),
                attribute.String("http.url", r.URL.String()),
            ),
        )
        defer span.End()

        // 只缓存 GET 请求
        if r.Method != http.MethodGet {
            next.ServeHTTP(w, r.WithContext(ctx))
            return
        }

        // 尝试从缓存获取
        if content, ok := p.Get(ctx, r); ok {
            span.SetAttributes(
                attribute.Bool("cache.served_from_cache", true),
            )
            w.Header().Set("X-Cache", "HIT")
            w.Write(content)
            return
        }

        // 缓存未命中，执行请求并缓存响应
        span.SetAttributes(attribute.Bool("cache.served_from_cache", false))
        w.Header().Set("X-Cache", "MISS")

        // 创建响应记录器
        rec := &responseRecorder{
            ResponseWriter: w,
            body:           make([]byte, 0),
        }

        next.ServeHTTP(rec, r.WithContext(ctx))

        // 只缓存成功的响应
        if rec.statusCode == http.StatusOK {
            p.Set(ctx, r, rec.body)
        }
    })
}

// responseRecorder 响应记录器
type responseRecorder struct {
    http.ResponseWriter
    statusCode int
    body       []byte
}

func (r *responseRecorder) WriteHeader(statusCode int) {
    r.statusCode = statusCode
    r.ResponseWriter.WriteHeader(statusCode)
}

func (r *responseRecorder) Write(b []byte) (int, error) {
    r.body = append(r.body, b...)
    return r.ResponseWriter.Write(b)
}

// 使用示例
func ExamplePageCache() {
    cache := NewPageCache([]string{"localhost:11211"}, 5*time.Minute)

    http.Handle("/", cache.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        // 模拟耗时操作
        time.Sleep(100 * time.Millisecond)
        w.Write([]byte("Hello, World!"))
    })))

    log.Println("Server starting on :8080")
    http.ListenAndServe(":8080", nil)
}
```

---

## 4. 高级特性

### 4.1 一致性哈希

```go
package consistent

import (
    "hash/crc32"
    "sort"
    "sync"
)

// ConsistentHash 一致性哈希
type ConsistentHash struct {
    replicas int
    keys     []int
    hashMap  map[int]string
    mu       sync.RWMutex
}

func NewConsistentHash(replicas int) *ConsistentHash {
    return &ConsistentHash{
        replicas: replicas,
        hashMap:  make(map[int]string),
    }
}

// Add 添加节点
func (c *ConsistentHash) Add(nodes ...string) {
    c.mu.Lock()
    defer c.mu.Unlock()

    for _, node := range nodes {
        for i := 0; i < c.replicas; i++ {
            hash := int(crc32.ChecksumIEEE([]byte(fmt.Sprintf("%s:%d", node, i))))
            c.keys = append(c.keys, hash)
            c.hashMap[hash] = node
        }
    }

    sort.Ints(c.keys)
}

// Get 获取节点
func (c *ConsistentHash) Get(key string) string {
    c.mu.RLock()
    defer c.mu.RUnlock()

    if len(c.keys) == 0 {
        return ""
    }

    hash := int(crc32.ChecksumIEEE([]byte(key)))

    // 二分查找
    idx := sort.Search(len(c.keys), func(i int) bool {
        return c.keys[i] >= hash
    })

    if idx == len(c.keys) {
        idx = 0
    }

    return c.hashMap[c.keys[idx]]
}
```

### 4.2 缓存预热

```go
package warmup

import (
    "context"
    "log"
    "sync"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// CacheWarmer 缓存预热器
type CacheWarmer struct {
    cache  *MemcacheManager
    tracer trace.Tracer
}

func NewCacheWarmer(cache *MemcacheManager) *CacheWarmer {
    return &CacheWarmer{
        cache:  cache,
        tracer: otel.Tracer("cache-warmer"),
    }
}

// WarmUp 预热缓存
func (w *CacheWarmer) WarmUp(ctx context.Context, keys []string, loader func(string) (interface{}, error)) error {
    ctx, span := w.tracer.Start(ctx, "CacheWarmer.WarmUp",
        trace.WithAttributes(
            attribute.Int("warmup.keys.count", len(keys)),
        ),
    )
    defer span.End()

    var wg sync.WaitGroup
    errCh := make(chan error, len(keys))

    // 并发预热
    for _, key := range keys {
        wg.Add(1)
        go func(k string) {
            defer wg.Done()

            value, err := loader(k)
            if err != nil {
                errCh <- err
                return
            }

            if err := w.cache.Set(ctx, k, value, time.Hour); err != nil {
                errCh <- err
            }
        }(key)
    }

    wg.Wait()
    close(errCh)

    // 收集错误
    for err := range errCh {
        log.Printf("Warmup error: %v", err)
    }

    span.SetAttributes(attribute.Bool("warmup.completed", true))
    return nil
}
```

### 4.3 多级缓存

```go
package multilevel

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// MultiLevelCache 多级缓存
type MultiLevelCache struct {
    l1     *sync.Map // 本地缓存
    l2     *MemcacheManager // Memcached
    tracer trace.Tracer
}

func NewMultiLevelCache(memcache *MemcacheManager) *MultiLevelCache {
    return &MultiLevelCache{
        l1:     &sync.Map{},
        l2:     memcache,
        tracer: otel.Tracer("multilevel-cache"),
    }
}

// Get 获取缓存（L1 -> L2）
func (m *MultiLevelCache) Get(ctx context.Context, key string, dest interface{}) error {
    ctx, span := m.tracer.Start(ctx, "MultiLevelCache.Get",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    // 尝试 L1 缓存
    if value, ok := m.l1.Load(key); ok {
        span.SetAttributes(
            attribute.String("cache.level", "L1"),
            attribute.Bool("cache.hit", true),
        )
        *dest.(*interface{}) = value
        return nil
    }

    // 尝试 L2 缓存
    if err := m.l2.Get(ctx, key, dest); err == nil {
        span.SetAttributes(
            attribute.String("cache.level", "L2"),
            attribute.Bool("cache.hit", true),
        )
        // 回填 L1
        m.l1.Store(key, *dest.(*interface{}))
        return nil
    }

    span.SetAttributes(attribute.Bool("cache.hit", false))
    return ErrCacheMiss
}

// Set 设置缓存（L1 + L2）
func (m *MultiLevelCache) Set(ctx context.Context, key string, value interface{}, ttl time.Duration) error {
    ctx, span := m.tracer.Start(ctx, "MultiLevelCache.Set")
    defer span.End()

    // 写入 L1
    m.l1.Store(key, value)

    // 写入 L2
    return m.l2.Set(ctx, key, value, ttl)
}

// Delete 删除缓存
func (m *MultiLevelCache) Delete(ctx context.Context, key string) error {
    m.l1.Delete(key)
    return m.l2.Delete(ctx, key)
}
```

---

## 5. 性能优化

```text
✅ 连接池优化:
  - 使用连接池减少连接开销
  - 设置合理的超时时间
  - 启用 TCP keepalive

✅ 批量操作:
  - 使用 GetMulti 批量获取
  - 减少网络往返

✅ 键设计:
  - 使用短键名
  - 避免特殊字符
  - 使用前缀区分业务

✅ 序列化:
  - 使用高效的序列化格式
  - 压缩大值
  - 考虑 Protocol Buffers

✅ 过期策略:
  - 设置合理的 TTL
  - 避免永久缓存
  - 定期清理

✅ 内存管理:
  - 监控内存使用
  - 设置最大内存
  - 使用 LRU 淘汰
```

---

## 6. 生产部署

**Docker Compose**:

```yaml
version: '3.8'

services:
  memcached-1:
    image: memcached:1.6-alpine
    ports:
      - "11211:11211"
    command: memcached -m 256 -c 1024
    healthcheck:
      test: ["CMD", "nc", "-z", "localhost", "11211"]
      interval: 30s
      timeout: 3s
      retries: 3

  memcached-2:
    image: memcached:1.6-alpine
    ports:
      - "11212:11211"
    command: memcached -m 256 -c 1024

  memcached-3:
    image: memcached:1.6-alpine
    ports:
      - "11213:11211"
    command: memcached -m 256 -c 1024
```

**Kubernetes**:

```yaml
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: memcached
spec:
  serviceName: memcached
  replicas: 3
  selector:
    matchLabels:
      app: memcached
  template:
    metadata:
      labels:
        app: memcached
    spec:
      containers:
      - name: memcached
        image: memcached:1.6-alpine
        args:
          - memcached
          - -m 256
          - -c 1024
        ports:
        - containerPort: 11211
        resources:
          requests:
            cpu: "250m"
            memory: "256Mi"
          limits:
            cpu: "500m"
            memory: "512Mi"
```

---

## 7. 最佳实践

```text
✅ 使用场景:
  - 简单键值缓存
  - 高性能要求
  - 无需持久化

✅ 数据设计:
  - 序列化为 JSON/MsgPack
  - 压缩大数据
  - 设置合理 TTL

✅ 错误处理:
  - 区分 CacheMiss 和错误
  - 实现降级策略
  - 记录错误日志

✅ 监控指标:
  - 命中率
  - 延迟
  - 内存使用
  - 连接数

✅ 安全:
  - 限制网络访问
  - 使用防火墙
  - 避免缓存敏感数据
```

---

## 总结

Memcached 是一个简单高效的缓存解决方案，适合对性能有极致要求的场景。

**关键要点**：

1. **简单高效** - 键值存储
2. **极致性能** - 200K+ ops/s
3. **分布式** - 客户端分片
4. **完整追踪** - OTLP 集成
5. **生产就绪** - 久经考验

**参考资源**：

- [Memcached 官方文档](https://memcached.org/)
- [gomemcache GitHub](https://github.com/bradfitz/gomemcache)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

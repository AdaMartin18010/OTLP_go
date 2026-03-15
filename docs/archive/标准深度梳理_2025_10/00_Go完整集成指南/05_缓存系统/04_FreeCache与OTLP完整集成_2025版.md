# FreeCache 与 OTLP 完整集成（2025版）

> **FreeCache 版本**: v1.2+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [FreeCache 与 OTLP 完整集成（2025版）](#freecache-与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. FreeCache 概述](#1-freecache-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 性能优势](#12-性能优势)
    - [1.3 适用场景](#13-适用场景)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础集成](#22-基础集成)
    - [2.3 OTLP 包装器](#23-otlp-包装器)
  - [3. 完整集成示例](#3-完整集成示例)
    - [3.1 本地缓存管理器](#31-本地缓存管理器)
    - [3.2 热点数据缓存](#32-热点数据缓存)
    - [3.3 API 响应缓存](#33-api-响应缓存)
  - [4. 高级特性](#4-高级特性)
    - [4.1 零 GC 优化](#41-零-gc-优化)
    - [4.2 统计监控](#42-统计监控)
    - [4.3 淘汰策略](#43-淘汰策略)
  - [5. 性能优化](#5-性能优化)
  - [6. 与其他缓存对比](#6-与其他缓存对比)
  - [7. 最佳实践](#7-最佳实践)
  - [总结](#总结)

---

## 1. FreeCache 概述

### 1.1 核心特性

**FreeCache** 是一个零 GC 开销的高性能内存缓存库。

```text
🚀 核心特性:
  ✅ 零 GC 开销 - 内存直接管理
  ✅ 高性能 - 超低延迟
  ✅ 线程安全 - 并发友好
  ✅ LRU 淘汰 - 自动清理
  ✅ TTL 支持 - 过期删除
  ✅ 简单 API - 易于使用
  
⚡ 性能数据:
  - 读: 10M+ ops/s
  - 写: 5M+ ops/s
  - 延迟: P99 < 100μs
  - GC 暂停: ~0ms
```

### 1.2 性能优势

```text
┌──────────────┬──────────────┬─────────────┬─────────────┐
│   指标       │  FreeCache   │  sync.Map   │  BigCache   │
├──────────────┼──────────────┼─────────────┼─────────────┤
│ 读性能       │  10M ops/s   │  20M ops/s  │  5M ops/s   │
│ 写性能       │  5M ops/s    │  5M ops/s   │  3M ops/s   │
│ 延迟(P99)    │  <100μs      │  <50μs      │  <200μs     │
│ GC 压力      │  零          │  高         │  零         │
│ 内存效率     │  高          │  中         │  高         │
│ TTL 支持     │  ✅          │  ❌         │  ✅         │
│ LRU 淘汰     │  ✅          │  ❌         │  ❌         │
│ 并发安全     │  ✅          │  ✅         │  ✅         │
│ 适用场景     │  高性能缓存  │  通用       │  大对象缓存 │
└──────────────┴──────────────┴─────────────┴─────────────┘
```

### 1.3 适用场景

```text
✅ 适合场景:
  - 高并发缓存
  - 热点数据缓存
  - API 响应缓存
  - 会话缓存
  - 对象池
  - 速率限制
  - 避免 GC 压力

❌ 不适合场景:
  - 需要持久化
  - 分布式缓存
  - 超大对象（>1MB）
  - 复杂查询
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 FreeCache
go get -u github.com/coocood/freecache

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u go.opentelemetry.io/otel/sdk@v1.32.0
```

**go.mod 示例**：

```go
module github.com/yourorg/freecache-otlp-demo

go 1.25.1

require (
    github.com/coocood/freecache v1.2.4
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

    "github.com/coocood/freecache"
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
            semconv.ServiceName("freecache-app"),
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

    // 创建缓存 (100MB)
    cache := freecache.NewCache(100 * 1024 * 1024)

    ctx := context.Background()
    tracer := otel.Tracer("freecache-example")

    // 设置缓存
    ctx, span := tracer.Start(ctx, "cache.Set")
    err = cache.Set([]byte("key"), []byte("value"), 3600)
    span.End()
    if err != nil {
        log.Fatal(err)
    }

    // 获取缓存
    ctx, span = tracer.Start(ctx, "cache.Get")
    value, err := cache.Get([]byte("key"))
    span.End()
    if err != nil {
        log.Fatal(err)
    }

    fmt.Println("Value:", string(value))

    // 查看统计
    fmt.Printf("Hit count: %d\n", cache.HitCount())
    fmt.Printf("Miss count: %d\n", cache.MissCount())
    fmt.Printf("Entry count: %d\n", cache.EntryCount())
}
```

### 2.3 OTLP 包装器

```go
package cache

import (
    "context"
    "time"

    "github.com/coocood/freecache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TracedCache 带追踪的 FreeCache
type TracedCache struct {
    cache  *freecache.Cache
    tracer trace.Tracer
}

func NewTracedCache(size int) *TracedCache {
    return &TracedCache{
        cache:  freecache.NewCache(size),
        tracer: otel.Tracer("freecache"),
    }
}

// Get 获取缓存
func (c *TracedCache) Get(ctx context.Context, key []byte) ([]byte, error) {
    ctx, span := c.tracer.Start(ctx, "freecache.Get",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("cache.system", "freecache"),
            attribute.String("cache.operation", "GET"),
            attribute.Int("cache.key.size", len(key)),
        ),
    )
    defer span.End()

    start := time.Now()
    value, err := c.cache.Get(key)
    duration := time.Since(start)

    span.SetAttributes(
        attribute.Float64("cache.duration_us", float64(duration.Microseconds())),
    )

    if err == freecache.ErrNotFound {
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
        attribute.Int("cache.value.size", len(value)),
    )
    span.SetStatus(codes.Ok, "")

    return value, nil
}

// Set 设置缓存
func (c *TracedCache) Set(ctx context.Context, key, value []byte, expireSeconds int) error {
    ctx, span := c.tracer.Start(ctx, "freecache.Set",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("cache.system", "freecache"),
            attribute.String("cache.operation", "SET"),
            attribute.Int("cache.key.size", len(key)),
            attribute.Int("cache.value.size", len(value)),
            attribute.Int("cache.ttl_seconds", expireSeconds),
        ),
    )
    defer span.End()

    start := time.Now()
    err := c.cache.Set(key, value, expireSeconds)
    duration := time.Since(start)

    span.SetAttributes(
        attribute.Float64("cache.duration_us", float64(duration.Microseconds())),
    )

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// Del 删除缓存
func (c *TracedCache) Del(ctx context.Context, key []byte) bool {
    ctx, span := c.tracer.Start(ctx, "freecache.Del",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("cache.system", "freecache"),
            attribute.String("cache.operation", "DEL"),
        ),
    )
    defer span.End()

    affected := c.cache.Del(key)
    span.SetAttributes(attribute.Bool("cache.deleted", affected))

    return affected
}

// Clear 清空缓存
func (c *TracedCache) Clear(ctx context.Context) {
    ctx, span := c.tracer.Start(ctx, "freecache.Clear")
    defer span.End()

    c.cache.Clear()
}

// Stats 获取统计信息
func (c *TracedCache) Stats(ctx context.Context) map[string]int64 {
    ctx, span := c.tracer.Start(ctx, "freecache.Stats")
    defer span.End()

    stats := map[string]int64{
        "hit_count":        c.cache.HitCount(),
        "miss_count":       c.cache.MissCount(),
        "entry_count":      c.cache.EntryCount(),
        "evict_count":      c.cache.EvacuateCount(),
        "expired_count":    c.cache.ExpiredCount(),
        "average_access":   c.cache.AverageAccessTime(),
        "hit_rate":         int64(c.cache.HitRate() * 100),
        "lookup_count":     c.cache.LookupCount(),
        "overwrite_count":  c.cache.OverwriteCount(),
    }

    for k, v := range stats {
        span.SetAttributes(attribute.Int64("cache."+k, v))
    }

    return stats
}

// GetOrLoad 获取或加载
func (c *TracedCache) GetOrLoad(ctx context.Context, key []byte, ttl int, loader func(context.Context) ([]byte, error)) ([]byte, error) {
    ctx, span := c.tracer.Start(ctx, "TracedCache.GetOrLoad")
    defer span.End()

    value, err := c.Get(ctx, key)
    if err == nil {
        span.SetAttributes(attribute.Bool("cache.loaded_from_cache", true))
        return value, nil
    }

    if err != freecache.ErrNotFound {
        span.RecordError(err)
        return nil, err
    }

    span.SetAttributes(attribute.Bool("cache.loaded_from_cache", false))
    value, err = loader(ctx)
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    if err := c.Set(ctx, key, value, ttl); err != nil {
        span.RecordError(err)
    }

    return value, nil
}
```

---

## 3. 完整集成示例

### 3.1 本地缓存管理器

```go
package cache

import (
    "context"
    "encoding/json"
    "fmt"
    "time"

    "github.com/coocood/freecache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// LocalCacheManager 本地缓存管理器
type LocalCacheManager struct {
    cache  *TracedCache
    tracer trace.Tracer
    prefix string
}

func NewLocalCacheManager(size int, prefix string) *LocalCacheManager {
    return &LocalCacheManager{
        cache:  NewTracedCache(size),
        tracer: otel.Tracer("local-cache-manager"),
        prefix: prefix,
    }
}

// Get 获取缓存
func (m *LocalCacheManager) Get(ctx context.Context, key string, dest interface{}) error {
    ctx, span := m.tracer.Start(ctx, "LocalCacheManager.Get",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    fullKey := []byte(m.prefix + key)
    data, err := m.cache.Get(ctx, fullKey)
    if err == freecache.ErrNotFound {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        return ErrCacheMiss
    }
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("cache.value.size", len(data)),
    )

    if err := json.Unmarshal(data, dest); err != nil {
        span.RecordError(err)
        return err
    }

    return nil
}

// Set 设置缓存
func (m *LocalCacheManager) Set(ctx context.Context, key string, value interface{}, ttl time.Duration) error {
    ctx, span := m.tracer.Start(ctx, "LocalCacheManager.Set",
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

    fullKey := []byte(m.prefix + key)
    return m.cache.Set(ctx, fullKey, data, int(ttl.Seconds()))
}

// Delete 删除缓存
func (m *LocalCacheManager) Delete(ctx context.Context, key string) bool {
    ctx, span := m.tracer.Start(ctx, "LocalCacheManager.Delete")
    defer span.End()

    fullKey := []byte(m.prefix + key)
    return m.cache.Del(ctx, fullKey)
}

// GetOrLoad 获取或加载
func (m *LocalCacheManager) GetOrLoad(ctx context.Context, key string, ttl time.Duration, loader func(context.Context) (interface{}, error)) (interface{}, error) {
    ctx, span := m.tracer.Start(ctx, "LocalCacheManager.GetOrLoad")
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

// Stats 获取统计信息
func (m *LocalCacheManager) Stats(ctx context.Context) map[string]int64 {
    return m.cache.Stats(ctx)
}

// Clear 清空缓存
func (m *LocalCacheManager) Clear(ctx context.Context) {
    m.cache.Clear(ctx)
}

var ErrCacheMiss = fmt.Errorf("cache miss")

// 使用示例
func ExampleLocalCacheManager() {
    ctx := context.Background()

    // 创建 100MB 缓存
    cache := NewLocalCacheManager(100*1024*1024, "app:")

    // 设置缓存
    type User struct {
        ID   int    `json:"id"`
        Name string `json:"name"`
    }

    user := User{ID: 123, Name: "Alice"}
    if err := cache.Set(ctx, "user:123", user, time.Hour); err != nil {
        log.Fatal(err)
    }

    // 获取缓存
    var retrieved User
    if err := cache.Get(ctx, "user:123", &retrieved); err != nil {
        log.Fatal(err)
    }

    fmt.Printf("User: %+v\n", retrieved)

    // 查看统计
    stats := cache.Stats(ctx)
    fmt.Printf("Cache stats: %+v\n", stats)
}
```

### 3.2 热点数据缓存

```go
package hotspot

import (
    "context"
    "sync"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// HotspotCache 热点数据缓存
type HotspotCache struct {
    cache       *TracedCache
    tracer      trace.Tracer
    accessCount sync.Map // 访问计数
    threshold   int64    // 热点阈值
}

func NewHotspotCache(size int, threshold int64) *HotspotCache {
    return &HotspotCache{
        cache:     NewTracedCache(size),
        tracer:    otel.Tracer("hotspot-cache"),
        threshold: threshold,
    }
}

// Get 获取数据（跟踪热点）
func (h *HotspotCache) Get(ctx context.Context, key []byte) ([]byte, bool) {
    ctx, span := h.tracer.Start(ctx, "HotspotCache.Get")
    defer span.End()

    // 增加访问计数
    countVal, _ := h.accessCount.LoadOrStore(string(key), new(int64))
    count := countVal.(*int64)
    newCount := atomic.AddInt64(count, 1)

    isHotspot := newCount >= h.threshold
    span.SetAttributes(
        attribute.Int64("access.count", newCount),
        attribute.Bool("is_hotspot", isHotspot),
    )

    value, err := h.cache.Get(ctx, key)
    if err != nil {
        return nil, false
    }

    return value, true
}

// Set 设置数据
func (h *HotspotCache) Set(ctx context.Context, key, value []byte, ttl int) error {
    ctx, span := h.tracer.Start(ctx, "HotspotCache.Set")
    defer span.End()

    return h.cache.Set(ctx, key, value, ttl)
}

// GetHotspots 获取热点数据
func (h *HotspotCache) GetHotspots(ctx context.Context) []string {
    ctx, span := h.tracer.Start(ctx, "HotspotCache.GetHotspots")
    defer span.End()

    var hotspots []string
    h.accessCount.Range(func(key, value interface{}) bool {
        count := atomic.LoadInt64(value.(*int64))
        if count >= h.threshold {
            hotspots = append(hotspots, key.(string))
        }
        return true
    })

    span.SetAttributes(attribute.Int("hotspots.count", len(hotspots)))
    return hotspots
}

// ResetCounters 重置计数器
func (h *HotspotCache) ResetCounters(ctx context.Context) {
    ctx, span := h.tracer.Start(ctx, "HotspotCache.ResetCounters")
    defer span.End()

    h.accessCount = sync.Map{}
}

// 使用示例
func ExampleHotspotCache() {
    ctx := context.Background()

    cache := NewHotspotCache(50*1024*1024, 100) // 访问100次视为热点

    // 模拟访问
    key := []byte("popular-item")
    cache.Set(ctx, key, []byte("value"), 3600)

    for i := 0; i < 150; i++ {
        cache.Get(ctx, key)
    }

    // 获取热点数据
    hotspots := cache.GetHotspots(ctx)
    fmt.Printf("Hotspots: %v\n", hotspots)
}
```

### 3.3 API 响应缓存

```go
package apicache

import (
    "context"
    "crypto/md5"
    "fmt"
    "net/http"
    "time"

    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// APICache API 响应缓存
type APICache struct {
    cache  *TracedCache
    tracer trace.Tracer
    ttl    int
}

func NewAPICache(size int, ttl time.Duration) *APICache {
    return &APICache{
        cache:  NewTracedCache(size),
        tracer: otel.Tracer("api-cache"),
        ttl:    int(ttl.Seconds()),
    }
}

// CacheKey 生成缓存键
func (a *APICache) CacheKey(r *http.Request) []byte {
    key := fmt.Sprintf("%s:%s:%s", r.Method, r.URL.Path, r.URL.RawQuery)
    hash := md5.Sum([]byte(key))
    return []byte(fmt.Sprintf("api:%x", hash))
}

// Get 获取缓存的响应
func (a *APICache) Get(ctx context.Context, r *http.Request) ([]byte, bool) {
    ctx, span := a.tracer.Start(ctx, "APICache.Get",
        trace.WithAttributes(
            attribute.String("http.method", r.Method),
            attribute.String("http.url", r.URL.String()),
        ),
    )
    defer span.End()

    key := a.CacheKey(r)
    value, err := a.cache.Get(ctx, key)
    if err != nil {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        return nil, false
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("response.size", len(value)),
    )

    return value, true
}

// Set 设置响应缓存
func (a *APICache) Set(ctx context.Context, r *http.Request, response []byte) error {
    ctx, span := a.tracer.Start(ctx, "APICache.Set",
        trace.WithAttributes(
            attribute.String("http.url", r.URL.String()),
            attribute.Int("response.size", len(response)),
        ),
    )
    defer span.End()

    key := a.CacheKey(r)
    return a.cache.Set(ctx, key, response, a.ttl)
}

// Middleware 缓存中间件
func (a *APICache) Middleware(next http.Handler) http.Handler {
    return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
        ctx := r.Context()
        ctx, span := a.tracer.Start(ctx, "APICache.Middleware",
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
        if response, ok := a.Get(ctx, r); ok {
            span.SetAttributes(attribute.Bool("served_from_cache", true))
            w.Header().Set("X-Cache", "HIT")
            w.Write(response)
            return
        }

        // 缓存未命中
        span.SetAttributes(attribute.Bool("served_from_cache", false))
        w.Header().Set("X-Cache", "MISS")

        // 创建响应记录器
        rec := &responseRecorder{
            ResponseWriter: w,
            body:           make([]byte, 0),
        }

        next.ServeHTTP(rec, r.WithContext(ctx))

        // 只缓存成功的响应
        if rec.statusCode == http.StatusOK {
            a.Set(ctx, r, rec.body)
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
func ExampleAPICache() {
    cache := NewAPICache(100*1024*1024, 5*time.Minute)

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

### 4.1 零 GC 优化

```go
package optimization

import (
    "context"
    "sync"

    "github.com/coocood/freecache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

// ZeroGCCache 零 GC 缓存
type ZeroGCCache struct {
    cache  *freecache.Cache
    tracer trace.Tracer
    pool   *sync.Pool
}

func NewZeroGCCache(size int) *ZeroGCCache {
    return &ZeroGCCache{
        cache:  freecache.NewCache(size),
        tracer: otel.Tracer("zero-gc-cache"),
        pool: &sync.Pool{
            New: func() interface{} {
                return make([]byte, 0, 4096)
            },
        },
    }
}

// Get 获取数据（使用池化 buffer）
func (z *ZeroGCCache) Get(ctx context.Context, key []byte) ([]byte, error) {
    ctx, span := z.tracer.Start(ctx, "ZeroGCCache.Get")
    defer span.End()

    // 从池中获取 buffer
    buf := z.pool.Get().([]byte)
    defer z.pool.Put(buf[:0])

    value, err := z.cache.GetWithBuf(key, buf)
    if err != nil {
        return nil, err
    }

    // 复制数据（避免引用池中的 buffer）
    result := make([]byte, len(value))
    copy(result, value)

    return result, nil
}

// Set 设置数据
func (z *ZeroGCCache) Set(ctx context.Context, key, value []byte, ttl int) error {
    ctx, span := z.tracer.Start(ctx, "ZeroGCCache.Set")
    defer span.End()

    return z.cache.Set(key, value, ttl)
}
```

### 4.2 统计监控

```go
package monitoring

import (
    "context"
    "time"

    "github.com/coocood/freecache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/metric"
)

// CacheMonitor 缓存监控器
type CacheMonitor struct {
    cache       *freecache.Cache
    meter       metric.Meter
    hitCounter  metric.Int64Counter
    missCounter metric.Int64Counter
}

func NewCacheMonitor(cache *freecache.Cache) (*CacheMonitor, error) {
    meter := otel.Meter("cache-monitor")

    hitCounter, err := meter.Int64Counter(
        "cache.hits",
        metric.WithDescription("Number of cache hits"),
    )
    if err != nil {
        return nil, err
    }

    missCounter, err := meter.Int64Counter(
        "cache.misses",
        metric.WithDescription("Number of cache misses"),
    )
    if err != nil {
        return nil, err
    }

    monitor := &CacheMonitor{
        cache:       cache,
        meter:       meter,
        hitCounter:  hitCounter,
        missCounter: missCounter,
    }

    // 启动定期报告
    go monitor.periodicReport()

    return monitor, nil
}

// periodicReport 定期报告指标
func (m *CacheMonitor) periodicReport() {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()

    for range ticker.C {
        ctx := context.Background()

        // 报告命中率
        hitCount := m.cache.HitCount()
        missCount := m.cache.MissCount()

        m.hitCounter.Add(ctx, hitCount)
        m.missCounter.Add(ctx, missCount)

        // 计算命中率
        hitRate := float64(hitCount) / float64(hitCount+missCount)
        log.Printf("Cache hit rate: %.2f%%", hitRate*100)
    }
}
```

### 4.3 淘汰策略

```go
package eviction

import (
    "context"
    "time"

    "github.com/coocood/freecache"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// EvictionManager 淘汰管理器
type EvictionManager struct {
    cache  *freecache.Cache
    tracer trace.Tracer
}

func NewEvictionManager(cache *freecache.Cache) *EvictionManager {
    return &EvictionManager{
        cache:  cache,
        tracer: otel.Tracer("eviction-manager"),
    }
}

// GetEvictionStats 获取淘汰统计
func (e *EvictionManager) GetEvictionStats(ctx context.Context) map[string]int64 {
    ctx, span := e.tracer.Start(ctx, "EvictionManager.GetEvictionStats")
    defer span.End()

    stats := map[string]int64{
        "evict_count":   e.cache.EvacuateCount(),
        "expired_count": e.cache.ExpiredCount(),
    }

    for k, v := range stats {
        span.SetAttributes(attribute.Int64(k, v))
    }

    return stats
}

// MonitorEviction 监控淘汰
func (e *EvictionManager) MonitorEviction(ctx context.Context) {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()

    for range ticker.C {
        stats := e.GetEvictionStats(ctx)
        log.Printf("Eviction stats: %+v", stats)
    }
}
```

---

## 5. 性能优化

```text
✅ 内存配置:
  - 根据实际需求设置缓存大小
  - 避免过大导致内存压力
  - 监控内存使用率

✅ TTL 设置:
  - 根据数据特性设置合理 TTL
  - 热点数据使用较长 TTL
  - 避免永久缓存

✅ 键设计:
  - 使用短键名
  - 避免重复前缀
  - 使用哈希键

✅ 并发优化:
  - FreeCache 天然线程安全
  - 避免锁竞争
  - 使用 GetOrLoad 模式

✅ GC 优化:
  - 利用零 GC 特性
  - 避免频繁创建对象
  - 使用对象池
```

---

## 6. 与其他缓存对比

```text
选择 FreeCache:
  ✅ 需要零 GC 开销
  ✅ 高并发场景
  ✅ 本地缓存
  ✅ 简单键值存储

选择 sync.Map:
  ✅ 简单场景
  ✅ 无需 TTL
  ✅ 无需 LRU

选择 Redis:
  ✅ 分布式缓存
  ✅ 持久化需求
  ✅ 复杂数据结构
```

---

## 7. 最佳实践

```text
✅ 使用场景:
  - 高并发 API 缓存
  - 会话存储
  - 热点数据
  - 限流计数器

✅ 监控指标:
  - 命中率
  - 淘汰率
  - 内存使用
  - 访问延迟

✅ 错误处理:
  - 处理 ErrNotFound
  - 降级策略
  - 日志记录

✅ 维护:
  - 定期查看统计
  - 调整缓存大小
  - 优化 TTL
```

---

## 总结

FreeCache 是一个零 GC 的高性能内存缓存库，非常适合高并发场景。

**关键要点**：

1. **零 GC** - 避免 GC 压力
2. **高性能** - 10M+ ops/s
3. **线程安全** - 并发友好
4. **简单易用** - API 简洁
5. **生产就绪** - 久经考验

**参考资源**：

- [FreeCache GitHub](https://github.com/coocood/freecache)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

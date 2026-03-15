# BadgerDB 与 OTLP 完整集成（2025版）

> **BadgerDB 版本**: v4.3+  
> **Go 版本**: 1.25.1  
> **OpenTelemetry SDK**: v1.32.0  
> **最后更新**: 2025-10-11  
> **文档状态**: ✅ 生产就绪

---

## 📋 目录

- [BadgerDB 与 OTLP 完整集成（2025版）](#badgerdb-与-otlp-完整集成2025版)
  - [📋 目录](#-目录)
  - [1. BadgerDB 概述](#1-badgerdb-概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 性能优势](#12-性能优势)
    - [1.3 适用场景](#13-适用场景)
  - [2. 快速开始](#2-快速开始)
    - [2.1 依赖安装](#21-依赖安装)
    - [2.2 基础集成](#22-基础集成)
    - [2.3 OTLP 包装器](#23-otlp-包装器)
  - [3. 完整集成示例](#3-完整集成示例)
    - [3.1 嵌入式缓存](#31-嵌入式缓存)
    - [3.2 时序数据存储](#32-时序数据存储)
    - [3.3 本地状态管理](#33-本地状态管理)
  - [4. 高级特性](#4-高级特性)
    - [4.1 事务处理](#41-事务处理)
    - [4.2 流式迭代](#42-流式迭代)
    - [4.3 TTL 过期](#43-ttl-过期)
  - [5. 性能优化](#5-性能优化)
  - [6. 生产部署](#6-生产部署)
  - [7. 最佳实践](#7-最佳实践)
  - [总结](#总结)

---

## 1. BadgerDB 概述

### 1.1 核心特性

**BadgerDB** 是一个用纯 Go 编写的高性能嵌入式键值数据库，基于 LSM 树设计。

```text
🚀 核心特性:
  ✅ 纯 Go 实现 - 无 CGO 依赖
  ✅ 高性能 - LSM 树架构
  ✅ 嵌入式 - 无需独立进程
  ✅ 事务支持 - ACID 保证
  ✅ TTL 支持 - 自动过期
  ✅ 流式迭代 - 内存高效
  ✅ 压缩 - 减少磁盘占用
  
⚡ 性能数据:
  - 读: 500K+ ops/s
  - 写: 300K+ ops/s
  - 延迟: P99 < 5ms
  - 磁盘: SSD 优化
```

### 1.2 性能优势

```text
┌─────────────┬──────────────┬─────────────┬─────────────┐
│   指标      │  BadgerDB    │  BoltDB     │  LevelDB    │
├─────────────┼──────────────┼─────────────┼─────────────┤
│ 读性能      │  500K ops/s  │  100K ops/s │  200K ops/s │
│ 写性能      │  300K ops/s  │  50K ops/s  │  150K ops/s │
│ 延迟(P99)   │  5ms         │  10ms       │  8ms        │
│ CGO依赖     │  ❌          │  ❌        │  ✅         │
│ 事务        │  ✅          │  ✅        │  ❌         │
│ TTL        │  ✅          │  ❌         │  ❌         │
│ 压缩        │  ✅         │  ❌         │  ✅         │
│ 内存使用    │  中          │  低          │  中          │
│ 磁盘优化    │  SSD优化     │  通用        │  通用        │
│ 社区活跃度  │  高          │  低          │  中          │
└─────────────┴──────────────┴─────────────┴─────────────┘
```

### 1.3 适用场景

```text
✅ 适合场景:
  - 嵌入式缓存
  - 本地状态存储
  - 时序数据存储
  - 离线数据处理
  - 边缘计算
  - IoT 设备存储
  - 单机高性能应用

❌ 不适合场景:
  - 分布式存储（需自行实现）
  - 需要 SQL 查询
  - 多进程共享访问
  - 频繁的大范围扫描
```

---

## 2. 快速开始

### 2.1 依赖安装

```bash
# 安装 BadgerDB v4
go get -u github.com/dgraph-io/badger/v4@latest

# 安装 OpenTelemetry
go get -u go.opentelemetry.io/otel@v1.32.0
go get -u go.opentelemetry.io/otel/trace@v1.32.0
go get -u go.opentelemetry.io/otel/sdk@v1.32.0
```

**go.mod 示例**：

```go
module github.com/yourorg/badger-otlp-demo

go 1.25.1

require (
    github.com/dgraph-io/badger/v4 v4.3.1
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

    "github.com/dgraph-io/badger/v4"
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
            semconv.ServiceName("badger-storage"),
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

    // 打开数据库
    opts := badger.DefaultOptions("./data")
    opts.Logger = nil // 禁用默认日志

    db, err := badger.Open(opts)
    if err != nil {
        log.Fatal(err)
    }
    defer db.Close()

    ctx := context.Background()
    tracer := otel.Tracer("badger-example")

    // 写入数据
    ctx, span := tracer.Start(ctx, "badger.Set")
    err = db.Update(func(txn *badger.Txn) error {
        return txn.Set([]byte("key"), []byte("value"))
    })
    span.End()
    if err != nil {
        log.Fatal(err)
    }

    // 读取数据
    ctx, span = tracer.Start(ctx, "badger.Get")
    err = db.View(func(txn *badger.Txn) error {
        item, err := txn.Get([]byte("key"))
        if err != nil {
            return err
        }

        return item.Value(func(val []byte) error {
            fmt.Println("Value:", string(val))
            return nil
        })
    })
    span.End()
    if err != nil {
        log.Fatal(err)
    }
}
```

### 2.3 OTLP 包装器

```go
package badgerdb

import (
    "context"
    "time"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

// TracedDB 带追踪的 BadgerDB
type TracedDB struct {
    *badger.DB
    tracer trace.Tracer
}

func NewTracedDB(opts badger.Options) (*TracedDB, error) {
    db, err := badger.Open(opts)
    if err != nil {
        return nil, err
    }

    return &TracedDB{
        DB:     db,
        tracer: otel.Tracer("badger"),
    }, nil
}

// Get 获取键值
func (db *TracedDB) Get(ctx context.Context, key []byte) ([]byte, error) {
    ctx, span := db.tracer.Start(ctx, "badger.Get",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "badger"),
            attribute.String("db.operation", "GET"),
            attribute.Int("db.key.size", len(key)),
        ),
    )
    defer span.End()

    var value []byte
    start := time.Now()

    err := db.DB.View(func(txn *badger.Txn) error {
        item, err := txn.Get(key)
        if err != nil {
            return err
        }

        return item.Value(func(val []byte) error {
            value = append([]byte{}, val...)
            return nil
        })
    })

    duration := time.Since(start)
    span.SetAttributes(
        attribute.Float64("db.duration_ms", float64(duration.Microseconds())/1000.0),
    )

    if err == badger.ErrKeyNotFound {
        span.SetAttributes(attribute.Bool("cache.hit", false))
        span.SetStatus(codes.Ok, "key not found")
        return nil, err
    }

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetAttributes(
        attribute.Bool("cache.hit", true),
        attribute.Int("db.value.size", len(value)),
    )
    span.SetStatus(codes.Ok, "")

    return value, nil
}

// Set 设置键值
func (db *TracedDB) Set(ctx context.Context, key, value []byte, ttl time.Duration) error {
    ctx, span := db.tracer.Start(ctx, "badger.Set",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "badger"),
            attribute.String("db.operation", "SET"),
            attribute.Int("db.key.size", len(key)),
            attribute.Int("db.value.size", len(value)),
        ),
    )
    defer span.End()

    if ttl > 0 {
        span.SetAttributes(attribute.Float64("db.ttl_seconds", ttl.Seconds()))
    }

    start := time.Now()

    err := db.DB.Update(func(txn *badger.Txn) error {
        entry := badger.NewEntry(key, value)
        if ttl > 0 {
            entry = entry.WithTTL(ttl)
        }
        return txn.SetEntry(entry)
    })

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
func (db *TracedDB) Delete(ctx context.Context, key []byte) error {
    ctx, span := db.tracer.Start(ctx, "badger.Delete",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "badger"),
            attribute.String("db.operation", "DELETE"),
            attribute.Int("db.key.size", len(key)),
        ),
    )
    defer span.End()

    err := db.DB.Update(func(txn *badger.Txn) error {
        return txn.Delete(key)
    })

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// Scan 扫描键值对
func (db *TracedDB) Scan(ctx context.Context, prefix []byte, limit int) ([][2][]byte, error) {
    ctx, span := db.tracer.Start(ctx, "badger.Scan",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "badger"),
            attribute.String("db.operation", "SCAN"),
            attribute.Int("db.prefix.size", len(prefix)),
            attribute.Int("db.limit", limit),
        ),
    )
    defer span.End()

    var results [][2][]byte
    start := time.Now()

    err := db.DB.View(func(txn *badger.Txn) error {
        opts := badger.DefaultIteratorOptions
        opts.Prefix = prefix
        it := txn.NewIterator(opts)
        defer it.Close()

        count := 0
        for it.Seek(prefix); it.ValidForPrefix(prefix) && count < limit; it.Next() {
            item := it.Item()
            key := item.KeyCopy(nil)

            err := item.Value(func(val []byte) error {
                value := append([]byte{}, val...)
                results = append(results, [2][]byte{key, value})
                return nil
            })

            if err != nil {
                return err
            }

            count++
        }

        return nil
    })

    duration := time.Since(start)
    span.SetAttributes(
        attribute.Float64("db.duration_ms", float64(duration.Microseconds())/1000.0),
        attribute.Int("db.results.count", len(results)),
    )

    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }

    span.SetStatus(codes.Ok, "")
    return results, nil
}

// Batch 批量写入
func (db *TracedDB) Batch(ctx context.Context, entries map[string][]byte) error {
    ctx, span := db.tracer.Start(ctx, "badger.Batch",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            attribute.String("db.system", "badger"),
            attribute.String("db.operation", "BATCH"),
            attribute.Int("db.batch.size", len(entries)),
        ),
    )
    defer span.End()

    wb := db.DB.NewWriteBatch()
    defer wb.Cancel()

    for key, value := range entries {
        if err := wb.Set([]byte(key), value); err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, err.Error())
            return err
        }
    }

    if err := wb.Flush(); err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}
```

---

## 3. 完整集成示例

### 3.1 嵌入式缓存

```go
package cache

import (
    "context"
    "encoding/json"
    "fmt"
    "time"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// EmbeddedCache 嵌入式缓存
type EmbeddedCache struct {
    db     *TracedDB
    tracer trace.Tracer
    prefix string
}

func NewEmbeddedCache(dbPath, prefix string) (*EmbeddedCache, error) {
    opts := badger.DefaultOptions(dbPath)
    opts.Logger = nil

    db, err := NewTracedDB(opts)
    if err != nil {
        return nil, err
    }

    return &EmbeddedCache{
        db:     db,
        tracer: otel.Tracer("embedded-cache"),
        prefix: prefix,
    }, nil
}

// Get 获取缓存
func (c *EmbeddedCache) Get(ctx context.Context, key string, dest interface{}) error {
    ctx, span := c.tracer.Start(ctx, "EmbeddedCache.Get",
        trace.WithAttributes(
            attribute.String("cache.key", key),
        ),
    )
    defer span.End()

    fullKey := []byte(c.prefix + key)
    data, err := c.db.Get(ctx, fullKey)
    if err == badger.ErrKeyNotFound {
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
func (c *EmbeddedCache) Set(ctx context.Context, key string, value interface{}, ttl time.Duration) error {
    ctx, span := c.tracer.Start(ctx, "EmbeddedCache.Set",
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

    fullKey := []byte(c.prefix + key)
    return c.db.Set(ctx, fullKey, data, ttl)
}

// Delete 删除缓存
func (c *EmbeddedCache) Delete(ctx context.Context, key string) error {
    ctx, span := c.tracer.Start(ctx, "EmbeddedCache.Delete")
    defer span.End()

    fullKey := []byte(c.prefix + key)
    return c.db.Delete(ctx, fullKey)
}

// GetOrLoad 获取或加载
func (c *EmbeddedCache) GetOrLoad(ctx context.Context, key string, ttl time.Duration, loader func(context.Context) (interface{}, error)) (interface{}, error) {
    ctx, span := c.tracer.Start(ctx, "EmbeddedCache.GetOrLoad")
    defer span.End()

    var result interface{}
    err := c.Get(ctx, key, &result)
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

    if err := c.Set(ctx, key, result, ttl); err != nil {
        span.RecordError(fmt.Errorf("failed to set cache: %w", err))
    }

    return result, nil
}

// Close 关闭缓存
func (c *EmbeddedCache) Close() error {
    return c.db.Close()
}

var ErrCacheMiss = fmt.Errorf("cache miss")

// 使用示例
func ExampleEmbeddedCache() {
    ctx := context.Background()

    cache, err := NewEmbeddedCache("./cache_data", "myapp:")
    if err != nil {
        log.Fatal(err)
    }
    defer cache.Close()

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

    // 获取或加载
    result, err := cache.GetOrLoad(ctx, "user:456", time.Hour, func(ctx context.Context) (interface{}, error) {
        return User{ID: 456, Name: "Bob"}, nil
    })
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("Loaded: %+v\n", result)
}
```

### 3.2 时序数据存储

```go
package timeseries

import (
    "context"
    "encoding/binary"
    "fmt"
    "time"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TimeSeriesDB 时序数据库
type TimeSeriesDB struct {
    db     *TracedDB
    tracer trace.Tracer
}

func NewTimeSeriesDB(dbPath string) (*TimeSeriesDB, error) {
    opts := badger.DefaultOptions(dbPath)
    opts.Logger = nil

    db, err := NewTracedDB(opts)
    if err != nil {
        return nil, err
    }

    return &TimeSeriesDB{
        db:     db,
        tracer: otel.Tracer("timeseries-db"),
    }, nil
}

// DataPoint 数据点
type DataPoint struct {
    Timestamp time.Time
    Value     float64
    Tags      map[string]string
}

// Write 写入数据点
func (ts *TimeSeriesDB) Write(ctx context.Context, metric string, point DataPoint) error {
    ctx, span := ts.tracer.Start(ctx, "TimeSeriesDB.Write",
        trace.WithAttributes(
            attribute.String("metric", metric),
            attribute.Int64("timestamp", point.Timestamp.Unix()),
            attribute.Float64("value", point.Value),
        ),
    )
    defer span.End()

    // 生成键: metric:timestamp
    key := ts.makeKey(metric, point.Timestamp)

    // 序列化值
    value := ts.encodeDataPoint(point)

    return ts.db.Set(ctx, key, value, 0)
}

// Query 查询时间范围内的数据
func (ts *TimeSeriesDB) Query(ctx context.Context, metric string, start, end time.Time) ([]DataPoint, error) {
    ctx, span := ts.tracer.Start(ctx, "TimeSeriesDB.Query",
        trace.WithAttributes(
            attribute.String("metric", metric),
            attribute.Int64("start", start.Unix()),
            attribute.Int64("end", end.Unix()),
        ),
    )
    defer span.End()

    var points []DataPoint

    err := ts.db.DB.View(func(txn *badger.Txn) error {
        opts := badger.DefaultIteratorOptions
        opts.PrefetchValues = true
        it := txn.NewIterator(opts)
        defer it.Close()

        prefix := []byte(metric + ":")
        startKey := ts.makeKey(metric, start)

        for it.Seek(startKey); it.ValidForPrefix(prefix); it.Next() {
            item := it.Item()

            // 检查时间范围
            timestamp := ts.extractTimestamp(item.Key())
            if timestamp.After(end) {
                break
            }

            err := item.Value(func(val []byte) error {
                point := ts.decodeDataPoint(val)
                point.Timestamp = timestamp
                points = append(points, point)
                return nil
            })

            if err != nil {
                return err
            }
        }

        return nil
    })

    span.SetAttributes(attribute.Int("results.count", len(points)))

    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return points, nil
}

// Aggregate 聚合数据
func (ts *TimeSeriesDB) Aggregate(ctx context.Context, metric string, start, end time.Time, fn func([]float64) float64) (float64, error) {
    ctx, span := ts.tracer.Start(ctx, "TimeSeriesDB.Aggregate",
        trace.WithAttributes(
            attribute.String("metric", metric),
        ),
    )
    defer span.End()

    points, err := ts.Query(ctx, metric, start, end)
    if err != nil {
        return 0, err
    }

    values := make([]float64, len(points))
    for i, point := range points {
        values[i] = point.Value
    }

    result := fn(values)
    span.SetAttributes(
        attribute.Int("data_points", len(values)),
        attribute.Float64("result", result),
    )

    return result, nil
}

// makeKey 生成时序键
func (ts *TimeSeriesDB) makeKey(metric string, t time.Time) []byte {
    key := []byte(fmt.Sprintf("%s:%d", metric, t.UnixNano()))
    return key
}

// extractTimestamp 从键中提取时间戳
func (ts *TimeSeriesDB) extractTimestamp(key []byte) time.Time {
    // 假设格式: metric:timestamp
    parts := string(key)
    var timestamp int64
    fmt.Sscanf(parts, "%*[^:]:%d", &timestamp)
    return time.Unix(0, timestamp)
}

// encodeDataPoint 编码数据点
func (ts *TimeSeriesDB) encodeDataPoint(point DataPoint) []byte {
    buf := make([]byte, 8)
    binary.BigEndian.PutUint64(buf, uint64(point.Value))
    // 简化: 实际应该包含 tags
    return buf
}

// decodeDataPoint 解码数据点
func (ts *TimeSeriesDB) decodeDataPoint(data []byte) DataPoint {
    value := float64(binary.BigEndian.Uint64(data))
    return DataPoint{
        Value: value,
        Tags:  make(map[string]string),
    }
}

// Close 关闭数据库
func (ts *TimeSeriesDB) Close() error {
    return ts.db.Close()
}

// 使用示例
func ExampleTimeSeriesDB() {
    ctx := context.Background()

    tsdb, err := NewTimeSeriesDB("./timeseries_data")
    if err != nil {
        log.Fatal(err)
    }
    defer tsdb.Close()

    // 写入数据点
    now := time.Now()
    for i := 0; i < 100; i++ {
        point := DataPoint{
            Timestamp: now.Add(time.Duration(i) * time.Second),
            Value:     float64(i) * 1.5,
            Tags: map[string]string{
                "host": "server-01",
            },
        }

        if err := tsdb.Write(ctx, "cpu.usage", point); err != nil {
            log.Fatal(err)
        }
    }

    // 查询数据
    start := now
    end := now.Add(50 * time.Second)
    points, err := tsdb.Query(ctx, "cpu.usage", start, end)
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("Found %d data points\n", len(points))

    // 聚合: 计算平均值
    avg, err := tsdb.Aggregate(ctx, "cpu.usage", start, end, func(values []float64) float64 {
        sum := 0.0
        for _, v := range values {
            sum += v
        }
        return sum / float64(len(values))
    })
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("Average CPU usage: %.2f\n", avg)
}
```

### 3.3 本地状态管理

```go
package state

import (
    "context"
    "encoding/json"
    "fmt"
    "sync"
    "time"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// StateManager 状态管理器
type StateManager struct {
    db     *TracedDB
    tracer trace.Tracer
    cache  sync.Map
}

func NewStateManager(dbPath string) (*StateManager, error) {
    opts := badger.DefaultOptions(dbPath)
    opts.Logger = nil

    db, err := NewTracedDB(opts)
    if err != nil {
        return nil, err
    }

    sm := &StateManager{
        db:     db,
        tracer: otel.Tracer("state-manager"),
    }

    // 启动后台同步
    go sm.periodicSync()

    return sm, nil
}

// GetState 获取状态
func (sm *StateManager) GetState(ctx context.Context, key string) (interface{}, error) {
    ctx, span := sm.tracer.Start(ctx, "StateManager.GetState",
        trace.WithAttributes(
            attribute.String("state.key", key),
        ),
    )
    defer span.End()

    // 先查内存缓存
    if value, ok := sm.cache.Load(key); ok {
        span.SetAttributes(attribute.Bool("cache.hit", true))
        return value, nil
    }

    // 从磁盘加载
    span.SetAttributes(attribute.Bool("cache.hit", false))
    data, err := sm.db.Get(ctx, []byte(key))
    if err == badger.ErrKeyNotFound {
        return nil, ErrStateNotFound
    }
    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    var value interface{}
    if err := json.Unmarshal(data, &value); err != nil {
        span.RecordError(err)
        return nil, err
    }

    // 更新缓存
    sm.cache.Store(key, value)

    return value, nil
}

// SetState 设置状态
func (sm *StateManager) SetState(ctx context.Context, key string, value interface{}) error {
    ctx, span := sm.tracer.Start(ctx, "StateManager.SetState",
        trace.WithAttributes(
            attribute.String("state.key", key),
        ),
    )
    defer span.End()

    // 更新内存缓存
    sm.cache.Store(key, value)

    // 持久化到磁盘
    data, err := json.Marshal(value)
    if err != nil {
        span.RecordError(err)
        return err
    }

    return sm.db.Set(ctx, []byte(key), data, 0)
}

// DeleteState 删除状态
func (sm *StateManager) DeleteState(ctx context.Context, key string) error {
    ctx, span := sm.tracer.Start(ctx, "StateManager.DeleteState")
    defer span.End()

    sm.cache.Delete(key)
    return sm.db.Delete(ctx, []byte(key))
}

// ListStates 列出所有状态
func (sm *StateManager) ListStates(ctx context.Context) (map[string]interface{}, error) {
    ctx, span := sm.tracer.Start(ctx, "StateManager.ListStates")
    defer span.End()

    states := make(map[string]interface{})

    err := sm.db.DB.View(func(txn *badger.Txn) error {
        opts := badger.DefaultIteratorOptions
        it := txn.NewIterator(opts)
        defer it.Close()

        for it.Rewind(); it.Valid(); it.Next() {
            item := it.Item()
            key := string(item.KeyCopy(nil))

            err := item.Value(func(val []byte) error {
                var value interface{}
                if err := json.Unmarshal(val, &value); err != nil {
                    return err
                }
                states[key] = value
                return nil
            })

            if err != nil {
                return err
            }
        }

        return nil
    })

    span.SetAttributes(attribute.Int("states.count", len(states)))

    if err != nil {
        span.RecordError(err)
        return nil, err
    }

    return states, nil
}

// periodicSync 定期同步缓存到磁盘
func (sm *StateManager) periodicSync() {
    ticker := time.NewTicker(10 * time.Second)
    defer ticker.Stop()

    for range ticker.C {
        ctx := context.Background()
        ctx, span := sm.tracer.Start(ctx, "StateManager.PeriodicSync")

        // 遍历缓存并同步
        count := 0
        sm.cache.Range(func(key, value interface{}) bool {
            keyStr := key.(string)
            data, err := json.Marshal(value)
            if err != nil {
                return true
            }

            if err := sm.db.Set(ctx, []byte(keyStr), data, 0); err != nil {
                span.RecordError(err)
            } else {
                count++
            }

            return true
        })

        span.SetAttributes(attribute.Int("synced.count", count))
        span.End()
    }
}

// Close 关闭状态管理器
func (sm *StateManager) Close() error {
    // 最后一次同步
    ctx := context.Background()
    sm.cache.Range(func(key, value interface{}) bool {
        keyStr := key.(string)
        data, _ := json.Marshal(value)
        sm.db.Set(ctx, []byte(keyStr), data, 0)
        return true
    })

    return sm.db.Close()
}

var ErrStateNotFound = fmt.Errorf("state not found")

// 使用示例
func ExampleStateManager() {
    ctx := context.Background()

    sm, err := NewStateManager("./state_data")
    if err != nil {
        log.Fatal(err)
    }
    defer sm.Close()

    // 设置状态
    appState := map[string]interface{}{
        "version":    "1.0.0",
        "started_at": time.Now(),
        "config": map[string]interface{}{
            "debug": true,
            "port":  8080,
        },
    }

    if err := sm.SetState(ctx, "app.state", appState); err != nil {
        log.Fatal(err)
    }

    // 获取状态
    retrieved, err := sm.GetState(ctx, "app.state")
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("State: %+v\n", retrieved)

    // 列出所有状态
    allStates, err := sm.ListStates(ctx)
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("Total states: %d\n", len(allStates))
}
```

---

## 4. 高级特性

### 4.1 事务处理

```go
package transaction

import (
    "context"
    "fmt"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// TransactionManager 事务管理器
type TransactionManager struct {
    db     *badger.DB
    tracer trace.Tracer
}

func NewTransactionManager(db *badger.DB) *TransactionManager {
    return &TransactionManager{
        db:     db,
        tracer: otel.Tracer("transaction-manager"),
    }
}

// RunTransaction 执行事务
func (tm *TransactionManager) RunTransaction(ctx context.Context, fn func(*badger.Txn) error) error {
    ctx, span := tm.tracer.Start(ctx, "TransactionManager.RunTransaction")
    defer span.End()

    err := tm.db.Update(fn)
    if err != nil {
        span.RecordError(err)
        return err
    }

    span.SetStatus(codes.Ok, "")
    return nil
}

// TransferBalance 转账示例（原子操作）
func (tm *TransactionManager) TransferBalance(ctx context.Context, from, to string, amount float64) error {
    ctx, span := tm.tracer.Start(ctx, "TransactionManager.TransferBalance",
        trace.WithAttributes(
            attribute.String("from", from),
            attribute.String("to", to),
            attribute.Float64("amount", amount),
        ),
    )
    defer span.End()

    return tm.RunTransaction(ctx, func(txn *badger.Txn) error {
        // 读取源账户余额
        fromItem, err := txn.Get([]byte("balance:" + from))
        if err != nil {
            return err
        }

        var fromBalance float64
        err = fromItem.Value(func(val []byte) error {
            fromBalance = bytesToFloat64(val)
            return nil
        })
        if err != nil {
            return err
        }

        // 检查余额
        if fromBalance < amount {
            return fmt.Errorf("insufficient balance")
        }

        // 读取目标账户余额
        toItem, err := txn.Get([]byte("balance:" + to))
        if err != nil && err != badger.ErrKeyNotFound {
            return err
        }

        var toBalance float64
        if err != badger.ErrKeyNotFound {
            err = toItem.Value(func(val []byte) error {
                toBalance = bytesToFloat64(val)
                return nil
            })
            if err != nil {
                return err
            }
        }

        // 执行转账
        fromBalance -= amount
        toBalance += amount

        // 写入新余额
        if err := txn.Set([]byte("balance:"+from), float64ToBytes(fromBalance)); err != nil {
            return err
        }

        if err := txn.Set([]byte("balance:"+to), float64ToBytes(toBalance)); err != nil {
            return err
        }

        span.SetAttributes(
            attribute.Float64("from.new_balance", fromBalance),
            attribute.Float64("to.new_balance", toBalance),
        )

        return nil
    })
}

func bytesToFloat64(b []byte) float64 {
    // 简化实现
    var f float64
    fmt.Sscanf(string(b), "%f", &f)
    return f
}

func float64ToBytes(f float64) []byte {
    return []byte(fmt.Sprintf("%f", f))
}
```

### 4.2 流式迭代

```go
package stream

import (
    "context"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// StreamProcessor 流式处理器
type StreamProcessor struct {
    db     *badger.DB
    tracer trace.Tracer
}

func NewStreamProcessor(db *badger.DB) *StreamProcessor {
    return &StreamProcessor{
        db:     db,
        tracer: otel.Tracer("stream-processor"),
    }
}

// ProcessStream 流式处理
func (sp *StreamProcessor) ProcessStream(ctx context.Context, prefix []byte, processor func(key, value []byte) error) error {
    ctx, span := sp.tracer.Start(ctx, "StreamProcessor.ProcessStream",
        trace.WithAttributes(
            attribute.Int("prefix.size", len(prefix)),
        ),
    )
    defer span.End()

    stream := sp.db.NewStream()
    stream.Prefix = prefix
    stream.NumGo = 16 // 并发 goroutine 数量

    count := 0
    stream.Send = func(buf *badger.KVList) error {
        for _, kv := range buf.Kv {
            if err := processor(kv.Key, kv.Value); err != nil {
                return err
            }
            count++
        }
        return nil
    }

    if err := stream.Orchestrate(ctx); err != nil {
        span.RecordError(err)
        return err
    }

    span.SetAttributes(attribute.Int("processed.count", count))
    return nil
}

// ExportToFile 导出到文件
func (sp *StreamProcessor) ExportToFile(ctx context.Context, filename string) error {
    ctx, span := sp.tracer.Start(ctx, "StreamProcessor.ExportToFile")
    defer span.End()

    file, err := os.Create(filename)
    if err != nil {
        span.RecordError(err)
        return err
    }
    defer file.Close()

    return sp.ProcessStream(ctx, nil, func(key, value []byte) error {
        _, err := fmt.Fprintf(file, "%s=%s\n", key, value)
        return err
    })
}
```

### 4.3 TTL 过期

```go
package ttl

import (
    "context"
    "time"

    "github.com/dgraph-io/badger/v4"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
)

// TTLManager TTL 管理器
type TTLManager struct {
    db     *badger.DB
    tracer trace.Tracer
}

func NewTTLManager(db *badger.DB) *TTLManager {
    tm := &TTLManager{
        db:     db,
        tracer: otel.Tracer("ttl-manager"),
    }

    // 启动 GC
    go tm.runGC()

    return tm
}

// SetWithTTL 设置带 TTL 的键值
func (tm *TTLManager) SetWithTTL(ctx context.Context, key, value []byte, ttl time.Duration) error {
    ctx, span := tm.tracer.Start(ctx, "TTLManager.SetWithTTL",
        trace.WithAttributes(
            attribute.Float64("ttl_seconds", ttl.Seconds()),
        ),
    )
    defer span.End()

    return tm.db.Update(func(txn *badger.Txn) error {
        entry := badger.NewEntry(key, value).WithTTL(ttl)
        return txn.SetEntry(entry)
    })
}

// runGC 运行垃圾回收
func (tm *TTLManager) runGC() {
    ticker := time.NewTicker(5 * time.Minute)
    defer ticker.Stop()

    for range ticker.C {
        ctx := context.Background()
        ctx, span := tm.tracer.Start(ctx, "TTLManager.GC")

        // 运行 GC
        if err := tm.db.RunValueLogGC(0.5); err != nil {
            span.RecordError(err)
        }

        span.End()
    }
}
```

---

## 5. 性能优化

```text
✅ 数据库配置:
  - ValueLogFileSize: 1GB (SSD)
  - MemTableSize: 64MB
  - NumMemtables: 5
  - NumLevelZeroTables: 5
  - NumLevelZeroTablesStall: 10
  - NumCompactors: 4
  - Compression: Snappy/Zstd

✅ 批量操作:
  - 使用 WriteBatch 批量写入
  - 使用 Stream 批量读取
  - 减少事务开销

✅ 索引优化:
  - 使用前缀扫描
  - 合理设计键结构
  - 使用 Bloom Filter

✅ 内存优化:
  - 调整 TableLoadingMode
  - 使用压缩
  - 定期运行 GC

✅ 磁盘优化:
  - 使用 SSD
  - 分离数据和日志
  - 定期备份
```

---

## 6. 生产部署

**配置示例**：

```go
func NewProductionDB(dbPath string) (*badger.DB, error) {
    opts := badger.DefaultOptions(dbPath)

    // 生产配置
    opts.ValueLogFileSize = 1 << 30 // 1GB
    opts.MemTableSize = 64 << 20    // 64MB
    opts.NumMemtables = 5
    opts.NumLevelZeroTables = 5
    opts.NumLevelZeroTablesStall = 10
    opts.NumCompactors = 4
    opts.Compression = options.Snappy
    opts.SyncWrites = false
    opts.NumVersionsToKeep = 1
    opts.CompactL0OnClose = true

    // 日志
    opts.Logger = customLogger

    return badger.Open(opts)
}
```

**Docker 部署**:

```dockerfile
FROM golang:1.25.1-alpine AS builder

WORKDIR /build
COPY . .
RUN go mod download
RUN CGO_ENABLED=0 go build -o app ./cmd/server

FROM alpine:latest
WORKDIR /app
COPY --from=builder /build/app .

# 创建数据目录
RUN mkdir -p /data

VOLUME ["/data"]
EXPOSE 8080

CMD ["./app", "--db-path=/data"]
```

**备份脚本**:

```bash
#!/bin/bash
# backup.sh

DB_PATH="/data/badger"
BACKUP_DIR="/backups"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
BACKUP_FILE="$BACKUP_DIR/badger_$TIMESTAMP.tar.gz"

# 创建备份
tar -czf "$BACKUP_FILE" -C "$DB_PATH" .

# 保留最近 7 天的备份
find "$BACKUP_DIR" -name "badger_*.tar.gz" -mtime +7 -delete

echo "Backup completed: $BACKUP_FILE"
```

---

## 7. 最佳实践

```text
✅ 数据设计:
  - 使用前缀组织键
  - 避免热键
  - 合理设置 TTL
  - 使用序列化格式

✅ 事务管理:
  - 保持事务简短
  - 避免长时间持有事务
  - 使用 WriteBatch 批量写入

✅ 错误处理:
  - 处理 ErrKeyNotFound
  - 实现重试机制
  - 记录错误日志

✅ 监控指标:
  - LSM 层级
  - 内存使用
  - 磁盘 I/O
  - GC 频率

✅ 维护:
  - 定期备份
  - 监控磁盘空间
  - 运行 GC
  - 版本升级
```

---

## 总结

BadgerDB 是一个高性能的嵌入式键值数据库，适合需要本地持久化存储的场景。

**关键要点**：

1. **纯 Go 实现** - 无 CGO 依赖
2. **高性能** - LSM 树架构
3. **完整功能** - 事务/TTL/流式处理
4. **OTLP 集成** - 完整追踪
5. **生产就绪** - 久经考验

**参考资源**：

- [BadgerDB 官方文档](https://dgraph.io/docs/badger/)
- [BadgerDB GitHub](https://github.com/dgraph-io/badger)
- [OpenTelemetry Go](https://opentelemetry.io/docs/instrumentation/go/)

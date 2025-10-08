# Redis 语义约定

> **最后更新**: 2025年10月8日  
> **规范版本**: OpenTelemetry Semantic Conventions v1.24.0  
> **目标读者**: 后端工程师、可观测性工程师

---

## 目录

- [Redis 语义约定](#redis-语义约定)
  - [目录](#目录)
  - [1. Redis追踪概述](#1-redis追踪概述)
  - [2. 通用Redis属性](#2-通用redis属性)
  - [3. Redis命令属性](#3-redis命令属性)
  - [4. 连接池属性](#4-连接池属性)
  - [5. Span命名规范](#5-span命名规范)
  - [6. 完整实现示例](#6-完整实现示例)
    - [6.1 Go实现](#61-go实现)
    - [6.2 Python实现](#62-python实现)
    - [6.3 Java实现](#63-java实现)
  - [7. 高级场景](#7-高级场景)
    - [7.1 Pipeline追踪](#71-pipeline追踪)
    - [7.2 Pub/Sub追踪](#72-pubsub追踪)
  - [8. 性能考虑](#8-性能考虑)
  - [9. 最佳实践](#9-最佳实践)
  - [10. 参考资源](#10-参考资源)

---

## 1. Redis追踪概述

**为什么追踪Redis**:

```text
1. 性能分析
   - 识别慢命令
   - 发现热点Key
   - 优化查询模式

2. 故障排查
   - 连接问题诊断
   - 超时原因分析
   - 错误追踪

3. 容量规划
   - 流量模式分析
   - 峰值负载监控
   - 集群扩展决策

4. 成本优化
   - 识别不必要的查询
   - 优化缓存命中率
   - 减少网络往返
```

---

## 2. 通用Redis属性

| 属性名 | 类型 | 描述 | 示例 | 必需 |
|-------|------|------|------|------|
| `db.system` | string | 数据库系统标识符 | `redis` | ✅ 是 |
| `db.connection_string` | string | 连接字符串（不含密码） | `redis://cache.example.com:6379` | ⚠️ 可选 |
| `db.user` | string | 数据库用户名 | `cache_user` | ⚠️ 可选 |
| `network.peer.address` | string | Redis服务器地址 | `cache.example.com` | ✅ 是 |
| `network.peer.port` | int | Redis服务器端口 | `6379` | ✅ 是 |
| `db.redis.database_index` | int | Redis数据库索引 | `0` | ⚠️ 可选 |

**形式化定义**:

```text
RedisSpan = {
  name: string,
  kind: SpanKind.CLIENT,
  attributes: {
    db.system: "redis",
    network.peer.address: string,
    network.peer.port: int,
    db.redis.database_index?: int,
    ...
  },
  ...
}
```

---

## 3. Redis命令属性

| 属性名 | 类型 | 描述 | 示例 | 必需 |
|-------|------|------|------|------|
| `db.statement` | string | Redis命令（参数可脱敏） | `GET user:123` | ✅ 是 |
| `db.operation` | string | Redis操作类型 | `GET`, `SET`, `HGETALL` | ✅ 是 |

**命令脱敏规则**:

```text
✅ 推荐做法:
GET user:123 → GET user:?
MGET user:123 user:456 → MGET user:? user:?
SET session:abc123 "data" → SET session:? ?

❌ 不推荐:
SET session:abc123 "sensitive_data" (暴露敏感信息)
```

---

## 4. 连接池属性

| 属性名 | 类型 | 描述 | 示例 |
|-------|------|------|------|
| `pool.name` | string | 连接池名称 | `redis-pool-1` |
| `state` | string | 连接状态 | `idle`, `used` |

---

## 5. Span命名规范

```text
格式: <operation> <target>

示例:
✅ 推荐:
- GET user:*
- SET session:*
- HGETALL product:*
- ZADD leaderboard:*

❌ 不推荐:
- GET user:123 (太具体)
- redis (太模糊)
- cache (太通用)

复杂命令:
- MGET 5 keys
- PIPELINE 10 commands
- EVAL script
```

---

## 6. 完整实现示例

### 6.1 Go实现

```go
package main

import (
    "context"
    "fmt"
    
    "github.com/go-redis/redis/v8"
    "go.opentelemetry.io/contrib/instrumentation/github.com/go-redis/redis/v8/otelredis"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

// 使用官方Instrumentation
func createInstrumentedRedisClient() *redis.Client {
    rdb := redis.NewClient(&redis.Options{
        Addr:     "localhost:6379",
        Password: "",
        DB:       0,
    })
    
    // 添加OTel钩子
    rdb.AddHook(otelredis.NewTracingHook())
    
    return rdb
}

// 手动Instrumentation示例
func manualInstrumentation() {
    tracer := otel.Tracer("redis-client")
    rdb := redis.NewClient(&redis.Options{Addr: "localhost:6379"})
    
    ctx := context.Background()
    
    // GET命令
    ctx, span := tracer.Start(ctx, "GET user:*",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemRedis,
            semconv.NetworkPeerAddress("localhost"),
            semconv.NetworkPeerPort(6379),
            attribute.Int("db.redis.database_index", 0),
            attribute.String("db.operation", "GET"),
        ),
    )
    defer span.End()
    
    userID := "user:123"
    result, err := rdb.Get(ctx, userID).Result()
    
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return
    }
    
    span.SetAttributes(
        attribute.String("db.statement", fmt.Sprintf("GET %s", maskKey(userID))),
        attribute.Int("db.response.size", len(result)),
    )
    span.SetStatus(codes.Ok, "")
}

// Key脱敏
func maskKey(key string) string {
    // user:123 → user:?
    parts := strings.SplitN(key, ":", 2)
    if len(parts) == 2 {
        return parts[0] + ":?"
    }
    return "?"
}

// Pipeline示例
func tracePipeline(ctx context.Context, rdb *redis.Client) {
    tracer := otel.Tracer("redis-client")
    
    ctx, span := tracer.Start(ctx, "PIPELINE 3 commands",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemRedis,
            attribute.String("db.operation", "PIPELINE"),
            attribute.Int("db.redis.pipeline.commands", 3),
        ),
    )
    defer span.End()
    
    pipe := rdb.Pipeline()
    
    incr := pipe.Incr(ctx, "counter")
    set := pipe.Set(ctx, "key", "value", 0)
    get := pipe.Get(ctx, "key")
    
    _, err := pipe.Exec(ctx)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return
    }
    
    span.SetAttributes(
        attribute.Int64("counter.value", incr.Val()),
    )
    span.SetStatus(codes.Ok, "")
}

// 完整使用示例
func main() {
    // 使用自动Instrumentation
    rdb := createInstrumentedRedisClient()
    defer rdb.Close()
    
    ctx := context.Background()
    
    // 自动追踪
    err := rdb.Set(ctx, "key", "value", 0).Err()
    if err != nil {
        panic(err)
    }
    
    val, err := rdb.Get(ctx, "key").Result()
    if err != nil {
        panic(err)
    }
    fmt.Println("key:", val)
}
```

### 6.2 Python实现

```python
from opentelemetry import trace
from opentelemetry.instrumentation.redis import RedisInstrumentor
from opentelemetry.semconv.trace import SpanAttributes
import redis

# 自动Instrumentation
RedisInstrumentor().instrument()

# 创建Redis客户端
r = redis.Redis(host='localhost', port=6379, db=0)

# 自动追踪
r.set('key', 'value')
value = r.get('key')

# 手动Instrumentation
tracer = trace.get_tracer(__name__)

def get_user(user_id: str) -> dict:
    with tracer.start_as_current_span(
        "GET user:*",
        kind=trace.SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "redis",
            SpanAttributes.NET_PEER_NAME: "localhost",
            SpanAttributes.NET_PEER_PORT: 6379,
            SpanAttributes.DB_OPERATION: "GET",
        }
    ) as span:
        try:
            key = f"user:{user_id}"
            data = r.get(key)
            
            span.set_attribute("db.statement", f"GET user:?")
            span.set_status(trace.Status(trace.StatusCode.OK))
            
            return data
        except Exception as e:
            span.record_exception(e)
            span.set_status(trace.Status(trace.StatusCode.ERROR, str(e)))
            raise

# Pipeline追踪
def pipeline_example():
    with tracer.start_as_current_span(
        "PIPELINE 3 commands",
        kind=trace.SpanKind.CLIENT,
        attributes={
            SpanAttributes.DB_SYSTEM: "redis",
            SpanAttributes.DB_OPERATION: "PIPELINE",
            "db.redis.pipeline.commands": 3,
        }
    ) as span:
        pipe = r.pipeline()
        pipe.incr('counter')
        pipe.set('key', 'value')
        pipe.get('key')
        results = pipe.execute()
        
        span.set_attribute("counter.value", results[0])
        span.set_status(trace.Status(trace.StatusCode.OK))
```

### 6.3 Java实现

```java
import io.opentelemetry.api.GlobalOpenTelemetry;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import io.opentelemetry.semconv.trace.attributes.SemanticAttributes;
import redis.clients.jedis.Jedis;
import redis.clients.jedis.Pipeline;

public class RedisTracing {
    
    private static final Tracer tracer = 
        GlobalOpenTelemetry.getTracer("redis-client");
    
    // 手动Instrumentation
    public String getUser(Jedis jedis, String userId) {
        Span span = tracer.spanBuilder("GET user:*")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute(SemanticAttributes.DB_SYSTEM, "redis")
            .setAttribute(SemanticAttributes.NET_PEER_NAME, "localhost")
            .setAttribute(SemanticAttributes.NET_PEER_PORT, 6379)
            .setAttribute(SemanticAttributes.DB_OPERATION, "GET")
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            String key = "user:" + userId;
            String result = jedis.get(key);
            
            span.setAttribute("db.statement", "GET user:?");
            span.setStatus(StatusCode.OK);
            
            return result;
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        } finally {
            span.end();
        }
    }
    
    // Pipeline追踪
    public void pipelineExample(Jedis jedis) {
        Span span = tracer.spanBuilder("PIPELINE 3 commands")
            .setSpanKind(SpanKind.CLIENT)
            .setAttribute(SemanticAttributes.DB_SYSTEM, "redis")
            .setAttribute("db.operation", "PIPELINE")
            .setAttribute("db.redis.pipeline.commands", 3)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            Pipeline pipe = jedis.pipelined();
            pipe.incr("counter");
            pipe.set("key", "value");
            pipe.get("key");
            pipe.sync();
            
            span.setStatus(StatusCode.OK);
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
        } finally {
            span.end();
        }
    }
}
```

---

## 7. 高级场景

### 7.1 Pipeline追踪

```go
func tracePipelineAdvanced(ctx context.Context, rdb *redis.Client) {
    tracer := otel.Tracer("redis-client")
    
    ctx, parentSpan := tracer.Start(ctx, "Process batch orders",
        trace.WithSpanKind(trace.SpanKindInternal),
    )
    defer parentSpan.End()
    
    // Pipeline Span
    ctx, pipeSpan := tracer.Start(ctx, "PIPELINE 100 commands",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            semconv.DBSystemRedis,
            attribute.String("db.operation", "PIPELINE"),
        ),
    )
    
    pipe := rdb.Pipeline()
    
    for i := 0; i < 100; i++ {
        orderKey := fmt.Sprintf("order:%d", i)
        pipe.HSet(ctx, orderKey, "status", "processing")
    }
    
    cmds, err := pipe.Exec(ctx)
    pipeSpan.SetAttributes(
        attribute.Int("db.redis.pipeline.commands", len(cmds)),
        attribute.Int("db.redis.pipeline.executed", len(cmds)),
    )
    
    if err != nil {
        pipeSpan.RecordError(err)
        pipeSpan.SetStatus(codes.Error, err.Error())
    } else {
        pipeSpan.SetStatus(codes.Ok, "")
    }
    pipeSpan.End()
}
```

### 7.2 Pub/Sub追踪

```go
// Publisher
func publishEvent(ctx context.Context, rdb *redis.Client, channel, message string) {
    tracer := otel.Tracer("redis-pubsub")
    
    ctx, span := tracer.Start(ctx, fmt.Sprintf("PUBLISH %s", channel),
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.DBSystemRedis,
            attribute.String("db.operation", "PUBLISH"),
            attribute.String("messaging.destination", channel),
            attribute.String("messaging.system", "redis"),
        ),
    )
    defer span.End()
    
    // 注入TraceContext到消息
    carrier := propagation.MapCarrier{}
    otel.GetTextMapPropagator().Inject(ctx, carrier)
    
    // 序列化消息+context
    payload := map[string]interface{}{
        "data":       message,
        "tracecontext": carrier,
    }
    
    jsonPayload, _ := json.Marshal(payload)
    
    err := rdb.Publish(ctx, channel, jsonPayload).Err()
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
    } else {
        span.SetStatus(codes.Ok, "")
    }
}

// Subscriber
func subscribeEvents(ctx context.Context, rdb *redis.Client, channel string) {
    pubsub := rdb.Subscribe(ctx, channel)
    defer pubsub.Close()
    
    ch := pubsub.Channel()
    
    for msg := range ch {
        // 解析消息
        var payload map[string]interface{}
        json.Unmarshal([]byte(msg.Payload), &payload)
        
        // 提取TraceContext
        carrier := propagation.MapCarrier(payload["tracecontext"].(map[string]string))
        ctx := otel.GetTextMapPropagator().Extract(context.Background(), carrier)
        
        // 创建Consumer Span
        tracer := otel.Tracer("redis-pubsub")
        ctx, span := tracer.Start(ctx, fmt.Sprintf("CONSUME %s", channel),
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.DBSystemRedis,
                attribute.String("messaging.destination", channel),
                attribute.String("messaging.system", "redis"),
            ),
        )
        
        // 处理消息
        processMessage(ctx, payload["data"].(string))
        
        span.End()
    }
}
```

---

## 8. 性能考虑

```text
1. 采样策略
   # 高频命令采样
   if command in ["GET", "SET"]:
       sample_rate = 0.01  # 1%
   else:
       sample_rate = 1.0   # 100%

2. 批处理优化
   # 使用Pipeline减少网络往返
   pipe = rdb.pipeline()
   for key in keys:
       pipe.get(key)
   results = pipe.execute()
   
   # 一个Span vs 多个Span

3. 连接池监控
   # 监控指标
   - pool.connections.active
   - pool.connections.idle
   - pool.wait_duration
   - pool.timeouts

4. 慢命令追踪
   # 仅追踪慢命令
   if duration > 100ms:
       create_span()
```

---

## 9. 最佳实践

```text
✅ DO (推荐)
1. 使用官方Instrumentation库
2. 脱敏Key和Value
3. Pipeline操作创建单个Span
4. 记录命令执行时间
5. 追踪连接池状态
6. 监控缓存命中率
7. 追踪Pub/Sub消息流
8. 合理采样高频命令

❌ DON'T (避免)
1. 不要记录完整Value
2. 不要为每个命令创建独立Span (Pipeline)
3. 不要100%采样高频命令
4. 不要忽略连接错误
5. 不要暴露敏感Key
6. 不要跳过Pipeline追踪

Key脱敏示例:
✅ session:? (推荐)
❌ session:abc123 (暴露信息)

Value脱敏:
✅ SET key ? (推荐)
❌ SET key "user_password" (暴露密码)

Span命名:
✅ GET user:* (推荐)
✅ MGET 100 keys (推荐)
❌ GET user:123 (太具体)

监控指标:
✅ 追踪以下指标
- redis.commands.duration (命令耗时)
- redis.connections.active (活跃连接)
- redis.cache.hit_rate (命中率)
- redis.errors.total (错误总数)
```

---

## 10. 参考资源

- **OpenTelemetry Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/database/redis/>
- **Go Redis Instrumentation**: <https://github.com/go-redis/redis>
- **Python Redis Instrumentation**: <https://opentelemetry-python-contrib.readthedocs.io/en/latest/instrumentation/redis/redis.html>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [Kafka语义约定](01_Kafka.md), [数据库语义约定](../02_追踪属性/03_数据库.md)

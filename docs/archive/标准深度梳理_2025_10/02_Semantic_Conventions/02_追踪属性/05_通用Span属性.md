# Span 通用属性

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Span 通用属性](#span-通用属性)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是Span通用属性](#11-什么是span通用属性)
    - [1.2 属性分类](#12-属性分类)
  - [2. 网络属性](#2-网络属性)
    - [2.1 传输层属性](#21-传输层属性)
    - [2.2 连接属性](#22-连接属性)
    - [2.3 对等点属性](#23-对等点属性)
    - [2.4 主机属性](#24-主机属性)
  - [3. 错误属性](#3-错误属性)
    - [3.1 错误标记](#31-错误标记)
    - [3.2 异常属性](#32-异常属性)
    - [3.3 Go示例](#33-go示例)
  - [4. 用户与会话属性](#4-用户与会话属性)
    - [4.1 用户标识](#41-用户标识)
    - [4.2 会话标识](#42-会话标识)
  - [5. 线程与代码位置属性](#5-线程与代码位置属性)
    - [5.1 线程信息](#51-线程信息)
    - [5.2 代码位置](#52-代码位置)
  - [6. 对等服务属性](#6-对等服务属性)
  - [7. SpanKind特定属性](#7-spankind特定属性)
    - [7.1 CLIENT Span](#71-client-span)
    - [7.2 SERVER Span](#72-server-span)
    - [7.3 PRODUCER Span](#73-producer-span)
    - [7.4 CONSUMER Span](#74-consumer-span)
    - [7.5 INTERNAL Span](#75-internal-span)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 属性选择原则](#81-属性选择原则)
    - [8.2 命名规范](#82-命名规范)
    - [8.3 值类型选择](#83-值类型选择)
  - [9. 完整示例](#9-完整示例)
    - [9.1 Go HTTP客户端](#91-go-http客户端)
    - [9.2 Python数据库查询](#92-python数据库查询)
    - [9.3 Java消息生产者](#93-java消息生产者)
  - [10. 参考资源](#10-参考资源)
    - [官方文档](#官方文档)
    - [相关规范](#相关规范)
    - [SDK文档](#sdk文档)

---

## 1. 概述

### 1.1 什么是Span通用属性

**Span通用属性**是适用于所有或多种类型Span的标准化属性，不依赖于特定的协议、系统或技术栈。

**核心目的**:

```text
✅ 提供跨系统的一致性
✅ 简化查询和分析
✅ 支持自动化告警和监控
✅ 促进工具之间的互操作性
```

### 1.2 属性分类

```text
1. 网络属性
   ├─ 传输层 (net.transport, net.protocol.*)
   ├─ 对等点 (net.peer.*)
   └─ 主机 (net.host.*)

2. 错误属性
   ├─ error (布尔标记)
   ├─ exception.* (异常详情)
   └─ error.type (错误类型)

3. 用户与会话属性
   ├─ enduser.* (用户标识)
   └─ session.* (会话信息)

4. 线程与代码位置
   ├─ thread.* (线程信息)
   └─ code.* (代码位置)

5. 对等服务
   └─ peer.service (对等服务名)
```

---

## 2. 网络属性

### 2.1 传输层属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `net.transport` | string | 传输协议 | `ip_tcp`, `ip_udp`, `pipe`, `inproc` |
| `net.protocol.name` | string | 应用层协议名 | `http`, `grpc`, `amqp` |
| `net.protocol.version` | string | 协议版本 | `1.1`, `2.0`, `3.0` |
| `net.sock.family` | string | Socket协议族 | `inet`, `inet6`, `unix` |

**传输协议枚举**:

```text
ip_tcp:   TCP over IP
ip_udp:   UDP over IP  
pipe:     Named or anonymous pipe
inproc:   进程内通信
unix:     Unix Domain Socket
```

**示例**:

```go
span.SetAttributes(
    attribute.String("net.transport", "ip_tcp"),
    attribute.String("net.protocol.name", "http"),
    attribute.String("net.protocol.version", "1.1"),
    attribute.String("net.sock.family", "inet"),
)
```

### 2.2 连接属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `net.sock.peer.addr` | string | 远程socket地址 | `192.168.0.1`, `::1` |
| `net.sock.peer.port` | int | 远程socket端口 | `8080` |
| `net.sock.host.addr` | string | 本地socket地址 | `10.0.0.5` |
| `net.sock.host.port` | int | 本地socket端口 | `443` |

### 2.3 对等点属性

用于描述客户端连接的远程端点。

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `net.peer.name` | string | 远程主机名或域名 | `example.com` |
| `net.peer.port` | int | 远程端口 | `80`, `443` |
| `net.peer.ip` | string | 远程IP地址 | `192.168.1.1` |

**使用场景**: CLIENT Span

**示例**:

```go
// HTTP客户端调用
span.SetAttributes(
    attribute.String("net.peer.name", "api.example.com"),
    attribute.Int("net.peer.port", 443),
    attribute.String("net.peer.ip", "203.0.113.42"),
)
```

### 2.4 主机属性

用于描述服务器端监听的端点。

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `net.host.name` | string | 本地主机名 | `web-server-01` |
| `net.host.port` | int | 本地监听端口 | `8080` |
| `net.host.ip` | string | 本地IP地址 | `10.0.0.5` |
| `net.host.connection.type` | string | 连接类型 | `wifi`, `wired`, `cell` |
| `net.host.connection.subtype` | string | 连接子类型 | `gprs`, `edge`, `lte` |
| `net.host.carrier.name` | string | 移动运营商 | `China Mobile` |
| `net.host.carrier.mcc` | string | 移动国家码 | `460` |
| `net.host.carrier.mnc` | string | 移动网络码 | `00` |
| `net.host.carrier.icc` | string | ISO国家码 | `CN` |

**使用场景**: SERVER Span

---

## 3. 错误属性

### 3.1 错误标记

| 属性名 | 类型 | 描述 | 取值 |
|--------|------|------|------|
| `error` | boolean | Span是否包含错误 | `true` / `false` |

**已废弃**: 在新版本中，推荐使用Span Status而不是`error`属性。

### 3.2 异常属性

当Span中发生异常时，应记录以下属性：

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `exception.type` | string | 异常类型 | `java.net.ConnectException` |
| `exception.message` | string | 异常消息 | `Connection refused` |
| `exception.stacktrace` | string | 堆栈跟踪 | `at java.net...` |
| `exception.escaped` | boolean | 异常是否逃逸出Span | `true` |

**注意**: 异常信息通常通过`span.RecordException()`记录，而不是手动设置属性。

### 3.3 Go示例

```go
package main

import (
    "context"
    "errors"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

func ProcessWithError(ctx context.Context) error {
    tracer := otel.Tracer("example")
    ctx, span := tracer.Start(ctx, "process-operation")
    defer span.End()
    
    err := doSomething()
    if err != nil {
        // 记录异常
        span.RecordException(err)
        
        // 设置Span状态为Error
        span.SetStatus(codes.Error, err.Error())
        
        return err
    }
    
    span.SetStatus(codes.Ok, "Success")
    return nil
}

func doSomething() error {
    return errors.New("connection timeout")
}
```

**Python示例**:

```python
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode

def process_with_error(span):
    try:
        # 可能抛出异常的操作
        result = risky_operation()
        span.set_status(Status(StatusCode.OK))
        return result
    except Exception as e:
        # 记录异常
        span.record_exception(e)
        span.set_status(Status(StatusCode.ERROR, str(e)))
        raise
```

---

## 4. 用户与会话属性

### 4.1 用户标识

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `enduser.id` | string | 用户唯一标识符 | `user123`, `john.doe@example.com` |
| `enduser.role` | string | 用户角色 | `admin`, `user`, `guest` |
| `enduser.scope` | string | 用户权限范围 | `read:messages write:messages` |

**使用场景**:

- Web应用请求追踪
- API调用追踪
- 用户行为分析

**隐私考虑**:

```text
⚠️ 不要记录敏感个人信息（PII）
⚠️ 使用哈希或匿名ID
⚠️ 遵守GDPR等数据保护法规
```

**示例**:

```go
span.SetAttributes(
    // ✅ 使用哈希ID
    attribute.String("enduser.id", "hash:a1b2c3d4"),
    attribute.String("enduser.role", "premium_user"),
)

// ❌ 避免
span.SetAttributes(
    attribute.String("enduser.id", "john.doe@example.com"), // 暴露邮箱
    attribute.String("enduser.name", "John Doe"),            // 暴露姓名
)
```

### 4.2 会话标识

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `session.id` | string | 会话唯一标识符 | `session-abc123` |
| `session.previous_id` | string | 前一个会话ID | `session-xyz789` |

---

## 5. 线程与代码位置属性

### 5.1 线程信息

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `thread.id` | int | 线程ID | `42` |
| `thread.name` | string | 线程名称 | `pool-1-thread-3` |

**Java示例**:

```java
span.setAttribute(
    AttributeKey.longKey("thread.id"),
    Thread.currentThread().getId()
);
span.setAttribute(
    AttributeKey.stringKey("thread.name"),
    Thread.currentThread().getName()
);
```

### 5.2 代码位置

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `code.function` | string | 函数名 | `processRequest` |
| `code.namespace` | string | 命名空间/包名 | `com.example.api` |
| `code.filepath` | string | 文件路径 | `/app/handler.go` |
| `code.lineno` | int | 行号 | `42` |
| `code.column` | int | 列号 | `10` |

**自动记录示例** (Go):

```go
import (
    "runtime"
    "go.opentelemetry.io/otel/attribute"
)

func recordCodeLocation(span trace.Span) {
    pc, file, line, ok := runtime.Caller(1)
    if !ok {
        return
    }
    
    fn := runtime.FuncForPC(pc)
    if fn == nil {
        return
    }
    
    span.SetAttributes(
        attribute.String("code.function", fn.Name()),
        attribute.String("code.filepath", file),
        attribute.Int("code.lineno", line),
    )
}
```

---

## 6. 对等服务属性

| 属性名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `peer.service` | string | 被调用的远程服务名 | `auth-service`, `payment-api` |

**使用场景**: 当Span表示对另一个服务的调用时。

**与net.peer.name的区别**:

```text
peer.service:    逻辑服务名（如 "payment-api"）
net.peer.name:   物理主机名（如 "payment-01.example.com"）
```

**示例**:

```go
// 调用支付服务
span.SetAttributes(
    attribute.String("peer.service", "payment-service"),
    attribute.String("net.peer.name", "payment-01.prod.example.com"),
    attribute.Int("net.peer.port", 8080),
)
```

---

## 7. SpanKind特定属性

### 7.1 CLIENT Span

**必需**:

```text
✅ peer.service 或 net.peer.name
```

**推荐**:

```text
✅ net.peer.port
✅ net.transport
```

### 7.2 SERVER Span

**推荐**:

```text
✅ net.host.name
✅ net.host.port
```

### 7.3 PRODUCER Span

**必需**:

```text
✅ messaging.destination (队列/主题名)
```

**推荐**:

```text
✅ messaging.system
✅ net.peer.name
```

### 7.4 CONSUMER Span

**必需**:

```text
✅ messaging.source (队列/主题名)
```

**推荐**:

```text
✅ messaging.system
✅ messaging.operation
```

### 7.5 INTERNAL Span

**推荐**:

```text
✅ code.function
✅ code.namespace
```

---

## 8. 最佳实践

### 8.1 属性选择原则

**优先级**:

```text
P0 (必须): 
  协议特定的必需属性

P1 (强烈推荐):
  ✅ SpanKind对应的标准属性
  ✅ 网络传输层基础属性
  ✅ 错误和异常信息

P2 (推荐):
  ✅ 用户标识（注意隐私）
  ✅ 对等服务名
  ✅ 线程信息

P3 (可选):
  ✅ 代码位置
  ✅ 会话信息
  ✅ 自定义业务属性
```

### 8.2 命名规范

**✅ 推荐**:

```text
- 使用小写字母
- 使用点分隔命名空间
- 使用下划线分隔单词
- 保持简洁但有意义
```

**示例**:

```text
✅ net.peer.name
✅ db.connection.string
✅ messaging.destination.name

❌ NetPeerName (使用驼峰)
❌ net-peer-name (使用连字符)
❌ networkPeerHostname (过长)
```

### 8.3 值类型选择

| 类型 | 使用场景 | 示例 |
|------|----------|------|
| string | 名称、标识符、枚举 | `"http"`, `"GET"` |
| int/int64 | 计数、端口、大小 | `8080`, `1024` |
| double | 比率、百分比 | `0.95`, `99.9` |
| boolean | 标志 | `true`, `false` |
| array | 列表、标签 | `["tag1", "tag2"]` |

---

## 9. 完整示例

### 9.1 Go HTTP客户端

```go
package main

import (
    "context"
    "net/http"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

func HTTPClientCall(ctx context.Context, url string) (*http.Response, error) {
    tracer := otel.Tracer("http-client")
    
    // 创建CLIENT Span
    ctx, span := tracer.Start(ctx, "HTTP GET",
        trace.WithSpanKind(trace.SpanKindClient),
        trace.WithAttributes(
            // HTTP特定属性
            attribute.String("http.method", "GET"),
            attribute.String("http.url", url),
            attribute.String("http.scheme", "https"),
            
            // 网络通用属性
            attribute.String("net.transport", "ip_tcp"),
            attribute.String("net.protocol.name", "http"),
            attribute.String("net.protocol.version", "1.1"),
            attribute.String("net.peer.name", "api.example.com"),
            attribute.Int("net.peer.port", 443),
            
            // 对等服务
            attribute.String("peer.service", "api-service"),
            
            // 用户标识（如果已认证）
            attribute.String("enduser.id", "user-hash-123"),
            attribute.String("enduser.role", "premium"),
        ),
    )
    defer span.End()
    
    // 执行HTTP请求
    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        span.RecordException(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    
    resp, err := http.DefaultClient.Do(req)
    if err != nil {
        span.RecordException(err)
        span.SetStatus(codes.Error, err.Error())
        return nil, err
    }
    
    // 记录响应属性
    span.SetAttributes(
        attribute.Int("http.status_code", resp.StatusCode),
        attribute.Int64("http.response_content_length", resp.ContentLength),
    )
    
    if resp.StatusCode >= 400 {
        span.SetStatus(codes.Error, "HTTP error response")
    } else {
        span.SetStatus(codes.Ok, "Success")
    }
    
    return resp, nil
}
```

### 9.2 Python数据库查询

```python
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode
import pymysql

def execute_query(query):
    tracer = trace.get_tracer(__name__)
    
    with tracer.start_as_current_span(
        "mysql.query",
        kind=trace.SpanKind.CLIENT,
        attributes={
            # 数据库特定属性
            "db.system": "mysql",
            "db.name": "production",
            "db.statement": query,
            "db.operation": "SELECT",
            "db.sql.table": "users",
            
            # 网络通用属性
            "net.transport": "ip_tcp",
            "net.peer.name": "mysql-primary.example.com",
            "net.peer.port": 3306,
            
            # 对等服务
            "peer.service": "mysql-cluster",
            
            # 线程信息
            "thread.id": threading.get_ident(),
            "thread.name": threading.current_thread().name,
        }
    ) as span:
        try:
            connection = pymysql.connect(
                host='mysql-primary.example.com',
                port=3306,
                user='app_user',
                database='production'
            )
            
            with connection.cursor() as cursor:
                cursor.execute(query)
                results = cursor.fetchall()
                
                # 记录结果数量
                span.set_attribute("db.rows_affected", len(results))
                
                span.set_status(Status(StatusCode.OK))
                return results
                
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR, str(e)))
            raise
        finally:
            if 'connection' in locals():
                connection.close()
```

### 9.3 Java消息生产者

```java
import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.SpanKind;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.common.AttributeKey;
import io.opentelemetry.context.Scope;

public class MessageProducer {
    private final Tracer tracer;
    
    public MessageProducer(OpenTelemetry openTelemetry) {
        this.tracer = openTelemetry.getTracer("message-producer");
    }
    
    public void sendMessage(String destination, String message) {
        // 创建PRODUCER Span
        Span span = tracer.spanBuilder("send")
            .setSpanKind(SpanKind.PRODUCER)
            .setAttribute(AttributeKey.stringKey("messaging.system"), "kafka")
            .setAttribute(AttributeKey.stringKey("messaging.destination"), destination)
            .setAttribute(AttributeKey.stringKey("messaging.destination.kind"), "topic")
            .setAttribute(AttributeKey.stringKey("messaging.protocol"), "kafka")
            .setAttribute(AttributeKey.stringKey("messaging.protocol.version"), "2.8.0")
            
            // 网络通用属性
            .setAttribute(AttributeKey.stringKey("net.transport"), "ip_tcp")
            .setAttribute(AttributeKey.stringKey("net.peer.name"), "kafka-broker-01")
            .setAttribute(AttributeKey.intKey("net.peer.port"), 9092)
            
            // 对等服务
            .setAttribute(AttributeKey.stringKey("peer.service"), "kafka-cluster")
            
            // 消息属性
            .setAttribute(AttributeKey.longKey("messaging.message.payload_size_bytes"), 
                         message.getBytes().length)
            
            // 线程信息
            .setAttribute(AttributeKey.longKey("thread.id"), 
                         Thread.currentThread().getId())
            .setAttribute(AttributeKey.stringKey("thread.name"), 
                         Thread.currentThread().getName())
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 发送消息到Kafka
            sendToKafka(destination, message);
            
            span.setStatus(StatusCode.OK);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR, e.getMessage());
            throw e;
            
        } finally {
            span.end();
        }
    }
    
    private void sendToKafka(String destination, String message) {
        // 实际Kafka发送逻辑
    }
}
```

---

## 10. 参考资源

### 官方文档

- **OpenTelemetry Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/>
- **General Attributes**: <https://opentelemetry.io/docs/specs/semconv/general/attributes/>
- **Span Conventions**: <https://opentelemetry.io/docs/specs/semconv/general/trace/>

### 相关规范

- **W3C Trace Context**: <https://www.w3.org/TR/trace-context/>
- **OpenTelemetry Specification**: <https://github.com/open-telemetry/opentelemetry-specification>

### SDK文档

- **Go SDK**: <https://pkg.go.dev/go.opentelemetry.io/otel>
- **Python SDK**: <https://opentelemetry-python.readthedocs.io/>
- **Java SDK**: <https://opentelemetry.io/docs/instrumentation/java/>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

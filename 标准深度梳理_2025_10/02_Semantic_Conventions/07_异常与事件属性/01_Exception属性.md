# Exception 异常属性

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Exception 异常属性](#exception-异常属性)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 异常事件属性](#2-异常事件属性)
    - [2.1 exception.type](#21-exceptiontype)
    - [2.2 exception.message](#22-exceptionmessage)
    - [2.3 exception.stacktrace](#23-exceptionstacktrace)
    - [2.4 exception.escaped](#24-exceptionescaped)
  - [3. RecordException使用](#3-recordexception使用)
    - [3.1 Go SDK](#31-go-sdk)
    - [3.2 Python SDK](#32-python-sdk)
    - [3.3 Java SDK](#33-java-sdk)
    - [3.4 JavaScript/Node.js SDK](#34-javascriptnodejs-sdk)
  - [4. 异常Span状态](#4-异常span状态)
    - [4.1 状态码映射](#41-状态码映射)
    - [4.2 完整异常处理模式](#42-完整异常处理模式)
  - [5. 最佳实践](#5-最佳实践)
    - [5.1 何时记录异常](#51-何时记录异常)
    - [5.2 敏感信息处理](#52-敏感信息处理)
    - [5.3 多次异常记录](#53-多次异常记录)
    - [5.4 异常与Span Status](#54-异常与span-status)
  - [6. 完整示例](#6-完整示例)
    - [6.1 Go HTTP客户端异常处理](#61-go-http客户端异常处理)
    - [6.2 Python数据库操作异常处理](#62-python数据库操作异常处理)
    - [6.3 Java批处理异常处理](#63-java批处理异常处理)
  - [7. 参考资源](#7-参考资源)
    - [官方文档](#官方文档)
    - [SDK文档](#sdk文档)

---

## 1. 概述

**异常属性**用于记录Span执行过程中发生的异常信息，包括异常类型、消息、堆栈跟踪等。

**核心特性**:

```text
✅ 标准化异常记录
✅ 自动堆栈跟踪捕获
✅ 支持多次异常记录
✅ 与Span状态集成
```

---

## 2. 异常事件属性

当异常发生时，通过Span Event记录以下属性：

| 属性名 | 类型 | 必需 | 描述 | 示例 |
|--------|------|------|------|------|
| `exception.type` | string | ✅ | 异常类型/类名 | `java.net.ConnectException`, `ValueError` |
| `exception.message` | string | ❌ | 异常消息 | `Connection refused`, `invalid literal` |
| `exception.stacktrace` | string | ❌ | 堆栈跟踪 | `at com.example...` |
| `exception.escaped` | boolean | ❌ | 异常是否逃逸出Span边界 | `true` / `false` |

### 2.1 exception.type

**定义**: 异常的完全限定类名或类型标识。

**格式**:

```text
Java:   java.lang.NullPointerException
Python: builtins.ValueError
Go:     *errors.errorString
C#:     System.ArgumentNullException
```

### 2.2 exception.message

**定义**: 异常的描述性消息。

**注意事项**:

```text
⚠️ 避免包含敏感信息（密码、令牌等）
⚠️ 保持简洁明了
⚠️ 使用英文（便于自动化处理）
```

### 2.3 exception.stacktrace

**定义**: 异常发生时的完整堆栈跟踪。

**格式**: 与语言运行时生成的格式一致。

**示例**:

```java
java.lang.NullPointerException: Cannot invoke method on null object
    at com.example.service.UserService.getUser(UserService.java:42)
    at com.example.controller.UserController.handleRequest(UserController.java:28)
    at sun.reflect.NativeMethodAccessorImpl.invoke0(Native Method)
    ...
```

### 2.4 exception.escaped

**定义**: 异常是否逃逸出当前Span的边界（即未被Span内捕获）。

**取值**:

```text
true:  异常传播到Span外部
false: 异常在Span内被捕获处理（默认值）
```

**使用场景**:

```go
func ProcessRequest(ctx context.Context) (err error) {
    ctx, span := tracer.Start(ctx, "process")
    defer func() {
        if err != nil {
            span.RecordException(err,
                trace.WithAttributes(
                    attribute.Bool("exception.escaped", true), // 异常返回给调用者
                ),
            )
        }
        span.End()
    }()
    
    return doSomething() // 可能返回错误
}
```

---

## 3. RecordException使用

### 3.1 Go SDK

```go
package main

import (
    "context"
    "errors"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

func ProcessWithException(ctx context.Context) error {
    tracer := otel.Tracer("example")
    ctx, span := tracer.Start(ctx, "process")
    defer span.End()
    
    err := doSomething()
    if err != nil {
        // 记录异常
        span.RecordException(err)
        
        // 设置Span状态
        span.SetStatus(codes.Error, err.Error())
        
        return err
    }
    
    span.SetStatus(codes.Ok, "Success")
    return nil
}

func doSomething() error {
    return errors.New("something went wrong")
}
```

### 3.2 Python SDK

```python
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode

def process_with_exception():
    tracer = trace.get_tracer(__name__)
    
    with tracer.start_as_current_span("process") as span:
        try:
            result = risky_operation()
            span.set_status(Status(StatusCode.OK))
            return result
        except Exception as e:
            # 记录异常（自动捕获type、message、stacktrace）
            span.record_exception(e)
            
            # 设置Span状态
            span.set_status(Status(StatusCode.ERROR, str(e)))
            
            # 重新抛出或处理
            raise

def risky_operation():
    raise ValueError("Invalid input")
```

### 3.3 Java SDK

```java
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;

public void processWithException() {
    Span span = tracer.spanBuilder("process").startSpan();
    
    try (Scope scope = span.makeCurrent()) {
        riskyOperation();
        span.setStatus(StatusCode.OK);
        
    } catch (Exception e) {
        // 记录异常
        span.recordException(e);
        
        // 设置Span状态
        span.setStatus(StatusCode.ERROR, e.getMessage());
        
        throw e;
        
    } finally {
        span.end();
    }
}
```

### 3.4 JavaScript/Node.js SDK

```javascript
const { trace, SpanStatusCode } = require('@opentelemetry/api');

async function processWithException() {
    const tracer = trace.getTracer('example');
    const span = tracer.startSpan('process');
    
    try {
        const result = await riskyOperation();
        span.setStatus({ code: SpanStatusCode.OK });
        return result;
        
    } catch (error) {
        // 记录异常
        span.recordException(error);
        
        // 设置Span状态
        span.setStatus({
            code: SpanStatusCode.ERROR,
            message: error.message
        });
        
        throw error;
        
    } finally {
        span.end();
    }
}
```

---

## 4. 异常Span状态

### 4.1 状态码映射

当异常发生时，应设置Span状态：

| 情况 | StatusCode | 描述 |
|------|------------|------|
| 无异常 | `Ok` | 操作成功完成 |
| 有异常 | `Error` | 操作因异常失败 |
| 未设置 | `Unset` | 状态未明确（默认） |

### 4.2 完整异常处理模式

```go
func CompleteExceptionHandling(ctx context.Context) (err error) {
    ctx, span := tracer.Start(ctx, "operation")
    
    // defer确保Span总是被结束
    defer func() {
        // 处理panic
        if r := recover(); r != nil {
            err = fmt.Errorf("panic recovered: %v", r)
            span.RecordException(err,
                trace.WithAttributes(
                    attribute.Bool("exception.escaped", true),
                    attribute.String("exception.type", "panic"),
                ),
            )
            span.SetStatus(codes.Error, err.Error())
        }
        
        // 处理返回的error
        if err != nil && !span.IsRecording() {
            span.RecordException(err,
                trace.WithAttributes(
                    attribute.Bool("exception.escaped", true),
                ),
            )
            span.SetStatus(codes.Error, err.Error())
        }
        
        span.End()
    }()
    
    // 业务逻辑
    return businessLogic(ctx)
}
```

---

## 5. 最佳实践

### 5.1 何时记录异常

**✅ 应该记录**:

```text
- 影响操作结果的错误
- 业务逻辑异常
- 外部依赖失败
- 超时和取消
- 资源耗尽
```

**❌ 不应记录**:

```text
- 正常的业务流程（如"用户未找到"）
- 预期的验证错误
- 调试日志
- 重试前的临时错误
```

### 5.2 敏感信息处理

**避免记录敏感信息**:

```go
// ❌ 不好
err := fmt.Errorf("authentication failed for user %s with password %s", username, password)
span.RecordException(err)

// ✅ 推荐
err := fmt.Errorf("authentication failed for user %s", username)
span.RecordException(err)

// ✅ 更好
err := errors.New("authentication failed")
span.RecordException(err)
span.SetAttributes(
    attribute.String("auth.user_id", hashUserID(username)),
)
```

### 5.3 多次异常记录

**Span可以记录多个异常**:

```python
span = tracer.start_span("batch_process")

for item in items:
    try:
        process_item(item)
    except Exception as e:
        # 记录每个失败项的异常
        span.record_exception(e)
        span.add_event("item_failed", {
            "item_id": item.id,
            "error": str(e)
        })
        
span.end()
```

### 5.4 异常与Span Status

**规则**:

```text
1. 记录异常时，应设置Span状态为Error
2. Span状态为Error时，不一定要有异常记录
3. 多个异常时，通常只设置一次Error状态
```

**示例**:

```go
// 场景1: 单个异常
if err != nil {
    span.RecordException(err)           // 记录异常
    span.SetStatus(codes.Error, err.Error())  // 设置状态
}

// 场景2: Error状态但无异常
if httpCode >= 500 {
    // HTTP 500错误，但不是Go异常
    span.SetStatus(codes.Error, "Server error")
    // 不调用RecordException
}
```

---

## 6. 完整示例

### 6.1 Go HTTP客户端异常处理

```go
package main

import (
    "context"
    "fmt"
    "net/http"
    "time"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    "go.opentelemetry.io/otel/trace"
)

func HTTPGetWithExceptionHandling(ctx context.Context, url string) (*http.Response, error) {
    tracer := otel.Tracer("http-client")
    
    ctx, span := tracer.Start(ctx, "HTTP GET",
        trace.WithAttributes(
            attribute.String("http.url", url),
            attribute.String("http.method", "GET"),
        ),
    )
    defer span.End()
    
    // 创建请求
    req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
    if err != nil {
        span.RecordException(err,
            trace.WithAttributes(
                attribute.String("error.phase", "request_creation"),
                attribute.Bool("exception.escaped", true),
            ),
        )
        span.SetStatus(codes.Error, "Failed to create request")
        return nil, fmt.Errorf("create request: %w", err)
    }
    
    // 执行请求（带超时）
    client := &http.Client{Timeout: 10 * time.Second}
    resp, err := client.Do(req)
    if err != nil {
        span.RecordException(err,
            trace.WithAttributes(
                attribute.String("error.phase", "request_execution"),
                attribute.Bool("exception.escaped", true),
            ),
        )
        span.SetStatus(codes.Error, "HTTP request failed")
        return nil, fmt.Errorf("execute request: %w", err)
    }
    
    // 检查HTTP状态码
    span.SetAttributes(
        attribute.Int("http.status_code", resp.StatusCode),
    )
    
    if resp.StatusCode >= 500 {
        // HTTP错误，但不是Go exception
        span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", resp.StatusCode))
        // 不调用RecordException
    } else if resp.StatusCode >= 400 {
        // 客户端错误
        span.SetStatus(codes.Error, fmt.Sprintf("HTTP %d", resp.StatusCode))
    } else {
        span.SetStatus(codes.Ok, "Success")
    }
    
    return resp, nil
}
```

### 6.2 Python数据库操作异常处理

```python
from opentelemetry import trace
from opentelemetry.trace import Status, StatusCode
import pymysql

def database_query_with_exception_handling(query):
    tracer = trace.get_tracer(__name__)
    
    with tracer.start_as_current_span(
        "db.query",
        attributes={
            "db.system": "mysql",
            "db.statement": query,
        }
    ) as span:
        connection = None
        try:
            # 连接数据库
            connection = pymysql.connect(
                host='localhost',
                user='user',
                database='mydb',
                connect_timeout=5
            )
            
            with connection.cursor() as cursor:
                cursor.execute(query)
                results = cursor.fetchall()
                
                span.set_attribute("db.rows_returned", len(results))
                span.set_status(Status(StatusCode.OK))
                
                return results
                
        except pymysql.err.OperationalError as e:
            # 连接/操作错误
            span.record_exception(e)
            span.set_attribute("exception.escaped", True)
            span.set_status(Status(StatusCode.ERROR, "Database connection failed"))
            raise
            
        except pymysql.err.ProgrammingError as e:
            # SQL语法错误
            span.record_exception(e)
            span.set_attribute("exception.escaped", True)
            span.set_status(Status(StatusCode.ERROR, "Invalid SQL"))
            raise
            
        except Exception as e:
            # 其他未预期的异常
            span.record_exception(e)
            span.set_attribute("exception.escaped", True)
            span.set_attribute("exception.unexpected", True)
            span.set_status(Status(StatusCode.ERROR, "Unexpected error"))
            raise
            
        finally:
            if connection:
                connection.close()
```

### 6.3 Java批处理异常处理

```java
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.StatusCode;
import io.opentelemetry.api.common.AttributeKey;
import io.opentelemetry.api.common.Attributes;

public class BatchProcessor {
    
    public void processBatch(List<Item> items) {
        Span span = tracer.spanBuilder("batch.process")
            .setAttribute("batch.size", items.size())
            .startSpan();
        
        int successCount = 0;
        int failureCount = 0;
        
        try (Scope scope = span.makeCurrent()) {
            for (int i = 0; i < items.size(); i++) {
                Item item = items.get(i);
                try {
                    processItem(item);
                    successCount++;
                    
                } catch (Exception e) {
                    failureCount++;
                    
                    // 记录每个失败的异常
                    span.recordException(e,
                        Attributes.of(
                            AttributeKey.longKey("item.index"), (long)i,
                            AttributeKey.stringKey("item.id"), item.getId(),
                            AttributeKey.booleanKey("exception.escaped"), false
                        )
                    );
                    
                    // 记录失败事件
                    span.addEvent("item.failed",
                        Attributes.of(
                            AttributeKey.longKey("item.index"), (long)i,
                            AttributeKey.stringKey("error.message"), e.getMessage()
                        )
                    );
                }
            }
            
            // 设置统计信息
            span.setAttribute("batch.success_count", successCount);
            span.setAttribute("batch.failure_count", failureCount);
            
            // 设置Span状态
            if (failureCount == 0) {
                span.setStatus(StatusCode.OK);
            } else if (failureCount < items.size()) {
                span.setStatus(StatusCode.ERROR, 
                    String.format("Partial failure: %d/%d items failed", 
                                  failureCount, items.size()));
            } else {
                span.setStatus(StatusCode.ERROR, "All items failed");
            }
            
        } finally {
            span.end();
        }
    }
    
    private void processItem(Item item) throws Exception {
        // 处理单个项目
        if (item.isInvalid()) {
            throw new IllegalArgumentException("Invalid item: " + item.getId());
        }
        // ... 实际处理逻辑
    }
}
```

---

## 7. 参考资源

### 官方文档

- **OpenTelemetry Exception Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/exceptions/exceptions-spans/>
- **Span Status Specification**: <https://opentelemetry.io/docs/specs/otel/trace/api/#set-status>

### SDK文档

- **Go SDK - RecordException**: <https://pkg.go.dev/go.opentelemetry.io/otel/trace#Span>
- **Python SDK - record_exception**: <https://opentelemetry-python.readthedocs.io/en/latest/sdk/trace.html>
- **Java SDK - recordException**: <https://javadoc.io/doc/io.opentelemetry/opentelemetry-api/latest/io/opentelemetry/api/trace/Span.html>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

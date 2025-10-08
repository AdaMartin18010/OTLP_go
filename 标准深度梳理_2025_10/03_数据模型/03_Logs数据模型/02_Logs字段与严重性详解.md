# Logs 字段与严重性详解

> **标准版本**: v1.27.0  
> **状态**: Stable  
> **最后更新**: 2025年10月8日

---

## 目录

- [Logs 字段与严重性详解](#logs-字段与严重性详解)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. LogRecord核心字段](#2-logrecord核心字段)
    - [2.1 必需字段](#21-必需字段)
    - [2.2 推荐字段](#22-推荐字段)
    - [2.3 可选字段](#23-可选字段)
  - [3. 严重性级别](#3-严重性级别)
    - [3.1 严重性枚举](#31-严重性枚举)
    - [3.2 级别映射](#32-级别映射)
    - [3.3 使用指南](#33-使用指南)
  - [4. Body字段详解](#4-body字段详解)
  - [5. Attributes详解](#5-attributes详解)
    - [常用属性](#常用属性)
    - [示例](#示例)
  - [6. 结构化日志](#6-结构化日志)
    - [6.1 结构化vs非结构化](#61-结构化vs非结构化)
    - [6.2 结构化日志优势](#62-结构化日志优势)
  - [7. 完整示例](#7-完整示例)
    - [7.1 Go完整示例](#71-go完整示例)
    - [7.2 Python完整示例](#72-python完整示例)
    - [7.3 Java完整示例](#73-java完整示例)
  - [8. 参考资源](#8-参考资源)
    - [官方文档](#官方文档)
    - [SDK文档](#sdk文档)

---

## 1. 概述

OpenTelemetry Logs数据模型定义了标准化的日志记录格式，支持结构化日志和传统日志的统一表示。

**核心特性**：

```text
✅ 统一日志格式
✅ 标准严重性级别
✅ 结构化属性
✅ Trace关联
✅ 资源属性
```

---

## 2. LogRecord核心字段

### 2.1 必需字段

| 字段名 | 类型 | 描述 |
|--------|------|------|
| `Timestamp` | uint64 | 日志记录时间戳（纳秒） |
| `ObservedTimestamp` | uint64 | 日志被观察/收集的时间戳 |

### 2.2 推荐字段

| 字段名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `SeverityNumber` | int32 | 数值严重性级别 | 9 (INFO) |
| `SeverityText` | string | 文本严重性级别 | "INFO" |
| `Body` | any | 日志消息主体 | "User logged in" |

### 2.3 可选字段

| 字段名 | 类型 | 描述 | 示例 |
|--------|------|------|------|
| `TraceId` | bytes | 关联的Trace ID | `4bf92f3577b34da6a3ce929d0e0e4736` |
| `SpanId` | bytes | 关联的Span ID | `00f067aa0ba902b7` |
| `TraceFlags` | uint8 | Trace标志 | 1 (sampled) |
| `Attributes` | map | 键值对属性 | `{"user.id": "123"}` |
| `DroppedAttributesCount` | uint32 | 被丢弃的属性数 | 0 |

---

## 3. 严重性级别

### 3.1 严重性枚举

OpenTelemetry定义了24个严重性级别：

| SeverityNumber | SeverityText | 说明 | 使用场景 |
|----------------|--------------|------|----------|
| 1-4 | TRACE, TRACE2-4 | 追踪级别 | 详细调试信息 |
| 5-8 | DEBUG, DEBUG2-4 | 调试级别 | 调试信息 |
| 9-12 | INFO, INFO2-4 | 信息级别 | 一般信息 |
| 13-16 | WARN, WARN2-4 | 警告级别 | 警告消息 |
| 17-20 | ERROR, ERROR2-4 | 错误级别 | 错误信息 |
| 21-24 | FATAL, FATAL2-4 | 致命级别 | 致命错误 |

**主要级别**：

```text
TRACE  (1):  最详细的追踪信息
DEBUG  (5):  调试信息
INFO   (9):  ✅ 默认级别，一般信息
WARN   (13): 警告信息
ERROR  (17): 错误信息
FATAL  (21): 致命错误，通常导致程序终止
```

### 3.2 级别映射

**从常见日志框架映射**：

| 框架 | 级别 | OpenTelemetry |
|------|------|---------------|
| **slog (Go)** | DEBUG | DEBUG (5) |
| | INFO | INFO (9) |
| | WARN | WARN (13) |
| | ERROR | ERROR (17) |
| **Python logging** | DEBUG | DEBUG (5) |
| | INFO | INFO (9) |
| | WARNING | WARN (13) |
| | ERROR | ERROR (17) |
| | CRITICAL | FATAL (21) |
| **Log4j (Java)** | TRACE | TRACE (1) |
| | DEBUG | DEBUG (5) |
| | INFO | INFO (9) |
| | WARN | WARN (13) |
| | ERROR | ERROR (17) |
| | FATAL | FATAL (21) |
| **Winston (Node.js)** | silly | TRACE (1) |
| | debug | DEBUG (5) |
| | info | INFO (9) |
| | warn | WARN (13) |
| | error | ERROR (17) |

### 3.3 使用指南

**TRACE (1)**：

```go
// 非常详细的追踪信息
logger.Trace("Entering function processRequest",
    "requestId", requestId,
    "params", params,
)
```

**DEBUG (5)**：

```go
// 调试信息，帮助诊断问题
logger.Debug("Database query executed",
    "query", sql,
    "duration", duration,
    "rows", rowCount,
)
```

**INFO (9)** ✅：

```go
// 一般信息性消息
logger.Info("User logged in successfully",
    "userId", userId,
    "ip", clientIP,
)
```

**WARN (13)**：

```go
// 警告，可能的问题但不影响功能
logger.Warn("API rate limit approaching",
    "userId", userId,
    "remaining", remaining,
    "limit", limit,
)
```

**ERROR (17)**：

```go
// 错误，功能失败但应用可以继续
logger.Error("Failed to process payment",
    "orderId", orderId,
    "error", err.Error(),
)
```

**FATAL (21)**：

```go
// 致命错误，应用无法继续
logger.Fatal("Database connection failed",
    "error", err.Error(),
)
// 通常会退出程序
```

---

## 4. Body字段详解

`Body`字段可以是任何类型：

**1. 字符串（最常见）**：

```go
Body: "User authentication successful"
```

**2. 结构化对象**：

```json
{
  "message": "Order processed",
  "orderId": "ORD-12345",
  "amount": 99.99,
  "currency": "USD"
}
```

**3. 数组**：

```json
["Error occurred", "Connection timeout", "Retry attempt 3"]
```

**最佳实践**：

```text
✅ 简单消息使用字符串
✅ 复杂信息使用结构化对象
✅ 保持Body简洁，详细信息放Attributes
❌ 避免在Body中重复Attributes信息
```

---

## 5. Attributes详解

### 常用属性

**应用属性**：

```text
service.name:     服务名称
service.version:  服务版本
deployment.environment: 部署环境
```

**HTTP属性**：

```text
http.method:      HTTP方法
http.url:         请求URL
http.status_code: 状态码
```

**用户属性**：

```text
user.id:          用户ID
user.role:        用户角色
user.session_id:  会话ID
```

**错误属性**：

```text
error.type:       错误类型
error.message:    错误消息
error.stack:      堆栈跟踪
```

### 示例

**Go SDK**：

```go
logger.InfoContext(ctx, "User action",
    slog.String("user.id", userID),
    slog.String("action", "purchase"),
    slog.Float64("amount", 99.99),
    slog.String("currency", "USD"),
)
```

**Python SDK**：

```python
logger.info("User action",
    extra={
        "user.id": user_id,
        "action": "purchase",
        "amount": 99.99,
        "currency": "USD"
    }
)
```

---

## 6. 结构化日志

### 6.1 结构化vs非结构化

**非结构化日志**：

```text
2025-10-08 10:30:15 INFO User john.doe logged in from 192.168.1.1
```

**结构化日志**：

```json
{
  "timestamp": "2025-10-08T10:30:15Z",
  "severity": "INFO",
  "message": "User logged in",
  "attributes": {
    "user.name": "john.doe",
    "user.ip": "192.168.1.1"
  }
}
```

### 6.2 结构化日志优势

```text
✅ 易于查询和过滤
✅ 支持聚合和分析
✅ 机器可读
✅ 标准化格式
✅ 更好的可观测性
```

---

## 7. 完整示例

### 7.1 Go完整示例

```go
package main

import (
    "context"
    "log/slog"
    "os"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/trace"
)

func main() {
    // 配置OpenTelemetry Logs Bridge
    logger := slog.New(slog.NewJSONHandler(os.Stdout, &slog.HandlerOptions{
        Level: slog.LevelInfo,
    }))
    
    ctx := context.Background()
    
    // INFO级别日志
    logger.InfoContext(ctx, "Application started",
        slog.String("version", "1.0.0"),
        slog.String("environment", "production"),
    )
    
    // 带Trace关联的日志
    tracer := otel.Tracer("example")
    ctx, span := tracer.Start(ctx, "process-order")
    defer span.End()
    
    logger.InfoContext(ctx, "Processing order",
        slog.String("order.id", "ORD-12345"),
        slog.Float64("order.amount", 99.99),
        slog.String("user.id", "user-123"),
    )
    
    // 错误日志
    err := processPayment()
    if err != nil {
        logger.ErrorContext(ctx, "Payment failed",
            slog.String("order.id", "ORD-12345"),
            slog.String("error", err.Error()),
        )
    }
    
    // 警告日志
    logger.WarnContext(ctx, "Rate limit approaching",
        slog.String("user.id", "user-123"),
        slog.Int("requests.remaining", 10),
        slog.Int("requests.limit", 100),
    )
}

func processPayment() error {
    // 支付处理逻辑
    return nil
}
```

### 7.2 Python完整示例

```python
import logging
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry._logs import set_logger_provider
from opentelemetry.sdk._logs import LoggerProvider, LoggingHandler
from opentelemetry.sdk._logs.export import BatchLogRecordProcessor

# 配置OpenTelemetry Logs
logger_provider = LoggerProvider()
set_logger_provider(logger_provider)

# 配置日志处理器
handler = LoggingHandler(logger_provider=logger_provider)
logging.basicConfig(level=logging.INFO, handlers=[handler])

logger = logging.getLogger(__name__)

def process_order(order_id, user_id, amount):
    # 创建Trace
    tracer = trace.get_tracer(__name__)
    with tracer.start_as_current_span("process-order") as span:
        # INFO日志
        logger.info("Processing order", extra={
            "order.id": order_id,
            "user.id": user_id,
            "order.amount": amount
        })
        
        try:
            # 处理订单
            process_payment(order_id, amount)
            
            logger.info("Order processed successfully", extra={
                "order.id": order_id,
                "status": "completed"
            })
            
        except PaymentError as e:
            # 错误日志
            logger.error("Payment failed", extra={
                "order.id": order_id,
                "error.type": type(e).__name__,
                "error.message": str(e)
            }, exc_info=True)
            
        # 警告日志
        if check_inventory_low():
            logger.warning("Inventory running low", extra={
                "product.id": "PROD-123",
                "quantity.remaining": 5,
                "quantity.threshold": 10
            })

def process_payment(order_id, amount):
    # 支付逻辑
    pass

class PaymentError(Exception):
    pass

def check_inventory_low():
    return False
```

### 7.3 Java完整示例

```java
import io.opentelemetry.api.OpenTelemetry;
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.api.trace.Tracer;
import io.opentelemetry.context.Scope;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.slf4j.MDC;

public class OrderService {
    private static final Logger logger = LoggerFactory.getLogger(OrderService.class);
    private final Tracer tracer;
    
    public OrderService(OpenTelemetry openTelemetry) {
        this.tracer = openTelemetry.getTracer("order-service");
    }
    
    public void processOrder(String orderId, String userId, double amount) {
        Span span = tracer.spanBuilder("process-order").startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // 设置MDC（Mapped Diagnostic Context）
            MDC.put("order.id", orderId);
            MDC.put("user.id", userId);
            
            // INFO日志
            logger.info("Processing order: amount={}", amount);
            
            try {
                processPayment(orderId, amount);
                logger.info("Order processed successfully");
                
            } catch (PaymentException e) {
                // 错误日志
                logger.error("Payment failed", e);
                MDC.put("error.type", e.getClass().getName());
            }
            
            // 警告日志
            if (isRateLimitApproaching(userId)) {
                logger.warn("Rate limit approaching for user: remaining={}",
                    getRemainingRequests(userId));
            }
            
        } finally {
            MDC.clear();
            span.end();
        }
    }
    
    private void processPayment(String orderId, double amount) throws PaymentException {
        // 支付处理逻辑
    }
    
    private boolean isRateLimitApproaching(String userId) {
        return false;
    }
    
    private int getRemainingRequests(String userId) {
        return 10;
    }
    
    static class PaymentException extends Exception {
        public PaymentException(String message) {
            super(message);
        }
    }
}
```

---

## 8. 参考资源

### 官方文档

- **OpenTelemetry Logs Data Model**: <https://opentelemetry.io/docs/specs/otel/logs/data-model/>
- **Logs Bridge API**: <https://opentelemetry.io/docs/specs/otel/logs/bridge-api/>
- **Log Semantic Conventions**: <https://opentelemetry.io/docs/specs/semconv/general/logs/>

### SDK文档

- **Go slog**: <https://pkg.go.dev/log/slog>
- **Python Logging**: <https://docs.python.org/3/library/logging.html>
- **SLF4J (Java)**: <http://www.slf4j.org/>

---

**文档维护**: OTLP深度梳理项目组  
**最后更新**: 2025年10月8日  
**文档版本**: v1.0  
**质量等级**: ⭐⭐⭐⭐⭐

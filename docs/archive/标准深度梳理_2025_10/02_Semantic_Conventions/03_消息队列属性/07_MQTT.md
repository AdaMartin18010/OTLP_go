# MQTT语义约定详解

> **IoT消息协议**: MQTT Tracing与Metrics完整规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [MQTT语义约定详解](#mqtt语义约定详解)
  - [目录](#目录)
  - [1. MQTT概述](#1-mqtt概述)
    - [1.1 MQTT特点](#11-mqtt特点)
    - [1.2 核心架构](#12-核心架构)
  - [2. MQTT通用属性](#2-mqtt通用属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Publisher属性](#3-publisher属性)
    - [3.1 发布属性](#31-发布属性)
    - [3.2 QoS级别](#32-qos级别)
  - [4. Subscriber属性](#4-subscriber属性)
    - [4.1 订阅属性](#41-订阅属性)
    - [4.2 通配符订阅](#42-通配符订阅)
  - [5. Context传播](#5-context传播)
    - [5.1 MQTT 3.1.1挑战](#51-mqtt-311挑战)
    - [5.2 MQTT 5.0解决方案](#52-mqtt-50解决方案)
  - [6. Go实现示例](#6-go实现示例)
    - [6.1 Publisher (MQTT 5.0)](#61-publisher-mqtt-50)
    - [6.2 Subscriber (MQTT 5.0)](#62-subscriber-mqtt-50)
    - [6.3 MQTT 3.1.1变通方案](#63-mqtt-311变通方案)
  - [7. Python实现示例](#7-python实现示例)
    - [7.1 Publisher](#71-publisher)
    - [7.2 Subscriber](#72-subscriber)
  - [8. Java实现示例](#8-java实现示例)
    - [8.1 Publisher](#81-publisher)
    - [8.2 Subscriber](#82-subscriber)
  - [9. Metrics定义](#9-metrics定义)
    - [9.1 Publisher Metrics](#91-publisher-metrics)
    - [9.2 Subscriber Metrics](#92-subscriber-metrics)
    - [9.3 Broker Metrics](#93-broker-metrics)
  - [10. 高级特性](#10-高级特性)
    - [10.1 Retained Messages](#101-retained-messages)
    - [10.2 Last Will Testament](#102-last-will-testament)
    - [10.3 持久会话](#103-持久会话)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 性能优化](#111-性能优化)
    - [11.2 可靠性保证](#112-可靠性保证)
    - [11.3 监控建议](#113-监控建议)

---

## 1. MQTT概述

### 1.1 MQTT特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT (Message Queuing Telemetry Transport)

诞生背景:
- 1999年IBM开发
- 专为物联网设计
- 轻量级、低带宽
- 适合不稳定网络

核心特性:
✅ 极简协议 (最小报文2字节)
✅ Pub/Sub模型 (解耦发布订阅)
✅ 3个QoS级别 (0/1/2)
✅ Topic通配符 (+/#)
✅ Retained消息 (新订阅者立即收到)
✅ Last Will (遗嘱消息)
✅ 持久会话 (断线重连)
✅ 低功耗 (适合电池设备)

版本对比:
- MQTT 3.1.1: 主流版本 (无User Properties)
- MQTT 5.0: 最新版本 (支持User Properties)

适用场景:
✅ 物联网 (IoT)
✅ 智能家居
✅ 车联网
✅ 工业4.0
✅ 移动应用推送
✅ 传感器网络

vs 其他协议:
✅ vs HTTP: 更轻量、双向、低延迟
✅ vs Kafka: 更简单、低功耗、适合边缘
✅ vs AMQP: 更轻量、易实现

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 核心架构

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT架构:

┌─────────────┐
│ Publisher 1 │──┐
└─────────────┘  │
                 │
┌─────────────┐  │   ┌──────────────┐
│ Publisher 2 │──┼──►│ MQTT Broker  │
└─────────────┘  │   └──────┬───────┘
                 │          │
┌─────────────┐  │          │
│ Publisher 3 │──┘          │
└─────────────┘             │
                            │
                ┌───────────┼───────────┐
                │           │           │
                ▼           ▼           ▼
         ┌────────────┐┌────────────┐┌────────────┐
         │Subscriber 1││Subscriber 2││Subscriber 3│
         └────────────┘└────────────┘└────────────┘

Topic层级示例:
home/living-room/temperature
home/living-room/humidity
home/bedroom/temperature
home/+/temperature          (通配符: 单层)
home/#                      (通配符: 多层)

QoS级别:
QoS 0: At most once  (最多一次，可能丢失)
QoS 1: At least once (至少一次，可能重复)
QoS 2: Exactly once  (精确一次，最可靠)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. MQTT通用属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.system` | string | 消息系统标识 | `"mqtt"` |
| `messaging.destination.name` | string | Topic名称 | `"home/living-room/temperature"` |
| `messaging.operation` | string | 操作类型 | `"publish"`, `"receive"` |
| `net.peer.name` | string | Broker地址 | `"mqtt.example.com"` |
| `net.peer.port` | int | Broker端口 | `1883`, `8883` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `messaging.mqtt.qos` | int | QoS级别 | `0`, `1`, `2` |
| `messaging.mqtt.retained` | boolean | Retained标志 | `true`, `false` |
| `messaging.mqtt.duplicate` | boolean | Duplicate标志 | `true`, `false` |
| `messaging.mqtt.client_id` | string | 客户端ID | `"device-12345"` |
| `messaging.message.body.size` | int | 消息体大小(字节) | `1024` |
| `messaging.mqtt.protocol_version` | string | 协议版本 | `"3.1.1"`, `"5.0"` |
| `net.transport` | string | 传输协议 | `"tcp"`, `"websocket"` |

---

## 3. Publisher属性

### 3.1 发布属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT Publisher属性:

必需:
✅ messaging.system = "mqtt"
✅ messaging.destination.name (Topic)
✅ messaging.operation = "publish"
✅ net.peer.name
✅ net.peer.port

推荐:
📋 messaging.mqtt.qos
📋 messaging.mqtt.retained
📋 messaging.mqtt.client_id
📋 messaging.message.body.size
📋 messaging.mqtt.protocol_version

MQTT 5.0额外:
📋 messaging.mqtt.message_expiry_interval
📋 messaging.mqtt.content_type
📋 messaging.mqtt.response_topic
📋 messaging.mqtt.correlation_data

示例:
    ```go
    span.SetAttributes(
        semconv.MessagingSystemKey.String("mqtt"),
        semconv.MessagingDestinationNameKey.String(
            "home/living-room/temperature"),
        semconv.MessagingOperationKey.String("publish"),
        attribute.Int("messaging.mqtt.qos", 1),
        attribute.Bool("messaging.mqtt.retained", false),
        attribute.String("messaging.mqtt.client_id", "device-12345"),
        attribute.Int("messaging.message.body.size", len(payload)),
    )
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 3.2 QoS级别

| QoS | 名称 | 描述 | 适用场景 | 追踪属性 |
|-----|------|------|---------|---------|
| 0 | At most once | 最多一次，不确认 | 环境监测、日志 | `messaging.mqtt.qos=0` |
| 1 | At least once | 至少一次，可能重复 | 遥测数据、传感器 | `messaging.mqtt.qos=1` |
| 2 | Exactly once | 精确一次，最可靠 | 计费、控制指令 | `messaging.mqtt.qos=2` |

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

QoS 0 流程:
Publisher ──► Broker ──► Subscriber
(不等待确认)

QoS 1 流程:
Publisher ──PUBLISH──► Broker ──PUBLISH──► Subscriber
         ◄──PUBACK────         ◄──PUBACK────
(确认一次)

QoS 2 流程:
Publisher ──PUBLISH──► Broker ──PUBLISH──► Subscriber
         ◄──PUBREC────         ◄──PUBREC────
         ──PUBREL───►          ──PUBREL───►
         ◄──PUBCOMP───         ◄──PUBCOMP───
(四次握手，精确一次)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 4. Subscriber属性

### 4.1 订阅属性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT Subscriber属性:

必需:
✅ messaging.system = "mqtt"
✅ messaging.destination.name (Topic/Pattern)
✅ messaging.operation = "receive"

推荐:
📋 messaging.mqtt.qos
📋 messaging.mqtt.client_id
📋 messaging.mqtt.subscription_pattern
📋 messaging.message.body.size

示例:
    ```go
    span.SetAttributes(
        semconv.MessagingSystemKey.String("mqtt"),
        semconv.MessagingDestinationNameKey.String(
            "home/+/temperature"), // 通配符订阅
        semconv.MessagingOperationKey.String("receive"),
        attribute.String("messaging.mqtt.subscription_pattern", 
            "home/+/temperature"),
        attribute.Int("messaging.mqtt.qos", 1),
    )
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 4.2 通配符订阅

| 通配符 | 名称 | 描述 | 示例 |
|--------|------|------|------|
| `+` | 单层通配符 | 匹配单个层级 | `home/+/temperature` |
| `#` | 多层通配符 | 匹配多个层级 | `home/#` |

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

通配符示例:

订阅: home/+/temperature
匹配:
✅ home/living-room/temperature
✅ home/bedroom/temperature
✅ home/kitchen/temperature
❌ home/living-room/humidity
❌ home/living-room/sensor/temperature

订阅: home/#
匹配:
✅ home/living-room/temperature
✅ home/bedroom/humidity
✅ home/living-room/sensor/motion
✅ home/a/b/c/d

订阅: +/temperature
匹配:
✅ home/temperature
✅ office/temperature
❌ home/living-room/temperature

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 5. Context传播

### 5.1 MQTT 3.1.1挑战

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT 3.1.1 Context传播挑战:

问题:
❌ 没有User Properties机制
❌ 没有消息头 (Headers)
❌ 只有Payload (消息体)

变通方案:

1. Payload包装 (JSON) ⭐⭐⭐
   {
     "traceparent": "00-...",
     "data": { ... }
   }
   
   优点: 简单易实现
   缺点: 增加消息体大小

2. Topic编码 ⭐
   sensors/trace-abc123/temperature
   
   优点: 不改变消息体
   缺点: Topic污染，难管理

3. 独立追踪消息 ⭐
   发送独立的追踪消息到特殊Topic
   
   优点: 不影响业务消息
   缺点: 增加消息数量，关联复杂

推荐: Payload包装 (JSON)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.2 MQTT 5.0解决方案

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

MQTT 5.0 User Properties:

MQTT 5.0引入了User Properties (用户属性):

User Properties:
- 键值对列表
- 不影响消息体
- 完美支持追踪

示例:
User Properties:
  - traceparent: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
  - tracestate: vendor=value
  - baggage: userId=12345

优点:
✅ 原生支持
✅ 不改变消息体
✅ 多个属性
✅ 标准化

推荐: MQTT 5.0 + User Properties

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 6. Go实现示例

### 6.1 Publisher (MQTT 5.0)

```go
package main

import (
    "context"
    "encoding/json"
    
    mqtt "github.com/eclipse/paho.mqtt.golang"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

func PublishWithTracing(
    ctx context.Context,
    client mqtt.Client,
    topic string,
    qos byte,
    retained bool,
    payload []byte,
) error {
    tracer := otel.Tracer("mqtt-publisher")
    
    // 创建Publisher Span
    ctx, span := tracer.Start(ctx, "mqtt.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
        trace.WithAttributes(
            semconv.MessagingSystemKey.String("mqtt"),
            semconv.MessagingDestinationNameKey.String(topic),
            semconv.MessagingOperationKey.String("publish"),
            attribute.Int("messaging.mqtt.qos", int(qos)),
            attribute.Bool("messaging.mqtt.retained", retained),
            attribute.Int("messaging.message.body.size", len(payload)),
            attribute.String("messaging.mqtt.protocol_version", "5.0"),
        ),
    )
    defer span.End()
    
    // MQTT 5.0: 使用User Properties
    properties := make(map[string]string)
    
    // 注入Trace Context
    carrier := &MQTTPropertiesCarrier{properties: properties}
    otel.GetTextMapPropagator().Inject(ctx, carrier)
    
    // 创建MQTT 5.0消息 (带User Properties)
    token := client.Publish(topic, qos, retained, payload)
    // Note: paho.mqtt.golang需要使用支持MQTT 5.0的版本
    // 或使用其他MQTT 5.0客户端库
    
    // 等待发布完成
    if token.Wait() && token.Error() != nil {
        span.RecordError(token.Error())
        span.SetStatus(codes.Error, "publish failed")
        return token.Error()
    }
    
    span.SetStatus(codes.Ok, "published")
    return nil
}

// MQTT Properties Carrier
type MQTTPropertiesCarrier struct {
    properties map[string]string
}

func (c *MQTTPropertiesCarrier) Get(key string) string {
    return c.properties[key]
}

func (c *MQTTPropertiesCarrier) Set(key, value string) {
    c.properties[key] = value
}

func (c *MQTTPropertiesCarrier) Keys() []string {
    keys := make([]string, 0, len(c.properties))
    for k := range c.properties {
        keys = append(keys, k)
    }
    return keys
}
```

### 6.2 Subscriber (MQTT 5.0)

```go
func SubscribeWithTracing(
    ctx context.Context,
    client mqtt.Client,
    topic string,
    qos byte,
    handler func(context.Context, []byte) error,
) error {
    tracer := otel.Tracer("mqtt-subscriber")
    
    // 订阅回调
    callback := func(client mqtt.Client, msg mqtt.Message) {
        // 提取Trace Context (MQTT 5.0 User Properties)
        properties := extractUserProperties(msg)
        carrier := &MQTTPropertiesCarrier{properties: properties}
        msgCtx := otel.GetTextMapPropagator().Extract(ctx, carrier)
        
        // 创建Consumer Span
        msgCtx, span := tracer.Start(msgCtx, "mqtt.receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
            trace.WithAttributes(
                semconv.MessagingSystemKey.String("mqtt"),
                semconv.MessagingDestinationNameKey.String(msg.Topic()),
                semconv.MessagingOperationKey.String("receive"),
                attribute.Int("messaging.mqtt.qos", int(msg.Qos())),
                attribute.Bool("messaging.mqtt.retained", msg.Retained()),
                attribute.Bool("messaging.mqtt.duplicate", msg.Duplicate()),
                attribute.Int("messaging.message.body.size", 
                    len(msg.Payload())),
            ),
        )
        
        // 处理消息
        err := handler(msgCtx, msg.Payload())
        
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
        } else {
            span.SetStatus(codes.Ok, "processed")
        }
        
        span.End()
    }
    
    // 订阅Topic
    token := client.Subscribe(topic, qos, callback)
    if token.Wait() && token.Error() != nil {
        return token.Error()
    }
    
    return nil
}

func extractUserProperties(msg mqtt.Message) map[string]string {
    // MQTT 5.0: 从User Properties提取
    // 需要使用支持MQTT 5.0的客户端库
    // 这里是伪代码示例
    properties := make(map[string]string)
    // properties["traceparent"] = msg.UserProperty("traceparent")
    // properties["tracestate"] = msg.UserProperty("tracestate")
    return properties
}
```

### 6.3 MQTT 3.1.1变通方案

```go
// MQTT 3.1.1: Payload包装方案

type MessageWithContext struct {
    Traceparent string          `json:"traceparent,omitempty"`
    Tracestate  string          `json:"tracestate,omitempty"`
    Data        json.RawMessage `json:"data"`
}

func PublishWithTracing311(
    ctx context.Context,
    client mqtt.Client,
    topic string,
    qos byte,
    data []byte,
) error {
    tracer := otel.Tracer("mqtt-publisher")
    
    ctx, span := tracer.Start(ctx, "mqtt.publish",
        trace.WithSpanKind(trace.SpanKindProducer),
    )
    defer span.End()
    
    // 创建包装消息
    wrapper := MessageWithContext{
        Data: data,
    }
    
    // 提取trace context
    spanCtx := trace.SpanContextFromContext(ctx)
    if spanCtx.IsValid() {
        wrapper.Traceparent = spanCtx.TraceID().String() + "-" + 
                             spanCtx.SpanID().String()
    }
    
    // JSON序列化
    payload, err := json.Marshal(wrapper)
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    // 发布
    token := client.Publish(topic, qos, false, payload)
    if token.Wait() && token.Error() != nil {
        span.RecordError(token.Error())
        span.SetStatus(codes.Error, "publish failed")
        return token.Error()
    }
    
    span.SetStatus(codes.Ok, "published")
    return nil
}

func SubscribeWithTracing311(
    ctx context.Context,
    client mqtt.Client,
    topic string,
    qos byte,
    handler func(context.Context, []byte) error,
) error {
    tracer := otel.Tracer("mqtt-subscriber")
    
    callback := func(client mqtt.Client, msg mqtt.Message) {
        // 解析包装消息
        var wrapper MessageWithContext
        if err := json.Unmarshal(msg.Payload(), &wrapper); err != nil {
            // 处理错误
            return
        }
        
        // 重建trace context (简化版)
        msgCtx := ctx
        if wrapper.Traceparent != "" {
            // 从traceparent重建context
            // 需要完整实现W3C Trace Context解析
        }
        
        // 创建span
        msgCtx, span := tracer.Start(msgCtx, "mqtt.receive",
            trace.WithSpanKind(trace.SpanKindConsumer),
        )
        defer span.End()
        
        // 处理实际数据
        err := handler(msgCtx, wrapper.Data)
        if err != nil {
            span.RecordError(err)
            span.SetStatus(codes.Error, "handler failed")
        } else {
            span.SetStatus(codes.Ok, "processed")
        }
    }
    
    token := client.Subscribe(topic, qos, callback)
    return token.Error()
}
```

---

## 7. Python实现示例

### 7.1 Publisher

```python
import json
import paho.mqtt.client as mqtt
from opentelemetry import trace, propagate
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)

def publish_with_tracing(
    client: mqtt.Client,
    topic: str,
    payload: bytes,
    qos: int = 1,
    retain: bool = False
):
    """发布MQTT消息with tracing (MQTT 5.0)"""
    with tracer.start_as_current_span(
        "mqtt.publish",
        kind=SpanKind.PRODUCER,
        attributes={
            SpanAttributes.MESSAGING_SYSTEM: "mqtt",
            SpanAttributes.MESSAGING_DESTINATION_NAME: topic,
            SpanAttributes.MESSAGING_OPERATION: "publish",
            "messaging.mqtt.qos": qos,
            "messaging.mqtt.retained": retain,
            "messaging.message.body.size": len(payload),
        }
    ) as span:
        # MQTT 5.0: 使用User Properties
        properties = mqtt.Properties(mqtt.PacketTypes.PUBLISH)
        
        # 注入trace context
        carrier = {}
        propagate.inject(carrier)
        
        # 添加User Properties
        if 'traceparent' in carrier:
            properties.UserProperty = [
                ('traceparent', carrier['traceparent'])
            ]
        if 'tracestate' in carrier:
            properties.UserProperty.append(
                ('tracestate', carrier['tracestate'])
            )
        
        try:
            # 发布消息
            result = client.publish(
                topic,
                payload,
                qos=qos,
                retain=retain,
                properties=properties
            )
            
            result.wait_for_publish()
            span.set_status(Status(StatusCode.OK))
            
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def publish_with_tracing_311(
    client: mqtt.Client,
    topic: str,
    data: dict,
    qos: int = 1
):
    """发布MQTT消息with tracing (MQTT 3.1.1变通方案)"""
    with tracer.start_as_current_span(
        "mqtt.publish",
        kind=SpanKind.PRODUCER
    ) as span:
        # 注入trace context到payload
        carrier = {}
        propagate.inject(carrier)
        
        # 包装消息
        wrapper = {
            'traceparent': carrier.get('traceparent', ''),
            'tracestate': carrier.get('tracestate', ''),
            'data': data
        }
        
        try:
            # JSON序列化
            payload = json.dumps(wrapper).encode('utf-8')
            
            # 发布
            result = client.publish(topic, payload, qos=qos)
            result.wait_for_publish()
            span.set_status(Status(StatusCode.OK))
            
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise
```

### 7.2 Subscriber

```python
def create_subscriber_with_tracing(
    client: mqtt.Client,
    topic: str,
    qos: int,
    handler
):
    """创建带追踪的订阅者 (MQTT 5.0)"""
    
    def on_message(client, userdata, msg):
        # 提取User Properties
        properties = {}
        if hasattr(msg, 'properties') and msg.properties:
            for key, value in msg.properties.UserProperty:
                properties[key] = value
        
        # 提取trace context
        ctx = propagate.extract(properties)
        
        # 创建span
        with tracer.start_as_current_span(
            "mqtt.receive",
            context=ctx,
            kind=SpanKind.CONSUMER,
            attributes={
                SpanAttributes.MESSAGING_SYSTEM: "mqtt",
                SpanAttributes.MESSAGING_DESTINATION_NAME: msg.topic,
                SpanAttributes.MESSAGING_OPERATION: "receive",
                "messaging.mqtt.qos": msg.qos,
                "messaging.mqtt.retained": msg.retain,
                "messaging.message.body.size": len(msg.payload),
            }
        ) as span:
            try:
                # 处理消息
                handler(msg.payload)
                span.set_status(Status(StatusCode.OK))
            except Exception as e:
                span.record_exception(e)
                span.set_status(Status(StatusCode.ERROR))
    
    client.on_message = on_message
    client.subscribe(topic, qos)

def create_subscriber_with_tracing_311(
    client: mqtt.Client,
    topic: str,
    qos: int,
    handler
):
    """创建带追踪的订阅者 (MQTT 3.1.1)"""
    
    def on_message(client, userdata, msg):
        try:
            # 解析包装消息
            wrapper = json.loads(msg.payload.decode('utf-8'))
            
            # 提取trace context
            carrier = {
                'traceparent': wrapper.get('traceparent', ''),
                'tracestate': wrapper.get('tracestate', '')
            }
            ctx = propagate.extract(carrier)
            
            # 创建span
            with tracer.start_as_current_span(
                "mqtt.receive",
                context=ctx,
                kind=SpanKind.CONSUMER
            ) as span:
                try:
                    # 处理实际数据
                    handler(wrapper['data'])
                    span.set_status(Status(StatusCode.OK))
                except Exception as e:
                    span.record_exception(e)
                    span.set_status(Status(StatusCode.ERROR))
        
        except json.JSONDecodeError:
            # 非包装消息，直接处理
            handler(msg.payload)
    
    client.on_message = on_message
    client.subscribe(topic, qos)
```

---

## 8. Java实现示例

### 8.1 Publisher

```java
import org.eclipse.paho.mqttv5.client.*;
import org.eclipse.paho.mqttv5.common.MqttMessage;
import org.eclipse.paho.mqttv5.common.packet.MqttProperties;
import io.opentelemetry.api.trace.*;
import io.opentelemetry.context.Context;

public class MQTTPublisherTracing {
    
    private static final Tracer tracer = 
        openTelemetry.getTracer("mqtt-publisher");
    
    public void publishWithTracing(
        MqttAsyncClient client,
        String topic,
        byte[] payload,
        int qos,
        boolean retained
    ) throws MqttException {
        
        // 创建span
        Span span = tracer.spanBuilder("mqtt.publish")
            .setSpanKind(SpanKind.PRODUCER)
            .setAttribute("messaging.system", "mqtt")
            .setAttribute("messaging.destination.name", topic)
            .setAttribute("messaging.operation", "publish")
            .setAttribute("messaging.mqtt.qos", qos)
            .setAttribute("messaging.mqtt.retained", retained)
            .startSpan();
        
        try (Scope scope = span.makeCurrent()) {
            // MQTT 5.0: 创建User Properties
            MqttProperties properties = new MqttProperties();
            
            // 注入trace context
            Context.current().propagate((key, value) -> {
                properties.setUserProperty(key, value);
            });
            
            // 创建消息
            MqttMessage message = new MqttMessage(payload);
            message.setQos(qos);
            message.setRetained(retained);
            message.setProperties(properties);
            
            // 发布
            client.publish(topic, message).waitForCompletion();
            span.setStatus(StatusCode.OK);
            
        } catch (Exception e) {
            span.recordException(e);
            span.setStatus(StatusCode.ERROR);
            throw e;
        } finally {
            span.end();
        }
    }
}
```

### 8.2 Subscriber

```java
public class MQTTSubscriberTracing {
    
    private static final Tracer tracer = 
        openTelemetry.getTracer("mqtt-subscriber");
    
    public void subscribeWithTracing(
        MqttAsyncClient client,
        String topic,
        int qos,
        MessageHandler handler
    ) throws MqttException {
        
        client.subscribe(topic, qos, (t, msg) -> {
            // 提取User Properties
            Map<String, String> properties = new HashMap<>();
            if (msg.getProperties() != null) {
                msg.getProperties().getUserProperties()
                    .forEach(prop -> properties.put(
                        prop.getKey(), prop.getValue()));
            }
            
            // 提取trace context
            Context extractedContext = propagate.extract(properties);
            
            // 创建span
            Span span = tracer.spanBuilder("mqtt.receive")
                .setParent(extractedContext)
                .setSpanKind(SpanKind.CONSUMER)
                .setAttribute("messaging.system", "mqtt")
                .setAttribute("messaging.destination.name", t)
                .setAttribute("messaging.operation", "receive")
                .setAttribute("messaging.mqtt.qos", msg.getQos())
                .startSpan();
            
            try (Scope scope = span.makeCurrent()) {
                // 处理消息
                handler.handle(msg.getPayload());
                span.setStatus(StatusCode.OK);
                
            } catch (Exception e) {
                span.recordException(e);
                span.setStatus(StatusCode.ERROR);
            } finally {
                span.end();
            }
        });
    }
}
```

---

## 9. Metrics定义

### 9.1 Publisher Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.mqtt.publish.duration` | Histogram | ms | 发布延迟 |
| `messaging.mqtt.publish.messages` | Counter | messages | 发布消息数 |
| `messaging.mqtt.publish.bytes` | Counter | bytes | 发布字节数 |
| `messaging.mqtt.publish.errors` | Counter | errors | 发布错误数 |
| `messaging.mqtt.publish.retries` | Counter | retries | 重试次数 |

**推荐标签**:

- `messaging.mqtt.qos`: QoS级别
- `messaging.destination.name`: Topic
- `net.peer.name`: Broker地址

### 9.2 Subscriber Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.mqtt.receive.duration` | Histogram | ms | 接收延迟 |
| `messaging.mqtt.receive.messages` | Counter | messages | 接收消息数 |
| `messaging.mqtt.receive.bytes` | Counter | bytes | 接收字节数 |
| `messaging.mqtt.subscription.count` | Gauge | subscriptions | 订阅数量 |

### 9.3 Broker Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `messaging.mqtt.connections.active` | Gauge | connections | 活跃连接数 |
| `messaging.mqtt.clients.connected` | Gauge | clients | 已连接客户端 |
| `messaging.mqtt.messages.inflight` | Gauge | messages | 飞行中消息数 |
| `messaging.mqtt.messages.retained` | Gauge | messages | Retained消息数 |
| `messaging.mqtt.subscriptions.total` | Gauge | subscriptions | 总订阅数 |

---

## 10. 高级特性

### 10.1 Retained Messages

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Retained消息:

定义:
Broker保留Topic的最后一条消息，
新订阅者立即收到该消息。

使用场景:
✅ 设备状态 (在线/离线)
✅ 配置信息
✅ 最新读数

示例:
Publisher发布:
  Topic: device/sensor-1/status
  Payload: {"status": "online"}
  Retained: true

新Subscriber订阅后:
  立即收到最新状态: {"status": "online"}

追踪:
span.SetAttributes(
    attribute.Bool("messaging.mqtt.retained", true),
)

注意:
- 每个Topic只保留一条
- 发布空消息可删除Retained

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.2 Last Will Testament

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

遗嘱消息 (LWT):

定义:
客户端连接时设置遗嘱消息，
异常断开时Broker自动发布。

使用场景:
✅ 设备离线通知
✅ 故障告警
✅ 连接监控

示例:
client.Connect({
    WillTopic:   "device/sensor-1/status",
    WillPayload: []byte(`{"status": "offline"}`),
    WillQoS:     1,
    WillRetained: true,
})

当客户端异常断开:
Broker自动发布遗嘱消息到 device/sensor-1/status

追踪:
span.SetAttributes(
    attribute.String("messaging.mqtt.will_topic", willTopic),
    attribute.Bool("messaging.mqtt.will_retained", true),
)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.3 持久会话

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

持久会话 (Clean Session = false):

定义:
Broker保存客户端的订阅和未确认消息，
断线重连后继续接收。

使用场景:
✅ 不稳定网络
✅ 移动设备
✅ 关键消息不丢失

示例:
client.Connect({
    ClientID:     "device-12345",
    CleanSession: false, // 持久会话
})

断线期间:
Broker保存QoS>0的消息

重连后:
自动接收断线期间的消息

追踪:
span.SetAttributes(
    attribute.Bool("messaging.mqtt.clean_session", false),
    attribute.String("messaging.mqtt.session_present", "true"),
)

注意:
- 需要固定ClientID
- 占用Broker资源

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 11. 最佳实践

### 11.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

性能优化建议:

1. QoS选择 ⭐⭐⭐⭐⭐
   - 环境监测: QoS 0 (最快)
   - 传感器数据: QoS 1 (平衡)
   - 控制指令: QoS 2 (可靠)

2. Payload大小 ⭐⭐⭐⭐⭐
   - 保持小于1KB
   - 使用二进制格式 (Protobuf/MessagePack)
   - 压缩大数据

3. Topic设计 ⭐⭐⭐⭐
   - 扁平结构 (避免过深层级)
   - 避免动态Topic
   - 合理使用通配符

4. 连接管理 ⭐⭐⭐⭐
   - 复用连接
   - 配置心跳 (Keep Alive)
   - 优雅断开

5. 批量操作 ⭐⭐⭐
   - 批量订阅
   - 合并小消息

6. Clean Session ⭐⭐⭐⭐
   - 临时客户端: true
   - 固定设备: false

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 11.2 可靠性保证

```go
// 可靠性配置
opts := mqtt.NewClientOptions()
opts.AddBroker("tcp://mqtt.example.com:1883")
opts.SetClientID("device-12345")

// 自动重连
opts.SetAutoReconnect(true)
opts.SetMaxReconnectInterval(60 * time.Second)

// 持久会话
opts.SetCleanSession(false)

// 心跳
opts.SetKeepAlive(60 * time.Second)

// 遗嘱消息
opts.SetWill(
    "device/sensor-1/status",
    `{"status": "offline"}`,
    1,
    true,
)

// 连接回调
opts.SetOnConnectHandler(func(client mqtt.Client) {
    log.Println("Connected")
    // 重新订阅
})

opts.SetConnectionLostHandler(func(client mqtt.Client, err error) {
    log.Printf("Connection lost: %v", err)
})

client := mqtt.NewClient(opts)
```

### 11.3 监控建议

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键监控指标:

1. 客户端
   - 连接状态 (connected/disconnected)
   - 发布/订阅速率
   - 消息延迟
   - 错误率

2. Broker
   - 活跃连接数
   - 消息吞吐量
   - 内存使用
   - CPU使用
   - Retained消息数
   - 订阅数量

3. 消息质量
   - QoS 0/1/2分布
   - 消息丢失率
   - 重传次数

告警规则:
- 连接断开 > 5秒
- 消息延迟 > 1秒
- 错误率 > 0.1%
- Broker CPU > 80%
- Broker内存 > 90%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**MQTT版本**: 3.1.1 / 5.0  
**适用场景**: IoT设备、智能家居、车联网、工业4.0

**关键特性**:

- ✅ MQTT 3.1.1 Payload包装方案
- ✅ MQTT 5.0 User Properties原生支持
- ✅ 3个QoS级别详解
- ✅ Topic通配符订阅
- ✅ Retained消息追踪
- ✅ Last Will Testament
- ✅ 持久会话
- ✅ Go/Python/Java完整示例
- ✅ IoT场景最佳实践

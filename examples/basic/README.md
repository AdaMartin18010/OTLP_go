# 基础追踪示例

## 📋 目录

- [基础追踪示例](#基础追踪示例)
  - [📋 目录](#-目录)
  - [运行示例](#运行示例)
    - [1. 启动 OTLP Collector](#1-启动-otlp-collector)
    - [2. 运行示例](#2-运行示例)
    - [3. 查看输出](#3-查看输出)
  - [代码说明](#代码说明)
    - [初始化 TracerProvider](#初始化-tracerprovider)
    - [创建 Span](#创建-span)
    - [添加属性](#添加属性)
    - [添加事件](#添加事件)
  - [学习要点](#学习要点)
  - [下一步](#下一步)

这是最简单的 OTLP 追踪示例，展示了如何：

- 初始化 OTLP Exporter
- 创建 TracerProvider
- 创建和管理 Span
- 添加属性和事件
- 设置 Span 状态

## 运行示例

### 1. 启动 OTLP Collector

```bash
docker run -d --name otel-collector \
  -p 4317:4317 \
  -p 4318:4318 \
  otel/opentelemetry-collector-contrib:latest
```

### 2. 运行示例

```bash
go run main.go
```

### 3. 查看输出

```text
Starting basic OTLP tracing example...
Created root span
Starting work...
Database query completed
External API call completed
Data processing completed
Work completed
Basic tracing example completed successfully!
```

## 代码说明

### 初始化 TracerProvider

```go
tp, err := initTracerProvider()
otel.SetTracerProvider(tp)
```

### 创建 Span

```go
ctx, span := tracer.Start(ctx, "operation-name")
defer span.End()
```

### 添加属性

```go
span.SetAttributes(
    attribute.String("key", "value"),
    attribute.Int("count", 42),
)
```

### 添加事件

```go
span.AddEvent("event-name",
    trace.WithAttributes(
        attribute.String("detail", "info"),
    ),
)
```

## 学习要点

1. **TracerProvider**: 管理 Tracer 的生命周期
2. **Tracer**: 创建 Span 的工厂
3. **Span**: 表示一个操作或事件
4. **Attributes**: 描述 Span 的键值对
5. **Events**: Span 生命周期中的时间点

## 下一步

- 学习 [context-propagation](../context-propagation/) 示例
- 了解 [custom-sampler](../custom-sampler/) 示例
- 探索 [distributed-tracing](../distributed-tracing/) 示例

# AWS Lambda语义约定详解

> **Serverless计算**: AWS Lambda完整Tracing与Metrics规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [AWS Lambda语义约定详解](#aws-lambda语义约定详解)
  - [目录](#目录)
  - [1. AWS Lambda概述](#1-aws-lambda概述)
    - [1.1 Lambda特点](#11-lambda特点)
    - [1.2 执行模型](#12-执行模型)
  - [2. Lambda Resource属性](#2-lambda-resource属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Lambda Span属性](#3-lambda-span属性)
    - [3.1 调用属性](#31-调用属性)
    - [3.2 触发器属性](#32-触发器属性)
  - [4. 触发器类型详解](#4-触发器类型详解)
    - [4.1 API Gateway](#41-api-gateway)
    - [4.2 SQS](#42-sqs)
    - [4.3 DynamoDB Streams](#43-dynamodb-streams)
    - [4.4 S3事件](#44-s3事件)
    - [4.5 EventBridge](#45-eventbridge)
  - [5. Go实现示例](#5-go实现示例)
    - [5.1 基本Lambda函数](#51-基本lambda函数)
    - [5.2 API Gateway触发](#52-api-gateway触发)
    - [5.3 SQS触发](#53-sqs触发)
  - [6. Python实现示例](#6-python实现示例)
    - [6.1 基本函数](#61-基本函数)
    - [6.2 自动化装饰器](#62-自动化装饰器)
  - [7. Metrics定义](#7-metrics定义)
    - [7.1 Lambda Metrics](#71-lambda-metrics)
    - [7.2 自定义Metrics](#72-自定义metrics)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 性能优化](#81-性能优化)
    - [8.2 成本优化](#82-成本优化)
    - [8.3 监控建议](#83-监控建议)

---

## 1. AWS Lambda概述

### 1.1 Lambda特点

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

AWS Lambda - Serverless计算服务

核心特性:
✅ 无服务器 (零运维)
✅ 按请求付费 (毫秒级计费)
✅ 自动扩展 (并发1000+)
✅ 事件驱动
✅ 多语言支持 (Python/Node.js/Go/Java/C#/.NET/Ruby)
✅ 内置容错
✅ 与AWS服务深度集成

优势:
✅ 无需管理服务器
✅ 自动高可用
✅ 成本优化 (按使用付费)
✅ 快速迭代

适用场景:
✅ API后端 (API Gateway + Lambda)
✅ 数据处理 (S3/Kinesis触发)
✅ 流式处理 (DynamoDB Streams)
✅ 定时任务 (EventBridge)
✅ Webhook处理
✅ 异步任务队列 (SQS)

限制:
⚠️  执行时间: 最长15分钟
⚠️  内存: 128MB - 10GB
⚠️  部署包: 50MB (压缩), 250MB (解压)
⚠️  临时存储: /tmp 最大10GB

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 执行模型

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Lambda执行生命周期:

┌────────────────────────────────────────────┐
│  1. 冷启动 (Cold Start) - 首次调用         │
│     - 下载代码                             │
│     - 初始化运行时                         │
│     - 执行初始化代码                       │
│     - 耗时: 100ms - 几秒                   │
└────────────────────────────────────────────┘
              │
              ▼
┌────────────────────────────────────────────┐
│  2. 执行Handler                            │
│     - 处理事件                             │
│     - 执行业务逻辑                         │
│     - 返回响应                             │
└────────────────────────────────────────────┘
              │
              ▼
┌────────────────────────────────────────────┐
│  3. 保持热启动 (Warm) - 5-15分钟          │
│     - 容器保留                             │
│     - 后续调用无需冷启动                   │
│     - 耗时: < 10ms                         │
└────────────────────────────────────────────┘
              │
              ▼
┌────────────────────────────────────────────┐
│  4. 冻结/销毁                              │
│     - 无新请求时冻结                       │
│     - 最终销毁容器                         │
└────────────────────────────────────────────┘

并发模型:
- 每个请求一个容器实例
- 自动并发扩展
- Reserved Concurrency (预留并发)
- Provisioned Concurrency (预配置并发，避免冷启动)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Lambda Resource属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"aws"` |
| `cloud.platform` | string | 平台类型 | `"aws_lambda"` |
| `cloud.region` | string | AWS区域 | `"us-east-1"` |
| `faas.name` | string | 函数名称 | `"my-function"` |
| `faas.version` | string | 函数版本 | `"$LATEST"`, `"1"` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.instance` | string | 实例ID | Lambda自动生成 |
| `faas.max_memory` | int | 配置内存(MB) | `1024` |
| `aws.lambda.invoked_arn` | string | 调用ARN | `"arn:aws:lambda:..."` |
| `aws.lambda.log_group_name` | string | CloudWatch日志组 | `"/aws/lambda/my-function"` |
| `aws.lambda.log_stream_name` | string | 日志流 | `"2025/10/08/[$LATEST]abc123"` |
| `cloud.account.id` | string | AWS账号ID | `"123456789012"` |

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Lambda Resource属性示例:

    ```yaml
    resource:
    attributes:
        cloud.provider: aws
        cloud.platform: aws_lambda
        cloud.region: us-east-1
        faas.name: my-function
        faas.version: "$LATEST"
        faas.max_memory: 1024
        aws.lambda.invoked_arn: "arn:aws:lambda:us-east-1:123456789012:function:my-function"
        aws.lambda.log_group_name: "/aws/lambda/my-function"
        cloud.account.id: "123456789012"
    ```

    环境变量获取:

    - AWS_REGION
    - AWS_LAMBDA_FUNCTION_NAME
    - AWS_LAMBDA_FUNCTION_VERSION
    - AWS_LAMBDA_FUNCTION_MEMORY_SIZE
    - AWS_LAMBDA_LOG_GROUP_NAME
    - AWS_LAMBDA_LOG_STREAM_NAME
    - _X_AMZN_TRACE_ID (X-Ray Trace ID)

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

---

## 3. Lambda Span属性

### 3.1 调用属性

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Lambda调用Span属性:

    必需:
    ✅ faas.invocation_id (请求ID)
    ✅ faas.trigger (触发器类型)

    推荐:
    📋 faas.execution
    📋 faas.coldstart (是否冷启动)
    📋 aws.lambda.invoked_arn

    示例:
    ```go
    span.SetAttributes(
        attribute.String("faas.invocation_id", ctx.RequestID),
        attribute.String("faas.trigger", "http"),
        attribute.Bool("faas.coldstart", isColdStart),
        attribute.String("aws.lambda.invoked_arn", ctx.InvokedFunctionArn),
    )
    ```

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.invocation_id` | string | 请求ID | Lambda自动生成 |
| `faas.trigger` | string | 触发器类型 | `"http"`, `"pubsub"`, `"datasource"`, `"timer"` |
| `faas.coldstart` | boolean | 冷启动标志 | `true`, `false` |
| `faas.execution` | string | 执行环境 | `"aws_lambda"` |
| `aws.lambda.request_id` | string | 请求ID (同faas.invocation_id) | - |

### 3.2 触发器属性

| 触发器类型 | faas.trigger | 额外属性 |
|-----------|--------------|---------|
| API Gateway | `"http"` | `http.method`, `http.route`, `http.target` |
| ALB | `"http"` | `http.method`, `http.target` |
| SQS | `"pubsub"` | `messaging.system="aws_sqs"`, `messaging.destination.name` |
| SNS | `"pubsub"` | `messaging.system="aws_sns"`, `messaging.destination.name` |
| S3 | `"datasource"` | `aws.s3.bucket`, `aws.s3.key` |
| DynamoDB Streams | `"datasource"` | `aws.dynamodb.table_name`, `aws.dynamodb.stream_arn` |
| Kinesis | `"datasource"` | `aws.kinesis.stream_name` |
| EventBridge | `"timer"` | `aws.eventbridge.rule_name` |
| CloudWatch Logs | `"datasource"` | `aws.cloudwatch.log_group` |

---

## 4. 触发器类型详解

### 4.1 API Gateway

```text
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    API Gateway + Lambda:

    ┌─────────┐    ┌──────────────┐    ┌──────────┐
    │ Client  │───►│ API Gateway  │───►│  Lambda  │
    └─────────┘    └──────────────┘    └──────────┘

    属性:
    ✅ faas.trigger = "http"
    ✅ http.method
    ✅ http.route
    ✅ http.target
    ✅ http.status_code
    ✅ http.user_agent

    示例:
    ```go
    span.SetAttributes(
        attribute.String("faas.trigger", "http"),
        attribute.String("http.method", "POST"),
        attribute.String("http.route", "/users"),
        attribute.String("http.target", "/users?id=123"),
        attribute.Int("http.status_code", 200),
    )
    ```

    Context传播:
    API Gateway会传递X-Ray Trace ID到Lambda

    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 4.2 SQS

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SQS + Lambda:

┌─────────┐    ┌──────────┐    ┌──────────┐
│Producer │───►│   SQS    │───►│  Lambda  │
└─────────┘    └──────────┘    └──────────┘
                                 (批量处理)

属性:
✅ faas.trigger = "pubsub"
✅ messaging.system = "aws_sqs"
✅ messaging.destination.name (队列名称)
✅ messaging.operation = "receive"
✅ aws.lambda.batch_size (批量大小)

Lambda SQS批量处理:
- 默认批量大小: 10
- 最大: 10,000
- Lambda按批次调用

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.3 DynamoDB Streams

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

DynamoDB Streams + Lambda:

┌──────────┐    ┌────────────────┐    ┌──────────┐
│DynamoDB  │───►│DynamoDB Streams│───►│  Lambda  │
└──────────┘    └────────────────┘    └──────────┘
  (变更)          (CDC Stream)        (处理变更)

属性:
✅ faas.trigger = "datasource"
✅ aws.dynamodb.table_name
✅ aws.dynamodb.stream_arn
✅ aws.dynamodb.event_name ("INSERT", "MODIFY", "REMOVE")

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.4 S3事件

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

S3 + Lambda:

┌─────────┐    ┌──────┐    ┌──────────┐
│ Upload  │───►│  S3  │───►│  Lambda  │
└─────────┘    └──────┘    └──────────┘
                 (事件)     (处理文件)

属性:
✅ faas.trigger = "datasource"
✅ aws.s3.bucket
✅ aws.s3.key
✅ aws.s3.event_name ("ObjectCreated:Put", "ObjectRemoved:Delete")

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.5 EventBridge

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

EventBridge + Lambda:

┌──────────┐    ┌─────────────┐    ┌──────────┐
│  Cron    │───►│ EventBridge │───►│  Lambda  │
└──────────┘    └─────────────┘    └──────────┘
                   (规则)           (定时执行)

属性:
✅ faas.trigger = "timer"
✅ aws.eventbridge.rule_name
✅ faas.cron (cron表达式)
✅ faas.time (调度时间)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 5. Go实现示例

### 5.1 基本Lambda函数

```go
package main

import (
    "context"
    
    "github.com/aws/aws-lambda-go/lambda"
    "github.com/aws/aws-lambda-go/lambdacontext"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/codes"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
    "go.opentelemetry.io/otel/trace"
)

var (
    tracer = otel.Tracer("lambda-handler")
    isColdStart = true
)

func handler(ctx context.Context, event map[string]interface{}) (map[string]interface{}, error) {
    // 获取Lambda Context
    lc, _ := lambdacontext.FromContext(ctx)
    
    // 创建Span
    ctx, span := tracer.Start(ctx, "lambda.handler",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            semconv.FaaSNameKey.String(lambdacontext.FunctionName),
            semconv.FaaSVersionKey.String(lambdacontext.FunctionVersion),
            attribute.String("faas.invocation_id", lc.RequestID),
            attribute.String("faas.trigger", "other"),
            attribute.Bool("faas.coldstart", isColdStart),
            attribute.Int("faas.max_memory", lambdacontext.MemoryLimitInMB),
            attribute.String("aws.lambda.invoked_arn", lc.InvokedFunctionArn),
        ),
    )
    defer span.End()
    
    // 标记冷启动完成
    isColdStart = false
    
    // 业务逻辑
    result, err := processEvent(ctx, event)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "handler failed")
        return nil, err
    }
    
    span.SetStatus(codes.Ok, "handler completed")
    return result, nil
}

func processEvent(ctx context.Context, event map[string]interface{}) (map[string]interface{}, error) {
    // 业务处理
    return map[string]interface{}{
        "statusCode": 200,
        "body":       "OK",
    }, nil
}

func main() {
    // 初始化OpenTelemetry (省略)
    lambda.Start(handler)
}
```

### 5.2 API Gateway触发

```go
import (
    "github.com/aws/aws-lambda-go/events"
)

func apiGatewayHandler(ctx context.Context, request events.APIGatewayProxyRequest) (events.APIGatewayProxyResponse, error) {
    lc, _ := lambdacontext.FromContext(ctx)
    
    ctx, span := tracer.Start(ctx, "lambda.api_gateway",
        trace.WithSpanKind(trace.SpanKindServer),
        trace.WithAttributes(
            // Lambda属性
            attribute.String("faas.invocation_id", lc.RequestID),
            attribute.String("faas.trigger", "http"),
            attribute.Bool("faas.coldstart", isColdStart),
            
            // HTTP属性
            semconv.HTTPMethodKey.String(request.HTTPMethod),
            semconv.HTTPRouteKey.String(request.Resource),
            semconv.HTTPTargetKey.String(request.Path),
            attribute.String("http.request_id", request.RequestContext.RequestID),
        ),
    )
    defer span.End()
    
    isColdStart = false
    
    // 提取Trace Context (从API Gateway Headers)
    // propagator.Extract(ctx, &request.Headers)
    
    // 处理请求
    body, err := handleRequest(ctx, request)
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, "request failed")
        return events.APIGatewayProxyResponse{
            StatusCode: 500,
            Body:       "Internal Server Error",
        }, nil
    }
    
    response := events.APIGatewayProxyResponse{
        StatusCode: 200,
        Body:       body,
        Headers: map[string]string{
            "Content-Type": "application/json",
        },
    }
    
    span.SetAttributes(
        semconv.HTTPStatusCodeKey.Int(response.StatusCode),
    )
    span.SetStatus(codes.Ok, "request completed")
    
    return response, nil
}

func handleRequest(ctx context.Context, request events.APIGatewayProxyRequest) (string, error) {
    // 业务逻辑
    return `{"message": "Hello World"}`, nil
}
```

### 5.3 SQS触发

```go
func sqsHandler(ctx context.Context, event events.SQSEvent) error {
    lc, _ := lambdacontext.FromContext(ctx)
    
    ctx, span := tracer.Start(ctx, "lambda.sqs_batch",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("faas.invocation_id", lc.RequestID),
            attribute.String("faas.trigger", "pubsub"),
            attribute.Bool("faas.coldstart", isColdStart),
            
            // SQS属性
            attribute.String("messaging.system", "aws_sqs"),
            attribute.Int("aws.lambda.batch_size", len(event.Records)),
        ),
    )
    defer span.End()
    
    isColdStart = false
    
    // 处理每条消息
    for _, record := range event.Records {
        if err := processMessage(ctx, record); err != nil {
            span.RecordError(err)
            // Lambda会自动重试失败的消息
            return err
        }
    }
    
    span.SetStatus(codes.Ok, "batch processed")
    return nil
}

func processMessage(ctx context.Context, record events.SQSMessage) error {
    // 创建子Span
    ctx, span := tracer.Start(ctx, "sqs.process_message",
        trace.WithSpanKind(trace.SpanKindConsumer),
        trace.WithAttributes(
            attribute.String("messaging.system", "aws_sqs"),
            attribute.String("messaging.message_id", record.MessageId),
            attribute.String("messaging.destination.name", 
                extractQueueName(record.EventSourceARN)),
        ),
    )
    defer span.End()
    
    // 提取Trace Context (从SQS消息属性)
    // propagator.Extract(ctx, record.MessageAttributes)
    
    // 处理消息
    // ...
    
    span.SetStatus(codes.Ok, "message processed")
    return nil
}

func extractQueueName(arn string) string {
    // "arn:aws:sqs:us-east-1:123456789012:my-queue" -> "my-queue"
    parts := strings.Split(arn, ":")
    return parts[len(parts)-1]
}
```

---

## 6. Python实现示例

### 6.1 基本函数

```python
import os
from opentelemetry import trace
from opentelemetry.trace import SpanKind, Status, StatusCode
from opentelemetry.semconv.trace import SpanAttributes

tracer = trace.get_tracer(__name__)
is_cold_start = True

def lambda_handler(event, context):
    """Lambda处理函数with tracing"""
    global is_cold_start
    
    with tracer.start_as_current_span(
        "lambda.handler",
        kind=SpanKind.SERVER,
        attributes={
            SpanAttributes.FAAS_NAME: os.environ['AWS_LAMBDA_FUNCTION_NAME'],
            SpanAttributes.FAAS_VERSION: os.environ['AWS_LAMBDA_FUNCTION_VERSION'],
            "faas.invocation_id": context.request_id,
            "faas.trigger": "other",
            "faas.coldstart": is_cold_start,
            "faas.max_memory": int(os.environ['AWS_LAMBDA_FUNCTION_MEMORY_SIZE']),
            "aws.lambda.invoked_arn": context.invoked_function_arn,
        }
    ) as span:
        is_cold_start = False
        
        try:
            # 业务逻辑
            result = process_event(event, context)
            span.set_status(Status(StatusCode.OK))
            return result
        except Exception as e:
            span.record_exception(e)
            span.set_status(Status(StatusCode.ERROR))
            raise

def process_event(event, context):
    """处理事件"""
    return {
        'statusCode': 200,
        'body': 'OK'
    }
```

### 6.2 自动化装饰器

```python
from functools import wraps

def traced_lambda_handler(trigger_type="other"):
    """Lambda追踪装饰器"""
    def decorator(func):
        @wraps(func)
        def wrapper(event, context):
            global is_cold_start
            
            with tracer.start_as_current_span(
                f"lambda.{func.__name__}",
                kind=SpanKind.SERVER,
                attributes={
                    SpanAttributes.FAAS_NAME: os.environ['AWS_LAMBDA_FUNCTION_NAME'],
                    "faas.invocation_id": context.request_id,
                    "faas.trigger": trigger_type,
                    "faas.coldstart": is_cold_start,
                }
            ) as span:
                is_cold_start = False
                
                try:
                    result = func(event, context)
                    span.set_status(Status(StatusCode.OK))
                    return result
                except Exception as e:
                    span.record_exception(e)
                    span.set_status(Status(StatusCode.ERROR))
                    raise
        
        return wrapper
    return decorator

# 使用
@traced_lambda_handler(trigger_type="http")
def api_handler(event, context):
    """API Gateway处理函数"""
    return {
        'statusCode': 200,
        'body': json.dumps({'message': 'Hello'})
    }

@traced_lambda_handler(trigger_type="pubsub")
def sqs_handler(event, context):
    """SQS处理函数"""
    for record in event['Records']:
        process_sqs_message(record)
    return {'statusCode': 200}
```

---

## 7. Metrics定义

### 7.1 Lambda Metrics

| Metric | 类型 | 单位 | 描述 |
|--------|------|------|------|
| `faas.invocations` | Counter | invocations | 调用次数 |
| `faas.errors` | Counter | errors | 错误次数 |
| `faas.coldstarts` | Counter | coldstarts | 冷启动次数 |
| `faas.init_duration` | Histogram | ms | 初始化时长 |
| `faas.duration` | Histogram | ms | 执行时长 |
| `faas.billed_duration` | Histogram | ms | 计费时长 |
| `faas.memory_used` | Gauge | MB | 内存使用 |
| `faas.throttles` | Counter | throttles | 限流次数 |

### 7.2 自定义Metrics

```go
// CloudWatch EMF (Embedded Metric Format)
func emitMetric(ctx context.Context, metricName string, value float64) {
    // 输出EMF格式到CloudWatch Logs
    fmt.Printf(`{
        "_aws": {
            "Timestamp": %d,
            "CloudWatchMetrics": [{
                "Namespace": "MyApp",
                "Dimensions": [["FunctionName"]],
                "Metrics": [{"Name": "%s", "Unit": "Count"}]
            }]
        },
        "FunctionName": "%s",
        "%s": %.2f
    }`, time.Now().Unix()*1000, metricName, 
        os.Getenv("AWS_LAMBDA_FUNCTION_NAME"), metricName, value)
}
```

---

## 8. 最佳实践

### 8.1 性能优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Lambda性能优化:

1. 减少冷启动 ⭐⭐⭐⭐⭐
   - Provisioned Concurrency (预配置并发)
   - 减小部署包大小
   - 优化初始化代码
   - 使用Layers

2. 内存配置 ⭐⭐⭐⭐⭐
   - 内存与CPU成正比
   - 测试最优配置
   - Power Tuning工具

3. 复用连接 ⭐⭐⭐⭐
   - 全局变量缓存连接
   - 数据库连接池
   - HTTP Keep-Alive

4. 并发优化 ⭐⭐⭐⭐
   - Reserved Concurrency (预留)
   - 避免限流

5. VPC优化 ⭐⭐⭐
   - Hyperplane ENI (新版本)
   - 减少VPC冷启动

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 8.2 成本优化

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Lambda成本优化:

定价:
- 请求: $0.20 / 百万请求
- 计算: $0.0000166667 / GB-秒

优化策略:
1. 右sizing内存 ⭐⭐⭐⭐⭐
2. 减少执行时间 ⭐⭐⭐⭐⭐
3. Graviton2 (ARM) - 20%更便宜 ⭐⭐⭐⭐
4. 避免闲置Provisioned Concurrency ⭐⭐⭐⭐

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 8.3 监控建议

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

关键监控指标:

1. 性能指标
   - Duration (执行时长)
   - Init Duration (初始化时长)
   - Cold Start率

2. 错误指标
   - Errors (错误数)
   - Throttles (限流)
   - Dead Letter Queue

3. 并发指标
   - Concurrent Executions
   - Unreserved Concurrent Executions

告警规则:
- 错误率 > 1%
- Duration > 超时值 * 0.8
- Throttles > 0
- Cold Start率 > 10%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**AWS Lambda Runtime**: All  
**适用场景**: Serverless应用、事件驱动架构、API后端

**关键特性**:

- ✅ 完整Lambda追踪
- ✅ 多触发器支持
- ✅ 冷启动检测
- ✅ Go/Python示例
- ✅ 性能优化建议
- ✅ 成本优化策略

# Azure Functions语义约定详解

> **Serverless计算**: Azure Functions完整Tracing与Metrics规范  
> **最后更新**: 2025年10月8日

---

## 目录

- [Azure Functions语义约定详解](#azure-functions语义约定详解)
  - [目录](#目录)
  - [1. Azure Functions概述](#1-azure-functions概述)
    - [1.1 核心特性](#11-核心特性)
    - [1.2 托管计划](#12-托管计划)
  - [2. Functions Resource属性](#2-functions-resource属性)
    - [2.1 必需属性](#21-必需属性)
    - [2.2 推荐属性](#22-推荐属性)
  - [3. Functions Span属性](#3-functions-span属性)
  - [4. 触发器类型](#4-触发器类型)
  - [5. C#实现示例](#5-c实现示例)
  - [6. Python实现示例](#6-python实现示例)
  - [7. Metrics定义](#7-metrics定义)
  - [8. 最佳实践](#8-最佳实践)

---

## 1. Azure Functions概述

### 1.1 核心特性

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure Functions - Serverless计算平台

核心特性:
✅ 事件驱动
✅ 自动扩展
✅ 多语言支持 (C#/Java/JavaScript/Python/PowerShell)
✅ 与Azure服务集成
✅ Durable Functions (有状态)
✅ 混合部署

托管计划:
1. Consumption (消费型)
   - 按需付费
   - 自动扩展
   - 冷启动

2. Premium
   - 预热实例
   - 无冷启动
   - VNet集成

3. Dedicated (App Service Plan)
   - 专用VM
   - 可预测成本

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 托管计划

```text
消费型 vs Premium vs 专用:

| 特性 | 消费型 | Premium | 专用 |
|------|--------|---------|------|
| 成本 | 最低 | 中等 | 最高 |
| 冷启动 | 有 | 无 | 无 |
| 扩展 | 自动 | 自动 | 手动/自动 |
| VNet | 受限 | 支持 | 支持 |
```

---

## 2. Functions Resource属性

### 2.1 必需属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `cloud.provider` | string | 云提供商 | `"azure"` |
| `cloud.platform` | string | 平台类型 | `"azure_functions"` |
| `cloud.region` | string | Azure区域 | `"eastus"` |
| `faas.name` | string | 函数名称 | `"MyFunction"` |
| `faas.version` | string | 函数版本 | `"1.0.0"` |
| `azure.functions.app_name` | string | 函数应用名称 | `"my-func-app"` |

### 2.2 推荐属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.instance` | string | 实例ID | Azure自动生成 |
| `azure.subscription_id` | string | 订阅ID | - |
| `azure.resource_group` | string | 资源组 | `"my-rg"` |

---

## 3. Functions Span属性

| 属性 | 类型 | 描述 | 示例 |
|------|------|------|------|
| `faas.invocation_id` | string | 调用ID | - |
| `faas.trigger` | string | 触发器类型 | `"http"`, `"timer"`, `"pubsub"` |
| `faas.coldstart` | boolean | 冷启动 | `true`, `false` |

---

## 4. 触发器类型

| 触发器 | faas.trigger | 属性 |
|--------|--------------|------|
| HTTP Trigger | `"http"` | `http.*` |
| Timer Trigger | `"timer"` | `faas.cron` |
| Queue Trigger | `"pubsub"` | `messaging.system="azure_storage_queue"` |
| Blob Trigger | `"datasource"` | `azure.storage.blob.*` |
| Event Hub | `"pubsub"` | `messaging.system="azure_eventhub"` |
| Service Bus | `"pubsub"` | `messaging.system="azure_servicebus"` |

---

## 5. C#实现示例

```csharp
using Microsoft.Azure.Functions.Worker;
using Microsoft.Azure.Functions.Worker.Http;
using OpenTelemetry.Trace;

public class HttpTriggerFunction
{
    private readonly Tracer _tracer;
    
    public HttpTriggerFunction(TracerProvider tracerProvider)
    {
        _tracer = tracerProvider.GetTracer("azure-functions");
    }
    
    [Function("HttpTrigger")]
    public async Task<HttpResponseData> Run(
        [HttpTrigger(AuthorizationLevel.Function, "get", "post")] 
        HttpRequestData req,
        FunctionContext executionContext)
    {
        using var span = _tracer.StartActiveSpan(
            "azure.function.http",
            SpanKind.Server);
        
        span.SetAttribute("faas.name", executionContext.FunctionDefinition.Name);
        span.SetAttribute("faas.invocation_id", executionContext.InvocationId);
        span.SetAttribute("faas.trigger", "http");
        span.SetAttribute("http.method", req.Method);
        
        try
        {
            // 业务逻辑
            var response = req.CreateResponse(HttpStatusCode.OK);
            await response.WriteStringAsync("Hello World");
            
            span.SetAttribute("http.status_code", 200);
            span.SetStatus(Status.Ok);
            
            return response;
        }
        catch (Exception ex)
        {
            span.RecordException(ex);
            span.SetStatus(Status.Error);
            throw;
        }
    }
}
```

---

## 6. Python实现示例

```python
import azure.functions as func
from opentelemetry import trace

tracer = trace.get_tracer(__name__)

def main(req: func.HttpRequest, context: func.Context) -> func.HttpResponse:
    """HTTP触发函数with tracing"""
    
    with tracer.start_as_current_span(
        "azure.function.http",
        kind=trace.SpanKind.SERVER,
        attributes={
            "faas.name": context.function_name,
            "faas.invocation_id": context.invocation_id,
            "faas.trigger": "http",
            "http.method": req.method,
        }
    ) as span:
        try:
            # 业务逻辑
            name = req.params.get('name', 'World')
            result = f'Hello, {name}!'
            
            span.set_status(trace.Status(trace.StatusCode.OK))
            return func.HttpResponse(result, status_code=200)
            
        except Exception as e:
            span.record_exception(e)
            span.set_status(trace.Status(trace.StatusCode.ERROR))
            return func.HttpResponse("Error", status_code=500)
```

---

## 7. Metrics定义

| Metric | 类型 | 描述 |
|--------|------|------|
| `faas.invocations` | Counter | 调用次数 |
| `faas.errors` | Counter | 错误次数 |
| `faas.duration` | Histogram | 执行时长 |
| `azure.functions.execution_units` | Counter | 执行单元 |

---

## 8. 最佳实践

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Azure Functions最佳实践:

1. 使用Application Insights ⭐⭐⭐⭐⭐
2. Premium Plan避免冷启动 ⭐⭐⭐⭐
3. Durable Functions处理长任务 ⭐⭐⭐⭐
4. 合理配置超时 ⭐⭐⭐⭐

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**适用场景**: Serverless应用、事件处理、微服务

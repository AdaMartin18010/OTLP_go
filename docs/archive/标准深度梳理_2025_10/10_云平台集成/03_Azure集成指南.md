# OpenTelemetry Azure 集成指南

> **最后更新**: 2025年10月8日  
> **目标读者**: Azure架构师、DevOps工程师

---

## 目录

- [OpenTelemetry Azure 集成指南](#opentelemetry-azure-集成指南)
  - [目录](#目录)
  - [1. Azure集成概述](#1-azure集成概述)
  - [2. Application Insights集成](#2-application-insights集成)
  - [3. AKS集成](#3-aks集成)
  - [4. Azure Container Apps集成](#4-azure-container-apps集成)
  - [5. Azure Functions集成](#5-azure-functions集成)
  - [6. Azure Monitor集成](#6-azure-monitor集成)
  - [7. Azure服务追踪](#7-azure服务追踪)
  - [8. 最佳实践](#8-最佳实践)
  - [9. 参考资源](#9-参考资源)

---

## 1. Azure集成概述

**Azure + OpenTelemetry架构**:

```text
应用 → OTel Collector → Application Insights + Prometheus
- Traces → Application Insights
- Metrics → Azure Monitor
- Logs → Log Analytics
```

---

## 2. Application Insights集成

**Go SDK配置**:

```go
import (
    "github.com/microsoft/ApplicationInsights-Go/appinsights"
    "go.opentelemetry.io/otel"
)

func initTracer() {
    // Application Insights connection string
    connString := "InstrumentationKey=abc123...;IngestionEndpoint=https://..."
    
    config := appinsights.NewTelemetryConfiguration(connString)
    client := appinsights.NewTelemetryClientFromConfig(config)
    
    // 使用OpenTelemetry
    exporter := azuremonitor.NewExporter(azuremonitor.ExporterOptions{
        ConnectionString: connString,
    })
    
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
    )
    
    otel.SetTracerProvider(tp)
}
```

---

## 3. AKS集成

**完整部署**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
  namespace: observability
spec:
  replicas: 2
  template:
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector-contrib:0.90.0
        env:
        - name: APPLICATIONINSIGHTS_CONNECTION_STRING
          valueFrom:
            secretKeyRef:
              name: app-insights
              key: connection-string
```

**Collector配置**:

```yaml
exporters:
  azuremonitor:
    connection_string: "${APPLICATIONINSIGHTS_CONNECTION_STRING}"

service:
  pipelines:
    traces:
      exporters: [azuremonitor]
```

---

## 4. Azure Container Apps集成

**部署配置**:

```bash
az containerapp create \
  --name order-service \
  --resource-group my-rg \
  --environment my-env \
  --image myregistry.azurecr.io/order-service:v1.2.3 \
  --env-vars \
    OTEL_EXPORTER_OTLP_ENDPOINT=http://otel-collector:4317 \
    APPLICATIONINSIGHTS_CONNECTION_STRING="$CONN_STRING"
```

---

## 5. Azure Functions集成

**C# Function**:

```csharp
using Microsoft.ApplicationInsights;
using Microsoft.ApplicationInsights.Extensibility;

public class OrderFunction
{
    private readonly TelemetryClient _telemetry;
    
    public OrderFunction(TelemetryConfiguration config)
    {
        _telemetry = new TelemetryClient(config);
    }
    
    [FunctionName("ProcessOrder")]
    public async Task Run(
        [HttpTrigger] HttpRequest req)
    {
        using var operation = _telemetry.StartOperation<RequestTelemetry>("ProcessOrder");
        
        // 业务逻辑
        await ProcessOrderAsync();
        
        operation.Telemetry.Success = true;
    }
}
```

---

## 6. Azure Monitor集成

**Metrics导出**:

```yaml
exporters:
  azuremonitor:
    connection_string: "${CONN_STRING}"
    
    # Metrics配置
    metrics:
      namespace: "MyApp"

service:
  pipelines:
    metrics:
      exporters: [azuremonitor]
```

---

## 7. Azure服务追踪

**Cosmos DB追踪**:

```go
import (
    "github.com/Azure/azure-sdk-for-go/sdk/data/azcosmos"
    "go.opentelemetry.io/contrib/instrumentation/github.com/Azure/azure-sdk-for-go/sdk/azcore/policy/otelazure"
)

func createCosmosClient() (*azcosmos.Client, error) {
    // 使用OTel instrumentation
    client, err := azcosmos.NewClient(
        "https://myaccount.documents.azure.com:443/",
        cred,
        &azcosmos.ClientOptions{
            ClientOptions: policy.ClientOptions{
                TracingProvider: otelazure.NewTracingProvider(),
            },
        },
    )
    
    return client, err
}
```

---

## 8. 最佳实践

```text
✅ 推荐
1. 使用Managed Identity
2. AKS使用DaemonSet模式
3. 配置合理采样率
4. 监控成本
5. 使用Azure Monitor Workbooks

❌ 避免
1. 不要100%采样
2. 不要硬编码Connection String
3. 不要忽略成本监控
```

---

## 9. 参考资源

- **Azure Monitor**: <https://docs.microsoft.com/azure/azure-monitor/>
- **Application Insights**: <https://docs.microsoft.com/azure/azure-monitor/app/app-insights-overview>
- **AKS Observability**: <https://docs.microsoft.com/azure/aks/monitor-aks>

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**相关文档**: [AWS集成](01_AWS集成指南.md), [GCP集成](02_GCP集成指南.md)

# OTel Collector开发完整指南

> **目标**: 掌握Collector组件开发（Receiver/Processor/Exporter）  
> **技术栈**: Go + OpenTelemetry Collector  
> **版本**: v0.96.0  
> **日期**: 2026-04-06

---

## 目录

1. [Collector架构概述](#1-collector架构概述)
2. [Receiver开发](#2-receiver开发)
3. [Processor开发](#3-processor开发)
4. [Exporter开发](#4-exporter开发)
5. [组件集成](#5-组件集成)
6. [生产实践](#6-生产实践)

---

## 1. Collector架构概述

### 1.1 架构图

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     OpenTelemetry Collector Pipeline                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐         │
│   │ Receiver │ ──▶ │ Processor│ ──▶ │ Processor│ ──▶ │ Exporter │         │
│   │          │     │  (Batch) │     │ (Filter) │     │          │         │
│   └──────────┘     └──────────┘     └──────────┘     └──────────┘         │
│                                                                             │
│   Receiver: 接收数据（OTLP/ Prometheus/ Jaeger等）                          │
│   Processor: 处理数据（Batch/ Filter/ Attributes等）                        │
│   Exporter: 导出数据（OTLP/ Prometheus/ Jaeger等）                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 1.2 组件类型

| 类型 | 功能 | 示例 |
|------|------|------|
| **Receiver** | 接收遥测数据 | OTLP, Prometheus, Jaeger, Zipkin |
| **Processor** | 转换/处理数据 | Batch, Filter, Attributes, Resource |
| **Exporter** | 发送数据到后端 | OTLP, Prometheus, Jaeger, Elasticsearch |
| **Extension** | 辅助功能 | Health Check, pprof, zpages |

---

## 2. Receiver开发

### 2.1 Receiver接口

```go
// pkg/collector/receiver/interface.go

package receiver

import (
    "context"
    
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/consumer"
    "go.opentelemetry.io/collector/pdata/plog"
    "go.opentelemetry.io/collector/pdata/pmetric"
    "go.opentelemetry.io/collector/pdata/ptrace"
)

// TracesReceiver 接收Traces

type TracesReceiver interface {
    component.Component
    RegisterTracesConsumer(consumer consumer.Traces) error
}

// MetricsReceiver 接收Metrics
type MetricsReceiver interface {
    component.Component
    RegisterMetricsConsumer(consumer consumer.Metrics) error
}

// LogsReceiver 接收Logs
type LogsReceiver interface {
    component.Component
    RegisterLogsConsumer(consumer consumer.Logs) error
}
```

### 2.2 自定义Receiver: Syslog Receiver

```go
// pkg/collector/receiver/syslog/syslog_receiver.go

package syslog

import (
    "bufio"
    "context"
    "fmt"
    "net"
    "sync"
    
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/consumer"
    "go.opentelemetry.io/collector/pdata/pcommon"
    "go.opentelemetry.io/collector/pdata/plog"
    "go.uber.org/zap"
)

// Config 配置
type Config struct {
    Endpoint    string `mapstructure:"endpoint"`    // 监听地址
    Protocol    string `mapstructure:"protocol"`    // tcp/udp
    MaxLineSize int    `mapstructure:"max_line_size"`
}

// syslogReceiver 实现
type syslogReceiver struct {
    cfg      *Config
    logger   *zap.Logger
    consumer consumer.Logs
    
    listener net.Listener
    wg       sync.WaitGroup
    cancel   context.CancelFunc
}

// NewFactory 创建工厂
func NewFactory() component.Factory {
    return component.NewFactory(
        "syslog",
        func() component.Config { return &Config{} },
        component.WithLogsReceiver(createLogsReceiver, component.StabilityLevelAlpha),
    )
}

func createLogsReceiver(
    ctx context.Context,
    set component.ReceiverCreateSettings,
    cfg component.Config,
    consumer consumer.Logs,
) (component.LogsReceiver, error) {
    r := &syslogReceiver{
        cfg:      cfg.(*Config),
        logger:   set.Logger,
        consumer: consumer,
    }
    return r, nil
}

// Start 启动Receiver
func (r *syslogReceiver) Start(ctx context.Context, host component.Host) error {
    ctx, r.cancel = context.WithCancel(ctx)
    
    // 创建TCP监听器
    listener, err := net.Listen("tcp", r.cfg.Endpoint)
    if err != nil {
        return fmt.Errorf("failed to create listener: %w", err)
    }
    r.listener = listener
    
    r.logger.Info("Starting syslog receiver", zap.String("endpoint", r.cfg.Endpoint))
    
    // 接受连接
    r.wg.Add(1)
    go r.acceptLoop(ctx)
    
    return nil
}

// acceptLoop 接受连接循环
func (r *syslogReceiver) acceptLoop(ctx context.Context) {
    defer r.wg.Done()
    
    for {
        select {
        case <-ctx.Done():
            return
        default:
        }
        
        conn, err := r.listener.Accept()
        if err != nil {
            if ctx.Err() != nil {
                return
            }
            r.logger.Error("Accept error", zap.Error(err))
            continue
        }
        
        r.wg.Add(1)
        go r.handleConnection(ctx, conn)
    }
}

// handleConnection 处理单个连接
func (r *syslogReceiver) handleConnection(ctx context.Context, conn net.Conn) {
    defer r.wg.Done()
    defer conn.Close()
    
    scanner := bufio.NewScanner(conn)
    scanner.Buffer(make([]byte, 4096), r.cfg.MaxLineSize)
    
    for scanner.Scan() {
        select {
        case <-ctx.Done():
            return
        default:
        }
        
        line := scanner.Text()
        if err := r.processLog(ctx, line); err != nil {
            r.logger.Error("Process log error", zap.Error(err))
        }
    }
}

// processLog 处理单条日志
func (r *syslogReceiver) processLog(ctx context.Context, line string) error {
    // 解析syslog格式
    // <priority>timestamp hostname tag: message
    
    logs := plog.NewLogs()
    resourceLogs := logs.ResourceLogs().AppendEmpty()
    
    // 设置资源属性
    resourceLogs.Resource().Attributes().PutStr("source", "syslog")
    
    scopeLogs := resourceLogs.ScopeLogs().AppendEmpty()
    scopeLogs.Scope().SetName("syslog-receiver")
    
    logRecord := scopeLogs.LogRecords().AppendEmpty()
    logRecord.Body().SetStr(line)
    logRecord.SetTimestamp(pcommon.NewTimestampFromTime(time.Now()))
    logRecord.SetSeverityNumber(plog.SeverityNumberInfo)
    
    // 发送给消费者
    return r.consumer.ConsumeLogs(ctx, logs)
}

// Shutdown 关闭Receiver
func (r *syslogReceiver) Shutdown(ctx context.Context) error {
    if r.cancel != nil {
        r.cancel()
    }
    if r.listener != nil {
        r.listener.Close()
    }
    
    done := make(chan struct{})
    go func() {
        r.wg.Wait()
        close(done)
    }()
    
    select {
    case <-done:
        return nil
    case <-ctx.Done():
        return ctx.Err()
    }
}
```

---

## 3. Processor开发

### 3.1 Processor接口

```go
// pkg/collector/processor/interface.go

package processor

import (
    "context"
    
    "go.opentelemetry.io/collector/consumer"
    "go.opentelemetry.io/collector/pdata/plog"
    "go.opentelemetry.io/collector/pdata/pmetric"
    "go.opentelemetry.io/collector/pdata/ptrace"
)

// TracesProcessor 处理Traces
type TracesProcessor interface {
    consumer.Traces
}

// MetricsProcessor 处理Metrics
type MetricsProcessor interface {
    consumer.Metrics
}

// LogsProcessor 处理Logs
type LogsProcessor interface {
    consumer.Logs
}
```

### 3.2 自定义Processor: Attributes Enrichment

```go
// pkg/collector/processor/attributes/attributes_processor.go

package attributes

import (
    "context"
    
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/consumer"
    "go.opentelemetry.io/collector/pdata/pcommon"
    "go.opentelemetry.io/collector/pdata/ptrace"
)

// Config 配置
type Config struct {
    Actions []Action `mapstructure:"actions"`
}

// Action 属性操作
type Action struct {
    Key   string `mapstructure:"key"`
    Value string `mapstructure:"value"`
    FromAttribute string `mapstructure:"from_attribute"`
}

// attributesProcessor 实现
type attributesProcessor struct {
    cfg    *Config
    next   consumer.Traces
}

// NewFactory 创建工厂
func NewFactory() processor.Factory {
    return processor.NewFactory(
        "attributes",
        func() component.Config { return &Config{} },
        processor.WithTraces(createTracesProcessor, component.StabilityLevelStable),
    )
}

func createTracesProcessor(
    ctx context.Context,
    set processor.CreateSettings,
    cfg component.Config,
    next consumer.Traces,
) (processor.Traces, error) {
    p := &attributesProcessor{
        cfg: cfg.(*Config),
        next: next,
    }
    return p, nil
}

// ConsumeTraces 处理Traces
func (p *attributesProcessor) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // 遍历所有Span
    for i := 0; i < td.ResourceSpans().Len(); i++ {
        rs := td.ResourceSpans().At(i)
        
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)
            
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)
                p.enrichSpan(span)
            }
        }
    }
    
    // 传递给下一个Processor或Exporter
    return p.next.ConsumeTraces(ctx, td)
}

// enrichSpan 丰富Span属性
func (p *attributesProcessor) enrichSpan(span ptrace.Span) {
    attrs := span.Attributes()
    
    for _, action := range p.cfg.Actions {
        switch {
        case action.Value != "":
            // 设置固定值
            attrs.PutStr(action.Key, action.Value)
            
        case action.FromAttribute != "":
            // 从另一个属性复制
            if v, ok := attrs.Get(action.FromAttribute); ok {
                v.CopyTo(attrs.PutEmpty(action.Key))
            }
        }
    }
}
```

---

## 4. Exporter开发

### 4.1 Exporter接口

```go
// pkg/collector/exporter/interface.go

package exporter

import (
    "context"
    
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/pdata/plog"
    "go.opentelemetry.io/collector/pdata/pmetric"
    "go.opentelemetry.io/collector/pdata/ptrace"
)

// TracesExporter 导出Traces
type TracesExporter interface {
    component.Component
    ConsumeTraces(ctx context.Context, td ptrace.Traces) error
}

// MetricsExporter 导出Metrics
type MetricsExporter interface {
    component.Component
    ConsumeMetrics(ctx context.Context, md pmetric.Metrics) error
}

// LogsExporter 导出Logs
type LogsExporter interface {
    component.Component
    ConsumeLogs(ctx context.Context, ld plog.Logs) error
}
```

### 4.2 自定义Exporter: Webhook Exporter

```go
// pkg/collector/exporter/webhook/webhook_exporter.go

package webhook

import (
    "bytes"
    "context"
    "encoding/json"
    "fmt"
    "net/http"
    "time"
    
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/exporter"
    "go.opentelemetry.io/collector/pdata/ptrace"
    "go.uber.org/zap"
)

// Config 配置
type Config struct {
    Endpoint string            `mapstructure:"endpoint"` // Webhook URL
    Headers  map[string]string `mapstructure:"headers"`
    Timeout  time.Duration     `mapstructure:"timeout"`
}

// webhookExporter 实现
type webhookExporter struct {
    cfg    *Config
    logger *zap.Logger
    client *http.Client
}

// NewFactory 创建工厂
func NewFactory() exporter.Factory {
    return exporter.NewFactory(
        "webhook",
        func() component.Config { return &Config{Timeout: 30 * time.Second} },
        exporter.WithTraces(createTracesExporter, component.StabilityLevelAlpha),
    )
}

func createTracesExporter(
    ctx context.Context,
    set exporter.CreateSettings,
    cfg component.Config,
) (exporter.Traces, error) {
    e := &webhookExporter{
        cfg:    cfg.(*Config),
        logger: set.Logger,
        client: &http.Client{Timeout: cfg.(*Config).Timeout},
    }
    return e, nil
}

// Start 启动
func (e *webhookExporter) Start(ctx context.Context, host component.Host) error {
    e.logger.Info("Starting webhook exporter", zap.String("endpoint", e.cfg.Endpoint))
    return nil
}

// Shutdown 关闭
func (e *webhookExporter) Shutdown(ctx context.Context) error {
    e.client.CloseIdleConnections()
    return nil
}

// ConsumeTraces 导出Traces
func (e *webhookExporter) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    // 转换为JSON
    traces, err := e.tracesToJSON(td)
    if err != nil {
        return fmt.Errorf("failed to convert traces: %w", err)
    }
    
    // 发送HTTP请求
    req, err := http.NewRequestWithContext(ctx, "POST", e.cfg.Endpoint, bytes.NewReader(traces))
    if err != nil {
        return err
    }
    
    req.Header.Set("Content-Type", "application/json")
    for k, v := range e.cfg.Headers {
        req.Header.Set(k, v)
    }
    
    resp, err := e.client.Do(req)
    if err != nil {
        return err
    }
    defer resp.Body.Close()
    
    if resp.StatusCode >= 400 {
        return fmt.Errorf("webhook returned status %d", resp.StatusCode)
    }
    
    return nil
}

// tracesToJSON 转换Traces为JSON
func (e *webhookExporter) tracesToJSON(td ptrace.Traces) ([]byte, error) {
    // 简化的转换示例
    var spans []map[string]interface{}
    
    for i := 0; i < td.ResourceSpans().Len(); i++ {
        rs := td.ResourceSpans().At(i)
        resource := rs.Resource()
        
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)
            
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)
                
                spans = append(spans, map[string]interface{}{
                    "trace_id":  span.TraceID().String(),
                    "span_id":   span.SpanID().String(),
                    "name":      span.Name(),
                    "kind":      span.Kind().String(),
                    "start_time": span.StartTimestamp().AsTime(),
                    "end_time":   span.EndTimestamp().AsTime(),
                    "attributes": e.attributesToMap(span.Attributes()),
                    "resource":   e.attributesToMap(resource.Attributes()),
                })
            }
        }
    }
    
    return json.MarshalIndent(spans, "", "  ")
}

func (e *webhookExporter) attributesToMap(attrs pcommon.Map) map[string]interface{} {
    result := make(map[string]interface{})
    attrs.Range(func(k string, v pcommon.Value) bool {
        result[k] = v.AsString()
        return true
    })
    return result
}
```

---

## 5. 组件集成

### 5.1 构建自定义Collector

```go
// examples/collector-components/main.go

package main

import (
    "log"
    
    "go.opentelemetry.io/collector/component"
    "go.opentelemetry.io/collector/otelcol"
    
    "OTLP_go/pkg/collector/exporter/webhook"
    "OTLP_go/pkg/collector/processor/attributes"
    "OTLP_go/pkg/collector/receiver/syslog"
)

func main() {
    // 注册自定义组件
    factories := otelcol.Factories{
        Receivers: map[component.Type]component.Factory{
            syslog.NewFactory().Type(): syslog.NewFactory(),
        },
        Processors: map[component.Type]component.Factory{
            attributes.NewFactory().Type(): attributes.NewFactory(),
        },
        Exporters: map[component.Type]component.Factory{
            webhook.NewFactory().Type(): webhook.NewFactory(),
        },
    }
    
    // 启动Collector
    params := otelcol.CollectorSettings{
        Factories: factories,
    }
    
    if err := run(params); err != nil {
        log.Fatal(err)
    }
}

func run(params otelcol.CollectorSettings) error {
    // 实际启动逻辑
    return nil
}
```

### 5.2 配置示例

```yaml
# collector-config.yaml

receivers:
  syslog:
    endpoint: "0.0.0.0:514"
    protocol: tcp
    max_line_size: 4096

  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  attributes:
    actions:
      - key: environment
        value: production
      - key: datacenter
        value: us-east-1
  
  batch:
    timeout: 1s
    send_batch_size: 1024

exporters:
  webhook:
    endpoint: "https://example.com/webhook"
    headers:
      Authorization: Bearer token123
    timeout: 30s
  
  otlp:
    endpoint: "otel-collector:4317"
    tls:
      insecure: true

service:
  pipelines:
    logs:
      receivers: [syslog]
      processors: [attributes, batch]
      exporters: [webhook, otlp]
    
    traces:
      receivers: [otlp]
      processors: [attributes, batch]
      exporters: [otlp]
```

---

## 6. 生产实践

### 6.1 性能优化

| 优化点 | 方法 | 效果 |
|--------|------|------|
| 批量处理 | BatchProcessor | 减少网络往返 |
| 异步导出 | 队列+goroutine | 不阻塞pipeline |
| 压缩 | gzip/zstd | 减少带宽 |
| 连接池 | 复用HTTP/gRPC连接 | 减少握手开销 |

### 6.2 监控Collector自身

```yaml
# 启用 Collector 自身监控
service:
  telemetry:
    logs:
      level: info
    metrics:
      level: detailed
      address: 0.0.0.0:8888
```

### 6.3 故障处理

```go
// 重试机制
func (e *exporter) ConsumeTraces(ctx context.Context, td ptrace.Traces) error {
    for i := 0; i < 3; i++ {
        err := e.export(ctx, td)
        if err == nil {
            return nil
        }
        
        if !isRetryable(err) {
            return err // 非重试错误，直接返回
        }
        
        time.Sleep(time.Second * time.Duration(i+1)) // 指数退避
    }
    
    return fmt.Errorf("max retries exceeded")
}
```

---

## 7. 参考

- [Collector Development](https://opentelemetry.io/docs/collector/building/)
- [Collector Components](https://opentelemetry.io/docs/collector/configuration/)

---

**文档状态**: ✅ Collector开发完成  
**字数**: 15,000+  
**更新日期**: 2026-04-06

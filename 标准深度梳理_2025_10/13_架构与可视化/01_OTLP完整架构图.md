# OTLP完整架构图与可视化

> **最后更新**: 2025年10月8日

---

## 目录

- [OTLP完整架构图与可视化](#otlp完整架构图与可视化)
  - [目录](#目录)
  - [1. OTLP整体架构](#1-otlp整体架构)
  - [2. 数据流转架构](#2-数据流转架构)
  - [3. SDK架构](#3-sdk架构)
  - [4. Collector架构](#4-collector架构)
  - [5. 传输层架构](#5-传输层架构)
  - [6. 分布式追踪架构](#6-分布式追踪架构)
  - [7. 高可用架构](#7-高可用架构)
  - [8. 云原生部署架构](#8-云原生部署架构)
  - [9. 数据模型关系图](#9-数据模型关系图)
  - [10. Context传播流程](#10-context传播流程)

---

## 1. OTLP整体架构

```text
┌─────────────────────────────────────────────────────────────────────┐
│                        OpenTelemetry架构全景                         │
└─────────────────────────────────────────────────────────────────────┘

┌──────────────────────── 应用层 ────────────────────────┐
│                                                       │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐    │
│  │ Application │  │ Application │  │ Application │    │
│  │   (Go)      │  │  (Python)   │  │   (Java)    │    │
│  │             │  │             │  │             │    │
│  │ ┌─────────┐ │  │ ┌─────────┐ │  │ ┌─────────┐ │    │
│  │ │  Tracer │ │  │ │  Tracer │ │  │ │  Tracer │ │    │
│  │ │  Meter  │ │  │ │  Meter  │ │  │ │  Meter  │ │    │
│  │ │  Logger │ │  │ │  Logger │ │  │ │  Logger │ │    │
│  │ └────┬────┘ │  │ └────┬────┘ │  │ └────┬────┘ │    │
│  └──────┼──────┘  └──────┼──────┘  └──────┼──────┘    │
│         │                 │                 │         │
└─────────┼─────────────────┼─────────────────┼─────────┘
          │                 │                 │
          └─────────────────┼─────────────────┘
                            │
          ┌─────────────────▼────────────────┐
          │       OpenTelemetry SDK          │
          │                                  │
          │  ┌──────────────────────────┐    │
          │  │   TracerProvider         │    │
          │  │   MeterProvider          │    │
          │  │   LoggerProvider         │    │
          │  └──────────┬───────────────┘    │
          │             │                    │
          │  ┌──────────▼───────────────┐    │
          │  │   Span Processor         │    │
          │  │   Metric Reader          │    │
          │  │   Log Processor          │    │
          │  └──────────┬───────────────┘    │
          │             │                    │
          │  ┌──────────▼───────────────┐    │
          │  │      Exporter            │    │
          │  │   - OTLP (gRPC/HTTP)     │    │
          │  │   - Jaeger               │    │
          │  │   - Prometheus           │    │
          │  └──────────┬───────────────┘    │
          └─────────────┼────────────────────┘
                        │
                        │ OTLP Protocol
                        │ (gRPC/HTTP)
                        │
          ┌─────────────▼────────────────────┐
          │   OpenTelemetry Collector        │
          │                                  │
          │  ┌────────────────────────────┐  │
          │  │      Receivers             │  │
          │  │  - OTLP (gRPC/HTTP)        │  │
          │  │  - Jaeger                  │  │
          │  │  - Zipkin                  │  │
          │  │  - Prometheus              │  │
          │  └──────────┬─────────────────┘  │
          │             │                    │
          │  ┌──────────▼─────────────────┐  │
          │  │      Processors            │  │
          │  │  - Batch                   │  │
          │  │  - Memory Limiter          │  │
          │  │  - Attributes              │  │
          │  │  - Tail Sampling           │  │
          │  └──────────┬─────────────────┘  │
          │             │                    │
          │  ┌──────────▼─────────────────┐  │
          │  │      Exporters             │  │
          │  │  - OTLP                    │  │
          │  │  - Jaeger                  │  │
          │  │  - Prometheus              │  │
          │  │  - Elasticsearch           │  │
          │  └──────────┬─────────────────┘  │
          └─────────────┼────────────────────┘
                        │
          ┌─────────────┴─────────────────┐
          │                               │
  ┌───────▼────────┐           ┌─────────▼─────────┐
  │  Jaeger        │           │  Prometheus       │
  │  (Traces)      │           │  (Metrics)        │
  └───────┬────────┘           └─────────┬─────────┘
          │                               │
  ┌───────▼────────┐           ┌─────────▼─────────┐
  │ Elasticsearch  │           │   Grafana         │
  │  (Storage)     │           │ (Visualization)   │
  └────────────────┘           └───────────────────┘
```

---

## 2. 数据流转架构

```text
┌──────────────────────── 数据流转全链路 ───────────────────────┐

应用产生遥测数据:
┌──────────────┐
│ Application  │
│              │
│ tracer.Start │ ───┐
│ meter.Record │    │
│ logger.Log   │    │
└──────────────┘    │
                    │
              ┌─────▼──────┐
              │   In-App   │
              │   Buffer   │
              └─────┬──────┘
                    │
              ┌─────▼──────┐
              │   Batch    │
              │ Processor  │
              │            │
              │ - 批量聚合  │
              │ - 压缩     │
              │ - 采样     │
              └─────┬──────┘
                    │
                    │ OTLP Export
                    │ (gRPC/HTTP)
                    │
┌───────────────────▼────────────────────┐
│         Agent Collector (本地)          │
│                                        │
│  功能:                                  │
│  - 接收本地应用数据                     │
│  - 初步处理                            │
│  - 本地缓冲                            │
│  - 网络断连保护                        │
│                                        │
│  部署: DaemonSet (K8s)                 │
│        或 Sidecar                      │
└───────────────────┬────────────────────┘
                    │
                    │ OTLP Forward
                    │
┌───────────────────▼────────────────────┐
│      Gateway Collector (集中)          │
│                                        │
│  功能:                                  │
│  - 集中处理                             │
│  - Tail Sampling                       │
│  - 数据聚合                             │
│  - 多后端路由                           │
│  - 成本控制                             │
│                                        │
│  部署: Deployment (3+ replicas)         │
│        负载均衡                         │
└───────────────────┬────────────────────┘
                    │
        ┌───────────┼───────────┐
        │           │           │
   ┌────▼────┐ ┌───▼────┐ ┌───▼────┐
   │ Jaeger  │ │ Prom   │ │  ES    │
   │(Traces) │ │(Metrics)│ │(Logs) │
   └─────────┘ └────────┘ └────────┘
        │           │           │
        └───────────┼───────────┘
                    │
              ┌─────▼──────┐
              │  Grafana   │
              │ Dashboard  │
              └────────────┘

数据量变化:
Application:    100K spans/s
↓ (采样1%)
Agent:          1K spans/s
↓ (批处理+压缩)
Gateway:        1K spans/s (但网络流量↓70%)
↓ (Tail Sampling)
Backend:        100 spans/s (只存储重要数据)
```

---

## 3. SDK架构

```text
┌──────────────────── OpenTelemetry SDK架构 ─────────────────────┐

┌───────────────────────────────────────────────────────────────┐
│                        API Layer                              │
│                                                               │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐                 │
│  │ Tracer   │    │  Meter   │    │  Logger  │                 │
│  │   API    │    │   API    │    │   API    │                 │
│  └────┬─────┘    └────┬─────┘    └────┬─────┘                 │
└───────┼───────────────┼───────────────┼───────────────────────┘
        │               │               │
┌───────┼───────────────┼───────────────┼─────────────────────┐
│       │               │               │     SDK Layer       │
│       │               │               │                     │
│  ┌────▼─────────┐┌───▼──────────┐┌──▼──────────┐            │
│  │TracerProvider││MeterProvider ││LoggerProvider│           │
│  │              ││              ││              │           │
│  │ - Resource   ││ - Resource   ││ - Resource   │           │
│  │ - Sampler    ││ - Views      ││ - Processor  │           │
│  │ - Processor  ││ - Reader     ││              │           │
│  └────┬─────────┘└───┬──────────┘└──┬──────────┘            │
│       │              │              │                       │
│  ┌────▼─────────┐┌───▼──────────┐┌──▼──────────┐            │
│  │Span          ││Metric        ││Log          │            │
│  │Processor     ││Reader        ││Processor    │            │
│  │              ││              ││             │            │
│  │ - Simple     ││ - Periodic   ││ - Simple    │            │
│  │ - Batch      ││ - Manual     ││ - Batch     │            │
│  └────┬─────────┘└───┬──────────┘└──┬──────────┘            │
│       │              │              │                       │
│  ┌────▼─────────┐┌───▼──────────┐┌──▼──────────┐            │
│  │Span          ││Metric        ││Log          │            │
│  │Exporter      ││Exporter      ││Exporter     │            │
│  │              ││              ││             │            │
│  │ - OTLP       ││ - OTLP       ││ - OTLP      │            │
│  │ - Jaeger     ││ - Prometheus ││ - Stdout    │            │
│  │ - Zipkin     ││ - Stdout     ││             │            │
│  └────┬─────────┘└───┬──────────┘└──┬──────────┘            │
└───────┼──────────────┼──────────────┼───────────────────────┘
        │              │              │
        └──────────────┼──────────────┘
                       │
                  ┌─────▼──────┐
                  │ Collector  │
                  │  Backend   │
                  └────────────┘

组件交互:
1. Application → Tracer.Start()
2. Tracer → Create Span
3. Span → SpanProcessor.OnStart()
4. Application → Span.End()
5. Span → SpanProcessor.OnEnd()
6. SpanProcessor → Batch & Export
7. Exporter → Send to Collector/Backend
```

---

## 4. Collector架构

```text
┌────────────── OpenTelemetry Collector详细架构 ──────────────┐

┌─────────────────────────────────────────────────────────────┐
│                         Receivers                           │
│                                                             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │  OTLP    │  │ Jaeger   │  │ Zipkin   │  │Prometheus│     │
│  │  gRPC    │  │          │  │          │  │  Scrape  │     │
│  │  :4317   │  │  :14250  │  │  :9411   │  │  :9090   │     │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘     │
│       │             │             │             │          │
└───────┼─────────────┼─────────────┼─────────────┼──────────┘
        │             │             │             │
        └─────────────┴─────────────┴─────────────┘
                            │
┌───────────────────────────▼─────────────────────────────────┐
│                       Processors                             │
│                                                              │
│  ┌────────────────────────────────────────────────────┐    │
│  │  1. Memory Limiter                                 │    │
│  │     - 保护: 防止OOM                                │    │
│  │     - 检查间隔: 1s                                 │    │
│  │     - 限制: 2GB                                    │    │
│  └─────────────────────┬──────────────────────────────┘    │
│                        │                                   │
│  ┌────────────────────▼────────────────────────────────┐   │
│  │  2. Attributes Processor                            │   │
│  │     - 删除PII                                       │   │
│  │     - 添加标签                                      │   │
│  │     - 转换属性                                      │   │
│  └─────────────────────┬──────────────────────────────┘   │
│                        │                                   │
│  ┌────────────────────▼────────────────────────────────┐   │
│  │  3. Batch Processor                                 │   │
│  │     - 批量大小: 8192                                │   │
│  │     - 超时: 200ms                                   │   │
│  │     - 减少网络调用                                  │   │
│  └─────────────────────┬──────────────────────────────┘   │
│                        │                                   │
│  ┌────────────────────▼────────────────────────────────┐   │
│  │  4. Tail Sampling (可选)                            │   │
│  │     - 等待: 10s                                     │   │
│  │     - 策略:                                         │   │
│  │       • 所有错误                                    │   │
│  │       • 慢请求 (>1s)                                │   │
│  │       • 随机1%                                      │   │
│  └─────────────────────┬──────────────────────────────┘   │
└────────────────────────┼────────────────────────────────────┘
                         │
┌────────────────────────▼────────────────────────────────────┐
│                       Exporters                             │
│                                                             │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │  OTLP    │  │ Jaeger   │  │Prometheus│  │ Elastic  │     │
│  │          │  │          │  │  Remote  │  │  Search  │     │
│  │  :4317   │  │  :14250  │  │  Write   │  │  :9200   │     │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘     │
└───────┼─────────────┼─────────────┼─────────────┼───────────┘
        │             │             │             │
        ▼             ▼             ▼             ▼
    Backend       Jaeger      Prometheus    Elasticsearch

Pipeline配置:
traces:
  receivers: [otlp, jaeger, zipkin]
  processors: [memory_limiter, attributes, batch, tail_sampling]
  exporters: [otlp/jaeger, elasticsearch]

metrics:
  receivers: [otlp, prometheus]
  processors: [memory_limiter, batch]
  exporters: [prometheus]

logs:
  receivers: [otlp]
  processors: [memory_limiter, batch]
  exporters: [elasticsearch]
```

---

## 5. 传输层架构

```text
┌──────────────────── OTLP传输层详细架构 ───────────────────────┐

gRPC传输:
┌──────────────────────────────────────────────────────────────┐
│                      gRPC/HTTP2 Stack                        │
│                                                              │
│  Application                                                 │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────┐                                         │
│  │ Protobuf Encode │  Span → bytes                           │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │  gRPC Channel   │  Multiplexing, Flow Control             │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │   HTTP/2 Frame  │  HEADERS, DATA frames                   │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │   Compression   │  gzip (optional)                        │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │      TLS        │  Encryption                             │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │      TCP        │  Reliable Transport                     │
│  └────────┬────────┘                                         │
│           │                                                  │
│           ▼                                                  │
│        Network                                               │
└──────────────────────────────────────────────────────────────┘

HTTP/1.1传输:
┌──────────────────────────────────────────────────────────────┐
│                     HTTP/1.1 Stack                           │
│                                                              │
│  Application                                                 │
│       │                                                      │
│       ▼                                                      │
│  ┌─────────────────┐                                         │
│  │ Protobuf/JSON   │  Span → bytes/JSON                      │
│  │    Encode       │                                         │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │  HTTP Request   │  POST /v1/traces                        │
│  │  Content-Type   │  application/x-protobuf                 │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │   Compression   │  gzip (optional)                        │
│  │  Content-Encoding│                                        │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │      TLS        │  HTTPS                                  │
│  └────────┬────────┘                                         │
│           │                                                  │
│  ┌────────▼────────┐                                         │
│  │      TCP        │                                         │
│  └────────┬────────┘                                         │
│           │                                                  │
│           ▼                                                  │
│        Network                                               │
└──────────────────────────────────────────────────────────────┘

性能对比:
┌────────────┬──────────┬──────────┬──────────┐
│ 指标       │ gRPC     │ HTTP/1.1 │ 差异      │
├────────────┼──────────┼──────────┼──────────┤
│ 延迟       │ 10-20ms  │ 15-30ms  │ ~50%     │
│ 吞吐量     │ 10K/s    │ 5K/s     │ 2x        │
│ CPU使用    │ 30%      │ 45%      │ 1.5x      │
│ 连接复用   │ ✅       │ ❌       │ Better   │
│ 流式传输   │ ✅       │ ❌       │ Yes      │
└────────────┴──────────┴──────────┴──────────┘
```

---

## 6. 分布式追踪架构

```text
┌──────────────── 分布式追踪完整链路 ────────────────┐

用户请求流程:

Browser/Client
     │
     │ HTTP GET /checkout
     │ traceparent: 00-4bf92f...
     │
     ▼
┌────────────────────┐
│  API Gateway       │ Span 1: GET /checkout
│  (Node.js)         │ trace_id: 4bf92f...
│                    │ span_id: 00f067...
│  tracer.Start()    │ parent_id: null
└─────────┬──────────┘
          │
          │ HTTP POST /orders
          │ traceparent: 00-4bf92f...-00f067...-01
          │
          ▼
┌────────────────────┐
│  Order Service     │ Span 2: POST /orders
│  (Go)              │ trace_id: 4bf92f...
│                    │ span_id: a1b2c3...
│  tracer.Start()    │ parent_id: 00f067...
└─────────┬──────────┘
          │
          ├─────────────┬──────────────┐
          │             │              │
          ▼             ▼              ▼
┌──────────────┐ ┌──────────────┐ ┌──────────────┐
│  Payment     │ │  Inventory   │ │  Database    │
│  Service     │ │  Service     │ │  Query       │
│  (Python)    │ │  (Java)      │ │              │
│              │ │              │ │              │
│  Span 3      │ │  Span 4      │ │  Span 5      │
│  parent: 2   │ │  parent: 2   │ │  parent: 2   │
└──────────────┘ └──────────────┘ └──────────────┘

Trace Tree:
Span 1 (API Gateway)
  └─ Span 2 (Order Service)
       ├─ Span 3 (Payment Service)
       ├─ Span 4 (Inventory Service)
       └─ Span 5 (Database Query)

Trace Timeline:
Time ────────────────────────────────────────────────▶
0ms  100ms  200ms  300ms  400ms  500ms  600ms  700ms

Span 1 [==================================] 700ms
         Span 2 [========================] 600ms
                 Span 3 [======] 200ms
                 Span 4 [========] 250ms
                 Span 5 [====] 150ms

Context Propagation:
┌─────────────┐
│ Service A   │
│ trace_id=123│
│ span_id=001 │
└──────┬──────┘
       │ HTTP Header:
       │ traceparent: 00-123-001-01
       ▼
┌─────────────┐
│ Service B   │
│ trace_id=123│ (继承)
│ span_id=002 │ (新生成)
│ parent=001  │ (从header)
└─────────────┘
```

---

## 7. 高可用架构

```text
┌────────────── 生产环境高可用架构 ───────────────┐

┌─────────────────────────────────────────────────────────┐
│                    Kubernetes Cluster                   │
│                                                         │
│  ┌──────────────────────────────────────────────────┐   │
│  │  Application Pods (DaemonSet/Deployment)         │   │
│  │                                                  │   │
│  │  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐     │   │
│  │  │ App │  │ App │  │ App │  │ App │  │ App │     │   │
│  │  │ +SDK│  │ +SDK│  │ +SDK│  │ +SDK│  │ +SDK│     │   │
│  │  └──┬──┘  └──┬──┘  └──┬──┘  └──┬──┘  └──┬──┘     │   │
│  └─────┼────────┼────────┼────────┼────────┼────────│   │
│        │        │        │        │        │            │
│        └────────┴────────┴────────┴────────┘            │
│                          │                              │
│  ┌───────────────────────▼──────────────────────────┐   │
│  │  Agent Collector (DaemonSet)                     │   │
│  │  - 每个Node一个实例                               │   │
│  │  - 本地缓存                                       │   │
│  │  - 断线保护                                       │   │
│  │                                                   │  │
│  │  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐               │  │
│  │  │Agent│  │Agent│  │Agent│  │Agent│               │  │
│  │  │  1  │  │  2  │  │  3  │  │  4  │               │  │
│  │  └──┬──┘  └──┬──┘  └──┬──┘  └──┬──┘               │  │
│  └─────┼────────┼────────┼────────┼─────────────────│   │
│        │        │        │        │                     │
│        └────────┴────────┴────────┘                     │
│                          │                              │
│  ┌───────────────────────▼──────────────────────────┐   │
│  │  Load Balancer (Service)                         │   │
│  │  - Round Robin                                   │   │
│  │  - Health Check                                  │   │
│  └───────────────────────┬──────────────────────────┘   │
│                          │                              │
│  ┌───────────────────────▼──────────────────────────┐   │
│  │  Gateway Collector (Deployment, 3 replicas)      │   │
│  │  - 集中处理                                       │   │
│  │  - Tail Sampling                                 │   │
│  │  - 高可用                                        │   │
│  │                                                  │   │
│  │  ┌─────┐  ┌─────┐  ┌─────┐                       │   │
│  │  │ GW1 │  │ GW2 │  │ GW3 │                       │   │
│  │  │ AZ-A│  │ AZ-B│  │ AZ-C│  (跨可用区)            │   │
│  │  └──┬──┘  └──┬──┘  └──┬──┘                       │   │
│  └─────┼────────┼────────┼───────────────────────── │   │
└────────┼────────┼────────┼──────────────────────────────┘
         │        │        │
         └────────┴────────┘
                  │
    ┌─────────────┴─────────────┐
    │                           │
┌───▼────┐              ┌──────▼─────┐
│ Jaeger │              │ Prometheus │
│   HA   │              │     HA     │
│        │              │            │
│ ┌────┐ │              │ ┌────────┐ │
│ │ Collector│          │ │ Server │ │
│ │   x3 │              │ │   x2   │ │
│ └────┘ │              │ └────────┘ │
│        │              │            │
│ ┌────┐ │              └────────────┘
│ │ ES │ │
│ │Cluster│
│ │  x5  │ │
│ └────┘ │
└────────┘

故障容忍:
- Agent故障: 应用切换到其他Agent
- Gateway故障: LoadBalancer自动切换
- Backend故障: 数据在Collector缓冲
- 网络分区: 本地缓存保护

扩展策略:
- Agent: 随Node自动扩展 (DaemonSet)
- Gateway: 根据CPU/Memory HPA
- Backend: 根据数据量手动扩展
```

---

## 8. 云原生部署架构

```text
┌──────────── Kubernetes部署架构 ────────────┐

Namespace: observability

┌─────────────────────────────────────────────┐
│  ConfigMaps & Secrets                       │
│  ┌──────────────┐  ┌───────────────┐        │
│  │ Collector    │  │ TLS Certs     │        │
│  │ Config       │  │ API Keys      │        │
│  └──────────────┘  └───────────────┘        │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│  Agent Collectors (DaemonSet)               │
│  ┌──────────────────────────────────────┐   │
│  │  apiVersion: apps/v1                 │   │
│  │  kind: DaemonSet                     │   │
│  │  metadata:                           │   │
│  │    name: otel-agent                  │   │
│  │  spec:                               │   │
│  │    template:                         │   │
│  │      spec:                           │   │
│  │        containers:                   │   │
│  │        - name: otel-collector        │   │
│  │          image: otel/collector:0.9   │   │
│  │          ports:                      │   │
│  │          - containerPort: 4317       │   │
│  │          - containerPort: 4318       │   │
│  │          resources:                  │   │
│  │            requests:                 │   │
│  │              cpu: 200m               │   │
│  │              memory: 256Mi           │   │
│  │            limits:                   │   │
│  │              cpu: 500m               │   │
│  │              memory: 512Mi           │   │
│  └──────────────────────────────────────┘   │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│  Gateway Collectors (Deployment)            │
│  ┌──────────────────────────────────────┐  │
│  │  apiVersion: apps/v1                 │  │
│  │  kind: Deployment                    │  │
│  │  metadata:                           │  │
│  │    name: otel-gateway                │  │
│  │  spec:                               │  │
│  │    replicas: 3                       │  │
│  │    strategy:                         │  │
│  │      type: RollingUpdate             │  │
│  │      rollingUpdate:                  │  │
│  │        maxSurge: 1                   │  │
│  │        maxUnavailable: 0             │  │
│  │    template:                         │  │
│  │      spec:                           │  │
│  │        affinity:                     │  │
│  │          podAntiAffinity:            │  │
│  │            requiredDuringScheduling..│  │
│  │        containers:                   │  │
│  │        - name: otel-collector        │  │
│  │          image: otel/collector:0.9   │  │
│  │          resources:                  │  │
│  │            requests:                 │  │
│  │              cpu: 1000m              │  │
│  │              memory: 2Gi             │  │
│  │            limits:                   │  │
│  │              cpu: 2000m              │  │
│  │              memory: 4Gi             │  │
│  └──────────────────────────────────────┘  │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│  Services                                   │
│  ┌──────────────────────────────────────┐  │
│  │  Agent Service (ClusterIP)           │  │
│  │  - Headless for direct access        │  │
│  │                                      │  │
│  │  Gateway Service (LoadBalancer)      │  │
│  │  - External access                   │  │
│  │  - Load balancing                    │  │
│  └──────────────────────────────────────┘  │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│  HorizontalPodAutoscaler                    │
│  ┌──────────────────────────────────────┐  │
│  │  Gateway HPA:                        │  │
│  │  - Target: CPU 70%                   │  │
│  │  - Min: 3                            │  │
│  │  - Max: 10                           │  │
│  └──────────────────────────────────────┘  │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│  PodDisruptionBudget                        │
│  ┌──────────────────────────────────────┐  │
│  │  Gateway PDB:                        │  │
│  │  - minAvailable: 2                   │  │
│  │  (保证至少2个pod运行)                 │  │
│  └──────────────────────────────────────┘  │
└─────────────────────────────────────────────┘
```

---

## 9. 数据模型关系图

```text
┌────────────── OTLP数据模型关系图 ───────────────┐

ResourceSpans (根对象)
  │
  ├─ Resource (1个)
  │   └─ Attributes (Map<string, AnyValue>)
  │       ├─ service.name
  │       ├─ service.version
  │       ├─ deployment.environment
  │       └─ ...
  │
  └─ ScopeSpans (多个)
      │
      ├─ Scope (instrumentation library)
      │   ├─ name
      │   └─ version
      │
      └─ Spans (多个)
          │
          ├─ trace_id (16 bytes)
          ├─ span_id (8 bytes)
          ├─ parent_span_id (8 bytes, optional)
          ├─ name (string)
          ├─ kind (SpanKind enum)
          ├─ start_time_unix_nano (uint64)
          ├─ end_time_unix_nano (uint64)
          ├─ attributes (Map)
          │   ├─ http.method
          │   ├─ http.status_code
          │   └─ ...
          ├─ events (list)
          │   └─ Event
          │       ├─ time_unix_nano
          │       ├─ name
          │       └─ attributes
          ├─ links (list)
          │   └─ Link
          │       ├─ trace_id
          │       ├─ span_id
          │       └─ attributes
          └─ status
              ├─ code (OK/ERROR/UNSET)
              └─ message

关系:
Resource (1) ───< ScopeSpans (N)
ScopeSpans (1) ───< Spans (N)
Span (1) ───< Events (N)
Span (1) ───< Links (N)

Span关联:
┌─────────┐       ┌─────────┐
│ Span A  │──────>│ Span B  │
│trace_id │       │trace_id │ (same)
│span_id=1│       │span_id=2│
└─────────┘       │parent=1 │
                  └─────────┘
```

---

## 10. Context传播流程

```text
┌──────────── Context传播详细流程 ────────────┐

Service A → Service B传播:

Service A (Go):
┌────────────────────────────────────────────┐
│ func makeRequest(ctx context.Context) {    │
│                                            │
│   // 1. 创建Span                           │
│   ctx, span := tracer.Start(ctx, "req")    │
│   defer span.End()                         │
│                                            │
│   // 2. 创建HTTP请求                       │
│   req, _ := http.NewRequestWithContext(   │
│       ctx, "GET", url, nil)               │
│                                            │
│   // 3. 注入Context到Headers               │
│   propagator.Inject(ctx,                  │
│       propagation.HeaderCarrier(          │
│           req.Header))                     │
│                                            │
│   // req.Header现在包含:                    │
│   // traceparent: 00-4bf92f...-001-01      │
│   // tracestate: ...                       │
│   // baggage: key1=value1                  │
│                                            │
│   // 4. 发送请求                            │
│   client.Do(req)                           │
│ }                                          │
└────────────────────────────────────────────┘
         │
         │ HTTP Request
         │ Headers:
         │ - traceparent
         │ - tracestate
         │ - baggage
         │
         ▼
Service B (Python):
┌────────────────────────────────────────────┐
│ @app.route('/api')                         │
│ def handler():                             │
│{                                           │
│   // 1. 提取Context从Headers                │
│   ctx = extract(request.headers)           │
│                                            │
│   // ctx现在包含:                           │
│   // - trace_id (from traceparent)         │
│   // - span_id (from traceparent)          │
│   // - baggage                             │
│                                            │
│   // 2. 创建Span (自动关联父Span)           │
│   with tracer.start_as_current_span(       │
│       "handler", context=ctx):             │
│                                            │
│       // 3. 业务逻辑                        │
│       result = process()                   │
│                                            │
│       return result                        │
│ }                                          │
└────────────────────────────────────────────┘

结果Trace:
┌─────────────────────────────────────┐
│ Trace: 4bf92f...                    │
│                                     │
│ Span 1 (Service A, Go)              │
│ ├─ span_id: 001                     │
│ ├─ parent_id: null                  │
│ └─ duration: 150ms                  │
│     │                               │
│     └─ Span 2 (Service B, Python)   │
│        ├─ span_id: 002              │
│        ├─ parent_id: 001            │
│        └─ duration: 100ms           │
└─────────────────────────────────────┘

W3C Trace Context Format:
┌──────────────────────────────────────────┐
│ traceparent:                             │
│ 00-4bf92f3577b34da6a3ce929d0e0e4736-     │
│    00f067aa0ba902b7-01                   │
│    │  │                │           │     │
│    │  │                │           └─ flags
│    │  │                └─ parent_id      │
│    │  └─ trace_id                        │
│    └─ version                            │
└──────────────────────────────────────────┘
```

---

**文档状态**: ✅ 完成  
**审核状态**: 待审核  
**用途**: 架构设计参考、技术分享、文档说明

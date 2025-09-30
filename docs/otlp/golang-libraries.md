# Golang × OTLP 开源库选型与成熟度

结合 2025 年的社区现状，推荐与评估如下生态组件（以稳定性与维护度为先）：

## 目录

- [Golang × OTLP 开源库选型与成熟度](#golang--otlp-开源库选型与成熟度)
  - [目录](#目录)
  - [1. 应用侧 SDK](#1-应用侧-sdk)
    - [核心库（生产级）](#核心库生产级)
    - [Exporters（OTLP协议）](#exportersotlp协议)
    - [性能特性](#性能特性)
  - [2. 集成中间件](#2-集成中间件)
    - [HTTP中间件](#http中间件)
    - [gRPC中间件](#grpc中间件)
    - [数据库集成](#数据库集成)
    - [消息队列](#消息队列)
  - [3. Collector 与处理器](#3-collector-与处理器)
    - [官方Collector](#官方collector)
    - [核心处理器](#核心处理器)
    - [OTTL处理器（2025年v1.0稳定）](#ottl处理器2025年v10稳定)
    - [Profiling支持](#profiling支持)
  - [4. 控制平面](#4-控制平面)
    - [OPAMP（Open Agent Management Protocol v1.0）](#opampopen-agent-management-protocol-v10)
    - [Kubernetes集成](#kubernetes集成)
    - [控制面实现](#控制面实现)
  - [5. 观测后端](#5-观测后端)
    - [开源方案](#开源方案)
    - [云服务](#云服务)
  - [6. 选型准则](#6-选型准则)
    - [稳定性要求](#稳定性要求)
    - [功能特性](#功能特性)
    - [集成能力](#集成能力)

## 1. 应用侧 SDK

### 核心库（生产级）

- **`go.opentelemetry.io/otel` v1.28.0**：官方主线，Trace/Metrics/Logs 三支柱对齐
- **`go.opentelemetry.io/otel/sdk` v1.28.0**：SDK实现，支持批处理、重试、资源管理
- **`go.opentelemetry.io/otel/semconv/v1.26.0`**：语义约定，包含HTTP、DB、RPC、云原生等标签

### Exporters（OTLP协议）

- **`go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc`**：gRPC Trace导出器
- **`go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc`**：gRPC Metrics导出器
- **`go.opentelemetry.io/otel/exporters/otlp/otlplog/otlploggrpc`**：gRPC Logs导出器（实验性）

### 性能特性

- **批处理**：自动批量发送，减少网络开销
- **重试机制**：指数退避，支持自定义重试策略
- **背压控制**：队列满时自动丢弃或阻塞
- **资源管理**：自动资源发现和标签注入

## 2. 集成中间件

### HTTP中间件

- **`go.opentelemetry.io/contrib/instrumentation/net/http/otelhttp`**：HTTP客户端/服务端自动追踪
- **特性**：自动Span创建、请求/响应大小记录、错误标记

### gRPC中间件

- **`go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc`**：gRPC客户端/服务端自动追踪
- **特性**：方法名追踪、状态码记录、流式RPC支持

### 数据库集成

- **`go.opentelemetry.io/contrib/instrumentation/database/sql/otelsql`**：SQL数据库自动追踪
- **特性**：查询语句记录、连接池监控、事务追踪

### 消息队列

- **`go.opentelemetry.io/contrib/instrumentation/github.com/Shopify/sarama/otelsarama`**：Kafka客户端追踪
- **特性**：消息生产/消费追踪、分区信息记录

## 3. Collector 与处理器

### 官方Collector

- **`opentelemetry-collector`**：官方核心Collector，支持OTLP接收和转发
- **`opentelemetry-collector-contrib`**：扩展组件集合，包含各种receivers/processors/exporters

### 核心处理器

- **`batch`**：批处理处理器，优化网络传输效率
- **`memory_limiter`**：内存限制器，防止OOM
- **`attributes`**：属性处理器，添加/删除/修改属性
- **`filter`**：过滤器，基于条件过滤数据
- **`routing`**：路由器，基于属性路由到不同exporter

### OTTL处理器（2025年v1.0稳定）

- **`transform`**：OTTL语言处理器，支持声明式数据转换
- **语法特性**：条件过滤、属性操作、路由规则
- **性能**：字节码+SIMD优化，单核吞吐300k span/s

### Profiling支持

- **`profilingreceiver`**：eBPF性能分析接收器
- **导出器**：Grafana Phlare、Pyroscope、Elastic Universal Profiling
- **格式**：pprof.proto + OTLP Resource语义

## 4. 控制平面

### OPAMP（Open Agent Management Protocol v1.0）

- **`opamp-go`**：官方Go实现，用于远程配置/证书/插件分发
- **核心功能**：
  - 远程配置下发（YAML、OTTL规则）
  - mTLS证书自动轮换
  - 二进制升级包分发
  - WASM插件热更新
- **安全特性**：哈希校验、数字签名、灰度发布

### Kubernetes集成

- **`opamp-operator`**：K8s CRD方式管理Sidecar/DaemonSet
- **特性**：声明式配置、自动扩缩容、健康检查

### 控制面实现

- **Server端**：配置管理、规则引擎、监控面板
- **Agent端**：配置接收、热更新、状态上报
- **协议**：gRPC双向流，支持实时配置推送

## 5. 观测后端

### 开源方案

- **Trace**：Jaeger、Tempo、Zipkin
- **Metrics**：Prometheus、Mimir、Thanos
- **Logs**：Loki、Elasticsearch、ClickHouse
- **Profiles**：Grafana Phlare、Pyroscope、Elastic Universal Profiling

### 云服务

- **AWS**：X-Ray、CloudWatch、OpenSearch
- **Google Cloud**：Cloud Trace、Cloud Monitoring、Cloud Logging
- **Azure**：Application Insights、Monitor、Log Analytics

## 6. 选型准则

### 稳定性要求

- **版本兼容**：与Go 1.25.1和OTLP v1.3兼容
- **维护活跃**：社区活跃，定期更新
- **生产验证**：大规模生产环境验证

### 功能特性

- **语义约定**：与semconv v1.26.0对齐
- **性能优化**：支持批处理、压缩、重试
- **可配置性**：资源/标签/采样率可配置
- **扩展性**：支持OTTL/OPAMP集成

### 集成能力

- **中间件支持**：HTTP、gRPC、数据库自动追踪
- **容器化**：Kubernetes、Docker支持
- **云原生**：Service Mesh、微服务架构支持

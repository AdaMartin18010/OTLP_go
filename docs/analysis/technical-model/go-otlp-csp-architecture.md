# Go × OTLP × CSP 技术架构与分布式设计

本文整合 Go 1.25.1 的 CSP 编程模型与 OTLP 的语义/传输，为服务与数据平面提供端到端设计蓝图。

## 目录

- [Go × OTLP × CSP 技术架构与分布式设计](#go--otlp--csp-技术架构与分布式设计)
  - [目录](#目录)
  - [1. 端侧（应用）](#1-端侧应用)
  - [2. 采集与中枢（Collector）](#2-采集与中枢collector)
  - [3. 控制平面（OPAMP）](#3-控制平面opamp)
  - [4. 观测到控制的闭环](#4-观测到控制的闭环)
  - [5. 分布式模式库](#5-分布式模式库)
  - [6. 指标建议](#6-指标建议)
  - [7. 实施路线](#7-实施路线)

## 1. 端侧（应用）

- SDK：`go.opentelemetry.io/otel`、`go.opentelemetry.io/otel/sdk`、`go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlpmetric`。
- 结构：HTTP/gRPC 中间件注入 Trace；业务层以通道和工作池组织，指标对齐资源语义，日志结构化携带 trace 关联键。
- 性能：批处理、限频、并发安全队列；Exporter 与业务解耦（非阻塞导出）。

## 2. 采集与中枢（Collector）

- Receiver：`otlp`/`prometheus`/`profiling`；
- Processor：`batch`、`transform`（OTTL）、`attributes`、`routing`、`filter`；
- Exporter：`logging`、`otlp`、`kafka`、`prometheusremotewrite`、`s3`。

## 3. 控制平面（OPAMP）

- 能力：远程分发配置、OTTL 规则、证书与插件；
- 策略：标签、权重、回滚窗口；
- 安全：mTLS、签名、哈希。

## 4. 观测到控制的闭环

1) 应用产生 Trace/Metrics/Logs →
2) Collector 执行 OTTL（脱敏/降维/路由）→
3) 后端分析产出阈值/规则 →
4) OPAMP 下发新配置到边缘 →
5) 应用/Agent 即时生效（毫秒级）。

## 5. 分布式模式库

- 请求拓扑：入口网关 → 服务 A/B/C → 存储；跨服务传播 W3C TraceContext。
- 异常控制：超时、重试、熔断、限流，以 CSP 流水线和 select 实现；
- 资源治理：按 `service.*`/`k8s.*` 聚类分析与容量规划。

## 6. 指标建议

- 延迟：直方图（请求/阶段/队列）；
- 资源：CPU/内存/GC/协程数；
- 流水线：通道长度、丢弃率、重试计数；
- 业务：QPS、成功率、SLA 违约数。

## 7. 实施路线

- v1：打通端侧 SDK 与 Collector，产出基础四支柱；
- v2：引入 OTTL 统一过滤与路由；
- v3：接入 OPAMP 完成动态调参与规则闭环；
- v4：接入 eBPF Profiling，完成第四支柱。

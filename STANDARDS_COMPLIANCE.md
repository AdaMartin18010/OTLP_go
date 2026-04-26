# 标准合规性声明 (Standards Compliance)

本文档声明 OTLP_go 项目遵循的权威标准及其合规状态。文中使用 [RFC 2119](https://tools.ietf.org/html/rfc2119) / [BCP 14](https://tools.ietf.org/html/bcp14) 关键词（MUST, MUST NOT, SHOULD, SHOULD NOT, MAY, RECOMMENDED, REQUIRED）以明确各项要求的级别。

---

## 1. 遵循标准清单

| 标准名称 | 版本/基线 | 强制级别 | 引用地址 |
|---------|----------|---------|---------|
| OpenTelemetry Specification | v1.42.0 | MUST | `https://opentelemetry.io/docs/specs/otel/` |
| OTLP Protocol Specification | v1.10.0 | MUST | `https://opentelemetry.io/docs/specs/otlp/` |
| W3C Trace Context | Level 2 | MUST | `https://www.w3.org/TR/trace-context-2/` |
| W3C Baggage | Level 1 | SHOULD | `https://www.w3.org/TR/baggage/` |
| Semantic Conventions | v1.28.0+ | MUST | `https://opentelemetry.io/docs/specs/semconv/` |
| OpenTelemetry Go SDK/API | v1.42.0 | SHOULD | `https://pkg.go.dev/go.opentelemetry.io/otel` |
| OpenTelemetry Collector Spec | v0.112.0+ | SHOULD | `https://opentelemetry.io/docs/collector/` |
| IETF RFC 2119 / RFC 8174 | BCP 14 | MUST | `https://tools.ietf.org/html/rfc2119` |
| Protobuf proto3 | v3 | MUST | `https://protobuf.dev/` |
| CNCF Project Governance | 最新版 | SHOULD | `https://www.cncf.io/` |

---

## 2. 模块合规状态

| 模块 | 稳定性 | 合规状态 | 说明 |
|------|--------|---------|------|
| `pkg/otel` | Beta | 部分合规 | MUST 实现 Trace/Metric SDK；SHOULD 实现 Log SDK 完整分层 |
| `pkg/types` | Stable | 合规 | MUST 保持与 OpenTelemetry Attribute 类型兼容 |
| `pkg/logs` | Beta | 部分合规 | MUST 对齐 Logs SDK API 分层；MAY 在后续版本补充 EventName |
| `pkg/resource` | Stable | 合规 | MUST 实现 Resource 检测规范；SHOULD 扩展云提供商检测 |
| `pkg/config` | Stable | 合规 | MUST 支持环境变量与文件配置；MAY 支持动态热加载 |
| `pkg/concurrency` | Stable | 扩展 | 纯 Go 工程实践，非 OTel 核心规范范畴 |
| `pkg/errors` | Stable | 扩展 | Circuit Breaker 为工程增强，SHOULD 遵循错误处理最佳实践 |
| `pkg/pool` | Stable | 扩展 | 对象池为性能优化组件，MUST 保证线程安全 |
| `pkg/profiling` | Alpha | 开发中 | Profiles 信号尚处 Development 阶段，MAY 随规范演进调整 |
| `pkg/performance` | Beta | 扩展 | 性能指标采集为工程增强，SHOULD 对齐 Semantic Conventions |
| `pkg/propagation` | Beta | 部分合规 | MUST 实现 W3C Trace Context Level 2；SHOULD 实现 Baggage 传播 |
| `pkg/semconv` | Beta | 部分合规 | MUST 使用官方语义约定常量；MUST NOT 硬编码字符串 |
| `pkg/collector` | Development | 部分合规 | Collector 组件随官方规范迭代，MAY 存在重大变更 |
| `pkg/security` | Beta | 扩展 | 安全审计为工程增强，SHOULD 遵循 OWASP 与 OTel 安全指南 |
| `pkg/shutdown` | Stable | 扩展 | 优雅关闭为工程增强，MUST 保证数据不丢失 |
| `pkg/automation` | Alpha | 实验性 | 自动化配置为项目创新，MAY 随社区反馈调整 |
| `pkg/ebpf` | Development | 实验性 | eBPF 零侵入追踪为前沿探索，MUST NOT 破坏现有 Trace API |
| `pkg/context` | Beta | 部分合规 | MUST 实现 W3C Baggage 规范；SHOULD 支持上下文传播器 |
| `pkg/runtime` | Beta | 扩展 | 运行时自省为 Go 特定增强，SHOULD 对齐 Runtime Metrics 约定 |
| `pkg/testing` | Stable | 扩展 | 测试工具为工程支持，MUST 兼容标准 testing 包 |
| `pkg/options` | Stable | 扩展 | 函数式选项为 Go 惯用法，SHOULD 保持向后兼容 |

---

## 3. 不合规项说明与计划

### 3.1 P0 — 必须补齐（MUST）

| 不合规项 | 规范条款 | 计划 | 目标版本 |
|---------|---------|------|---------|
| OTLP/HTTP JSON 编码 | OTLP Spec §2.2.2 | 实现 JSON Protobuf Encoding | v0.5.0 |
| W3C Trace Context Level 2 random-trace-id flag | W3C §3.2.2 | 修改 TraceID 生成器 | v0.4.0 |
| Partial Success 处理 | OTLP Spec §3.2 | 实现 rejected_* 字段解析与重试 | v0.5.0 |
| Metrics View 机制 | OTel Spec Metrics SDK §View | 引入 MetricReader + View | v0.6.0 |
| Exponential Histogram | OTel Spec Metrics Data Model | 支持 ExponentialHistogram 聚合 | v0.6.0 |

### 3.2 P1 — 建议补齐（SHOULD）

| 不合规项 | 规范条款 | 计划 | 目标版本 |
|---------|---------|------|---------|
| Prometheus Exporter | OpenMetrics | 实现 Prometheus 格式导出 | v0.7.0 |
| Collector Connector | Collector Spec §Connectors | 实现 Span-to-Metric 转换 | v0.7.0 |
| OpenCensus Bridge | OTel Spec §Compatibility | 提供 OpenCensus 迁移桥接 | v0.8.0 |

### 3.3 P2 — 可选补齐（MAY）

| 不合规项 | 规范条款 | 计划 | 目标版本 |
|---------|---------|------|---------|
| FaaS Semantic Conventions | SemConv §FaaS | 按需添加函数计算属性 | v0.8.0 |
| CloudEvents Semantic Conventions | SemConv §CloudEvents | 按需添加云事件属性 | v0.8.0 |

---

## 4. RFC 2119 关键词使用约定

项目文档和代码注释中使用以下关键词时，其含义严格遵循 [RFC 2119](https://tools.ietf.org/html/rfc2119)：

- **MUST / REQUIRED / SHALL**：绝对要求，不遵守将导致标准互操作性失败。
- **MUST NOT / SHALL NOT**：绝对禁止。
- **SHOULD / RECOMMENDED**：建议，有充分理由时可偏离，但必须理解其后果。
- **SHOULD NOT / NOT RECOMMENDED**：不建议，有充分理由时可偏离。
- **MAY / OPTIONAL**：可选，完全由实现者决定。

所有包含规范性要求的文档（如 `docs/` 下的设计文档和本文件）必须使用大写形式（`MUST`, `SHOULD`, `MAY` 等）以表明其为 BCP 14 关键词。

---

*文档版本: 2026-04-26*
*基准规范: OpenTelemetry Specification v1.42.0*

# OTLP_go 项目 — 国际标准对齐路线图 (Standard Alignment Roadmap)

> **版本**: v1.0.0
> **日期**: 2026-04-26
> **目标**: 将项目整体合规度从 ~53% 提升至 ≥90%（核心规范域 ≥95%）
> **对齐基准**: OpenTelemetry Specification (2026-Q1), W3C Trace Context Level 2, OTLP v1.10.0, Semantic Conventions v1.28.0

---

## 一、战略阶段规划

```
Phase 1: 基础设施对齐（P0基石）    ████████████  4周  → 合规度 53% → 70%
Phase 2: 信号深度对齐（P0核心）    ████████████  6周  → 合规度 70% → 85%
Phase 3: 语义约定全覆盖（P1扩展）  ████████████  6周  → 合规度 85% → 92%
Phase 4: Collector生态完善（P1）   ████████████  4周  → 合规度 92% → 95%
Phase 5: 前瞻探索与社区回馈        ████████████  持续  → 巩固差异化优势
```

---

## 二、Phase 1: 基础设施对齐（4周）— 合规度目标 70%

### 2.1 任务 P1-OTLP-HTTP: OTLP/HTTP 传输层完整实现

**负责人**: Core Protocol Team
**依赖**: `pkg/otel/exporter` 重构
**验收标准**: 通过 OTLP Compatibility Test Suite

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P1-OTLP-HTTP-01` 实现 Binary Protobuf Exporter | 3d | `Content-Type: application/x-protobuf`, 默认端口4318 | OTLP Spec §OTLP/HTTP |
| `P1-OTLP-HTTP-02` 实现 JSON Protobuf Exporter | 2d | `Content-Type: application/json`, 字段名保持camelCase | OTLP Spec §JSON Encoding |
| `P1-OTLP-HTTP-03` URL路径规范化 | 1d | `/v1/traces`, `/v1/metrics`, `/v1/logs`, `/v1development/profiles` | OTLP Spec §URL Path |
| `P1-OTLP-HTTP-04` CORS预检支持 | 2d | `OPTIONS`预检响应，`Access-Control-*`头部 | OTLP Spec §CORS |
| `P1-OTLP-HTTP-05` 压缩协商 | 1d | `gzip`, `none`，通过`Content-Encoding`协商 | OTLP Spec §Compression |
| `P1-OTLP-HTTP-06` HTTP状态码映射 | 1d | 429/502/503/504 → 可重试, 400/404 → 不可重试 | OTLP Spec §Retry |
| `P1-OTLP-HTTP-07` Partial Success解析 | 2d | 解析`rejected_*`字段，触发告警/补偿导出 | OTLP Spec §Partial Success |
| `P1-OTLP-HTTP-08` Throttling感知 | 2d | 解析`Retry-After`, gRPC `RetryInfo`，自适应退避 | OTLP Spec §Throttling |
| `P1-OTLP-HTTP-09` 多目的地导出架构 | 3d | ExporterManager支持多endpoint并行导出，独立失败处理 | OTLP Spec §Multi-Destination |
| `P1-OTLP-HTTP-10` 兼容性测试套件 | 2d | 使用`opentelemetry-proto`的示例消息验证编解码 | - |

**里程碑**: `pkg/otel/exporter/http` 包通过所有OTLP/HTTP规范测试

---

### 2.2 任务 P1-W3C-L2: W3C Trace Context Level 2 合规

**负责人**: Propagation Team
**依赖**: `pkg/otel/propagation`

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P1-W3C-L2-01` random-trace-id flag支持 | 2d | `trace-flags |= 0x02`，确保trace-id[7:16]随机性 | W3C TC2 §4.1 |
| `P1-W3C-L2-02` tracestate严格验证 | 2d | 32条目上限，键256字符限制，非法字符过滤 | W3C TC2 §3.3 |
| `P1-W3C-L2-03` tracestate截断策略 | 1d | 超限时优先保留`vendor@key`格式键 | W3C TC2 §3.3.3 |
| `P1-W3C-L2-04` 隐私安全检查器 | 2d | 扫描traceparent/tracestate中的PII模式，告警拦截 | W3C TC2 §6 |
| `P1-W3C-L2-05` Level 2兼容性测试 | 1d | 通过W3C官方测试向量 | W3C TC Test Suite |

**里程碑**: `pkg/otel/propagation` 通过W3C Trace Context Level 2全部测试用例

---

### 2.3 任务 P1-RFC2119: 文档规范化（BCP 14合规）

**负责人**: Documentation Team
**范围**: 全部`docs/`目录 + `pkg/`包级文档

| 子任务 | 工时 | 技术要点 |
|--------|------|---------|
| `P1-RFC2119-01` 建立术语表 | 2d | Glossary文档，统一Trace/Span/Resource/InstrumentationScope等术语 |
| `P1-RFC2119-02` 要求级别标注 | 3d | 所有规范相关文档使用**MUST**/**SHOULD**/**MAY**/**MUST NOT**大写格式 |
| `P1-RFC2119-03` 稳定性标注 | 2d | 每个模块/包顶部标注`[Stability: Stable|Beta|Alpha|Development]` |
| `P1-RFC2119-04` 版本兼容性声明 | 1d | 明确各模块的MAJOR.MINOR兼容性承诺 |

**里程碑**: 全部技术文档通过RFC 2119合规性审查

---

## 三、Phase 2: 信号深度对齐（6周）— 合规度目标 85%

### 3.1 任务 P2-METRICS: Metrics SDK架构重构

**负责人**: Metrics Team
**风险**: 高（涉及API变更）
**向后兼容**: 通过deprecated标记保障过渡期

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P2-METRICS-01` MetricReader抽象 | 4d | `MetricReader`接口，`RegisterProducer`, `ForceFlush`, `Shutdown` | Metrics SDK §Reader |
| `P2-METRICS-02` Pull型Reader | 2d | `ManualReader`（测试用）, `PeriodicExportingReader`（定时推送） | Metrics SDK §Pull |
| `P2-METRICS-03` View机制 | 5d | `View`配置：属性过滤、聚合选择、桶边界自定义、instrument重命名 | Metrics SDK §View |
| `P2-METRICS-04` Aggregation类型全集 | 4d | `DropAggregation`, `SumAggregation`, `LastValueAggregation`, `ExplicitBucketHistogramAggregation`, `ExponentialHistogramAggregation` | Metrics SDK §Aggregation |
| `P2-METRICS-05` Temporality配置 | 3d | `DeltaTemporalitySelector`, `CumulativeTemporalitySelector`, 按Exporter配置 | Metrics SDK §Temporality |
| `P2-METRICS-06` ExponentialHistogram | 4d | 基于`base=2^(2^-scale)`的指数桶，scale范围-10~20 | Metrics Data Model §ExponentialHistogram |
| `P2-METRICS-07` Prometheus兼容导出 | 3d | 实现`PrometheusExporter`，支持`target_info`、`otel_scope_info` | Compatibility §Prometheus |

**里程碑**: Metrics模块通过OpenTelemetry Metrics SDK Compliance Test

---

### 3.2 任务 P2-LOGS: Logs分层与EventName

**负责人**: Logs Team

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P2-LOGS-01` Logs API层抽象 | 3d | `LoggerProvider`, `Logger`, `LogRecord` 接口定义（面向桥接器） | Logs API Spec |
| `P2-LOGS-02` Logs SDK重构 | 4d | `SimpleLogRecordProcessor`, `BatchLogRecordProcessor`, `LogRecordExporter` | Logs SDK Spec |
| `P2-LOGS-03` EventName字段 | 1d | `LogRecord.EventName string`，与Semantic Conventions事件名对接 | Logs Data Model |
| `P2-LOGS-04` SeverityNumber严格验证 | 1d | 入参校验1-24范围，非法值拒绝或降级 | Logs Data Model §Severity |
| `P2-LOGS-05` Bridge示例 | 2d | 为`log/slog`, `logrus`, `zap`提供Appender桥接示例 | Logs API §Bridge |

**里程碑**: Logs模块通过分层测试，Bridge示例可运行

---

### 3.3 任务 P2-TRACES: Trace完善与Partial Success

**负责人**: Trace Team

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P2-TRACES-01` trace.IDGenerator接口 | 2d | `IDGenerator`接口，`NewIDs()`, `NewSpanID()`，支持随机与顺序模式 | Go SDK `trace` pkg |
| `P2-TRACES-02` Partial Success处理器 | 2d | 在`SpanExporter`基类中统一处理`ExportTraceServiceResponse.PartialSuccess` | OTLP Spec §Partial Success |
| `P2-TRACES-03` 导出失败补偿队列 | 3d | 失败span进入补偿队列，定时重试，超期丢弃+告警 | 可靠性最佳实践 |

**里程碑**: Trace导出可靠性达到99.9%（测试模拟Partial Success场景）

---

## 四、Phase 3: 语义约定全覆盖（6周）— 合规度目标 92%

### 4.1 任务 P3-SEMCONV: Semantic Conventions代码生成与实现

**负责人**: Semantic Conventions Team
**策略**: 采用代码生成（基于`semantic-conventions`仓库YAML定义）

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P3-SEMCONV-01` 语义约定代码生成器 | 5d | 解析`semantic-conventions`仓库YAML，生成Go常量包 | semconv仓库 |
| `P3-SEMCONV-02` HTTP语义约定 | 3d | `http.request.method`, `http.response.status_code`, `http.route`, `server.address`, `server.port` | SemConv §HTTP |
| `P3-SEMCONV-03` Database语义约定 | 3d | `db.system`, `db.operation`, `db.sql.table`, `db.query.text` | SemConv §Database |
| `P3-SEMCONV-04` Messaging语义约定 | 3d | `messaging.system`, `messaging.destination.name`, `messaging.operation.type` | SemConv §Messaging |
| `P3-SEMCONV-05` RPC语义约定 | 2d | `rpc.system`, `rpc.service`, `rpc.method`, `rpc.grpc.status_code` | SemConv §RPC |
| `P3-SEMCONV-06` GenAI语义约定 | 4d | `gen_ai.system`, `gen_ai.request.model`, `gen_ai.usage.input_tokens`, `gen_ai.usage.output_tokens` | SemConv §GenAI |
| `P3-SEMCONV-07` 系统Metrics约定 | 3d | `system.cpu.time`, `system.memory.usage`, `system.disk.io`, `system.network.io` + UCUM单位 | SemConv §System |
| `P3-SEMCONV-08` Resource约定完善 | 2d | `service.namespace`, `service.instance.id`, `deployment.environment` | SemConv §Resource |
| `P3-SEMCONV-09` Cloud Provider检测器 | 3d | AWS EC2/ECS/EKS, Azure VM/AKS, GCP GCE/GKE 元数据检测 | SemConv §Cloud Providers |
| `P3-SEMCONV-10` 属性命名静态检查 | 2d | Linter规则：禁止硬编码属性字符串，强制使用`semconv`常量 | 内部规范 |

**里程碑**: `pkg/semconv` 包生成并覆盖全部P0/P1语义约定领域

---

## 五、Phase 4: Collector生态完善（4周）— 合规度目标 95%

### 5.1 任务 P4-COLLECTOR: Collector组件扩展

**负责人**: Collector Team

| 子任务 | 工时 | 技术要点 | 引用标准 |
|--------|------|---------|---------|
| `P4-COLLECTOR-01` Connector框架 | 4d | `Connector`接口，跨pipeline数据流转，示例：SpanCount Connector | Collector Spec §Connectors |
| `P4-COLLECTOR-02` Health Check Extension | 2d | `/health`端点， readiness/liveness探针 | Collector Spec §Extensions |
| `P4-COLLECTOR-03` pprof Extension | 1d | 集成Go pprof HTTP端点 | Collector Spec §Extensions |
| `P4-COLLECTOR-04` Config Provider框架 | 3d | `file://`, `env://`, `yaml://`, `http://`, `https://`配置加载 | Collector Spec §Providers |
| `P4-COLLECTOR-05` 配置验证命令 | 2d | `validate`子命令，配置文件语法与语义校验 | Collector Spec §Commands |
| `P4-COLLECTOR-06` TLS/mTLS完整实现 | 2d | `cert_file`, `key_file`, `ca_file`, `client_ca_file`, `reload_interval` | Collector Spec §Security |
| `P4-COLLECTOR-07` OIDC认证Extension | 3d | OIDC token验证，Audience/Scope校验 | Collector Spec §Auth |

**里程碑**: `pkg/collector` 从预留状态升级为功能完整的Collector SDK

---

## 六、Phase 5: 前瞻探索与社区回馈（持续）

### 6.1 保持差异化优势

| 主题 | 行动 | 目标 |
|------|------|------|
| **eBPF零侵入** | 跟踪OTel eBPF Profiler标准演进，贡献Go运行时探测方案 | 成为OTel eBPF Go子项目参考实现 |
| **OTel Arrow** | 推进Arrow编码从OTEP进入主规范，贡献Go Arrow exporter | Arrow信号标准化贡献者 |
| **AI/ML可观测性** | 基于GenAI语义约定，扩展LLM调用链自动追踪库 | 社区首个完整Go LLM Instrumentation库 |
| **CSP并发模式** | 提取通用模式为独立开源模块 | Go并发模式参考实现 |

### 6.2 社区贡献计划

| 贡献目标 | 形式 | 时间线 |
|---------|------|--------|
| OTLP/HTTP Go Exporter | PR至`opentelemetry-go` | Phase 1完成后 |
| ExponentialHistogram实现 | PR至`opentelemetry-go` | Phase 2完成后 |
| GenAI Instrumentation库 | 新建`opentelemetry-go-contrib`模块 | Phase 3完成后 |
| eBPF Go Probe规范 | OTEP提案 | Phase 4完成后 |

---

## 七、质量保障体系

### 7.1 自动化合规检查

```yaml
# .github/workflows/compliance-check.yml
合规检查清单:
  - Semantic Conventions常量引用检查 (semconv-lint)
  - RFC 2119关键词格式检查 (bcp14-lint)
  - W3C Trace Context测试向量执行 (w3c-tc-test)
  - OTLP兼容性测试套件 (otlp-compat-test)
  - Metrics SDK合规测试 (metrics-sdk-compliance)
  - OpenTelemetry Go API兼容性 (api-compatibility)
```

### 7.2 文档同步机制

| 触发条件 | 动作 | 负责人 |
|---------|------|--------|
| OpenTelemetry规范Release | 自动创建差异分析Issue | CI Bot |
| Semantic Conventions新版本 | 触发代码生成器更新 | SemConv Team |
| W3C标准更新 | 评估影响，创建对齐任务 | Architecture Team |
| 每周 | 扫描`opentelemetry-specification`仓库PR | Compliance Officer |

### 7.3 验收测试矩阵

| 测试类别 | 工具/框架 | 通过标准 |
|---------|----------|---------|
| OTLP/gRPC兼容性 | `opentelemetry-proto`示例消息 | 100%编解码通过 |
| OTLP/HTTP兼容性 | 自建Mock Collector + 官方验证 | 所有HTTP状态码场景通过 |
| W3C Trace Context | W3C官方测试向量 | Level 1 & Level 2全通过 |
| Metrics SDK | `opentelemetry-go`的`sdk/metric`测试 | 覆盖率≥90% |
| Semantic Conventions | 代码生成器 diff 检查 | 与官方YAML无遗漏 |
| 端到端 | Docker Compose完整链路 | Traces+Metrics+Logs全链路可观测 |

---

## 八、资源与依赖

### 8.1 人力分配建议

| 团队 | Phase 1 | Phase 2 | Phase 3 | Phase 4 | Phase 5 |
|------|---------|---------|---------|---------|---------|
| Core Protocol (3人) | ████████ | ████ | ██ | █ | 持续 |
| Trace/Propagation (2人) | ████ | ██████ | ██ | █ | 持续 |
| Metrics (2人) | ██ | ████████ | ████ | █ | 持续 |
| Logs (1人) | █ | ██████ | ████ | █ | 持续 |
| SemConv/Resource (2人) | █ | ██ | ████████ | ██ | 持续 |
| Collector (2人) | ██ | █ | ██ | ████████ | 持续 |
| Documentation (1人) | ████ | ████ | ████ | ████ | 持续 |
| QA/Compliance (1人) | ██ | ████ | ████ | ████ | 持续 |

### 8.2 外部依赖

| 依赖项 | 用途 | 获取方式 |
|--------|------|---------|
| `open-telemetry/opentelemetry-proto` | OTLP消息定义与测试向量 | Git submodule |
| `open-telemetry/semantic-conventions` | YAML定义与代码生成源 | Git submodule |
| W3C Trace Context Test Suite | 传播器合规测试 | npm包/直接引用 |
| `opentelemetry-go` compliance tests | SDK行为一致性验证 | Go module test import |

---

## 九、关键里程碑时间表

| 里程碑 | 日期 | 交付物 | 合规度 |
|--------|------|--------|--------|
| M1: HTTP Exporter GA | 2026-05-24 | `pkg/otel/exporter/http` + 完整测试 | 70% |
| M2: W3C Level 2合规 | 2026-05-31 | 传播器通过全部W3C测试 | 72% |
| M3: Metrics SDK重构完成 | 2026-06-21 | View + Reader + ExponentialHistogram | 80% |
| M4: Logs分层完成 | 2026-06-28 | API/SDK分离 + Bridge示例 | 83% |
| M5: Semantic Conventions生成 | 2026-07-19 | `pkg/semconv`覆盖20+领域 | 90% |
| M6: Collector生态可用 | 2026-08-02 | Connectors + Extensions + Config Providers | 93% |
| M7: 全面合规审计 | 2026-08-16 | 第三方合规性评审报告 | ≥95% |
| M8: 社区首个贡献合并 | 2026-09-01 | `opentelemetry-go` PR merged | - |

---

## 十、成功指标 (KPIs)

| 指标 | 基线 | 目标 | 测量方式 |
|------|------|------|---------|
| 整体合规度 | 53% | ≥90% | 规范条款覆盖率检查 |
| OTLP/HTTP功能覆盖率 | 30% | 100% | 功能测试矩阵 |
| W3C TC测试通过率 | 70% | 100% | 官方测试套件 |
| Semantic Conventions覆盖 | 30% | ≥95% | 代码生成diff |
| 外部贡献PR数 | 0 | ≥4 | GitHub统计 |
| 测试覆盖率 | 94.2% | ≥95% | `go test -cover` |
| 文档RFC 2119合规 | 0% | 100% | 自动化lint |

---

*路线图版本: v1.0.0*
*下次修订: M3完成后 (2026-06-21)*
*变更日志: 见 Git 历史*

# OTLP_go 知识图谱

> **项目**: Go OTLP全栈技术研究
> **版本**: v1.0
> **日期**: 2026-04-06

---

## 1. 技术栈全景图

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Go OTLP 技术栈全景                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │    理论层    │  │    SDK层     │  │   协议层     │  │   部署层     │    │
│  │              │  │              │  │              │  │              │    │
│  │ • CSP理论    │  │ • Traces     │  │ • OTLP/gRPC  │  │ • Docker     │    │
│  │ • 形式化语义 │  │ • Metrics    │  │ • OTLP/HTTP  │  │ • Kubernetes │    │
│  │ • 分布式理论 │  │ • Logs       │  │ • Protobuf   │  │ • Collector  │    │
│  │ • eBPF原理   │  │ • Baggage    │  │ • W3C标准    │  │ • 服务网格   │    │
│  │              │  │ • Propagation│  │              │  │              │    │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘    │
│         │                 │                 │                 │            │
│         └─────────────────┴─────────────────┴─────────────────┘            │
│                                       │                                     │
│                              ┌────────┴────────┐                          │
│                              │    可观测性平台   │                          │
│                              │                 │                          │
│                              │ • Jaeger        │                          │
│                              │ • Prometheus    │                          │
│                              │ • Grafana       │                          │
│                              │ • Loki          │                          │
│                              │ • Parca         │                          │
│                              └─────────────────┘                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. 核心技术关联

### 2.1 CSP ↔ OTLP 同构关系

```
┌─────────────────────────────────────────────────────────────┐
│                    CSP ⟷ OTLP 同构映射                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   CSP Process      ⟷    Go Goroutine     ⟷   OTLP Span    │
│        │                    │                    │          │
│        ▼                    ▼                    ▼          │
│   CSP Event        ⟷    Channel Op       ⟷   Span Event   │
│                                                             │
│   CSP Trace        ⟷    执行序列         ⟷   Trace Tree   │
│                                                             │
│   External Choice  ⟷    Select语句       ⟷   Span Fork    │
│                                                             │
│   Parallel Comp.   ⟷    Goroutine并发    ⟷   Sibling Span │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 传播格式对比

```
┌─────────────────────────────────────────────────────────────┐
│                    传播格式对比                             │
├──────────────┬──────────────┬──────────────┬───────────────┤
│    特性      │   W3C        │    B3        │   Jaeger      │
├──────────────┼──────────────┼──────────────┼───────────────┤
│ Header数     │ 1-2个        │ 1或5个       │ 1个           │
│ TraceID      │ 32字符       │ 16/32字符    │ 16/32字符     │
│ 可读性       │ 高           │ 中           │ 低            │
│ 生态         │ OTel官方     │ Zipkin       │ Jaeger        │
│ Baggage      │ 单独头       │ 否           │ uberctx-*     │
│ 2026推荐     │ ✅ 首选      │ ✅ 兼容      │ ⚠️ 遗留      │
└──────────────┴──────────────┴──────────────┴───────────────┘
```

### 2.3 采样策略决策树

```
┌─────────────────────────────────────────────────────────────┐
│                    采样策略选择                             │
│                                                             │
│  开始                                                        │
│    │                                                        │
│    ▼                                                        │
│  生产环境? ──否──▶ AlwaysOn (开发/测试)                     │
│    │是                                                      │
│    ▼                                                        │
│  流量 > 1000 QPS? ──否──▶ ParentBased(AlwaysOn)            │
│    │是                                                      │
│    ▼                                                        │
│  关键API? ──是──▶ NameBased(关键API全采, 其他1%)           │
│    │否                                                      │
│    ▼                                                        │
│  ParentBased(TraceIDRatioBased(0.01))  # 1%采样            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## 3. 组件依赖图

### 3.1 SDK内部依赖

```
┌─────────────────────────────────────────────────────────────┐
│                    SDK内部依赖                              │
│                                                             │
│   TracerProvider                                            │
│        │                                                    │
│   ┌────┴────┬────────┬────────┐                            │
│   ▼         ▼        ▼        ▼                            │
│   Tracer  Sampler  Resource  SpanProcessor                 │
│      │                              │                       │
│      │         ┌────────────────────┘                       │
│      │         │                                            │
│      ▼         ▼                                            │
│     Span  ──▶  Exporter                                     │
│      │                                                      │
│      ▼                                                      │
│   OTEL_EXPORTER_OTLP_ENDPOINT                               │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 3.2 完整数据流

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          完整数据流                                      │
│                                                                         │
│   Application                                                           │
│       │                                                                 │
│       ▼                                                                 │
│   ┌─────────────────────────────────────────────────────────────┐      │
│   │                     OTel SDK                                │      │
│   │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │      │
│   │  │ Traces  │  │ Metrics │  │  Logs   │  │ Baggage │        │      │
│   │  └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘        │      │
│   │       └─────────────┴─────────────┴─────────────┘          │      │
│   │                      │                                     │      │
│   │                      ▼                                     │      │
│   │              ┌───────────────┐                             │      │
│   │              │  BatchProcessor│                             │      │
│   │              └───────┬───────┘                             │      │
│   └──────────────────────┼────────────────────────────────────┘      │
│                          │                                            │
│                          ▼                                            │
│                  ┌───────────────┐                                    │
│                  │ OTLP Exporter │                                    │
│                  │  (gRPC/HTTP)  │                                    │
│                  └───────┬───────┘                                    │
│                          │                                            │
│                          ▼                                            │
│   ┌─────────────────────────────────────────────────────────────┐    │
│   │                 OpenTelemetry Collector                     │    │
│   │   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐       │    │
│   │   │ Receiver│  │ Processor│  │  OTLP   │  │ Exporter│       │    │
│   │   │  4317   │──▶│ Batch  │──▶│ Queue  │──▶│Multiple │       │    │
│   │   └─────────┘  └─────────┘  └─────────┘  └────┬────┘       │    │
│   └───────────────────────────────────────────────┼────────────┘    │
│                                                   │                  │
│           ┌──────────┬──────────┬──────────┬──────┘                  │
│           ▼          ▼          ▼          ▼                         │
│       ┌──────┐   ┌──────┐   ┌──────┐   ┌──────┐                    │
│       │Jaeger│   │Prometheus│ │Grafana│   │  S3   │                    │
│       │16686 │   │ 9090   │   │ 3000 │   │Archive│                    │
│       └──────┘   └──────┘   └──────┘   └──────┘                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 4. 学习路径推荐

### 4.1 初学者路径 (1-2周)

```
Week 1:
├── Day 1-2: [快速开始] docs/core/concurrency-patterns-csp.md
├── Day 3-4: [OTLP基础] docs/core/production-deployment-guide.md
└── Day 5-7: [实践] examples/quickstart/ + examples/complete/

Week 2:
├── Day 1-3: [SDK源码] docs/research/otel-sdk-tracerprovider-init.md
├── Day 4-5: [采样] docs/research/otel-sdk-sampling-strategies.md
└── Day 6-7: [项目实践] 集成到自己的项目
```

### 4.2 进阶路径 (3-4周)

```
Week 3:
├── [eBPF] docs/research/ebpf/ebpf-setup-guide.md
├── [eBPF] docs/research/ebpf/ebpf-uprobe-deep-dive.md
└── [实现] pkg/ebpf/ 代码实现

Week 4:
├── [传播器] docs/research/protocol/b3-propagation-implementation.md
├── [协议] docs/research/protocol/protobuf-encoding-deep-dive.md
└── [实现] pkg/propagation/ 完整实现
```

### 4.3 专家路径 (5-8周)

```
Week 5-6:
├── [Metrics] docs/research/otel-sdk-metrics-deep-dive.md
├── [Collector] docs/research/collector-architecture-analysis.md
└── [实战] examples/microservices-platform/

Week 7-8:
├── [性能] 基准测试与优化
├── [文档] docs/KNOWLEDGE_GRAPH.md
└── [总结] docs/FINAL_REPORT.md
```

---

## 5. 关键技术决策

### 5.1 传播器选择

| 场景 | 推荐 | 理由 |
|------|------|------|
| 纯OTel生态 | W3C | 官方标准，最广泛支持 |
| 与Zipkin共存 | W3C + B3 | 向后兼容 |
| 遗留Jaeger | W3C + Jaeger | 平滑迁移 |
| 最大兼容 | W3C + B3 + Jaeger | 全覆盖 |

### 5.2 采样策略决策

| 流量 | 策略 | 预期采样率 |
|------|------|-----------|
| < 100 TPS | AlwaysOn | 100% |
| 100-1000 TPS | TraceIDRatioBased(0.5) | 50% |
| 1000-10000 TPS | ParentBased(0.1) | 10% |
| > 10000 TPS | ParentBased(0.01) | 1% |

### 5.3 导出协议选择

| 优先级 | 协议 | 理由 |
|--------|------|------|
| 1 | OTLP/gRPC | 性能最佳，推荐 |
| 2 | OTLP/HTTP | 兼容性更好，防火墙友好 |
| 3 | Jaeger Thrift | 遗留系统兼容 |
| 4 | Zipkin JSON | 遗留系统兼容 |

---

## 6. 2026技术趋势

### 6.1 已标准化

- ✅ **OpenTelemetry 1.0+**: 全信号稳定
- ✅ **eBPF零侵入**: Beyla/OBI成为标准
- ✅ **W3C Trace Context**: 广泛支持
- ✅ **语义约定 v1.40**: 统一属性

### 6.2 发展中

- 🔄 **eBPF Profiling**: 持续剖析
- 🔄 **OpenTelemetry Arrow**: 高性能传输
- 🔄 **AI/ML可观测性**: 智能分析

### 6.3 本项目覆盖

```
核心技术: ████████████████████ 100%
├── OTel SDK Traces     ████ 100%
├── OTel SDK Metrics    ████ 100%
├── OTel SDK Logs       ████ 100%
├── Propagation         ████ 100%
├── eBPF Integration    ████ 100%
├── Sampling            ████ 100%
└── Collector           ████ 100%

前沿技术: ████████░░░░░░░░░░░░ 40%
├── Profiles (eBPF)     ██░░ 50%
├── Arrow OTLP          ░░░░ 0%
└── AI Observability    ░░░░ 0%
```

---

## 7. 参考资源

### 7.1 官方文档

- [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/)
- [Go SDK Documentation](https://pkg.go.dev/go.opentelemetry.io/otel)
- [OTLP Protocol](https://opentelemetry.io/docs/specs/otlp/)

### 7.2 本项目文档索引

```
docs/
├── INDEX.md                          # 文档导航
├── RESEARCH_TRACKING.md              # 进度看板
├── KNOWLEDGE_GRAPH.md                # 本文件
├── FINAL_REPORT.md                   # 项目总结
├── core/                             # 核心文档
│   ├── csp-ebpf-integration.md       # CSP与eBPF
│   ├── service-mesh-istio-linkerd.md # 服务网格
│   ├── profiling-complete-guide.md   # 性能剖析
│   ├── production-deployment-guide.md # 生产部署
│   └── concurrency-patterns-csp.md   # 并发模式
└── research/                         # 研究文档
    ├── ebpf/
    ├── otel-sdk/
    ├── protocol/
    └── architecture/
```

---

**维护**: 平台工程团队
**更新**: 2026-04-06

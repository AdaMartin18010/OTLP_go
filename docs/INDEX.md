# OTLP_go 文档导航中心

> **项目目标**: 深度掌握Go OTLP全栈技术（源码分析 + 实践验证）
> **Go版本**: 1.26.1 | **最后更新**: 2026-04-06

---

## 📚 文档结构

```
docs/
├── INDEX.md                    # 本文档：导航中心
├── RESEARCH_TRACKING.md        # 研究进度看板
├── core/                       # 核心研究文档（必读）
│   ├── csp-ebpf-integration.md
│   ├── service-mesh-istio-linkerd.md
│   ├── profiling-complete-guide.md
│   ├── production-deployment-guide.md
│   └── concurrency-patterns-csp.md
├── research/                   # 深度研究文档（进行中）
│   ├── ebpf/                   # eBPF实践研究
│   ├── otel-sdk/               # OpenTelemetry SDK源码分析
│   ├── protocol/               # OTLP协议研究
│   └── architecture/           # 架构设计研究
├── examples/                   # 示例文档
├── archive-2025.zip            # 历史文档归档
└── archive/README.md           # 归档说明
```

---

## 🎯 快速开始

### 研究者路径

#### 路径1: eBPF零侵入追踪研究

```
1. docs/core/csp-ebpf-integration.md          (理论)
2. docs/research/ebpf-setup-guide.md          (环境)
3. docs/research/ebpf-uprobe-deep-dive.md     (实践)
4. pkg/ebpf/                                  (代码)
5. examples/ebpf-uprobe/                      (演示)
```

#### 路径2: OpenTelemetry SDK源码研究

```
1. docs/research/otel-sdk-tracerprovider-init.md   (启动流程)
2. docs/research/otel-sdk-span-lifecycle.md        (Span生命周期)
3. docs/research/otel-sdk-metrics-deep-dive.md     (Metrics实现)
4. docs/research/otel-sdk-propagation-mechanism.md (传播机制)
```

#### 路径3: OTLP协议深度研究

```
1. docs/research/protobuf-encoding-deep-dive.md    (编码原理)
2. docs/research/manual-otlp-encoding.md           (手写编码)
3. docs/research/otlp-transport-comparison.md      (传输对比)
```

---

## 📖 核心文档（Phase 1完成）

### P0级核心文档

| 文档 | 主题 | 状态 | 阅读时长 |
|------|------|------|----------|
| [CSP与eBPF集成](core/csp-ebpf-integration.md) | 零侵入可观测性 | ✅ 完成 | 60min |
| [服务网格实战](core/service-mesh-istio-linkerd.md) | Istio/Linkerd | ✅ 完成 | 45min |
| [Profiling指南](core/profiling-complete-guide.md) | 性能剖析 | ✅ 完成 | 50min |
| [生产部署指南](core/production-deployment-guide.md) | K8s部署 | ✅ 完成 | 40min |
| [并发模式](core/concurrency-patterns-csp.md) | CSP/GMP | ✅ 完成 | 55min |

---

## 🔬 研究文档（进行中）

### eBPF研究系列

| 文档 | 目标 | 状态 | 预计完成 |
|------|------|------|----------|
| ebpf-setup-guide.md | 环境搭建手册 | 📝 待开始 | W1 |
| ebpf-uprobe-deep-dive.md | uprobe追踪分析 | 📝 待开始 | W2 |
| ebpf-goroutine-scheduler.md | Goroutine调度追踪 | 📝 待开始 | W2 |
| zero-intrusion-observability.md | 零侵入架构 | 📝 待开始 | W2 |
| ebpf-performance-analysis.md | 性能分析报告 | 📝 待开始 | W2 |

### SDK源码分析系列

| 文档 | 目标 | 状态 | 预计完成 |
|------|------|------|----------|
| otel-sdk-tracerprovider-init.md | Provider启动 | 📝 待开始 | W2 |
| otel-sdk-span-lifecycle.md | Span生命周期 | 📝 待开始 | W2 |
| otel-sdk-metrics-deep-dive.md | Metrics实现 | 📝 待开始 | W3 |
| otel-sdk-propagation-mechanism.md | 传播机制 | 📝 待开始 | W3 |
| otel-sdk-sampling-strategies.md | 采样策略 | 📝 待开始 | W3 |

### 协议研究系列

| 文档 | 目标 | 状态 | 预计完成 |
|------|------|------|----------|
| protobuf-encoding-deep-dive.md | Protobuf编码 | 📝 待开始 | W4 |
| manual-otlp-encoding.md | 手写OTLP编码 | 📝 待开始 | W4 |
| otlp-transport-comparison.md | 传输层对比 | 📝 待开始 | W4 |

### 传播器实现系列

| 文档 | 目标 | 状态 | 预计完成 |
|------|------|------|----------|
| b3-propagation-implementation.md | B3实现 | 📝 待开始 | W4 |
| jaeger-propagation-implementation.md | Jaeger实现 | 📝 待开始 | W4 |
| composite-propagator-design.md | 复合传播器 | 📝 待开始 | W4 |

---

## 🗂️ 代码导航

### 核心包结构

```
pkg/
├── otel/              # SDK初始化与管理
│   ├── otel.go        # 快速设置接口
│   ├── provider.go    # Tracer/Meter/Logger Provider
│   └── exporter.go    # 导出器管理
├── config/            # 配置管理
│   ├── config.go      # 通用配置
│   └── otel_config.go # OTel专用配置
├── propagation/       # 传播器 (W4完善)
│   ├── b3_single.go   # B3单头 (待实现)
│   └── jaeger.go      # Jaeger (待实现)
├── ebpf/              # eBPF追踪 (W2创建)
│   ├── tracer.go      # eBPF追踪器
│   └── loader.go      # BPF加载器
├── concurrency/       # 并发工具
│   ├── pool.go        # Worker Pool
│   └── pipeline.go    # Pipeline模式
└── ...
```

---

## 📊 研究进度

详见 [RESEARCH_TRACKING.md](RESEARCH_TRACKING.md) 获取实时进度。

---

## 🆘 需要帮助？

| 问题类型 | 查看文档 |
|----------|----------|
| 快速开始 | [README.md](../README.md) |
| 构建问题 | [Makefile](../Makefile) |
| 历史文档 | [archive/README.md](archive/README.md) |
| 项目架构 | [ARCHITECTURE.md](../ARCHITECTURE.md) |

---

**维护**: 平台工程团队
**更新**: 2026-04-06

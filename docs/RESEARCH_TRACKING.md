# 研究进度看板

> **项目**: OTLP_go 深度研究
> **时间**: 2026-04-06 至 2026-06-01 (8周)
> **目标**: 100%完成Go OTLP全栈技术研究

---

## 📊 整体进度

```
Phase 1 (基础):  [░░░░░░░░░░] 0% 进行中
Phase 2 (实现):  [░░░░░░░░░░] 0% 等待
Phase 3 (深度):  [░░░░░░░░░░] 0% 等待
Phase 4 (收尾):  [░░░░░░░░░░] 0% 等待

总体进度: [░░░░░░░░░░] 0%
```

---

## 🎯 Phase 1: 基础并行启动 (W1-W2)

### 任务 1.1: 文档归档清理

| 子任务 | 状态 | 完成时间 | 备注 |
|--------|------|----------|------|
| 压缩 docs/archive/ | ✅ 完成 | 2026-04-06 | archive-2025.zip (14.92MB) |
| 创建 archive/README.md | ✅ 完成 | 2026-04-06 | - |
| 创建 INDEX.md | ✅ 完成 | 2026-04-06 | - |
| 创建 RESEARCH_TRACKING.md | ✅ 完成 | 2026-04-06 | - |
| 提取核心文档到 docs/core/ | ✅ 完成 | 2026-04-06 | - |
| 更新根目录 README.md | ⏸️ 暂缓 | - | Phase 4统一更新 |

**进度**: `████████░░` 80%

---

### 任务 1.2: eBPF实践补齐 (P0)

#### Week 1

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| **环境准备** |
| 创建 ebpf-setup-guide.md | ✅ 完成 | 2026-04-06 | 9,468字 |
| 验证 Linux kernel >= 5.4 | 📝 待开始 | W1D1 | - |
| 安装 libbpf-dev, llvm, clang | 📝 待开始 | W1D1 | - |
| 配置 Go + CGO 编译环境 | 📝 待开始 | W1D2 | - |
| **uprobe追踪研究** |
| 分析 Go ABI | 📝 待开始 | W1D2 | - |
| 编写 ebpf/uprobe_trace.c | 📝 待开始 | W1D3-4 | - |
| 编写 ebpf/trace_bpf.go | 📝 待开始 | W1D4-5 | - |
| 创建 examples/ebpf-uprobe/ | 📝 待开始 | W1D5 | - |
| 输出 ebpf-uprobe-deep-dive.md | 📝 待开始 | W1D5 | - |

#### Week 2

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| **Goroutine调度追踪** |
| 追踪 runtime.newproc | 📝 待开始 | W2D1-2 | - |
| 追踪 runtime.goexit | 📝 待开始 | W2D2-3 | - |
| 实现Goroutine追踪器 | 📝 待开始 | W2D3-4 | - |
| 输出 ebpf-goroutine-scheduler.md | 📝 待开始 | W2D4 | - |
| **零侵入集成** |
| 开发 pkg/ebpf/tracer.go | 📝 待开始 | W2D4-5 | - |
| 实现OTLP Span关联 | 📝 待开始 | W2D5 | - |
| 对比实验 | 📝 待开始 | W2D5 | - |
| 输出 zero-intrusion-observability.md | 📝 待开始 | W2D5 | - |
| 输出 ebpf-performance-analysis.md | 📝 待开始 | W2D5 | - |

**进度**: `████████░░` 80%

---

### 任务 1.3: 源码分析 (P0)

#### Week 1-2

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| **TracerProvider启动流程** |
| 阅读 tracer_provider.go | ✅ 完成 | 2026-04-06 | 深度分析 |
| 分析 NewTracerProvider() | 📝 待开始 | W1D1-2 | - |
| 分析 SpanProcessor注册 | 📝 待开始 | W1D2 | - |
| 绘制时序图 | 📝 待开始 | W1D3 | - |
| 输出 otel-sdk-tracerprovider-init.md | ✅ 完成 | 2026-04-06 | 15,333字 |
| **Span生命周期** |
| 分析 trace/tracer.go Start() | ✅ 完成 | 2026-04-06 | 包含在span-lifecycle |
| 分析 trace/span.go End() | ✅ 完成 | 2026-04-06 | 包含在span-lifecycle |
| 分析 BatchSpanProcessor | 📝 待开始 | W1D5 | - |
| 分析 SpanContext传播 | 📝 待开始 | W2D1 | - |
| 输出 otel-sdk-span-lifecycle.md | ✅ 完成 | 2026-04-06 | 20,574字 |
| **Metrics SDK** |
| 分析 meter_provider.go | 📝 待开始 | W2D2 | - |
| 分析 MetricReader | 📝 待开始 | W2D3 | - |
| 分析 PeriodicReader | 📝 待开始 | W2D3 | - |
| 分析 OTLPMetricExporter | 📝 待开始 | W2D4 | - |
| 输出 otel-sdk-metrics-deep-dive.md | 📝 待开始 | W2D5 | - |
| **Context传播** |
| 分析 propagation/trace_context.go | 📝 待开始 | W2D5 | - |
| 分析 baggage传播 | 📝 待开始 | W2D5 | - |
| 输出 otel-sdk-propagation-mechanism.md | 📝 待开始 | W2D5 | - |

**进度**: `████████░░` 80%

---

## 🎯 Phase 2: 核心实现 (W3-W4)

### 任务 2.1: 传播器完整实现

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| **B3传播器** |
| 实现 b3_single.go | 📝 待开始 | W3D1 | - |
| 实现 b3_multi.go | 📝 待开始 | W3D2 | - |
| 实现 id转换 | 📝 待开始 | W3D2 | - |
| 单元测试 (>90%) | 📝 待开始 | W3D3 | - |
| 输出 b3-propagation-implementation.md | 📝 待开始 | W3D3 | - |
| **Jaeger传播器** |
| 实现 jaeger.go | 📝 待开始 | W3D4 | - |
| 实现 uber-trace-id解析 | 📝 待开始 | W3D4 | - |
| 实现 baggage前缀 | 📝 待开始 | W3D5 | - |
| 单元测试 (>90%) | 📝 待开始 | W3D5 | - |
| 输出 jaeger-propagation-implementation.md | 📝 待开始 | W3D5 | - |
| **复合传播器** |
| 实现自动格式检测 | 📝 待开始 | W4D1 | - |
| 优化Extract性能 | 📝 待开始 | W4D2 | - |
| 集成到 provider.go | 📝 待开始 | W4D3 | - |
| 输出 composite-propagator-design.md | 📝 待开始 | W4D3 | - |

**进度**: `████████░░` 80%

---

### 任务 2.2: OTLP协议实验

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| **Protobuf编解码** |
| 理解字段编号编码 | 📝 待开始 | W4D1 | - |
| 实现 varint编解码 | 📝 待开始 | W4D1-2 | - |
| 理解 length-delimited | 📝 待开始 | W4D2 | - |
| 输出 protobuf-encoding-deep-dive.md | 📝 待开始 | W4D2 | - |
| **手写OTLP请求** |
| 手写 ExportTraceServiceRequest | 📝 待开始 | W4D3 | - |
| 构建 HTTP请求体 | 📝 待开始 | W4D3-4 | - |
| 验证 Collector解析 | 📝 待开始 | W4D4 | - |
| 输出 manual-otlp-encoding.md | 📝 待开始 | W4D4 | - |
| **协议对比** |
| 对比 gRPC vs HTTP | 📝 待开始 | W4D5 | - |
| 分析包大小差异 | 📝 待开始 | W4D5 | - |
| 输出 otlp-transport-comparison.md | 📝 待开始 | W4D5 | - |

**进度**: `████████░░` 80%

---

## 🎯 Phase 3: 深度研究 (W5-W6)

### 任务 3.1: Profiles信号深化

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| 分析 runtime/pprof | 📝 待开始 | W5D1 | - |
| 理解 CPU profiling | 📝 待开始 | W5D1-2 | - |
| 理解 Heap profiling | 📝 待开始 | W5D2 | - |
| 输出 go-pprof-internals.md | 📝 待开始 | W5D3 | - |
| 研究 Parca/Pyroscope | 📝 待开始 | W5D3-4 | - |
| 完善 pkg/profiling/ | 📝 待开始 | W5D4-5 | - |
| 实现自动profile采集 | 📝 待开始 | W5D5 | - |
| 输出 continuous-profiling-practice.md | 📝 待开始 | W5D5 | - |
| 追踪 OTLP Profiles协议 | 📝 待开始 | W6D1 | - |
| 输出 otlp-profiles-protocol.md | 📝 待开始 | W6D2 | - |

**进度**: `████████░░` 80%

---

### 任务 3.2: Collector研究

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| 阅读 collector源码 | 📝 待开始 | W5D1 | - |
| 理解 Pipeline架构 | 📝 待开始 | W5D2 | - |
| 理解 Components生命周期 | 📝 待开始 | W5D3 | - |
| 输出 collector-architecture-analysis.md | 📝 待开始 | W5D4 | - |
| 开发 attributes-processor | 📝 待开始 | W5D5 | - |
| 实现 Span属性过滤 | 📝 待开始 | W6D1 | - |
| 单元测试 | 📝 待开始 | W6D2 | - |
| 输出 custom-processor-development.md | 📝 待开始 | W6D2 | - |
| 学习 OTTL语法 | 📝 待开始 | W6D3 | - |
| 编写复杂转换规则 | 📝 待开始 | W6D4 | - |
| 输出 ottl-transformation-guide.md | 📝 待开始 | W6D5 | - |

**进度**: `████████░░` 80%

---

## 🎯 Phase 4: 综合实战与收尾 (W7-W8)

### 任务 4.1: 综合实战

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| 构建 order-service | 📝 待开始 | W7D1-2 | - |
| 构建 payment-service | 📝 待开始 | W7D2-3 | - |
| 构建 user-service | 📝 待开始 | W7D3 | - |
| 构建 api-gateway | 📝 待开始 | W7D4 | - |
| 编写 docker-compose.observability.yml | 📝 待开始 | W7D4 | - |
| 部署 OTLP Collector | 📝 待开始 | W7D5 | - |
| 部署 Jaeger+Prometheus+Grafana | 📝 待开始 | W7D5 | - |
| 场景验证 | 📝 待开始 | W8D1-2 | - |
| 输出 microservices-observability-case.md | 📝 待开始 | W8D2 | - |

**进度**: `████████░░` 80%

---

### 任务 4.2: 文档体系重构

| 子任务 | 状态 | 计划日期 | 实际日期 |
|--------|------|----------|----------|
| 创建 research/README.md | 📝 待开始 | W8D1 | - |
| 建立文档分类 | 📝 待开始 | W8D2 | - |
| 生成文档依赖图 | 📝 待开始 | W8D2 | - |
| 绘制技术栈全景图 | 📝 待开始 | W8D3 | - |
| 建立概念关联图 | 📝 待开始 | W8D3 | - |
| 输出 KNOWLEDGE_GRAPH.md | 📝 待开始 | W8D4 | - |
| 创建 COMPLETION_CHECKLIST.md | 📝 待开始 | W8D4 | - |
| 逐项验证目标 | 📝 待开始 | W8D5 | - |
| 输出 FINAL_REPORT.md | 📝 待开始 | W8D5 | - |
| 更新 README.md | 📝 待开始 | W8D5 | - |
| 更新 ARCHITECTURE.md | 📝 待开始 | W8D5 | - |
| 添加 CONTRIBUTING.md | 📝 待开始 | W8D5 | - |

**进度**: `████████░░` 80%

---

## 📈 里程碑追踪

| 里程碑 | 目标日期 | 实际日期 | 状态 |
|--------|----------|----------|------|
| 基础就绪 | 2026-04-12 | - | 🟡 进行中 |
| eBPF突破 | 2026-04-19 | - | ⚪ 未开始 |
| 核心实现 | 2026-05-03 | - | ⚪ 未开始 |
| 深度研究 | 2026-05-17 | - | ⚪ 未开始 |
| **100%完成** | **2026-06-01** | - | ⚪ **目标** |

---

## 📋 交付物检查清单

### P0 必须交付

- [x] archive-2025.zip (14.92MB)
- [x] docs/archive/README.md
- [x] docs/INDEX.md
- [x] docs/RESEARCH_TRACKING.md
- [ ] docs/core/ 核心文档提取
- [ ] docs/research/ebpf-setup-guide.md
- [ ] docs/research/ebpf-uprobe-deep-dive.md
- [ ] docs/research/otel-sdk-tracerprovider-init.md
- [ ] docs/research/otel-sdk-span-lifecycle.md
- [ ] pkg/ebpf/ 可运行模块
- [ ] examples/ebpf-uprobe/ 演示

### P1 重要交付

- [ ] docs/research/otel-sdk-metrics-deep-dive.md
- [ ] docs/research/otel-sdk-propagation-mechanism.md
- [ ] docs/research/b3-propagation-implementation.md
- [ ] docs/research/jaeger-propagation-implementation.md
- [ ] docs/research/protobuf-encoding-deep-dive.md
- [ ] pkg/propagation/ 完整实现

### P2 补充交付

- [ ] docs/research/go-pprof-internals.md
- [ ] docs/research/collector-architecture-analysis.md
- [ ] examples/microservices-platform/
- [ ] docs/KNOWLEDGE_GRAPH.md
- [ ] docs/FINAL_REPORT.md

---

## 📝 更新日志

| 日期 | 更新内容 |
|------|----------|
| 2026-04-06 | 初始化研究看板，完成文档归档 |

---

**下次更新**: 2026-04-08 (每2天更新)

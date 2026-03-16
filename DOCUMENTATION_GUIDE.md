# 📚 OTLP Go 项目文档导航指南

> **版本**: v3.0.0  
> **更新日期**: 2026-03-17  
> **Go 版本**: 1.26  
> **OTLP 版本**: 1.10.0

---

## 🎯 核心文档（根目录）

| 文档 | 说明 | 优先级 |
|------|------|--------|
| [README.md](./README.md) | 项目主文档，快速开始指南 | ⭐⭐⭐ |
| [ARCHITECTURE.md](./ARCHITECTURE.md) | 项目架构详解，三层架构设计 | ⭐⭐⭐ |
| [BEST_PRACTICES.md](./BEST_PRACTICES.md) | 生产环境最佳实践 | ⭐⭐ |
| [CONTRIBUTING.md](./CONTRIBUTING.md) | 贡献指南 | ⭐ |

---

## 📂 文档组织结构

```
docs/
├── 📖 核心分析文档
│   └── analysis/
│       ├── csp-otlp/                 # CSP 与 OTLP 集成分析
│       ├── golang-language/          # Go 语言分析
│       ├── semantic-model/           # 语义模型
│       └── system-perspectives/      # 系统视角
│
├── 💻 实现文档
│   └── implementation/
│
├── 📦 归档文档（历史版本）
│   └── archive/
│       ├── go126_migration/          # Go 1.26 迁移相关
│       ├── project_reports/          # 项目报告
│       └── 标准深度梳理_2025_10/      # 历史深度梳理文档
│
└── 📋 其他文档
    └── 00_index.md
```

---

## 🚀 快速开始路径

### 入门路径（1-2周）

1. **阅读 README** → 了解项目概览和快速开始
2. **学习 ARCHITECTURE** → 理解项目架构设计
3. **运行示例** → `examples/` 目录下的完整示例

### 进阶路径（2-4周）

1. **阅读 docs/analysis/** → 深入理解 CSP-OTLP 集成
2. **研究 src/** → 核心代码实现
3. **实践 BEST_PRACTICES** → 生产环境部署

### 专家路径（4-8周）

1. **形式化验证** → docs/analysis/formal-proofs/
2. **性能优化** → benchmarks/ 和性能分析文档
3. **贡献代码** → 阅读 CONTRIBUTING.md

---

## 📊 文档统计

| 类别 | 数量 | 状态 |
|------|------|------|
| 核心文档（根目录） | 5 | ✅ 精简完成 |
| 分析文档（docs/analysis/） | ~200 | ✅ 主题相关 |
| 实现文档（docs/implementation/） | ~10 | ✅ 维护中 |
| 归档文档（docs/archive/） | ~600 | 📦 已归档 |

---

## 🔍 主题对齐声明

### ✅ 核心主题

本项目专注于以下技术领域：

- **Go 1.26** - 最新语言特性和性能优化
- **OTLP (OpenTelemetry Protocol) 1.10.0** - 可观测性标准协议
- **CSP 并发模式** - 理论到实践的完整映射
- **eBPF 零侵入可观测性** - 内核级追踪
- **服务网格** - Istio/Linkerd 集成
- **云原生部署** - Kubernetes + Docker

### ❌ 已归档/无关内容

以下内容已归档到 `docs/archive/`，不再主动维护：

- 大量重复的项目完成报告
- Go 1.25.1 及更早版本的旧文档
- 与 Rust 相关的文档（本项目专注 Go）
- 历史里程碑报告和状态更新

---

## 📈 版本对齐状态

| 组件 | 当前版本 | 状态 |
|------|----------|------|
| Go | 1.26 | ✅ 已对齐 |
| OTLP Protocol | 1.10.0 | ✅ 已对齐 |
| OpenTelemetry SDK | 1.30.0+ | ✅ 已对齐 |
| Kubernetes | 1.32+ | ✅ 已对齐 |

---

## 📝 维护说明

- **活跃维护**: 根目录文档和 `docs/analysis/csp-otlp/` 下的核心分析文档
- **定期审查**: `docs/implementation/` 实现文档
- **历史归档**: `docs/archive/` 下的所有文档（只读）

---

**维护者**: 平台工程团队  
**最后更新**: 2026-03-17

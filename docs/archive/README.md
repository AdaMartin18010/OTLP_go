# 历史文档归档说明

## 归档信息

- **归档文件**: `docs/archive-2025.zip`
- **归档日期**: 2026-04-06
- **原始大小**: ~50MB
- **压缩后**: 14.92MB
- **文档数量**: 700+ 历史文档

## 归档内容

### 2025-10 月度报告

包含2025年10月的所有项目完成报告、进度报告、里程碑庆祝文档。

### go126_migration

Go 1.26 迁移过程中的修复报告和迁移指南。

### golang-1.25.1-otlp-integration

早期Go 1.25.1与OTLP集成的研究文档（已过时，仅供参考）。

### 标准深度梳理_2025_10

核心研究文档目录，包含以下重要文档：

#### 保留核心文档（已提取到 docs/core/）

以下5个文档是项目的核心研究成果，已在归档外保留：

1. **🐝 Go + eBPF深度集成指南** (`csp-ebpf-integration.md`)
   - 零侵入式可观测性
   - Goroutine追踪
   - GC监控

2. **🕸️ Go服务网格集成实战** (`service-mesh-istio-linkerd.md`)
   - Istio + Linkerd
   - 流量管理
   - mTLS安全

3. **🔥 Go Profiling完整指南** (`profiling-complete-guide.md`)
   - CPU/内存/Goroutine分析
   - OTLP Profiles集成

4. **🚀 Go生产环境部署运维指南** (`production-deployment-guide.md`)
   - Docker、Kubernetes
   - OTLP Collector部署
   - CI/CD集成

5. **⚡ Go并发模式深度实战** (`concurrency-patterns-csp.md`)
   - GMP模型
   - CSP模式
   - 无锁编程

## 如何使用归档

```bash
# 解压查看历史文档
unzip docs/archive-2025.zip -d docs/archive-extracted/
```

## 注意事项

- 归档内的文档不再更新
- 如发现需要提取的核心文档，请提交issue
- 新研究文档请直接写入 docs/research/ 目录

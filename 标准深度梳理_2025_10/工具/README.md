# 🛠️ OpenTelemetry 工具集

> **目的**: 提供实用工具,简化OpenTelemetry的配置、部署和管理

---

## 📖 目录

- [🛠️ OpenTelemetry 工具集](#️-opentelemetry-工具集)
  - [📖 目录](#-目录)
  - [🚀 可用工具](#-可用工具)
    - [1. 配置生成器 (Config Generator)](#1-配置生成器-config-generator)
  - [🎯 工具对比](#-工具对比)
  - [📚 使用指南](#-使用指南)
    - [配置生成器快速上手](#配置生成器快速上手)
  - [🔮 规划中的工具](#-规划中的工具)
    - [2. SDK示例代码生成器 (SDK Code Generator)](#2-sdk示例代码生成器-sdk-code-generator)
    - [3. 性能测试工具 (Performance Tester)](#3-性能测试工具-performance-tester)
    - [4. 配置迁移工具 (Config Migrator)](#4-配置迁移工具-config-migrator)
    - [5. 可视化Pipeline编辑器 (Visual Pipeline Editor)](#5-可视化pipeline编辑器-visual-pipeline-editor)
    - [6. 成本计算器 (Cost Calculator)](#6-成本计算器-cost-calculator)
  - [🤝 贡献工具](#-贡献工具)
  - [📖 相关文档](#-相关文档)

---

## 🚀 可用工具

### 1. 配置生成器 (Config Generator)

**路径**: `config-generator/`

**描述**: 交互式Web应用,帮助快速生成OpenTelemetry Collector配置文件

**功能**:

- ✅ 可视化配置OpenTelemetry Collector
- ✅ 支持Agent、Gateway、混合部署模式
- ✅ 自动生成Kubernetes/Docker部署清单
- ✅ 智能配置推荐和安全检查
- ✅ 云平台集成支持 (阿里云、腾讯云、华为云)
- ✅ 配置验证脚本生成

**使用场景**:

- 🎯 初次配置OpenTelemetry Collector
- 🎯 快速验证不同配置组合
- 🎯 生成生产级配置模板
- 🎯 学习最佳配置实践

**快速开始**:

```bash
# 进入工具目录
cd config-generator/

# 打开index.html
open index.html  # macOS
start index.html # Windows
xdg-open index.html # Linux
```

**详细文档**: [config-generator/README.md](./config-generator/README.md)

**技术栈**:

- 纯前端 (HTML + CSS + JavaScript)
- 无需后端服务器
- 零依赖

**版本**: v1.0.0  
**基于**: OTLP v1.3.0, Collector v0.113.0

---

## 🎯 工具对比

| 工具 | 类型 | 适用对象 | 难度 | 部署方式 |
|------|------|----------|------|----------|
| **配置生成器** | Web应用 | 所有用户 | ⭐ 简单 | 直接打开HTML |

---

## 📚 使用指南

### 配置生成器快速上手

**步骤1: 选择场景**:

根据您的部署环境选择:

| 场景 | 部署模式 | 资源配置 |
|------|----------|----------|
| **Kubernetes微服务** | Agent (DaemonSet) | 512 MiB |
| **集中式网关** | Gateway | 2048 MiB |
| **大规模生产** | Hybrid | 视情况而定 |
| **本地开发调试** | Gateway | 512 MiB |

**步骤2: 配置组件**:

根据需求选择:

- **Traces**: 分布式追踪 (推荐)
- **Metrics**: 指标监控 (推荐)
- **Logs**: 日志采集
- **Profiles**: 性能画像 (v1.3.0+)

**步骤3: 性能调优**:

调整关键参数:

```yaml
# 批处理大小
send_batch_size: 8192  # 生产环境推荐

# 内存限制
limit_mib: 2048  # Gateway模式
# 或
limit_mib: 512   # Agent模式

# 压缩算法
compression: gzip  # 或 zstd (v1.3.0+)
```

**步骤4: 安全配置**:

生产环境必须启用:

- ☑️ **TLS加密**: 保护传输安全
- ☑️ **认证**: Bearer Token或API Key

**步骤5: 部署**:

生成的配置包括:

1. **config.yaml**: Collector配置文件
2. **部署命令**: Kubernetes/Docker部署清单
3. **validate.sh**: 配置验证脚本

---

## 🔮 规划中的工具

以下工具正在规划中,欢迎贡献:

### 2. SDK示例代码生成器 (SDK Code Generator)

**状态**: 🚧 规划中

**功能**:

- 生成多语言SDK集成代码 (Go, Java, Python, JavaScript)
- 支持自动/手动仪表化
- 生成Trace、Metric、Log示例代码

### 3. 性能测试工具 (Performance Tester)

**状态**: 🚧 规划中

**功能**:

- Collector性能基准测试
- 负载模拟和压力测试
- 生成性能报告

### 4. 配置迁移工具 (Config Migrator)

**状态**: 🚧 规划中

**功能**:

- Jaeger → OTLP配置迁移
- Zipkin → OTLP配置迁移
- Prometheus → OTLP配置迁移

### 5. 可视化Pipeline编辑器 (Visual Pipeline Editor)

**状态**: 🚧 规划中

**功能**:

- 拖拽式Pipeline设计
- 实时预览数据流
- 性能预估

### 6. 成本计算器 (Cost Calculator)

**状态**: 🚧 规划中

**功能**:

- 估算云平台成本
- 采样策略优化建议
- ROI计算

---

## 🤝 贡献工具

欢迎贡献新工具!

**贡献流程**:

1. **提出想法**: 在Issue中描述工具功能
2. **设计方案**: 提供工具设计文档
3. **开发实现**: 遵循项目代码规范
4. **文档编写**: 提供详细的README
5. **测试验证**: 确保工具可用性

**工具要求**:

- ✅ 解决实际问题
- ✅ 易于使用
- ✅ 文档齐全
- ✅ 跨平台兼容
- ✅ 开源许可 (MIT)

**工具目录结构**:

```text
工具/
├── README.md                    # 工具集总览 (本文件)
├── config-generator/            # 配置生成器
│   ├── README.md               # 详细文档
│   ├── index.html              # 主应用
│   ├── generator.js            # 核心逻辑
│   └── examples/               # 使用示例
└── [新工具名]/
    ├── README.md
    └── ...
```

---

## 📖 相关文档

**速查手册系列**:

- [OTLP协议速查手册](../速查手册/01_OTLP协议速查手册.md)
- [Semantic Conventions速查手册](../速查手册/02_Semantic_Conventions速查手册.md)
- [Collector配置速查手册](../速查手册/03_Collector配置速查手册.md)
- [故障排查速查手册](../速查手册/04_故障排查速查手册.md)
- [性能优化速查手册](../速查手册/05_性能优化速查手册.md)
- [安全配置速查手册](../速查手册/06_安全配置速查手册.md)

**云平台集成**:

- [阿里云OTLP集成指南](../云平台集成/01_阿里云OTLP集成指南.md)
- [腾讯云OTLP集成指南](../云平台集成/02_腾讯云OTLP集成指南.md)
- [华为云OTLP集成指南](../云平台集成/03_华为云OTLP集成指南.md)

**核心文档**:

- [OTLP核心协议](../01_OTLP核心协议/)
- [Semantic Conventions](../02_Semantic_Conventions/)
- [数据模型](../03_数据模型/)
- [核心组件](../04_核心组件/)

---

**🚀 开始使用工具,提升OpenTelemetry配置效率!**

```bash
# 快速启动配置生成器
cd config-generator/
open index.html
```

---

**最后更新**: 2025年10月9日  
**维护者**: OTLP标准深度梳理项目组

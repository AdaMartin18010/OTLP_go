# 📚 OpenTelemetry速查手册系列

> **系列完成度**: 100% (6/6)  
> **最后更新**: 2025年10月9日  
> **总行数**: ~3,100行

---

## 🎯 系列简介

本系列提供6篇精简、实用的OpenTelemetry速查手册,每篇都经过精心设计,聚焦于"快速查阅"和"立即可用"的原则。

### ✨ 核心特点

- **📄 精简**: 每篇<600行,快速浏览
- **📊 表格化**: 结构化信息,便于查找
- **🚀 实用**: 可直接复制的配置和代码
- **🎯 场景化**: 按使用场景组织内容

---

## 📖 手册列表

### 1️⃣ [OTLP协议速查手册](./01_OTLP协议速查手册.md)

**行数**: ~550行  
**用途**: 快速参考OTLP核心协议要点

**核心内容**:

- 协议版本演进 (v1.0.0 → v1.3.0)
- 传输协议对比 (gRPC vs HTTP)
- 信号类型速查 (Traces, Metrics, Logs, Profiles)
- 编码格式 (Protobuf vs JSON)
- HTTP Headers & 响应码
- 批处理 & 压缩配置
- 重试策略
- 多语言SDK配置示例
- 快速诊断命令

**适合**:

- 快速了解OTLP协议规范
- 配置SDK导出器
- 诊断连接问题

---

### 2️⃣ [Semantic Conventions速查手册](./02_Semantic_Conventions速查手册.md)

**行数**: ~620行  
**用途**: 快速查找OpenTelemetry语义约定标准

**核心内容**:

- 通用属性 (service.name, deployment.environment)
- 资源属性 (Service, Container, K8s, Cloud)
- Traces属性 (Span Kind, 错误属性)
- Metrics命名规范
- Logs属性
- HTTP约定 (请求/响应/状态码)
- 数据库约定 (SQL/NoSQL)
- 消息队列约定 (Kafka, RabbitMQ)
- 云平台约定 (AWS, Azure, GCP, 阿里云)
- **GenAI约定 (v1.29.0稳定)** 🆕
- 命名规范和最佳实践

**适合**:

- 查找标准属性名称
- 实施语义约定
- 确保跨系统互操作性

---

### 3️⃣ [Collector配置速查手册](./03_Collector配置速查手册.md)

**行数**: ~560行  
**用途**: 快速配置OpenTelemetry Collector

**核心内容**:

- 配置结构 (Receivers, Processors, Exporters, Extensions)
- Receivers速查 (OTLP, Prometheus, Jaeger, Filelog, Kafka)
- Processors速查 (Batch, Memory Limiter, Resource, Attributes, Tail Sampling, Filter, Transform)
- Exporters速查 (OTLP, Prometheus, Logging, File, Kafka, Loki)
- Extensions速查 (Health Check, PProf, zPages)
- Service Pipeline配置
- 常用配置模板 (简单网关、生产级、K8s DaemonSet、多后端)
- 部署模式 (Agent, Gateway, 混合模式)
- 性能调优建议

**适合**:

- 配置Collector
- 选择合适的Processor
- 优化Pipeline性能

---

### 4️⃣ [故障排查速查手册](./04_故障排查速查手册.md)

**行数**: ~520行  
**用途**: 快速诊断和解决OpenTelemetry常见问题

**核心内容**:

- 快速诊断流程图
- 连接问题 (连接拒绝, TLS握手失败)
- 数据未到达 (逐层排查: SDK → Collector → Backend)
- 性能问题 (高延迟, OOM, CPU占用高)
- 错误码速查 (HTTP 4xx/5xx, gRPC错误码)
- Collector问题 (启动失败, 数据丢失, 重启)
- SDK问题 (Go, Python, JavaScript常见错误)
- 网络问题 (DNS, 防火墙, 代理)
- 调试工具 (grpcurl, curl, tcpdump, zPages)
- 故障排查清单

**适合**:

- 快速定位问题
- 解决常见错误
- 学习调试技巧

---

### 5️⃣ [性能优化速查手册](./05_性能优化速查手册.md)

**行数**: ~500行  
**用途**: 快速优化OpenTelemetry性能,降低开销

**核心内容**:

- 性能目标基准
- SDK优化 (批处理、采样、避免高基数属性)
- Collector优化 (批处理、内存限制、并发导出、资源配置)
- Pipeline精简
- 网络优化 (压缩、gRPC vs HTTP)
- 采样策略 (Head Sampling, Tail Sampling, 混合采样)
- 成本优化 (存储成本、网络成本、计算成本)
- 监控指标 (SDK/Collector关键指标)
- 告警规则
- 优化清单 (快速/进阶/高级)

**适合**:

- 降低性能开销
- 优化成本
- 提升吞吐量

---

### 6️⃣ [安全配置速查手册](./06_安全配置速查手册.md)

**行数**: ~550行  
**用途**: 快速配置OpenTelemetry安全防护

**核心内容**:

- 安全威胁分析 (MITM, 未授权访问, 敏感数据泄露)
- 传输加密 (TLS, mTLS配置)
- 证书管理 (生成自签名证书, 证书轮换)
- 认证授权 (Bearer Token, API Key, OAuth 2.0, mTLS)
- 数据脱敏 (删除敏感字段, 哈希脱敏, 日志脱敏)
- 网络隔离 (VPC部署, NetworkPolicy, 防火墙)
- 访问控制 (RBAC, Pod Security Policy)
- 审计日志
- 密钥管理 (环境变量, K8s Secrets, Vault)
- 安全清单 (生产环境安全基线)
- 安全等级 (基础/增强/高安全)

**适合**:

- 加固生产环境安全
- 实施数据保护
- 通过安全审计

---

## 🚀 快速开始

### 场景1: 我是新手,刚接触OpenTelemetry

**推荐阅读顺序**:

1. [OTLP协议速查手册](./01_OTLP协议速查手册.md) - 了解基础协议
2. [Semantic Conventions速查手册](./02_Semantic_Conventions速查手册.md) - 学习标准约定
3. [Collector配置速查手册](./03_Collector配置速查手册.md) - 配置Collector
4. [故障排查速查手册](./04_故障排查速查手册.md) - 解决常见问题

---

### 场景2: 我要部署生产环境

**推荐阅读顺序**:

1. [Collector配置速查手册](./03_Collector配置速查手册.md) - 生产级配置
2. [安全配置速查手册](./06_安全配置速查手册.md) - 安全加固
3. [性能优化速查手册](./05_性能优化速查手册.md) - 性能调优
4. [故障排查速查手册](./04_故障排查速查手册.md) - 故障预案

---

### 场景3: 系统出现问题,需要快速诊断

**直接跳转**:

- [故障排查速查手册](./04_故障排查速查手册.md) - 第一时间定位问题
- [OTLP协议速查手册](./01_OTLP协议速查手册.md#快速诊断) - 验证连接和配置

---

### 场景4: 成本过高,需要优化

**直接跳转**:

- [性能优化速查手册](./05_性能优化速查手册.md#成本优化) - 降低存储/网络成本
- [性能优化速查手册](./05_性能优化速查手册.md#采样策略) - 配置采样

---

### 场景5: 安全审计要求整改

**直接跳转**:

- [安全配置速查手册](./06_安全配置速查手册.md#安全清单) - 完整安全基线
- [安全配置速查手册](./06_安全配置速查手册.md#传输加密) - TLS配置
- [安全配置速查手册](./06_安全配置速查手册.md#数据脱敏) - 敏感数据保护

---

## 📊 系列统计

| 手册 | 行数 | 主要内容 | 完成度 |
|-----|------|---------|--------|
| 01_OTLP协议速查 | ~550 | 协议规范、配置、诊断 | ✅ 100% |
| 02_Semantic_Conventions速查 | ~620 | 语义约定、GenAI | ✅ 100% |
| 03_Collector配置速查 | ~560 | 配置模板、部署模式 | ✅ 100% |
| 04_故障排查速查 | ~520 | 问题诊断、解决方案 | ✅ 100% |
| 05_性能优化速查 | ~500 | 性能调优、成本优化 | ✅ 100% |
| 06_安全配置速查 | ~550 | 安全加固、数据保护 | ✅ 100% |
| **总计** | **~3,100** | **6篇完整手册** | **✅ 100%** |

---

## 🎯 使用建议

### ✅ 推荐用法

- **快速查阅**: 遇到问题时,快速找到相关章节
- **配置参考**: 复制粘贴配置示例,快速上手
- **团队培训**: 作为内部培训材料
- **故障手册**: 加入运维故障应急手册
- **安全审计**: 作为安全合规检查清单

### ⚠️ 注意事项

- 本系列为**速查手册**,不是完整教程
- 配置示例需根据实际场景调整
- 生产环境配置前务必测试
- 定期查看官方文档以获取最新信息

---

## 🔗 相关资源

### 项目内其他文档

- [01_OTLP核心协议](../01_OTLP核心协议/) - 协议深度解析
- [02_Semantic_Conventions](../02_Semantic_Conventions/) - 语义约定详解
- [03_数据模型](../03_数据模型/) - Traces/Metrics/Logs详解

### 官方资源

| 资源 | 链接 |
|------|------|
| **OpenTelemetry官网** | <https://opentelemetry.io/> |
| **OTLP规范** | <https://opentelemetry.io/docs/specs/otlp/> |
| **Collector文档** | <https://opentelemetry.io/docs/collector/> |
| **Semantic Conventions** | <https://opentelemetry.io/docs/specs/semconv/> |
| **GitHub** | <https://github.com/open-telemetry> |

---

## 📝 更新日志

### 2025-10-09 (v1.0.0)

- ✅ 创建完整的速查手册系列 (6篇)
- ✅ 涵盖OTLP v1.3.0最新特性
- ✅ 包含GenAI语义约定 (v1.29.0)
- ✅ 提供生产级配置示例
- ✅ 完整的故障排查指南
- ✅ 量化的性能和成本优化建议
- ✅ 企业级安全配置方案

---

## 🤝 贡献

如果您发现任何错误或有改进建议,欢迎提交Issue或Pull Request。

---

## 📄 许可

本文档遵循项目根目录的LICENSE文件。

---

**系列作者**: OTLP项目改进小组  
**完成时间**: 2025年10月9日  
**工作量**: 约12小时  
**维护状态**: ✅ 活跃维护

---

## 🎉 享受快速查阅的便利

立即开始使用这些速查手册,让OpenTelemetry集成变得更简单、更高效!

**快速链接**:

- [📘 OTLP协议](./01_OTLP协议速查手册.md)
- [📘 语义约定](./02_Semantic_Conventions速查手册.md)
- [📘 Collector配置](./03_Collector配置速查手册.md)
- [📘 故障排查](./04_故障排查速查手册.md)
- [📘 性能优化](./05_性能优化速查手册.md)
- [📘 安全配置](./06_安全配置速查手册.md)

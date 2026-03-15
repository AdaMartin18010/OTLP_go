# 🚀 OpenTelemetry Collector 配置生成器

> **Version**: 1.0.0  
> **基于**: OTLP v1.3.0, Collector v0.113.0  
> **类型**: 交互式 Web 应用 (纯前端)

---

## 📖 目录

- [🚀 OpenTelemetry Collector 配置生成器](#-opentelemetry-collector-配置生成器)
  - [📖 目录](#-目录)
  - [🎯 功能特性](#-功能特性)
  - [🏁 快速开始](#-快速开始)
    - [方式一: 直接打开 (推荐)](#方式一-直接打开-推荐)
    - [方式二: 本地HTTP服务器](#方式二-本地http服务器)
  - [📝 使用指南](#-使用指南)
    - [1. 选择部署模式](#1-选择部署模式)
    - [2. 配置遥测信号](#2-配置遥测信号)
    - [3. 选择组件](#3-选择组件)
    - [4. 性能与安全](#4-性能与安全)
    - [5. 生成与部署](#5-生成与部署)
  - [🔧 支持的配置选项](#-支持的配置选项)
    - [部署模式](#部署模式)
    - [遥测信号](#遥测信号)
    - [接收器 (Receivers)](#接收器-receivers)
    - [处理器 (Processors)](#处理器-processors)
    - [导出器 (Exporters)](#导出器-exporters)
    - [性能配置](#性能配置)
    - [安全配置](#安全配置)
  - [📊 生成的文件](#-生成的文件)
    - [1. 配置文件 (`config.yaml`)](#1-配置文件-configyaml)
    - [2. 部署命令](#2-部署命令)
    - [3. 验证脚本 (`validate.sh`)](#3-验证脚本-validatesh)
  - [🎨 界面预览](#-界面预览)
  - [💡 使用场景示例](#-使用场景示例)
    - [场景1: Kubernetes微服务追踪](#场景1-kubernetes微服务追踪)
    - [场景2: 生产级网关模式](#场景2-生产级网关模式)
    - [场景3: 开发环境调试](#场景3-开发环境调试)
    - [场景4: 云平台集成 (阿里云)](#场景4-云平台集成-阿里云)
  - [🔍 配置验证](#-配置验证)
  - [📚 最佳实践建议](#-最佳实践建议)
    - [资源配置](#资源配置)
    - [批处理优化](#批处理优化)
    - [采样策略](#采样策略)
    - [安全加固](#安全加固)
  - [🐛 故障排查](#-故障排查)
  - [🔄 更新日志](#-更新日志)
    - [v1.0.0 (2025-10-09)](#v100-2025-10-09)
  - [📖 相关文档](#-相关文档)
  - [🤝 贡献指南](#-贡献指南)
  - [📄 许可证](#-许可证)

---

## 🎯 功能特性

✅ **零依赖**: 纯前端实现,无需后端服务器  
✅ **交互式界面**: 现代化UI,实时预览生成的配置  
✅ **多场景支持**: Agent、Gateway、混合模式  
✅ **完整配置**: 自动生成Receiver、Processor、Exporter、Service  
✅ **部署就绪**: 提供Kubernetes/Docker部署清单  
✅ **智能推荐**: 根据环境自动优化配置参数  
✅ **安全检查**: 验证TLS、认证等安全配置  
✅ **云平台集成**: 支持阿里云、腾讯云、华为云  
✅ **一键复制**: 快速复制配置文件和部署脚本  

---

## 🏁 快速开始

### 方式一: 直接打开 (推荐)

```bash
# 1. 进入工具目录
cd 标准深度梳理_2025_10/工具/config-generator/

# 2. 用浏览器打开 index.html
# Windows:
start index.html

# macOS:
open index.html

# Linux:
xdg-open index.html
```

### 方式二: 本地HTTP服务器

```bash
# Python 3
python -m http.server 8080

# Node.js (需要安装 http-server)
npx http-server -p 8080

# 然后访问: http://localhost:8080
```

---

## 📝 使用指南

### 1. 选择部署模式

- **Agent模式**: 适合Kubernetes DaemonSet,每个节点运行一个实例
- **Gateway模式**: 集中式网关,处理所有遥测数据
- **混合模式**: Agent收集 + Gateway汇聚

### 2. 配置遥测信号

选择需要采集的信号类型:

- ✅ **Traces** (链路追踪)
- ✅ **Metrics** (指标)
- ✅ **Logs** (日志)
- ✅ **Profiles** (性能画像,v1.3.0+新特性)

### 3. 选择组件

- **Receivers**: OTLP (推荐), Prometheus, Jaeger, Zipkin
- **Processors**: Batch, Memory Limiter, Resource, Attributes, Tail Sampling, Filter
- **Exporters**: OTLP, Prometheus, Jaeger, Elasticsearch, Loki, Kafka, 云平台

### 4. 性能与安全

调整性能参数:

- **批处理大小**: 8192 (生产推荐)
- **内存限制**: Agent 512-1024 MiB, Gateway 2048-4096 MiB
- **压缩算法**: gzip (推荐) 或 zstd (v1.3.0+)

配置安全选项:

- ☑️ 启用TLS加密
- ☑️ 启用Bearer Token认证

### 5. 生成与部署

点击 **"🚀 生成配置"** 按钮,然后:

1. **配置文件** Tab: 复制生成的 `config.yaml`
2. **部署命令** Tab: 复制Kubernetes/Docker部署命令
3. **验证脚本** Tab: 复制验证脚本并运行

---

## 🔧 支持的配置选项

### 部署模式

| 模式 | 描述 | 适用场景 | 资源需求 |
|------|------|----------|----------|
| **Agent** | DaemonSet,每节点一个 | K8s集群,边缘采集 | 512-1024 MiB |
| **Gateway** | 中心化网关 | 集中处理,跨集群 | 2048-4096 MiB |
| **Hybrid** | Agent + Gateway | 大规模生产环境 | 视场景而定 |

### 遥测信号

| 信号 | 支持版本 | 描述 |
|------|----------|------|
| Traces | v1.0.0+ | 分布式链路追踪 |
| Metrics | v1.0.0+ | 时间序列指标 |
| Logs | v1.0.0+ (GA) | 结构化日志 |
| Profiles | v1.3.0+ | 持续性能画像 |

### 接收器 (Receivers)

- ✅ **OTLP** (gRPC + HTTP)
- ✅ **Prometheus** (Scrape)
- ✅ **Jaeger** (gRPC + Thrift HTTP)
- ✅ **Zipkin** (HTTP)

### 处理器 (Processors)

| 处理器 | 必需 | 功能 |
|--------|------|------|
| **Batch** | ✅ | 批处理,提升吞吐 |
| **Memory Limiter** | 推荐 | 防止OOM |
| **Resource** | 可选 | 添加资源属性 |
| **Attributes** | 可选 | 属性处理,脱敏 |
| **Tail Sampling** | 生产推荐 | 智能采样,降低成本 |
| **Filter** | 可选 | 过滤健康检查等 |

### 导出器 (Exporters)

**开源后端**:

- OTLP (标准)
- Prometheus
- Jaeger
- Elasticsearch
- Loki
- Kafka

**云平台**:

- 阿里云 SLS (日志服务)
- 腾讯云 CLS (日志服务)
- 华为云 LTS (日志服务)

### 性能配置

| 参数 | 开发环境 | 生产环境 | 说明 |
|------|----------|----------|------|
| **批处理大小** | 2048 | 8192-16384 | 更大批次=更高吞吐 |
| **内存限制** | 512 MiB | 2048-4096 MiB | 根据负载调整 |
| **压缩算法** | gzip | gzip/zstd | zstd更高压缩率 |

### 安全配置

- ☑️ **TLS加密**: 保护数据传输
- ☑️ **Bearer Token认证**: 防止未授权访问
- ☑️ **数据脱敏**: 自动哈希/移除PII

---

## 📊 生成的文件

生成器会创建以下内容:

### 1. 配置文件 (`config.yaml`)

完整的Collector配置,包括:

```yaml
receivers:      # 数据接收
processors:     # 数据处理
exporters:      # 数据导出
extensions:     # 扩展功能
service:        # Pipeline编排
```

### 2. 部署命令

- **Kubernetes DaemonSet** (Agent模式)
- **Kubernetes Deployment + Service** (Gateway模式)
- **Docker Compose** (单机模式)

### 3. 验证脚本 (`validate.sh`)

自动化验证脚本:

```bash
✅ 配置语法验证
✅ 后端连通性测试
✅ 安全配置检查
✅ 资源需求评估
```

---

## 🎨 界面预览

```text
┌─────────────────────────────────────────────────────────────┐
│         OpenTelemetry Collector 配置生成器                   │
│         快速生成适合您场景的 OTLP Collector 配置文件          │
└─────────────────────────────────────────────────────────────┘

┌───────────────────────┐  ┌──────────────────────────────────┐
│   📝 配置选项          │  │  📄 生成的配置文件                │
│                       │  │                                  │
│  🏗️ 部署模式          │  │  ┌──────┬──────┬──────┐          │
│   ▼ Gateway模式       │  │  │ 120  │  15  │   3  │          │
│                       │  │  │ 行   │ 组件 │Pipeline│         │
│  📊 遥测信号          │  │  └──────┴──────┴──────┘          │
│   ☑️ Traces           │  │                                  │
│   ☑️ Metrics          │  │  [配置文件][部署命令][验证脚本]  │
│   ☑️ Logs             │  │                                  │
│                       │  │  receivers:                      │
│  📥 接收器            │  │    otlp:                         │
│   ☑️ OTLP             │  │      protocols:                  │
│   ☐ Prometheus        │  │        grpc: ...                 │
│                       │  │                                  │
│  ⚙️ 处理器            │  │  [📋 复制配置]                    │
│   ☑️ Batch            │  │                                  │
│   ☑️ Memory Limiter   │  │  💡 建议: 生产环境建议启用TLS     │
│                       │  │                                  │
│  [🚀 生成配置]        │  │                                  │
└───────────────────────┘  └──────────────────────────────────┘
```

---

## 💡 使用场景示例

### 场景1: Kubernetes微服务追踪

**需求**: 追踪K8s集群中的微服务调用链

**配置**:

- 部署模式: `Agent` (DaemonSet)
- 信号: `Traces`, `Metrics`
- Receivers: `OTLP`
- Processors: `Memory Limiter`, `Resource`, `Batch`
- Exporter: `OTLP` → Jaeger/Tempo
- 资源: 512 MiB内存

**生成步骤**:

1. 选择 "Agent模式"
2. 勾选 Traces + Metrics
3. 启用 OTLP Receiver
4. 设置内存限制为 512 MiB
5. 点击生成,部署到K8s

### 场景2: 生产级网关模式

**需求**: 集中处理所有遥测数据,支持采样和过滤

**配置**:

- 部署模式: `Gateway`
- 信号: `Traces`, `Metrics`, `Logs`
- Processors: 全部启用 (包括 Tail Sampling)
- 批处理: 8192
- 内存: 2048 MiB
- 压缩: `gzip`
- 安全: ☑️ TLS + ☑️ Auth

**预期效果**:

- 智能采样,保留错误和慢请求
- 过滤健康检查端点
- 降低90%以上数据量
- TLS加密,认证保护

### 场景3: 开发环境调试

**需求**: 本地开发,查看所有遥测数据

**配置**:

- 部署模式: `Gateway`
- 环境: `Development`
- Exporter: `Logging` (控制台输出)
- 禁用采样
- 启用 zPages 调试页面

**使用方式**:

```bash
docker-compose up
# 访问 http://localhost:55679 查看调试信息
```

### 场景4: 云平台集成 (阿里云)

**需求**: 将遥测数据发送到阿里云SLS

**配置**:

- Exporter: `阿里云SLS`
- Endpoint: `cn-hangzhou.log.aliyuncs.com`
- 环境变量:

  ```bash
  export ALIYUN_SLS_PROJECT=my-project
  export ALIYUN_SLS_LOGSTORE=my-logstore
  export ALIYUN_ACCESS_KEY_ID=xxx
  export ALIYUN_ACCESS_KEY_SECRET=xxx
  ```

---

## 🔍 配置验证

生成配置后,使用验证脚本确保正确性:

```bash
# 1. 保存验证脚本
cat > validate.sh <<'EOF'
# (从"验证脚本"Tab复制内容)
EOF

# 2. 添加执行权限
chmod +x validate.sh

# 3. 运行验证
./validate.sh
```

**验证内容**:

```text
🔍 Validating OpenTelemetry Collector Configuration...
📝 Validating config.yaml syntax...
✅ Configuration syntax is valid
🌐 Testing connectivity to backend...
✅ Backend otel-backend:4317 is reachable
🚀 Starting Collector in dry-run mode...
📊 Resource Requirements:
  Memory Limit: 2048MiB
  Batch Size: 8192
  Compression: gzip
✅ Validation completed successfully!
```

---

## 📚 最佳实践建议

### 资源配置

| 负载级别 | 数据量/秒 | CPU | 内存 | 副本数 |
|---------|-----------|-----|------|--------|
| **小型** | <1K spans | 200m | 512 MiB | 1 |
| **中型** | 1K-10K spans | 500m | 2 GiB | 2-3 |
| **大型** | 10K-100K spans | 2000m | 4 GiB | 3-5 |
| **超大型** | >100K spans | 4000m | 8 GiB | 5+ |

### 批处理优化

```yaml
# 推荐配置
batch:
  timeout: 10s              # 最大延迟
  send_batch_size: 8192     # 正常批次
  send_batch_max_size: 16384 # 突发批次
```

**效果**:

- 减少网络请求数 ~95%
- 提升压缩效率 ~30%
- 降低CPU使用 ~50%

### 采样策略

生产环境推荐使用 **尾部采样 (Tail Sampling)**:

```yaml
tail_sampling:
  policies:
    - name: errors          # 保留所有错误
      type: status_code
      status_code: {status_codes: [ERROR]}
    
    - name: slow            # 保留慢请求 (>500ms)
      type: latency
      latency: {threshold_ms: 500}
    
    - name: normal          # 采样10%正常流量
      type: probabilistic
      probabilistic: {sampling_percentage: 10}
```

**成本节约**:

- 保留100%错误 + 100%慢请求
- 仅10%正常流量
- **总体数据量降低 ~90%**

### 安全加固

生产环境 **必须** 启用:

1. **TLS加密**:

   ```yaml
   tls:
     insecure: false
     cert_file: /etc/otel/certs/client.crt
     key_file: /etc/otel/certs/client.key
     ca_file: /etc/otel/certs/ca.crt
   ```

2. **认证**:

   ```yaml
   headers:
     authorization: "Bearer ${OTEL_AUTH_TOKEN}"
   ```

3. **数据脱敏**:

   ```yaml
   attributes:
     actions:
       - key: http.url
         pattern: "(password|token)=([^&]+)"
         replacement: "$1=***"
         action: update
   ```

---

## 🐛 故障排查

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| 配置验证失败 | YAML语法错误 | 检查缩进和字段名 |
| 无法连接后端 | 端点地址错误 | 验证 `endpoint` 配置 |
| OOM (内存溢出) | 内存限制不足 | 增加 `limit_mib` 或启用采样 |
| 数据丢失 | 批处理超时 | 减少 `send_batch_size` |
| CPU使用率高 | 批处理太小 | 增加 `send_batch_size` 到 8192+ |
| TLS连接失败 | 证书路径错误 | 检查 `cert_file` 路径 |

**诊断命令**:

```bash
# 查看Collector日志
kubectl logs -n observability -l app=otel-collector

# 检查健康状态
curl http://localhost:13133

# 查看内部指标
curl http://localhost:8888/metrics
```

---

## 🔄 更新日志

### v1.0.0 (2025-10-09)

**初始版本**:

- ✅ 支持 OTLP v1.3.0 所有特性
- ✅ Profiles信号支持 (v1.3.0新增)
- ✅ zstd压缩支持 (v1.3.0新增)
- ✅ 3种部署模式: Agent, Gateway, Hybrid
- ✅ 10+ Exporters,包括3大云平台
- ✅ 智能配置推荐
- ✅ 一键生成部署清单
- ✅ 自动化验证脚本

---

## 📖 相关文档

- [OTLP协议速查手册](../../速查手册/01_OTLP协议速查手册.md)
- [Collector配置速查手册](../../速查手册/03_Collector配置速查手册.md)
- [性能优化速查手册](../../速查手册/05_性能优化速查手册.md)
- [安全配置速查手册](../../速查手册/06_安全配置速查手册.md)
- [阿里云OTLP集成指南](../../云平台集成/01_阿里云OTLP集成指南.md)
- [腾讯云OTLP集成指南](../../云平台集成/02_腾讯云OTLP集成指南.md)
- [华为云OTLP集成指南](../../云平台集成/03_华为云OTLP集成指南.md)

---

## 🤝 贡献指南

欢迎提交问题和改进建议!

**改进方向**:

- 🔧 添加更多Receiver/Exporter支持
- 📊 可视化Pipeline编辑器
- 🧪 配置模板库
- 🌐 多语言支持 (英文版)
- 📱 响应式设计优化

---

## 📄 许可证

本工具为开源项目,遵循 **MIT License**。

---

**🎉 快速开始使用配置生成器,3分钟生成生产级Collector配置!**

```bash
cd 标准深度梳理_2025_10/工具/config-generator/
open index.html  # 或 start index.html (Windows)
```

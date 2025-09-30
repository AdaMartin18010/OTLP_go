# OTLP_go

OTLP golang

## 目录

- [OTLP\_go](#otlp_go)
  - [目录](#目录)
  - [文档导航](#文档导航)
    - [核心文档](#核心文档)
    - [语言与生态](#语言与生态)
    - [深度分析论证](#深度分析论证)
    - [实践指南](#实践指南)
  - [运行示例](#运行示例)
  - [本机一键运行](#本机一键运行)
  - [容器与编排（可选）](#容器与编排可选)
  - [关停与优雅退出](#关停与优雅退出)
  - [形式化验证（可选）](#形式化验证可选)

## 文档导航

### 核心文档

- 文档索引：`docs/00_index.md`
- **综合技术分析报告**：`docs/analysis/comprehensive-analysis.md`
- **CSP × OTLP × 分布式（总览）**：`docs/analysis/csp-otlp/overview.md`

### 语言与生态

- Go 1.25.1 语言特性：`docs/language/go-1.25.1.md`
- OTLP 语义模型：`docs/otlp/semantic-model.md`
- Golang OTLP 生态映射：`docs/otlp/libraries.md`
- Golang × OTLP 开源库选型：`docs/otlp/golang-libraries.md`

### 深度分析论证

- **语义模型分析**：`docs/analysis/semantic-analysis/`
- **技术模型设计**：`docs/analysis/technical-model/`
- **分布式模型论证**：`docs/analysis/distributed-model/`
- **形式化证明**：`docs/analysis/formal-proofs/`
- **生态映射分析**：`docs/analysis/ecosystem-mapping/`
- **CSP × OTLP 体系化整合**：`docs/analysis/csp-otlp/`
- 语言与语义映射：`docs/analysis/csp-otlp/language-semantics.md`
- 技术整合与库选型：`docs/analysis/csp-otlp/technical-integration.md`
- 分布式设计：`docs/analysis/csp-otlp/distributed-design.md`
- 形式化与验证：`docs/analysis/csp-otlp/formalization.md`

### 实践指南

- OTTL 示例与最佳实践：`docs/otlp/ottl-examples.md`
- 高级 Collector 配置（含 OTTL/采样/路由）：`configs/collector-advanced.yaml`
- OPAMP 样例与流程：`docs/opamp/sample.md`
- 技术/分布式/形式化：见 `docs/design/`
- Profiles（eBPF 连续性能分析）：`docs/profiles/overview.md`
- OPAMP 控制面概览：`docs/opamp/overview.md`

## 运行示例

1. 启动 Collector（本地日志导出）：

    ```bash
    otelcol --config configs/collector.yaml
    ```

2. 运行示例服务（需 Go 1.25.1）：

    ```bash
    set OTLP_GRPC_ENDPOINT=127.0.0.1:4317
    go run ./src
    ```

3. 访问：`http://localhost:8080/hello`，在 Collector 控制台看到 Trace 与 Metrics 输出。

- 健康检查：`http://localhost:8080/healthz` 返回 `ok`。

- 指标输出：示例会每秒上报 `demo.requests` 计数器，Collector 控制台会打印 metrics 日志（通过 `logging` exporter）。

- 日志输出：服务启动与每次请求通过标准库 `slog` 打印到 stdout，可由容器/sidecar/Agent 采集；Collector 默认管道仅演示 traces/metrics。

## 本机一键运行

- Collector: 双击或在 PowerShell 执行 `./run-collector.ps1`
- App: 双击或在 PowerShell 执行 `./run-app.ps1`
- 一键启动：`./run-all.ps1`（先拉起 Collector，再拉起 App）

## 容器与编排（可选）

- 构建与启动：`./run-docker.ps1 up`
- 查看日志：`./run-docker.ps1 logs`
- 停止并清理：`./run-docker.ps1 down`

说明：`docker-compose.yml` 使用本地 `configs/collector.yaml`，App 通过环境变量连接 `collector:4317`。

## 关停与优雅退出

- 在 App 窗口按 Ctrl+C，服务将优雅关闭 HTTP，并调用 OTel 提供者 Shutdown 确保 flush。

## 形式化验证（可选）

- 安装 TLA+ Tools (TLC)，在 IDE 中打开 `docs/formal/tla/pipeline.tla`
- 使用配置 `docs/formal/tla/pipeline.cfg` 运行模型检查

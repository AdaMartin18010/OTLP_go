# OTLP_go

OTLP golang

## 文档导航

- 文档索引：`docs/00_index.md`
- Go 1.25.1 语言特性：`docs/language/go-1.25.1.md`
- OTLP 语义模型：`docs/otlp/semantic-model.md`
- Golang OTLP 生态映射：`docs/otlp/libraries.md`
- 技术/分布式/形式化：见 `docs/design/`

- OTTL 示例与最佳实践：`docs/otlp/ottl-examples.md`
- 高级 Collector 配置（含 OTTL/采样/路由）：`configs/collector-advanced.yaml`
- OPAMP 样例与流程：`docs/opamp/sample.md`

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

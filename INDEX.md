# OTLP Go 项目索引

## 📚 文档导航

### 核心文档

- [README.md](README.md) - 项目介绍
- [PROJECT_OVERVIEW.md](PROJECT_OVERVIEW.md) - 项目概览
- [ARCHITECTURE.md](ARCHITECTURE.md) - 架构设计
- [WORKSPACE.md](WORKSPACE.md) - Workspace 使用指南

### 开发文档

- [Makefile](Makefile) - 构建命令
- [dev.ps1](dev.ps1) - 开发脚本
- [stats.ps1](stats.ps1) - 统计脚本
- [check_quality.ps1](check_quality.ps1) - 质量检查

### 示例代码

- [examples/basic](examples/basic/) - 基础示例
- [examples/logs-sdk](examples/logs-sdk/) - 日志 SDK 示例
- [examples/metrics](examples/metrics/) - 指标示例
- [examples/microservices](examples/microservices/) - 微服务示例

### 核心包

- [pkg/logs](pkg/logs/) - 日志 SDK
- [pkg/otel](pkg/otel/) - OpenTelemetry 管理
- [pkg/concurrency](pkg/concurrency/) - 并发工具
- [pkg/config](pkg/config/) - 配置管理

## 🚀 快速链接

```bash
# 开始使用
go run examples/basic/main.go

# 运行测试
go test ./...

# 构建项目
go build ./...
```

## 📊 项目状态

- Go 版本: 1.26
- OpenTelemetry: v1.42.0
- 模块数: 36
- 状态: ✅ 生产就绪

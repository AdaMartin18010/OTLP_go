# OTLP Go 项目概览

## 项目状态

![Build Status](https://img.shields.io/badge/build-passing-brightgreen)
![Tests](https://img.shields.io/badge/tests-passing-brightgreen)
![Go Version](https://img.shields.io/badge/go-1.26-blue)
![OpenTelemetry](https://img.shields.io/badge/opentelemetry-v1.42.0-blue)

## 快速开始

```bash
# 构建项目
make build

# 运行测试
make test

# 运行示例
make example-logs

# 检查代码质量
./check_quality.ps1
```

## 项目结构

```
OTLP_go/
├── pkg/                    # 核心包模块
│   ├── automation/         # CI/CD 自动化
│   ├── concurrency/        # 并发工具
│   ├── config/            # 配置管理
│   ├── context/           # 上下文传播
│   ├── errors/            # 错误处理
│   ├── logs/              # 日志 SDK (新增)
│   ├── otel/              # OpenTelemetry 管理
│   ├── pool/              # 对象池
│   ├── security/          # 安全
│   └── ...
├── examples/              # 示例程序
│   ├── basic/             # 基础示例
│   ├── logs-sdk/          # 日志 SDK 示例
│   └── ...
├── src/                   # 应用源码
├── docs/                  # 文档
└── .github/workflows/     # CI/CD 配置
```

## 特性

- ✅ **Traces** - 完整分布式链路追踪
- ✅ **Metrics** - 指标收集和导出
- ✅ **Logs** - 结构化日志 SDK
- ✅ **Batch Processing** - 高性能批量处理
- ✅ **TLS Security** - 安全传输
- ✅ **Go 1.26** - 最新 Go 版本支持

## 模块数量

- 总模块数: 36
- 核心包: 16
- 示例程序: 16
- 应用模块: 4

## 代码统计

- Go 文件: 76
- 代码行数: ~33,000
- 测试文件: 19
- 测试覆盖率: 持续改进中

## 开发工具

```bash
# 开发脚本
./dev.ps1 build    # 构建
./dev.ps1 test     # 测试
./dev.ps1 tidy     # 整理依赖
./dev.ps1 example  # 运行示例

# 统计信息
./stats.ps1        # 项目统计

# 质量检查
./check_quality.ps1  # 全面检查
```

## 贡献

欢迎提交 Issue 和 PR！

## 许可证

MIT License

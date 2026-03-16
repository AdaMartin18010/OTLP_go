# Go Workspace 使用指南

本项目使用 **Go 1.26 Workspace** 模式管理多模块结构，支持独立发布、版本管理和本地开发。

## 📁 项目结构

```
OTLP_go/
├── go.work              # Workspace 定义文件
├── go.mod               # 核心 SDK 模块
├── WORKSPACE.md         # 本文档
│
├── pkg/                 # 独立子包模块 (可单独发布)
│   ├── automation/      # CI/CD 自动化
│   ├── concurrency/     # 并发工具
│   ├── config/          # 配置管理
│   ├── context/         # 上下文传播
│   ├── errors/          # 错误处理
│   ├── options/         # 选项模式
│   ├── otel/            # OpenTelemetry 管理
│   ├── performance/     # 性能优化
│   ├── pool/            # 对象池
│   ├── profiling/       # 性能分析
│   ├── resource/        # 资源管理
│   ├── runtime/         # 运行时
│   ├── security/        # 安全
│   ├── shutdown/        # 优雅关闭
│   ├── testing/         # 测试工具
│   └── types/           # 类型定义
│
├── examples/            # 示例程序 (各自独立模块)
│   ├── basic/
│   ├── logs/
│   ├── metrics/
│   ├── microservices/
│   └── ...
│
└── src/                 # 核心源码 (主模块)
    ├── main.go
    ├── metrics.go
    ├── logs.go
    └── pipeline.go
```

## 🚀 快速开始

### 1. 查看所有模块

```bash
go list -m all
```

### 2. 构建所有模块

```bash
# 构建 workspace 中所有模块
go build ./...

# 构建特定模块
go build OTLP_go/pkg/otel
go build OTLP_go/examples/basic
```

### 3. 测试所有模块

```bash
# 测试所有子包
go test -race OTLP_go/pkg/...

# 测试特定模块
go test -race OTLP_go/pkg/concurrency

# 测试覆盖率
go test -cover OTLP_go/pkg/...
```

### 4. 同步依赖版本

```bash
# 当任何模块的 go.mod 修改后，同步所有模块的依赖版本
go work sync
```

### 5. 添加新模块到 Workspace

```bash
# 创建新模块目录
mkdir -p pkg/newmodule
cd pkg/newmodule
go mod init OTLP_go/pkg/newmodule

# 添加到 workspace
cd ../..
go work use ./pkg/newmodule
```

## 📦 模块引用

### 在同一 Workspace 内引用

直接导入模块路径：

```go
import (
    "OTLP_go/pkg/config"
    "OTLP_go/pkg/otel"
    "OTLP_go/pkg/shutdown"
)
```

### 外部项目引用

发布到 GitHub 后，外部项目可以引用：

```go
import "github.com/yourusername/otlp-go/pkg/config"
```

在 go.mod 中：

```go
require github.com/yourusername/otlp-go/pkg/config v1.0.0
```

## 🔧 Workspace 命令速查

| 命令 | 说明 |
|------|------|
| `go work sync` | 同步所有模块依赖版本 |
| `go work use <path>` | 添加模块到 workspace |
| `go work edit -dropuse <path>` | 从 workspace 移除模块 |
| `go list -m all` | 列出所有模块 |
| `go list -m -json all` | JSON 格式列出模块详情 |

## 🔄 依赖管理

### 统一版本控制

Workspace 会自动协调所有模块的依赖版本：

```bash
# 修改根模块依赖
go get go.opentelemetry.io/otel@v1.32.0

# 同步到所有模块
go work sync
```

### 模块独立版本

每个子包可以独立管理版本：

```bash
cd pkg/config
go get github.com/some/lib@v2.0.0
cd ../..
go work sync
```

## 🛠️ 开发工作流

### 场景 1：修改子包并在主模块测试

```bash
# 1. 修改 pkg/config/config.go
# 2. 直接构建主模块（会自动使用本地修改）
go build ./src/...

# 3. 运行测试
go test -race OTLP_go/pkg/config
```

### 场景 2：发布子包新版本

```bash
cd pkg/config

# 提交修改
git add .
git commit -m "feat: add new config option"

# 打标签（独立版本）
git tag pkg/config/v1.2.0
git push origin pkg/config/v1.2.0
```

### 场景 3：添加新示例

```bash
# 创建示例目录
mkdir -p examples/my-example
cd examples/my-example

# 初始化模块
go mod init OTLP_go/examples/my-example

# 添加核心 SDK 依赖
go get OTLP_go@latest

# 回到根目录添加 workspace
cd ../..
go work use ./examples/my-example
```

## 📋 CI/CD 集成

### GitHub Actions

```yaml
name: Test Workspace
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: actions/setup-go@v5
        with:
          go-version: '1.26'
      
      - name: Sync workspace
        run: go work sync
      
      - name: Build all modules
        run: go build ./...
      
      - name: Test all modules
        run: go test -race ./...
```

## 🎯 设计优势

1. **独立演进**: 子包可以独立发布版本，不影响其他模块
2. **清晰边界**: 每个模块职责明确，降低耦合
3. **本地开发**: 修改子包立即反映到引用它的模块
4. **依赖对齐**: `go work sync` 自动统一依赖版本
5. **按需引用**: 外部项目只需引用需要的子包，不用导入整个 SDK

## ❓ 常见问题

### Q: 为什么子包在 pkg/ 而不是 src/pkg/?

A: Go Workspace 的最佳实践是将可独立发布的包放在顶层，与主模块分离。`pkg/` 是 Go 社区约定的可公开导入包目录。

### Q: 如何引用本地未发布的模块？

A: Workspace 自动处理本地引用，无需 replace 指令。

### Q: 子包可以有自己的 go.sum 吗？

A: 是的，每个子包维护自己的 go.sum，但依赖版本由 workspace 协调。

### Q: 如何移除不再使用的子包？

```bash
go work edit -dropuse ./pkg/oldmodule
rm -rf pkg/oldmodule
```

## 📚 参考文档

- [Go Workspace 官方文档](https://go.dev/ref/mod#workspaces)
- [Go Modules 参考](https://go.dev/ref/mod)
- [多模块仓库最佳实践](https://go.dev/doc/modules/managing-source#multiple-module-source)

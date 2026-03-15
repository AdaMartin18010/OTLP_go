# OTLP Go SDK - Scripts

此目录包含用于构建、测试和代码检查的跨平台脚本。

## 脚本列表

| 脚本 | 用途 | 使用方式 |
|------|------|----------|
| `test.sh` | 运行测试套件 | `./test.sh [options]` |
| `build.sh` | 构建项目 | `./build.sh [options]` |
| `lint.sh` | 代码质量检查 | `./lint.sh [options]` |

## 快速开始

```bash
# 运行所有测试
./scripts/test.sh

# 构建项目
./scripts/build.sh

# 运行代码检查
./scripts/lint.sh

# 构建发布版本
./scripts/build.sh --release

# 运行测试并生成覆盖率报告
./scripts/test.sh --coverage

# 自动修复代码格式问题
./scripts/lint.sh --fix
```

## 跨平台支持

这些脚本支持以下平台：

- **Linux**: Bash 4.0+
- **macOS**: Bash 3.2+ (预装)
- **Windows**: Git Bash, WSL, Cygwin, MSYS2

## 详细说明

### test.sh

运行项目测试套件，支持多种选项：

```bash
./test.sh [OPTIONS]

Options:
    -h, --help          显示帮助
    -c, --coverage      生成覆盖率报告
    -b, --benchmark     运行基准测试
    -s, --short         运行短测试
    -v, --verbose       详细输出
    -m, --module MOD    测试指定模块
    --no-race           禁用竞争检测
```

### build.sh

构建项目，支持多平台交叉编译：

```bash
./build.sh [OPTIONS]

Options:
    -h, --help          显示帮助
    -t, --type TYPE     构建类型: debug|release
    -o, --os OS         目标操作系统
    -a, --arch ARCH     目标架构
    -c, --clean         清理构建
    -s, --skip-tests    跳过测试
    -e, --examples      构建示例程序
    -r, --release       构建发布版本
    -v, --verbose       详细输出
```

### lint.sh

运行代码质量检查和格式化：

```bash
./lint.sh [OPTIONS]

Options:
    -h, --help          显示帮助
    -f, --fix           自动修复问题
    -v, --verbose       详细输出
    --no-fmt            跳过 gofmt
    --no-vet            跳过 go vet
    --no-golangci       跳过 golangci-lint
    --no-staticcheck    跳过 staticcheck
    --vulncheck         运行漏洞检查
    -m, --module MOD    检查指定模块
```

## 环境要求

- Go 1.26 或更高版本
- Bash 3.2 或更高版本
- 可选工具（会自动安装）：
  - golangci-lint
  - staticcheck
  - govulncheck

## Windows 用户注意事项

### Git Bash
在 Git Bash 中直接运行脚本：
```bash
./scripts/test.sh
```

### PowerShell
使用 WSL 或 Git Bash：
```powershell
# 使用 WSL
wsl ./scripts/test.sh

# 或使用 Git Bash
"C:\Program Files\Git\bin\bash.exe" ./scripts/test.sh
```

### CMD
```cmd
"C:\Program Files\Git\bin\bash.exe" scripts\test.sh
```

## 与 Makefile 的集成

这些脚本也可以通过 Makefile 调用：

```bash
# 使用脚本运行测试
make run-script SCRIPT=test

# 使用脚本构建
make run-script SCRIPT=build

# 使用脚本检查代码
make run-script SCRIPT=lint
```

或者使用 Makefile 的原生命令：

```bash
make test      # 运行测试
make build     # 构建项目
make lint      # 代码检查
make coverage  # 覆盖率报告
```

## 故障排除

### 权限问题

如果脚本无法执行，请添加执行权限：

```bash
chmod +x scripts/*.sh
```

### 行尾问题 (Windows)

如果在 Windows 上遇到 `^M: bad interpreter` 错误，转换行尾：

```bash
dos2unix scripts/*.sh
```

或使用 Git：
```bash
git config --global core.autocrlf input
```

### 找不到 Go

确保 Go 已安装并在 PATH 中：

```bash
go version
```

## 持续集成

这些脚本设计用于 CI/CD 环境。示例 GitHub Actions 配置：

```yaml
name: CI
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: actions/setup-go@v4
        with:
          go-version: '1.26'
      - run: ./scripts/test.sh --coverage
      - run: ./scripts/lint.sh
      - run: ./scripts/build.sh --type release
```

## 许可证

与项目主许可证相同。

# 贡献指南

感谢您对 OTLP_go 项目的关注！我们欢迎各种形式的贡献。

---

## 📋 目录

- [行为准则](#行为准则)
- [如何贡献](#如何贡献)
- [开发环境设置](#开发环境设置)
- [代码规范](#代码规范)
- [提交规范](#提交规范)
- [Pull Request 流程](#pull-request-流程)
- [问题报告](#问题报告)

---

## 行为准则

本项目遵循 [Contributor Covenant](https://www.contributor-covenant.org/) 行为准则。参与本项目即表示您同意遵守其条款。

---

## 如何贡献

### 贡献类型

我们欢迎以下类型的贡献：

- 🐛 **Bug 修复**: 修复代码中的错误
- ✨ **新功能**: 添加新的示例或功能
- 📝 **文档改进**: 改进或补充文档
- 🎨 **代码优化**: 性能优化或代码重构
- 🧪 **测试**: 添加或改进测试用例
- 🌐 **翻译**: 文档翻译

---

## 开发环境设置

### 前置要求

- **Go**: 1.25.1 或更高版本
- **Docker**: 用于运行 OTLP Collector 和 Jaeger
- **Make**: 用于运行构建脚本
- **Git**: 版本控制

### 设置步骤

1. **Fork 项目**

    ```bash
    # 在 GitHub 上 Fork 项目
    # 然后克隆到本地
    git clone https://github.com/YOUR_USERNAME/OTLP_go.git
    cd OTLP_go
    ```

2. **安装依赖**

    ```bash
    # 下载 Go 依赖
    make mod-download

    # 安装开发工具
    make install-tools
    ```

3. **启动服务**

    ```bash
    # 启动 OTLP Collector 和 Jaeger
    make docker-up
    ```

4. **运行测试**

    ```bash
    # 运行所有测试
    make test

    # 运行基准测试
    make bench
    ```

---

## 代码规范

### Go 代码风格

遵循官方 [Go Code Review Comments](https://github.com/golang/go/wiki/CodeReviewComments)。

**关键点**:

- 使用 `gofmt` 格式化代码
- 使用有意义的变量名
- 添加必要的注释
- 导出的函数和类型必须有文档注释
- 错误处理要完整

**示例**:

```go
// GoodExample demonstrates proper Go code style
func GoodExample(ctx context.Context, name string) error {
    if name == "" {
        return errors.New("name cannot be empty")
    }

    // Process the name
    result, err := processName(ctx, name)
    if err != nil {
        return fmt.Errorf("failed to process name: %w", err)
    }

    log.Printf("Processed: %s", result)
    return nil
}
```

### 文档规范

- 使用 Markdown 格式
- 添加目录（超过 3 个章节）
- 包含代码示例
- 添加运行说明
- 包含输出示例

---

## 提交规范

### Commit Message 格式

使用 [Conventional Commits](https://www.conventionalcommits.org/) 规范：

```text
<type>(<scope>): <subject>

<body>

<footer>
```

**类型 (type)**:

- `feat`: 新功能
- `fix`: Bug 修复
- `docs`: 文档更新
- `style`: 代码格式（不影响功能）
- `refactor`: 代码重构
- `perf`: 性能优化
- `test`: 测试相关
- `chore`: 构建/工具相关

**示例**:

```text
feat(examples): add distributed tracing example

Add a complete distributed tracing example demonstrating:
- API Gateway
- Order Service
- Payment Service
- Inventory Service

Closes #123
```

---

## Pull Request 流程

### 1. 创建分支

```bash
# 从 main 创建功能分支
git checkout -b feature/your-feature-name

# 或修复分支
git checkout -b fix/your-bug-fix
```

### 2. 开发和测试

```bash
# 开发您的功能
# ...

# 运行测试
make test

# 运行代码检查
make lint

# 格式化代码
make fmt
```

### 3. 提交更改

```bash
# 添加更改
git add .

# 提交（遵循提交规范）
git commit -m "feat(scope): description"

# 推送到您的 Fork
git push origin feature/your-feature-name
```

### 4. 创建 Pull Request

1. 在 GitHub 上打开 Pull Request
2. 填写 PR 模板
3. 等待 CI 检查通过
4. 等待代码审查

### PR 检查清单

- [ ] 代码遵循项目规范
- [ ] 添加了必要的测试
- [ ] 所有测试通过
- [ ] 更新了相关文档
- [ ] Commit message 符合规范
- [ ] 没有合并冲突

---

## 问题报告

### Bug 报告

使用 Bug 报告模板，包含：

- **环境信息**: Go 版本、OS、Docker 版本
- **重现步骤**: 详细的步骤
- **预期行为**: 应该发生什么
- **实际行为**: 实际发生了什么
- **日志/截图**: 相关的错误信息

**示例**:

```markdown
    **环境**:
    - Go: 1.25.1
    - OS: Ubuntu 20.04
    - Docker: 24.0.0

    **重现步骤**:
    1. 运行 `make docker-up`
    2. 运行 `cd examples/basic && go run main.go`
    3. 观察错误

    **预期**: 示例成功运行
    **实际**: 连接被拒绝

    **日志**:
    ```text

    Error: connection refused to localhost:4317

    ```
```

### 功能请求

包含：

- **功能描述**: 清晰描述新功能
- **使用场景**: 为什么需要这个功能
- **建议实现**: 如何实现（可选）
- **替代方案**: 其他可能的方案

---

## 代码审查

### 审查标准

- **功能性**: 代码是否正确实现功能
- **可读性**: 代码是否易于理解
- **性能**: 是否有性能问题
- **测试**: 测试是否充分
- **文档**: 文档是否完整

### 审查流程

1. 自动化检查（CI）
2. 代码审查（至少 1 个维护者）
3. 测试验证
4. 合并到 main

---

## 开发技巧

### 运行单个示例

```bash
cd examples/basic
go run main.go
```

### 运行特定测试

```bash
cd benchmarks
go test -run TestSpanCreation
```

### 查看 Collector 日志

```bash
docker logs -f otel-collector
```

### 调试追踪

```bash
# 访问 Jaeger UI
open http://localhost:16686
```

---

## 获取帮助

- **文档**: 查看 [docs/](./docs/) 目录
- **示例**: 查看 [examples/](./examples/) 目录
- **问题**: 提交 GitHub Issue
- **讨论**: 使用 GitHub Discussions

---

## 许可证

贡献的代码将采用与项目相同的许可证（见 [LICENSE](./LICENSE)）。

---

**感谢您的贡献！** 🎉

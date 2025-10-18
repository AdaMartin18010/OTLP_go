# 🤝 贡献指南

感谢您对 **OTLP Go技术栈深度梳理** 项目的关注！本文档将帮助您了解如何为项目做出贡献。

---

## 📋 目录

- [贡献类型](#贡献类型)
- [开始之前](#开始之前)
- [贡献流程](#贡献流程)
- [代码规范](#代码规范)
- [文档规范](#文档规范)
- [提交规范](#提交规范)
- [审核流程](#审核流程)

---

## 🎯 贡献类型

我们欢迎以下类型的贡献：

### 1. 📝 文档改进
- 修正拼写错误、语法错误
- 补充缺失的说明
- 改进文档结构和可读性
- 添加更多实战案例

### 2. 💻 代码示例
- 新增完整的代码示例
- 改进现有示例的质量
- 添加更多注释和说明
- 补充单元测试

### 3. 🐛 问题修复
- 修复代码错误
- 修复配置错误
- 修复文档中的技术错误

### 4. 🌟 新特性
- 新增技术领域的深度梳理
- 补充缺失的最佳实践
- 添加生产环境案例

### 5. 📊 性能测试
- 补充基准测试
- 验证优化效果
- 提供性能对比数据

---

## 🚀 开始之前

### 前置要求

1. **环境准备**
   - Go 1.25.1+
   - Git
   - VSCode/GoLand (推荐)

2. **了解项目**
   - 阅读 [README.md](README.md)
   - 浏览 [项目导航中心](标准深度梳理_2025_10/📍_Go语言项目导航中心_2025-Q4.md)
   - 查看 [项目看板](标准深度梳理_2025_10/📊_项目持续推进看板_2025-Q4.md)

3. **检查现有Issue**
   - 搜索是否已有相关Issue
   - 避免重复工作

---

## 🔄 贡献流程

### 1. Fork 项目

点击 GitHub 页面右上角的 **Fork** 按钮

### 2. 克隆到本地

```bash
git clone https://github.com/YOUR_USERNAME/OTLP_go.git
cd OTLP_go
```

### 3. 创建分支

```bash
# 文档改进
git checkout -b docs/improve-ebpf-guide

# 代码示例
git checkout -b feat/add-grpc-example

# 问题修复
git checkout -b fix/correct-k8s-yaml

# 性能测试
git checkout -b test/benchmark-sharded-lock
```

### 4. 进行修改

#### 文档修改
```bash
# 编辑文档
vim 标准深度梳理_2025_10/🐝_Go_eBPF深度集成指南_零侵入式可观测性.md

# 预览效果（使用Markdown预览工具）
```

#### 代码修改
```bash
# 编辑代码
vim examples/otlp-basic/main.go

# 格式化
gofmt -w examples/otlp-basic/main.go

# 运行测试
go test ./examples/otlp-basic/...
```

### 5. 提交更改

```bash
# 添加修改
git add .

# 提交（遵循提交规范）
git commit -m "docs: 补充eBPF Ring Buffer使用说明"

# 推送到远程
git push origin docs/improve-ebpf-guide
```

### 6. 创建Pull Request

1. 访问您的Fork仓库页面
2. 点击 **New Pull Request**
3. 填写PR标题和描述（参考模板）
4. 提交PR

---

## 📐 代码规范

### Go代码规范

#### 1. 格式化

```bash
# 使用gofmt格式化
gofmt -w .

# 或使用goimports（推荐）
goimports -w .
```

#### 2. 代码检查

```bash
# 运行golangci-lint
golangci-lint run --timeout 5m

# 竞态检测
go test -race ./...
```

#### 3. 注释规范

```go
// ✅ 正确：包注释
// Package telemetry 提供OpenTelemetry集成功能
package telemetry

// ✅ 正确：函数注释
// InitOTLP 初始化OpenTelemetry Pipeline
// 返回shutdown函数用于优雅关闭
func InitOTLP(ctx context.Context, cfg OTLPConfig) (func(context.Context) error, error) {
    // 实现...
}

// ✅ 正确：复杂逻辑注释
func processData(data []byte) error {
    // 步骤1: 验证数据格式
    if err := validate(data); err != nil {
        return err
    }
    
    // 步骤2: 解析数据
    parsed, err := parse(data)
    if err != nil {
        return err
    }
    
    // 步骤3: 处理业务逻辑
    return handle(parsed)
}
```

#### 4. 错误处理

```go
// ✅ 正确：使用fmt.Errorf包装错误
if err := doSomething(); err != nil {
    return fmt.Errorf("failed to do something: %w", err)
}

// ❌ 错误：不包装错误
if err := doSomething(); err != nil {
    return err
}
```

#### 5. 单元测试

```go
// ✅ 正确：表驱动测试
func TestAdd(t *testing.T) {
    tests := []struct {
        name string
        a    int
        b    int
        want int
    }{
        {"positive", 1, 2, 3},
        {"negative", -1, -2, -3},
        {"zero", 0, 0, 0},
    }
    
    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            got := Add(tt.a, tt.b)
            if got != tt.want {
                t.Errorf("Add(%d, %d) = %d; want %d", tt.a, tt.b, got, tt.want)
            }
        })
    }
}
```

---

## 📝 文档规范

### Markdown规范

#### 1. 标题层级

```markdown
# H1 - 文档标题（仅一个）
## H2 - 章节
### H3 - 小节
#### H4 - 子小节
```

#### 2. 代码块

````markdown
```go
// 指定语言以启用语法高亮
func main() {
    fmt.Println("Hello, World!")
}
```
````

#### 3. 表格

```markdown
| 列1 | 列2 | 列3 |
|-----|-----|-----|
| 值1 | 值2 | 值3 |
```

#### 4. 链接

```markdown
# 文档内链接
[相关章节](#章节锚点)

# 其他文档链接
[eBPF指南](标准深度梳理_2025_10/🐝_Go_eBPF深度集成指南_零侵入式可观测性.md)

# 外部链接
[Go官方文档](https://go.dev/doc/)
```

#### 5. 列表

```markdown
# 无序列表
- 项目1
- 项目2
  - 子项目2.1
  - 子项目2.2

# 有序列表
1. 第一步
2. 第二步
3. 第三步

# 任务列表
- [x] 已完成
- [ ] 待完成
```

---

## 💬 提交规范

### Commit Message格式

```
<type>(<scope>): <subject>

<body>

<footer>
```

### Type类型

- `feat`: 新功能
- `fix`: 修复问题
- `docs`: 文档修改
- `style`: 格式修改（不影响代码逻辑）
- `refactor`: 重构
- `test`: 测试相关
- `chore`: 构建/工具相关

### 示例

```bash
# 文档修改
git commit -m "docs: 补充Kubernetes HPA配置说明"

# 新增功能
git commit -m "feat: 添加gRPC追踪示例代码"

# 修复问题
git commit -m "fix: 修正Dockerfile中的构建参数"

# 测试
git commit -m "test: 添加分片锁性能基准测试"
```

---

## 🔍 审核流程

### Pull Request检查清单

提交PR前，请确认：

- [ ] 代码通过 `gofmt` 格式化
- [ ] 代码通过 `golangci-lint` 检查
- [ ] 所有测试通过 `go test ./...`
- [ ] 通过竞态检测 `go test -race ./...`
- [ ] 文档更新（如需要）
- [ ] 添加必要的注释
- [ ] 提交消息符合规范

### 审核标准

我们将从以下方面审核PR：

1. **代码质量**
   - 遵循Go最佳实践
   - 代码简洁易读
   - 适当的错误处理

2. **文档质量**
   - 内容准确无误
   - 结构清晰
   - 示例完整可运行

3. **测试覆盖**
   - 单元测试覆盖率 > 80%
   - 关键路径有测试
   - 边界情况考虑

4. **性能影响**
   - 无明显性能退化
   - 有性能测试数据支持

---

## 🎯 优先级指南

我们特别欢迎以下类型的贡献：

### 高优先级 ⭐⭐⭐

- 修复技术错误
- 补充生产环境案例
- 添加性能基准测试
- 改进代码示例质量

### 中优先级 ⭐⭐

- 补充文档说明
- 新增代码示例
- 文档格式优化

### 低优先级 ⭐

- 拼写错误修正
- 样式调整

---

## ❓ 常见问题

### 1. 我的PR被拒绝了怎么办？

不要气馁！查看审核意见，根据反馈修改后重新提交。

### 2. 我不确定我的想法是否合适？

先创建一个Issue讨论您的想法，获得反馈后再开始编码。

### 3. 我只想修改一个拼写错误，也需要这么复杂的流程吗？

对于小修改，可以简化流程，但仍需遵循基本的提交规范。

### 4. 代码审核需要多长时间？

通常在3-7个工作日内完成审核。紧急修复会优先处理。

---

## 📞 联系我们

如有任何问题，欢迎通过以下方式联系：

- **GitHub Issues**: 提交Issue讨论
- **GitHub Discussions**: 参与社区讨论
- **Email**: platform@example.com

---

## 🙏 感谢

感谢所有为本项目做出贡献的开发者！

您的每一个贡献都让这个项目变得更好 ❤️

---

**最后更新**: 2025-10-17  
**维护者**: 平台工程团队

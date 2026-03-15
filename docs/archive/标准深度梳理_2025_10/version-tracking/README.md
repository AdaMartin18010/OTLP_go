# OTLP标准版本自动监控系统

> **目标**: 自动追踪OpenTelemetry标准的最新版本,确保文档始终与最新标准保持同步

---

## 📋 系统概述

本系统通过GitHub Actions自动化监控以下OpenTelemetry核心组件的版本更新:

| 组件 | 仓库 | 当前版本 | 监控频率 |
|------|------|---------|---------|
| **OTLP Protocol** | [opentelemetry-proto](https://github.com/open-telemetry/opentelemetry-proto) | v1.3.2 | 每日 |
| **Semantic Conventions** | [semantic-conventions](https://github.com/open-telemetry/semantic-conventions) | v1.29.0 | 每日 |
| **Collector** | [opentelemetry-collector](https://github.com/open-telemetry/opentelemetry-collector) | v0.113.0 | 每日 |

---

## 🔧 工作流程

```text
┌─────────────────────────────────────────────────────────────┐
│               GitHub Actions (每日UTC 00:00)                │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ↓
         ┌─────────────────────────────┐
         │  1. 获取各仓库最新Release    │
         │     - OTLP Spec             │
         │     - Semantic Conventions  │
         │     - Collector             │
         └──────────┬──────────────────┘
                    │
                    ↓
         ┌─────────────────────────────┐
         │  2. 对比本地版本记录        │
         │     (current-versions.yml)  │
         └──────────┬──────────────────┘
                    │
                    ↓
         ┌─────────────────────────────┐
         │  3. 发现版本差异?            │
         └──────────┬──────────────────┘
                    │
          ┌─────────┴─────────┐
          │ YES              │ NO
          ↓                   ↓
┌──────────────────┐   ┌──────────────┐
│ 4a. 生成更新报告 │   │ 4b. 记录检查 │
│ 4b. 创建GitHub   │   │     结果     │
│     Issue提醒    │   │              │
│ 4c. 更新版本文件 │   │              │
│ 4d. 上传报告     │   │              │
└──────────────────┘   └──────────────┘
```

---

## 📂 文件结构

```text
version-tracking/
├── README.md                      # 本文件
├── current-versions.yml           # 当前版本记录 (自动更新)
├── updates.json                   # 最近一次检测到的更新
├── issue-body.md                  # Issue内容模板
└── reports/                       # 历史报告
    ├── update-report-latest.md    # 最新更新报告
    └── weekly-YYYYMMDD.md         # 周报

.github/workflows/
└── otlp-version-monitor.yml       # GitHub Actions工作流
```

---

## 🚀 使用指南

### 自动监控

系统会自动执行,无需手动干预:

- **每日检查**: UTC 00:00 (北京时间08:00)
- **自动Issue**: 发现新版本时自动创建Issue
- **自动更新**: 更新`current-versions.yml`文件

### 手动触发

如需立即检查最新版本:

1. 访问: <https://github.com/YOUR_REPO/actions/workflows/otlp-version-monitor.yml>
2. 点击 "Run workflow"
3. 选择分支并执行

或使用GitHub CLI:

```bash
gh workflow run otlp-version-monitor.yml
```

### 查看结果

**方式1: GitHub Issues**:

- 新版本发现时会自动创建Issue
- 标签: `version-update`, `P0`, `documentation`
- Issue包含完整的更新详情和待办清单

**方式2: Workflow Summary**:

- 访问Actions页面查看运行记录
- 每次运行都有版本摘要

**方式3: Artifacts**:

- 下载历史报告: Actions → 选择运行 → Artifacts

---

## 📊 版本更新处理流程

当收到版本更新Issue时:

### 1. 审查变更 (⏱️ 30分钟)

```bash
# 查看Release Notes
open "https://github.com/open-telemetry/opentelemetry-proto/releases/tag/vX.Y.Z"

# 对比变更
open "https://github.com/open-telemetry/opentelemetry-proto/compare/vOLD...vNEW"
```

**关注点**:

- Breaking Changes (破坏性变更)
- New Features (新特性)
- Deprecations (废弃功能)
- Bug Fixes (bug修复)

### 2. 评估影响 (⏱️ 1小时)

根据变更类型,识别需要更新的文档:

| 变更类型 | 影响文档 | 优先级 |
|---------|---------|-------|
| **协议变更** | `01_OTLP核心协议/` | P0 |
| **数据模型变更** | `03_数据模型/` | P0 |
| **语义约定变更** | `02_Semantic_Conventions/` | P0 |
| **Collector变更** | `04_核心组件/` | P1 |
| **新功能** | 创建新文档 | P1 |
| **废弃功能** | 添加废弃标记 | P2 |
| **Bug修复** | 更新说明/示例 | P2 |

### 3. 更新文档 (⏱️ 2-8小时)

**标准更新模板**:

```markdown
# 文件头部
> **标准版本**: vX.Y.Z (从vOLD更新)  
> **发布日期**: YYYY-MM-DD  
> **最后更新**: YYYY-MM-DD  
> **变更追踪**: vOLD → vNEW

## 🆕 vX.Y.Z 新增特性 (YYYY-MM-DD)

- [新特性1]: 详细说明
- [新特性2]: 详细说明

## ⚠️ Breaking Changes

- [变更1]: 迁移指南
- [变更2]: 迁移指南

## ⛔ Deprecated

- [废弃功能]: 将在vFUTURE移除,请使用[替代方案]
```

### 4. 验证更新 (⏱️ 1-2小时)

```bash
# 1. 检查链接有效性
npm install -g markdown-link-check
find . -name "*.md" -exec markdown-link-check {} \;

# 2. 验证代码示例
cd examples/
go test ./...      # Go示例
python -m pytest   # Python示例
npm test           # Node.js示例

# 3. 运行linter
markdownlint **/*.md
```

### 5. 提交PR (⏱️ 30分钟)

```bash
# 创建分支
git checkout -b update/otlp-vX.Y.Z

# 提交变更
git add .
git commit -m "docs: update to OTLP vX.Y.Z"

# 推送并创建PR
git push origin update/otlp-vX.Y.Z
gh pr create --title "📚 Update to OTLP vX.Y.Z" \
             --body "Closes #ISSUE_NUMBER"
```

**PR检查清单**:

- [ ] 所有文档版本号已更新
- [ ] 代码示例已验证
- [ ] 添加了变更说明
- [ ] 链接检查通过
- [ ] 关联了对应Issue

### 6. 关闭Issue

PR合并后,在Issue中添加评论:

```markdown
✅ 已完成更新,详见 PR #XXX

**更新内容**:
- 已更新XX个文档
- 已验证XX个代码示例
- 已添加vX.Y.Z新特性说明

**文档链接**: [查看更新后文档](链接)
```

---

## 📈 监控指标

系统会追踪以下指标:

| 指标 | 说明 | 目标 |
|-----|------|------|
| **检查频率** | 每日自动检查 | 100% |
| **检测延迟** | 发现新版本的时间 | <24小时 |
| **Issue响应时间** | 从创建到开始处理 | <48小时 |
| **文档更新时间** | 从发现到完成更新 | <7天 (Major), <3天 (Minor) |
| **同步率** | 文档与最新标准的一致性 | >95% |

### 查看指标

```bash
# 统计历史更新
cd version-tracking/reports/
ls -l | wc -l  # 报告数量

# 查看最近5次更新
yq '.version_history[:5]' current-versions.yml
```

---

## 🔧 配置说明

### 修改监控频率

编辑 `.github/workflows/otlp-version-monitor.yml`:

```yaml
on:
  schedule:
    - cron: '0 0 * * *'  # 每天UTC 00:00
    # - cron: '0 */6 * * *'  # 每6小时
    # - cron: '0 0 * * 1'    # 每周一
```

### 添加监控仓库

编辑 `version-tracking/current-versions.yml`:

```yaml
monitoring_config:
  additional_repos:
    - name: your-repo-name
      repo: org/repo-name
      track_releases: true
```

然后更新workflow添加检查步骤。

### 禁用自动Issue创建

编辑workflow,注释掉或删除 "Create Issue for Updates" 步骤。

---

## 🐛 故障排查

### 问题1: Workflow执行失败

**可能原因**:

- GitHub API限流
- 权限不足
- 网络问题

**解决方案**:

```bash
# 检查workflow日志
gh run list --workflow=otlp-version-monitor.yml
gh run view <run-id> --log

# 重新运行
gh run rerun <run-id>
```

### 问题2: 未检测到新版本

**可能原因**:

- Release标签格式变化
- API响应异常

**解决方案**:

```bash
# 手动检查最新版本
curl -s https://api.github.com/repos/open-telemetry/opentelemetry-proto/releases/latest | jq

# 更新current-versions.yml
vim version-tracking/current-versions.yml
```

### 问题3: 创建Issue失败

**可能原因**:

- GITHUB_TOKEN权限不足
- Issue已存在

**解决方案**:

- 确保workflow有 `issues: write` 权限
- 检查是否有重复Issue

---

## 📚 相关资源

### OpenTelemetry官方

- [OTLP Specification](https://github.com/open-telemetry/opentelemetry-proto)
- [Semantic Conventions](https://github.com/open-telemetry/semantic-conventions)
- [Collector](https://github.com/open-telemetry/opentelemetry-collector)
- [Release Calendar](https://github.com/open-telemetry/community#release-schedule)

### GitHub Actions

- [GitHub Actions文档](https://docs.github.com/en/actions)
- [GitHub API文档](https://docs.github.com/en/rest)
- [Workflow语法](https://docs.github.com/en/actions/reference/workflow-syntax-for-github-actions)

### 自动化工具

- [semantic-release](https://github.com/semantic-release/semantic-release) - 自动化版本管理
- [release-drafter](https://github.com/release-drafter/release-drafter) - 自动生成Release Notes
- [dependabot](https://github.com/dependabot) - 依赖更新自动化

---

## 🤝 贡献指南

### 改进监控系统

欢迎提交PR改进监控系统:

1. **增强功能**:
   - 添加Slack/钉钉通知
   - 支持更多仓库
   - 生成变更对比报告
   - 自动化测试

2. **优化性能**:
   - 减少API调用
   - 并行检查
   - 缓存结果

3. **改进报告**:
   - 更详细的影响分析
   - 可视化版本历史
   - 自动生成迁移指南

### 提交流程

```bash
# 1. Fork仓库
# 2. 创建功能分支
git checkout -b feature/improve-monitor

# 3. 测试改动
act -j check-versions  # 使用act本地测试

# 4. 提交PR
gh pr create --title "feat: improve version monitor"
```

---

## 📞 联系与支持

- **Issue**: 遇到问题请创建Issue
- **Discussion**: 功能建议请在Discussions中讨论
- **邮件**: <otel-docs@example.com>

---

## 📜 变更日志

| 日期 | 版本 | 变更 |
|-----|------|------|
| 2025-10-09 | v1.0 | 初始版本发布 |

---

*本系统是OTLP标准深度梳理项目的一部分,确保文档始终保持最新状态。*

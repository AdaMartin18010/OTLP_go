# OpenTelemetry SDK 版本跟踪

> **当前版本**: v1.42.0 (2026-03-06)
> **Go版本**: 1.26.1
> **最后检查**: 2026-04-06

---

## 📋 版本历史

| 版本 | 发布日期 | Go版本 | 主要变更 | 项目适配 |
|------|----------|--------|----------|----------|
| v1.42.0 | 2026-03-06 | 1.26 | ForceFlush改进,资源检测优化 | ✅ 当前版本 |
| v1.41.0 | 2026-02-15 | 1.26 | Logs SDK稳定,新的Samplers | - |
| v1.40.0 | 2026-01-20 | 1.25 | Metrics性能优化 | - |
| v1.35.0 | 2025-11-10 | 1.23 | 初始稳定版本 | - |

---

## 🔍 版本检查机制

### 自动检查

```yaml
# .github/workflows/otel-sdk-version-check.yml
- 每周一自动检查新版本
- 发现新版本自动创建GitHub Issue
- 标记labels: dependencies, otel-sdk, documentation
```

### 手动检查

```bash
# 查看最新版本
curl -s https://api.github.com/repos/open-telemetry/opentelemetry-go/releases/latest | jq -r '.tag_name'

# 查看当前项目版本
grep "go.opentelemetry.io/otel " go.mod

# 检查可更新依赖
go list -u -m all | grep opentelemetry
```

---

## 📝 升级流程

### Step 1: 检查Release Notes

```bash
# 查看release notes
open https://github.com/open-telemetry/opentelemetry-go/releases

# 重点关注:
# - Breaking Changes
# - Deprecations
# - New Features
# - Performance Improvements
```

### Step 2: 评估影响

| 组件 | 检查点 | 文档 |
|------|--------|------|
| TracerProvider | 初始化方式变更 | otel-sdk-tracerprovider-init.md |
| Propagation | 传播器接口变更 | propagation/*.go |
| Metrics | API变化 | otel-sdk-metrics-deep-dive.md |
| Sampling | 新采样器 | otel-sdk-sampling-strategies.md |

### Step 3: 执行升级

```bash
# 更新依赖
go get go.opentelemetry.io/otel@v1.x.x
go get go.opentelemetry.io/otel/sdk@v1.x.x
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.x.x

# 同步工作区
go work sync

# 运行测试
go test ./...
```

### Step 4: 更新文档

- [ ] 更新代码示例中的版本号
- [ ] 更新文档中的变更说明
- [ ] 更新本跟踪文档

---

## 📊 兼容性矩阵

| OTel SDK | Go版本 | 本项目状态 |
|----------|--------|------------|
| v1.42.0 | 1.26.1 | ✅ 已适配 |
| v1.41.0 | 1.26 | ⚠️ 待测试 |
| v1.40.0 | 1.25 | ⚠️ 待测试 |
| v1.35.0 | 1.23 | ✅ 兼容 |

---

## 🔔 订阅更新

### GitHub Watch

1. 访问 <https://github.com/open-telemetry/opentelemetry-go>
2. 点击 Watch → Custom → Releases
3. 开启邮件通知

### RSS订阅

```
https://github.com/open-telemetry/opentelemetry-go/releases.atom
```

---

**维护者**: OTLP_go团队
**更新频率**: 每周检查
**下次检查**: 2026-04-13

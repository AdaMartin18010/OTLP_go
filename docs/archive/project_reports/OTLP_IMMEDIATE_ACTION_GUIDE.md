# 🚀 OTLP 标准更新立即行动指南

**制定日期**: 2026-03-15
**紧急程度**: 🔴 高
**预计完成**: 1-2周

---

## ⚡ 立即执行清单 (Today)

### Step 1: 环境准备 (30分钟)

```bash
# 1.1 创建新分支
git checkout -b feature/otlp-standards-update-2026

# 1.2 备份当前状态
git tag backup-before-otlp-update-$(date +%Y%m%d)

# 1.3 确保 Go 1.26 环境
go version  # 应显示 go1.26.0
```

### Step 2: 安全扫描 (10分钟)

```bash
# 2.1 搜索不安全的 WithInsecure 使用
grep -r "WithInsecure" --include="*.go" .

# 2.2 搜索结果应显示:
# ./examples/basic/main.go
# ./examples/metrics/main.go
# ./src/main.go
# ./src/metrics.go
# ... 等文件

# 2.3 记录需要修改的文件列表
grep -r "WithInsecure" --include="*.go" -l > /tmp/insecure_files.txt
cat /tmp/insecure_files.txt
```

### Step 3: 依赖版本检查 (10分钟)

```bash
# 3.1 检查当前 semconv 版本
grep -r "semconv/v1\." --include="*.go" .

# 3.2 应显示 v1.26.0，需要升级到 v1.30.0
```

---

## 🔧 批量修复脚本

### 脚本 1: 修复安全问题

```bash
#!/bin/bash
# fix_security.sh - 修复所有不安全配置

echo "🔒 开始修复安全问题..."

# 创建 TLS 配置模板
cat > /tmp/tls_config.go << 'EOF'
import "google.golang.org/grpc/credentials"

// getTLSCredentials 返回 TLS 配置
func getTLSCredentials() credentials.TransportCredentials {
    // 生产环境使用证书
    // return credentials.NewClientTLSFromFile("cert.pem", "")

    // 开发环境使用系统证书池
    return credentials.NewClientTLSFromCert(nil, "")
}
EOF

# 批量替换 WithInsecure
for file in $(cat /tmp/insecure_files.txt); do
    echo "处理: $file"

    # 添加 import
    sed -i 's|"google.golang.org/grpc/credentials"|credentials "google.golang.org/grpc/credentials"|' "$file"

    # 替换 WithInsecure
    sed -i 's/WithInsecure()/WithTLSCredentials(credentials.NewClientTLSFromCert(nil, ""))/' "$file"
done

echo "✅ 安全修复完成"
```

### 脚本 2: 升级 Semantic Conventions

```bash
#!/bin/bash
# upgrade_semconv.sh - 升级语义约定版本

echo "⬆️  开始升级 Semantic Conventions..."

OLD_VERSION="v1.26.0"
NEW_VERSION="v1.30.0"

# 批量替换
find . -name "*.go" -exec sed -i "s|semconv/v1.26.0|semconv/v1.30.0|g" {} \;

# 验证替换
echo "验证替换结果:"
grep -r "semconv/v1\." --include="*.go" . | head -10

echo "✅ Semantic Conventions 升级完成"
```

### 脚本 3: 添加重试配置

```bash
#!/bin/bash
# add_retry.sh - 为所有 Exporter 添加重试

echo "🔄 开始添加重试配置..."

# 在 otlptracegrpc.New 调用后添加重试配置
find . -name "*.go" -exec sed -i '/otlptracegrpc.New/,/)/{
/)/a\
\ \totlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{\
\t\t\tEnabled:         true,\
\t\t\tInitialInterval: 1 * time.Second,\
\t\t\tMaxInterval:     10 * time.Second,\
\t\t\tMaxElapsedTime:  30 * time.Second,\
\t\t}),
}' {} \;

echo "✅ 重试配置添加完成"
```

---

## 📝 详细修复步骤

### 修复 1: src/main.go

```go
// 修改前:
import (
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

exp, err := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint(endpoint),
    otlptracegrpc.WithInsecure(), // ❌ 移除
)

// 修改后:
import (
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    semconv "go.opentelemetry.io/otel/semconv/v1.30.0"  // ⬆️ 升级
    "google.golang.org/grpc/credentials"  // ➕ 添加
)

exp, err := otlptracegrpc.New(ctx,
    otlptracegrpc.WithEndpoint(endpoint),
    otlptracegrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")), // ✅ 安全
    otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{  // ➕ 添加重试
        Enabled:         true,
        InitialInterval: 1 * time.Second,
        MaxInterval:     10 * time.Second,
        MaxElapsedTime:  30 * time.Second,
    }),
)
```

### 修复 2: src/metrics.go

```go
// 修改前:
import (
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

exp, err := otlpmetricgrpc.New(ctx,
    otlpmetricgrpc.WithEndpoint(endpoint),
    otlpmetricgrpc.WithInsecure(), // ❌ 移除
)

// 修改后:
import (
    semconv "go.opentelemetry.io/otel/semconv/v1.30.0"  // ⬆️ 升级
    "google.golang.org/grpc/credentials"  // ➕ 添加
)

exp, err := otlpmetricgrpc.New(ctx,
    otlpmetricgrpc.WithEndpoint(endpoint),
    otlpmetricgrpc.WithTLSCredentials(credentials.NewClientTLSFromCert(nil, "")), // ✅ 安全
    otlpmetricgrpc.WithRetry(otlpmetricgrpc.RetryConfig{  // ➕ 添加重试
        Enabled:         true,
        InitialInterval: 1 * time.Second,
        MaxInterval:     10 * time.Second,
    }),
)
```

### 修复 3: examples 目录批量修复

```bash
# 创建修复脚本
cat > /tmp/fix_examples.sh << 'SCRIPT'
#!/bin/bash

for file in examples/*/main.go; do
    echo "修复: $file"

    # 升级 semconv
    sed -i 's|semconv/v1.26.0|semconv/v1.30.0|g' "$file"

    # 如果存在 WithInsecure，添加 credentials import 并替换
    if grep -q "WithInsecure" "$file"; then
        # 添加 import
        sed -i '/"go.opentelemetry.io\/otel\/exporters\/otlp/a\\t"google.golang.org/grpc/credentials"' "$file"

        # 替换 WithInsecure
        sed -i 's/WithInsecure()/WithTLSCredentials(credentials.NewClientTLSFromCert(nil, ""))/g' "$file"
    fi
done

echo "✅ Examples 修复完成"
SCRIPT

chmod +x /tmp/fix_examples.sh
/tmp/fix_examples.sh
```

---

## 🧪 验证检查清单

### 编译验证

```bash
# 1. 更新依赖
go mod tidy

# 2. 编译检查
go build ./...

# 3. 测试检查
go test ./src/pkg/... -race

# 4. 输出应显示:
# ok  OTLP_go/src/pkg/... (全部通过)
```

### 安全验证

```bash
# 1. 确认无 WithInsecure
if grep -r "WithInsecure" --include="*.go" .; then
    echo "❌ 仍有 WithInsecure 未修复"
    exit 1
else
    echo "✅ 无 WithInsecure"
fi

# 2. 确认 semconv 版本
grep -r "semconv/v1\." --include="*.go" . | grep -v "v1.30.0"
if [ $? -eq 0 ]; then
    echo "❌ 仍有旧版本 semconv"
else
    echo "✅ 所有 semconv 已升级到 v1.30.0"
fi
```

### 功能验证

```bash
# 运行示例测试
cd examples/basic
go run main.go &
sleep 5
# 检查是否正常启动无错误
kill %1
```

---

## 📊 进度跟踪模板

```markdown
## Week 1 进度

### Day 1
- [ ] 创建分支
- [ ] 安全扫描
- [ ] 修复 src/main.go
- [ ] 修复 src/metrics.go

### Day 2
- [ ] 批量修复 examples
- [ ] 升级 semconv
- [ ] 添加重试配置
- [ ] 编译验证

### Day 3
- [ ] 运行全量测试
- [ ] Race detector 检查
- [ ] 修复测试失败
- [ ] 更新文档

### Day 4
- [ ] 代码审查
- [ ] 安全审查
- [ ] 性能测试
- [ ] 准备发布说明

### Day 5
- [ ] 合并到 main
- [ ] 打标签 v3.3.1
- [ ] 更新 CHANGELOG
- [ ] 通知团队

## 阻碍记录
| 日期 | 问题 | 解决方案 | 状态 |
|------|------|----------|------|
|      |      |          |      |
```

---

## 🆘 常见问题解决

### 问题 1: 编译失败 - 缺少 credentials 包

```bash
# 解决:
go get google.golang.org/grpc/credentials
```

### 问题 2: 测试失败 - semconv 属性变更

```bash
# 检查 v1.26 → v1.30 的变更
go doc go.opentelemetry.io/otel/semconv/v1.30.0 | grep -i "deprecated"

# 修复已弃用的属性
# 例如: semconv.HostName → semconv.HostNameKey
```

### 问题 3: 循环依赖

```bash
# 如果出现循环依赖，可能是 import 顺序问题
# 解决: 检查 credentials import 位置
```

---

## 📞 升级支持

### 内部资源

- 技术负责人: @tech-lead
- OTLP 专家: @otlp-expert
- 安全专员: @security-lead

### 外部资源

- [OTLP v1.5.0 迁移指南](https://opentelemetry.io/docs/specs/otlp/migration/)
- [Go SDK 升级指南](https://github.com/open-telemetry/opentelemetry-go/blob/main/VERSIONING.md)
- [Semantic Conventions 变更日志](https://github.com/open-telemetry/semantic-conventions/blob/main/CHANGELOG.md)

---

## ✅ 完成标准

当满足以下条件时，Week 1 任务完成:

```markdown
- [ ] 所有 WithInsecure 已替换
- [ ] 所有 semconv 升级到 v1.30.0
- [ ] 所有 Exporter 配置重试
- [ ] 全量测试通过
- [ ] Race detector 无警告
- [ ] 安全扫描通过
- [ ] 文档已更新
- [ ] 代码审查通过
- [ ] 已合并到 main
- [ ] 已打标签 v3.3.1
```

---

**开始时间**: ****-****-____
**预计完成**: ****-****-____
**负责人**: ________________

🚀 **准备好了吗？开始行动！**

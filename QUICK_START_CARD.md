# OTLP Go 快速开始卡片 🚀

**5 分钟快速上手指南**-

---

## 🎯 核心概念 (1 分钟)

```text
Trace (追踪)
  └─ Span (跨度)
      ├─ Context (上下文)
      ├─ Attributes (属性)
      └─ Events (事件)
```

**关键术语**:

- **Trace**: 完整的请求路径
- **Span**: 单个操作单元
- **Context**: 传播追踪信息
- **Tracer**: 创建 Span 的工厂

---

## 💻 最小示例 (2 分钟)

### 1. 初始化 Tracer

```go
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/sdk/trace"
)

func initTracer() *trace.TracerProvider {
    tp := trace.NewTracerProvider()
    otel.SetTracerProvider(tp)
    return tp
}
```

### 2. 创建 Span

```go
func doWork(ctx context.Context) {
    tracer := otel.Tracer("my-app")
    ctx, span := tracer.Start(ctx, "doWork")
    defer span.End()
    
    // 你的业务逻辑
    span.SetAttributes(attribute.String("key", "value"))
}
```

### 3. 传播 Context

```go
func parentFunc(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "parent")
    defer span.End()
    
    childFunc(ctx) // Context 自动传播
}

func childFunc(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "child")
    defer span.End()
    // ...
}
```

---

## 📚 核心文档 (1 分钟)

| 文档 | 用途 | 时间 |
|------|------|------|
| `README.md` | 项目概览 | 5 分钟 |
| `docs/00_index.md` | 文档索引 | 10 分钟 |
| `examples/basic/` | 基础示例 | 30 分钟 |
| `otlp-golang-idiomatic-programming-guide.md` | 编程惯用法 | 3 小时 |
| `otlp-recursive-system-analysis.md` | 深度分析 | 2-3 天 |

---

## 🔧 常用命令 (1 分钟)

```powershell
# 运行应用
.\run-app.ps1

# 启动 Docker 环境
.\run-docker.ps1

# 运行测试
go test ./...

# 运行基准测试
go test -bench=. ./benchmarks/
```

---

## 📖 学习路径

### 快速路径 (2-3 小时)

```text
README → examples/basic/ → semantic-model
```

### 系统路径 (1-2 周)

```text
semantic-model (6 篇) → system-perspectives → examples/
```

### 深度路径 (1-2 月)

```text
全部理论文档 → 形式化验证 → 源码研究
```

---

## 🎯 核心 API

### Tracer

```go
tracer := otel.Tracer("service-name")
ctx, span := tracer.Start(ctx, "operation-name")
defer span.End()
```

### Span

```go
span.SetAttributes(attribute.String("key", "value"))
span.AddEvent("event-name")
span.RecordError(err)
span.SetStatus(codes.Error, "error message")
```

### Context

```go
ctx := context.Background()
ctx = context.WithValue(ctx, key, value)
value := ctx.Value(key)
```

---

## 🚨 常见问题

### Q: Span 没有导出?

**A**: 检查 TracerProvider 和 Exporter 配置

### Q: Context 没有传播?

**A**: 确保使用 `tracer.Start(ctx, ...)` 返回的 ctx

### Q: 性能影响大?

**A**: 使用采样 (Sampler) 和批处理 (BatchProcessor)

---

## 📊 文档规模

- **总文档**: 20+ 篇
- **总行数**: 20,000+ 行
- **代码示例**: 500+ 个
- **形式化定理**: 40+ 个

---

## 🔗 快速链接

- **主索引**: `docs/00_index.md`
- **学习指南**: `OTLP_COMPLETE_LEARNING_GUIDE.md`
- **文档地图**: `DOCUMENTATION_MAP.md`
- **完成报告**: `SYSTEM_PERSPECTIVES_COMPLETION_REPORT.md`

---

## 🎓 下一步

1. ✅ 阅读 `README.md`
2. ✅ 运行 `examples/basic/`
3. ✅ 学习 `docs/00_index.md`
4. ⏭️ 深入 `semantic-model/`

---

**版本**: v1.0.0  
**更新**: 2025-10-06

**Happy Coding! 🚀**:

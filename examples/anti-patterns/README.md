# 反例代码示例

这个示例展示了 Go 编程中应该避免的模式和反例。

## 目的

通过展示错误的代码示例，帮助开发者识别和避免常见的编程错误。

## 包含的反例

1. **错误处理**: 丢失原始错误信息
2. **资源管理**: 忘记关闭资源导致泄漏
3. **Defer 使用**: 在循环中错误使用 defer
4. **Context 使用**: 忘记取消 context 导致 goroutine 泄漏
5. **切片分配**: 没有预分配容量导致多次重新分配
6. **日志使用**: 使用格式化日志而非结构化日志

## 运行

\\\ash
go run main.go
\\\

## 对照参考

- [BEST_PRACTICES.md](../../BEST_PRACTICES.md) - 最佳实践指南
- [Go Code Review Comments](https://github.com/golang/go/wiki/CodeReviewComments)
- [Effective Go](https://go.dev/doc/effective_go)
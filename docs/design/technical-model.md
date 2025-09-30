# 技术模型（架构/实现/性能）

- 架构分层：SDK → Agent/Sidecar → Collector → Gateway → Backend
- 关键路径：应用插桩（Span/Metrics/Logs/Profile）→ OTLP 导出（gRPC/HTTP + gzip）→ Collector 处理（batch/transform/route）→ 后端存储
- 性能基线：
  - 单实例吞吐：Tracing ≥ 200k span/s（batch + tail_sampling 前置过滤）
  - 指标聚合：Histogram/ExponentialHistogram 降维 10×
  - 延迟预算：应用侧导出 < 2 ms p95；Collector 处理 < 8 ms p95
- 可编程性：OTTL + WASM 作为通用算子层，热更新无重启
- 安全性：mTLS、证书热轮转、签名校验；多租户隔离标签与路由
- 运维性：OPAMP 下发配置/插件；灰度 + 回滚窗口；健康探针/自愈脚本集成
- 参考：`docs/analysis/technical-model/architecture.md`、`docs/language/go-1.25.1.md`、`docs/analysis/technical-model/collector-sdk-mapping.md`

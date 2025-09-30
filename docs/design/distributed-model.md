# 分布式模型（拓扑/一致性/容错）

- 拓扑：DaemonSet Agent（边缘聚合）→ 区域 Gateway（跨 AZ 汇聚）→ 中心 Backend
- 一致性：
  - 最终一致：遥测为追加型数据流，采用 at-least-once + 去重 ID
  - 顺序性：每资源实体内采用时间戳有序 + 批量窗口对齐
- 容错：
  - 背压：批量 + 重试 + 断路器；队列高水位时降采样/降精度
  - 旁路：后端不可用时本地落盘（Parquet）+ 延迟回传
- 隔离：租户/环境/区域三维标签；路由至独立管道与存储
- 自愈：EWMA/Z-score 边缘检测 → 触发限流/重启/调度（通过 OPAMP 下发策略）
- 参考：`docs/analysis/distributed-model/system-model.md`；联动：OPAMP 热更新 OTTL 规则，语义由 SchemaURL/Validator 保障

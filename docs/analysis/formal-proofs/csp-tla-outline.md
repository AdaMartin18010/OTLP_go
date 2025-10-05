# CSP × TLA+ 形式化验证大纲（OTLP 观测证据）

## 目录

- [CSP × TLA+ 形式化验证大纲（OTLP 观测证据）](#csp--tla-形式化验证大纲otlp-观测证据)
  - [目录](#目录)
  - [1. 抽象](#1-抽象)
  - [2. 与 OTLP 的连接](#2-与-otlp-的连接)
  - [3. 验证议题](#3-验证议题)
  - [4. 扩展 `pipeline.tla`](#4-扩展-pipelinetla)
  - [5. 运行](#5-运行)

本文给出将 CSP 风格流水线抽象为 TLA+ 的状态机轮廓，并说明如何利用现有 `docs/formal/tla/pipeline.tla` 进行最小验证与扩展。

## 1. 抽象

- 状态：`Queue`, `Workers`, `InFlight`, `Dropped`, `Config`；
- 动作：`Enqueue`, `Dispatch`, `ProcessOK`, `ProcessFail`, `Timeout`, `Drop`；
- 不变式：队列上界、不丢失已接收确认的任务、超时后不可再次被处理（若无幂等键则标记）。

## 2. 与 OTLP 的连接

- 将动作对应为 span 事件与指标：`queue.length`, `drop.count`, `retry.count`, `latency.hist`；
- 以 `resource.*` 绑定实例身份，以便回放与对账。

## 3. 验证议题

- 活性：在稳态到达率小于处理能力时，`Enqueue` 最终导致 `ProcessOK ∨ Drop`；
- 安全：超时动作触发后，不得再进入 `ProcessOK`；
- 预算：重试预算不变式：窗口内 `retry.count ≤ budget(config)`。

## 4. 扩展 `pipeline.tla`

- 增加 `Budget` 与 `TimeoutChain` 参数；
- 在 `Next` 中加入 `Timeout` 与 `Drop` 的联动；
- 在 `Spec` 中引入 `WF_vars(Dispatch)` 活性约束。

## 5. 运行

- 打开 `docs/formal/tla/pipeline.tla` 与 `pipeline.cfg`；
- 添加新常量并设置小规模模型（队列容量、worker 数、预算）；
- 运行 TLC 检查不变式与活性；
- 以 OTLP 回放数据对比模型统计量。

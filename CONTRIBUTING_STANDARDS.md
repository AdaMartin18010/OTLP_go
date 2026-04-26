# 贡献者标准指南 (Contributing Standards)

本文档定义向 OTLP_go 项目贡献代码和文档时必须遵循的标准。所有贡献者 MUST 在提交 PR 前阅读并遵守本指南。

---

## 1. OpenTelemetry 规范遵循

- **MUST**: 所有新代码 MUST 与 [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otel/) 保持一致。
- **MUST**: 实现 Trace、Metric、Log、Profile 信号时，MUST 参考对应信号的 SDK/API 规范。
- **SHOULD**: 优先使用官方 OpenTelemetry Go SDK（`go.opentelemetry.io/otel`）提供的类型和接口，避免重复造轮子。
- **MUST NOT**: 不得引入与 OpenTelemetry 数据模型不兼容的自定义字段或类型，除非该类型被明确标记为实验性（Alpha/Development）并在文档中说明。

---

## 2. 稳定性标注

- **MUST**: 每个新增的 `pkg/` 子包 MUST 在其入口文件（通常是第一个 `.go` 文件）的包注释中添加稳定性标注。
- **格式**:

  ```go
  // Stability: [Stable|Beta|Alpha|Development]
  // Compliance: OpenTelemetry Specification vX.Y.Z
  ```

- **含义**:
  - `Stable`: API 已冻结，MAJOR 版本变更前不会破坏向后兼容。
  - `Beta`: API 基本稳定，但 MAY 在 MINOR 版本中调整。
  - `Alpha`: API 尚未稳定，MAY 随时发生重大变更。
  - `Development`: 实验性实现，NOT RECOMMENDED 用于生产环境。
- **MUST**: 修改现有包的公共 API 时，MUST 同步更新稳定性标注和 `STANDARDS_COMPLIANCE.md` 中的合规状态。

---

## 3. 文档 RFC 2119 关键词

- **MUST**: 所有位于 `docs/` 目录下的设计文档、规范说明和差距分析，在描述规范性要求时 MUST 使用 [RFC 2119](https://tools.ietf.org/html/rfc2119) / [BCP 14](https://tools.ietf.org/html/bcp14) 关键词。
- **关键词列表**: `MUST`, `MUST NOT`, `REQUIRED`, `SHALL`, `SHALL NOT`, `SHOULD`, `SHOULD NOT`, `RECOMMENDED`, `NOT RECOMMENDED`, `MAY`, `OPTIONAL`。
- **格式**: 关键词 MUST 使用全大写英文形式。在中文文档中，可在括号内补充中文解释，例如：`MUST（必须）`。
- **MUST NOT**: 不得使用小写的 `must`、`should`、`may` 表达规范性要求。

---

## 4. 语义约定 (Semantic Conventions)

- **MUST**: 代码中引用语义约定属性时，MUST 使用 `pkg/semconv/` 中定义的常量，禁止硬编码字符串。
- **MUST**: 新增属性常量时，MUST 遵循 [Attribute Naming](https://opentelemetry.io/docs/concepts/semantic-conventions/#attribute-naming) 规范（小写、点号分隔、避免缩写）。
- **SHOULD**: 尽量复用官方 `go.opentelemetry.io/otel/semconv/v1.xx.0` 包中的常量，减少自定义定义。

---

## 5. PR 检查清单

在创建 Pull Request 前，贡献者 MUST 完成以下检查：

- [ ] 代码通过 `go build ./...` 和 `go test ./...`。
- [ ] 新增的 `pkg/` 子包已添加稳定性标注。
- [ ] 文档中使用的规范性关键词符合 RFC 2119 大写要求。
- [ ] 未引入硬编码的语义约定字符串（使用 `pkg/semconv/` 常量）。
- [ ] `STANDARDS_COMPLIANCE.md` 已同步更新（如新增模块或变更合规状态）。
- [ ] `docs/alignment/STANDARD_ALIGNMENT_GAP_ANALYSIS.md` 已同步更新（如涉及标准差距变更）。
- [ ] 提交信息遵循 [Conventional Commits](https://www.conventionalcommits.org/) 规范（推荐）。

---

## 6. 代码风格

- 遵循标准 Go 代码风格，`gofmt` / `goimports` 无差异。
- 公共函数、类型 MUST 附带 GoDoc 注释。
- 错误处理 MUST 使用 `pkg/errors` 包或标准 `errors` 包，避免裸 `panic`。

---

*文档版本: 2026-04-26*
*规范基线: OpenTelemetry Specification v1.42.0, RFC 2119*

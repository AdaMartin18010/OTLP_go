# Golang 最成熟 OTLP 生态库映射

- opentelemetry-go（SDK）：Tracing/Metrics/Logs API 与实现，稳定版 v1.x，支持 OTLP/gRPC 与 HTTP exporters。
- opentelemetry-collector/collector-contrib：可编程遥测引擎（Receiver/Processor/Exporter/Extensions），支持 OTTL、WASM 插件与高性能流水线。
- opentelemetry-go-contrib：常见框架自动插桩（`net/http`、`grpc`、`database/sql`、gin、echo 等）。
- opentelemetry-proto：含 Profiles 信号与 Resource 语义；与 Profiles 可视化（Phlare/Pyroscope/Elastic）兼容。
- OPAMP 生态：opamp-go（Agent/Server 参考实现），支持远程配置、证书轮转与插件分发。

选型建议：

- 应用侧：优先使用 opentelemetry-go + otlpgrpc exporter；
- 边缘/网关：OTel Collector + transform/OTTL + batch + tail_sampling；
- 控制面：引入 OPAMP Server，对 Agent/Collector 做灰度配置与热更新。

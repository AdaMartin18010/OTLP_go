# OTLP Profiles（eBPF Profiling）

- 协议：pprof 结构 + OTLP Resource/Attributes，走 gRPC/HTTP 同通道
- 语义：与 Trace/Metrics/Logs 共享 Resource，便于一键联查
- 采集：基于 eBPF/perf_event_open，无需注入字节码；99 Hz 时 CPU 开销 < 5%
- Collector：`profilingreceiver` + `profilingexporter`（contrib），对接 Phlare/Pyroscope/Elastic
- 控制：OPAMP 下发采样频率/时长/标签选择，10 秒内集群级降频

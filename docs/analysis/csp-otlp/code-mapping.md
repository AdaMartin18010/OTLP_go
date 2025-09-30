# 代码-语义-指标映射（本仓库示例）

## Provider 初始化

- `src/main.go:newTracerProvider`：`semconv.ServiceName("otlp-go-demo")`、`DeploymentEnvironment("dev")`、`runtime.go=1.25.1`
- `src/metrics.go:initMetricProvider`：`PeriodicReader` 2s 推送间隔

## Traces

- `demo/handler`：HTTP 处理器 `GET /hello` → `Span`，事件写入 `req.id`
- `demo/pipeline`：工作协程处理 `pipeline.process` 事件，附 `task.id`

## Metrics

- `demo.requests`：每秒 +1（心跳/吞吐）
- `pipeline.queue.length`：入队 +1 / 出队 -1
- `pipeline.task.latency`：从入队到处理完成的秒级直方图
- `pipeline.queue.drop`：因 `ctx` 取消导致的丢弃 +1，`reason=enqueue_ctx_cancel`

## Logs

- `slog`：启动、处理事件，建议 Collector 侧进行结构化归并

## Resource

- `service.name=otlp-go-demo`、`deployment.environment=dev`、`runtime.go=1.25.1`

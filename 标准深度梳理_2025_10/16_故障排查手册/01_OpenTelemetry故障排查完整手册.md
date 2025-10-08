# OpenTelemetry故障排查完整手册

> **实战指南**: 生产环境故障诊断与解决  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry故障排查完整手册](#opentelemetry故障排查完整手册)
  - [目录](#目录)
  - [1. 快速诊断流程](#1-快速诊断流程)
    - [1.1 故障分类](#11-故障分类)
    - [1.2 诊断决策树](#12-诊断决策树)
  - [2. SDK故障排查](#2-sdk故障排查)
    - [2.1 数据未发送](#21-数据未发送)
    - [2.2 性能问题](#22-性能问题)
  - [3. Collector故障排查](#3-collector故障排查)
    - [3.1 连接问题](#31-连接问题)
    - [3.2 数据丢失](#32-数据丢失)
  - [4. 网络问题](#4-网络问题)
    - [4.1 连接超时](#41-连接超时)
    - [4.2 TLS错误](#42-tls错误)
  - [5. 数据质量问题](#5-数据质量问题)
    - [5.1 Trace不完整](#51-trace不完整)
    - [5.2 属性缺失](#52-属性缺失)
  - [6. 性能瓶颈](#6-性能瓶颈)
    - [6.1 高延迟](#61-高延迟)
    - [6.2 高CPU/内存](#62-高cpu内存)
  - [7. Kubernetes环境](#7-kubernetes环境)
    - [7.1 Pod问题](#71-pod问题)
    - [7.2 资源限制](#72-资源限制)
  - [8. Backend集成](#8-backend集成)
    - [8.1 Jaeger问题](#81-jaeger问题)
    - [8.2 Prometheus问题](#82-prometheus问题)
  - [9. 诊断工具](#9-诊断工具)
    - [9.1 内置工具](#91-内置工具)
    - [9.2 第三方工具](#92-第三方工具)
  - [10. 故障案例库](#10-故障案例库)
    - [10.1 典型案例](#101-典型案例)
    - [10.2 罕见问题](#102-罕见问题)

---

## 1. 快速诊断流程

### 1.1 故障分类

```text
故障分类矩阵:

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

按影响范围:
┌────────────────────────────────────────────────┐
│ P0 (紧急)    - 完全无数据 / 服务宕机             │
│ P1 (高)      - 数据丢失 > 50% / 严重延迟         │
│ P2 (中)      - 部分数据丢失 / 性能下降           │
│ P3 (低)      - 数据质量问题 / 告警噪音           │
└────────────────────────────────────────────────┘

按故障类型:
┌────────────────────────────────────────────────┐
│ 🔌 连接问题   - 网络/认证/TLS                   │
│ 📦 数据问题   - 丢失/不完整/错误                 │
│ ⚡ 性能问题   - 延迟/吞吐量/资源                 │
│ 🔧 配置问题   - 参数错误/版本不兼容              │
│ 🐛 Bug问题    - SDK/Collector/Backend bug      │
└────────────────────────────────────────────────┘

按组件:
┌────────────────────────────────────────────────┐
│ 📱 SDK层      - 应用内SDK问题                   │
│ 🔄 Collector  - Collector处理问题              │
│ 🌐 网络层     - 传输/连接问题                   │
│ 💾 存储层     - Backend存储问题                 │
│ 📊 查询层     - 查询/展示问题                   │
└────────────────────────────────────────────────┘

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.2 诊断决策树

```text
快速诊断决策树:

问题: 完全没有数据？
├─ 是 → 
│  ├─ SDK正常初始化？
│  │  ├─ 否 → 检查SDK配置
│  │  └─ 是 → 
│  │     ├─ Collector可达？
│  │     │  ├─ 否 → 检查网络/DNS
│  │     │  └─ 是 → 检查认证/TLS
│  │     └─ Backend可达？
│  │        └─ 检查Exporter配置
│  └─
└─ 否 → 部分数据丢失？
   ├─ 是 → 
   │  ├─ 特定时间段？
   │  │  └─ 检查Collector日志
   │  ├─ 特定服务？
   │  │  └─ 检查SDK/采样配置
   │  └─ 随机丢失？
   │     └─ 检查资源限制/背压
   └─ 否 → 数据质量问题？
      ├─ Trace不完整？
      │  └─ 检查Context传播
      ├─ 属性缺失？
      │  └─ 检查Processor配置
      └─ 性能问题？
         └─ 检查资源使用/优化配置
```

---

## 2. SDK故障排查

### 2.1 数据未发送

**症状**: SDK初始化成功，但没有数据发送到Collector

**诊断步骤**:

```go
// 1. 启用SDK调试日志
import (
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
)

// 临时使用stdout exporter验证数据生成
func debugSDK() {
    exporter, _ := stdouttrace.New(
        stdouttrace.WithPrettyPrint(),
    )
    
    tp := trace.NewTracerProvider(
        trace.WithBatcher(exporter),
    )
    otel.SetTracerProvider(tp)
    
    // 创建测试Span
    ctx := context.Background()
    tracer := otel.Tracer("debug")
    _, span := tracer.Start(ctx, "test-span")
    span.End()
    
    // 强制Flush
    tp.ForceFlush(ctx)
    tp.Shutdown(ctx)
}
```

**常见原因与解决**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 未调用Shutdown/ForceFlush ❌
   问题: 程序退出前数据在缓冲区
   解决:
    ```go
    defer tp.Shutdown(context.Background())
    // 或定期Flush
    tp.ForceFlush(context.Background())
    ```

2. Endpoint配置错误 ❌
   问题: 错误的Collector地址
   解决:

    ```go
    // 检查环境变量
    endpoint := os.Getenv("OTEL_EXPORTER_OTLP_ENDPOINT")
    // 默认: localhost:4317 (gRPC) / localhost:4318 (HTTP)
    ```

3. 采样率设置为0 ❌
   问题: AlwaysOff sampler
   解决:

    ```go
    trace.WithSampler(trace.AlwaysSample())
    // 或
    trace.WithSampler(trace.TraceIDRatioBased(1.0))
    ```

4. 网络防火墙阻断 ❌
   解决:

    ```bash
    # 测试连接
    telnet collector-host 4317
    curl -v http://collector-host:4318/v1/traces
    ```

5. 认证失败 ❌
   解决:

    ```go
    // 添加认证Header
    otlptracegrpc.WithHeaders(map[string]string{
        "Authorization": "Bearer " + token,
    })
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

### 2.2 性能问题

**症状**: SDK导致应用性能下降

**诊断工具**:

```go
// 性能分析
func profileSDK() {
    // 1. CPU Profiling
    f, _ := os.Create("cpu.prof")
    pprof.StartCPUProfile(f)
    defer pprof.StopCPUProfile()
    
    // 2. 内存Profiling
    runtime.GC()
    f2, _ := os.Create("mem.prof")
    pprof.WriteHeapProfile(f2)
    f2.Close()
    
    // 3. Goroutine Profiling
    f3, _ := os.Create("goroutine.prof")
    pprof.Lookup("goroutine").WriteTo(f3, 0)
    f3.Close()
}

// 监控SDK内部指标
func monitorSDKMetrics() {
    meter := otel.Meter("sdk-monitoring")
    
    // 导出队列大小
    queueSize, _ := meter.Int64ObservableGauge("otel.exporter.queue_size")
    // 导出延迟
    exportLatency, _ := meter.Float64Histogram("otel.exporter.duration")
    // 丢弃的Span数
    droppedSpans, _ := meter.Int64Counter("otel.exporter.dropped_spans")
}
```

**优化方案**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 调整批处理参数 ✅
    ```go
    trace.WithBatcher(exporter,
        trace.WithMaxExportBatchSize(512),     // 增加批大小
        trace.WithBatchTimeout(5*time.Second), // 增加超时
        trace.WithMaxQueueSize(2048),          // 增加队列
    )
    ```

2. 降低采样率 ✅

    ```go
    // 从100%降到10%
    trace.WithSampler(trace.TraceIDRatioBased(0.1))
    ```

3. 使用异步处理 ✅
   - 默认BatchSpanProcessor已是异步
   - 避免使用SimpleSpanProcessor (同步)

4. 减少属性数量 ✅

    ```go
    // 限制属性数量
    trace.WithSpanLimits(trace.SpanLimits{
        AttributeCountLimit: 32,
    })
    ```

5. 优化Processor链 ✅
   - 移除不必要的Processor
   - 合并多个Processor功能

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```

---

## 3. Collector故障排查

### 3.1 连接问题

**症状**: SDK无法连接到Collector

**检查清单**:

```bash
# 1. 检查Collector是否运行
kubectl get pods -l app=opentelemetry-collector
# 或
ps aux | grep otelcol

# 2. 检查端口监听
netstat -tlnp | grep -E "4317|4318"
# 应该看到:
# 0.0.0.0:4317 (gRPC)
# 0.0.0.0:4318 (HTTP)

# 3. 检查Collector日志
kubectl logs -f deployment/opentelemetry-collector
# 或
tail -f /var/log/otelcol.log

# 4. 测试连接
# gRPC测试
grpcurl -plaintext collector:4317 list
# HTTP测试
curl -X POST http://collector:4318/v1/traces \
  -H "Content-Type: application/json" \
  -d '{}'

# 5. 检查健康端点
curl http://collector:13133/
```

**常见错误与解决**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

错误1: "connection refused"
原因: Collector未启动或端口未监听
解决:
  - 检查Collector配置是否正确
  - 检查端口是否被占用
  - 检查防火墙规则

错误2: "context deadline exceeded"
原因: 网络延迟或Collector过载
解决:
  - 增加超时时间
  - 检查网络延迟: ping/traceroute
  - 检查Collector资源使用

错误3: "certificate verify failed"
原因: TLS证书问题
解决:
  - 检查证书有效期
  - 检查CA证书配置
  - 验证服务器名称

错误4: "permission denied"
原因: 认证失败
解决:
  - 检查Bearer Token
  - 检查mTLS客户端证书
  - 查看Collector认证日志

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 3.2 数据丢失

**症状**: Collector接收到数据但未导出到Backend

**诊断步骤**:

```yaml
# 1. 启用详细日志
service:
  telemetry:
    logs:
      level: debug  # 临时调试用
      
# 2. 添加日志导出器验证数据
exporters:
  logging:
    loglevel: debug
    sampling_initial: 10
    sampling_thereafter: 100

service:
  pipelines:
    traces:
      receivers: [otlp]
      processors: [batch]
      exporters: [logging, otlp]  # 同时导出到日志和Backend

# 3. 检查内部指标
receivers:
  prometheus:
    config:
      scrape_configs:
        - job_name: 'otelcol'
          static_configs:
            - targets: ['localhost:8888']
```

**关键指标**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

监控指标:

1. 接收器指标
   - otelcol_receiver_accepted_spans    (接收的Span数)
   - otelcol_receiver_refused_spans     (拒绝的Span数)

2. 处理器指标
   - otelcol_processor_batch_batch_send_size    (批大小)
   - otelcol_processor_batch_timeout_trigger    (超时触发)

3. 导出器指标
   - otelcol_exporter_sent_spans                (发送的Span数)
   - otelcol_exporter_send_failed_spans         (发送失败)
   - otelcol_exporter_queue_size                (队列大小)

4. 队列指标
   - otelcol_exporter_queue_capacity            (队列容量)
   - otelcol_exporter_enqueue_failed_spans      (入队失败)

故障分析:
- 接收 > 发送 → 数据积压，检查Backend
- 拒绝 > 0    → 资源不足，增加资源
- 队列满      → 背压，扩容Collector

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 4. 网络问题

### 4.1 连接超时

**诊断脚本**:

```bash
#!/bin/bash
# 网络诊断脚本

COLLECTOR_HOST="collector.example.com"
GRPC_PORT=4317
HTTP_PORT=4318

echo "=== OpenTelemetry Network Diagnostics ==="

# 1. DNS解析
echo "[1] DNS Resolution:"
nslookup $COLLECTOR_HOST
dig $COLLECTOR_HOST

# 2. 网络可达性
echo "[2] Network Connectivity:"
ping -c 3 $COLLECTOR_HOST

# 3. 端口连通性
echo "[3] Port Connectivity:"
timeout 5 bash -c "cat < /dev/null > /dev/tcp/$COLLECTOR_HOST/$GRPC_PORT" && echo "gRPC port OK" || echo "gRPC port FAILED"
timeout 5 bash -c "cat < /dev/null > /dev/tcp/$COLLECTOR_HOST/$HTTP_PORT" && echo "HTTP port OK" || echo "HTTP port FAILED"

# 4. 路由跟踪
echo "[4] Route Trace:"
traceroute -m 10 $COLLECTOR_HOST

# 5. 延迟测试
echo "[5] Latency Test:"
for i in {1..10}; do
  curl -o /dev/null -s -w "%{time_total}s\n" http://$COLLECTOR_HOST:$HTTP_PORT/
done | awk '{sum+=$1; count++} END {print "Avg:", sum/count "s"}'

# 6. TLS测试
echo "[6] TLS Certificate:"
openssl s_client -connect $COLLECTOR_HOST:$GRPC_PORT -showcerts 2>/dev/null | openssl x509 -noout -dates

echo "=== Diagnostics Complete ==="
```

### 4.2 TLS错误

**常见TLS错误**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

错误1: "x509: certificate signed by unknown authority"
原因: CA证书未配置
解决:
  ```go
  caCert, _ := os.ReadFile("/path/to/ca.crt")
  caCertPool := x509.NewCertPool()
  caCertPool.AppendCertsFromPEM(caCert)
  
  tlsConfig := &tls.Config{
      RootCAs: caCertPool,
  }
  ```

错误2: "x509: certificate has expired"
原因: 证书过期
解决:

- 更新证书
- 检查系统时间同步
- 自动化证书轮换

错误3: "x509: certificate is valid for X, not Y"
原因: 证书CN/SAN不匹配
解决:

  ```go
  tlsConfig := &tls.Config{
      ServerName: "correct-server-name",
  }
  // 或重新签发证书
  ```

错误4: "tls: handshake failure"
原因: TLS版本或密码套件不匹配
解决:

  ```go
  tlsConfig := &tls.Config{
      MinVersion: tls.VersionTLS12,  // 降低最低版本
      CipherSuites: []uint16{
          tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
          // ... 更多兼容密码套件
      },
  }
  ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

---

## 5. 数据质量问题

### 5.1 Trace不完整

**症状**: Trace中缺少部分Span

**诊断清单**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

检查项:

□ Context传播
  - W3C Trace Context Header正确？
  - 跨服务边界传播？
  - 异步任务Context传递？

□ 采样一致性
  - 所有服务使用相同采样决策？
  - TraceID-based采样？
  - 父Span采样决策传递？

□ 时间同步
  - 所有服务时间同步（NTP）？
  - Span时间戳正确？
  - 时区设置一致？

□ SDK版本
  - 所有服务SDK版本兼容？
  - 协议版本一致？
  - 已知Bug？

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

**修复示例**:

```go
// 1. 正确传播Context (HTTP)
func httpClientWithContext(ctx context.Context) {
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    
    // Context自动注入到Header
    otel.GetTextMapPropagator().Inject(ctx, propagation.HeaderCarrier(req.Header))
    
    resp, _ := http.DefaultClient.Do(req)
}

// 2. 跨Goroutine传播Context
func asyncTask(parentCtx context.Context) {
    go func() {
        // 创建新Span，继承parent context
        ctx, span := otel.Tracer("async").Start(parentCtx, "async-task")
        defer span.End()
        
        // ... 异步任务
    }()
}

// 3. 强制采样重要Trace
func importantOperation(ctx context.Context) {
    // 创建AlwaysSample的Span
    ctx, span := otel.Tracer("important").Start(ctx, "critical-op",
        trace.WithSpanKind(trace.SpanKindServer),
        // 强制采样
        trace.WithAttributes(attribute.Bool("force.sample", true)),
    )
    defer span.End()
}
```

### 5.2 属性缺失

**诊断**:

```go
// 验证属性是否设置
func validateSpanAttributes(span trace.Span) {
    required := []attribute.Key{
        "http.method",
        "http.url",
        "http.status_code",
    }
    
    // 使用ReadOnlySpan检查
    if ros, ok := span.(trace.ReadOnlySpan); ok {
        attrs := ros.Attributes()
        for _, key := range required {
            found := false
            for _, attr := range attrs {
                if attr.Key == key {
                    found = true
                    break
                }
            }
            if !found {
                log.Printf("Missing required attribute: %s", key)
            }
        }
    }
}
```

---

## 6. 性能瓶颈

### 6.1 高延迟

**排查步骤**:

```bash
# 1. 检查Collector延迟
curl -w "@curl-format.txt" -o /dev/null -s http://collector:4318/v1/traces

# curl-format.txt内容:
#     time_namelookup:  %{time_namelookup}s\n
#        time_connect:  %{time_connect}s\n
#     time_appconnect:  %{time_appconnect}s\n
#    time_pretransfer:  %{time_pretransfer}s\n
#       time_redirect:  %{time_redirect}s\n
#  time_starttransfer:  %{time_starttransfer}s\n
#          time_total:  %{time_total}s\n

# 2. 分析延迟分布
# Prometheus查询:
histogram_quantile(0.99, 
  rate(otelcol_exporter_send_failed_spans_bucket[5m])
)

# 3. 检查网络延迟
mtr collector.example.com

# 4. 检查Backend延迟
# Jaeger查询延迟
curl -w "%{time_total}" http://jaeger:16686/api/traces?service=my-service
```

### 6.2 高CPU/内存

**诊断与优化**:

```yaml
# 1. 资源监控配置
processors:
  # 限制内存使用
  memory_limiter:
    check_interval: 1s
    limit_mib: 512
    spike_limit_mib: 128
    
  # 批处理优化
  batch:
    timeout: 10s
    send_batch_size: 1024
    send_batch_max_size: 2048

# 2. 采样降低数据量
processors:
  # 尾部采样（智能采样）
  tail_sampling:
    decision_wait: 10s
    num_traces: 100
    expected_new_traces_per_sec: 10
    policies:
      # 保留错误Trace
      - name: error-traces
        type: status_code
        status_code: {status_codes: [ERROR]}
      # 慢请求Trace
      - name: slow-traces
        type: latency
        latency: {threshold_ms: 1000}
      # 随机采样
      - name: random-sample
        type: probabilistic
        probabilistic: {sampling_percentage: 10}

# 3. 限流保护
extensions:
  health_check:
    endpoint: 0.0.0.0:13133
  pprof:
    endpoint: 0.0.0.0:1777
  zpages:
    endpoint: 0.0.0.0:55679
```

**性能分析**:

```bash
# Collector性能分析
# 1. CPU Profile
curl http://collector:1777/debug/pprof/profile?seconds=30 > cpu.prof
go tool pprof cpu.prof

# 2. 内存Profile
curl http://collector:1777/debug/pprof/heap > mem.prof
go tool pprof mem.prof

# 3. Goroutine分析
curl http://collector:1777/debug/pprof/goroutine > goroutine.prof
go tool pprof goroutine.prof

# 4. zPages诊断
open http://collector:55679/debug/tracez
open http://collector:55679/debug/pipelinez
```

---

## 7. Kubernetes环境

### 7.1 Pod问题

**常见Pod问题排查**:

```bash
# 1. Pod状态检查
kubectl get pods -l app=otel-collector -o wide

# 2. Pod事件
kubectl describe pod <pod-name>

# 3. 资源使用
kubectl top pod <pod-name>

# 4. 日志查看
kubectl logs -f <pod-name> --tail=100

# 5. 容器进入
kubectl exec -it <pod-name> -- /bin/sh

# 6. 网络测试
kubectl exec <pod-name> -- wget -O- http://backend:9200/_cluster/health
```

**常见问题**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

问题1: CrashLoopBackOff
排查:
  - kubectl logs <pod> --previous  # 查看崩溃前日志
  - 检查配置ConfigMap
  - 检查Resource limits
  - 检查Liveness/Readiness probe

问题2: Pending
排查:
  - kubectl describe pod <pod>
  - 检查节点资源: kubectl describe nodes
  - 检查PVC状态
  - 检查Pod affinity/anti-affinity

问题3: ImagePullBackOff
排查:
  - 检查镜像名称和tag
  - 检查ImagePullSecrets
  - 检查私有仓库访问权限

问题4: OOMKilled
排查:
  - 增加memory limits
  - 启用memory_limiter processor
  - 优化采样策略
  - 检查内存泄漏

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 7.2 资源限制

**推荐资源配置**:

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: opentelemetry-collector
spec:
  replicas: 3
  template:
    spec:
      containers:
      - name: otel-collector
        image: otel/opentelemetry-collector:latest
        resources:
          # 请求资源
          requests:
            cpu: 200m
            memory: 256Mi
          # 限制资源
          limits:
            cpu: 1000m
            memory: 512Mi
        
        # 健康检查
        livenessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 10
          periodSeconds: 5
          
        readinessProbe:
          httpGet:
            path: /
            port: 13133
          initialDelaySeconds: 5
          periodSeconds: 3
        
        # 环境变量
        env:
        - name: GOGC
          value: "80"  # 更激进的GC
        - name: GOMEMLIMIT
          value: "450MiB"  # 内存限制

      # HPA自动扩缩容
---
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: otel-collector-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: opentelemetry-collector
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

---

## 8. Backend集成

### 8.1 Jaeger问题

**常见问题**:

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

问题1: "failed to push traces to Jaeger"
排查:
  # 检查Jaeger健康
  curl http://jaeger:14269/health
  
  # 检查Collector配置
  exporters:
    jaeger:
      endpoint: jaeger:14250
      tls:
        insecure: true  # 或配置TLS

问题2: Trace查询为空
排查:
  # 检查Elasticsearch/Cassandra
  curl http://elasticsearch:9200/_cat/indices?v
  
  # 检查Jaeger Query
  curl http://jaeger:16686/api/services
  
  # 检查时间范围和Service名称

问题3: 查询慢
优化:
  # 1. 添加索引
  # 2. 增加副本数
  # 3. 使用Span存储策略
  # 4. 定期清理旧数据

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 8.2 Prometheus问题

**Metrics导出问题**:

```yaml
# Collector配置
exporters:
  prometheus:
    endpoint: "0.0.0.0:8889"
    namespace: "otel"
    const_labels:
      environment: "production"

# Prometheus scrape配置
scrape_configs:
  - job_name: 'otel-collector'
    scrape_interval: 15s
    static_configs:
      - targets: ['otel-collector:8889']
```

**验证**:

```bash
# 1. 检查Prometheus targets
curl http://prometheus:9090/api/v1/targets | jq .

# 2. 检查metrics可用性
curl http://collector:8889/metrics

# 3. 查询示例metrics
curl -G http://prometheus:9090/api/v1/query \
  --data-urlencode 'query=otelcol_receiver_accepted_spans' | jq .
```

---

## 9. 诊断工具

### 9.1 内置工具

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Collector zpages
   URL: http://collector:55679/debug/
   功能:
   - /debug/tracez  - Trace采样查看
   - /debug/pipelinez - Pipeline状态
   - /debug/servicez - 服务信息
   - /debug/extensionz - 扩展状态

2. Collector pprof
   URL: http://collector:1777/debug/pprof/
   功能:
   - CPU profiling
   - Memory profiling
   - Goroutine分析
   - Mutex分析

3. Health Check
   URL: http://collector:13133/
   返回: {"status":"Server available"}

4. Metrics端点
   URL: http://collector:8888/metrics
   Prometheus格式metrics

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 第三方工具

```bash
# 1. grpcurl - gRPC调试
grpcurl -plaintext collector:4317 list
grpcurl -plaintext -d @ collector:4317 opentelemetry.proto.collector.trace.v1.TraceService/Export

# 2. otelcol validate - 配置验证
otelcol validate --config=/etc/otelcol/config.yaml

# 3. tcpdump - 网络抓包
tcpdump -i any -w otel.pcap 'port 4317 or port 4318'
# 用Wireshark分析otel.pcap

# 4. strace - 系统调用跟踪
strace -p <collector-pid> -f -e trace=network

# 5. OpenTelemetry Collector Builder
# 构建自定义Collector
go install go.opentelemetry.io/collector/cmd/builder@latest
builder --config=builder-config.yaml
```

---

## 10. 故障案例库

### 10.1 典型案例

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

案例1: 数据延迟增加
现象: P99延迟从100ms增加到2s
根因: Backend Elasticsearch磁盘满
解决: 
  1. 清理旧索引
  2. 增加磁盘空间
  3. 配置自动清理策略
教训: 监控Backend存储使用率

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

案例2: Collector OOM
现象: Collector频繁重启
根因: 未配置memory_limiter
解决:
  processors:
    memory_limiter:
      limit_mib: 512
教训: 生产环境必须配置资源限制

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

案例3: Trace断裂
现象: 跨服务Trace不连续
根因: 异步消息队列未传播Context
解决: 在消息中携带Trace Context
教训: 所有跨服务通信都要传播Context

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.2 罕见问题

```text
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

问题1: 时钟漂移导致Span顺序错乱
现象: 子Span时间戳早于父Span
根因: 服务器时间未同步
解决: 配置NTP，确保时间同步
检测: span.StartTime < parent.StartTime

问题2: gRPC连接泄漏
现象: 连接数持续增长
根因: SDK未正确关闭连接
解决: 确保调用Shutdown()
检测: netstat -an | grep 4317 | wc -l

问题3: Unicode属性值导致问题
现象: Backend存储错误
根因: 特殊字符未正确转义
解决: 验证和清理属性值
检测: 日志中"invalid UTF-8"

问题4: 批处理死锁
现象: 数据停止发送
根因: Batch processor bug
解决: 升级Collector版本
检测: queue_size持续为0

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**适用版本**: OpenTelemetry v1.28+  
**更新频率**: 持续更新

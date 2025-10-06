# OTLP Profiles 完整指南（eBPF Profiling）

## 目录

- [OTLP Profiles 完整指南（eBPF Profiling）](#otlp-profiles-完整指南ebpf-profiling)
  - [目录](#目录)
  - [1. Profiles 概述](#1-profiles-概述)
    - [1.1 什么是 Profiling](#11-什么是-profiling)
    - [1.2 OTLP Profiles 优势](#12-otlp-profiles-优势)
  - [2. 协议与数据模型](#2-协议与数据模型)
    - [2.1 pprof 结构](#21-pprof-结构)
    - [2.2 OTLP 封装](#22-otlp-封装)
    - [2.3 传输协议](#23-传输协议)
  - [3. 采集方式](#3-采集方式)
    - [3.1 eBPF 采集](#31-ebpf-采集)
    - [3.2 Go pprof 采集](#32-go-pprof-采集)
    - [3.3 性能开销](#33-性能开销)
  - [4. Collector 集成](#4-collector-集成)
    - [4.1 Profiling Receiver](#41-profiling-receiver)
    - [4.2 Profiling Exporter](#42-profiling-exporter)
    - [4.3 Pipeline 配置](#43-pipeline-配置)
  - [5. 后端存储](#5-后端存储)
    - [5.1 Grafana Phlare](#51-grafana-phlare)
    - [5.2 Pyroscope](#52-pyroscope)
    - [5.3 Elastic Universal Profiling](#53-elastic-universal-profiling)
  - [6. 与其他信号关联](#6-与其他信号关联)
    - [6.1 Trace-Profile 关联](#61-trace-profile-关联)
    - [6.2 统一查询](#62-统一查询)
  - [7. OPAMP 动态控制](#7-opamp-动态控制)
    - [7.1 采样频率调整](#71-采样频率调整)
    - [7.2 标签过滤](#72-标签过滤)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 生产环境配置](#81-生产环境配置)
    - [8.2 性能调优](#82-性能调优)
  - [9. Go 语言性能分析实战](#9-go-语言性能分析实战)
    - [9.1 完整的 Go 应用 Profiling 集成](#91-完整的-go-应用-profiling-集成)
    - [9.2 使用 eBPF 进行持续 Profiling](#92-使用-ebpf-进行持续-profiling)
    - [9.3 性能分析最佳实践](#93-性能分析最佳实践)
    - [9.4 与 Trace 关联](#94-与-trace-关联)
    - [9.5 Grafana 可视化](#95-grafana-可视化)
    - [9.6 生产环境 Checklist](#96-生产环境-checklist)
  - [10. 参考资料](#10-参考资料)

## 1. Profiles 概述

### 1.1 什么是 Profiling

**Profiling** 是一种性能分析技术，用于采集程序运行时的资源使用情况：

- **CPU Profiling**：函数调用栈和 CPU 时间分布
- **Memory Profiling**：内存分配和泄漏检测
- **Goroutine Profiling**：Go 协程数量和状态
- **Mutex Profiling**：锁竞争分析
- **Block Profiling**：阻塞操作分析

**应用场景**：

- 性能瓶颈定位
- 内存泄漏排查
- CPU 热点分析
- 并发问题诊断

### 1.2 OTLP Profiles 优势

**统一协议**：

- 与 Traces/Metrics/Logs 使用相同的 OTLP 协议
- 共享 Resource 语义，便于跨信号关联
- 统一的传输通道和安全机制

**语义关联**：

```text
Trace (trace_id, span_id)
  ↓ 关联
Profile (trace_id, span_id, timestamp)
  ↓ 展示
火焰图 + 调用栈
```

**云原生友好**：

- Kubernetes 自动资源标签注入
- 多租户隔离与路由
- 动态采样控制（OPAMP）

## 2. 协议与数据模型

### 2.1 pprof 结构

**Profile 数据结构**（基于 Google pprof）：

```protobuf
message Profile {
  repeated ValueType sample_type = 1;
  repeated Sample sample = 2;
  repeated Mapping mapping = 3;
  repeated Location location = 4;
  repeated Function function = 5;
  repeated string string_table = 6;
  int64 time_nanos = 9;
  int64 duration_nanos = 10;
}

message Sample {
  repeated uint64 location_id = 1;
  repeated int64 value = 2;
  repeated Label label = 3;
}

message Location {
  uint64 id = 1;
  uint64 mapping_id = 2;
  uint64 address = 3;
  repeated Line line = 4;
}
```

**示例**（CPU Profile）：

```go
import "runtime/pprof"

func captureProfile() []byte {
    var buf bytes.Buffer
    pprof.StartCPUProfile(&buf)
    defer pprof.StopCPUProfile()
    
    // 运行需要分析的代码
    doWork()
    
    return buf.Bytes()
}
```

### 2.2 OTLP 封装

**OTLP Profiles 消息**：

```protobuf
message ProfilesData {
  repeated ResourceProfiles resource_profiles = 1;
}

message ResourceProfiles {
  Resource resource = 1;
  repeated ScopeProfiles scope_profiles = 2;
  string schema_url = 3;
}

message ScopeProfiles {
  InstrumentationScope scope = 1;
  repeated ProfileContainer profiles = 2;
  string schema_url = 3;
}

message ProfileContainer {
  bytes profile_id = 1;
  fixed64 start_time_unix_nano = 2;
  fixed64 end_time_unix_nano = 3;
  repeated KeyValue attributes = 4;
  uint32 dropped_attributes_count = 5;
  bytes original_payload_format = 6;
  bytes original_payload = 7;
}
```

**Go 代码示例**：

```go
import (
    profilepb "go.opentelemetry.io/proto/otlp/profiles/v1experimental"
    commonpb "go.opentelemetry.io/proto/otlp/common/v1"
    resourcepb "go.opentelemetry.io/proto/otlp/resource/v1"
)

func createOTLPProfile(pprofData []byte) *profilepb.ProfilesData {
    return &profilepb.ProfilesData{
        ResourceProfiles: []*profilepb.ResourceProfiles{
            {
                Resource: &resourcepb.Resource{
                    Attributes: []*commonpb.KeyValue{
                        {
                            Key: "service.name",
                            Value: &commonpb.AnyValue{
                                Value: &commonpb.AnyValue_StringValue{
                                    StringValue: "my-service",
                                },
                            },
                        },
                    },
                },
                ScopeProfiles: []*profilepb.ScopeProfiles{
                    {
                        Profiles: []*profilepb.ProfileContainer{
                            {
                                ProfileId:           generateProfileID(),
                                StartTimeUnixNano:   uint64(time.Now().UnixNano()),
                                EndTimeUnixNano:     uint64(time.Now().Add(10 * time.Second).UnixNano()),
                                OriginalPayloadFormat: []byte("pprof"),
                                OriginalPayload:     pprofData,
                            },
                        },
                    },
                },
            },
        },
    }
}
```

### 2.3 传输协议

**gRPC 传输**：

```go
import "go.opentelemetry.io/otel/exporters/otlp/otlpprofile/otlpprofilegrpc"

exporter, err := otlpprofilegrpc.New(context.Background(),
    otlpprofilegrpc.WithEndpoint("localhost:4317"),
    otlpprofilegrpc.WithInsecure(),
)
```

**HTTP 传输**：

```go
import "go.opentelemetry.io/otel/exporters/otlp/otlpprofile/otlpprofilehttp"

exporter, err := otlpprofilehttp.New(context.Background(),
    otlpprofilehttp.WithEndpoint("localhost:4318"),
    otlpprofilehttp.WithURLPath("/v1/profiles"),
)
```

## 3. 采集方式

### 3.1 eBPF 采集

**优势**：

- **无侵入**：无需修改应用代码或重新编译
- **低开销**：CPU 开销 < 5%（99 Hz 采样频率）
- **全栈覆盖**：支持任何语言（Go/Java/Python/C++）

**实现**（基于 BPF CO-RE）：

```c
// eBPF 程序（简化版）
SEC("perf_event")
int profile_cpu(struct bpf_perf_event_data *ctx) {
    u64 pid_tgid = bpf_get_current_pid_tgid();
    u32 pid = pid_tgid >> 32;
    u32 tid = pid_tgid;
    
    // 获取调用栈
    struct stack_trace_t stack_trace = {};
    stack_trace.pid = pid;
    stack_trace.tid = tid;
    stack_trace.kernel_stack_id = bpf_get_stackid(ctx, &stack_traces, 0);
    stack_trace.user_stack_id = bpf_get_stackid(ctx, &stack_traces, BPF_F_USER_STACK);
    
    // 发送到用户空间
    bpf_perf_event_output(ctx, &events, BPF_F_CURRENT_CPU, &stack_trace, sizeof(stack_trace));
    return 0;
}
```

**Go 用户空间采集器**：

```go
import (
    "github.com/cilium/ebpf"
    "github.com/cilium/ebpf/perf"
)

func startEBPFProfiler() {
    // 加载 eBPF 程序
    spec, err := ebpf.LoadCollectionSpec("profiler.o")
    coll, err := ebpf.NewCollection(spec)
    defer coll.Close()
    
    // 附加到 perf_event
    perfEvent, err := perf.Open(coll.Programs["profile_cpu"], perf.Options{
        SampleFrequency: 99,  // 99 Hz
    })
    defer perfEvent.Close()
    
    // 读取事件
    reader, err := perf.NewReader(perfEvent, 4096)
    for {
        record, err := reader.Read()
        if err != nil {
            continue
        }
        
        // 处理调用栈
        processStackTrace(record.RawSample)
    }
}
```

### 3.2 Go pprof 采集

**HTTP 端点**：

```go
import _ "net/http/pprof"

func main() {
    go func() {
        http.ListenAndServe("localhost:6060", nil)
    }()
    
    // 应用逻辑
}
```

**访问**：

```bash
# CPU Profile
curl http://localhost:6060/debug/pprof/profile?seconds=30 -o cpu.pprof

# Heap Profile
curl http://localhost:6060/debug/pprof/heap -o heap.pprof

# Goroutine Profile
curl http://localhost:6060/debug/pprof/goroutine -o goroutine.pprof
```

**程序化采集**：

```go
import (
    "runtime/pprof"
    "os"
)

func captureCPUProfile() {
    f, _ := os.Create("cpu.pprof")
    defer f.Close()
    
    pprof.StartCPUProfile(f)
    defer pprof.StopCPUProfile()
    
    // 运行需要分析的代码
    doWork()
}

func captureHeapProfile() {
    f, _ := os.Create("heap.pprof")
    defer f.Close()
    
    pprof.WriteHeapProfile(f)
}
```

### 3.3 性能开销

**eBPF Profiling 开销**：

| 采样频率 | CPU 开销 | 内存开销 | 适用场景 |
|---------|---------|---------|---------|
| 49 Hz | < 2% | ~10 MB | 生产环境（低开销） |
| 99 Hz | < 5% | ~20 MB | 生产环境（推荐） |
| 250 Hz | ~10% | ~50 MB | 性能调优 |
| 1000 Hz | ~30% | ~100 MB | 开发环境 |

**Go pprof 开销**：

| Profile 类型 | CPU 开销 | 内存开销 | 采集时长 |
|-------------|---------|---------|---------|
| CPU | 5-10% | 低 | 30-60s |
| Heap | < 1% | 中 | 瞬时 |
| Goroutine | < 1% | 低 | 瞬时 |
| Mutex | 10-20% | 低 | 30-60s |

## 4. Collector 集成

### 4.1 Profiling Receiver

**配置**（opentelemetry-collector-contrib）：

```yaml
receivers:
  # eBPF Profiling Receiver
  profiling:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
      http:
        endpoint: 0.0.0.0:4318
    
    # 采样配置
    sampling:
      frequency_hz: 99
      duration_seconds: 10
    
    # 过滤规则
    filters:
      - include:
          resource_attributes:
            service.name: "my-service"
```

### 4.2 Profiling Exporter

**Grafana Phlare**：

```yaml
exporters:
  phlare:
    endpoint: http://phlare:4100
    tls:
      insecure: true
    headers:
      x-scope-orgid: "tenant-1"
```

**Pyroscope**：

```yaml
exporters:
  pyroscope:
    endpoint: http://pyroscope:4040
    application_name: "my-service"
    tags:
      env: "production"
      region: "us-west"
```

### 4.3 Pipeline 配置

**完整 Pipeline**：

```yaml
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317
  
  profiling:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4318

processors:
  batch:
    timeout: 10s
    send_batch_size: 100
  
  resource:
    attributes:
      - key: deployment.environment
        value: production
        action: insert
  
  # Profile 特定处理
  transform:
    profiles:
      - set(attributes["profile.type"], "cpu")
        where resource.attributes["service.name"] == "my-service"

exporters:
  phlare:
    endpoint: http://phlare:4100
  
  otlp:
    endpoint: backend.example.com:4317

service:
  pipelines:
    profiles:
      receivers: [otlp, profiling]
      processors: [batch, resource, transform]
      exporters: [phlare, otlp]
```

## 5. 后端存储

### 5.1 Grafana Phlare

**特性**：

- 原生 OTLP 支持
- 与 Grafana 深度集成
- 高效的列式存储（Parquet）
- 多租户支持

**部署**：

```yaml
version: '3'
services:
  phlare:
    image: grafana/phlare:latest
    ports:
      - "4100:4100"
    volumes:
      - phlare-data:/data
    command:
      - -config.file=/etc/phlare/config.yaml
```

**查询**：

```promql
# 查询 CPU Profile
{service_name="my-service", profile_type="cpu"}

# 过滤特定函数
{service_name="my-service"} | function =~ ".*Handler.*"
```

### 5.2 Pyroscope

**特性**：

- 实时火焰图
- 时间范围对比
- 标签过滤
- 多语言支持

**Go SDK 集成**：

```go
import "github.com/grafana/pyroscope-go"

func main() {
    pyroscope.Start(pyroscope.Config{
        ApplicationName: "my-service",
        ServerAddress:   "http://pyroscope:4040",
        Tags: map[string]string{
            "env": "production",
        },
        ProfileTypes: []pyroscope.ProfileType{
            pyroscope.ProfileCPU,
            pyroscope.ProfileAllocObjects,
            pyroscope.ProfileAllocSpace,
            pyroscope.ProfileInuseObjects,
            pyroscope.ProfileInuseSpace,
        },
    })
}
```

### 5.3 Elastic Universal Profiling

**特性**：

- 全栈 Profiling（内核 + 用户空间）
- 自动符号解析
- 与 APM 集成
- Fleet 管理

**配置**：

```yaml
# elastic-agent.yml
inputs:
  - type: profiling
    enabled: true
    sampling_frequency: 99
    
outputs:
  default:
    type: elasticsearch
    hosts: ["https://elasticsearch:9200"]
```

## 6. 与其他信号关联

### 6.1 Trace-Profile 关联

**Span 中注入 Profile ID**：

```go
import (
    "go.opentelemetry.io/otel/trace"
    "go.opentelemetry.io/otel/attribute"
)

func handleRequest(w http.ResponseWriter, r *http.Request) {
    ctx, span := tracer.Start(r.Context(), "handle-request")
    defer span.End()
    
    // 采集 Profile
    profileID := captureProfile()
    
    // 注入到 Span
    span.SetAttributes(
        attribute.String("profile.id", profileID),
        attribute.String("profile.type", "cpu"),
    )
    
    // 业务逻辑
    processRequest(ctx)
}
```

**查询关联**：

```sql
-- 查询 Trace
SELECT * FROM traces WHERE trace_id = 'abc123';

-- 根据 Span 中的 profile.id 查询 Profile
SELECT * FROM profiles WHERE profile_id = 'xyz789';
```

### 6.2 统一查询

**Grafana 面板**：

```json
{
  "panels": [
    {
      "type": "trace",
      "datasource": "Tempo",
      "targets": [
        {"query": "trace_id=abc123"}
      ]
    },
    {
      "type": "flamegraph",
      "datasource": "Phlare",
      "targets": [
        {"query": "{trace_id=\"abc123\"}"}
      ]
    }
  ]
}
```

## 7. OPAMP 动态控制

### 7.1 采样频率调整

**OPAMP 配置下发**：

```yaml
# Server 下发配置
remote_config:
  receivers:
    profiling:
      sampling:
        frequency_hz: 49  # 从 99 Hz 降至 49 Hz
        duration_seconds: 5  # 从 10s 降至 5s
```

**响应时间**：10 秒内集群级生效

### 7.2 标签过滤

**动态过滤规则**：

```yaml
remote_config:
  processors:
    filter:
      profiles:
        include:
          match_type: strict
          resource_attributes:
            - key: service.name
              value: "critical-service"
        exclude:
          match_type: regexp
          resource_attributes:
            - key: service.name
              value: ".*-test"
```

## 8. 最佳实践

### 8.1 生产环境配置

**推荐设置**：

```yaml
# Collector 配置
receivers:
  profiling:
    sampling:
      frequency_hz: 99  # 平衡精度与开销
      duration_seconds: 10
    
    # 仅采集关键服务
    filters:
      - include:
          resource_attributes:
            tier: "critical"

processors:
  batch:
    timeout: 30s  # Profile 数据较大，增加批次时间
    send_batch_size: 50
  
  memory_limiter:
    limit_mib: 1024  # Profile 占用内存较多

exporters:
  phlare:
    endpoint: http://phlare:4100
    retry_on_failure:
      enabled: true
      max_elapsed_time: 5m
```

### 8.2 性能调优

**采样策略**：

| 环境 | 采样频率 | 采集时长 | 保留时间 |
|------|---------|---------|---------|
| 开发 | 250 Hz | 30s | 7 天 |
| 测试 | 99 Hz | 10s | 14 天 |
| 生产 | 49-99 Hz | 5-10s | 30 天 |

**存储优化**：

```yaml
# Phlare 配置
storage:
  # 使用对象存储
  backend: s3
  s3:
    bucket: profiles-bucket
    region: us-west-2
  
  # 数据压缩
  compression: zstd
  
  # 保留策略
  retention:
    period: 30d
    max_size_gb: 1000
```

## 9. Go 语言性能分析实战

### 9.1 完整的 Go 应用 Profiling 集成

**生产级 Go 应用集成**：

```go
package main

import (
    "context"
    "fmt"
    "log"
    "net/http"
    "net/http/pprof"
    "os"
    "runtime"
    "time"

    "go.opentelemetry.io/contrib/instrumentation/runtime"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlpmetric/otlpmetricgrpc"
    "go.opentelemetry.io/otel/sdk/metric"
    "go.opentelemetry.io/otel/sdk/resource"
    semconv "go.opentelemetry.io/otel/semconv/v1.24.0"
)

type ProfileCollector struct {
    meterProvider *metric.MeterProvider
    stopChan      chan struct{}
}

func NewProfileCollector(endpoint string) (*ProfileCollector, error) {
    ctx := context.Background()
    
    // 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceName("my-go-app"),
            semconv.ServiceVersion("1.0.0"),
            semconv.DeploymentEnvironment(os.Getenv("ENV")),
        ),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create resource: %w", err)
    }
    
    // 创建 OTLP 导出器
    exporter, err := otlpmetricgrpc.New(ctx,
        otlpmetricgrpc.WithEndpoint(endpoint),
        otlpmetricgrpc.WithInsecure(),
    )
    if err != nil {
        return nil, fmt.Errorf("failed to create exporter: %w", err)
    }
    
    // 创建 MeterProvider
    meterProvider := metric.NewMeterProvider(
        metric.WithResource(res),
        metric.WithReader(metric.NewPeriodicReader(exporter,
            metric.WithInterval(10*time.Second),
        )),
    )
    
    otel.SetMeterProvider(meterProvider)
    
    // 启动 runtime metrics 收集
    if err := runtime.Start(runtime.WithMinimumReadMemStatsInterval(time.Second)); err != nil {
        return nil, fmt.Errorf("failed to start runtime metrics: %w", err)
    }
    
    pc := &ProfileCollector{
        meterProvider: meterProvider,
        stopChan:      make(chan struct{}),
    }
    
    // 启动自定义 profiling
    go pc.collectProfiles()
    
    return pc, nil
}

func (pc *ProfileCollector) collectProfiles() {
    ticker := time.NewTicker(30 * time.Second)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            pc.captureProfile()
        case <-pc.stopChan:
            return
        }
    }
}

func (pc *ProfileCollector) captureProfile() {
    // CPU Profile
    cpuProfile := captureC CPUProfile(5 * time.Second)
    if cpuProfile != nil {
        pc.sendProfile("cpu", cpuProfile)
    }
    
    // Heap Profile
    heapProfile := captureHeapProfile()
    if heapProfile != nil {
        pc.sendProfile("heap", heapProfile)
    }
    
    // Goroutine Profile
    goroutineProfile := captureGoroutineProfile()
    if goroutineProfile != nil {
        pc.sendProfile("goroutine", goroutineProfile)
    }
}

func captureCPUProfile(duration time.Duration) []byte {
    // 实现 CPU profiling 捕获
    // 返回 pprof 格式数据
    return nil
}

func captureHeapProfile() []byte {
    // 实现 Heap profiling 捕获
    return nil
}

func captureGoroutineProfile() []byte {
    // 实现 Goroutine profiling 捕获
    return nil
}

func (pc *ProfileCollector) sendProfile(profileType string, data []byte) {
    // 发送 profile 数据到 OTLP Collector
    log.Printf("Sending %s profile (%d bytes)", profileType, len(data))
}

func (pc *ProfileCollector) Shutdown(ctx context.Context) error {
    close(pc.stopChan)
    return pc.meterProvider.Shutdown(ctx)
}

// HTTP pprof 端点
func setupPprofEndpoints() {
    mux := http.NewServeMux()
    
    // 标准 pprof 端点
    mux.HandleFunc("/debug/pprof/", pprof.Index)
    mux.HandleFunc("/debug/pprof/cmdline", pprof.Cmdline)
    mux.HandleFunc("/debug/pprof/profile", pprof.Profile)
    mux.HandleFunc("/debug/pprof/symbol", pprof.Symbol)
    mux.HandleFunc("/debug/pprof/trace", pprof.Trace)
    
    // 自定义端点：获取当前内存统计
    mux.HandleFunc("/debug/pprof/memstats", func(w http.ResponseWriter, r *http.Request) {
        var m runtime.MemStats
        runtime.ReadMemStats(&m)
        
        fmt.Fprintf(w, "Alloc = %v MB\n", m.Alloc/1024/1024)
        fmt.Fprintf(w, "TotalAlloc = %v MB\n", m.TotalAlloc/1024/1024)
        fmt.Fprintf(w, "Sys = %v MB\n", m.Sys/1024/1024)
        fmt.Fprintf(w, "NumGC = %v\n", m.NumGC)
        fmt.Fprintf(w, "NumGoroutine = %v\n", runtime.NumGoroutine())
    })
    
    go func() {
        log.Println("Starting pprof server on :6060")
        if err := http.ListenAndServe(":6060", mux); err != nil {
            log.Printf("pprof server error: %v", err)
        }
    }()
}

func main() {
    // 设置 GOMAXPROCS
    runtime.GOMAXPROCS(runtime.NumCPU())
    
    // 启动 pprof HTTP 端点
    setupPprofEndpoints()
    
    // 创建 Profile Collector
    collector, err := NewProfileCollector("collector:4317")
    if err != nil {
        log.Fatalf("Failed to create profile collector: %v", err)
    }
    defer collector.Shutdown(context.Background())
    
    // 启动应用
    log.Println("Application started")
    
    // 模拟工作负载
    for {
        doWork()
        time.Sleep(100 * time.Millisecond)
    }
}

func doWork() {
    // 模拟 CPU 密集型工作
    for i := 0; i < 1000000; i++ {
        _ = i * i
    }
    
    // 模拟内存分配
    data := make([]byte, 1024*1024)
    _ = data
}
```

### 9.2 使用 eBPF 进行持续 Profiling

**eBPF Profiler 集成**：

```go
package main

import (
    "context"
    "fmt"
    "log"
    "time"

    "github.com/cilium/ebpf"
    "github.com/cilium/ebpf/link"
    "github.com/cilium/ebpf/perf"
)

type EBPFProfiler struct {
    collection *ebpf.Collection
    reader     *perf.Reader
    stopChan   chan struct{}
}

func NewEBPFProfiler() (*EBPFProfiler, error) {
    // 加载 eBPF 程序
    spec, err := ebpf.LoadCollectionSpec("profiler.o")
    if err != nil {
        return nil, fmt.Errorf("failed to load eBPF spec: %w", err)
    }
    
    coll, err := ebpf.NewCollection(spec)
    if err != nil {
        return nil, fmt.Errorf("failed to create collection: %w", err)
    }
    
    // 附加到 perf 事件
    prog := coll.Programs["profile_cpu"]
    link, err := link.AttachPerfEvent(link.PerfEventOptions{
        Program:   prog,
        SampleFrequency: 99, // 99 Hz
    })
    if err != nil {
        coll.Close()
        return nil, fmt.Errorf("failed to attach perf event: %w", err)
    }
    defer link.Close()
    
    // 创建 perf reader
    reader, err := perf.NewReader(coll.Maps["events"], 4096)
    if err != nil {
        coll.Close()
        return nil, fmt.Errorf("failed to create perf reader: %w", err)
    }
    
    profiler := &EBPFProfiler{
        collection: coll,
        reader:     reader,
        stopChan:   make(chan struct{}),
    }
    
    go profiler.readEvents()
    
    return profiler, nil
}

func (p *EBPFProfiler) readEvents() {
    for {
        select {
        case <-p.stopChan:
            return
        default:
            record, err := p.reader.Read()
            if err != nil {
                if perf.IsClosed(err) {
                    return
                }
                log.Printf("Error reading perf event: %v", err)
                continue
            }
            
            // 处理 profiling 事件
            p.processEvent(record.RawSample)
        }
    }
}

func (p *EBPFProfiler) processEvent(data []byte) {
    // 解析堆栈跟踪
    // 聚合样本
    // 发送到 OTLP Collector
}

func (p *EBPFProfiler) Close() error {
    close(p.stopChan)
    p.reader.Close()
    return p.collection.Close()
}
```

### 9.3 性能分析最佳实践

**1. 内存泄漏检测**：

```go
package main

import (
    "log"
    "runtime"
    "time"
)

type MemoryLeakDetector struct {
    baseline  runtime.MemStats
    threshold float64 // 增长阈值（百分比）
}

func NewMemoryLeakDetector(threshold float64) *MemoryLeakDetector {
    var baseline runtime.MemStats
    runtime.ReadMemStats(&baseline)
    
    return &MemoryLeakDetector{
        baseline:  baseline,
        threshold: threshold,
    }
}

func (d *MemoryLeakDetector) Check() bool {
    var current runtime.MemStats
    runtime.ReadMemStats(&current)
    
    // 计算内存增长
    growth := float64(current.Alloc-d.baseline.Alloc) / float64(d.baseline.Alloc) * 100
    
    if growth > d.threshold {
        log.Printf("WARNING: Memory leak detected! Growth: %.2f%%", growth)
        log.Printf("  Baseline Alloc: %d MB", d.baseline.Alloc/1024/1024)
        log.Printf("  Current Alloc: %d MB", current.Alloc/1024/1024)
        log.Printf("  NumGC: %d", current.NumGC)
        
        // 触发 heap dump
        d.captureHeapDump()
        return true
    }
    
    return false
}

func (d *MemoryLeakDetector) captureHeapDump() {
    filename := fmt.Sprintf("heap-%d.prof", time.Now().Unix())
    f, err := os.Create(filename)
    if err != nil {
        log.Printf("Failed to create heap dump: %v", err)
        return
    }
    defer f.Close()
    
    runtime.GC() // 强制 GC
    if err := pprof.WriteHeapProfile(f); err != nil {
        log.Printf("Failed to write heap profile: %v", err)
    } else {
        log.Printf("Heap dump saved to %s", filename)
    }
}

func (d *MemoryLeakDetector) Start(interval time.Duration) {
    ticker := time.NewTicker(interval)
    defer ticker.Stop()
    
    for range ticker.C {
        d.Check()
    }
}
```

**2. Goroutine 泄漏检测**：

```go
package main

import (
    "log"
    "runtime"
    "time"
)

type GoroutineLeakDetector struct {
    baseline  int
    threshold int
}

func NewGoroutineLeakDetector(threshold int) *GoroutineLeakDetector {
    return &GoroutineLeakDetector{
        baseline:  runtime.NumGoroutine(),
        threshold: threshold,
    }
}

func (d *GoroutineLeakDetector) Check() bool {
    current := runtime.NumGoroutine()
    increase := current - d.baseline
    
    if increase > d.threshold {
        log.Printf("WARNING: Goroutine leak detected!")
        log.Printf("  Baseline: %d", d.baseline)
        log.Printf("  Current: %d", current)
        log.Printf("  Increase: %d", increase)
        
        // 捕获 goroutine profile
        d.captureGoroutineProfile()
        return true
    }
    
    return false
}

func (d *GoroutineLeakDetector) captureGoroutineProfile() {
    filename := fmt.Sprintf("goroutine-%d.prof", time.Now().Unix())
    f, err := os.Create(filename)
    if err != nil {
        log.Printf("Failed to create goroutine profile: %v", err)
        return
    }
    defer f.Close()
    
    if err := pprof.Lookup("goroutine").WriteTo(f, 2); err != nil {
        log.Printf("Failed to write goroutine profile: %v", err)
    } else {
        log.Printf("Goroutine profile saved to %s", filename)
    }
}
```

**3. CPU 热点分析**：

```go
package main

import (
    "fmt"
    "log"
    "os"
    "runtime/pprof"
    "time"
)

type CPUProfiler struct {
    duration time.Duration
}

func NewCPUProfiler(duration time.Duration) *CPUProfiler {
    return &CPUProfiler{duration: duration}
}

func (p *CPUProfiler) Profile() error {
    filename := fmt.Sprintf("cpu-%d.prof", time.Now().Unix())
    f, err := os.Create(filename)
    if err != nil {
        return fmt.Errorf("failed to create CPU profile: %w", err)
    }
    defer f.Close()
    
    log.Printf("Starting CPU profiling for %v...", p.duration)
    
    if err := pprof.StartCPUProfile(f); err != nil {
        return fmt.Errorf("failed to start CPU profile: %w", err)
    }
    
    time.Sleep(p.duration)
    
    pprof.StopCPUProfile()
    
    log.Printf("CPU profile saved to %s", filename)
    log.Println("Analyze with: go tool pprof -http=:8080 " + filename)
    
    return nil
}

// 自动分析 CPU 热点
func (p *CPUProfiler) AnalyzeHotspots() {
    // 使用 pprof 包分析
    // 识别 CPU 占用最高的函数
}
```

### 9.4 与 Trace 关联

**Profile-Trace 关联示例**：

```go
package main

import (
    "context"
    "fmt"
    "runtime/pprof"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

func processRequest(ctx context.Context, requestID string) error {
    tracer := otel.Tracer("my-service")
    ctx, span := tracer.Start(ctx, "processRequest",
        trace.WithAttributes(
            attribute.String("request.id", requestID),
        ),
    )
    defer span.End()
    
    // 在 Span 中添加 profile 标签
    labels := pprof.Labels(
        "trace_id", span.SpanContext().TraceID().String(),
        "span_id", span.SpanContext().SpanID().String(),
        "request_id", requestID,
    )
    
    // 在 profile 上下文中执行
    pprof.Do(ctx, labels, func(ctx context.Context) {
        // 执行实际工作
        doWork(ctx)
    })
    
    return nil
}

func doWork(ctx context.Context) {
    // CPU 密集型操作
    // Profile 会自动关联到 Trace
}
```

### 9.5 Grafana 可视化

**查询 Profile 数据**：

```promql
# 查看 CPU 使用率趋势
rate(process_cpu_seconds_total{service="my-go-app"}[5m])

# 查看内存使用
process_resident_memory_bytes{service="my-go-app"}

# 查看 Goroutine 数量
go_goroutines{service="my-go-app"}

# 查看 GC 暂停时间
rate(go_gc_duration_seconds_sum[5m]) / rate(go_gc_duration_seconds_count[5m])
```

**Grafana Dashboard JSON**：

```json
{
  "dashboard": {
    "title": "Go Application Profiling",
    "panels": [
      {
        "title": "CPU Usage",
        "targets": [
          {
            "expr": "rate(process_cpu_seconds_total{service=\"$service\"}[5m])"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Memory Usage",
        "targets": [
          {
            "expr": "process_resident_memory_bytes{service=\"$service\"}"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Goroutines",
        "targets": [
          {
            "expr": "go_goroutines{service=\"$service\"}"
          }
        ],
        "type": "graph"
      },
      {
        "title": "GC Pause",
        "targets": [
          {
            "expr": "rate(go_gc_duration_seconds_sum{service=\"$service\"}[5m]) / rate(go_gc_duration_seconds_count{service=\"$service\"}[5m])"
          }
        ],
        "type": "graph"
      },
      {
        "title": "Flame Graph",
        "type": "flamegraph",
        "datasource": "Phlare",
        "targets": [
          {
            "profileTypeId": "process_cpu:cpu:nanoseconds:cpu:nanoseconds",
            "labelSelector": "{service=\"$service\"}"
          }
        ]
      }
    ]
  }
}
```

### 9.6 生产环境 Checklist

**部署前检查清单**：

- [ ] 启用 pprof HTTP 端点（仅内部访问）
- [ ] 配置合理的采样频率（49-99 Hz）
- [ ] 设置 profile 数据保留时间（30 天）
- [ ] 配置内存/Goroutine 泄漏检测
- [ ] 设置告警规则（CPU/内存/Goroutine 阈值）
- [ ] 验证 Profile-Trace 关联
- [ ] 测试 profile 数据导出
- [ ] 配置 Grafana Dashboard
- [ ] 文档化分析流程

**性能基准**：

| 指标 | 目标值 | 告警阈值 |
|------|--------|---------|
| CPU 使用率 | < 70% | > 85% |
| 内存使用 | < 80% | > 90% |
| Goroutine 数量 | < 10000 | > 50000 |
| GC 暂停时间 | < 10ms | > 50ms |
| Profile 开销 | < 5% CPU | > 10% CPU |

## 10. 参考资料

- **OTLP Profiles 规范**：[opentelemetry-proto/profiles](https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles)
- **Grafana Phlare**：<https://grafana.com/oss/phlare/>
- **Pyroscope**：<https://pyroscope.io/>
- **eBPF Profiling**：<https://ebpf.io/>
- **Go pprof**：<https://pkg.go.dev/runtime/pprof>
- **OPAMP 控制**：`docs/opamp/overview.md`
- **语义模型**：`docs/otlp/semantic-model.md`

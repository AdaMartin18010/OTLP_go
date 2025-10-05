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
  - [9. 参考资料](#9-参考资料)

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

## 9. 参考资料

- **OTLP Profiles 规范**：[opentelemetry-proto/profiles](https://github.com/open-telemetry/opentelemetry-proto/tree/main/opentelemetry/proto/profiles)
- **Grafana Phlare**：<https://grafana.com/oss/phlare/>
- **Pyroscope**：<https://pyroscope.io/>
- **eBPF Profiling**：<https://ebpf.io/>
- **Go pprof**：<https://pkg.go.dev/runtime/pprof>
- **OPAMP 控制**：`docs/opamp/overview.md`
- **语义模型**：`docs/otlp/semantic-model.md`

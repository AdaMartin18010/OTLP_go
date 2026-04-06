# eBPF HTTP Tracer

> 基于eBPF uprobes的Go HTTP零侵入追踪器

## 架构

```
User Space                    Kernel Space
┌─────────────┐              ┌───────────────────────┐
│  Go App     │              │      eBPF VM          │
│  (Target)   │              │  ┌─────────────────┐  │
│             │              │  │  uprobe         │  │
│ ServeHTTP() │─────────────▶│  │  uretprobe      │  │
│             │              │  │                 │  │
└─────────────┘              │  │  Capture:       │  │
       │                     │  │  - timestamp    │  │
       │                     │  │  - method       │  │
       │                     │  │  - path         │  │
       │                     │  │  - duration     │  │
       │                     │  └────────┬────────┘  │
       │                     │           │           │
       │                     │  ┌────────▼────────┐  │
       │                     │  │   Ring Buffer   │  │
       │                     │  └────────┬────────┘  │
       │                     └───────────┼───────────┘
       │                                 │
       │                                 ▼
       │                     ┌───────────────────────┐
       │                     │   perf_event_output   │
       │                     └───────────┬───────────┘
       │                                 │
       ▼                                 ▼
┌─────────────────────────────────────────────────────┐
│              Tracer (Loader Program)                 │
│  ┌─────────────────────────────────────────────────┐│
│  │  1. Load eBPF objects into kernel               ││
│  │  2. Attach uprobes to target binary             ││
│  │  3. Read events from ring buffer                ││
│  │  4. Convert to OpenTelemetry spans              ││
│  └─────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────┘
```

## 编译

### 前置要求

```bash
# Linux 5.4+
uname -r

# 安装依赖
sudo apt-get update
sudo apt-get install -y \
    clang llvm libbpf-dev \
    linux-headers-$(uname -r)

# 安装bpf2go
go install github.com/cilium/ebpf/cmd/bpf2go@latest
```

### 生成eBPF代码

```bash
cd pkg/ebpf/tracer

go generate .

# 或手动运行
bpf2go -target amd64 -type http_event tracer bpf/http_trace.c
```

### 构建

```bash
# 作为库使用
go build ./pkg/ebpf/tracer

# 或运行示例
go run ./pkg/ebpf/examples/http_trace
```

## 使用

### 追踪指定程序

```bash
# 编译示例HTTP服务
go build -o /tmp/test-server ./examples/http-server

# 运行追踪器
sudo go run ./pkg/ebpf/examples/http_trace -binary /tmp/test-server
```

### 作为库使用

```go
import "your-module/pkg/ebpf/tracer"

func main() {
    cfg := &tracer.Config{
        BinaryPath: "/path/to/your/app",
    }
    
    t, err := tracer.New(cfg, tracerProvider)
    if err != nil {
        log.Fatal(err)
    }
    
    if err := t.Load(); err != nil {
        log.Fatal(err)
    }
    
    if err := t.Attach(); err != nil {
        log.Fatal(err)
    }
    
    ctx := context.Background()
    if err := t.Start(ctx); err != nil {
        log.Fatal(err)
    }
    
    defer t.Stop()
    
    // Wait...
    select {}
}
```

## 事件结构

```go
type HTTPEvent struct {
    Timestamp   uint64    // nanoseconds since boot
    PID         uint32    // process ID
    TID         uint32    // thread ID
    DurationNs  uint64    // request duration in nanoseconds
    StatusCode  uint16    // HTTP status (if available)
    MethodLen   uint16    // method string length
    PathLen     uint16    // path string length
    Method      [8]byte   // HTTP method
    Path        [128]byte // request path
    RemoteAddr  [64]byte  // remote address
}
```

## 性能

| 指标 | 数值 | 说明 |
|------|------|------|
| 延迟开销 | ~100ns | uprobe进入/退出 |
| CPU占用 | <1% | 典型HTTP服务 |
| 内存占用 | ~2MB | eBPF maps + buffer |

## 限制

1. **需要root权限** - 加载eBPF程序需要CAP_SYS_ADMIN
2. **内核版本** - 需要Linux 5.4+ (ring buffer)
3. **目标符号** - 需要未被stripped的二进制文件
4. **Go版本** - 结构体偏移量可能因Go版本变化

## 调试

```bash
# 查看eBPF程序加载状态
sudo bpftool prog list

# 查看maps
sudo bpftool map list

# 查看trace pipe
sudo cat /sys/kernel/debug/tracing/trace_pipe
```

## 参考

- [Cilium eBPF](https://github.com/cilium/ebpf)
- [eBPF.io](https://ebpf.io/)

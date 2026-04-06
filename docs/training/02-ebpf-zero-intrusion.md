# 内部培训: eBPF零侵入可观测性

> **培训对象**: 平台工程团队
> **时长**: 3小时
> **目标**: 掌握eBPF原理与Go应用零侵入追踪

---

## 📚 培训大纲

### 第一部分: eBPF基础 (45分钟)

#### 1.1 什么是eBPF?

```
eBPF = extended Berkeley Packet Filter

传统BPF: 网络包过滤
eBPF: 通用内核虚拟机

┌─────────────────────────────────────────────────────────────┐
│                      eBPF架构                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  User Space                    Kernel Space                 │
│  ┌─────────────┐               ┌───────────────────────┐   │
│  │   Go Code   │               │      eBPF VM          │   │
│  │  (Control)  │ ──compile──▶  │  ┌─────────────────┐  │   │
│  │             │               │  │  eBPF Program   │  │   │
│  │  libbpf-go  │ ◀──maps─────  │  │  - kprobe       │  │   │
│  │  (Loader)   │               │  │  - uprobe       │  │   │
│  └─────────────┘               │  │  - tracepoint   │  │   │
│                                │  │  - XDP          │  │   │
│                                │  └─────────────────┘  │   │
│                                │           │           │   │
│                                │           ▼           │   │
│                                │  ┌─────────────────┐  │   │
│                                │  │   Hook Points   │  │   │
│                                │  │  - Kernel funcs │  │   │
│                                │  │  - User funcs   │  │   │
│                                │  │  - Network stack│  │   │
│                                │  └─────────────────┘  │   │
│                                └───────────────────────┘   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

#### 1.2 eBPF程序类型

| 类型 | 用途 | Go应用 |
|------|------|--------|
| **kprobe** | 内核函数追踪 | GC监控 |
| **uprobe** | 用户函数追踪 | HTTP/gRPC追踪 |
| **tracepoint** | 内核静态追踪 | 调度事件 |
| **perf_event** | 性能监控 | CPU剖析 |

#### 1.3 为什么eBPF适合Go?

```
传统方式的问题:
1. Go无注解/Aspect - 无法AOP
2. runtime.GoroutineProfile() - 侵入式
3. 反射性能差 - 不适合高频调用

eBPF解决方案:
1. 无需修改代码 - 真正零侵入
2. 内核级性能 - 纳秒级开销
3. 安全沙箱 - 验证器保证安全
```

---

### 第二部分: Go + eBPF实战 (60分钟)

#### 2.1 环境准备

```bash
# 系统要求
uname -r  # >= 5.4

# 安装依赖
sudo apt-get update
sudo apt-get install -y \
    llvm clang libbpf-dev \
    linux-headers-$(uname -r) \
    linux-tools-common linux-tools-generic

# Go库
go get github.com/cilium/ebpf
```

#### 2.2 第一个eBPF程序: HTTP追踪

```c
// bpf/http_trace.c
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

// 事件结构
struct http_event {
    u64 timestamp;
    u32 pid;
    char method[8];
    char path[128];
    u64 duration_ns;
};

// Ring buffer输出
struct {
    __uint(type, BPF_MAP_TYPE_RINGBUF);
    __uint(max_entries, 256 * 1024);
} events SEC(".maps");

// 活跃的请求 (临时存储开始时间)
struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 10240);
    __type(key, u64);      // pid << 32 | tid
    __type(value, u64);    // start timestamp
} active_requests SEC(".maps");

// uprobe: ServeHTTP入口
SEC("uprobe/net_http_Server_ServeHTTP")
int BPF_KPROBE(trace_serve_http_entry, void *w, void *r) {
    u64 pid_tgid = bpf_get_current_pid_tgid();
    u64 ts = bpf_ktime_get_ns();

    // 记录开始时间
    bpf_map_update_elem(&active_requests, &pid_tgid, &ts, BPF_ANY);

    return 0;
}

// uretprobe: ServeHTTP出口
SEC("uretprobe/net_http_Server_ServeHTTP")
int BPF_KPROBE(trace_serve_http_exit) {
    u64 pid_tgid = bpf_get_current_pid_tgid();

    // 获取开始时间
    u64 *start_ts = bpf_map_lookup_elem(&active_requests, &pid_tgid);
    if (!start_ts) return 0;

    // 分配事件
    struct http_event *e = bpf_ringbuf_reserve(&events, sizeof(*e), 0);
    if (!e) {
        bpf_map_delete_elem(&active_requests, &pid_tgid);
        return 0;
    }

    // 填充数据
    e->timestamp = *start_ts;
    e->pid = pid_tgid >> 32;
    e->duration_ns = bpf_ktime_get_ns() - *start_ts;

    // 读取HTTP方法 (简化示例)
    bpf_probe_read_str(e->method, sizeof(e->method), "GET");
    bpf_probe_read_str(e->path, sizeof(e->path), "/api/example");

    // 提交事件
    bpf_ringbuf_submit(e, 0);
    bpf_map_delete_elem(&active_requests, &pid_tgid);

    return 0;
}

char LICENSE[] SEC("license") = "Dual MIT/GPL";
```

#### 2.3 Go加载器

```go
package main

import (
    "fmt"
    "log"
    "os"
    "os/signal"

    "github.com/cilium/ebpf"
    "github.com/cilium/ebpf/link"
    "github.com/cilium/ebpf/perf"
)

func main() {
    // 1. 编译eBPF (或加载预编译的)
    spec, err := ebpf.LoadCollectionSpec("http_trace.o")
    if err != nil {
        log.Fatal(err)
    }

    // 2. 加载到内核
    objs := struct {
        Programs struct {
            TraceServeHttpEntry *ebpf.Program `ebpf:"trace_serve_http_entry"`
            TraceServeHttpExit  *ebpf.Program `ebpf:"trace_serve_http_exit"`
        }
        Maps struct {
            Events *ebpf.Map `ebpf:"events"`
        }
    }{}

    if err := spec.LoadAndAssign(&objs, nil); err != nil {
        log.Fatal(err)
    }
    defer objs.Programs.TraceServeHttpEntry.Close()
    defer objs.Programs.TraceServeHttpExit.Close()
    defer objs.Maps.Events.Close()

    // 3. 附加uprobe
    // 假设我们要追踪 /usr/local/bin/myapp
    ex, err := link.OpenExecutable("/usr/local/bin/myapp")
    if err != nil {
        log.Fatal(err)
    }

    entryLink, err := ex.Uprobe(
        "net/http.(*Server).ServeHTTP",
        objs.Programs.TraceServeHttpEntry,
        nil,
    )
    if err != nil {
        log.Fatal(err)
    }
    defer entryLink.Close()

    exitLink, err := ex.Uretprobe(
        "net/http.(*Server).ServeHTTP",
        objs.Programs.TraceServeHttpExit,
        nil,
    )
    if err != nil {
        log.Fatal(err)
    }
    defer exitLink.Close()

    // 4. 读取事件
    rd, err := perf.NewReader(objs.Maps.Events, os.Getpagesize())
    if err != nil {
        log.Fatal(err)
    }
    defer rd.Close()

    // 5. 处理信号
    sig := make(chan os.Signal, 1)
    signal.Notify(sig, os.Interrupt)

    go func() {
        <-sig
        rd.Close()
    }()

    // 6. 读取事件循环
    fmt.Println("Tracing HTTP requests... Ctrl+C to stop")

    for {
        record, err := rd.Read()
        if err != nil {
            if perf.IsClosed(err) {
                return
            }
            log.Printf("reading from perf event reader: %s", err)
            continue
        }

        // 解析事件
        event := (*HttpEvent)(unsafe.Pointer(&record.RawSample[0]))
        fmt.Printf("[%d] %s %s - %dms\n",
            event.Pid,
            event.Method,
            event.Path,
            event.DurationNs/1e6,
        )
    }
}

type HttpEvent struct {
    Timestamp  uint64
    Pid        uint32
    Method     [8]byte
    Path       [128]byte
    DurationNs uint64
}
```

#### 2.4 生成OTLP Span

```go
// 将eBPF事件转换为OTel Span
func (t *Tracer) createSpan(event *HttpEvent) {
    ctx := context.Background()

    method := string(bytes.Trim(event.Method[:], "\x00"))
    path := string(bytes.Trim(event.Path[:], "\x00"))

    _, span := t.tracer.Start(ctx, fmt.Sprintf("%s %s", method, path),
        trace.WithTimestamp(time.Unix(0, int64(event.Timestamp))),
        trace.WithAttributes(
            attribute.String("http.method", method),
            attribute.String("http.path", path),
            attribute.String("ebpf.source", "uprobe"),
        ),
    )

    duration := time.Duration(event.DurationNs)
    span.End(trace.WithTimestamp(
        time.Unix(0, int64(event.Timestamp)).Add(duration),
    ))
}
```

---

### 第三部分: 高级主题 (60分钟)

#### 3.1 Goroutine调度追踪

```c
// 追踪runtime.newproc和runtime.goexit

SEC("uprobe/runtime_newproc")
int trace_goroutine_create(struct pt_regs *ctx) {
    u64 pid_tgid = bpf_get_current_pid_tgid();
    u32 pid = pid_tgid >> 32;

    struct goroutine_event e = {};
    e.timestamp = bpf_ktime_get_ns();
    e.pid = pid;
    e.event_type = GOROUTINE_CREATE;

    bpf_ringbuf_submit(&e, 0);
    return 0;
}

SEC("uprobe/runtime_goexit1")
int trace_goroutine_exit(struct pt_regs *ctx) {
    // 类似实现...
    return 0;
}
```

#### 3.2 性能优化

| 优化点 | 方法 | 效果 |
|--------|------|------|
| 批量读取 | Ring buffer批量提交 | 减少syscall |
| 采样 | 只追踪1%请求 | 降低开销 |
| 过滤 | 内核态过滤 | 减少数据传输 |
| BTF | 使用BTF信息 | 更好的可移植性 |

#### 3.3 生产部署

```yaml
# kubernetes/daemonset.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: ebpf-tracer
spec:
  selector:
    matchLabels:
      app: ebpf-tracer
  template:
    spec:
      hostPID: true  # 访问主机进程
      containers:
      - name: tracer
        image: myregistry/ebpf-tracer:latest
        securityContext:
          privileged: true  # 加载eBPF需要特权
        volumeMounts:
        - name: debugfs
          mountPath: /sys/kernel/debug
        - name: bpffs
          mountPath: /sys/fs/bpf
      volumes:
      - name: debugfs
        hostPath:
          path: /sys/kernel/debug
      - name: bpffs
        hostPath:
          path: /sys/fs/bpf
```

---

### 第四部分: 实战演练 (15分钟)

#### 练习1: 编译运行

编译并运行HTTP追踪程序，观察输出。

#### 练习2: 修改追踪点

尝试追踪其他Go函数，如`database/sql`查询。

#### 练习3: 性能测试

对比eBPF追踪与手动插码的性能差异。

---

## 📝 关键要点总结

1. **eBPF真正零侵入** - 无需修改应用代码
2. **纳秒级开销** - 适合生产环境
3. **安全沙箱** - 内核验证器保证安全
4. **Go生态成熟** - cilium/ebpf库完善

---

## 📚 参考资料

- 本项目: `docs/research/ebpf/ebpf-uprobe-deep-dive.md`
- [cilium/ebpf文档](https://github.com/cilium/ebpf)
- [eBPF.io](https://ebpf.io/)

---

**培训材料版本**: v1.0
**更新日期**: 2026-04-06

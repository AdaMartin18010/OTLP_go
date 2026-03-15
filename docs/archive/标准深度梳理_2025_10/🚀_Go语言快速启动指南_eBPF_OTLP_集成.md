# 🚀 Go语言快速启动指南 - eBPF + OTLP 集成

**创建时间**: 2025年10月17日  
**适用项目**: Go语言OTLP项目 - P0-1任务  
**技术栈**: Go 1.25+ | cilium/ebpf | OpenTelemetry  
**目标**: 30分钟内搭建完整开发环境并运行第一个示例

---

## 🎯 前置条件

### 已有环境 ✅

```bash
# 确认Go版本
go version
# 输出: go version go1.25 windows/amd64

# 确认项目存在
cd E:\_src\OTLP_go
ls src/  # 查看现有Go代码
```

### 需要安装 ⚠️

- WSL2 (Windows Subsystem for Linux 2)
- Ubuntu 22.04 (在WSL2中)
- eBPF开发工具链

---

## 📦 第1步: 安装WSL2 (10分钟)

### 在Windows PowerShell (管理员模式)

```powershell
# 启用WSL2
wsl --install -d Ubuntu-22.04

# 等待安装完成,设置用户名和密码
# 例如: 用户名 developer, 密码 dev2025

# 验证安装
wsl --list --verbose
# 输出应显示: Ubuntu-22.04   Running   2
```

### 进入WSL2

```powershell
# 启动Ubuntu
wsl

# 或者
ubuntu2204.exe
```

---

## 🛠️ 第2步: 在WSL2中安装eBPF开发环境 (5分钟)

### 更新系统并安装依赖

```bash
# 更新包管理器
sudo apt-get update && sudo apt-get upgrade -y

# 安装必要工具
sudo apt-get install -y \
  clang \
  llvm \
  libbpf-dev \
  linux-headers-$(uname -r) \
  build-essential \
  git \
  curl

# 验证安装
clang --version       # 应显示 14.0+
llvm-config --version # 应显示 14.0+
```

### 安装Go (在WSL2中)

```bash
# 下载Go 1.25 (如果WSL2中没有)
cd /tmp
wget https://go.dev/dl/go1.25.linux-amd64.tar.gz
sudo tar -C /usr/local -xzf go1.25.linux-amd64.tar.gz

# 配置环境变量
echo 'export PATH=$PATH:/usr/local/go/bin' >> ~/.bashrc
echo 'export GOPATH=$HOME/go' >> ~/.bashrc
echo 'export PATH=$PATH:$GOPATH/bin' >> ~/.bashrc
source ~/.bashrc

# 验证Go安装
go version
# 输出: go version go1.25 linux/amd64
```

---

## 🔧 第3步: 安装cilium/ebpf Go库 (3分钟)

### 创建测试项目

```bash
# 创建项目目录
mkdir -p ~/go-ebpf-otlp-demo
cd ~/go-ebpf-otlp-demo

# 初始化Go模块
go mod init example.com/go-ebpf-otlp-demo

# 安装cilium/ebpf
go get github.com/cilium/ebpf@latest

# 安装bpf2go工具 (用于生成Go代码)
go install github.com/cilium/ebpf/cmd/bpf2go@latest

# 安装OpenTelemetry Go SDK
go get go.opentelemetry.io/otel@v1.32.0
go get go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc@v1.32.0
go get go.opentelemetry.io/otel/sdk@v1.32.0

# 验证依赖
go mod tidy
cat go.mod
```

---

## 💻 第4步: 创建第一个eBPF + Go示例 (10分钟)

### 创建eBPF C程序

```bash
# 创建eBPF程序目录
mkdir -p bpf

# 创建eBPF C代码文件
cat > bpf/hello.c << 'EOF'
// +build ignore

#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

char __license[] SEC("license") = "Dual MIT/GPL";

// 定义一个简单的Map来存储计数
struct {
    __uint(type, BPF_MAP_TYPE_ARRAY);
    __type(key, __u32);
    __type(value, __u64);
    __uint(max_entries, 1);
} event_count SEC(".maps");

// kprobe挂载到sys_execve系统调用
SEC("kprobe/sys_execve")
int kprobe_execve(struct pt_regs *ctx) {
    __u32 key = 0;
    __u64 *count;

    count = bpf_map_lookup_elem(&event_count, &key);
    if (count) {
        __sync_fetch_and_add(count, 1);
    }

    return 0;
}
EOF
```

### 创建Go主程序

```bash
# 生成Go绑定代码
go generate ./...

# 创建main.go
cat > main.go << 'EOF'
package main

import (
    "context"
    "fmt"
    "log"
    "time"

    "github.com/cilium/ebpf"
    "github.com/cilium/ebpf/link"
    "github.com/cilium/ebpf/rlimit"
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
    "go.opentelemetry.io/otel/sdk/resource"
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
)

//go:generate go run github.com/cilium/ebpf/cmd/bpf2go -cc clang bpf ./bpf/hello.c -- -I/usr/include/bpf

func main() {
    // 初始化OpenTelemetry
    ctx := context.Background()
    tp, err := initTracer(ctx)
    if err != nil {
        log.Fatalf("failed to initialize tracer: %v", err)
    }
    defer func() {
        if err := tp.Shutdown(ctx); err != nil {
            log.Fatalf("failed to shutdown tracer: %v", err)
        }
    }()

    tracer := otel.Tracer("ebpf-demo")

    // 创建Span追踪eBPF操作
    _, span := tracer.Start(ctx, "ebpf-program-lifecycle")
    defer span.End()

    // 移除内存锁限制 (eBPF需要)
    if err := rlimit.RemoveMemlock(); err != nil {
        log.Fatal(err)
    }

    // 加载eBPF程序
    objs := bpfObjects{}
    if err := loadBpfObjects(&objs, nil); err != nil {
        log.Fatalf("loading objects: %v", err)
    }
    defer objs.Close()

    // 将eBPF程序挂载到kprobe
    kp, err := link.Kprobe("sys_execve", objs.KprobeExecve, nil)
    if err != nil {
        log.Fatalf("opening kprobe: %v", err)
    }
    defer kp.Close()

    log.Println("eBPF程序已加载,开始追踪sys_execve调用...")
    log.Println("在另一个终端运行命令 (如: ls, ps等) 以触发事件")

    // 定期读取事件计数
    ticker := time.NewTicker(2 * time.Second)
    defer ticker.Stop()

    for range ticker.C {
        var count uint64
        key := uint32(0)

        if err := objs.EventCount.Lookup(&key, &count); err != nil {
            log.Printf("reading map: %v", err)
            continue
        }

        fmt.Printf("sys_execve调用次数: %d\n", count)
    }
}

func initTracer(ctx context.Context) (*sdktrace.TracerProvider, error) {
    // 创建OTLP导出器
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithInsecure(),
        otlptracegrpc.WithEndpoint("localhost:4317"),
    )
    if err != nil {
        return nil, err
    }

    // 创建资源
    res, err := resource.New(ctx,
        resource.WithAttributes(
            semconv.ServiceNameKey.String("go-ebpf-demo"),
            semconv.ServiceVersionKey.String("v0.1.0"),
        ),
    )
    if err != nil {
        return nil, err
    }

    // 创建TracerProvider
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithBatcher(exporter),
        sdktrace.WithResource(res),
    )

    otel.SetTracerProvider(tp)
    return tp, nil
}
EOF
```

---

## 🚀 第5步: 运行示例 (2分钟)

### 编译并运行

```bash
# 生成eBPF Go绑定
go generate ./...

# 编译程序
go build -o go-ebpf-demo

# 以root权限运行 (eBPF需要)
sudo ./go-ebpf-demo
```

### 预期输出

```text
2025/10/17 10:00:00 eBPF程序已加载,开始追踪sys_execve调用...
2025/10/17 10:00:00 在另一个终端运行命令 (如: ls, ps等) 以触发事件
sys_execve调用次数: 0
sys_execve调用次数: 3   # 在另一终端运行了ls命令
sys_execve调用次数: 5   # 又运行了ps命令
```

### 在另一个终端测试

```bash
# 打开新的WSL2终端
wsl

# 运行几个命令触发sys_execve
ls
ps aux
whoami
```

---

## 🎉 成功标志

### ✅ 检查清单

- [ ] WSL2安装成功,可以进入Ubuntu
- [ ] eBPF开发工具链安装完成 (clang, llvm)
- [ ] Go 1.25在WSL2中可用
- [ ] cilium/ebpf库安装成功
- [ ] 示例程序编译成功
- [ ] eBPF程序成功加载到内核
- [ ] 能看到sys_execve调用计数增加

### 📊 验证OpenTelemetry集成

如果你启动了OTLP Collector,可以看到追踪数据:

```bash
# 在Windows PowerShell中启动Collector
cd E:\_src\OTLP_go
.\run-collector.ps1

# 你应该能在Collector日志中看到:
# Span: ebpf-program-lifecycle
# Service: go-ebpf-demo
```

---

## 🔧 故障排查

### 问题1: WSL2安装失败

```powershell
# 确保Windows版本支持WSL2 (Windows 10 1903+)
winver

# 手动启用WSL特性
dism.exe /online /enable-feature /featurename:Microsoft-Windows-Subsystem-Linux /all /norestart
dism.exe /online /enable-feature /featurename:VirtualMachinePlatform /all /norestart

# 重启后重试
wsl --install
```

### 问题2: eBPF程序加载失败

```bash
# 检查内核版本 (需要5.10+)
uname -r

# 如果内核版本过低,更新WSL2
wsl --update

# 检查eBPF支持
ls /sys/kernel/debug/tracing/
```

### 问题3: 权限错误

```bash
# 确保以root权限运行
sudo ./go-ebpf-demo

# 或者添加CAP_BPF能力
sudo setcap cap_bpf,cap_perfmon+ep ./go-ebpf-demo
./go-ebpf-demo
```

### 问题4: go generate失败

```bash
# 确保bpf2go已安装
which bpf2go
# 如果找不到,重新安装
go install github.com/cilium/ebpf/cmd/bpf2go@latest

# 确保在PATH中
export PATH=$PATH:$HOME/go/bin
```

---

## 📚 下一步

### 学习路径

1. ✅ **完成**: 基础eBPF程序运行
2. 🔜 **接下来**: 编写HTTP服务追踪eBPF程序
3. 🔜 **然后**: 集成OpenTelemetry完整链路追踪
4. 🔜 **最后**: 实现生产级eBPF监控系统

### 推荐资源

- [cilium/ebpf官方文档](https://github.com/cilium/ebpf)
- [eBPF.io学习资源](https://ebpf.io/)
- [OpenTelemetry Go SDK文档](https://opentelemetry.io/docs/languages/go/)

---

## 🎯 本项目目标回顾

**P0-1任务**: Go + eBPF深度集成指南  
**预计**: 3,000行文档 + 10个Go代码示例  
**完成日期**: 2025年11月10日

你已经完成了第一步! 🎉

---

**创建时间**: 2025年10月17日  
**适用于**: Windows + WSL2环境  
**Go版本**: 1.25+  
**eBPF库**: cilium/ebpf v0.12+  
**OpenTelemetry**: v1.32.0+

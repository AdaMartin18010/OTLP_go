# eBPF环境搭建指南

> **目标**: 配置完整的Go + eBPF开发环境
> **日期**: 2026-04-06
> **预计耗时**: 2-4小时

---

## 1. 环境要求

### 1.1 系统要求

| 组件 | 最低要求 | 推荐配置 |
|------|----------|----------|
| **操作系统** | Linux 5.4+ | Linux 6.x |
| **内核版本** | 5.4 (基础eBPF) | 5.13+ (Ring Buffer) |
| **Go版本** | 1.21+ | 1.26.1 |
| **内存** | 4GB | 8GB+ |
| **磁盘** | 10GB | 20GB+ |

### 1.2 验证内核支持

```bash
# 查看内核版本
uname -r
# 期望输出: 6.x.x 或 5.13+

# 验证BTF支持 (必须)
ls /sys/kernel/btf/
# 期望输出: vmlinux

# 验证eBPF支持
cat /boot/config-$(uname -r) | grep CONFIG_BPF
# 期望看到: CONFIG_BPF=y, CONFIG_BPF_SYSCALL=y

# 验证BPF Type Format (CO-RE必需)
cat /boot/config-$(uname -r) | grep CONFIG_DEBUG_INFO_BTF
# 期望看到: CONFIG_DEBUG_INFO_BTF=y
```

### 1.3 内核能力检查脚本

```bash
#!/bin/bash
# check-ebpf-capabilities.sh

echo "=== eBPF Capability Check ==="

# 检查内核版本
KERNEL_MAJOR=$(uname -r | cut -d. -f1)
KERNEL_MINOR=$(uname -r | cut -d. -f2)

if [ "$KERNEL_MAJOR" -ge 6 ] || ([ "$KERNEL_MAJOR" -eq 5 ] && [ "$KERNEL_MINOR" -ge 4 ]); then
    echo "✅ Kernel version: $(uname -r)"
else
    echo "❌ Kernel too old: $(uname -r), need 5.4+"
    exit 1
fi

# 检查BTF
if [ -f /sys/kernel/btf/vmlinux ]; then
    echo "✅ BTF support: YES"
else
    echo "⚠️  BTF support: NO (CO-RE may not work)"
fi

# 检查BPF系统调用
if grep -q "CONFIG_BPF_SYSCALL=y" /boot/config-$(uname -r) 2>/dev/null; then
    echo "✅ BPF syscall: YES"
else
    echo "❌ BPF syscall: NO"
    exit 1
fi

echo "=== All checks passed ==="
```

---

## 2. 工具链安装

### 2.1 系统依赖 (Ubuntu/Debian)

```bash
sudo apt-get update

# 基础编译工具
sudo apt-get install -y \
    build-essential \
    clang \
    llvm \
    libelf-dev \
    libbpf-dev \
    linux-headers-$(uname -r) \
    linux-tools-$(uname -r) \
    linux-tools-generic \
    pkg-config

# bpftool (eBPF工具集)
sudo apt-get install -y linux-tools-common linux-tools-generic
# 或从源码编译最新版
git clone --recurse-submodules https://github.com/libbpf/bpftool.git
cd bpftool/src
make
sudo make install
```

### 2.2 系统依赖 (CentOS/RHEL/Fedora)

```bash
# Fedora
sudo dnf install -y \
    clang \
    llvm \
    elfutils-libelf-devel \
    libbpf-devel \
    kernel-headers \
    bpftool \
    make

# CentOS/RHEL 8+
sudo yum install -y \
    clang \
    llvm \
    elfutils-libelf-devel \
    kernel-headers \
    make

# 从源码安装libbpf (如果yum版本太老)
git clone https://github.com/libbpf/libbpf.git
cd libbpf/src
make
sudo make install
```

### 2.3 验证工具安装

```bash
# 验证clang
clang --version
# 期望: 12.0+

# 验证llvm
llc --version
# 期望: 12.0+

# 验证bpftool
bpftool version
# 期望: 5.x+

# 验证libbpf
pkg-config --modversion libbpf
# 期望: 0.8+
```

---

## 3. Go eBPF库安装

### 3.1 安装cilium/ebpf

```bash
# 在项目目录
cd OTLP_go

go get github.com/cilium/ebpf
go get github.com/cilium/ebpf/link

# 安装bpf2go工具 (代码生成)
go install github.com/cilium/ebpf/cmd/bpf2go@latest

# 验证安装
bpf2go --version
```

### 3.2 go.mod 依赖

```go
require (
    github.com/cilium/ebpf v0.12.3
)
```

### 3.3 验证Go eBPF环境

```bash
# 创建测试程序
cat > /tmp/test_bpf.go << 'EOF'
package main

import (
    "fmt"
    "github.com/cilium/ebpf"
)

func main() {
    // 尝试加载一个最小的BPF程序
    prog := &ebpf.ProgramSpec{
        Type: ebpf.Kprobe,
        Instructions: []ebpf.Instruction{
            // mov r0, 0
            ebpf.Mov64(ebpf.Reg0, 0),
            // exit
            ebpf.Return(),
        },
    }

    p, err := ebpf.NewProgram(prog)
    if err != nil {
        fmt.Printf("Error: %v\n", err)
        return
    }
    defer p.Close()

    fmt.Println("✅ eBPF environment is ready!")
}
EOF

cd /tmp && go run test_bpf.go
# 期望输出: ✅ eBPF environment is ready!
```

---

## 4. 开发环境配置

### 4.1 VSCode配置

```json
// .vscode/settings.json
{
    "go.toolsManagement.autoUpdate": true,
    "go.useLanguageServer": true,
    "go.lintTool": "golangci-lint",
    "go.formatTool": "gofumpt",
    "go.diagnostic.vulncheck": "latest",
    "files.associations": {
        "*.bpf.c": "c"
    }
}
```

### 4.2 CGO环境变量

```bash
# 添加到 ~/.bashrc 或 ~/.zshrc
export CGO_ENABLED=1
export CGO_CFLAGS="-I/usr/include/bpf"
export CGO_LDFLAGS="-lelf -lz"

# 如果使用自定义libbpf路径
export LIBBPF_DIR=/usr/local/lib
export LD_LIBRARY_PATH=$LIBBPF_DIR:$LD_LIBRARY_PATH
```

### 4.3 权限配置

```bash
# 方式1: 使用sudo运行 (开发测试)
sudo go run main.go

# 方式2: 设置 capabilities (推荐)
sudo setcap cap_bpf,cap_perfmon,cap_net_admin,cap_sys_admin+eip ./your-program

# 方式3: 添加到bpf用户组
sudo groupadd bpf
sudo usermod -aG bpf $USER
# 重新登录生效
```

---

## 5. 项目eBPF目录结构

```
pkg/ebpf/
├── Makefile              # BPF编译规则
├── common/
│   └── common.h          # 共享头文件
├── headers/
│   └── vmlinux.h         # 内核类型定义 (自动生成)
├── uprobe/
│   ├── uprobe_trace.bpf.c    # uprobe BPF程序
│   └── uprobe_trace.go       # Go加载器
├── kprobe/
│   ├── kprobe_trace.bpf.c    # kprobe BPF程序
│   └── kprobe_trace.go       # Go加载器
└── tracepoint/
    ├── sched.bpf.c           # 调度事件追踪
    └── sched.go
```

### 5.1 Makefile模板

```makefile
# pkg/ebpf/Makefile

CLANG ?= clang
CFLAGS := -O2 -g -Wall -Werror \
    -target bpf \
    -D__TARGET_ARCH_x86 \
    -I./headers

BPF_SRCS := $(wildcard */*.bpf.c)
BPF_OBJS := $(BPF_SRCS:.bpf.c=.bpf.o)

all: $(BPF_OBJS) headers/vmlinux.h

headers/vmlinux.h:
 bpftool btf dump file /sys/kernel/btf/vmlinux format c > $@

%.bpf.o: %.bpf.c
 $(CLANG) $(CFLAGS) -c $< -o $@

clean:
 rm -f $(BPF_OBJS) headers/vmlinux.h

.PHONY: all clean
```

---

## 6. 快速验证

### 6.1 最小可运行示例

```go
// examples/ebpf-hello/main.go
package main

import (
    "fmt"
    "log"
    "time"

    "github.com/cilium/ebpf"
    "github.com/cilium/ebpf/link"
    "github.com/cilium/ebpf/rlimit"
)

//go:generate bpf2go -cc clang -cflags "-O2 -g -Wall -Werror -target bpf" hello ./hello.bpf.c -- -I../../pkg/ebpf/headers

func main() {
    // 解除资源限制
    if err := rlimit.RemoveMemlock(); err != nil {
        log.Fatal(err)
    }

    // 加载BPF程序
    objs := helloObjects{}
    if err := loadHelloObjects(&objs, nil); err != nil {
        log.Fatalf("loading objects: %v", err)
    }
    defer objs.Close()

    // 附加到kprobe
    kp, err := link.Kprobe("sys_execve", objs.Hello, nil)
    if err != nil {
        log.Fatalf("opening kprobe: %v", err)
    }
    defer kp.Close()

    fmt.Println("Tracing sys_execve... Press Ctrl+C to exit")

    // 读取计数器
    ticker := time.NewTicker(time.Second)
    defer ticker.Stop()

    for range ticker.C {
        var count uint64
        if err := objs.ExecveCounter.Get(&count); err != nil {
            log.Printf("reading counter: %v", err)
            continue
        }
        fmt.Printf("sys_execve called %d times\n", count)
    }
}
```

```c
// examples/ebpf-hello/hello.bpf.c
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>

struct {
    __uint(type, BPF_MAP_TYPE_ARRAY);
    __uint(max_entries, 1);
    __type(key, __u32);
    __type(value, __u64);
} execve_counter SEC(".maps");

SEC("kprobe/sys_execve")
int hello(struct pt_regs *ctx) {
    __u32 key = 0;
    __u64 *count = bpf_map_lookup_elem(&execve_counter, &key);
    if (count) {
        __sync_fetch_and_add(count, 1);
    }
    return 0;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL";
```

### 6.2 运行测试

```bash
cd examples/ebpf-hello

# 生成Go绑定
go generate

# 运行 (需要root或cap_bpf)
sudo go run main.go

# 期望输出:
# Tracing sys_execve... Press Ctrl+C to exit
# sys_execve called 0 times
# sys_execve called 3 times
# ...
```

---

## 7. 常见问题

### Q1: bpftool报错 "BTF is required"

```bash
# 解决: 生成vmlinux.h
bpftool btf dump file /sys/kernel/btf/vmlinux format c > headers/vmlinux.h
```

### Q2: "permission denied" 错误

```bash
# 解决: 使用sudo或设置capabilities
sudo go run main.go
# 或
sudo setcap cap_bpf,cap_perfmon,cap_net_admin,cap_sys_admin+eip ./main
```

### Q3: CGO编译错误

```bash
# 确保安装了libbpf-dev
sudo apt-get install libbpf-dev

# 设置CGO环境
export CGO_ENABLED=1
export CGO_CFLAGS="-I/usr/include/bpf"
```

### Q4: "field has incomplete type" 错误

```bash
# vmlinux.h不完整，重新生成
rm headers/vmlinux.h
make headers/vmlinux.h
```

---

## 8. 下一步

环境就绪后，开始 [ebpf-uprobe-deep-dive.md](./ebpf-uprobe-deep-dive.md) 研究。

---

**文档状态**: ✅ 完成
**更新日期**: 2026-04-06

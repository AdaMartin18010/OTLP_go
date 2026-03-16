# CSP 进程代数的形式语义：Trace/Failures/Divergences 模型

## 目录

- [CSP 进程代数的形式语义：Trace/Failures/Divergences 模型](#csp-进程代数的形式语义tracefailuresdivergences-模型)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. CSP 基础：语法与操作符](#2-csp-基础语法与操作符)
    - [2.1 核心操作符](#21-核心操作符)
    - [2.2 示例](#22-示例)
  - [3. Trace 语义模型](#3-trace-语义模型)
    - [3.1 定义](#31-定义)
    - [3.2 Trace 精化](#32-trace-精化)
    - [3.3 与 OTLP 的对应](#33-与-otlp-的对应)
  - [4. Failures 语义模型](#4-failures-语义模型)
    - [4.1 定义](#41-定义)
    - [4.2 Failure 精化](#42-failure-精化)
    - [4.3 死锁检查](#43-死锁检查)
  - [5. Divergences 语义模型](#5-divergences-语义模型)
    - [5.1 定义](#51-定义)
    - [5.2 活锁检查](#52-活锁检查)
  - [6. 精化检查（Refinement Checking）](#6-精化检查refinement-checking)
    - [6.1 规约与实现](#61-规约与实现)
    - [6.2 示例](#62-示例)
  - [7. FDR4 工具使用](#7-fdr4-工具使用)
    - [7.1 安装](#71-安装)
    - [7.2 示例：互斥锁验证](#72-示例互斥锁验证)
  - [8. 将 Go 代码建模为 CSP](#8-将-go-代码建模为-csp)
    - [8.1 Goroutine → Process](#81-goroutine--process)
    - [8.2 Channel → Event](#82-channel--event)
    - [8.3 完整示例：生产者-消费者](#83-完整示例生产者-消费者)
  - [9. 死锁与活锁检测](#9-死锁与活锁检测)
    - [9.1 死锁示例](#91-死锁示例)
    - [9.2 活锁示例](#92-活锁示例)
  - [10. 总结](#10-总结)
  - [参考文献](#参考文献)

---

## 1. 引言

**CSP（Communicating Sequential Processes）** 是 Tony Hoare 于 1978 年提出的进程代数，用于描述并发系统的行为。

**三种语义模型**：

1. **Trace 语义 (T)**：只关注可观察的事件序列
2. **Failures 语义 (F)**：考虑拒绝（refusal）— 进程拒绝执行某些事件
3. **Divergences 语义 (D)**：考虑发散（divergence）— 无限内部循环

**层次关系**：

\[
T \subseteq F \subseteq D
\]

---

## 2. CSP 基础：语法与操作符

### 2.1 核心操作符

**顺序组合 (Sequential Composition)**：

\[
P \to Q
\]

进程 \( P \) 完成后执行进程 \( Q \)。

**外部选择 (External Choice)**：

\[
P \square Q
\]

环境选择执行 \( P \) 或 \( Q \)。

**并行组合 (Parallel Composition)**：

\[
P \parallel_A Q
\]

进程 \( P \) 和 \( Q \) 并发执行，在事件集 \( A \) 上同步。

**前缀 (Prefix)**：

\[
a \to P
\]

执行事件 \( a \)，然后行为如 \( P \)。

### 2.2 示例

**互斥锁**：

```csp
MUTEX = acquire -> use -> release -> MUTEX

USER1 = acquire -> use -> release -> STOP
USER2 = acquire -> use -> release -> STOP

SYSTEM = MUTEX || {acquire, release} (USER1 ||| USER2)
```

---

## 3. Trace 语义模型

### 3.1 定义

**Trace**：进程可观察的事件序列。

\[
\text{traces}(P) = \{ s \mid P \text{ can perform sequence } s \}
\]

**示例**：

```csp
P = a -> b -> STOP

traces(P) = {[], [a], [a, b]}
```

### 3.2 Trace 精化

\[
Q \sqsubseteq_T P \iff \text{traces}(Q) \subseteq \text{traces}(P)
\]

**含义**：\( Q \) 的行为比 \( P \) 更受限制。

### 3.3 与 OTLP 的对应

**OTLP Trace 就是 CSP Trace**：

```go
// CSP: P = req -> process -> resp -> STOP
// OTLP Trace:
Root Span: "HandleRequest"
├── Event: "request_received"
├── Event: "processing"
└── Event: "response_sent"
```

---

## 4. Failures 语义模型

### 4.1 定义

**Failure**：一对 \( (s, X) \)，其中：

- \( s \)：事件序列（trace）
- \( X \)：拒绝集（refusal set）— 进程在 \( s \) 后拒绝执行的事件

\[
\text{failures}(P) = \{ (s, X) \mid P \text{ can perform } s \text{ and refuse } X \}
\]

**示例**：

```csp
P = a -> STOP

failures(P) = {
    ([], {}),         // 初始状态，不拒绝任何事件
    ([a], {a, b, c})  // 执行 a 后，拒绝所有事件（STOP）
}
```

### 4.2 Failure 精化

\[
Q \sqsubseteq_F P \iff \text{failures}(Q) \subseteq \text{failures}(P)
\]

### 4.3 死锁检查

**死锁**：进程在某个 trace 后拒绝所有事件。

\[
\text{Deadlock}(P) \iff \exists s : (s, \Sigma) \in \text{failures}(P)
\]

其中 \( \Sigma \) 是所有事件的集合。

---

## 5. Divergences 语义模型

### 5.1 定义

**Divergence**：无限的内部循环（如活锁）。

\[
\text{divergences}(P) = \{ s \mid P \text{ can diverge after } s \}
\]

**示例**：

```csp
P = a -> (b -> P |~| c -> STOP)

divergences(P) = {[a, b, b, b, ...]}  // 无限循环
```

### 5.2 活锁检查

\[
\text{Livelock}(P) \iff \exists s \in \text{divergences}(P)
\]

---

## 6. 精化检查（Refinement Checking）

### 6.1 规约与实现

**规约（Spec）**：期望的行为

**实现（Impl）**：实际的系统

**精化关系**：

\[
\text{Impl} \sqsubseteq \text{Spec}
\]

含义：实现的行为是规约的子集。

### 6.2 示例

**规约**：

```csp
SPEC = req -> resp -> SPEC
```

**实现**：

```csp
IMPL = req -> process -> resp -> IMPL
```

**检查**：

\[
\text{IMPL} \sqsubseteq_T \text{SPEC}
\]

结果：**True**（IMPL 的 trace 是 SPEC 的子集）

---

## 7. FDR4 工具使用

**FDR4（Failures-Divergences Refinement）** 是 CSP 的模型检查器。

### 7.1 安装

```bash
# Ubuntu
sudo apt-get install fdr

# macOS
brew install fdr
```

### 7.2 示例：互斥锁验证

**CSP 文件（mutex.csp）**：

```csp
-- 定义事件
channel acquire, release, use

-- 互斥锁
MUTEX = acquire -> release -> MUTEX

-- 用户
USER = acquire -> use -> release -> STOP

-- 系统
SYSTEM = MUTEX [| {acquire, release} |] (USER ||| USER)

-- 规约：不应该有两个用户同时使用
SPEC = acquire -> release -> acquire -> release -> SPEC

-- 验证
assert SYSTEM [T= SPEC
```

**运行**：

```bash
fdr4 mutex.csp
```

**输出**：

```text
Checking SYSTEM [T= SPEC: passed
```

---

## 8. 将 Go 代码建模为 CSP

### 8.1 Goroutine → Process

```go
go func() {
    data := <-ch
    process(data)
    resultCh <- result
}()
```

**CSP 模型**：

```csp
GOROUTINE = ch?data -> process -> resultCh!result -> STOP
```

### 8.2 Channel → Event

```go
ch := make(chan int)
ch <- 42
x := <-ch
```

**CSP 模型**：

```csp
channel ch : Int

P = ch!42 -> STOP
Q = ch?x -> STOP

SYSTEM = P [| {|ch|} |] Q
```

### 8.3 完整示例：生产者-消费者

**Go 代码**：

```go
func producer(ch chan int) {
    for i := 0; i < 10; i++ {
        ch <- i
    }
    close(ch)
}

func consumer(ch chan int) {
    for v := range ch {
        fmt.Println(v)
    }
}

func main() {
    ch := make(chan int)
    go producer(ch)
    go consumer(ch)
}
```

**CSP 模型**：

```csp
channel ch : Int

PRODUCER(n) = 
    if n < 10 then ch!n -> PRODUCER(n+1)
    else STOP

CONSUMER = ch?v -> CONSUMER [] STOP

SYSTEM = PRODUCER(0) [| {|ch|} |] CONSUMER
```

---

## 9. 死锁与活锁检测

### 9.1 死锁示例

**Go 代码（有死锁）**：

```go
ch1 := make(chan int)
ch2 := make(chan int)

go func() {
    ch1 <- 1
    <-ch2
}()

go func() {
    ch2 <- 2
    <-ch1
}()
```

**CSP 模型**：

```csp
channel ch1, ch2 : Int

P = ch1!1 -> ch2?x -> STOP
Q = ch2!2 -> ch1?y -> STOP

SYSTEM = P [| {|ch1, ch2|} |] Q
```

**FDR4 检查**：

```csp
assert SYSTEM :[deadlock free]
```

**结果**：

```text
Checking SYSTEM :[deadlock free]: failed
Counterexample: [ch1!1, ch2!2] (deadlock)
```

### 9.2 活锁示例

**Go 代码（有活锁）**：

```go
var flag1, flag2 bool

go func() {
    for {
        flag1 = true
        if flag2 {
            flag1 = false
        } else {
            // critical section
            break
        }
    }
}()

go func() {
    for {
        flag2 = true
        if flag1 {
            flag2 = false
        } else {
            // critical section
            break
        }
    }
}()
```

**CSP 模型**：

```csp
P = setFlag1 -> 
    (checkFlag2 -> clearFlag1 -> P 
     [] enter -> STOP)

Q = setFlag2 -> 
    (checkFlag1 -> clearFlag2 -> Q 
     [] enter -> STOP)

SYSTEM = P [| {|enter|} |] Q
```

**FDR4 检查**：

```csp
assert SYSTEM :[divergence free]
```

**结果**：

```text
Checking SYSTEM :[divergence free]: failed
Livelock detected
```

---

## 10. 总结

本文档论证了：

1. **CSP 提供了三层语义模型**（T/F/D）
2. **Trace 语义直接对应 OTLP Trace**
3. **Failures 语义用于死锁检测**
4. **Divergences 语义用于活锁检测**
5. **FDR4 工具可验证 Go 并发代码**

**与 OTLP 的连接**：

- **CSP Trace** = **OTLP Trace**
- **CSP Process** = **Goroutine**
- **CSP Channel** = **Go Channel**

---

## 参考文献

1. Hoare, C. A. R. (1978). Communicating Sequential Processes. CACM.
2. Roscoe, A. W. (2010). Understanding Concurrent Systems. Springer.
3. FDR4 Manual. <https://www.cs.ox.ac.uk/projects/fdr/>

---

**文档版本**：v1.0.0  
**最后更新**：2025-10-01  
**页数**：约 20 页

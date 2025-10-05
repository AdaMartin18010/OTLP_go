# CSP 形式化模型

## 目录

- [CSP 形式化模型](#csp-形式化模型)
  - [目录](#目录)
  - [1. CSP 进程代数](#1-csp-进程代数)
    - [1.1 基本进程定义](#11-基本进程定义)
    - [1.2 OTLP 进程建模](#12-otlp-进程建模)
    - [1.3 Channel 通信建模](#13-channel-通信建模)
  - [2. 并发组合与同步](#2-并发组合与同步)
    - [2.1 同步语义](#21-同步语义)
    - [2.2 OTLP Context 传播](#22-otlp-context-传播)
    - [2.3 Trace 完整性](#23-trace-完整性)
  - [3. 死锁检测](#3-死锁检测)
    - [3.1 死锁定义](#31-死锁定义)
    - [3.2 死锁示例](#32-死锁示例)
    - [3.3 OTLP Pipeline 死锁分析](#33-otlp-pipeline-死锁分析)
    - [3.4 死锁检测算法](#34-死锁检测算法)
  - [4. 活性与安全性](#4-活性与安全性)
    - [4.1 安全性属性](#41-安全性属性)
    - [4.2 活性属性](#42-活性属性)
    - [4.3 公平性](#43-公平性)
  - [5. TLA+ 规范](#5-tla-规范)
    - [5.1 OTLP Pipeline TLA+ 模型](#51-otlp-pipeline-tla-模型)
    - [5.2 Context 传播 TLA+ 模型](#52-context-传播-tla-模型)
  - [6. FDR 模型检查](#6-fdr-模型检查)
    - [6.1 FDR 检查示例](#61-fdr-检查示例)
    - [6.2 自动化验证](#62-自动化验证)
  - [7. 参考资料](#7-参考资料)

## 1. CSP 进程代数

### 1.1 基本进程定义

**原子进程**：

```csp
SKIP = √           -- 成功终止
STOP = ⊥           -- 死锁
DIV = μX.X         -- 发散（无限循环）
```

**前缀进程**：

```csp
P = a -> Q         -- 执行事件 a 后变为 Q
```

**选择组合**：

```csp
-- 外部选择（环境决定）
P □ Q = (a -> P') □ (b -> Q')

-- 内部选择（进程决定）
P ⊓ Q = (a -> P') ⊓ (a -> Q')
```

**顺序组合**：

```csp
P ; Q = P 成功终止后执行 Q
```

**并行组合**：

```csp
-- 交织并行（独立执行）
P ||| Q

-- 同步并行（在共享事件上同步）
P || Q = P [A || B] Q  -- A, B 是同步事件集

-- 完全同步
P || Q = P [Σ || Σ] Q  -- 所有事件都同步
```

### 1.2 OTLP 进程建模

**Span 创建进程**：

```csp
SPAN(id) = start.id -> 
           (event.id -> SPAN(id) 
            □ 
            end.id -> SKIP)

-- 多个 Span
TRACE = SPAN(1) ||| SPAN(2) ||| SPAN(3)
```

**父子 Span 关系**：

```csp
PARENT(pid) = start.pid -> 
              CHILD(pid, cid) ; 
              end.pid -> SKIP

CHILD(pid, cid) = start.cid -> 
                  end.cid -> 
                  SKIP

-- 组合（顺序执行）
HIERARCHY = PARENT(1) ; CHILD(1, 2)
```

**Pipeline 进程**：

```csp
STAGE1 = input?x -> process1.x -> output1!f(x) -> STAGE1
STAGE2 = input1?y -> process2.y -> output2!g(y) -> STAGE2
STAGE3 = input2?z -> process3.z -> output3!h(z) -> STAGE3

PIPELINE = STAGE1 [output1/input1] STAGE2 [output2/input2] STAGE3
```

### 1.3 Channel 通信建模

**无缓冲 Channel**：

```csp
CHANNEL = send?x -> receive!x -> CHANNEL

SENDER = send!msg -> SENDER
RECEIVER = receive?x -> process.x -> RECEIVER

SYSTEM = SENDER [send, receive] CHANNEL [send, receive] RECEIVER
```

**有缓冲 Channel**：

```csp
BUFFER(0) = send?x -> BUFFER([x])
BUFFER(xs) = 
    (|xs| < MAX) & send?x -> BUFFER(xs ++ [x])
    □
    (|xs| > 0) & receive!head(xs) -> BUFFER(tail(xs))

BUFFERED_CHANNEL(n) = BUFFER([])
```

## 2. 并发组合与同步

### 2.1 同步语义

**事件同步**：

```csp
-- P 和 Q 必须在事件 a 上同步
P [a] Q

-- 例子：生产者-消费者
PRODUCER = produce!item -> PRODUCER
CONSUMER = consume?item -> CONSUMER
BUFFER = produce?x -> consume!x -> BUFFER

SYSTEM = PRODUCER [produce] BUFFER [consume] CONSUMER
```

**接口并行**：

```csp
-- P 和 Q 在接口 A 上同步
P [A || B] Q

-- 例子：微服务通信
SERVICE_A = request!msg -> response?reply -> SERVICE_A
SERVICE_B = request?msg -> response!reply -> SERVICE_B

MICROSERVICES = SERVICE_A [{request, response}] SERVICE_B
```

### 2.2 OTLP Context 传播

```csp
-- Context 传播进程
CONTEXT(ctx) = 
    send.ctx -> CONTEXT(ctx)
    □
    receive?newCtx -> CONTEXT(newCtx)

-- 服务调用链
CLIENT = call.ctx1 -> CONTEXT(ctx1)
SERVER1 = receive.ctx1 -> call.ctx2 -> CONTEXT(ctx2)
SERVER2 = receive.ctx2 -> process.ctx2 -> SKIP

CALL_CHAIN = CLIENT [call.ctx1] SERVER1 [call.ctx2] SERVER2
```

### 2.3 Trace 完整性

```csp
-- Trace 必须有明确的开始和结束
VALID_TRACE = start.tid -> 
              (event.tid -> VALID_TRACE 
               □ 
               end.tid -> SKIP)

-- 不合法的 Trace（缺少 end）
INVALID_TRACE = start.tid -> event.tid -> STOP

-- 系统属性：所有 Trace 都是合法的
assert SYSTEM ⊑ VALID_TRACE
```

## 3. 死锁检测

### 3.1 死锁定义

**CSP 死锁**：

```csp
-- 进程 P 在某状态下无法执行任何事件
deadlock(P) ⇔ P ≡ STOP
```

**死锁自由**：

```csp
-- 进程 P 是死锁自由的
deadlock-free(P) ⇔ ∀s ∈ traces(P). P/s ≢ STOP
```

### 3.2 死锁示例

**循环等待（死锁）**：

```csp
P = a -> b -> SKIP
Q = b -> a -> SKIP

DEADLOCK_SYSTEM = P [a, b] Q  -- 死锁！P 等待 a，Q 等待 b
```

**正确的同步**：

```csp
P = a -> b -> SKIP
Q = a -> b -> SKIP

CORRECT_SYSTEM = P [a, b] Q  -- 无死锁，P 和 Q 同步执行
```

### 3.3 OTLP Pipeline 死锁分析

```csp
-- Pipeline 可能死锁的场景
STAGE1 = input?x -> output1!x -> STAGE1
STAGE2 = input1?y -> output2!y -> STAGE2

-- 如果 output1 和 input1 的缓冲满了，会死锁
DEADLOCK_PIPELINE = STAGE1 [output1/input1] STAGE2

-- 解决方案：添加缓冲或超时
BUFFERED_STAGE1 = input?x -> BUFFER!x -> STAGE1
BUFFER = ... -- 有界缓冲

SAFE_PIPELINE = BUFFERED_STAGE1 [buffer] STAGE2
```

### 3.4 死锁检测算法

```go
// 死锁检测（简化版）
type DeadlockDetector struct {
    waitGraph map[string][]string  // 等待图
    mu        sync.Mutex
}

func (dd *DeadlockDetector) AddWaitEdge(from, to string) {
    dd.mu.Lock()
    defer dd.mu.Unlock()
    
    dd.waitGraph[from] = append(dd.waitGraph[from], to)
    
    // 检测环
    if dd.hasCycle(from) {
        log.Fatal("Deadlock detected!")
    }
}

func (dd *DeadlockDetector) hasCycle(start string) bool {
    visited := make(map[string]bool)
    recStack := make(map[string]bool)
    
    return dd.dfs(start, visited, recStack)
}

func (dd *DeadlockDetector) dfs(node string, visited, recStack map[string]bool) bool {
    visited[node] = true
    recStack[node] = true
    
    for _, neighbor := range dd.waitGraph[node] {
        if !visited[neighbor] {
            if dd.dfs(neighbor, visited, recStack) {
                return true
            }
        } else if recStack[neighbor] {
            return true  // 找到环
        }
    }
    
    recStack[node] = false
    return false
}
```

## 4. 活性与安全性

### 4.1 安全性属性

**定义**：坏事永远不会发生

```csp
-- 安全性：进程 P 永远不会进入错误状态
safety(P) ⇔ ∀s ∈ traces(P). error ∉ s
```

**OTLP 安全性示例**：

```csp
-- Span 必须先 start 后 end
SAFE_SPAN = start -> (event -> SAFE_SPAN □ end -> SKIP)

-- 不安全的 Span（end 在 start 之前）
UNSAFE_SPAN = end -> start -> SKIP

-- 验证
assert SYSTEM ⊑ SAFE_SPAN
```

### 4.2 活性属性

**定义**：好事最终会发生

```csp
-- 活性：进程 P 最终会执行事件 a
liveness(P, a) ⇔ ∀s ∈ traces(P). ∃t. s ++ <a> ++ t ∈ traces(P)
```

**OTLP 活性示例**：

```csp
-- 所有 Span 最终都会结束
LIVENESS_SPAN = start -> (event -> LIVENESS_SPAN □ end -> SKIP)

-- 验证：从 start 状态最终能到达 end
assert start ∈ traces(LIVENESS_SPAN) ⇒ 
       ∃s. start ++ s ++ <end> ∈ traces(LIVENESS_SPAN)
```

### 4.3 公平性

```csp
-- 强公平性：如果事件 a 无限次可用，则必须无限次执行
strong_fairness(P, a) ⇔ 
    (∀i. ∃j > i. a enabled at j) ⇒ (∀i. ∃j > i. a occurs at j)

-- 弱公平性：如果事件 a 持续可用，则最终会执行
weak_fairness(P, a) ⇔ 
    (∃i. ∀j > i. a enabled at j) ⇒ (∃k. a occurs at k)
```

**OTLP 公平性**：

```go
// 确保所有 Span 都有机会被导出（公平调度）
type FairScheduler struct {
    queues map[string]*Queue
    mu     sync.Mutex
}

func (fs *FairScheduler) Schedule(ctx context.Context) {
    for {
        fs.mu.Lock()
        
        // 轮询所有队列（保证公平性）
        for service, queue := range fs.queues {
            if !queue.IsEmpty() {
                span := queue.Dequeue()
                go export(ctx, span)
            }
        }
        
        fs.mu.Unlock()
        
        time.Sleep(100 * time.Millisecond)
    }
}
```

## 5. TLA+ 规范

### 5.1 OTLP Pipeline TLA+ 模型

```tla
---- MODULE OTLPPipeline ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxQueueSize,
    MaxRetries,
    Spans

VARIABLES
    queue,          \* 队列状态
    exported,       \* 已导出的 Span
    retryCount,     \* 重试计数
    pipelineState   \* Pipeline 状态

TypeOK ==
    /\ queue \in Seq(Spans)
    /\ exported \subseteq Spans
    /\ retryCount \in [Spans -> 0..MaxRetries]
    /\ pipelineState \in {"RUNNING", "PAUSED", "STOPPED"}

Init ==
    /\ queue = <<>>
    /\ exported = {}
    /\ retryCount = [s \in Spans |-> 0]
    /\ pipelineState = "RUNNING"

Enqueue(span) ==
    /\ pipelineState = "RUNNING"
    /\ Len(queue) < MaxQueueSize
    /\ queue' = Append(queue, span)
    /\ UNCHANGED <<exported, retryCount, pipelineState>>

Dequeue ==
    /\ pipelineState = "RUNNING"
    /\ Len(queue) > 0
    /\ LET span == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ exported' = exported \union {span}
        /\ UNCHANGED <<retryCount, pipelineState>>

Retry(span) ==
    /\ span \in Spans
    /\ retryCount[span] < MaxRetries
    /\ retryCount' = [retryCount EXCEPT ![span] = @ + 1]
    /\ queue' = Append(queue, span)
    /\ UNCHANGED <<exported, pipelineState>>

Next ==
    \/ \E s \in Spans : Enqueue(s)
    \/ Dequeue
    \/ \E s \in Spans : Retry(s)

Spec == Init /\ [][Next]_<<queue, exported, retryCount, pipelineState>>

\* 安全性属性
NoDataLoss == \A s \in Spans : 
    (retryCount[s] = MaxRetries) => (s \in exported)

QueueBounded == Len(queue) <= MaxQueueSize

\* 活性属性
EventualExport == \A s \in Spans : 
    <>(s \in exported)

====
```

### 5.2 Context 传播 TLA+ 模型

```tla
---- MODULE ContextPropagation ----
EXTENDS Naturals, Sequences

CONSTANTS
    Services,
    TraceIDs

VARIABLES
    contexts,       \* 每个服务的 context
    callStack,      \* 调用栈
    activeTraces    \* 活跃的 trace

TypeOK ==
    /\ contexts \in [Services -> TraceIDs \union {NULL}]
    /\ callStack \in Seq(Services)
    /\ activeTraces \subseteq TraceIDs

Init ==
    /\ contexts = [s \in Services |-> NULL]
    /\ callStack = <<>>
    /\ activeTraces = {}

StartTrace(service, traceID) ==
    /\ contexts[service] = NULL
    /\ contexts' = [contexts EXCEPT ![service] = traceID]
    /\ activeTraces' = activeTraces \union {traceID}
    /\ UNCHANGED callStack

PropagateContext(from, to) ==
    /\ contexts[from] # NULL
    /\ contexts' = [contexts EXCEPT ![to] = contexts[from]]
    /\ callStack' = Append(callStack, to)
    /\ UNCHANGED activeTraces

EndTrace(service) ==
    /\ contexts[service] # NULL
    /\ contexts' = [contexts EXCEPT ![service] = NULL]
    /\ activeTraces' = activeTraces \ {contexts[service]}
    /\ UNCHANGED callStack

\* 不变式：Context 传播一致性
ContextConsistency ==
    \A s1, s2 \in Services :
        (contexts[s1] = contexts[s2] /\ contexts[s1] # NULL) =>
        (contexts[s1] \in activeTraces)

====
```

## 6. FDR 模型检查

### 6.1 FDR 检查示例

```csp
-- 定义进程
SENDER = send!1 -> SENDER
RECEIVER = receive?x -> RECEIVER
CHANNEL = send?x -> receive!x -> CHANNEL

SYSTEM = SENDER [send] CHANNEL [receive] RECEIVER

-- 检查死锁自由
assert SYSTEM :[deadlock free [F]]

-- 检查确定性
assert SYSTEM :[deterministic [F]]

-- 检查 refinement
SPEC = send -> receive -> SPEC
assert SPEC [T= SYSTEM

-- 检查 Trace 包含
assert SYSTEM :[has trace]: <send.1, receive.1>
```

### 6.2 自动化验证

```go
// 使用 FDR 进行自动化验证
func VerifyCSPModel(modelFile string) error {
    cmd := exec.Command("fdr4", "--batch", modelFile)
    output, err := cmd.CombinedOutput()
    
    if err != nil {
        return fmt.Errorf("verification failed: %v\n%s", err, output)
    }
    
    // 解析结果
    if strings.Contains(string(output), "PASSED") {
        log.Println("All assertions passed")
        return nil
    }
    
    return fmt.Errorf("verification failed:\n%s", output)
}
```

## 7. 参考资料

- **CSP Book**：Hoare, C.A.R. "Communicating Sequential Processes" (1985)
- **TLA+ Specification**：`docs/formal/tla/otlp-pipeline.tla`
- **FDR Tool**：<https://www.cs.ox.ac.uk/projects/fdr/>
- **Formal Proof**：`docs/design/formal-proof.md`
- **CSP-OTLP Mapping**：`01-csp-otlp-isomorphism.md`

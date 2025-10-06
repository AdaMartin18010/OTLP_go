# OTLP 系统的容错、排错、监测、控制与定位

## 目录

- [OTLP 系统的容错、排错、监测、控制与定位](#otlp-系统的容错排错监测控制与定位)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 容错机制 (Fault Tolerance)](#2-容错机制-fault-tolerance)
    - [2.1 故障分类与模型](#21-故障分类与模型)
    - [2.2 冗余设计](#22-冗余设计)
    - [2.3 故障隔离](#23-故障隔离)
    - [2.4 优雅降级](#24-优雅降级)
    - [2.5 故障恢复](#25-故障恢复)
  - [3. 排错机制 (Debugging)](#3-排错机制-debugging)
    - [3.1 分布式追踪排错](#31-分布式追踪排错)
    - [3.2 日志关联分析](#32-日志关联分析)
    - [3.3 指标异常检测](#33-指标异常检测)
    - [3.4 根因分析](#34-根因分析)
    - [3.5 时间旅行调试](#35-时间旅行调试)
  - [4. 监测机制 (Monitoring)](#4-监测机制-monitoring)
    - [4.1 四个黄金信号](#41-四个黄金信号)
    - [4.2 RED 方法](#42-red-方法)
    - [4.3 USE 方法](#43-use-方法)
    - [4.4 健康检查](#44-健康检查)
    - [4.5 SLI/SLO/SLA](#45-slislosla)
  - [5. 控制机制 (Control)](#5-控制机制-control)
    - [5.1 反馈控制](#51-反馈控制)
    - [5.2 自适应采样](#52-自适应采样)
    - [5.3 流量控制](#53-流量控制)
    - [5.4 配置管理](#54-配置管理)
    - [5.5 混沌工程](#55-混沌工程)
  - [6. 定位机制 (Localization)](#6-定位机制-localization)
    - [6.1 故障定位](#61-故障定位)
    - [6.2 性能瓶颈定位](#62-性能瓶颈定位)
    - [6.3 异常传播路径](#63-异常传播路径)
    - [6.4 依赖关系图](#64-依赖关系图)
    - [6.5 拓扑感知定位](#65-拓扑感知定位)
  - [7. 可观测性三支柱集成](#7-可观测性三支柱集成)
    - [7.1 Traces + Logs + Metrics](#71-traces--logs--metrics)
    - [7.2 关联查询](#72-关联查询)
    - [7.3 统一上下文](#73-统一上下文)
  - [8. 自动化运维](#8-自动化运维)
    - [8.1 自动告警](#81-自动告警)
    - [8.2 自动修复](#82-自动修复)
    - [8.3 预测性维护](#83-预测性维护)
  - [9. 案例研究](#9-案例研究)
    - [9.1 案例1: 级联故障定位](#91-案例1-级联故障定位)
    - [9.2 案例2: 内存泄漏排查](#92-案例2-内存泄漏排查)
    - [9.3 案例3: 网络分区恢复](#93-案例3-网络分区恢复)
  - [10. 参考文献](#10-参考文献)

## 1. 概述

OTLP 作为可观测性平台,其自身也需要强大的**容错、排错、监测、控制、定位**能力。本文档从运维视角,全面分析如何使用 OTLP 模型来实现这些能力。

**核心问题**:

1. 如何设计容错机制保证系统高可用?
2. 如何快速定位分布式系统中的故障?
3. 如何监测系统健康状态?
4. 如何实现自适应控制策略?
5. 如何精确定位性能瓶颈?

## 2. 容错机制 (Fault Tolerance)

### 2.1 故障分类与模型

**故障分类**:

| 故障类型 | 描述 | 检测方法 | 恢复策略 |
|---------|------|---------|---------|
| **瞬时故障** | 短暂的网络抖动 | 超时检测 | 重试 |
| **间歇性故障** | 周期性出现 | 统计分析 | 熔断 + 重试 |
| **永久性故障** | 节点崩溃 | 心跳检测 | 故障转移 |
| **拜占庭故障** | 恶意行为 | 签名验证 | 隔离 + 告警 |

**故障模型**:

```go
type FaultModel struct {
    Type        FaultType
    Probability float64
    MTBF        time.Duration  // Mean Time Between Failures
    MTTR        time.Duration  // Mean Time To Repair
}

type FaultType int

const (
    TransientFault FaultType = iota
    IntermittentFault
    PermanentFault
    ByzantineFault
)

// 计算系统可用性
func (fm *FaultModel) Availability() float64 {
    mtbf := fm.MTBF.Seconds()
    mttr := fm.MTTR.Seconds()
    return mtbf / (mtbf + mttr)
}

// 示例: MTBF=30天, MTTR=1小时
// Availability = (30*24) / (30*24 + 1) = 99.86%
```

### 2.2 冗余设计

**空间冗余 (Replication)**:

```yaml
# Collector 多副本部署
apiVersion: apps/v1
kind: Deployment
metadata:
  name: otel-collector
spec:
  replicas: 3  # 3 副本
  template:
    spec:
      affinity:
        podAntiAffinity:
          requiredDuringSchedulingIgnoredDuringExecution:
          - labelSelector:
              matchLabels:
                app: otel-collector
            topologyKey: kubernetes.io/hostname  # 不同节点
```

**时间冗余 (Retry)**:

```go
type RetryPolicy struct {
    MaxRetries      int
    InitialInterval time.Duration
    MaxInterval     time.Duration
    Multiplier      float64
}

func (rp *RetryPolicy) Execute(fn func() error) error {
    var lastErr error
    interval := rp.InitialInterval
    
    for attempt := 0; attempt <= rp.MaxRetries; attempt++ {
        if err := fn(); err == nil {
            return nil
        } else {
            lastErr = err
        }
        
        if attempt < rp.MaxRetries {
            time.Sleep(interval)
            interval = time.Duration(float64(interval) * rp.Multiplier)
            if interval > rp.MaxInterval {
                interval = rp.MaxInterval
            }
        }
    }
    
    return fmt.Errorf("max retries exceeded: %w", lastErr)
}
```

**信息冗余 (Checksum)**:

```go
type DataPacket struct {
    Data     []byte
    Checksum uint32
}

func (dp *DataPacket) Validate() bool {
    return crc32.ChecksumIEEE(dp.Data) == dp.Checksum
}

func (dp *DataPacket) Repair() error {
    // 使用 Reed-Solomon 纠错码
    return reedSolomon.Repair(dp.Data)
}
```

### 2.3 故障隔离

**舱壁模式 (Bulkhead Pattern)**:

```go
type Bulkhead struct {
    semaphore chan struct{}
    timeout   time.Duration
}

func NewBulkhead(maxConcurrent int, timeout time.Duration) *Bulkhead {
    return &Bulkhead{
        semaphore: make(chan struct{}, maxConcurrent),
        timeout:   timeout,
    }
}

func (b *Bulkhead) Execute(fn func() error) error {
    select {
    case b.semaphore <- struct{}{}:
        defer func() { <-b.semaphore }()
        return fn()
    case <-time.After(b.timeout):
        return errors.New("bulkhead timeout")
    }
}

// OTLP 使用舱壁隔离不同租户
func (c *Collector) ProcessTenant(tenantID string, data []byte) error {
    bulkhead := c.bulkheads[tenantID]
    return bulkhead.Execute(func() error {
        return c.process(data)
    })
}
```

**熔断器 (Circuit Breaker)**:

```go
type CircuitBreaker struct {
    state          atomic.Value  // "CLOSED", "OPEN", "HALF_OPEN"
    failureCount   atomic.Uint64
    successCount   atomic.Uint64
    threshold      uint64
    timeout        time.Duration
    lastFailTime   atomic.Value
}

func (cb *CircuitBreaker) Execute(fn func() error) error {
    state := cb.state.Load().(string)
    
    switch state {
    case "OPEN":
        // 检查是否可以进入半开状态
        lastFail := cb.lastFailTime.Load().(time.Time)
        if time.Since(lastFail) > cb.timeout {
            cb.state.Store("HALF_OPEN")
            return cb.tryExecute(fn)
        }
        return errors.New("circuit breaker open")
        
    case "HALF_OPEN":
        return cb.tryExecute(fn)
        
    case "CLOSED":
        if err := fn(); err != nil {
            cb.failureCount.Add(1)
            cb.lastFailTime.Store(time.Now())
            
            if cb.failureCount.Load() >= cb.threshold {
                cb.state.Store("OPEN")
            }
            return err
        }
        cb.failureCount.Store(0)
        return nil
    }
    
    return nil
}

func (cb *CircuitBreaker) tryExecute(fn func() error) error {
    if err := fn(); err != nil {
        cb.state.Store("OPEN")
        return err
    }
    
    cb.successCount.Add(1)
    if cb.successCount.Load() >= 3 {
        cb.state.Store("CLOSED")
        cb.successCount.Store(0)
        cb.failureCount.Store(0)
    }
    
    return nil
}
```

### 2.4 优雅降级

**降级策略**:

```go
type DegradationStrategy interface {
    ShouldDegrade(metrics SystemMetrics) bool
    Degrade() error
    Recover() error
}

// 采样率降级
type SamplingDegradation struct {
    normalRate    float64
    degradedRate  float64
    currentRate   atomic.Value
}

func (sd *SamplingDegradation) ShouldDegrade(metrics SystemMetrics) bool {
    return metrics.QueueUtilization > 0.8 || metrics.CPUUsage > 0.9
}

func (sd *SamplingDegradation) Degrade() error {
    sd.currentRate.Store(sd.degradedRate)
    log.Warnf("Degraded sampling rate to %.2f%%", sd.degradedRate*100)
    return nil
}

func (sd *SamplingDegradation) Recover() error {
    sd.currentRate.Store(sd.normalRate)
    log.Infof("Recovered sampling rate to %.2f%%", sd.normalRate*100)
    return nil
}

// 功能降级
type FeatureDegradation struct {
    features map[string]bool
}

func (fd *FeatureDegradation) Degrade() error {
    // 关闭非核心功能
    fd.features["tail_sampling"] = false
    fd.features["complex_transform"] = false
    log.Warn("Disabled non-critical features")
    return nil
}
```

### 2.5 故障恢复

**检查点 (Checkpoint) 恢复**:

```go
type CheckpointManager struct {
    interval    time.Duration
    storage     CheckpointStorage
    lastCheckpoint time.Time
}

type Checkpoint struct {
    Timestamp time.Time
    State     SystemState
    Metadata  map[string]string
}

func (cm *CheckpointManager) SaveCheckpoint(state SystemState) error {
    checkpoint := Checkpoint{
        Timestamp: time.Now(),
        State:     state,
        Metadata: map[string]string{
            "version": "1.0",
            "node_id": state.NodeID,
        },
    }
    
    if err := cm.storage.Save(checkpoint); err != nil {
        return fmt.Errorf("failed to save checkpoint: %w", err)
    }
    
    cm.lastCheckpoint = checkpoint.Timestamp
    return nil
}

func (cm *CheckpointManager) Recover() (SystemState, error) {
    checkpoint, err := cm.storage.LoadLatest()
    if err != nil {
        return SystemState{}, err
    }
    
    log.Infof("Recovering from checkpoint at %v", checkpoint.Timestamp)
    return checkpoint.State, nil
}
```

**Write-Ahead Log (WAL) 恢复**:

```go
type WALManager struct {
    file      *os.File
    seqNum    atomic.Uint64
    committed atomic.Uint64
}

type LogEntry struct {
    SeqNum    uint64
    Operation string
    Data      []byte
    Timestamp time.Time
}

func (wm *WALManager) Append(op string, data []byte) error {
    entry := LogEntry{
        SeqNum:    wm.seqNum.Add(1),
        Operation: op,
        Data:      data,
        Timestamp: time.Now(),
    }
    
    // 1. 写入 WAL
    if err := wm.writeLog(entry); err != nil {
        return err
    }
    
    // 2. 应用操作
    if err := wm.apply(entry); err != nil {
        return err
    }
    
    // 3. 标记已提交
    wm.committed.Store(entry.SeqNum)
    return nil
}

func (wm *WALManager) Replay() error {
    entries, err := wm.readAllLogs()
    if err != nil {
        return err
    }
    
    lastCommitted := wm.committed.Load()
    
    for _, entry := range entries {
        if entry.SeqNum > lastCommitted {
            if err := wm.apply(entry); err != nil {
                return err
            }
            wm.committed.Store(entry.SeqNum)
        }
    }
    
    return nil
}
```

## 3. 排错机制 (Debugging)

### 3.1 分布式追踪排错

**Trace 异常检测**:

```go
type TraceAnalyzer struct {
    errorPatterns []ErrorPattern
}

type ErrorPattern struct {
    Name      string
    Condition func(Trace) bool
    Severity  string
}

func (ta *TraceAnalyzer) Analyze(trace Trace) []Issue {
    var issues []Issue
    
    // 检测错误模式
    for _, pattern := range ta.errorPatterns {
        if pattern.Condition(trace) {
            issues = append(issues, Issue{
                TraceID:  trace.TraceID,
                Pattern:  pattern.Name,
                Severity: pattern.Severity,
            })
        }
    }
    
    return issues
}

// 错误模式示例
var ErrorPatterns = []ErrorPattern{
    {
        Name: "High Latency",
        Condition: func(t Trace) bool {
            return t.Duration() > 3*time.Second
        },
        Severity: "WARNING",
    },
    {
        Name: "Error Status",
        Condition: func(t Trace) bool {
            for _, span := range t.Spans {
                if span.Status == "ERROR" {
                    return true
                }
            }
            return false
        },
        Severity: "ERROR",
    },
    {
        Name: "Missing Span",
        Condition: func(t Trace) bool {
            // 检测是否有孤儿 Span
            for _, span := range t.Spans {
                if span.ParentSpanID != "" {
                    if !t.HasSpan(span.ParentSpanID) {
                        return true
                    }
                }
            }
            return false
        },
        Severity: "CRITICAL",
    },
}
```

**关键路径分析**:

```go
func (t *Trace) CriticalPath() []Span {
    // 构建 Span 依赖图
    graph := t.buildDependencyGraph()
    
    // 计算每个 Span 的最早开始时间和最晚结束时间
    est := make(map[string]time.Time)  // Earliest Start Time
    lft := make(map[string]time.Time)  // Latest Finish Time
    
    // 正向遍历计算 EST
    for _, span := range graph.TopologicalSort() {
        if span.ParentSpanID == "" {
            est[span.SpanID] = span.StartTime
        } else {
            parentEST := est[span.ParentSpanID]
            est[span.SpanID] = maxTime(span.StartTime, parentEST)
        }
    }
    
    // 反向遍历计算 LFT
    for i := len(graph.Nodes) - 1; i >= 0; i-- {
        span := graph.Nodes[i]
        if len(span.Children) == 0 {
            lft[span.SpanID] = span.EndTime
        } else {
            minChildLFT := time.Time{}
            for _, child := range span.Children {
                if minChildLFT.IsZero() || lft[child.SpanID].Before(minChildLFT) {
                    minChildLFT = lft[child.SpanID]
                }
            }
            lft[span.SpanID] = minTime(span.EndTime, minChildLFT)
        }
    }
    
    // 识别关键路径 (Slack = 0 的 Span)
    var criticalPath []Span
    for _, span := range t.Spans {
        slack := lft[span.SpanID].Sub(est[span.SpanID]) - span.Duration()
        if slack == 0 {
            criticalPath = append(criticalPath, span)
        }
    }
    
    return criticalPath
}
```

### 3.2 日志关联分析

**日志与 Trace 关联**:

```go
type LogEntry struct {
    Timestamp time.Time
    Level     string
    Message   string
    TraceID   string
    SpanID    string
    Attributes map[string]interface{}
}

func (le *LogEntry) CorrelateWithTrace(trace Trace) *Span {
    if le.TraceID != trace.TraceID {
        return nil
    }
    
    for _, span := range trace.Spans {
        if span.SpanID == le.SpanID {
            return &span
        }
    }
    
    return nil
}

// 查询: 给定 Trace,查找所有相关日志
func FindLogsForTrace(traceID string) []LogEntry {
    query := fmt.Sprintf(`
        SELECT * FROM logs
        WHERE trace_id = '%s'
        ORDER BY timestamp ASC
    `, traceID)
    
    return executeQuery(query)
}

// 查询: 给定错误日志,查找完整 Trace
func FindTraceForLog(logEntry LogEntry) Trace {
    if logEntry.TraceID == "" {
        return Trace{}
    }
    
    return fetchTrace(logEntry.TraceID)
}
```

**日志聚合分析**:

```go
type LogAggregator struct {
    window time.Duration
}

func (la *LogAggregator) AggregateErrors(logs []LogEntry) map[string]int {
    errorCounts := make(map[string]int)
    
    for _, log := range logs {
        if log.Level == "ERROR" {
            // 提取错误模式 (去除变量部分)
            pattern := la.extractPattern(log.Message)
            errorCounts[pattern]++
        }
    }
    
    return errorCounts
}

func (la *LogAggregator) extractPattern(message string) string {
    // 替换数字、UUID 等变量
    pattern := regexp.MustCompile(`\d+`).ReplaceAllString(message, "{num}")
    pattern = regexp.MustCompile(`[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}`).
        ReplaceAllString(pattern, "{uuid}")
    return pattern
}

// 示例输出:
// "Failed to connect to database: timeout after {num}ms" -> 127 次
// "User {uuid} not found" -> 45 次
```

### 3.3 指标异常检测

**统计异常检测**:

```go
type AnomalyDetector struct {
    window   time.Duration
    history  []float64
    threshold float64  // Z-score threshold (通常 3.0)
}

func (ad *AnomalyDetector) Detect(value float64) bool {
    if len(ad.history) < 30 {
        ad.history = append(ad.history, value)
        return false
    }
    
    mean, stddev := ad.statistics()
    zScore := (value - mean) / stddev
    
    isAnomaly := math.Abs(zScore) > ad.threshold
    
    if !isAnomaly {
        ad.history = append(ad.history[1:], value)
    }
    
    return isAnomaly
}

func (ad *AnomalyDetector) statistics() (float64, float64) {
    // 计算均值
    sum := 0.0
    for _, v := range ad.history {
        sum += v
    }
    mean := sum / float64(len(ad.history))
    
    // 计算标准差
    variance := 0.0
    for _, v := range ad.history {
        variance += math.Pow(v-mean, 2)
    }
    stddev := math.Sqrt(variance / float64(len(ad.history)))
    
    return mean, stddev
}
```

**机器学习异常检测**:

```go
type MLAnomalyDetector struct {
    model IsolationForest
}

func (mlad *MLAnomalyDetector) Train(metrics []MetricPoint) {
    features := mlad.extractFeatures(metrics)
    mlad.model.Fit(features)
}

func (mlad *MLAnomalyDetector) Detect(metric MetricPoint) (bool, float64) {
    features := mlad.extractFeatures([]MetricPoint{metric})
    score := mlad.model.AnomalyScore(features[0])
    
    // score > 0.5 表示异常
    return score > 0.5, score
}

func (mlad *MLAnomalyDetector) extractFeatures(metrics []MetricPoint) [][]float64 {
    var features [][]float64
    
    for _, m := range metrics {
        feature := []float64{
            m.Value,
            m.Rate(),
            m.Variance(),
            m.Trend(),
        }
        features = append(features, feature)
    }
    
    return features
}
```

### 3.4 根因分析

**因果图分析**:

```go
type CausalGraph struct {
    nodes map[string]*Node
    edges map[string][]string
}

type Node struct {
    ID     string
    Type   string  // "service", "database", "cache"
    Status string  // "healthy", "degraded", "failed"
}

func (cg *CausalGraph) FindRootCause(symptom string) []string {
    // 1. 从症状节点开始反向遍历
    visited := make(map[string]bool)
    var rootCauses []string
    
    cg.dfs(symptom, visited, &rootCauses)
    
    // 2. 按影响范围排序
    sort.Slice(rootCauses, func(i, j int) bool {
        return cg.impactScore(rootCauses[i]) > cg.impactScore(rootCauses[j])
    })
    
    return rootCauses
}

func (cg *CausalGraph) dfs(nodeID string, visited map[string]bool, rootCauses *[]string) {
    if visited[nodeID] {
        return
    }
    visited[nodeID] = true
    
    node := cg.nodes[nodeID]
    
    // 如果节点失败且没有上游依赖失败,则为根因
    upstreamFailed := false
    for _, upstream := range cg.getUpstream(nodeID) {
        if cg.nodes[upstream].Status == "failed" {
            upstreamFailed = true
            cg.dfs(upstream, visited, rootCauses)
        }
    }
    
    if node.Status == "failed" && !upstreamFailed {
        *rootCauses = append(*rootCauses, nodeID)
    }
}

func (cg *CausalGraph) impactScore(nodeID string) int {
    // 计算影响的下游节点数量
    visited := make(map[string]bool)
    return cg.countDownstream(nodeID, visited)
}
```

**5 Whys 分析**:

```go
type WhyAnalysis struct {
    Question string
    Answer   string
    Evidence []Evidence
    Next     *WhyAnalysis
}

type Evidence struct {
    Type string  // "trace", "log", "metric"
    Data interface{}
}

func (wa *WhyAnalysis) Ask5Whys(initialQuestion string) *WhyAnalysis {
    current := &WhyAnalysis{Question: initialQuestion}
    root := current
    
    for i := 0; i < 5; i++ {
        // 查找证据
        evidence := wa.findEvidence(current.Question)
        current.Evidence = evidence
        
        // 生成答案
        current.Answer = wa.generateAnswer(evidence)
        
        // 生成下一个问题
        if i < 4 {
            nextQuestion := fmt.Sprintf("Why %s?", current.Answer)
            current.Next = &WhyAnalysis{Question: nextQuestion}
            current = current.Next
        }
    }
    
    return root
}

// 示例:
// Q1: Why is the API slow?
// A1: Because the database query takes 5 seconds
// Q2: Why does the database query take 5 seconds?
// A2: Because there's no index on the user_id column
// Q3: Why is there no index?
// A3: Because the migration script failed
// Q4: Why did the migration script fail?
// A4: Because of insufficient disk space
// Q5: Why is there insufficient disk space?
// A5: Because log files are not being rotated
```

### 3.5 时间旅行调试

**快照回放**:

```go
type TimeTravel struct {
    snapshots []Snapshot
}

type Snapshot struct {
    Timestamp time.Time
    State     SystemState
    Events    []Event
}

func (tt *TimeTravel) ReplayTo(targetTime time.Time) SystemState {
    // 1. 找到最接近的快照
    snapshot := tt.findClosestSnapshot(targetTime)
    
    // 2. 从快照开始重放事件
    state := snapshot.State
    for _, event := range snapshot.Events {
        if event.Timestamp.After(targetTime) {
            break
        }
        state = state.Apply(event)
    }
    
    return state
}

func (tt *TimeTravel) DebugAt(targetTime time.Time) *Debugger {
    state := tt.ReplayTo(targetTime)
    return &Debugger{
        state:     state,
        timestamp: targetTime,
    }
}

// 使用示例
func debugIssue() {
    tt := NewTimeTravel()
    
    // 回到故障发生前 5 分钟
    issueTime := time.Parse(time.RFC3339, "2025-01-01T10:30:00Z")
    debugger := tt.DebugAt(issueTime.Add(-5 * time.Minute))
    
    // 单步执行
    for debugger.HasNext() {
        event := debugger.Step()
        fmt.Printf("[%v] %s\n", event.Timestamp, event.Description)
        
        if event.Type == "ERROR" {
            fmt.Printf("Found error: %v\n", event.Data)
            break
        }
    }
}
```

## 4. 监测机制 (Monitoring)

### 4.1 四个黄金信号

**Google SRE 四个黄金信号**:

```go
type GoldenSignals struct {
    Latency      *LatencyMetric
    Traffic      *TrafficMetric
    Errors       *ErrorMetric
    Saturation   *SaturationMetric
}

type LatencyMetric struct {
    P50  time.Duration
    P95  time.Duration
    P99  time.Duration
}

func (ls *GoldenSignals) Collect() {
    // 1. Latency (延迟)
    ls.Latency = &LatencyMetric{
        P50: calculatePercentile(0.50),
        P95: calculatePercentile(0.95),
        P99: calculatePercentile(0.99),
    }
    
    // 2. Traffic (流量)
    ls.Traffic = &TrafficMetric{
        RequestsPerSecond: calculateRPS(),
        BytesPerSecond:    calculateBPS(),
    }
    
    // 3. Errors (错误率)
    ls.Errors = &ErrorMetric{
        ErrorRate:   calculateErrorRate(),
        ErrorCount:  countErrors(),
    }
    
    // 4. Saturation (饱和度)
    ls.Saturation = &SaturationMetric{
        CPUUsage:    getCPUUsage(),
        MemoryUsage: getMemoryUsage(),
        QueueDepth:  getQueueDepth(),
    }
}

// Prometheus 查询示例
const (
    LatencyQuery = `
        histogram_quantile(0.95,
            rate(http_request_duration_seconds_bucket[5m])
        )
    `
    
    TrafficQuery = `
        rate(http_requests_total[5m])
    `
    
    ErrorsQuery = `
        rate(http_requests_total{status=~"5.."}[5m])
        /
        rate(http_requests_total[5m])
    `
    
    SaturationQuery = `
        avg(rate(container_cpu_usage_seconds_total[5m])) by (pod)
    `
)
```

### 4.2 RED 方法

**Rate, Errors, Duration**:

```go
type REDMetrics struct {
    Rate     float64
    Errors   float64
    Duration time.Duration
}

func (red *REDMetrics) Collect(service string) {
    // Rate: 请求速率
    red.Rate = prometheus.Query(fmt.Sprintf(`
        rate(http_requests_total{service="%s"}[5m])
    `, service))
    
    // Errors: 错误率
    red.Errors = prometheus.Query(fmt.Sprintf(`
        rate(http_requests_total{service="%s",status=~"5.."}[5m])
        /
        rate(http_requests_total{service="%s"}[5m])
    `, service, service))
    
    // Duration: 响应时间
    red.Duration = prometheus.Query(fmt.Sprintf(`
        histogram_quantile(0.95,
            rate(http_request_duration_seconds_bucket{service="%s"}[5m])
        )
    `, service))
}

// Grafana Dashboard JSON
const REDDashboard = `
{
  "panels": [
    {
      "title": "Request Rate",
      "targets": [{
        "expr": "rate(http_requests_total[5m])"
      }]
    },
    {
      "title": "Error Rate",
      "targets": [{
        "expr": "rate(http_requests_total{status=~\"5..\"}[5m])"
      }]
    },
    {
      "title": "Duration (P95)",
      "targets": [{
        "expr": "histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))"
      }]
    }
  ]
}
`
```

### 4.3 USE 方法

**Utilization, Saturation, Errors**:

```go
type USEMetrics struct {
    Utilization float64
    Saturation  float64
    Errors      int64
}

func (use *USEMetrics) CollectForResource(resource string) {
    switch resource {
    case "CPU":
        use.Utilization = getCPUUtilization()
        use.Saturation = getRunQueueLength()
        use.Errors = getCPUThrottlingCount()
        
    case "Memory":
        use.Utilization = getMemoryUtilization()
        use.Saturation = getSwapUsage()
        use.Errors = getOOMKillCount()
        
    case "Disk":
        use.Utilization = getDiskUtilization()
        use.Saturation = getDiskQueueLength()
        use.Errors = getDiskErrorCount()
        
    case "Network":
        use.Utilization = getNetworkUtilization()
        use.Saturation = getNetworkBufferUtilization()
        use.Errors = getNetworkErrorCount()
    }
}

// Prometheus 查询
const (
    CPUUtilizationQuery = `
        avg(rate(container_cpu_usage_seconds_total[5m])) by (pod)
    `
    
    CPUSaturationQuery = `
        avg(container_cpu_cfs_throttled_seconds_total) by (pod)
    `
    
    MemoryUtilizationQuery = `
        container_memory_usage_bytes / container_spec_memory_limit_bytes
    `
    
    MemorySaturationQuery = `
        container_memory_swap
    `
)
```

### 4.4 健康检查

**多层次健康检查**:

```go
type HealthChecker struct {
    checks []HealthCheck
}

type HealthCheck interface {
    Name() string
    Check(ctx context.Context) error
}

// Liveness 检查 (存活性)
type LivenessCheck struct{}

func (lc *LivenessCheck) Check(ctx context.Context) error {
    // 检查进程是否响应
    select {
    case <-ctx.Done():
        return ctx.Err()
    case <-time.After(100 * time.Millisecond):
        return nil
    }
}

// Readiness 检查 (就绪性)
type ReadinessCheck struct {
    dependencies []Dependency
}

func (rc *ReadinessCheck) Check(ctx context.Context) error {
    for _, dep := range rc.dependencies {
        if err := dep.Ping(ctx); err != nil {
            return fmt.Errorf("dependency %s not ready: %w", dep.Name(), err)
        }
    }
    return nil
}

// Startup 检查 (启动)
type StartupCheck struct {
    initialized atomic.Bool
}

func (sc *StartupCheck) Check(ctx context.Context) error {
    if !sc.initialized.Load() {
        return errors.New("not initialized")
    }
    return nil
}

// HTTP Handler
func (hc *HealthChecker) ServeHTTP(w http.ResponseWriter, r *http.Request) {
    ctx, cancel := context.WithTimeout(r.Context(), 5*time.Second)
    defer cancel()
    
    results := make(map[string]string)
    allHealthy := true
    
    for _, check := range hc.checks {
        if err := check.Check(ctx); err != nil {
            results[check.Name()] = fmt.Sprintf("FAIL: %v", err)
            allHealthy = false
        } else {
            results[check.Name()] = "OK"
        }
    }
    
    if allHealthy {
        w.WriteHeader(http.StatusOK)
    } else {
        w.WriteHeader(http.StatusServiceUnavailable)
    }
    
    json.NewEncoder(w).Encode(results)
}
```

### 4.5 SLI/SLO/SLA

**服务等级指标 (SLI)**:

```go
type SLI struct {
    Name        string
    Description string
    Query       string
    Target      float64
}

var SLIs = []SLI{
    {
        Name:        "Availability",
        Description: "Percentage of successful requests",
        Query: `
            sum(rate(http_requests_total{status!~"5.."}[30d]))
            /
            sum(rate(http_requests_total[30d]))
        `,
        Target: 0.999,  // 99.9%
    },
    {
        Name:        "Latency",
        Description: "95th percentile latency",
        Query: `
            histogram_quantile(0.95,
                rate(http_request_duration_seconds_bucket[30d])
            )
        `,
        Target: 0.1,  // 100ms
    },
}
```

**服务等级目标 (SLO)**:

```go
type SLO struct {
    SLI          SLI
    Target       float64
    Window       time.Duration
    ErrorBudget  float64
}

func (slo *SLO) CalculateErrorBudget() float64 {
    return 1.0 - slo.Target
}

func (slo *SLO) RemainingErrorBudget(current float64) float64 {
    errorBudget := slo.CalculateErrorBudget()
    consumed := 1.0 - current
    return errorBudget - consumed
}

// 示例: 99.9% 可用性 SLO
var AvailabilitySLO = SLO{
    SLI:    SLIs[0],
    Target: 0.999,
    Window: 30 * 24 * time.Hour,  // 30 天
}

// 错误预算: 1 - 0.999 = 0.001 = 0.1%
// 30 天 = 43,200 分钟
// 允许停机时间: 43,200 * 0.001 = 43.2 分钟
```

**服务等级协议 (SLA)**:

```go
type SLA struct {
    SLO         SLO
    Penalty     func(breach float64) float64
    CompensationTerms string
}

func (sla *SLA) CalculatePenalty(actualAvailability float64) float64 {
    if actualAvailability >= sla.SLO.Target {
        return 0
    }
    
    breach := sla.SLO.Target - actualAvailability
    return sla.Penalty(breach)
}

// 示例: 阶梯式赔偿
var StandardSLA = SLA{
    SLO: AvailabilitySLO,
    Penalty: func(breach float64) float64 {
        switch {
        case breach < 0.001:  // 99.9% - 99.8%
            return 0.10  // 10% 服务费用
        case breach < 0.01:   // 99.8% - 99.0%
            return 0.25  // 25% 服务费用
        default:              // < 99.0%
            return 0.50  // 50% 服务费用
        }
    },
    CompensationTerms: "Service credits applied to next billing cycle",
}
```

## 5. 控制机制 (Control)

### 5.1 反馈控制

**PID 控制器**:

```go
type PIDController struct {
    Kp         float64  // 比例系数
    Ki         float64  // 积分系数
    Kd         float64  // 微分系数
    setpoint   float64  // 目标值
    integral   float64
    lastError  float64
    lastTime   time.Time
}

func (pid *PIDController) Update(measured float64) float64 {
    now := time.Now()
    dt := now.Sub(pid.lastTime).Seconds()
    
    // 计算误差
    error := pid.setpoint - measured
    
    // 比例项
    P := pid.Kp * error
    
    // 积分项
    pid.integral += error * dt
    I := pid.Ki * pid.integral
    
    // 微分项
    derivative := (error - pid.lastError) / dt
    D := pid.Kd * derivative
    
    // 更新状态
    pid.lastError = error
    pid.lastTime = now
    
    // 输出控制量
    return P + I + D
}

// OTLP 使用 PID 控制采样率
type AdaptiveSampler struct {
    pid        *PIDController
    targetCPU  float64
}

func (as *AdaptiveSampler) AdjustSamplingRate() {
    currentCPU := getCPUUsage()
    
    // PID 控制器输出调整量
    adjustment := as.pid.Update(currentCPU)
    
    // 应用调整
    currentRate := getSamplingRate()
    newRate := currentRate + adjustment
    
    // 限制范围 [0.01, 1.0]
    newRate = math.Max(0.01, math.Min(1.0, newRate))
    
    setSamplingRate(newRate)
}
```

### 5.2 自适应采样

**动态采样策略**:

```go
type AdaptiveSamplingStrategy struct {
    baseRate      float64
    errorBoost    float64
    latencyBoost  float64
    loadFactor    float64
}

func (ass *AdaptiveSamplingStrategy) ShouldSample(span Span) bool {
    rate := ass.baseRate
    
    // 错误 Span 提高采样率
    if span.Status == "ERROR" {
        rate *= ass.errorBoost
    }
    
    // 慢请求提高采样率
    if span.Duration() > 1*time.Second {
        rate *= ass.latencyBoost
    }
    
    // 根据系统负载调整
    load := getSystemLoad()
    if load > 0.8 {
        rate *= ass.loadFactor
    }
    
    return rand.Float64() < rate
}

// 示例配置
var DefaultAdaptiveSampling = AdaptiveSamplingStrategy{
    baseRate:     0.1,   // 10% 基础采样率
    errorBoost:   10.0,  // 错误 100% 采样
    latencyBoost: 5.0,   // 慢请求 50% 采样
    loadFactor:   0.5,   // 高负载降低采样率
}
```

### 5.3 流量控制

**令牌桶算法**:

```go
type TokenBucket struct {
    capacity   int64
    tokens     atomic.Int64
    rate       float64  // tokens per second
    lastRefill atomic.Value
}

func (tb *TokenBucket) Allow() bool {
    tb.refill()
    
    for {
        tokens := tb.tokens.Load()
        if tokens <= 0 {
            return false
        }
        
        if tb.tokens.CompareAndSwap(tokens, tokens-1) {
            return true
        }
    }
}

func (tb *TokenBucket) refill() {
    now := time.Now()
    last := tb.lastRefill.Load().(time.Time)
    
    elapsed := now.Sub(last).Seconds()
    tokensToAdd := int64(elapsed * tb.rate)
    
    if tokensToAdd > 0 {
        for {
            current := tb.tokens.Load()
            new := min(current+tokensToAdd, tb.capacity)
            
            if tb.tokens.CompareAndSwap(current, new) {
                tb.lastRefill.Store(now)
                break
            }
        }
    }
}

// OTLP 使用令牌桶限流
func (c *Collector) ProcessWithRateLimit(data []byte) error {
    if !c.rateLimiter.Allow() {
        return errors.New("rate limit exceeded")
    }
    
    return c.process(data)
}
```

### 5.4 配置管理

**OPAMP 配置管理**:

```go
type ConfigManager struct {
    current    *Config
    pending    *Config
    history    []Config
    validator  ConfigValidator
    rollbacker Rollbacker
}

func (cm *ConfigManager) ApplyConfig(newConfig *Config) error {
    // 1. 验证配置
    if err := cm.validator.Validate(newConfig); err != nil {
        return fmt.Errorf("invalid config: %w", err)
    }
    
    // 2. 保存当前配置到历史
    cm.history = append(cm.history, *cm.current)
    
    // 3. 应用新配置
    cm.pending = newConfig
    if err := cm.apply(newConfig); err != nil {
        // 4. 应用失败,回滚
        cm.rollback()
        return err
    }
    
    // 5. 健康检查
    if !cm.healthCheck() {
        cm.rollback()
        return errors.New("health check failed after config update")
    }
    
    // 6. 提交配置
    cm.current = newConfig
    cm.pending = nil
    
    return nil
}

func (cm *ConfigManager) rollback() {
    if len(cm.history) == 0 {
        return
    }
    
    lastGood := cm.history[len(cm.history)-1]
    cm.apply(&lastGood)
    cm.current = &lastGood
    cm.history = cm.history[:len(cm.history)-1]
}
```

### 5.5 混沌工程

**故障注入**:

```go
type ChaosExperiment struct {
    name        string
    probability float64
    faultType   FaultType
    duration    time.Duration
}

type FaultType int

const (
    LatencyFault FaultType = iota
    ErrorFault
    DropFault
    PartitionFault
)

func (ce *ChaosExperiment) Inject(ctx context.Context, fn func() error) error {
    if rand.Float64() > ce.probability {
        return fn()
    }
    
    switch ce.faultType {
    case LatencyFault:
        time.Sleep(ce.duration)
        return fn()
        
    case ErrorFault:
        return errors.New("injected error")
        
    case DropFault:
        return nil  // 丢弃请求
        
    case PartitionFault:
        // 模拟网络分区
        return errors.New("network partition")
    }
    
    return fn()
}

// 使用示例
func (c *Collector) ProcessWithChaos(data []byte) error {
    experiment := ChaosExperiment{
        name:        "latency_injection",
        probability: 0.01,  // 1% 概率
        faultType:   LatencyFault,
        duration:    500 * time.Millisecond,
    }
    
    return experiment.Inject(context.Background(), func() error {
        return c.process(data)
    })
}
```

## 6. 定位机制 (Localization)

### 6.1 故障定位

**二分查找故障**:

```go
type FaultLocalizer struct {
    components []Component
}

func (fl *FaultLocalizer) BinarySearch() Component {
    left, right := 0, len(fl.components)-1
    
    for left < right {
        mid := (left + right) / 2
        
        // 测试前半部分
        if fl.testComponents(fl.components[left:mid+1]) {
            // 前半部分正常,故障在后半部分
            left = mid + 1
        } else {
            // 前半部分有故障
            right = mid
        }
    }
    
    return fl.components[left]
}

func (fl *FaultLocalizer) testComponents(components []Component) bool {
    for _, comp := range components {
        if !comp.HealthCheck() {
            return false
        }
    }
    return true
}
```

**依赖链追踪**:

```go
func (fl *FaultLocalizer) TraceDependencyChain(service string) []string {
    visited := make(map[string]bool)
    var chain []string
    
    fl.dfs(service, visited, &chain)
    
    return chain
}

func (fl *FaultLocalizer) dfs(service string, visited map[string]bool, chain *[]string) {
    if visited[service] {
        return
    }
    visited[service] = true
    
    *chain = append(*chain, service)
    
    // 检查依赖
    for _, dep := range fl.getDependencies(service) {
        if !fl.isHealthy(dep) {
            fl.dfs(dep, visited, chain)
        }
    }
}
```

### 6.2 性能瓶颈定位

**火焰图分析**:

```go
type FlameGraph struct {
    root *FlameNode
}

type FlameNode struct {
    Name     string
    Value    int64
    Children []*FlameNode
}

func (fg *FlameGraph) BuildFromTrace(trace Trace) {
    fg.root = &FlameNode{Name: "root"}
    
    for _, span := range trace.Spans {
        fg.addSpan(fg.root, span)
    }
}

func (fg *FlameGraph) addSpan(node *FlameNode, span Span) {
    // 查找或创建子节点
    var child *FlameNode
    for _, c := range node.Children {
        if c.Name == span.Name {
            child = c
            break
        }
    }
    
    if child == nil {
        child = &FlameNode{Name: span.Name}
        node.Children = append(node.Children, child)
    }
    
    child.Value += span.Duration().Nanoseconds()
}

func (fg *FlameGraph) FindBottleneck() *FlameNode {
    return fg.findMax(fg.root)
}

func (fg *FlameGraph) findMax(node *FlameNode) *FlameNode {
    max := node
    
    for _, child := range node.Children {
        candidate := fg.findMax(child)
        if candidate.Value > max.Value {
            max = candidate
        }
    }
    
    return max
}
```

### 6.3 异常传播路径

**异常传播图**:

```go
type ExceptionPropagation struct {
    graph *DependencyGraph
}

func (ep *ExceptionPropagation) TracePropagation(exception Exception) []PropagationPath {
    var paths []PropagationPath
    
    // 从异常源开始 BFS
    queue := []Node{{Service: exception.Source, Depth: 0}}
    visited := make(map[string]bool)
    
    for len(queue) > 0 {
        node := queue[0]
        queue = queue[1:]
        
        if visited[node.Service] {
            continue
        }
        visited[node.Service] = true
        
        // 检查是否有相同异常
        if ep.hasException(node.Service, exception.Type) {
            paths = append(paths, PropagationPath{
                From:  exception.Source,
                To:    node.Service,
                Depth: node.Depth,
            })
        }
        
        // 添加下游服务
        for _, downstream := range ep.graph.GetDownstream(node.Service) {
            queue = append(queue, Node{
                Service: downstream,
                Depth:   node.Depth + 1,
            })
        }
    }
    
    return paths
}
```

### 6.4 依赖关系图

**服务依赖图构建**:

```go
type DependencyGraph struct {
    nodes map[string]*ServiceNode
    edges map[string][]string
}

type ServiceNode struct {
    Name    string
    Type    string
    Metrics ServiceMetrics
}

func (dg *DependencyGraph) BuildFromTraces(traces []Trace) {
    for _, trace := range traces {
        for _, span := range trace.Spans {
            // 添加节点
            if _, ok := dg.nodes[span.ServiceName]; !ok {
                dg.nodes[span.ServiceName] = &ServiceNode{
                    Name: span.ServiceName,
                    Type: span.ServiceType,
                }
            }
            
            // 添加边 (调用关系)
            if span.ParentSpanID != "" {
                parentSpan := trace.FindSpan(span.ParentSpanID)
                if parentSpan != nil {
                    dg.addEdge(parentSpan.ServiceName, span.ServiceName)
                }
            }
        }
    }
}

func (dg *DependencyGraph) FindCriticalPath() []string {
    // 使用 PageRank 算法找到关键服务
    ranks := dg.pageRank()
    
    var critical []string
    for service, rank := range ranks {
        if rank > 0.1 {  // 阈值
            critical = append(critical, service)
        }
    }
    
    return critical
}

func (dg *DependencyGraph) pageRank() map[string]float64 {
    ranks := make(map[string]float64)
    for service := range dg.nodes {
        ranks[service] = 1.0 / float64(len(dg.nodes))
    }
    
    damping := 0.85
    iterations := 100
    
    for i := 0; i < iterations; i++ {
        newRanks := make(map[string]float64)
        
        for service := range dg.nodes {
            sum := 0.0
            for _, upstream := range dg.GetUpstream(service) {
                outDegree := len(dg.edges[upstream])
                sum += ranks[upstream] / float64(outDegree)
            }
            
            newRanks[service] = (1-damping)/float64(len(dg.nodes)) + damping*sum
        }
        
        ranks = newRanks
    }
    
    return ranks
}
```

### 6.5 拓扑感知定位

**区域感知故障定位**:

```go
type TopologyAwareLocalizer struct {
    topology *NetworkTopology
}

type NetworkTopology struct {
    regions map[string]*Region
}

type Region struct {
    Name     string
    Zones    []*Zone
    Latency  map[string]time.Duration  // 到其他区域的延迟
}

func (tal *TopologyAwareLocalizer) LocalizeByTopology(issue Issue) *Region {
    // 1. 收集受影响的服务实例
    affectedInstances := tal.getAffectedInstances(issue)
    
    // 2. 按区域聚合
    regionCounts := make(map[string]int)
    for _, instance := range affectedInstances {
        region := tal.topology.GetRegion(instance)
        regionCounts[region]++
    }
    
    // 3. 找到受影响最严重的区域
    maxCount := 0
    var faultyRegion string
    for region, count := range regionCounts {
        if count > maxCount {
            maxCount = count
            faultyRegion = region
        }
    }
    
    return tal.topology.regions[faultyRegion]
}
```

## 7. 可观测性三支柱集成

### 7.1 Traces + Logs + Metrics

**统一数据模型**:

```go
type ObservabilityData struct {
    TraceID    string
    SpanID     string
    Timestamp  time.Time
    Resource   Resource
    Attributes map[string]interface{}
    
    // 可选字段
    Trace  *Trace
    Logs   []LogEntry
    Metrics []MetricPoint
}

func (od *ObservabilityData) Correlate() {
    // 1. 通过 TraceID 关联 Logs
    od.Logs = findLogsByTraceID(od.TraceID)
    
    // 2. 通过 Resource 关联 Metrics
    od.Metrics = findMetricsByResource(od.Resource)
    
    // 3. 构建完整上下文
    od.buildContext()
}
```

### 7.2 关联查询

**跨信号查询**:

```sql
-- 查询: 给定 Trace,查找相关日志和指标
WITH trace_context AS (
    SELECT
        trace_id,
        span_id,
        service_name,
        start_time,
        end_time
    FROM traces
    WHERE trace_id = '${trace_id}'
)
SELECT
    t.trace_id,
    t.span_id,
    l.timestamp AS log_time,
    l.message AS log_message,
    m.timestamp AS metric_time,
    m.value AS metric_value
FROM trace_context t
LEFT JOIN logs l ON l.trace_id = t.trace_id AND l.span_id = t.span_id
LEFT JOIN metrics m ON m.service_name = t.service_name
    AND m.timestamp BETWEEN t.start_time AND t.end_time
ORDER BY l.timestamp, m.timestamp;
```

### 7.3 统一上下文

**Context Propagation**:

```go
type UnifiedContext struct {
    TraceID    string
    SpanID     string
    BaggageItems map[string]string
}

func (uc *UnifiedContext) Inject(carrier interface{}) {
    switch c := carrier.(type) {
    case http.Header:
        c.Set("traceparent", fmt.Sprintf("00-%s-%s-01", uc.TraceID, uc.SpanID))
        for k, v := range uc.BaggageItems {
            c.Set(fmt.Sprintf("baggage-%s", k), v)
        }
        
    case map[string]string:
        c["trace_id"] = uc.TraceID
        c["span_id"] = uc.SpanID
        for k, v := range uc.BaggageItems {
            c[k] = v
        }
    }
}

func (uc *UnifiedContext) Extract(carrier interface{}) error {
    switch c := carrier.(type) {
    case http.Header:
        traceparent := c.Get("traceparent")
        parts := strings.Split(traceparent, "-")
        if len(parts) >= 3 {
            uc.TraceID = parts[1]
            uc.SpanID = parts[2]
        }
        
        for k, v := range c {
            if strings.HasPrefix(k, "baggage-") {
                key := strings.TrimPrefix(k, "baggage-")
                uc.BaggageItems[key] = v[0]
            }
        }
    }
    
    return nil
}
```

## 8. 自动化运维

### 8.1 自动告警

**智能告警**:

```go
type AlertRule struct {
    Name        string
    Condition   string
    Severity    string
    Annotations map[string]string
}

type AlertManager struct {
    rules       []AlertRule
    deduplicator *AlertDeduplicator
    aggregator  *AlertAggregator
}

func (am *AlertManager) Evaluate(metrics map[string]float64) []Alert {
    var alerts []Alert
    
    for _, rule := range am.rules {
        if am.evaluateCondition(rule.Condition, metrics) {
            alert := Alert{
                Name:        rule.Name,
                Severity:    rule.Severity,
                Timestamp:   time.Now(),
                Annotations: rule.Annotations,
            }
            
            // 去重
            if !am.deduplicator.IsDuplicate(alert) {
                alerts = append(alerts, alert)
            }
        }
    }
    
    // 聚合相关告警
    return am.aggregator.Aggregate(alerts)
}

// Prometheus AlertManager 配置
const AlertConfig = `
groups:
  - name: otlp_alerts
    rules:
      - alert: HighErrorRate
        expr: rate(http_requests_total{status=~"5.."}[5m]) > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate is {{ $value }}%"
      
      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 1
        for: 10m
        labels:
          severity: warning
        annotations:
          summary: "High latency detected"
          description: "P95 latency is {{ $value }}s"
`
```

### 8.2 自动修复

**自愈系统**:

```go
type AutoRemediator struct {
    detectors []AnomalyDetector
    actions   map[string]RemediationAction
}

type RemediationAction interface {
    Execute(ctx context.Context, anomaly Anomaly) error
    Rollback(ctx context.Context) error
}

// 重启 Pod
type RestartPodAction struct {
    k8sClient kubernetes.Interface
}

func (rpa *RestartPodAction) Execute(ctx context.Context, anomaly Anomaly) error {
    podName := anomaly.Metadata["pod_name"]
    namespace := anomaly.Metadata["namespace"]
    
    return rpa.k8sClient.CoreV1().Pods(namespace).Delete(ctx, podName, metav1.DeleteOptions{})
}

// 扩容
type ScaleUpAction struct {
    k8sClient kubernetes.Interface
}

func (sua *ScaleUpAction) Execute(ctx context.Context, anomaly Anomaly) error {
    deployment := anomaly.Metadata["deployment"]
    namespace := anomaly.Metadata["namespace"]
    
    scale, err := sua.k8sClient.AppsV1().Deployments(namespace).GetScale(ctx, deployment, metav1.GetOptions{})
    if err != nil {
        return err
    }
    
    scale.Spec.Replicas++
    
    _, err = sua.k8sClient.AppsV1().Deployments(namespace).UpdateScale(ctx, deployment, scale, metav1.UpdateOptions{})
    return err
}

// 降级
type DegradeAction struct {
    configManager *ConfigManager
}

func (da *DegradeAction) Execute(ctx context.Context, anomaly Anomaly) error {
    degradedConfig := &Config{
        SamplingRate: 0.1,
        Features: map[string]bool{
            "tail_sampling": false,
            "complex_transform": false,
        },
    }
    
    return da.configManager.ApplyConfig(degradedConfig)
}
```

### 8.3 预测性维护

**时间序列预测**:

```go
type Predictor struct {
    model TimeSeriesModel
}

func (p *Predictor) PredictFailure(metrics []MetricPoint) (bool, time.Time) {
    // 1. 特征提取
    features := p.extractFeatures(metrics)
    
    // 2. 预测未来值
    future := p.model.Forecast(features, 24)  // 预测未来 24 小时
    
    // 3. 检测是否会超过阈值
    for i, value := range future {
        if value > threshold {
            failureTime := time.Now().Add(time.Duration(i) * time.Hour)
            return true, failureTime
        }
    }
    
    return false, time.Time{}
}

// ARIMA 模型
type ARIMAModel struct {
    p, d, q int
    params  []float64
}

func (am *ARIMAModel) Forecast(data []float64, steps int) []float64 {
    // ARIMA(p, d, q) 预测
    // 实现略
    return nil
}
```

## 9. 案例研究

### 9.1 案例1: 级联故障定位

**场景**: 支付服务突然大量超时

**排查过程**:

```go
func investigateCascadingFailure() {
    // 1. 查看支付服务的 Traces
    traces := fetchTraces("service.name=payment AND status=ERROR")
    
    // 2. 分析依赖链
    for _, trace := range traces {
        deps := analyzeDependencies(trace)
        fmt.Printf("Dependencies: %v\n", deps)
        // Output: [payment -> order -> inventory -> database]
    }
    
    // 3. 检查每个依赖的健康状态
    healthStatus := map[string]string{
        "payment":   "degraded",
        "order":     "degraded",
        "inventory": "healthy",
        "database":  "failed",  // 根因!
    }
    
    // 4. 查看数据库指标
    dbMetrics := fetchMetrics("service.name=database")
    fmt.Printf("DB Connections: %d/%d\n", dbMetrics.ActiveConnections, dbMetrics.MaxConnections)
    // Output: DB Connections: 1000/1000 (连接池耗尽)
    
    // 5. 查看数据库日志
    dbLogs := fetchLogs("service.name=database AND level=ERROR")
    // Output: "Too many connections"
    
    // 6. 根因: 数据库连接池耗尽导致级联故障
    fmt.Println("Root Cause: Database connection pool exhausted")
    
    // 7. 修复: 增加连接池大小
    scaleDatabase()
}
```

### 9.2 案例2: 内存泄漏排查

**场景**: Collector 内存持续增长

**排查过程**:

```go
func investigateMemoryLeak() {
    // 1. 采集 heap profile
    pprof.WriteHeapProfile(f)
    
    // 2. 分析 profile
    // go tool pprof -http=:8080 heap.prof
    
    // 3. 发现大量 Span 对象未释放
    // Top objects:
    // 500MB: []Span
    // 200MB: map[string]*Span
    
    // 4. 检查 Span 生命周期
    spans := getAllSpans()
    for _, span := range spans {
        age := time.Since(span.CreateTime)
        if age > 1*time.Hour {
            fmt.Printf("Old span: %s, age: %v\n", span.SpanID, age)
        }
    }
    
    // 5. 发现: 尾部采样缓冲区未清理
    // 根因: decision_wait 超时后未删除 Span
    
    // 6. 修复: 添加定期清理逻辑
    go func() {
        ticker := time.NewTicker(10 * time.Minute)
        for range ticker.C {
            cleanupOldSpans()
        }
    }()
}
```

### 9.3 案例3: 网络分区恢复

**场景**: 跨区域网络分区

**恢复过程**:

```go
func handleNetworkPartition() {
    // 1. 检测分区
    partitions := detectPartitions()
    fmt.Printf("Detected partitions: %v\n", partitions)
    // Output: [region-us-west, region-us-east]
    
    // 2. 确定多数派
    majority := findMajority(partitions)
    fmt.Printf("Majority: %s\n", majority)
    // Output: region-us-west (3 nodes vs 2 nodes)
    
    // 3. 少数派进入只读模式
    if !isMajority() {
        enterReadOnlyMode()
    }
    
    // 4. 等待分区恢复
    waitForPartitionHealing()
    
    // 5. 同步数据
    if isPartitionHealed() {
        syncData()
    }
    
    // 6. 解决冲突
    conflicts := detectConflicts()
    for _, conflict := range conflicts {
        resolveConflict(conflict)
    }
    
    // 7. 恢复正常模式
    exitReadOnlyMode()
}
```

## 10. 参考文献

1. **容错理论**:
   - Avizienis, A., et al. "Basic Concepts and Taxonomy of Dependable and Secure Computing" (2004)
   - Cristian, F. "Understanding Fault-Tolerant Distributed Systems" (1991)

2. **调试技术**:
   - Zeller, A. "Why Programs Fail: A Guide to Systematic Debugging" (2009)
   - Agans, D. J. "Debugging: The 9 Indispensable Rules" (2006)

3. **监控与可观测性**:
   - Beyer, B., et al. "Site Reliability Engineering" (Google SRE Book, 2016)
   - Majors, C., et al. "Observability Engineering" (2022)

4. **控制理论**:
   - Hellerstein, J. L., et al. "Feedback Control of Computing Systems" (2004)
   - Åström, K. J., & Murray, R. M. "Feedback Systems: An Introduction for Scientists and Engineers" (2008)

5. **混沌工程**:
   - Basiri, A., et al. "Chaos Engineering" (O'Reilly, 2020)
   - Rosenthal, C., & Hochstein, L. "Chaos Engineering: System Resiliency in Practice" (2020)

6. **相关文档**:
   - `docs/analysis/computational-model/control-execution-data-flow.md` - 控制流/执行流/数据流
   - `docs/analysis/computational-model/distributed-systems-theory.md` - 分布式系统理论
   - `docs/design/distributed-model.md` - 分布式模型
   - `docs/opamp/overview.md` - OPAMP 控制平面

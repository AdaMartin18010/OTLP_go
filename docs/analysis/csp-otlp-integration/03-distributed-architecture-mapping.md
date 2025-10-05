# 3. 分布式架构映射

## 目录

- [3. 分布式架构映射](#3-分布式架构映射)
  - [目录](#目录)
  - [3.1. 分布式 CSP 模型](#31-分布式-csp-模型)
    - [3.1.1. 进程网络拓扑](#311-进程网络拓扑)
    - [3.1.2. 通信模式](#312-通信模式)
    - [3.1.3. 故障模型](#313-故障模型)
  - [3.2. OTLP 分布式架构](#32-otlp-分布式架构)
    - [3.2.1. 三层架构](#321-三层架构)
    - [3.2.2. 数据流路径](#322-数据流路径)
    - [3.2.3. 组件交互](#323-组件交互)
  - [3.3. CSP-OTLP 架构映射](#33-csp-otlp-架构映射)
    - [3.3.1. 边缘层映射](#331-边缘层映射)
    - [3.3.2. 区域层映射](#332-区域层映射)
    - [3.3.3. 中心层映射](#333-中心层映射)
  - [3.4. 分布式一致性](#34-分布式一致性)
    - [3.4.1. 最终一致性](#341-最终一致性)
    - [3.4.2. 因果一致性](#342-因果一致性)
    - [3.4.3. 顺序一致性](#343-顺序一致性)
  - [3.5. 容错与恢复](#35-容错与恢复)
    - [3.5.1. 故障检测](#351-故障检测)
    - [3.5.2. 重试策略](#352-重试策略)
    - [3.5.3. 熔断机制](#353-熔断机制)
  - [3.6. 多租户隔离](#36-多租户隔离)
    - [3.6.1. 租户识别](#361-租户识别)
    - [3.6.2. 数据路由](#362-数据路由)
    - [3.6.3. 资源隔离](#363-资源隔离)
  - [3.7. 总结](#37-总结)

## 3.1. 分布式 CSP 模型

### 3.1.1. 进程网络拓扑

在分布式系统中，CSP 进程分布在多个节点上，通过网络通道进行通信。

**CSP 网络模型**：

```csp
SYSTEM = (P1 || P2 || ... || Pn) \ {internal_channels}

P1 = input?x -> process(x) -> network!result -> P1
P2 = network?data -> store(data) -> P2
```

**拓扑类型**：

1. **星型拓扑**：中心节点与多个边缘节点通信
2. **网状拓扑**：节点间任意通信
3. **层次拓扑**：多层级的树状结构

### 3.1.2. 通信模式

**同步通信**：

```csp
P1 = send!msg -> ack?() -> P1'
P2 = recv?msg -> process(msg) -> ack!() -> P2'
```

**异步通信**：

```csp
P1 = send!msg -> P1'  // 不等待确认
P2 = recv?msg -> process(msg) -> P2'
```

**广播通信**：

```csp
BROADCAST = msg?x -> (out1!x -> SKIP || out2!x -> SKIP || out3!x -> SKIP)
```

### 3.1.3. 故障模型

**进程故障**：

```csp
P = (normal -> P) [] (fail -> STOP)
```

**通道故障**：

```csp
CHANNEL = (send?x -> recv!x -> CHANNEL) [] (fail -> SKIP)
```

## 3.2. OTLP 分布式架构

### 3.2.1. 三层架构

```text
┌───────────────────────────────────────────────────────────┐
│                      应用层 (Application)                  │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│  │ Service A│  │ Service B│  │ Service C│  │ Service D│   │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │
└───────┼─────────────┼─────────────┼─────────────┼─────────┘
        │             │             │             │
        ▼             ▼             ▼             ▼
┌───────────────────────────────────────────────────────────┐
│                  边缘层 (Edge / Agent)                     │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│  │  Agent 1 │  │  Agent 2 │  │  Agent 3 │  │  Agent 4 │   │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │
└───────┼─────────────┼─────────────┼─────────────┼─────────┘
        │             │             │             │
        └──────┬──────┴──────┬──────┴──────┬──────┘
               │             │             │
               ▼             ▼             ▼
┌───────────────────────────────────────────────────────────┐
│                  区域层 (Regional Gateway)                 │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │  Gateway US  │  │  Gateway EU  │  │  Gateway APAC│     │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘     │
└─────────┼──────────────────┼──────────────────┼───────────┘
          │                  │                  │
          └────────┬─────────┴─────────┬────────┘
                   │                   │
                   ▼                   ▼
┌─────────────────────────────────────────────────────────────┐
│                  中心层 (Central Backend)                    │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │  Jaeger  │  │Prometheus│  │   Loki   │  │  Phlare  │     │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘     │
└─────────────────────────────────────────────────────────────┘
```

### 3.2.2. 数据流路径

**正常路径**：

```text
Application → SDK → Agent → Gateway → Backend
```

**降级路径**：

```text
Application → SDK → Gateway (bypass Agent)
Application → SDK → Local Storage → Batch Upload
```

### 3.2.3. 组件交互

**OTLP/gRPC 双向流**：

```go
// Agent 接收来自 SDK 的数据
func (a *Agent) Export(stream otlpgrpc.ExportTraceServiceServer) error {
    ctx, span := tracer.Start(stream.Context(), "agent.export")
    defer span.End()
    
    for {
        req, err := stream.Recv()
        if err == io.EOF {
            return stream.SendAndClose(&otlpgrpc.ExportTraceServiceResponse{})
        }
        if err != nil {
            return err
        }
        
        // 处理并转发到 Gateway
        a.forwardToGateway(ctx, req)
    }
}
```

## 3.3. CSP-OTLP 架构映射

### 3.3.1. 边缘层映射

**CSP 模型**：

```csp
EDGE_AGENT = app_input?data -> 
             process(data) -> 
             gateway_output!data -> 
             EDGE_AGENT
```

**Go 实现**：

```go
type EdgeAgent struct {
    appInput      <-chan OTLPData
    gatewayOutput chan<- OTLPData
    processor     Processor
}

func (a *EdgeAgent) Start(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "edge_agent")
    defer span.End()
    
    for {
        select {
        case data := <-a.appInput:
            // 处理数据
            processedData := a.processor.Process(ctx, data)
            
            // 转发到 Gateway
            select {
            case a.gatewayOutput <- processedData:
                span.AddEvent("forwarded_to_gateway")
            case <-ctx.Done():
                return
            default:
                // 背压处理
                span.AddEvent("gateway_channel_full")
                a.handleBackpressure(ctx, processedData)
            }
            
        case <-ctx.Done():
            return
        }
    }
}
```

### 3.3.2. 区域层映射

**CSP 模型**：

```csp
GATEWAY = (agent1_input?data -> GATEWAY_PROCESS(data))
       [] (agent2_input?data -> GATEWAY_PROCESS(data))
       [] (agentN_input?data -> GATEWAY_PROCESS(data))

GATEWAY_PROCESS(data) = 
    aggregate(data) -> 
    backend_output!data -> 
    GATEWAY
```

**Go 实现**：

```go
type RegionalGateway struct {
    agentInputs   []<-chan OTLPData
    backendOutput chan<- OTLPData
    aggregator    *Aggregator
}

func (g *RegionalGateway) Start(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "regional_gateway")
    defer span.End()
    
    // 使用 reflect.Select 实现多路复用
    cases := make([]reflect.SelectCase, len(g.agentInputs)+1)
    
    for i, input := range g.agentInputs {
        cases[i] = reflect.SelectCase{
            Dir:  reflect.SelectRecv,
            Chan: reflect.ValueOf(input),
        }
    }
    
    cases[len(g.agentInputs)] = reflect.SelectCase{
        Dir:  reflect.SelectRecv,
        Chan: reflect.ValueOf(ctx.Done()),
    }
    
    for {
        chosen, value, ok := reflect.Select(cases)
        
        if chosen == len(g.agentInputs) {
            // context cancelled
            return
        }
        
        if ok {
            data := value.Interface().(OTLPData)
            span.AddEvent("received_from_agent", trace.WithAttributes(
                attribute.Int("agent_id", chosen),
            ))
            
            // 聚合并转发
            aggregatedData := g.aggregator.Aggregate(ctx, data)
            g.backendOutput <- aggregatedData
        }
    }
}
```

### 3.3.3. 中心层映射

**CSP 模型**：

```csp
BACKEND = gateway_input?data -> 
          store(data) -> 
          index(data) -> 
          BACKEND
```

**Go 实现**：

```go
type CentralBackend struct {
    gatewayInput <-chan OTLPData
    storage      Storage
    indexer      Indexer
}

func (b *CentralBackend) Start(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "central_backend")
    defer span.End()
    
    for {
        select {
        case data := <-b.gatewayInput:
            // 存储数据
            if err := b.storage.Store(ctx, data); err != nil {
                span.RecordError(err)
                continue
            }
            
            // 索引数据
            if err := b.indexer.Index(ctx, data); err != nil {
                span.RecordError(err)
            }
            
            span.AddEvent("data_stored_and_indexed")
            
        case <-ctx.Done():
            return
        }
    }
}
```

## 3.4. 分布式一致性

### 3.4.1. 最终一致性

在分布式 OTLP 系统中，遥测数据通常采用最终一致性模型。

**CSP 模型**：

```csp
EVENTUAL_CONSISTENCY = 
    write!data -> 
    (propagate1!data || propagate2!data || propagate3!data) -> 
    EVENTUALLY_CONSISTENT
```

**Go 实现**：

```go
type EventualConsistencyStore struct {
    replicas []ReplicaStore
}

func (s *EventualConsistencyStore) Store(ctx context.Context, data OTLPData) error {
    ctx, span := tracer.Start(ctx, "eventual_consistency_store")
    defer span.End()
    
    var wg sync.WaitGroup
    errChan := make(chan error, len(s.replicas))
    
    // 异步写入所有副本
    for i, replica := range s.replicas {
        wg.Add(1)
        go func(id int, r ReplicaStore) {
            defer wg.Done()
            
            ctx, span := tracer.Start(ctx, "replica_write")
            span.SetAttributes(attribute.Int("replica.id", id))
            defer span.End()
            
            if err := r.Write(ctx, data); err != nil {
                span.RecordError(err)
                errChan <- err
            }
        }(i, replica)
    }
    
    wg.Wait()
    close(errChan)
    
    // 只要有一个副本成功即可
    errorCount := 0
    for err := range errChan {
        errorCount++
        if errorCount == len(s.replicas) {
            return fmt.Errorf("all replicas failed")
        }
    }
    
    return nil
}
```

### 3.4.2. 因果一致性

通过 `trace_id` 和 `span_id` 维护因果关系。

**CSP 模型**：

```csp
CAUSAL_ORDER = 
    event1!{trace_id, span_id_1, parent_id=nil} -> 
    event2!{trace_id, span_id_2, parent_id=span_id_1} -> 
    event3!{trace_id, span_id_3, parent_id=span_id_2} -> 
    CAUSAL_ORDER
```

**Go 实现**：

```go
type CausalConsistencyValidator struct {
    spanGraph map[string]map[string]bool // trace_id -> span_id -> exists
    mu        sync.RWMutex
}

func (v *CausalConsistencyValidator) Validate(ctx context.Context, span Span) error {
    ctx, traceSpan := tracer.Start(ctx, "causal_consistency_validate")
    defer traceSpan.End()
    
    v.mu.Lock()
    defer v.mu.Unlock()
    
    traceID := span.TraceID
    spanID := span.SpanID
    parentID := span.ParentSpanID
    
    // 初始化 trace 图
    if v.spanGraph[traceID] == nil {
        v.spanGraph[traceID] = make(map[string]bool)
    }
    
    // 验证父 span 是否存在（如果有父 span）
    if parentID != "" && !v.spanGraph[traceID][parentID] {
        err := fmt.Errorf("causal consistency violation: parent span %s not found", parentID)
        traceSpan.RecordError(err)
        return err
    }
    
    // 记录当前 span
    v.spanGraph[traceID][spanID] = true
    
    traceSpan.AddEvent("causal_consistency_validated")
    return nil
}
```

### 3.4.3. 顺序一致性

在某些场景下（如日志），需要保证事件的顺序。

**Go 实现**：

```go
type SequentialConsistencyBuffer struct {
    buffer   []OTLPData
    sequence uint64
    mu       sync.Mutex
}

func (b *SequentialConsistencyBuffer) Append(ctx context.Context, data OTLPData) error {
    ctx, span := tracer.Start(ctx, "sequential_append")
    defer span.End()
    
    b.mu.Lock()
    defer b.mu.Unlock()
    
    // 分配序列号
    b.sequence++
    data.Sequence = b.sequence
    
    b.buffer = append(b.buffer, data)
    
    span.SetAttributes(
        attribute.Int64("sequence", int64(b.sequence)),
    )
    
    return nil
}
```

## 3.5. 容错与恢复

### 3.5.1. 故障检测

**心跳机制**：

```go
type HealthChecker struct {
    targets  []string
    interval time.Duration
}

func (h *HealthChecker) Start(ctx context.Context) {
    ctx, span := tracer.Start(ctx, "health_checker")
    defer span.End()
    
    ticker := time.NewTicker(h.interval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            for _, target := range h.targets {
                go h.checkHealth(ctx, target)
            }
            
        case <-ctx.Done():
            return
        }
    }
}

func (h *HealthChecker) checkHealth(ctx context.Context, target string) {
    ctx, span := tracer.Start(ctx, "check_health")
    span.SetAttributes(attribute.String("target", target))
    defer span.End()
    
    ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
    defer cancel()
    
    // 发送健康检查请求
    if err := h.ping(ctx, target); err != nil {
        span.RecordError(err)
        span.SetAttributes(attribute.Bool("healthy", false))
        // 触发故障转移
        h.handleFailure(ctx, target)
    } else {
        span.SetAttributes(attribute.Bool("healthy", true))
    }
}
```

### 3.5.2. 重试策略

**指数退避重试**：

```go
type ExponentialBackoff struct {
    initialDelay time.Duration
    maxDelay     time.Duration
    multiplier   float64
    maxRetries   int
}

func (e *ExponentialBackoff) Retry(ctx context.Context, fn func() error) error {
    ctx, span := tracer.Start(ctx, "exponential_backoff_retry")
    defer span.End()
    
    delay := e.initialDelay
    
    for attempt := 0; attempt < e.maxRetries; attempt++ {
        err := fn()
        if err == nil {
            span.SetAttributes(attribute.Int("attempts", attempt+1))
            return nil
        }
        
        span.AddEvent("retry_attempt_failed", trace.WithAttributes(
            attribute.Int("attempt", attempt+1),
            attribute.String("error", err.Error()),
        ))
        
        // 等待后重试
        select {
        case <-time.After(delay):
            delay = time.Duration(float64(delay) * e.multiplier)
            if delay > e.maxDelay {
                delay = e.maxDelay
            }
        case <-ctx.Done():
            return ctx.Err()
        }
    }
    
    err := fmt.Errorf("max retries exceeded")
    span.RecordError(err)
    return err
}
```

### 3.5.3. 熔断机制

**熔断器实现**：

```go
type CircuitBreaker struct {
    maxFailures  int
    resetTimeout time.Duration
    
    failures     int
    lastFailTime time.Time
    state        string // "closed", "open", "half-open"
    mu           sync.Mutex
}

func (cb *CircuitBreaker) Call(ctx context.Context, fn func() error) error {
    ctx, span := tracer.Start(ctx, "circuit_breaker_call")
    defer span.End()
    
    cb.mu.Lock()
    
    // 检查是否需要从 open 转换到 half-open
    if cb.state == "open" && time.Since(cb.lastFailTime) > cb.resetTimeout {
        cb.state = "half-open"
        cb.failures = 0
    }
    
    // 如果熔断器打开，直接返回错误
    if cb.state == "open" {
        cb.mu.Unlock()
        err := fmt.Errorf("circuit breaker is open")
        span.RecordError(err)
        span.SetAttributes(attribute.String("circuit_breaker.state", "open"))
        return err
    }
    
    cb.mu.Unlock()
    
    // 执行函数
    err := fn()
    
    cb.mu.Lock()
    defer cb.mu.Unlock()
    
    if err != nil {
        cb.failures++
        cb.lastFailTime = time.Now()
        
        if cb.failures >= cb.maxFailures {
            cb.state = "open"
            span.AddEvent("circuit_breaker_opened")
        }
        
        span.RecordError(err)
    } else {
        // 成功，重置失败计数
        if cb.state == "half-open" {
            cb.state = "closed"
            span.AddEvent("circuit_breaker_closed")
        }
        cb.failures = 0
    }
    
    span.SetAttributes(
        attribute.String("circuit_breaker.state", cb.state),
        attribute.Int("circuit_breaker.failures", cb.failures),
    )
    
    return err
}
```

## 3.6. 多租户隔离

### 3.6.1. 租户识别

**通过 Resource 属性识别租户**：

```go
func extractTenantID(resource Resource) string {
    for _, attr := range resource.Attributes {
        if attr.Key == "tenant.id" {
            return attr.Value.AsString()
        }
    }
    return "default"
}
```

### 3.6.2. 数据路由

**基于租户的路由**：

```go
type TenantRouter struct {
    routes map[string]chan<- OTLPData
}

func (r *TenantRouter) Route(ctx context.Context, data OTLPData) error {
    ctx, span := tracer.Start(ctx, "tenant_router")
    defer span.End()
    
    tenantID := extractTenantID(data.Resource)
    
    span.SetAttributes(attribute.String("tenant.id", tenantID))
    
    output, exists := r.routes[tenantID]
    if !exists {
        output = r.routes["default"]
    }
    
    select {
    case output <- data:
        return nil
    case <-ctx.Done():
        return ctx.Err()
    default:
        return fmt.Errorf("output channel full for tenant %s", tenantID)
    }
}
```

### 3.6.3. 资源隔离

**租户级别的资源配额**：

```go
type TenantQuota struct {
    maxSpansPerSecond int64
    maxBytesPerSecond int64
    
    currentSpans int64
    currentBytes int64
    
    resetTime time.Time
    mu        sync.Mutex
}

func (q *TenantQuota) CheckAndConsume(ctx context.Context, data OTLPData) error {
    ctx, span := tracer.Start(ctx, "tenant_quota_check")
    defer span.End()
    
    q.mu.Lock()
    defer q.mu.Unlock()
    
    // 重置计数器（每秒）
    if time.Since(q.resetTime) > time.Second {
        q.currentSpans = 0
        q.currentBytes = 0
        q.resetTime = time.Now()
    }
    
    spanCount := int64(len(data.Spans))
    byteCount := int64(data.Size())
    
    // 检查配额
    if q.currentSpans+spanCount > q.maxSpansPerSecond {
        err := fmt.Errorf("span quota exceeded")
        span.RecordError(err)
        return err
    }
    
    if q.currentBytes+byteCount > q.maxBytesPerSecond {
        err := fmt.Errorf("byte quota exceeded")
        span.RecordError(err)
        return err
    }
    
    // 消费配额
    q.currentSpans += spanCount
    q.currentBytes += byteCount
    
    span.SetAttributes(
        attribute.Int64("quota.current_spans", q.currentSpans),
        attribute.Int64("quota.current_bytes", q.currentBytes),
    )
    
    return nil
}
```

## 3.7. 总结

分布式 CSP-OTLP 架构映射提供了一个清晰的框架来理解和实现大规模可观测性系统：

1. **层次化架构**：边缘、区域、中心三层架构对应 CSP 的进程网络拓扑
2. **一致性模型**：根据不同的数据类型选择合适的一致性保证
3. **容错机制**：通过健康检查、重试、熔断等机制保证系统可靠性
4. **多租户支持**：通过租户识别、路由和配额实现资源隔离

这种映射不仅有助于系统设计，也为形式化验证和性能优化提供了理论基础。

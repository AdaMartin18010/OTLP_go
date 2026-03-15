# OpenTelemetry最佳实践完整清单

> **实践指南**: 生产级OpenTelemetry部署与运维  
> **最后更新**: 2025年10月8日

---

## 目录

- [OpenTelemetry最佳实践完整清单](#opentelemetry最佳实践完整清单)
  - [目录](#目录)
  - [1. SDK最佳实践](#1-sdk最佳实践)
    - [1.1 初始化配置](#11-初始化配置)
    - [1.3 错误处理](#13-错误处理)
    - [2.2 属性设置](#22-属性设置)
    - [3.2 配置管理](#32-配置管理)
    - [3.3 资源管理](#33-资源管理)
  - [4. 采样策略](#4-采样策略)
    - [4.1 Head-based采样](#41-head-based采样)
    - [4.2 Tail-based采样](#42-tail-based采样)
    - [4.3 智能采样](#43-智能采样)
  - [5. 安全最佳实践](#5-安全最佳实践)
    - [5.1 数据保护](#51-数据保护)
    - [5.2 访问控制](#52-访问控制)
    - [5.3 合规性](#53-合规性)
  - [6. 监控与告警](#6-监控与告警)
    - [6.1 关键指标](#61-关键指标)
    - [6.2 告警规则](#62-告警规则)
    - [6.3 SLO定义](#63-slo定义)
  - [7. 成本优化](#7-成本优化)
    - [7.1 数据量控制](#71-数据量控制)
    - [7.2 资源优化](#72-资源优化)
    - [7.3 存储优化](#73-存储优化)
  - [8. 运维实践](#8-运维实践)
    - [8.1 部署流程](#81-部署流程)
    - [8.2 升级策略](#82-升级策略)
    - [8.3 故障恢复](#83-故障恢复)
  - [9. 团队协作](#9-团队协作)
    - [9.1 文档规范](#91-文档规范)
    - [9.2 变更管理](#92-变更管理)
    - [9.3 知识共享](#93-知识共享)
  - [10. 检查清单](#10-检查清单)
    - [10.1 上线前检查](#101-上线前检查)
    - [10.2 日常运维检查](#102-日常运维检查)
    - [10.3 优化检查](#103-优化检查)

---

## 1. SDK最佳实践

### 1.1 初始化配置

```text
✅ SDK初始化最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 使用环境变量配置 ⭐⭐⭐⭐⭐
   - OTEL_SERVICE_NAME
   - OTEL_EXPORTER_OTLP_ENDPOINT
   - OTEL_RESOURCE_ATTRIBUTES
   - OTEL_TRACES_SAMPLER

2. 延迟初始化 ⭐⭐⭐⭐
    ```go
    func init() {
        // ❌ 避免在init中初始化
    }
    
    func main() {
        // ✅ 在main中初始化
        tp := initTracer()
        defer tp.Shutdown(context.Background())
    }
    ```

3. 资源检测 ⭐⭐⭐⭐⭐
    ```go
    import "go.opentelemetry.io/contrib/detectors/aws/ec2"
    
    detector := resource.New(
        context.Background(),
        resource.WithDetectors(
            ec2.NewResourceDetector(),
        ),
        resource.WithFromEnv(),
    )
    ```

4. 批处理配置 ⭐⭐⭐⭐⭐
    ```go
    trace.WithBatcher(exporter,
        trace.WithMaxExportBatchSize(512),
        trace.WithBatchTimeout(5*time.Second),
        trace.WithMaxQueueSize(2048),
    )
    ```

5. 优雅关闭 ⭐⭐⭐⭐⭐
    ```go
    // 监听信号
    sigChan := make(chan os.Signal, 1)
    signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)
    
    <-sigChan
    
    // 超时上下文
    ctx, cancel := context.WithTimeout(
        context.Background(), 
        10*time.Second,
    )
    defer cancel()
    
    // 关闭TracerProvider
    tp.Shutdown(ctx)
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

### 1.2 性能优化

```text
✅ SDK性能优化清单

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 异步处理 ⭐⭐⭐⭐⭐
   ✅ 使用BatchSpanProcessor (异步)
   ❌ 避免SimpleSpanProcessor (同步)

2. 限制属性数量 ⭐⭐⭐⭐
    ```go
    trace.WithSpanLimits(trace.SpanLimits{
        AttributeCountLimit:      128,
        EventCountLimit:          128,
        LinkCountLimit:           128,
        AttributePerEventLimit:   128,
        AttributePerLinkLimit:    128,
    })
    ```

3. 采样率调整 ⭐⭐⭐⭐⭐
   - 开发环境: 100%
   - 测试环境: 50%
   - 生产环境: 1-10%
   - 高流量服务: 0.1-1%

4. 连接池复用 ⭐⭐⭐⭐
    ```go
    // gRPC连接复用
    conn, _ := grpc.Dial(endpoint,
        grpc.WithBlock(),
        grpc.WithKeepaliveParams(keepalive.ClientParameters{
            Time:                10 * time.Second,
            Timeout:             3 * time.Second,
            PermitWithoutStream: true,
        }),
    )
    ```

5. 避免热路径 ⭐⭐⭐⭐⭐
   ```go
   // ❌ 避免
   for i := 0; i < 1000000; i++ {
       _, span := tracer.Start(ctx, "loop-span")
       span.End()
   }
   
   // ✅ 推荐
   _, span := tracer.Start(ctx, "batch-operation")
   defer span.End()
   for i := 0; i < 1000000; i++ {
       // 业务逻辑
   }
   ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

### 1.3 错误处理

```text
✅ 错误处理最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 记录错误 ⭐⭐⭐⭐⭐
    ```go
    if err != nil {
        span.RecordError(err)
        span.SetStatus(codes.Error, err.Error())
        return err
    }
    ```

2. 错误分类 ⭐⭐⭐⭐
    ```go
    span.SetAttributes(
        attribute.String("error.type", "validation"),
        attribute.String("error.code", "INVALID_INPUT"),
    )
    ```

3. 避免敏感信息 ⭐⭐⭐⭐⭐
    ```go
    // ❌ 避免
    span.SetStatus(codes.Error, "password invalid: "+password)
    
    // ✅ 推荐
    span.SetStatus(codes.Error, "authentication failed")
    ```

4. 重试机制 ⭐⭐⭐⭐
    ```go
    exporter, err := otlptracegrpc.New(ctx,
        otlptracegrpc.WithRetry(otlptracegrpc.RetryConfig{
            Enabled:         true,
            InitialInterval: 5 * time.Second,
            MaxInterval:     30 * time.Second,
            MaxElapsedTime:  5 * time.Minute,
        }),
    )
    ```

5. 降级策略 ⭐⭐⭐⭐
   - 导出失败不影响业务
   - 本地缓存队列
   - 断路器模式

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

---

## 2. Instrumentation最佳实践

### 2.1 Span命名

```text
✅ Span命名规范

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 命名模式 ⭐⭐⭐⭐⭐
   
   HTTP:
   ✅ GET /api/users
   ✅ POST /api/orders
   ❌ /api/users?id=123
   
   gRPC:
   ✅ UserService.GetUser
   ✅ OrderService.CreateOrder
   
   Database:
   ✅ SELECT users
   ✅ INSERT INTO orders
   
   Message Queue:
   ✅ kafka.produce order-topic
   ✅ kafka.consume payment-topic

2. 使用SpanKind ⭐⭐⭐⭐⭐
    ```go
    // HTTP Server
    trace.WithSpanKind(trace.SpanKindServer)
    
    // HTTP Client
    trace.WithSpanKind(trace.SpanKindClient)
    
    // Message Producer
    trace.WithSpanKind(trace.SpanKindProducer)
    
    // Message Consumer
    trace.WithSpanKind(trace.SpanKindConsumer)
    
    // Internal
    trace.WithSpanKind(trace.SpanKindInternal)
    ```

3. 避免高基数 ⭐⭐⭐⭐⭐
    ```go
    // ❌ 避免
    tracer.Start(ctx, "get-user-"+userID)
    
    // ✅ 推荐
    _, span := tracer.Start(ctx, "get-user")
    span.SetAttributes(attribute.String("user.id", userID))
    ```

4. 描述性命名 ⭐⭐⭐⭐
   ✅ process-payment
   ✅ validate-order
   ✅ send-notification
   ❌ func1
   ❌ handler
   ❌ do-something

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 2.2 属性设置

```text
✅ 属性设置最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 遵循语义约定 ⭐⭐⭐⭐⭐
    ```go
    // HTTP
    span.SetAttributes(
        semconv.HTTPMethodKey.String("GET"),
        semconv.HTTPURLKey.String(url),
        semconv.HTTPStatusCodeKey.Int(200),
    )
    
    // Database
    span.SetAttributes(
        semconv.DBSystemKey.String("postgresql"),
        semconv.DBNameKey.String("mydb"),
        semconv.DBStatementKey.String(query),
    )
    ```

2. 业务属性 ⭐⭐⭐⭐
    ```go
    span.SetAttributes(
        attribute.String("user.id", userID),
        attribute.String("order.id", orderID),
        attribute.Float64("order.amount", amount),
        attribute.String("payment.method", "credit_card"),
    )
    ```

3. 属性限制 ⭐⭐⭐⭐
   - 单个Span: < 128个属性
   - 属性值长度: < 1KB
   - 避免大对象JSON序列化

4. 敏感数据脱敏 ⭐⭐⭐⭐⭐
    ```go
    // ❌ 避免
    span.SetAttributes(
        attribute.String("credit_card", "4111111111111111"),
        attribute.String("password", "secret123"),
    )
    
    // ✅ 推荐
    span.SetAttributes(
        attribute.String("credit_card", "****1111"),
        attribute.Bool("authenticated", true),
    )
    ```

5. 条件属性 ⭐⭐⭐
    ```go
    if debugMode {
        span.SetAttributes(
            attribute.String("debug.query", query),
            attribute.String("debug.stacktrace", stack),
        )
    }
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

### 2.3 Context传播

```text
✅ Context传播最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. HTTP传播 ⭐⭐⭐⭐⭐
    ```go
    // Client
    req, _ := http.NewRequestWithContext(ctx, "GET", url, nil)
    otel.GetTextMapPropagator().Inject(ctx, 
        propagation.HeaderCarrier(req.Header))
    
    // Server
    ctx := otel.GetTextMapPropagator().Extract(
        r.Context(),
        propagation.HeaderCarrier(r.Header),
    )
    ```

2. gRPC传播 ⭐⭐⭐⭐⭐
    ```go
    // 自动传播 (使用Interceptor)
    otelgrpc.UnaryClientInterceptor()
    otelgrpc.UnaryServerInterceptor()
    ```

3. 消息队列传播 ⭐⭐⭐⭐⭐
    ```go
    // Kafka Producer
    carrier := propagation.MapCarrier{}
    otel.GetTextMapPropagator().Inject(ctx, carrier)
    
    headers := []kafka.Header{}
    for k, v := range carrier {
        headers = append(headers, kafka.Header{
            Key: k, Value: []byte(v),
        })
    }
    
    // Kafka Consumer
    carrier := propagation.MapCarrier{}
    for _, h := range message.Headers {
        carrier[h.Key] = string(h.Value)
    }
    ctx := otel.GetTextMapPropagator().Extract(
        context.Background(), carrier,
    )
    ```

4. Goroutine传播 ⭐⭐⭐⭐
    ```go
    go func() {
        // ✅ 传递父Context
        ctx, span := tracer.Start(parentCtx, "async-task")
        defer span.End()
        
        // 业务逻辑
    }()
    ```

5. Baggage使用 ⭐⭐⭐
    ```go
    // 设置
    ctx = baggage.ContextWithValues(ctx,
        baggage.String("user.id", userID),
        baggage.String("tenant.id", tenantID),
    )
    
    // 读取
    userID := baggage.Value(ctx, "user.id").AsString()
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

---

## 3. Collector最佳实践

### 3.1 部署架构

```text
✅ Collector部署架构

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Agent模式 ⭐⭐⭐⭐⭐
   
   场景: 节点级数据收集
   
   ┌─────────────────────────────────────┐
   │ Node 1                              │
   │  ┌───────┐  ┌───────┐  ┌────────┐   │
   │  │App 1  │  │App 2  │  │App 3   │   │
   │  └───┬───┘  └───┬───┘  └───┬────┘   │
   │      └──────────┼──────────┘        │
   │                 │                   │
   │          ┌──────▼───────┐           │
   │          │   Collector  │           │
   │          │   (Agent)    │           │
   │          └──────┬───────┘           │
   └─────────────────┼───────────────────┘
                     │
              ┌──────▼────────┐
              │   Gateway     │
              │   Collector   │
              └───────────────┘
   
   优点:
   - 低延迟
   - 本地缓存
   - 资源隔离
   
   配置:
   - CPU: 100-200m
   - Memory: 128-256Mi
   - Replicas: 每节点1个

2. Gateway模式 ⭐⭐⭐⭐⭐
   
   场景: 集中处理
   
   ┌─────────┐  ┌─────────┐   ┌─────────┐
   │ App 1   │  │ App 2   │   │ App 3   │
   └────┬────┘  └────┬────┘   └────┬────┘
        └────────────┼─────────────┘
                     │
          ┌──────────▼──────────┐
          │   Gateway Collector │
          │   (3 replicas)      │
          └──────────┬──────────┘
                     │
          ┌──────────▼──────────┐
          │   Backends          │
          │ Jaeger/Prometheus   │
          └─────────────────────┘
   
   优点:
   - 集中管理
   - 高级处理
   - 降低Backend压力
   
   配置:
   - CPU: 1-2 cores
   - Memory: 2-4Gi
   - Replicas: 3+

3. 混合模式 ⭐⭐⭐⭐⭐ (推荐)
   
   Agent + Gateway
   
   优点:
   - 结合两者优势
   - 灵活扩展
   - 高可用

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 3.2 配置管理

```text
✅ Collector配置最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 模块化配置 ⭐⭐⭐⭐⭐
    ```yaml
    # base-config.yaml
    receivers:
        otlp:
        protocols:
            grpc:
            http:
    
    # production.yaml
    extends: base-config.yaml
    processors:
        batch:
        timeout: 10s
    ```

2. 环境变量 ⭐⭐⭐⭐
    ```yaml
    exporters:
        otlp:
        endpoint: ${OTLP_ENDPOINT}
        headers:
            api-key: ${API_KEY}
    ```

3. 配置验证 ⭐⭐⭐⭐⭐
    ```bash
    # 部署前验证
    otelcol validate --config=/etc/otelcol/config.yaml
    ```

4. 版本控制 ⭐⭐⭐⭐⭐
   - Git管理配置
   - 变更审查
   - 回滚能力

5. 热重载 ⭐⭐⭐⭐
    ```bash
    # 发送SIGHUP信号重载配置
    kill -HUP <collector-pid>
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 3.3 资源管理

```text
✅ Collector资源管理

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 内存限制 ⭐⭐⭐⭐⭐
    ```yaml
    processors:
        memory_limiter:
        check_interval: 1s
        limit_mib: 512
        spike_limit_mib: 128
    
    # 配置顺序: memory_limiter必须第一个
    service:
        pipelines:
        traces:
            processors: [memory_limiter, batch]
    ```

2. 批处理优化 ⭐⭐⭐⭐⭐
    ```yaml
    processors:
        batch:
        timeout: 10s
        send_batch_size: 1024
        send_batch_max_size: 2048
    ```

3. 队列配置 ⭐⭐⭐⭐
    ```yaml
    exporters:
        otlp:
        sending_queue:
            enabled: true
            num_consumers: 10
            queue_size: 5000
    ```

4. 资源请求 ⭐⭐⭐⭐⭐
    ```yaml
    # Kubernetes
    resources:
        requests:
        cpu: 200m
        memory: 256Mi
        limits:
        cpu: 1000m
        memory: 512Mi
    ```

5. 自动扩缩容 ⭐⭐⭐⭐
    ```yaml
    # HPA
    metrics:
    - type: Resource
        resource:
        name: cpu
        target:
            type: Utilization
            averageUtilization: 70
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 4. 采样策略

### 4.1 Head-based采样

```text
✅ Head-based采样最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. TraceID比率采样 ⭐⭐⭐⭐⭐
    ```go
    // SDK配置
    trace.WithSampler(trace.TraceIDRatioBased(0.1)) // 10%
    ```
    
    适用场景:
    - 高流量服务
    - 均匀采样需求
    - 简单场景

2. 父级采样 ⭐⭐⭐⭐
    ```go
    trace.WithSampler(trace.ParentBased(
        trace.TraceIDRatioBased(0.1),
    ))
    ```
    
    优点:
    - 保持Trace完整性
    - 跨服务一致性

3. 环境变量配置 ⭐⭐⭐⭐
    ```bash
    # 10%采样率
    export OTEL_TRACES_SAMPLER=traceidratio
    export OTEL_TRACES_SAMPLER_ARG=0.1
    ```

4. 分层采样 ⭐⭐⭐⭐
   - 前端: 1%
   - API网关: 10%
   - 核心服务: 50%
   - 数据库: 100% (错误)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.2 Tail-based采样

```text
✅ Tail-based采样最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 基于策略采样 ⭐⭐⭐⭐⭐
    ```yaml
    processors:
        tail_sampling:
        decision_wait: 10s
        num_traces: 100
        expected_new_traces_per_sec: 10
        policies:
            # 保留所有错误
            - name: errors
            type: status_code
            status_code:
                status_codes: [ERROR]
            
            # 保留慢请求 (>1s)
            - name: slow-requests
            type: latency
            latency:
                threshold_ms: 1000
            
            # 保留特定服务
            - name: critical-service
            type: string_attribute
            string_attribute:
                key: service.name
                values: [payment-service]
            
            # 随机采样10%
            - name: random-10
            type: probabilistic
            probabilistic:
                sampling_percentage: 10
    ```

2. 组合策略 ⭐⭐⭐⭐
   - OR逻辑: 满足任一条件保留
   - AND逻辑: 满足所有条件保留
   
    ```yaml
    policies:
        - name: error-or-slow
        type: and
        and:
            and_sub_policy:
            - name: errors
                type: status_code
            - name: slow
                type: latency
    ```

3. 性能考虑 ⭐⭐⭐⭐
   - decision_wait: 根据Trace持续时间调整
   - num_traces: 根据内存限制调整
   - 仅Gateway Collector使用

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 4.3 智能采样

```text
✅ 智能采样策略

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 自适应采样 ⭐⭐⭐⭐⭐
   
   动态调整采样率:
   - 低流量: 100%
   - 中流量: 10%
   - 高流量: 1%
   - 超高流量: 0.1%

2. 业务优先级 ⭐⭐⭐⭐
    ```yaml
    # 高价值交易
    - name: high-value-orders
        type: numeric_attribute
        numeric_attribute:
        key: order.amount
        min_value: 1000
    ```

3. 用户采样 ⭐⭐⭐
    ```yaml
    # VIP用户
    - name: vip-users
        type: string_attribute
        string_attribute:
        key: user.tier
        values: [vip, premium]
    ```

4. 异常检测 ⭐⭐⭐⭐
   - 错误率突增: 100%采样
   - 延迟异常: 100%采样
   - 正常情况: 1%采样

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 5. 安全最佳实践

### 5.1 数据保护

```text
✅ 数据保护最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. TLS加密 ⭐⭐⭐⭐⭐
   - SDK → Collector: TLS 1.3
   - Collector → Backend: TLS 1.3
   - mTLS双向认证 (生产环境)

2. 敏感数据脱敏 ⭐⭐⭐⭐⭐
    ```yaml
    processors:
        attributes:
        actions:
            - key: password
            action: delete
            - key: credit_card
            action: delete
            - key: ssn
            action: delete
    ```

3. PII删除 ⭐⭐⭐⭐⭐
    ```yaml
    processors:
        attributes:
        actions:
            - key: user.email
            action: hash
            - key: user.phone
            action: delete
            - key: user.address
            action: delete
    ```

4. 数据最小化 ⭐⭐⭐⭐
   - 只收集必要数据
   - 限制属性数量
   - 定期清理

5. 加密存储 ⭐⭐⭐⭐
   - Backend存储加密
   - 备份加密
   - 密钥管理 (KMS/Vault)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.2 访问控制

```text
✅ 访问控制最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 认证 ⭐⭐⭐⭐⭐
   - API Key
   - OAuth2
   - mTLS客户端证书

2. 授权 ⭐⭐⭐⭐⭐
   - RBAC (基于角色)
   - 最小权限原则
   - 定期审查

3. 网络隔离 ⭐⭐⭐⭐⭐
   - 私有网络
   - 防火墙规则
   - Network Policy (K8s)

4. 审计日志 ⭐⭐⭐⭐⭐
   - 记录所有访问
   - 不可篡改
   - 定期审查

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 5.3 合规性

```text
✅ 合规性最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. GDPR合规 ⭐⭐⭐⭐⭐
   □ 数据最小化
   □ 用户同意
   □ 数据可携权
   □ 删除权
   □ 数据保留策略

2. 数据保留 ⭐⭐⭐⭐⭐
   - Traces: 7-30天
   - Metrics: 30-90天
   - Logs: 7-30天
   - 审计日志: 7年

3. 数据出境 ⭐⭐⭐⭐
   - 数据本地化
   - 跨境传输协议
   - SCCs (标准合同条款)

4. 定期审计 ⭐⭐⭐⭐
   - 季度安全审计
   - 合规性检查
   - 渗透测试

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 6. 监控与告警

### 6.1 关键指标

```text
✅ 关键监控指标

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Collector健康 ⭐⭐⭐⭐⭐
   - otelcol_process_uptime
   - otelcol_process_cpu_seconds
   - otelcol_process_memory_rss

2. 数据流量 ⭐⭐⭐⭐⭐
   - otelcol_receiver_accepted_spans
   - otelcol_receiver_refused_spans
   - otelcol_exporter_sent_spans
   - otelcol_exporter_send_failed_spans

3. 队列状态 ⭐⭐⭐⭐
   - otelcol_exporter_queue_size
   - otelcol_exporter_queue_capacity
   - otelcol_exporter_enqueue_failed_spans

4. 处理延迟 ⭐⭐⭐⭐
   - otelcol_processor_batch_batch_send_size
   - otelcol_processor_batch_timeout_trigger

5. Backend状态 ⭐⭐⭐⭐⭐
   - Jaeger可用性
   - Prometheus可用性
   - 存储使用率

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 6.2 告警规则

```text
✅ 告警规则最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Collector不可用 ⭐⭐⭐⭐⭐
    ```yaml
    - alert: CollectorDown
        expr: up{job="otel-collector"} == 0
        for: 1m
        severity: critical
    ```

2. 数据丢失 ⭐⭐⭐⭐⭐
    ```yaml
    - alert: HighDataLoss
        expr: |
        rate(otelcol_receiver_refused_spans[5m]) > 100
        for: 5m
        severity: warning
    ```

3. 队列满 ⭐⭐⭐⭐
    ```yaml
    - alert: QueueFull
        expr: |
        otelcol_exporter_queue_size / 
        otelcol_exporter_queue_capacity > 0.9
        for: 5m
        severity: warning
    ```

4. 高CPU/内存 ⭐⭐⭐⭐
    ```yaml
    - alert: HighCPU
        expr: |
        rate(otelcol_process_cpu_seconds[5m]) > 0.8
        for: 10m
        severity: warning
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 6.3 SLO定义

```text
✅ SLO定义最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 可用性SLO ⭐⭐⭐⭐⭐
   - 目标: 99.9% (3个9)
   - 测量: uptime / total_time
   - 错误预算: 43.8分钟/月

2. 数据完整性SLO ⭐⭐⭐⭐⭐
   - 目标: 99.99% (4个9)
   - 测量: successful_spans / total_spans
   - 允许丢失: 0.01%

3. 延迟SLO ⭐⭐⭐⭐
   - 目标: P99 < 100ms
   - 测量: export_latency_p99
   - 超出阈值告警

4. SLO监控 ⭐⭐⭐⭐⭐
   - 实时仪表板
   - 错误预算追踪
   - 定期review

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 7. 成本优化

### 7.1 数据量控制

```text
✅ 数据量控制最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 采样优化 ⭐⭐⭐⭐⭐
   - 开发: 100%
   - 测试: 10%
   - 生产: 1-5%
   - 预计节省: 80-95%

2. 属性过滤 ⭐⭐⭐⭐
    ```yaml
    processors:
        attributes:
        actions:
            - key: http.user_agent
            action: delete  # 删除不必要属性
    ```

3. 去重 ⭐⭐⭐⭐
   - 相同Span去重
   - 相同Event去重

4. 压缩 ⭐⭐⭐⭐
    ```yaml
    exporters:
        otlp:
        compression: gzip  # 或snappy
    ```

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 7.2 资源优化

```text
✅ 资源优化最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 右sizing ⭐⭐⭐⭐⭐
   - 基于实际使用调整
   - 定期review
   - HPA自动扩缩容

2. Spot实例 ⭐⭐⭐⭐
   - Agent Collector使用Spot
   - 节省60-90%成本
   - 注意容错

3. 多租户 ⭐⭐⭐⭐
   - 共享Collector
   - 租户隔离
   - 成本分摊

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 7.3 存储优化

```text
✅ 存储优化最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 数据分层 ⭐⭐⭐⭐⭐
   - 热数据: SSD (7天)
   - 温数据: HDD (30天)
   - 冷数据: S3 (1年)

2. 定期清理 ⭐⭐⭐⭐⭐
    ```bash
    # 自动清理7天前数据
    curator --config curator.yml delete_indices
    ```

3. 压缩 ⭐⭐⭐⭐
   - Elasticsearch压缩
   - S3压缩
   - 节省50-70%空间

4. 采样存储 ⭐⭐⭐⭐
   - 保留100%错误Trace
   - 保留1%正常Trace

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 8. 运维实践

### 8.1 部署流程

```text
✅ 部署流程最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 灰度发布 ⭐⭐⭐⭐⭐
   - Canary: 5% → 25% → 50% → 100%
   - 每阶段观察30分钟
   - 异常自动回滚

2. 蓝绿部署 ⭐⭐⭐⭐
   - 零停机
   - 快速回滚
   - 流量切换

3. 部署检查 ⭐⭐⭐⭐⭐
   □ 健康检查通过
   □ 指标正常
   □ 无错误日志
   □ 数据流量正常

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 8.2 升级策略

```text
✅ 升级策略最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 版本管理 ⭐⭐⭐⭐⭐
   - 跟踪上游版本
   - 测试兼容性
   - 记录变更日志

2. 分阶段升级 ⭐⭐⭐⭐⭐
   - 开发环境 → 测试环境 → 生产环境
   - Agent → Gateway → Backend

3. 回滚计划 ⭐⭐⭐⭐⭐
   - 保留旧版本镜像
   - 快速回滚脚本
   - 数据兼容性

4. 升级验证 ⭐⭐⭐⭐
   - 功能测试
   - 性能测试
   - 负载测试

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 8.3 故障恢复

```text
✅ 故障恢复最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 备份策略 ⭐⭐⭐⭐⭐
   - 配置备份 (Git)
   - 数据备份 (每日)
   - 定期恢复演练

2. 高可用 ⭐⭐⭐⭐⭐
   - 多副本 (3+)
   - 跨AZ部署
   - 负载均衡

3. 降级方案 ⭐⭐⭐⭐
   - 关闭非关键功能
   - 增加采样率
   - 本地缓存

4. RTO/RPO ⭐⭐⭐⭐⭐
   - RTO: < 15分钟
   - RPO: < 5分钟

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 9. 团队协作

### 9.1 文档规范

```text
✅ 文档规范最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 架构文档 ⭐⭐⭐⭐⭐
   - 系统架构图
   - 数据流图
   - 组件说明

2. 运维手册 ⭐⭐⭐⭐⭐
   - 部署指南
   - 配置说明
   - 故障排查

3. 开发指南 ⭐⭐⭐⭐
   - SDK使用
   - 最佳实践
   - 示例代码

4. 变更日志 ⭐⭐⭐⭐⭐
   - 版本记录
   - 变更说明
   - 影响评估

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 变更管理

```text
✅ 变更管理最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 变更流程 ⭐⭐⭐⭐⭐
   - 提交变更请求
   - 技术评审
   - 测试验证
   - 审批部署

2. 影响评估 ⭐⭐⭐⭐⭐
   - 范围分析
   - 风险评估
   - 回滚计划

3. 沟通机制 ⭐⭐⭐⭐
   - 提前通知
   - 进度更新
   - 结果反馈

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.3 知识共享

```text
✅ 知识共享最佳实践

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. 技术分享 ⭐⭐⭐⭐
   - 定期分享会
   - 案例分析
   - 经验总结

2. 文档沉淀 ⭐⭐⭐⭐⭐
   - Wiki更新
   - FAQ维护
   - 最佳实践

3. Code Review ⭐⭐⭐⭐⭐
   - 配置审查
   - 代码审查
   - 知识传递

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 10. 检查清单

### 10.1 上线前检查

```text
✅ 上线前完整检查清单

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

□ SDK配置
  □ 正确的服务名称
  □ 合适的采样率
  □ Resource属性完整
  □ 优雅关闭配置

□ Collector配置
  □ 配置验证通过
  □ 资源限制设置
  □ memory_limiter配置
  □ 批处理优化

□ 安全配置
  □ TLS启用
  □ 认证配置
  □ 敏感数据脱敏
  □ 访问控制

□ 监控告警
  □ 关键指标监控
  □ 告警规则配置
  □ 值班机制

□ 文档准备
  □ 架构文档
  □ 运维手册
  □ 故障排查指南

□ 测试验证
  □ 功能测试
  □ 性能测试
  □ 压力测试
  □ 故障恢复演练

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.2 日常运维检查

```text
✅ 日常运维检查清单

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

每日检查:
□ Collector可用性
□ 数据流量正常
□ 队列状态健康
□ 无异常告警
□ 错误日志review

每周检查:
□ 资源使用率
□ 性能指标趋势
□ 告警规则review
□ 配置备份

每月检查:
□ 成本分析
□ 容量规划
□ 安全审计
□ 文档更新

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 10.3 优化检查

```text
✅ 优化检查清单

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

性能优化:
□ 采样率合理
□ 批处理优化
□ 资源配置合理
□ 无性能瓶颈

成本优化:
□ 数据量控制
□ 资源利用率
□ 存储策略
□ 定期清理

质量优化:
□ Trace完整性
□ 属性规范
□ 文档完善
□ 团队培训

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

**文档状态**: ✅ 完成  
**适用场景**: 企业级OpenTelemetry生产部署  
**持续更新**: 根据最新最佳实践持续迭代

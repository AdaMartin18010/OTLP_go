# OTLP 语义验证

## 目录

- [OTLP 语义验证](#otlp-语义验证)
  - [目录](#目录)
  - [1. Trace 完整性验证](#1-trace-完整性验证)
    - [1.1 Span 完整性](#11-span-完整性)
    - [1.2 Trace 树结构验证](#12-trace-树结构验证)
  - [2. 因果关系一致性](#2-因果关系一致性)
    - [2.1 Happens-Before 关系](#21-happens-before-关系)
    - [2.2 因果一致性验证](#22-因果一致性验证)
  - [3. 时间序列正确性](#3-时间序列正确性)
    - [3.1 时钟偏移检测](#31-时钟偏移检测)
    - [3.2 时间戳单调性](#32-时间戳单调性)
  - [4. 资源绑定验证](#4-资源绑定验证)
    - [4.1 Resource 一致性](#41-resource-一致性)
    - [4.2 语义约定验证](#42-语义约定验证)
  - [5. 语义约定验证](#5-语义约定验证)
    - [5.1 属性类型验证](#51-属性类型验证)
  - [6. 自动化验证工具](#6-自动化验证工具)
    - [6.1 验证管道](#61-验证管道)
  - [7. 参考资料](#7-参考资料)

## 1. Trace 完整性验证

### 1.1 Span 完整性

**验证规则**：

1. 每个 Span 必须有 `trace_id` 和 `span_id`
2. 每个 Span 必须有 `start_time` 和 `end_time`
3. `end_time` 必须 >= `start_time`
4. 子 Span 的时间范围必须在父 Span 内

```go
type SpanValidator struct{}

func (sv *SpanValidator) ValidateSpan(span ptrace.Span) []error {
    var errors []error
    
    // 验证 ID
    if span.TraceID().IsEmpty() {
        errors = append(errors, fmt.Errorf("missing trace_id"))
    }
    
    if span.SpanID().IsEmpty() {
        errors = append(errors, fmt.Errorf("missing span_id"))
    }
    
    // 验证时间
    if span.StartTimestamp() == 0 {
        errors = append(errors, fmt.Errorf("missing start_time"))
    }
    
    if span.EndTimestamp() == 0 {
        errors = append(errors, fmt.Errorf("missing end_time"))
    }
    
    if span.EndTimestamp() < span.StartTimestamp() {
        errors = append(errors, fmt.Errorf(
            "end_time (%d) < start_time (%d)",
            span.EndTimestamp(),
            span.StartTimestamp(),
        ))
    }
    
    return errors
}

func (sv *SpanValidator) ValidateParentChild(parent, child ptrace.Span) []error {
    var errors []error
    
    // 验证 Trace ID 一致
    if parent.TraceID() != child.TraceID() {
        errors = append(errors, fmt.Errorf(
            "trace_id mismatch: parent=%s, child=%s",
            parent.TraceID(),
            child.TraceID(),
        ))
    }
    
    // 验证 Parent Span ID
    if child.ParentSpanID() != parent.SpanID() {
        errors = append(errors, fmt.Errorf(
            "parent_span_id mismatch: expected=%s, got=%s",
            parent.SpanID(),
            child.ParentSpanID(),
        ))
    }
    
    // 验证时间范围
    if child.StartTimestamp() < parent.StartTimestamp() {
        errors = append(errors, fmt.Errorf(
            "child start_time (%d) < parent start_time (%d)",
            child.StartTimestamp(),
            parent.StartTimestamp(),
        ))
    }
    
    if child.EndTimestamp() > parent.EndTimestamp() {
        errors = append(errors, fmt.Errorf(
            "child end_time (%d) > parent end_time (%d)",
            child.EndTimestamp(),
            parent.EndTimestamp(),
        ))
    }
    
    return errors
}
```

### 1.2 Trace 树结构验证

```go
type TraceTree struct {
    Root     *SpanNode
    SpanMap  map[[8]byte]*SpanNode
}

type SpanNode struct {
    Span     ptrace.Span
    Children []*SpanNode
}

func BuildTraceTree(traces ptrace.Traces) (*TraceTree, error) {
    tree := &TraceTree{
        SpanMap: make(map[[8]byte]*SpanNode),
    }
    
    // 第一遍：创建所有节点
    for i := 0; i < traces.ResourceSpans().Len(); i++ {
        rs := traces.ResourceSpans().At(i)
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)
                node := &SpanNode{
                    Span:     span,
                    Children: make([]*SpanNode, 0),
                }
                tree.SpanMap[span.SpanID()] = node
            }
        }
    }
    
    // 第二遍：建立父子关系
    for _, node := range tree.SpanMap {
        if node.Span.ParentSpanID().IsEmpty() {
            // 根节点
            if tree.Root != nil {
                return nil, fmt.Errorf("multiple root spans found")
            }
            tree.Root = node
        } else {
            // 查找父节点
            parent, ok := tree.SpanMap[node.Span.ParentSpanID()]
            if !ok {
                return nil, fmt.Errorf(
                    "parent span not found: %s",
                    node.Span.ParentSpanID(),
                )
            }
            parent.Children = append(parent.Children, node)
        }
    }
    
    if tree.Root == nil {
        return nil, fmt.Errorf("no root span found")
    }
    
    return tree, nil
}

func (tt *TraceTree) Validate() []error {
    var errors []error
    
    // 验证树结构
    visited := make(map[[8]byte]bool)
    errors = append(errors, tt.validateNode(tt.Root, visited)...)
    
    // 检查是否有孤立节点
    for spanID := range tt.SpanMap {
        if !visited[spanID] {
            errors = append(errors, fmt.Errorf(
                "orphaned span: %s",
                spanID,
            ))
        }
    }
    
    return errors
}

func (tt *TraceTree) validateNode(node *SpanNode, visited map[[8]byte]bool) []error {
    var errors []error
    
    spanID := node.Span.SpanID()
    
    // 检查循环引用
    if visited[spanID] {
        return []error{fmt.Errorf("circular reference detected: %s", spanID)}
    }
    
    visited[spanID] = true
    
    // 验证子节点
    for _, child := range node.Children {
        // 验证父子关系
        validator := &SpanValidator{}
        errors = append(errors, validator.ValidateParentChild(node.Span, child.Span)...)
        
        // 递归验证子树
        errors = append(errors, tt.validateNode(child, visited)...)
    }
    
    return errors
}
```

## 2. 因果关系一致性

### 2.1 Happens-Before 关系

**定义**：

```text
Span A happens-before Span B (A → B) 当且仅当：
1. A.end_time < B.start_time (时间顺序)
2. A.span_id = B.parent_span_id (父子关系)
3. A → C 且 C → B (传递性)
```

**验证实现**：

```go
type HappensBeforeGraph struct {
    edges map[[8]byte]map[[8]byte]bool
}

func NewHappensBeforeGraph() *HappensBeforeGraph {
    return &HappensBeforeGraph{
        edges: make(map[[8]byte]map[[8]byte]bool),
    }
}

func (hb *HappensBeforeGraph) AddEdge(from, to [8]byte) {
    if hb.edges[from] == nil {
        hb.edges[from] = make(map[[8]byte]bool)
    }
    hb.edges[from][to] = true
}

func (hb *HappensBeforeGraph) HappensBefore(a, b [8]byte) bool {
    // 直接边
    if hb.edges[a][b] {
        return true
    }
    
    // 传递闭包（BFS）
    visited := make(map[[8]byte]bool)
    queue := [][8]byte{a}
    
    for len(queue) > 0 {
        current := queue[0]
        queue = queue[1:]
        
        if visited[current] {
            continue
        }
        visited[current] = true
        
        if current == b {
            return true
        }
        
        for next := range hb.edges[current] {
            queue = append(queue, next)
        }
    }
    
    return false
}

func BuildHappensBeforeGraph(traces ptrace.Traces) *HappensBeforeGraph {
    graph := NewHappensBeforeGraph()
    spans := extractAllSpans(traces)
    
    for i := 0; i < len(spans); i++ {
        for j := 0; j < len(spans); j++ {
            if i == j {
                continue
            }
            
            spanA := spans[i]
            spanB := spans[j]
            
            // 规则 1: 时间顺序
            if spanA.EndTimestamp() < spanB.StartTimestamp() {
                graph.AddEdge(spanA.SpanID(), spanB.SpanID())
            }
            
            // 规则 2: 父子关系
            if spanA.SpanID() == spanB.ParentSpanID() {
                graph.AddEdge(spanA.SpanID(), spanB.SpanID())
            }
        }
    }
    
    return graph
}
```

### 2.2 因果一致性验证

```go
func VerifyCausalConsistency(traces ptrace.Traces) []error {
    var errors []error
    
    graph := BuildHappensBeforeGraph(traces)
    spans := extractAllSpans(traces)
    
    for i := 0; i < len(spans); i++ {
        for j := i + 1; j < len(spans); j++ {
            spanA := spans[i]
            spanB := spans[j]
            
            aBeforeB := graph.HappensBefore(spanA.SpanID(), spanB.SpanID())
            bBeforeA := graph.HappensBefore(spanB.SpanID(), spanA.SpanID())
            
            // 检查循环依赖
            if aBeforeB && bBeforeA {
                errors = append(errors, fmt.Errorf(
                    "circular causality: %s <-> %s",
                    spanA.SpanID(),
                    spanB.SpanID(),
                ))
            }
            
            // 检查时间一致性
            if aBeforeB && spanA.EndTimestamp() > spanB.StartTimestamp() {
                errors = append(errors, fmt.Errorf(
                    "causality violation: %s happens-before %s but timestamps inconsistent",
                    spanA.SpanID(),
                    spanB.SpanID(),
                ))
            }
        }
    }
    
    return errors
}
```

## 3. 时间序列正确性

### 3.1 时钟偏移检测

```go
type ClockSkewDetector struct {
    maxSkew time.Duration
}

func NewClockSkewDetector(maxSkew time.Duration) *ClockSkewDetector {
    return &ClockSkewDetector{
        maxSkew: maxSkew,
    }
}

func (csd *ClockSkewDetector) DetectSkew(traces ptrace.Traces) []error {
    var errors []error
    
    // 按服务分组
    serviceSpans := make(map[string][]ptrace.Span)
    
    for i := 0; i < traces.ResourceSpans().Len(); i++ {
        rs := traces.ResourceSpans().At(i)
        serviceName := rs.Resource().Attributes().AsRaw()["service.name"].(string)
        
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)
                serviceSpans[serviceName] = append(serviceSpans[serviceName], span)
            }
        }
    }
    
    // 检测跨服务时钟偏移
    for serviceA, spansA := range serviceSpans {
        for serviceB, spansB := range serviceSpans {
            if serviceA == serviceB {
                continue
            }
            
            skew := csd.estimateSkew(spansA, spansB)
            if skew > csd.maxSkew {
                errors = append(errors, fmt.Errorf(
                    "clock skew detected between %s and %s: %v",
                    serviceA,
                    serviceB,
                    skew,
                ))
            }
        }
    }
    
    return errors
}

func (csd *ClockSkewDetector) estimateSkew(spansA, spansB []ptrace.Span) time.Duration {
    var maxSkew time.Duration
    
    for _, spanA := range spansA {
        for _, spanB := range spansB {
            // 如果 A 是 B 的父节点
            if spanA.SpanID() == spanB.ParentSpanID() {
                // B 的开始时间应该在 A 的时间范围内
                if spanB.StartTimestamp() < spanA.StartTimestamp() {
                    skew := time.Duration(spanA.StartTimestamp() - spanB.StartTimestamp())
                    if skew > maxSkew {
                        maxSkew = skew
                    }
                }
            }
        }
    }
    
    return maxSkew
}
```

### 3.2 时间戳单调性

```go
func VerifyTimestampMonotonicity(traces ptrace.Traces) []error {
    var errors []error
    
    tree, err := BuildTraceTree(traces)
    if err != nil {
        return []error{err}
    }
    
    errors = append(errors, verifyNodeMonotonicity(tree.Root)...)
    
    return errors
}

func verifyNodeMonotonicity(node *SpanNode) []error {
    var errors []error
    
    // 验证当前节点
    if node.Span.EndTimestamp() < node.Span.StartTimestamp() {
        errors = append(errors, fmt.Errorf(
            "span %s: end_time < start_time",
            node.Span.SpanID(),
        ))
    }
    
    // 验证事件时间戳
    for i := 0; i < node.Span.Events().Len(); i++ {
        event := node.Span.Events().At(i)
        
        if event.Timestamp() < node.Span.StartTimestamp() {
            errors = append(errors, fmt.Errorf(
                "span %s: event timestamp < start_time",
                node.Span.SpanID(),
            ))
        }
        
        if event.Timestamp() > node.Span.EndTimestamp() {
            errors = append(errors, fmt.Errorf(
                "span %s: event timestamp > end_time",
                node.Span.SpanID(),
            ))
        }
    }
    
    // 递归验证子节点
    for _, child := range node.Children {
        errors = append(errors, verifyNodeMonotonicity(child)...)
    }
    
    return errors
}
```

## 4. 资源绑定验证

### 4.1 Resource 一致性

```go
func VerifyResourceConsistency(traces ptrace.Traces) []error {
    var errors []error
    
    // 按 Trace ID 分组
    traceResources := make(map[[16]byte]map[string]interface{})
    
    for i := 0; i < traces.ResourceSpans().Len(); i++ {
        rs := traces.ResourceSpans().At(i)
        resource := rs.Resource().Attributes().AsRaw()
        
        for j := 0; j < rs.ScopeSpans().Len(); j++ {
            ss := rs.ScopeSpans().At(j)
            for k := 0; k < ss.Spans().Len(); k++ {
                span := ss.Spans().At(k)
                traceID := span.TraceID()
                
                if existing, ok := traceResources[traceID]; ok {
                    // 验证 Resource 一致性
                    if !resourcesEqual(existing, resource) {
                        errors = append(errors, fmt.Errorf(
                            "inconsistent resources for trace %s",
                            traceID,
                        ))
                    }
                } else {
                    traceResources[traceID] = resource
                }
            }
        }
    }
    
    return errors
}

func resourcesEqual(a, b map[string]interface{}) bool {
    // 检查关键属性
    keyAttributes := []string{
        "service.name",
        "service.namespace",
        "deployment.environment",
    }
    
    for _, key := range keyAttributes {
        if a[key] != b[key] {
            return false
        }
    }
    
    return true
}
```

### 4.2 语义约定验证

```go
type SemanticConventionValidator struct {
    requiredAttributes map[string][]string
}

func NewSemanticConventionValidator() *SemanticConventionValidator {
    return &SemanticConventionValidator{
        requiredAttributes: map[string][]string{
            "http": {
                "http.method",
                "http.url",
                "http.status_code",
            },
            "db": {
                "db.system",
                "db.statement",
            },
            "rpc": {
                "rpc.system",
                "rpc.service",
                "rpc.method",
            },
        },
    }
}

func (scv *SemanticConventionValidator) ValidateSpan(span ptrace.Span) []error {
    var errors []error
    
    spanKind := span.Kind()
    attrs := span.Attributes().AsRaw()
    
    // 根据 Span Kind 验证
    switch spanKind {
    case ptrace.SpanKindClient, ptrace.SpanKindServer:
        // 检查是否是 HTTP span
        if _, ok := attrs["http.method"]; ok {
            errors = append(errors, scv.validateHTTPSpan(attrs)...)
        }
        
        // 检查是否是 RPC span
        if _, ok := attrs["rpc.system"]; ok {
            errors = append(errors, scv.validateRPCSpan(attrs)...)
        }
        
    case ptrace.SpanKindInternal:
        // 检查是否是 DB span
        if _, ok := attrs["db.system"]; ok {
            errors = append(errors, scv.validateDBSpan(attrs)...)
        }
    }
    
    return errors
}

func (scv *SemanticConventionValidator) validateHTTPSpan(attrs map[string]interface{}) []error {
    var errors []error
    
    for _, required := range scv.requiredAttributes["http"] {
        if _, ok := attrs[required]; !ok {
            errors = append(errors, fmt.Errorf(
                "missing required HTTP attribute: %s",
                required,
            ))
        }
    }
    
    return errors
}
```

## 5. 语义约定验证

### 5.1 属性类型验证

```go
type AttributeTypeValidator struct {
    expectedTypes map[string]reflect.Kind
}

func NewAttributeTypeValidator() *AttributeTypeValidator {
    return &AttributeTypeValidator{
        expectedTypes: map[string]reflect.Kind{
            "http.status_code":    reflect.Int64,
            "http.method":         reflect.String,
            "http.url":            reflect.String,
            "db.statement":        reflect.String,
            "net.peer.port":       reflect.Int64,
            "error":               reflect.Bool,
        },
    }
}

func (atv *AttributeTypeValidator) ValidateAttributes(attrs map[string]interface{}) []error {
    var errors []error
    
    for key, value := range attrs {
        if expectedType, ok := atv.expectedTypes[key]; ok {
            actualType := reflect.TypeOf(value).Kind()
            
            if actualType != expectedType {
                errors = append(errors, fmt.Errorf(
                    "attribute %s: expected type %s, got %s",
                    key,
                    expectedType,
                    actualType,
                ))
            }
        }
    }
    
    return errors
}
```

## 6. 自动化验证工具

### 6.1 验证管道

```go
type ValidationPipeline struct {
    validators []Validator
}

type Validator interface {
    Validate(ptrace.Traces) []error
}

func NewValidationPipeline() *ValidationPipeline {
    return &ValidationPipeline{
        validators: []Validator{
            &SpanValidator{},
            &TraceTreeValidator{},
            &CausalConsistencyValidator{},
            &ClockSkewDetector{maxSkew: 5 * time.Second},
            &ResourceConsistencyValidator{},
            &SemanticConventionValidator{},
        },
    }
}

func (vp *ValidationPipeline) Validate(ctx context.Context, traces ptrace.Traces) ValidationResult {
    ctx, span := tracer.Start(ctx, "validation_pipeline")
    defer span.End()
    
    result := ValidationResult{
        Errors:   make([]error, 0),
        Warnings: make([]error, 0),
    }
    
    for _, validator := range vp.validators {
        errors := validator.Validate(traces)
        result.Errors = append(result.Errors, errors...)
    }
    
    span.SetAttributes(
        attribute.Int("errors.count", len(result.Errors)),
        attribute.Int("warnings.count", len(result.Warnings)),
    )
    
    return result
}

type ValidationResult struct {
    Errors   []error
    Warnings []error
}

func (vr ValidationResult) IsValid() bool {
    return len(vr.Errors) == 0
}
```

## 7. 参考资料

- **OTLP Specification**：<https://github.com/open-telemetry/opentelemetry-proto>
- **Semantic Conventions**：<https://opentelemetry.io/docs/specs/semconv/>
- **Formal Verification**：`docs/design/formal-proof.md`
- **CSP Model**：`07-csp-formal-model.md`

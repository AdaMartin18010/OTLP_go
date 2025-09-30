# Go 语言语法语义分析

## 目录

- [Go 语言语法语义分析](#go-语言语法语义分析)
  - [目录](#目录)
  - [1. Go 语言语法结构分析](#1-go-语言语法结构分析)
    - [1.1 基本语法元素](#11-基本语法元素)
      - [标识符和关键字](#标识符和关键字)
      - [类型系统](#类型系统)
    - [1.2 表达式和语句](#12-表达式和语句)
      - [表达式语法](#表达式语法)
      - [语句语法](#语句语法)
  - [2. Go 语言语义分析](#2-go-语言语义分析)
    - [2.1 语义模型定义](#21-语义模型定义)
      - [语义环境](#语义环境)
      - [语义规则](#语义规则)
    - [2.2 语义一致性](#22-语义一致性)
      - [类型一致性](#类型一致性)
  - [3. 控制流分析](#3-控制流分析)
    - [3.1 控制流图](#31-控制流图)
      - [控制流图定义](#控制流图定义)
      - [控制流构建](#控制流构建)
    - [3.2 控制流分析](#32-控制流分析)
      - [可达性分析](#可达性分析)
      - [循环检测](#循环检测)
  - [4. 执行流分析](#4-执行流分析)
    - [4.1 执行模型](#41-执行模型)
      - [执行状态](#执行状态)
      - [执行步骤](#执行步骤)
    - [4.2 调度模型](#42-调度模型)
      - [调度器](#调度器)
  - [5. 数据流分析](#5-数据流分析)
    - [5.1 数据流图](#51-数据流图)
      - [数据流图定义](#数据流图定义)
      - [数据流构建](#数据流构建)
    - [5.2 数据流分析](#52-数据流分析)
      - [活跃变量分析](#活跃变量分析)
      - [到达定义分析](#到达定义分析)
  - [6. 总结](#6-总结)

## 1. Go 语言语法结构分析

### 1.1 基本语法元素

#### 标识符和关键字

```go
// 标识符规则
type Identifier struct {
    Name string
    Scope Scope
    Type Type
}

// 关键字分类
const (
    // 声明关键字
    VAR = "var"
    CONST = "const"
    TYPE = "type"
    FUNC = "func"
    
    // 控制流关键字
    IF = "if"
    ELSE = "else"
    FOR = "for"
    RANGE = "range"
    SWITCH = "switch"
    CASE = "case"
    DEFAULT = "default"
    BREAK = "break"
    CONTINUE = "continue"
    GOTO = "goto"
    FALLTHROUGH = "fallthrough"
    
    // 并发关键字
    GO = "go"
    CHAN = "chan"
    SELECT = "select"
    DEFER = "defer"
    
    // 类型关键字
    INTERFACE = "interface"
    STRUCT = "struct"
    MAP = "map"
    SLICE = "slice"
)
```

#### 类型系统

```go
// 类型层次结构
type Type interface {
    String() string
    Size() int
    Align() int
    IsComparable() bool
    IsAssignable() bool
}

// 基本类型
type BasicType struct {
    Kind BasicKind
    Size int
}

type BasicKind int

const (
    Invalid BasicKind = iota
    Bool
    Int
    Int8
    Int16
    Int32
    Int64
    Uint
    Uint8
    Uint16
    Uint32
    Uint64
    Uintptr
    Float32
    Float64
    Complex64
    Complex128
    String
    UnsafePointer
)

// 复合类型
type CompositeType struct {
    Kind CompositeKind
    Elements []Type
}

type CompositeKind int

const (
    Array CompositeKind = iota
    Slice
    Struct
    Pointer
    Function
    Interface
    Map
    Channel
)
```

### 1.2 表达式和语句

#### 表达式语法

```go
// 表达式类型
type Expression interface {
    Type() Type
    Eval() Value
    String() string
}

// 基本表达式
type BasicExpr struct {
    Value Value
    Type Type
}

// 二元表达式
type BinaryExpr struct {
    Left Expression
    Op BinaryOp
    Right Expression
}

type BinaryOp int

const (
    ADD BinaryOp = iota
    SUB
    MUL
    QUO
    REM
    AND
    OR
    XOR
    SHL
    SHR
    AND_NOT
    LAND
    LOR
    EQL
    LSS
    GTR
    NEQ
    LEQ
    GEQ
)

// 一元表达式
type UnaryExpr struct {
    Op UnaryOp
    X Expression
}

type UnaryOp int

const (
    PLUS UnaryOp = iota
    MINUS
    NOT
    XOR
    ARROW
)
```

#### 语句语法

```go
// 语句类型
type Statement interface {
    Execute() error
    String() string
}

// 声明语句
type DeclStmt struct {
    Decl Declaration
}

// 表达式语句
type ExprStmt struct {
    X Expression
}

// 赋值语句
type AssignStmt struct {
    Lhs []Expression
    Tok token.Token
    Rhs []Expression
}

// 控制流语句
type IfStmt struct {
    Init Statement
    Cond Expression
    Body *BlockStmt
    Else Statement
}

type ForStmt struct {
    Init Statement
    Cond Expression
    Post Statement
    Body *BlockStmt
}

type RangeStmt struct {
    Key, Value Expression
    Tok token.Token
    X Expression
    Body *BlockStmt
}

type SwitchStmt struct {
    Init Statement
    Tag Expression
    Body *BlockStmt
}

type SelectStmt struct {
    Body *BlockStmt
}
```

## 2. Go 语言语义分析

### 2.1 语义模型定义

#### 语义环境

```go
// 语义环境
type SemanticEnvironment struct {
    Variables map[string]Value
    Types map[string]Type
    Functions map[string]Function
    Packages map[string]Package
    Scope Scope
}

// 作用域
type Scope struct {
    Parent *Scope
    Children []*Scope
    Objects map[string]Object
}

// 对象
type Object interface {
    Name() string
    Type() Type
    Pos() token.Position
}

type Var struct {
    Name string
    Type Type
    Value Value
    Pos token.Position
}

type Func struct {
    Name string
    Type *FunctionType
    Body *BlockStmt
    Pos token.Position
}

type TypeName struct {
    Name string
    Type Type
    Pos token.Position
}
```

#### 语义规则

```go
// 语义规则
type SemanticRule interface {
    Check(ast ASTNode, env *SemanticEnvironment) error
}

// 类型检查规则
type TypeCheckRule struct{}

func (r TypeCheckRule) Check(ast ASTNode, env *SemanticEnvironment) error {
    switch node := ast.(type) {
    case *BinaryExpr:
        return r.checkBinaryExpr(node, env)
    case *UnaryExpr:
        return r.checkUnaryExpr(node, env)
    case *CallExpr:
        return r.checkCallExpr(node, env)
    default:
        return nil
    }
}

func (r TypeCheckRule) checkBinaryExpr(expr *BinaryExpr, env *SemanticEnvironment) error {
    leftType := expr.Left.Type()
    rightType := expr.Right.Type()
    
    // 检查操作符兼容性
    if !r.isCompatible(leftType, rightType, expr.Op) {
        return fmt.Errorf("incompatible types: %s %s %s", 
            leftType, expr.Op, rightType)
    }
    
    return nil
}

// 作用域规则
type ScopeRule struct{}

func (r ScopeRule) Check(ast ASTNode, env *SemanticEnvironment) error {
    // 检查变量声明
    // 检查作用域嵌套
    // 检查重复声明
    return nil
}
```

### 2.2 语义一致性

#### 类型一致性

```go
// 类型一致性检查
type TypeConsistency struct{}

func (tc TypeConsistency) CheckConsistency(ast ASTNode, env *SemanticEnvironment) error {
    return tc.checkNode(ast, env)
}

func (tc TypeConsistency) checkNode(node ASTNode, env *SemanticEnvironment) error {
    switch n := node.(type) {
    case *AssignStmt:
        return tc.checkAssignment(n, env)
    case *CallExpr:
        return tc.checkFunctionCall(n, env)
    case *ReturnStmt:
        return tc.checkReturn(n, env)
    default:
        return nil
    }
}

func (tc TypeConsistency) checkAssignment(stmt *AssignStmt, env *SemanticEnvironment) error {
    if len(stmt.Lhs) != len(stmt.Rhs) {
        return fmt.Errorf("assignment count mismatch")
    }
    
    for i, lhs := range stmt.Lhs {
        rhs := stmt.Rhs[i]
        
        lhsType := lhs.Type()
        rhsType := rhs.Type()
        
        if !tc.isAssignable(lhsType, rhsType) {
            return fmt.Errorf("cannot assign %s to %s", rhsType, lhsType)
        }
    }
    
    return nil
}
```

## 3. 控制流分析

### 3.1 控制流图

#### 控制流图定义

```go
// 控制流图
type ControlFlowGraph struct {
    Nodes []*CFGNode
    Edges []*CFGEdge
    Entry *CFGNode
    Exit *CFGNode
}

// 控制流节点
type CFGNode struct {
    ID int
    Type NodeType
    Statement Statement
    InEdges []*CFGEdge
    OutEdges []*CFGEdge
}

type NodeType int

const (
    EntryNode NodeType = iota
    ExitNode
    StatementNode
    DecisionNode
    MergeNode
)

// 控制流边
type CFGEdge struct {
    From *CFGNode
    To *CFGNode
    Condition Expression
    Type EdgeType
}

type EdgeType int

const (
    TrueEdge EdgeType = iota
    FalseEdge
    UnconditionalEdge
    ExceptionEdge
)
```

#### 控制流构建

```go
// 控制流构建器
type CFGBuilder struct{}

func (b *CFGBuilder) Build(ast ASTNode) *ControlFlowGraph {
    cfg := &ControlFlowGraph{
        Nodes: make([]*CFGNode, 0),
        Edges: make([]*CFGEdge, 0),
    }
    
    b.buildNode(ast, cfg)
    return cfg
}

func (b *CFGBuilder) buildNode(node ASTNode, cfg *ControlFlowGraph) *CFGNode {
    switch n := node.(type) {
    case *IfStmt:
        return b.buildIfStmt(n, cfg)
    case *ForStmt:
        return b.buildForStmt(n, cfg)
    case *SwitchStmt:
        return b.buildSwitchStmt(n, cfg)
    case *SelectStmt:
        return b.buildSelectStmt(n, cfg)
    default:
        return b.buildStatement(n, cfg)
    }
}

func (b *CFGBuilder) buildIfStmt(stmt *IfStmt, cfg *ControlFlowGraph) *CFGNode {
    // 创建条件节点
    condNode := &CFGNode{
        ID: len(cfg.Nodes),
        Type: DecisionNode,
        Statement: stmt,
    }
    cfg.Nodes = append(cfg.Nodes, condNode)
    
    // 构建 then 分支
    thenNode := b.buildNode(stmt.Body, cfg)
    
    // 构建 else 分支
    var elseNode *CFGNode
    if stmt.Else != nil {
        elseNode = b.buildNode(stmt.Else, cfg)
    }
    
    // 创建合并节点
    mergeNode := &CFGNode{
        ID: len(cfg.Nodes),
        Type: MergeNode,
    }
    cfg.Nodes = append(cfg.Nodes, mergeNode)
    
    // 添加边
    cfg.Edges = append(cfg.Edges, &CFGEdge{
        From: condNode,
        To: thenNode,
        Type: TrueEdge,
    })
    
    if elseNode != nil {
        cfg.Edges = append(cfg.Edges, &CFGEdge{
            From: condNode,
            To: elseNode,
            Type: FalseEdge,
        })
        cfg.Edges = append(cfg.Edges, &CFGEdge{
            From: elseNode,
            To: mergeNode,
            Type: UnconditionalEdge,
        })
    } else {
        cfg.Edges = append(cfg.Edges, &CFGEdge{
            From: condNode,
            To: mergeNode,
            Type: FalseEdge,
        })
    }
    
    cfg.Edges = append(cfg.Edges, &CFGEdge{
        From: thenNode,
        To: mergeNode,
        Type: UnconditionalEdge,
    })
    
    return mergeNode
}
```

### 3.2 控制流分析

#### 可达性分析

```go
// 可达性分析
type ReachabilityAnalysis struct {
    cfg *ControlFlowGraph
    reachable map[int]bool
}

func (ra *ReachabilityAnalysis) Analyze() map[int]bool {
    ra.reachable = make(map[int]bool)
    ra.dfs(ra.cfg.Entry.ID)
    return ra.reachable
}

func (ra *ReachabilityAnalysis) dfs(nodeID int) {
    if ra.reachable[nodeID] {
        return
    }
    
    ra.reachable[nodeID] = true
    
    node := ra.cfg.Nodes[nodeID]
    for _, edge := range node.OutEdges {
        ra.dfs(edge.To.ID)
    }
}
```

#### 循环检测

```go
// 循环检测
type LoopDetection struct {
    cfg *ControlFlowGraph
    visited map[int]bool
    recStack map[int]bool
    loops []*Loop
}

type Loop struct {
    Header *CFGNode
    Body []*CFGNode
    Type LoopType
}

type LoopType int

const (
    ForLoop LoopType = iota
    WhileLoop
    DoWhileLoop
    InfiniteLoop
)

func (ld *LoopDetection) DetectLoops() []*Loop {
    ld.visited = make(map[int]bool)
    ld.recStack = make(map[int]bool)
    ld.loops = make([]*Loop, 0)
    
    for _, node := range ld.cfg.Nodes {
        if !ld.visited[node.ID] {
            ld.dfs(node.ID)
        }
    }
    
    return ld.loops
}

func (ld *LoopDetection) dfs(nodeID int) {
    ld.visited[nodeID] = true
    ld.recStack[nodeID] = true
    
    node := ld.cfg.Nodes[nodeID]
    for _, edge := range node.OutEdges {
        if !ld.visited[edge.To.ID] {
            ld.dfs(edge.To.ID)
        } else if ld.recStack[edge.To.ID] {
            // 发现循环
            loop := &Loop{
                Header: edge.To,
                Body: []*CFGNode{node},
                Type: ld.classifyLoop(edge.To, node),
            }
            ld.loops = append(ld.loops, loop)
        }
    }
    
    ld.recStack[nodeID] = false
}
```

## 4. 执行流分析

### 4.1 执行模型

#### 执行状态

```go
// 执行状态
type ExecutionState struct {
    ProgramCounter int
    Stack []Value
    Heap map[string]Value
    Goroutines map[int]*Goroutine
    Channels map[string]*Channel
    Mutexes map[string]*Mutex
}

// Goroutine 状态
type Goroutine struct {
    ID int
    State GoroutineState
    Stack []Value
    PC int
    Parent *Goroutine
    Children []*Goroutine
}

type GoroutineState int

const (
    Runnable GoroutineState = iota
    Running
    Blocked
    Waiting
    Dead
)

// Channel 状态
type Channel struct {
    Buffer []Value
    Capacity int
    Senders []*Goroutine
    Receivers []*Goroutine
    Closed bool
}

// Mutex 状态
type Mutex struct {
    Locked bool
    Owner *Goroutine
    Waiters []*Goroutine
}
```

#### 执行步骤

```go
// 执行器
type Executor struct {
    state *ExecutionState
    scheduler *Scheduler
}

func (e *Executor) Execute(ast ASTNode) error {
    return e.executeNode(ast)
}

func (e *Executor) executeNode(node ASTNode) error {
    switch n := node.(type) {
    case *GoStmt:
        return e.executeGoStmt(n)
    case *SendStmt:
        return e.executeSendStmt(n)
    case *RecvStmt:
        return e.executeRecvStmt(n)
    case *SelectStmt:
        return e.executeSelectStmt(n)
    default:
        return e.executeStatement(n)
    }
}

func (e *Executor) executeGoStmt(stmt *GoStmt) error {
    // 创建新的 goroutine
    goroutine := &Goroutine{
        ID: len(e.state.Goroutines),
        State: Runnable,
        Stack: make([]Value, 0),
        PC: 0,
    }
    
    e.state.Goroutines[goroutine.ID] = goroutine
    
    // 调度执行
    return e.scheduler.Schedule(goroutine, stmt.Call)
}
```

### 4.2 调度模型

#### 调度器

```go
// 调度器
type Scheduler struct {
    runnable []*Goroutine
    blocked []*Goroutine
    current *Goroutine
    quantum time.Duration
}

func (s *Scheduler) Schedule(goroutine *Goroutine, call *CallExpr) error {
    s.runnable = append(s.runnable, goroutine)
    return s.scheduleNext()
}

func (s *Scheduler) scheduleNext() error {
    if len(s.runnable) == 0 {
        return fmt.Errorf("no runnable goroutines")
    }
    
    // 选择下一个 goroutine
    next := s.selectNext()
    
    // 切换上下文
    if s.current != nil {
        s.current.State = Runnable
        s.runnable = append(s.runnable, s.current)
    }
    
    s.current = next
    s.current.State = Running
    
    // 执行
    return s.executeCurrent()
}

func (s *Scheduler) selectNext() *Goroutine {
    // 简单的轮询调度
    if len(s.runnable) == 0 {
        return nil
    }
    
    next := s.runnable[0]
    s.runnable = s.runnable[1:]
    return next
}
```

## 5. 数据流分析

### 5.1 数据流图

#### 数据流图定义

```go
// 数据流图
type DataFlowGraph struct {
    Nodes []*DFGNode
    Edges []*DFGEdge
    Variables map[string]*Variable
}

// 数据流节点
type DFGNode struct {
    ID int
    Type DFGNodeType
    Statement Statement
    Defs []*Variable
    Uses []*Variable
}

type DFGNodeType int

const (
    DefNode DFGNodeType = iota
    UseNode
    PhiNode
    CallNode
)

// 数据流边
type DFGEdge struct {
    From *DFGNode
    To *DFGNode
    Variable *Variable
}

// 变量
type Variable struct {
    Name string
    Type Type
    Defs []*DFGNode
    Uses []*DFGNode
}
```

#### 数据流构建

```go
// 数据流构建器
type DFGBuilder struct{}

func (b *DFGBuilder) Build(cfg *ControlFlowGraph) *DataFlowGraph {
    dfg := &DataFlowGraph{
        Nodes: make([]*DFGNode, 0),
        Edges: make([]*DFGEdge, 0),
        Variables: make(map[string]*Variable),
    }
    
    // 构建数据流节点
    for _, cfgNode := range cfg.Nodes {
        dfgNode := b.buildDFGNode(cfgNode, dfg)
        dfg.Nodes = append(dfg.Nodes, dfgNode)
    }
    
    // 构建数据流边
    b.buildDFGEdges(cfg, dfg)
    
    return dfg
}

func (b *DFGBuilder) buildDFGNode(cfgNode *CFGNode, dfg *DataFlowGraph) *DFGNode {
    dfgNode := &DFGNode{
        ID: cfgNode.ID,
        Statement: cfgNode.Statement,
        Defs: make([]*Variable, 0),
        Uses: make([]*Variable, 0),
    }
    
    // 分析定义和使用
    b.analyzeDefUse(cfgNode.Statement, dfgNode, dfg)
    
    return dfgNode
}
```

### 5.2 数据流分析

#### 活跃变量分析

```go
// 活跃变量分析
type LiveVariableAnalysis struct {
    dfg *DataFlowGraph
    liveIn map[int]map[string]bool
    liveOut map[int]map[string]bool
}

func (lva *LiveVariableAnalysis) Analyze() (map[int]map[string]bool, map[int]map[string]bool) {
    lva.liveIn = make(map[int]map[string]bool)
    lva.liveOut = make(map[int]map[string]bool)
    
    // 初始化
    for _, node := range lva.dfg.Nodes {
        lva.liveIn[node.ID] = make(map[string]bool)
        lva.liveOut[node.ID] = make(map[string]bool)
    }
    
    // 迭代直到收敛
    changed := true
    for changed {
        changed = false
        
        for _, node := range lva.dfg.Nodes {
            oldLiveIn := make(map[string]bool)
            oldLiveOut := make(map[string]bool)
            
            // 复制当前值
            for v := range lva.liveIn[node.ID] {
                oldLiveIn[v] = true
            }
            for v := range lva.liveOut[node.ID] {
                oldLiveOut[v] = true
            }
            
            // 计算新的 liveOut
            lva.computeLiveOut(node)
            
            // 计算新的 liveIn
            lva.computeLiveIn(node)
            
            // 检查是否改变
            if !lva.equal(oldLiveIn, lva.liveIn[node.ID]) || 
               !lva.equal(oldLiveOut, lva.liveOut[node.ID]) {
                changed = true
            }
        }
    }
    
    return lva.liveIn, lva.liveOut
}

func (lva *LiveVariableAnalysis) computeLiveOut(node *DFGNode) {
    // liveOut[n] = union of liveIn[s] for all successors s of n
    for _, edge := range node.OutEdges {
        for v := range lva.liveIn[edge.To.ID] {
            lva.liveOut[node.ID][v] = true
        }
    }
}

func (lva *LiveVariableAnalysis) computeLiveIn(node *DFGNode) {
    // liveIn[n] = use[n] union (liveOut[n] - def[n])
    
    // 复制 liveOut
    for v := range lva.liveOut[node.ID] {
        lva.liveIn[node.ID][v] = true
    }
    
    // 减去 def
    for _, def := range node.Defs {
        delete(lva.liveIn[node.ID], def.Name)
    }
    
    // 加上 use
    for _, use := range node.Uses {
        lva.liveIn[node.ID][use.Name] = true
    }
}
```

#### 到达定义分析

```go
// 到达定义分析
type ReachingDefinitionAnalysis struct {
    dfg *DataFlowGraph
    reachIn map[int]map[int]bool
    reachOut map[int]map[int]bool
}

func (rda *ReachingDefinitionAnalysis) Analyze() (map[int]map[int]bool, map[int]map[int]bool) {
    rda.reachIn = make(map[int]map[int]bool)
    rda.reachOut = make(map[int]map[int]bool)
    
    // 初始化
    for _, node := range rda.dfg.Nodes {
        rda.reachIn[node.ID] = make(map[int]bool)
        rda.reachOut[node.ID] = make(map[int]bool)
    }
    
    // 迭代直到收敛
    changed := true
    for changed {
        changed = false
        
        for _, node := range rda.dfg.Nodes {
            oldReachIn := make(map[int]bool)
            oldReachOut := make(map[int]bool)
            
            // 复制当前值
            for d := range rda.reachIn[node.ID] {
                oldReachIn[d] = true
            }
            for d := range rda.reachOut[node.ID] {
                oldReachOut[d] = true
            }
            
            // 计算新的 reachIn
            rda.computeReachIn(node)
            
            // 计算新的 reachOut
            rda.computeReachOut(node)
            
            // 检查是否改变
            if !rda.equal(oldReachIn, rda.reachIn[node.ID]) || 
               !rda.equal(oldReachOut, rda.reachOut[node.ID]) {
                changed = true
            }
        }
    }
    
    return rda.reachIn, rda.reachOut
}

func (rda *ReachingDefinitionAnalysis) computeReachIn(node *DFGNode) {
    // reachIn[n] = union of reachOut[p] for all predecessors p of n
    for _, edge := range node.InEdges {
        for d := range rda.reachOut[edge.From.ID] {
            rda.reachIn[node.ID][d] = true
        }
    }
}

func (rda *ReachingDefinitionAnalysis) computeReachOut(node *DFGNode) {
    // reachOut[n] = (reachIn[n] - kill[n]) union gen[n]
    
    // 复制 reachIn
    for d := range rda.reachIn[node.ID] {
        rda.reachOut[node.ID][d] = true
    }
    
    // 减去 kill
    rda.killDefinitions(node)
    
    // 加上 gen
    rda.genDefinitions(node)
}
```

## 6. 总结

Go 语言的语法语义分析涵盖了：

1. **语法结构** - 完整的语法元素和类型系统
2. **语义模型** - 语义环境和一致性检查
3. **控制流** - 控制流图构建和分析
4. **执行流** - 执行模型和调度机制
5. **数据流** - 数据流图构建和分析

这些分析为理解 Go 语言的执行语义和进行程序分析提供了理论基础。

# Go 测试进阶与 OTLP 集成

## 目录

- [Go 测试进阶与 OTLP 集成](#go-测试进阶与-otlp-集成)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [测试追踪架构](#测试追踪架构)
  - [2. 表驱动测试](#2-表驱动测试)
    - [2.1 基础表驱动测试](#21-基础表驱动测试)
    - [2.2 表驱动测试与追踪集成](#22-表驱动测试与追踪集成)
    - [2.3 子测试并发执行](#23-子测试并发执行)
  - [3. Fuzzing 模糊测试](#3-fuzzing-模糊测试)
    - [3.1 Fuzz 测试基础](#31-fuzz-测试基础)
    - [3.2 Fuzz 测试追踪](#32-fuzz-测试追踪)
    - [3.3 Fuzz 覆盖率分析](#33-fuzz-覆盖率分析)
  - [4. Mock 高级用法](#4-mock-高级用法)
    - [4.1 接口 Mock](#41-接口-mock)
    - [4.2 HTTP Mock](#42-http-mock)
    - [4.3 Database Mock](#43-database-mock)
  - [5. 集成测试](#5-集成测试)
    - [5.1 集成测试框架](#51-集成测试框架)
    - [5.2 Docker 容器测试](#52-docker-容器测试)
    - [5.3 端到端测试](#53-端到端测试)
  - [6. 性能测试](#6-性能测试)
    - [6.1 Benchmark 基准测试](#61-benchmark-基准测试)
    - [6.2 性能追踪分析](#62-性能追踪分析)
    - [6.3 内存分配分析](#63-内存分配分析)
  - [7. 测试覆盖率](#7-测试覆盖率)
    - [7.1 覆盖率收集](#71-覆盖率收集)
  - [8. Golden File 测试](#8-golden-file-测试)
    - [8.1 Golden File 模式](#81-golden-file-模式)
  - [9. 测试最佳实践](#9-测试最佳实践)
  - [总结](#总结)

---

## 1. 概述

测试是软件质量保障的核心。结合 OTLP,可以:

- **追踪测试执行**:记录每个测试用例的执行过程
- **性能基准**:建立性能基线,检测退化
- **错误分析**:快速定位失败原因

本指南基于 **Go 1.25.1** 和 **OpenTelemetry v1.32.0**。

### 测试追踪架构

```text
┌─────────────────────────────────────┐
│   Go 测试 OTLP 集成架构              │
├─────────────────────────────────────┤
│  单元测试  → Span 追踪              │
│  表驱动    → 批量用例追踪            │
│  Fuzzing   → 输入分析追踪            │
│  Mock      → 调用验证追踪            │
│  Benchmark → 性能指标收集            │
└─────────────────────────────────────┘
```

---

## 2. 表驱动测试

### 2.1 基础表驱动测试

```go
package testing_advanced

import (
    "testing"
    
    "go.opentelemetry.io/otel"
    "go.opentelemetry.io/otel/attribute"
    "go.opentelemetry.io/otel/trace"
)

// 示例函数:加法
func Add(a, b int) int {
    return a + b
}

// 表驱动测试示例
func TestAdd(t *testing.T) {
    tests := []struct {
        name     string
        a, b     int
        expected int
    }{
        {"positive numbers", 2, 3, 5},
        {"negative numbers", -5, -3, -8},
        {"mixed signs", 10, -5, 5},
        {"zero", 0, 0, 0},
    }
    
    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            result := Add(tt.a, tt.b)
            if result != tt.expected {
                t.Errorf("Add(%d, %d) = %d; expected %d", tt.a, tt.b, result, tt.expected)
            }
        })
    }
}
```

### 2.2 表驱动测试与追踪集成

```go
import (
    "context"
    
    sdktrace "go.opentelemetry.io/otel/sdk/trace"
    "go.opentelemetry.io/otel/sdk/trace/tracetest"
)

// TracedTestCase 可追踪的测试用例
type TracedTestCase[T any] struct {
    Name     string
    Input    T
    Expected interface{}
    Setup    func(context.Context) error
    Teardown func(context.Context) error
}

// TracedTestRunner 测试执行器
type TracedTestRunner struct {
    tracer trace.Tracer
    tp     *sdktrace.TracerProvider
}

func NewTracedTestRunner() *TracedTestRunner {
    // 使用内存导出器收集测试追踪
    exporter := tracetest.NewInMemoryExporter()
    tp := sdktrace.NewTracerProvider(
        sdktrace.WithSyncer(exporter),
    )
    
    return &TracedTestRunner{
        tracer: tp.Tracer("test-runner"),
        tp:     tp,
    }
}

// RunTableTests 执行表驱动测试并追踪
func (ttr *TracedTestRunner) RunTableTests(
    t *testing.T,
    testName string,
    tests []TracedTestCase[interface{}],
    fn func(context.Context, interface{}) (interface{}, error),
) {
    ctx := context.Background()
    ctx, span := ttr.tracer.Start(ctx, testName)
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("test.total_cases", len(tests)),
    )
    
    passed := 0
    failed := 0
    
    for _, tt := range tests {
        t.Run(tt.Name, func(t *testing.T) {
            testCtx, testSpan := ttr.tracer.Start(ctx, tt.Name)
            defer testSpan.End()
            
            testSpan.SetAttributes(
                attribute.String("test.name", tt.Name),
            )
            
            // Setup
            if tt.Setup != nil {
                if err := tt.Setup(testCtx); err != nil {
                    t.Fatalf("Setup failed: %v", err)
                    testSpan.RecordError(err)
                    failed++
                    return
                }
            }
            
            // 执行测试
            startTime := time.Now()
            result, err := fn(testCtx, tt.Input)
            duration := time.Since(startTime)
            
            testSpan.SetAttributes(
                attribute.Float64("test.duration_ms", float64(duration.Milliseconds())),
            )
            
            // 验证结果
            if err != nil {
                t.Errorf("Test failed with error: %v", err)
                testSpan.RecordError(err)
                testSpan.SetStatus(codes.Error, err.Error())
                failed++
            } else if !reflect.DeepEqual(result, tt.Expected) {
                err := fmt.Errorf("expected %v, got %v", tt.Expected, result)
                t.Error(err)
                testSpan.RecordError(err)
                testSpan.SetStatus(codes.Error, "assertion failed")
                failed++
            } else {
                testSpan.SetStatus(codes.Ok, "test passed")
                passed++
            }
            
            // Teardown
            if tt.Teardown != nil {
                if err := tt.Teardown(testCtx); err != nil {
                    t.Errorf("Teardown failed: %v", err)
                }
            }
        })
    }
    
    span.SetAttributes(
        attribute.Int("test.passed", passed),
        attribute.Int("test.failed", failed),
    )
}

// 使用示例
func TestAddWithTracing(t *testing.T) {
    runner := NewTracedTestRunner()
    defer runner.tp.Shutdown(context.Background())
    
    tests := []TracedTestCase[interface{}]{
        {
            Name:     "add_positive",
            Input:    []int{2, 3},
            Expected: 5,
        },
        {
            Name:     "add_negative",
            Input:    []int{-5, -3},
            Expected: -8,
        },
    }
    
    runner.RunTableTests(t, "TestAdd", tests, func(ctx context.Context, input interface{}) (interface{}, error) {
        nums := input.([]int)
        return Add(nums[0], nums[1]), nil
    })
}
```

### 2.3 子测试并发执行

```go
// ParallelTestRunner 并发测试执行器
type ParallelTestRunner struct {
    tracer trace.Tracer
}

func NewParallelTestRunner() *ParallelTestRunner {
    return &ParallelTestRunner{
        tracer: otel.Tracer("parallel-test-runner"),
    }
}

// RunParallelTests 并发执行测试
func (ptr *ParallelTestRunner) RunParallelTests(
    t *testing.T,
    tests []TracedTestCase[interface{}],
    fn func(context.Context, interface{}) (interface{}, error),
) {
    ctx := context.Background()
    ctx, span := ptr.tracer.Start(ctx, "parallel-tests")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("test.parallel_count", len(tests)),
    )
    
    for _, tt := range tests {
        tt := tt // 捕获循环变量
        
        t.Run(tt.Name, func(t *testing.T) {
            t.Parallel() // 并发执行
            
            testCtx, testSpan := ptr.tracer.Start(ctx, tt.Name)
            defer testSpan.End()
            
            // 记录 Goroutine ID
            testSpan.SetAttributes(
                attribute.Int64("test.goroutine_id", int64(runtime.NumGoroutine())),
            )
            
            result, err := fn(testCtx, tt.Input)
            
            if err != nil {
                t.Errorf("Test failed: %v", err)
                testSpan.RecordError(err)
            } else if !reflect.DeepEqual(result, tt.Expected) {
                t.Errorf("Expected %v, got %v", tt.Expected, result)
            }
        })
    }
}
```

---

## 3. Fuzzing 模糊测试

### 3.1 Fuzz 测试基础

```go
// Fuzz 测试示例(Go 1.18+)
func FuzzAdd(f *testing.F) {
    // 添加种子语料
    f.Add(2, 3)
    f.Add(-5, 10)
    f.Add(0, 0)
    
    f.Fuzz(func(t *testing.T, a, b int) {
        result := Add(a, b)
        
        // 验证属性:加法交换律
        reverseResult := Add(b, a)
        if result != reverseResult {
            t.Errorf("Add is not commutative: Add(%d,%d)=%d, Add(%d,%d)=%d", 
                a, b, result, b, a, reverseResult)
        }
        
        // 验证属性:加零不变性
        if Add(a, 0) != a {
            t.Errorf("Add(%d, 0) should equal %d", a, a)
        }
    })
}
```

### 3.2 Fuzz 测试追踪

```go
// FuzzTracer Fuzz 测试追踪器
type FuzzTracer struct {
    tracer trace.Tracer
    
    // 统计
    totalExecutions int64
    failures        int64
    uniqueInputs    sync.Map
}

func NewFuzzTracer() *FuzzTracer {
    return &FuzzTracer{
        tracer: otel.Tracer("fuzz-tracer"),
    }
}

// TrackFuzzExecution 追踪 Fuzz 执行
func (ft *FuzzTracer) TrackFuzzExecution(ctx context.Context, input interface{}, fn func() error) {
    ctx, span := ft.tracer.Start(ctx, "fuzz-execution")
    defer span.End()
    
    atomic.AddInt64(&ft.totalExecutions, 1)
    
    // 记录输入
    inputStr := fmt.Sprintf("%v", input)
    ft.uniqueInputs.Store(inputStr, true)
    
    span.SetAttributes(
        attribute.String("fuzz.input", inputStr),
        attribute.Int64("fuzz.execution_count", atomic.LoadInt64(&ft.totalExecutions)),
    )
    
    // 执行测试
    startTime := time.Now()
    err := fn()
    duration := time.Since(startTime)
    
    span.SetAttributes(
        attribute.Float64("fuzz.duration_ms", float64(duration.Microseconds())/1000),
    )
    
    if err != nil {
        atomic.AddInt64(&ft.failures, 1)
        span.RecordError(err)
        span.SetStatus(codes.Error, "fuzz test failed")
    }
}

// GetStats 获取 Fuzz 统计信息
func (ft *FuzzTracer) GetStats() map[string]interface{} {
    uniqueCount := 0
    ft.uniqueInputs.Range(func(key, value interface{}) bool {
        uniqueCount++
        return true
    })
    
    return map[string]interface{}{
        "total_executions": atomic.LoadInt64(&ft.totalExecutions),
        "failures":         atomic.LoadInt64(&ft.failures),
        "unique_inputs":    uniqueCount,
    }
}

// 使用示例
func FuzzAddWithTracing(f *testing.F) {
    fuzzTracer := NewFuzzTracer()
    ctx := context.Background()
    
    f.Add(2, 3)
    
    f.Fuzz(func(t *testing.T, a, b int) {
        fuzzTracer.TrackFuzzExecution(ctx, []int{a, b}, func() error {
            result := Add(a, b)
            reverseResult := Add(b, a)
            
            if result != reverseResult {
                return fmt.Errorf("commutativity violated")
            }
            
            return nil
        })
    })
    
    // 测试结束后输出统计
    stats := fuzzTracer.GetStats()
    f.Log("Fuzz Stats:", stats)
}
```

### 3.3 Fuzz 覆盖率分析

```go
// FuzzCoverageAnalyzer Fuzz 覆盖率分析器
type FuzzCoverageAnalyzer struct {
    tracer trace.Tracer
    
    // 代码路径覆盖
    coveredPaths sync.Map
}

func NewFuzzCoverageAnalyzer() *FuzzCoverageAnalyzer {
    return &FuzzCoverageAnalyzer{
        tracer: otel.Tracer("fuzz-coverage-analyzer"),
    }
}

// TrackCodePath 追踪代码路径
func (fca *FuzzCoverageAnalyzer) TrackCodePath(ctx context.Context, pathID string) {
    fca.coveredPaths.Store(pathID, true)
}

// GetCoverage 获取覆盖率
func (fca *FuzzCoverageAnalyzer) GetCoverage() int {
    count := 0
    fca.coveredPaths.Range(func(key, value interface{}) bool {
        count++
        return true
    })
    return count
}
```

---

## 4. Mock 高级用法

### 4.1 接口 Mock

```go
// UserRepository 用户仓库接口
type UserRepository interface {
    GetUser(ctx context.Context, id int) (*User, error)
    CreateUser(ctx context.Context, user *User) error
}

// MockUserRepository Mock 实现
type MockUserRepository struct {
    tracer trace.Tracer
    
    // Mock 数据
    users      map[int]*User
    callCounts map[string]int
    mu         sync.RWMutex
}

func NewMockUserRepository() *MockUserRepository {
    return &MockUserRepository{
        tracer:     otel.Tracer("mock-user-repo"),
        users:      make(map[int]*User),
        callCounts: make(map[string]int),
    }
}

// GetUser 实现接口
func (mur *MockUserRepository) GetUser(ctx context.Context, id int) (*User, error) {
    ctx, span := mur.tracer.Start(ctx, "mock.GetUser")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("mock.user_id", id),
    )
    
    mur.mu.Lock()
    mur.callCounts["GetUser"]++
    mur.mu.Unlock()
    
    mur.mu.RLock()
    user, exists := mur.users[id]
    mur.mu.RUnlock()
    
    if !exists {
        err := fmt.Errorf("user not found")
        span.RecordError(err)
        return nil, err
    }
    
    return user, nil
}

// CreateUser 实现接口
func (mur *MockUserRepository) CreateUser(ctx context.Context, user *User) error {
    ctx, span := mur.tracer.Start(ctx, "mock.CreateUser")
    defer span.End()
    
    span.SetAttributes(
        attribute.Int("mock.user_id", user.ID),
        attribute.String("mock.username", user.Username),
    )
    
    mur.mu.Lock()
    defer mur.mu.Unlock()
    
    mur.callCounts["CreateUser"]++
    mur.users[user.ID] = user
    
    return nil
}

// AssertCalled 验证方法被调用
func (mur *MockUserRepository) AssertCalled(t *testing.T, method string, times int) {
    mur.mu.RLock()
    defer mur.mu.RUnlock()
    
    count := mur.callCounts[method]
    if count != times {
        t.Errorf("Expected %s to be called %d times, but was called %d times", method, times, count)
    }
}

// 使用示例
func TestUserService(t *testing.T) {
    mockRepo := NewMockUserRepository()
    
    // 准备测试数据
    testUser := &User{ID: 1, Username: "testuser"}
    mockRepo.CreateUser(context.Background(), testUser)
    
    // 测试获取用户
    user, err := mockRepo.GetUser(context.Background(), 1)
    if err != nil {
        t.Fatalf("Expected no error, got %v", err)
    }
    
    if user.Username != "testuser" {
        t.Errorf("Expected username 'testuser', got %s", user.Username)
    }
    
    // 验证调用次数
    mockRepo.AssertCalled(t, "GetUser", 1)
    mockRepo.AssertCalled(t, "CreateUser", 1)
}
```

### 4.2 HTTP Mock

```go
// MockHTTPClient Mock HTTP 客户端
type MockHTTPClient struct {
    tracer trace.Tracer
    
    // Mock 响应
    responses map[string]*http.Response
    mu        sync.RWMutex
}

func NewMockHTTPClient() *MockHTTPClient {
    return &MockHTTPClient{
        tracer:    otel.Tracer("mock-http-client"),
        responses: make(map[string]*http.Response),
    }
}

// On 注册 Mock 响应
func (mhc *MockHTTPClient) On(url string, response *http.Response) {
    mhc.mu.Lock()
    defer mhc.mu.Unlock()
    
    mhc.responses[url] = response
}

// Do 实现 HTTP 请求
func (mhc *MockHTTPClient) Do(req *http.Request) (*http.Response, error) {
    ctx, span := mhc.tracer.Start(req.Context(), "mock.HTTP.Do")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("http.method", req.Method),
        attribute.String("http.url", req.URL.String()),
    )
    
    mhc.mu.RLock()
    response, exists := mhc.responses[req.URL.String()]
    mhc.mu.RUnlock()
    
    if !exists {
        err := fmt.Errorf("no mock response for %s", req.URL.String())
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.Int("http.status_code", response.StatusCode),
    )
    
    return response, nil
}

// 使用示例
func TestHTTPClient(t *testing.T) {
    mockClient := NewMockHTTPClient()
    
    // 注册 Mock 响应
    mockClient.On("https://api.example.com/users/1", &http.Response{
        StatusCode: 200,
        Body:       io.NopCloser(strings.NewReader(`{"id":1,"name":"John"}`)),
    })
    
    // 测试请求
    req, _ := http.NewRequest("GET", "https://api.example.com/users/1", nil)
    resp, err := mockClient.Do(req)
    
    if err != nil {
        t.Fatalf("Expected no error, got %v", err)
    }
    
    if resp.StatusCode != 200 {
        t.Errorf("Expected status 200, got %d", resp.StatusCode)
    }
}
```

### 4.3 Database Mock

```go
// MockDB Mock 数据库
type MockDB struct {
    tracer trace.Tracer
    
    // Mock 结果
    queryResults map[string][]interface{}
    execResults  map[string]sql.Result
    mu           sync.RWMutex
}

func NewMockDB() *MockDB {
    return &MockDB{
        tracer:       otel.Tracer("mock-db"),
        queryResults: make(map[string][]interface{}),
        execResults:  make(map[string]sql.Result),
    }
}

// ExpectQuery 注册查询结果
func (mdb *MockDB) ExpectQuery(query string, results []interface{}) {
    mdb.mu.Lock()
    defer mdb.mu.Unlock()
    
    mdb.queryResults[query] = results
}

// Query 执行查询
func (mdb *MockDB) Query(ctx context.Context, query string, args ...interface{}) ([]interface{}, error) {
    ctx, span := mdb.tracer.Start(ctx, "mock.DB.Query")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("db.query", query),
        attribute.Int("db.args_count", len(args)),
    )
    
    mdb.mu.RLock()
    results, exists := mdb.queryResults[query]
    mdb.mu.RUnlock()
    
    if !exists {
        err := fmt.Errorf("no mock result for query: %s", query)
        span.RecordError(err)
        return nil, err
    }
    
    span.SetAttributes(
        attribute.Int("db.result_count", len(results)),
    )
    
    return results, nil
}
```

---

## 5. 集成测试

### 5.1 集成测试框架

```go
// IntegrationTestSuite 集成测试套件
type IntegrationTestSuite struct {
    tracer trace.Tracer
    
    // 测试环境
    dbConn    *sql.DB
    redisConn *redis.Client
    httpServer *http.Server
}

func NewIntegrationTestSuite() *IntegrationTestSuite {
    return &IntegrationTestSuite{
        tracer: otel.Tracer("integration-test-suite"),
    }
}

// Setup 设置测试环境
func (its *IntegrationTestSuite) Setup(ctx context.Context) error {
    ctx, span := its.tracer.Start(ctx, "integration-test.Setup")
    defer span.End()
    
    // 初始化数据库
    db, err := sql.Open("postgres", "postgres://test:test@localhost/testdb")
    if err != nil {
        span.RecordError(err)
        return err
    }
    its.dbConn = db
    
    // 初始化 Redis
    its.redisConn = redis.NewClient(&redis.Options{
        Addr: "localhost:6379",
    })
    
    // 初始化 HTTP 服务器
    its.httpServer = &http.Server{
        Addr: ":8080",
    }
    
    go its.httpServer.ListenAndServe()
    
    span.SetStatus(codes.Ok, "setup complete")
    return nil
}

// Teardown 清理测试环境
func (its *IntegrationTestSuite) Teardown(ctx context.Context) error {
    ctx, span := its.tracer.Start(ctx, "integration-test.Teardown")
    defer span.End()
    
    if its.dbConn != nil {
        its.dbConn.Close()
    }
    
    if its.redisConn != nil {
        its.redisConn.Close()
    }
    
    if its.httpServer != nil {
        its.httpServer.Shutdown(ctx)
    }
    
    return nil
}

// RunTest 执行集成测试
func (its *IntegrationTestSuite) RunTest(t *testing.T, testName string, fn func(context.Context) error) {
    ctx := context.Background()
    ctx, span := its.tracer.Start(ctx, "integration-test."+testName)
    defer span.End()
    
    if err := fn(ctx); err != nil {
        t.Errorf("Integration test failed: %v", err)
        span.RecordError(err)
    }
}
```

### 5.2 Docker 容器测试

```go
// DockerTestContainer Docker 测试容器
type DockerTestContainer struct {
    tracer trace.Tracer
    
    containerID string
    image       string
}

func NewDockerTestContainer(image string) *DockerTestContainer {
    return &DockerTestContainer{
        tracer: otel.Tracer("docker-test-container"),
        image:  image,
    }
}

// Start 启动容器
func (dtc *DockerTestContainer) Start(ctx context.Context) error {
    ctx, span := dtc.tracer.Start(ctx, "docker.StartContainer")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("docker.image", dtc.image),
    )
    
    // 使用 docker CLI 启动容器(简化示例)
    cmd := exec.CommandContext(ctx, "docker", "run", "-d", dtc.image)
    
    output, err := cmd.Output()
    if err != nil {
        span.RecordError(err)
        return err
    }
    
    dtc.containerID = strings.TrimSpace(string(output))
    
    span.SetAttributes(
        attribute.String("docker.container_id", dtc.containerID),
    )
    
    return nil
}

// Stop 停止容器
func (dtc *DockerTestContainer) Stop(ctx context.Context) error {
    ctx, span := dtc.tracer.Start(ctx, "docker.StopContainer")
    defer span.End()
    
    cmd := exec.CommandContext(ctx, "docker", "stop", dtc.containerID)
    
    if err := cmd.Run(); err != nil {
        span.RecordError(err)
        return err
    }
    
    return nil
}
```

### 5.3 端到端测试

```go
// E2ETestRunner 端到端测试执行器
type E2ETestRunner struct {
    tracer trace.Tracer
    
    baseURL string
    client  *http.Client
}

func NewE2ETestRunner(baseURL string) *E2ETestRunner {
    return &E2ETestRunner{
        tracer:  otel.Tracer("e2e-test-runner"),
        baseURL: baseURL,
        client:  &http.Client{Timeout: 10 * time.Second},
    }
}

// TestUserFlow 测试用户流程
func (etr *E2ETestRunner) TestUserFlow(t *testing.T) {
    ctx := context.Background()
    ctx, span := etr.tracer.Start(ctx, "e2e.UserFlow")
    defer span.End()
    
    // 1. 注册用户
    registerResp, err := etr.client.Post(
        etr.baseURL+"/api/register",
        "application/json",
        strings.NewReader(`{"username":"testuser","password":"test123"}`),
    )
    if err != nil {
        t.Fatalf("Registration failed: %v", err)
    }
    defer registerResp.Body.Close()
    
    span.AddEvent("user-registered", trace.WithAttributes(
        attribute.Int("http.status_code", registerResp.StatusCode),
    ))
    
    // 2. 登录
    loginResp, err := etr.client.Post(
        etr.baseURL+"/api/login",
        "application/json",
        strings.NewReader(`{"username":"testuser","password":"test123"}`),
    )
    if err != nil {
        t.Fatalf("Login failed: %v", err)
    }
    defer loginResp.Body.Close()
    
    span.AddEvent("user-logged-in", trace.WithAttributes(
        attribute.Int("http.status_code", loginResp.StatusCode),
    ))
    
    // 3. 访问受保护资源
    // ... (省略)
    
    span.SetStatus(codes.Ok, "e2e test passed")
}
```

---

## 6. 性能测试

### 6.1 Benchmark 基准测试

```go
// BenchmarkAdd 基准测试
func BenchmarkAdd(b *testing.B) {
    b.ReportAllocs() // 报告内存分配
    
    for i := 0; i < b.N; i++ {
        Add(2, 3)
    }
}

// BenchmarkAddParallel 并发基准测试
func BenchmarkAddParallel(b *testing.B) {
    b.RunParallel(func(pb *testing.PB) {
        for pb.Next() {
            Add(2, 3)
        }
    })
}
```

### 6.2 性能追踪分析

```go
// BenchmarkTracer 性能测试追踪器
type BenchmarkTracer struct {
    tracer trace.Tracer
    meter  metric.Meter
    
    // Metrics
    opsPerSecond metric.Float64Histogram
    allocBytes   metric.Int64Histogram
}

func NewBenchmarkTracer() (*BenchmarkTracer, error) {
    meter := otel.Meter("benchmark-tracer")
    
    opsPerSecond, err := meter.Float64Histogram(
        "benchmark.ops_per_second",
        metric.WithDescription("Operations per second"),
    )
    if err != nil {
        return nil, err
    }
    
    allocBytes, err := meter.Int64Histogram(
        "benchmark.alloc_bytes",
        metric.WithDescription("Bytes allocated per operation"),
        metric.WithUnit("By"),
    )
    if err != nil {
        return nil, err
    }
    
    return &BenchmarkTracer{
        tracer:       otel.Tracer("benchmark-tracer"),
        meter:        meter,
        opsPerSecond: opsPerSecond,
        allocBytes:   allocBytes,
    }, nil
}

// TraceBenchmark 追踪基准测试
func (bt *BenchmarkTracer) TraceBenchmark(b *testing.B, name string, fn func()) {
    ctx := context.Background()
    ctx, span := bt.tracer.Start(ctx, "benchmark."+name)
    defer span.End()
    
    b.ResetTimer()
    
    startTime := time.Now()
    
    var m1, m2 runtime.MemStats
    runtime.ReadMemStats(&m1)
    
    for i := 0; i < b.N; i++ {
        fn()
    }
    
    runtime.ReadMemStats(&m2)
    
    duration := time.Since(startTime)
    
    // 计算性能指标
    opsPerSec := float64(b.N) / duration.Seconds()
    allocPerOp := int64(m2.TotalAlloc-m1.TotalAlloc) / int64(b.N)
    
    // 记录指标
    bt.opsPerSecond.Record(ctx, opsPerSec)
    bt.allocBytes.Record(ctx, allocPerOp)
    
    // 记录到 Span
    span.SetAttributes(
        attribute.Int("benchmark.iterations", b.N),
        attribute.Float64("benchmark.duration_sec", duration.Seconds()),
        attribute.Float64("benchmark.ops_per_sec", opsPerSec),
        attribute.Int64("benchmark.alloc_bytes_per_op", allocPerOp),
    )
}
```

### 6.3 内存分配分析

```go
// MemoryProfiler 内存分析器
type MemoryProfiler struct {
    tracer trace.Tracer
}

func NewMemoryProfiler() *MemoryProfiler {
    return &MemoryProfiler{
        tracer: otel.Tracer("memory-profiler"),
    }
}

// ProfileAllocation 分析内存分配
func (mp *MemoryProfiler) ProfileAllocation(ctx context.Context, name string, fn func()) {
    ctx, span := mp.tracer.Start(ctx, "memory-profile."+name)
    defer span.End()
    
    var m1, m2 runtime.MemStats
    
    runtime.ReadMemStats(&m1)
    fn()
    runtime.ReadMemStats(&m2)
    
    // 记录内存指标
    span.SetAttributes(
        attribute.Int64("memory.alloc_bytes", int64(m2.Alloc-m1.Alloc)),
        attribute.Int64("memory.total_alloc_bytes", int64(m2.TotalAlloc-m1.TotalAlloc)),
        attribute.Int64("memory.sys_bytes", int64(m2.Sys-m1.Sys)),
        attribute.Int64("memory.mallocs", int64(m2.Mallocs-m1.Mallocs)),
        attribute.Int64("memory.frees", int64(m2.Frees-m1.Frees)),
    )
}
```

---

## 7. 测试覆盖率

### 7.1 覆盖率收集

```go
// CoverageCollector 覆盖率收集器
type CoverageCollector struct {
    tracer trace.Tracer
    
    // 覆盖的行
    coveredLines map[string]map[int]bool
    totalLines   map[string]int
    mu           sync.RWMutex
}

func NewCoverageCollector() *CoverageCollector {
    return &CoverageCollector{
        tracer:       otel.Tracer("coverage-collector"),
        coveredLines: make(map[string]map[int]bool),
        totalLines:   make(map[string]int),
    }
}

// MarkLineCovered 标记行被覆盖
func (cc *CoverageCollector) MarkLineCovered(file string, line int) {
    cc.mu.Lock()
    defer cc.mu.Unlock()
    
    if _, exists := cc.coveredLines[file]; !exists {
        cc.coveredLines[file] = make(map[int]bool)
    }
    
    cc.coveredLines[file][line] = true
}

// GetCoverage 获取覆盖率
func (cc *CoverageCollector) GetCoverage() map[string]float64 {
    cc.mu.RLock()
    defer cc.mu.RUnlock()
    
    coverage := make(map[string]float64)
    
    for file, lines := range cc.coveredLines {
        total := cc.totalLines[file]
        if total == 0 {
            continue
        }
        
        covered := len(lines)
        coverage[file] = float64(covered) / float64(total) * 100
    }
    
    return coverage
}

// ReportCoverage 报告覆盖率到 Span
func (cc *CoverageCollector) ReportCoverage(ctx context.Context) {
    ctx, span := cc.tracer.Start(ctx, "report-coverage")
    defer span.End()
    
    coverage := cc.GetCoverage()
    
    totalCovered := 0
    totalLines := 0
    
    for file, percent := range coverage {
        span.AddEvent("file-coverage", trace.WithAttributes(
            attribute.String("file", file),
            attribute.Float64("coverage_percent", percent),
        ))
        
        covered := len(cc.coveredLines[file])
        total := cc.totalLines[file]
        
        totalCovered += covered
        totalLines += total
    }
    
    overallCoverage := float64(totalCovered) / float64(totalLines) * 100
    
    span.SetAttributes(
        attribute.Float64("coverage.overall_percent", overallCoverage),
        attribute.Int("coverage.total_lines", totalLines),
        attribute.Int("coverage.covered_lines", totalCovered),
    )
}
```

---

## 8. Golden File 测试

### 8.1 Golden File 模式

```go
// GoldenFileTest Golden File 测试
type GoldenFileTest struct {
    tracer trace.Tracer
    
    goldenDir string
}

func NewGoldenFileTest(goldenDir string) *GoldenFileTest {
    return &GoldenFileTest{
        tracer:    otel.Tracer("golden-file-test"),
        goldenDir: goldenDir,
    }
}

// AssertGolden 断言与 Golden File 一致
func (gft *GoldenFileTest) AssertGolden(t *testing.T, name string, actual []byte, update bool) {
    ctx, span := gft.tracer.Start(context.Background(), "golden-file.Assert")
    defer span.End()
    
    span.SetAttributes(
        attribute.String("golden.name", name),
        attribute.Int("golden.actual_size", len(actual)),
        attribute.Bool("golden.update", update),
    )
    
    goldenPath := filepath.Join(gft.goldenDir, name+".golden")
    
    if update {
        // 更新 Golden File
        if err := os.WriteFile(goldenPath, actual, 0644); err != nil {
            t.Fatalf("Failed to update golden file: %v", err)
            span.RecordError(err)
        }
        span.AddEvent("golden-file-updated")
        return
    }
    
    // 读取 Golden File
    expected, err := os.ReadFile(goldenPath)
    if err != nil {
        t.Fatalf("Failed to read golden file: %v", err)
        span.RecordError(err)
        return
    }
    
    span.SetAttributes(
        attribute.Int("golden.expected_size", len(expected)),
    )
    
    // 比较
    if !bytes.Equal(actual, expected) {
        t.Errorf("Golden file mismatch for %s\nExpected:\n%s\nActual:\n%s", 
            name, string(expected), string(actual))
        span.SetStatus(codes.Error, "golden file mismatch")
    }
}

// 使用示例
func TestRenderHTML(t *testing.T) {
    goldenTest := NewGoldenFileTest("testdata/golden")
    
    html := RenderHTML(map[string]interface{}{
        "title": "Test Page",
        "body":  "Hello, World!",
    })
    
    goldenTest.AssertGolden(t, "render_html", []byte(html), false)
}
```

---

## 9. 测试最佳实践

```go
// TestBestPractices 测试最佳实践示例
func TestBestPractices(t *testing.T) {
    // 1. 使用 t.Parallel() 并发执行
    t.Parallel()
    
    // 2. 使用 t.Helper() 标记辅助函数
    assertUser := func(t *testing.T, user *User, expectedName string) {
        t.Helper()
        if user.Username != expectedName {
            t.Errorf("Expected username %s, got %s", expectedName, user.Username)
        }
    }
    
    // 3. 使用 t.Cleanup() 清理资源
    tmpFile, _ := os.CreateTemp("", "test-*.txt")
    t.Cleanup(func() {
        os.Remove(tmpFile.Name())
    })
    
    // 4. 使用表驱动测试
    tests := []struct {
        name     string
        input    int
        expected int
    }{
        {"positive", 5, 5},
        {"negative", -5, -5},
        {"zero", 0, 0},
    }
    
    for _, tt := range tests {
        t.Run(tt.name, func(t *testing.T) {
            result := abs(tt.input)
            if result != tt.expected {
                t.Errorf("Expected %d, got %d", tt.expected, result)
            }
        })
    }
}

func abs(n int) int {
    if n < 0 {
        return -n
    }
    return n
}
```

---

## 总结

本指南涵盖了 Go 1.25.1 测试进阶与 OTLP 集成:

1. **表驱动测试**:结构化测试用例、追踪集成、并发执行
2. **Fuzzing**:模糊测试基础、执行追踪、覆盖率分析
3. **Mock**:接口 Mock、HTTP Mock、Database Mock
4. **集成测试**:测试套件、Docker 容器、端到端测试
5. **性能测试**:Benchmark、性能追踪、内存分析
6. **测试覆盖率**:覆盖率收集、追踪、可视化
7. **Golden File**:快照测试、回归测试
8. **最佳实践**:并发、辅助函数、清理资源

通过测试追踪,可实现 **测试可观测性** 和 **质量度量自动化**。

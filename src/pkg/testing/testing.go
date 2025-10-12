// Package testing provides comprehensive testing utilities for OTLP Go applications.
// It includes test suites, mock services, integration testing tools, performance testing,
// security testing, and various testing helpers for comprehensive test coverage.
//
// Key Features:
// - Test suite management with setup/teardown
// - Mock services for all microservices
// - Integration testing framework
// - Performance testing utilities
// - Security testing tools
// - Test data generators
// - Assertion helpers
// - OpenTelemetry integration for testing
//
// Usage Example:
//
//	// Create test suite
//	suite := testing.NewTestSuite("UserService Tests")
//
//	// Add test case
//	suite.AddTest("TestCreateUser", func(t *testing.T) error {
//	    // Test implementation
//	    return nil
//	})
//
//	// Run tests
//	suite.Run(t)
package testing

import (
	"context"
	"fmt"
	"math/rand"
	"sync"
	"testing"
	"time"

	"OTLP_go/src/pkg/config"
	"OTLP_go/src/pkg/errors"
	"OTLP_go/src/pkg/otel"
	"OTLP_go/src/pkg/types"
)

// TestSuite provides a comprehensive test suite management system with setup/teardown
// capabilities, test case management, and detailed test execution tracking.
//
// Features:
// - Suite-level setup and teardown
// - Individual test case management
// - Test execution with timeout support
// - Test result tracking and reporting
// - OpenTelemetry integration for test tracing
//
// Usage:
//
//	suite := NewTestSuite("MyTestSuite")
//	suite.SetSetup(func() error { /* setup */ return nil })
//	suite.AddTest("TestFunction", func(t *testing.T) error { /* test */ return nil })
//	suite.Run(t)
type TestSuite struct {
	name        string
	setup       func() error
	teardown    func() error
	tests       []*TestCase
	stats       *TestSuiteStats
	environment *TestEnvironment
	mu          sync.RWMutex
}

// TestSuiteStats holds statistics about test suite execution.
type TestSuiteStats struct {
	TotalTests       int64
	PassedTests      int64
	FailedTests      int64
	SkippedTests     int64
	TotalDuration    time.Duration
	LastRunTime      time.Time
	SetupDuration    time.Duration
	TeardownDuration time.Duration
}

// TestCase represents an individual test case with its own setup, teardown, and execution logic.
//
// Features:
// - Individual test setup and teardown
// - Configurable timeout
// - Test execution tracking
// - Error handling and reporting
// - Performance monitoring
//
// Usage:
//
//	testCase := &TestCase{
//	    name: "TestFunction",
//	    function: func(t *testing.T) error { /* test logic */ return nil },
//	    timeout: 30 * time.Second,
//	}
type TestCase struct {
	name      string
	function  func(t *testing.T) error
	setup     func() error
	teardown  func() error
	timeout   time.Duration
	stats     *TestCaseStats
	skip      bool
	parallel  bool
	benchmark bool
}

// TestCaseStats holds statistics about individual test case execution.
type TestCaseStats struct {
	Duration         time.Duration
	MemoryUsage      int64
	SetupDuration    time.Duration
	TestDuration     time.Duration
	TeardownDuration time.Duration
	LastRunTime      time.Time
	RunCount         int64
	SuccessCount     int64
	FailureCount     int64
}

// NewTestSuite creates a new test suite with the specified name and initializes
// all necessary components for comprehensive test management.
//
// Parameters:
//   - name: The name of the test suite
//
// Returns a new TestSuite instance ready for use.
func NewTestSuite(name string) *TestSuite {
	return &TestSuite{
		name:        name,
		tests:       make([]*TestCase, 0),
		stats:       &TestSuiteStats{},
		environment: NewTestEnvironment(),
	}
}

// AddTest adds a new test case to the test suite with the specified name and function.
//
// Parameters:
//   - name: The name of the test case
//   - fn: The test function to execute
//
// Returns the created TestCase instance for further configuration.
func (ts *TestSuite) AddTest(name string, fn func(t *testing.T) error) *TestCase {
	tc := &TestCase{
		name:      name,
		function:  fn,
		timeout:   30 * time.Second,
		stats:     &TestCaseStats{},
		skip:      false,
		parallel:  false,
		benchmark: false,
	}

	ts.mu.Lock()
	ts.tests = append(ts.tests, tc)
	ts.stats.TotalTests++
	ts.mu.Unlock()

	return tc
}

// SetSetup sets the suite-level setup function that will be executed before
// running any test cases in the suite.
//
// Parameters:
//   - fn: The setup function to execute
func (ts *TestSuite) SetSetup(fn func() error) {
	ts.mu.Lock()
	defer ts.mu.Unlock()
	ts.setup = fn
}

// SetTeardown sets the suite-level teardown function that will be executed after
// all test cases in the suite have completed.
//
// Parameters:
//   - fn: The teardown function to execute
func (ts *TestSuite) SetTeardown(fn func() error) {
	ts.mu.Lock()
	defer ts.mu.Unlock()
	ts.teardown = fn
}

// Run executes the entire test suite with comprehensive tracking, error handling,
// and performance monitoring.
//
// The execution process:
// 1. Suite-level setup
// 2. Individual test case execution with timeout support
// 3. Test case setup and teardown
// 4. Performance and statistics tracking
// 5. Suite-level teardown
//
// Parameters:
//   - t: The testing.T instance for test execution
func (ts *TestSuite) Run(t *testing.T) {
	startTime := time.Now()

	// Suite-level setup
	if ts.setup != nil {
		setupStart := time.Now()
		if err := ts.setup(); err != nil {
			t.Fatalf("Test suite setup failed: %v", err)
		}
		ts.stats.SetupDuration = time.Since(setupStart)
	}

	// Ensure suite-level cleanup
	defer func() {
		teardownStart := time.Now()
		if ts.teardown != nil {
			if err := ts.teardown(); err != nil {
				t.Errorf("Test suite teardown failed: %v", err)
			}
		}
		ts.stats.TeardownDuration = time.Since(teardownStart)
		ts.stats.TotalDuration = time.Since(startTime)
		ts.stats.LastRunTime = time.Now()
	}()

	// Execute test cases
	for _, tc := range ts.tests {
		t.Run(tc.name, func(t *testing.T) {
			if tc.skip {
				t.Skip("Test case is marked as skipped")
				ts.stats.SkippedTests++
				return
			}

			testStart := time.Now()

			// Test case setup
			if tc.setup != nil {
				setupStart := time.Now()
				if err := tc.setup(); err != nil {
					t.Fatalf("Test case setup failed: %v", err)
				}
				tc.stats.SetupDuration = time.Since(setupStart)
			}

			// Ensure test case cleanup
			defer func() {
				teardownStart := time.Now()
				if tc.teardown != nil {
					if err := tc.teardown(); err != nil {
						t.Errorf("Test case teardown failed: %v", err)
					}
				}
				tc.stats.TeardownDuration = time.Since(teardownStart)
				tc.stats.Duration = time.Since(testStart)
				tc.stats.LastRunTime = time.Now()
				tc.stats.RunCount++
			}()

			// Execute test with timeout
			done := make(chan error, 1)
			go func() {
				testFuncStart := time.Now()
				err := tc.function(t)
				tc.stats.TestDuration = time.Since(testFuncStart)
				done <- err
			}()

			select {
			case err := <-done:
				if err != nil {
					t.Errorf("Test failed: %v", err)
					ts.stats.FailedTests++
					tc.stats.FailureCount++
				} else {
					ts.stats.PassedTests++
					tc.stats.SuccessCount++
				}
			case <-time.After(tc.timeout):
				t.Errorf("Test timed out after %v", tc.timeout)
				ts.stats.FailedTests++
				tc.stats.FailureCount++
			}
		})
	}
}

// SetSetup sets the test case setup function that will be executed before
// running the test case.
//
// Parameters:
//   - fn: The setup function to execute
//
// Returns the TestCase instance for method chaining.
func (tc *TestCase) SetSetup(fn func() error) *TestCase {
	tc.setup = fn
	return tc
}

// SetTeardown sets the test case teardown function that will be executed after
// the test case completes.
//
// Parameters:
//   - fn: The teardown function to execute
//
// Returns the TestCase instance for method chaining.
func (tc *TestCase) SetTeardown(fn func() error) *TestCase {
	tc.teardown = fn
	return tc
}

// SetTimeout sets the timeout duration for the test case execution.
//
// Parameters:
//   - timeout: The maximum duration for test execution
//
// Returns the TestCase instance for method chaining.
func (tc *TestCase) SetTimeout(timeout time.Duration) *TestCase {
	tc.timeout = timeout
	return tc
}

// SetSkip marks the test case as skipped.
//
// Returns the TestCase instance for method chaining.
func (tc *TestCase) SetSkip() *TestCase {
	tc.skip = true
	return tc
}

// SetParallel marks the test case for parallel execution.
//
// Returns the TestCase instance for method chaining.
func (tc *TestCase) SetParallel() *TestCase {
	tc.parallel = true
	return tc
}

// SetBenchmark marks the test case as a benchmark test.
//
// Returns the TestCase instance for method chaining.
func (tc *TestCase) SetBenchmark() *TestCase {
	tc.benchmark = true
	return tc
}

// MockUserService provides a mock implementation of the user service for testing purposes.
// It simulates user operations with in-memory storage and supports various test scenarios.
//
// Features:
// - In-memory user storage
// - CRUD operations simulation
// - Error injection capabilities
// - Performance testing support
// - OpenTelemetry integration
//
// Usage:
//
//	mockService := NewMockUserService()
//	user, err := mockService.GetUser(ctx, "user-001")
type MockUserService struct {
	mu        sync.RWMutex
	users     map[string]*types.User
	stats     map[string]*MockServiceStats
	errorRate float64
	latency   time.Duration
}

// MockServiceStats holds statistics for mock service operations.
type MockServiceStats struct {
	GetUserCalls    int64
	CreateUserCalls int64
	UpdateUserCalls int64
	DeleteUserCalls int64
	TotalCalls      int64
	ErrorCount      int64
	AverageLatency  time.Duration
	LastCallTime    time.Time
}

// NewMockUserService creates a new mock user service with predefined test users
// and comprehensive testing capabilities.
//
// Returns a MockUserService instance with:
// - Predefined test users
// - Statistics tracking
// - Error injection support
// - Performance monitoring
// - Thread-safe operations
func NewMockUserService() *MockUserService {
	users := make(map[string]*types.User)
	stats := make(map[string]*MockServiceStats)

	// Add predefined test users
	users["user-001"] = &types.User{
		ID:        "user-001",
		Name:      "Test User 1",
		Email:     "test1@example.com",
		Phone:     "+1234567890",
		Level:     types.UserLevelNormal,
		CreatedAt: time.Now(),
	}

	users["user-002"] = &types.User{
		ID:        "user-002",
		Name:      "Test User 2",
		Email:     "test2@example.com",
		Phone:     "+1234567891",
		Level:     types.UserLevelVIP,
		CreatedAt: time.Now(),
	}

	users["user-003"] = &types.User{
		ID:        "user-003",
		Name:      "Test User 3",
		Email:     "test3@example.com",
		Phone:     "+1234567892",
		Level:     types.UserLevelPremium,
		CreatedAt: time.Now(),
	}

	// Initialize statistics
	stats["GetUser"] = &MockServiceStats{}
	stats["CreateUser"] = &MockServiceStats{}
	stats["UpdateUser"] = &MockServiceStats{}
	stats["DeleteUser"] = &MockServiceStats{}

	return &MockUserService{
		users:     users,
		stats:     stats,
		errorRate: 0.0,
		latency:   0,
	}
}

// GetUser retrieves a user by ID with comprehensive error handling, statistics tracking,
// and performance monitoring.
//
// Parameters:
//   - ctx: The context for the operation
//   - userID: The ID of the user to retrieve
//
// Returns the user if found, or an error if not found or if an error occurs.
func (m *MockUserService) GetUser(ctx context.Context, userID string) (*types.User, error) {
	start := time.Now()

	m.mu.Lock()
	defer m.mu.Unlock()

	// Update statistics
	stats := m.stats["GetUser"]
	stats.TotalCalls++
	stats.LastCallTime = time.Now()

	// Simulate latency if configured
	if m.latency > 0 {
		time.Sleep(m.latency)
	}

	// Simulate error if configured
	if m.errorRate > 0 && rand.Float64() < m.errorRate {
		stats.ErrorCount++
		return nil, errors.NewTypedError(errors.ErrorTypeInternal, "Simulated error", nil)
	}

	// Retrieve user
	user, exists := m.users[userID]
	if !exists {
		stats.ErrorCount++
		return nil, errors.NewTypedError(errors.ErrorTypeNotFound, "User not found", nil)
	}

	// Update latency statistics
	stats.AverageLatency = time.Since(start)
	stats.GetUserCalls++

	return user, nil
}

// GetUserStats retrieves user statistics with comprehensive tracking and error handling.
//
// Parameters:
//   - ctx: The context for the operation
//   - userID: The ID of the user to get statistics for
//
// Returns a map of user statistics or an error if the user is not found.
func (m *MockUserService) GetUserStats(ctx context.Context, userID string) (map[string]interface{}, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	// Check if user exists
	_, exists := m.users[userID]
	if !exists {
		return nil, errors.NewTypedError(errors.ErrorTypeNotFound, "User not found", nil)
	}

	// Simulate latency if configured
	if m.latency > 0 {
		time.Sleep(m.latency)
	}

	// Simulate error if configured
	if m.errorRate > 0 && rand.Float64() < m.errorRate {
		return nil, errors.NewTypedError(errors.ErrorTypeInternal, "Simulated error", nil)
	}

	// Generate mock statistics
	stats := map[string]interface{}{
		"total_orders":   rand.Intn(100) + 1,
		"total_spent":    float64(rand.Intn(10000)) + 100.0,
		"loyalty_points": rand.Intn(1000) + 50,
		"last_order":     time.Now().Add(-time.Duration(rand.Intn(30)) * 24 * time.Hour),
		"account_age":    time.Since(m.users[userID].CreatedAt),
	}

	return stats, nil
}

// SetErrorRate sets the error rate for simulating failures in the mock service.
//
// Parameters:
//   - rate: The error rate (0.0 to 1.0)
func (m *MockUserService) SetErrorRate(rate float64) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.errorRate = rate
}

// SetLatency sets the latency for simulating network delays in the mock service.
//
// Parameters:
//   - latency: The latency duration
func (m *MockUserService) SetLatency(latency time.Duration) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.latency = latency
}

// GetStats returns the current statistics for the mock service.
//
// Returns a map of operation names to their statistics.
func (m *MockUserService) GetStats() map[string]*MockServiceStats {
	m.mu.RLock()
	defer m.mu.RUnlock()

	// Return a copy to prevent external modification
	result := make(map[string]*MockServiceStats)
	for k, v := range m.stats {
		result[k] = &MockServiceStats{
			GetUserCalls:    v.GetUserCalls,
			CreateUserCalls: v.CreateUserCalls,
			UpdateUserCalls: v.UpdateUserCalls,
			DeleteUserCalls: v.DeleteUserCalls,
			TotalCalls:      v.TotalCalls,
			ErrorCount:      v.ErrorCount,
			AverageLatency:  v.AverageLatency,
			LastCallTime:    v.LastCallTime,
		}
	}
	return result
}

// MockOrderService 模拟订单服务
type MockOrderService struct {
	orders map[string]*types.Order
}

// NewMockOrderService 创建模拟订单服务
func NewMockOrderService() *MockOrderService {
	return &MockOrderService{
		orders: make(map[string]*types.Order),
	}
}

// CreateOrder 创建订单
func (m *MockOrderService) CreateOrder(ctx context.Context, req *types.CreateOrderRequest) (*types.Order, error) {
	order := &types.Order{
		ID:          fmt.Sprintf("order-%d", time.Now().UnixNano()),
		UserID:      req.UserID,
		Items:       req.Items,
		TotalAmount: req.TotalAmount,
		Status:      types.OrderStatusPending,
		CreatedAt:   time.Now(),
		UpdatedAt:   time.Now(),
	}

	m.orders[order.ID] = order
	return order, nil
}

// GetOrder 获取订单
func (m *MockOrderService) GetOrder(ctx context.Context, orderID string) (*types.Order, error) {
	order, exists := m.orders[orderID]
	if !exists {
		return nil, errors.NewTypedError(errors.ErrorTypeNotFound, "Order not found", nil)
	}
	return order, nil
}

// CancelOrder 取消订单
func (m *MockOrderService) CancelOrder(ctx context.Context, orderID string) error {
	order, exists := m.orders[orderID]
	if !exists {
		return errors.NewTypedError(errors.ErrorTypeNotFound, "Order not found", nil)
	}

	order.Status = types.OrderStatusCancelled
	order.UpdatedAt = time.Now()
	return nil
}

// MockPaymentService 模拟支付服务
type MockPaymentService struct {
	payments map[string]*types.Payment
}

// NewMockPaymentService 创建模拟支付服务
func NewMockPaymentService() *MockPaymentService {
	return &MockPaymentService{
		payments: make(map[string]*types.Payment),
	}
}

// ProcessPayment 处理支付
func (m *MockPaymentService) ProcessPayment(ctx context.Context, req *types.PaymentRequest) (*types.Payment, error) {
	payment := &types.Payment{
		ID:            fmt.Sprintf("payment-%d", time.Now().UnixNano()),
		OrderID:       req.OrderID,
		Amount:        req.Amount,
		Method:        req.Method,
		Status:        types.PaymentStatusCompleted,
		TransactionID: fmt.Sprintf("txn-%d", time.Now().UnixNano()),
		CreatedAt:     time.Now(),
		CompletedAt:   time.Now(),
	}

	m.payments[payment.ID] = payment
	return payment, nil
}

// GetPayment 获取支付
func (m *MockPaymentService) GetPayment(ctx context.Context, paymentID string) (*types.Payment, error) {
	payment, exists := m.payments[paymentID]
	if !exists {
		return nil, errors.NewTypedError(errors.ErrorTypeNotFound, "Payment not found", nil)
	}
	return payment, nil
}

// TestEnvironment 测试环境
type TestEnvironment struct {
	otelManager    *otel.OTelManager
	userService    *MockUserService
	orderService   *MockOrderService
	paymentService *MockPaymentService
	config         *config.OTLPConfig
}

// NewTestEnvironment 创建测试环境
func NewTestEnvironment() *TestEnvironment {
	return &TestEnvironment{
		userService:    NewMockUserService(),
		orderService:   NewMockOrderService(),
		paymentService: NewMockPaymentService(),
		config: &config.OTLPConfig{
			Endpoint:       "localhost:4317",
			Insecure:       true,
			SamplingRate:   1.0,
			ServiceName:    "test-service",
			ServiceVersion: "1.0.0",
			Environment:    "test",
		},
	}
}

// Setup 设置测试环境
func (te *TestEnvironment) Setup() error {
	// 初始化 OpenTelemetry
	if err := otel.InitializeGlobalOTel(context.Background(), te.config); err != nil {
		return fmt.Errorf("failed to initialize OTel: %w", err)
	}

	te.otelManager = otel.GetGlobalOTelManager()
	return nil
}

// Teardown 清理测试环境
func (te *TestEnvironment) Teardown() error {
	// 关闭 OpenTelemetry
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	if err := otel.ShutdownGlobalOTel(ctx); err != nil {
		return fmt.Errorf("failed to shutdown OTel: %w", err)
	}

	return nil
}

// GetUserService 获取用户服务
func (te *TestEnvironment) GetUserService() *MockUserService {
	return te.userService
}

// GetOrderService 获取订单服务
func (te *TestEnvironment) GetOrderService() *MockOrderService {
	return te.orderService
}

// GetPaymentService 获取支付服务
func (te *TestEnvironment) GetPaymentService() *MockPaymentService {
	return te.paymentService
}

// GetOTelManager 获取 OTel 管理器
func (te *TestEnvironment) GetOTelManager() *otel.OTelManager {
	return te.otelManager
}

// 集成测试工具

// IntegrationTest 集成测试
type IntegrationTest struct {
	name        string
	environment *TestEnvironment
	setup       func(*TestEnvironment) error
	test        func(*TestEnvironment, *testing.T) error
	teardown    func(*TestEnvironment) error
}

// NewIntegrationTest 创建集成测试
func NewIntegrationTest(name string) *IntegrationTest {
	return &IntegrationTest{
		name:        name,
		environment: NewTestEnvironment(),
	}
}

// SetSetup 设置初始化
func (it *IntegrationTest) SetSetup(fn func(*TestEnvironment) error) *IntegrationTest {
	it.setup = fn
	return it
}

// SetTest 设置测试函数
func (it *IntegrationTest) SetTest(fn func(*TestEnvironment, *testing.T) error) *IntegrationTest {
	it.test = fn
	return it
}

// SetTeardown 设置清理
func (it *IntegrationTest) SetTeardown(fn func(*TestEnvironment) error) *IntegrationTest {
	it.teardown = fn
	return it
}

// Run 运行集成测试
func (it *IntegrationTest) Run(t *testing.T) {
	// 环境初始化
	if err := it.environment.Setup(); err != nil {
		t.Fatalf("Environment setup failed: %v", err)
	}

	// 确保清理
	defer func() {
		if err := it.environment.Teardown(); err != nil {
			t.Errorf("Environment teardown failed: %v", err)
		}
	}()

	// 测试初始化
	if it.setup != nil {
		if err := it.setup(it.environment); err != nil {
			t.Fatalf("Test setup failed: %v", err)
		}
	}

	// 确保测试清理
	defer func() {
		if it.teardown != nil {
			if err := it.teardown(it.environment); err != nil {
				t.Errorf("Test teardown failed: %v", err)
			}
		}
	}()

	// 运行测试
	if err := it.test(it.environment, t); err != nil {
		t.Errorf("Integration test failed: %v", err)
	}
}

// 性能测试工具

// PerformanceTest 性能测试
type PerformanceTest struct {
	name        string
	iterations  int
	concurrency int
	test        func() error
}

// NewPerformanceTest 创建性能测试
func NewPerformanceTest(name string) *PerformanceTest {
	return &PerformanceTest{
		name:        name,
		iterations:  1000,
		concurrency: 10,
	}
}

// SetIterations 设置迭代次数
func (pt *PerformanceTest) SetIterations(iterations int) *PerformanceTest {
	pt.iterations = iterations
	return pt
}

// SetConcurrency 设置并发数
func (pt *PerformanceTest) SetConcurrency(concurrency int) *PerformanceTest {
	pt.concurrency = concurrency
	return pt
}

// SetTest 设置测试函数
func (pt *PerformanceTest) SetTest(fn func() error) *PerformanceTest {
	pt.test = fn
	return pt
}

// Run 运行性能测试
func (pt *PerformanceTest) Run(t *testing.T) {
	if pt.test == nil {
		t.Fatal("Test function not set")
	}

	start := time.Now()
	errors := make(chan error, pt.iterations)

	// 启动并发测试
	for i := 0; i < pt.concurrency; i++ {
		go func() {
			for j := 0; j < pt.iterations/pt.concurrency; j++ {
				if err := pt.test(); err != nil {
					errors <- err
				}
			}
		}()
	}

	// 等待完成
	errorCount := 0
	for i := 0; i < pt.iterations; i++ {
		select {
		case <-errors:
			errorCount++
		case <-time.After(30 * time.Second):
			t.Errorf("Performance test timed out")
			return
		}
	}

	duration := time.Since(start)

	t.Logf("Performance Test: %s", pt.name)
	t.Logf("Iterations: %d", pt.iterations)
	t.Logf("Concurrency: %d", pt.concurrency)
	t.Logf("Duration: %v", duration)
	t.Logf("Errors: %d", errorCount)
	t.Logf("Success Rate: %.2f%%", float64(pt.iterations-errorCount)/float64(pt.iterations)*100)
	t.Logf("Operations/sec: %.2f", float64(pt.iterations)/duration.Seconds())
}

// 测试辅助函数

// AssertEqual 断言相等
func AssertEqual(t *testing.T, expected, actual interface{}, message string) {
	if expected != actual {
		t.Errorf("%s: expected %v, got %v", message, expected, actual)
	}
}

// AssertNotEqual 断言不相等
func AssertNotEqual(t *testing.T, expected, actual interface{}, message string) {
	if expected == actual {
		t.Errorf("%s: expected not equal to %v, got %v", message, expected, actual)
	}
}

// AssertNil 断言为nil
func AssertNil(t *testing.T, value interface{}, message string) {
	if value != nil {
		t.Errorf("%s: expected nil, got %v", message, value)
	}
}

// AssertNotNil 断言不为nil
func AssertNotNil(t *testing.T, value interface{}, message string) {
	if value == nil {
		t.Errorf("%s: expected not nil, got nil", message)
	}
}

// AssertTrue 断言为true
func AssertTrue(t *testing.T, value bool, message string) {
	if !value {
		t.Errorf("%s: expected true, got false", message)
	}
}

// AssertFalse 断言为false
func AssertFalse(t *testing.T, value bool, message string) {
	if value {
		t.Errorf("%s: expected false, got true", message)
	}
}

// AssertError 断言有错误
func AssertError(t *testing.T, err error, message string) {
	if err == nil {
		t.Errorf("%s: expected error, got nil", message)
	}
}

// AssertNoError 断言无错误
func AssertNoError(t *testing.T, err error, message string) {
	if err != nil {
		t.Errorf("%s: expected no error, got %v", message, err)
	}
}

// 测试数据生成器

// GenerateTestUser 生成测试用户
func GenerateTestUser(id string) *types.User {
	return &types.User{
		ID:        id,
		Name:      fmt.Sprintf("Test User %s", id),
		Email:     fmt.Sprintf("test%s@example.com", id),
		Phone:     fmt.Sprintf("+123456789%s", id),
		Level:     types.UserLevelNormal,
		CreatedAt: time.Now(),
	}
}

// GenerateTestOrder 生成测试订单
func GenerateTestOrder(id, userID string) *types.Order {
	return &types.Order{
		ID:     id,
		UserID: userID,
		Items: []types.OrderItem{
			{
				ProductID: fmt.Sprintf("prod-%s", id),
				Quantity:  1,
				Price:     99.99,
			},
		},
		TotalAmount: 99.99,
		Status:      types.OrderStatusPending,
		CreatedAt:   time.Now(),
		UpdatedAt:   time.Now(),
	}
}

// GenerateTestPayment 生成测试支付
func GenerateTestPayment(id, orderID string) *types.Payment {
	return &types.Payment{
		ID:            id,
		OrderID:       orderID,
		Amount:        99.99,
		Method:        types.PaymentMethodCreditCard,
		Status:        types.PaymentStatusCompleted,
		TransactionID: fmt.Sprintf("txn-%s", id),
		CreatedAt:     time.Now(),
		CompletedAt:   time.Now(),
	}
}

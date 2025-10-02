package resilience

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// CircuitBreaker 熔断器实现
// 实现了三态熔断器模式：Closed、Open、Half-Open
type CircuitBreaker struct {
	name             string
	maxFailures      int
	timeout          time.Duration
	halfOpenMaxCalls int

	// 状态
	state            State
	failures         int64
	successes        int64
	consecutiveFails int64
	lastStateChange  time.Time
	halfOpenCalls    int64

	mu sync.RWMutex

	// OpenTelemetry
	tracer         trace.Tracer
	meter          metric.Meter
	stateGauge     metric.Int64ObservableGauge
	requestCounter metric.Int64Counter
	failureCounter metric.Int64Counter
	timeoutCounter metric.Int64Counter
}

// State 熔断器状态
type State int

const (
	StateClosed State = iota
	StateOpen
	StateHalfOpen
)

func (s State) String() string {
	switch s {
	case StateClosed:
		return "closed"
	case StateOpen:
		return "open"
	case StateHalfOpen:
		return "half-open"
	default:
		return "unknown"
	}
}

var (
	ErrCircuitOpen  = errors.New("circuit breaker is open")
	ErrTooManyCalls = errors.New("too many calls in half-open state")
)

// NewCircuitBreaker 创建熔断器
func NewCircuitBreaker(name string, maxFailures int, timeout time.Duration) *CircuitBreaker {
	tracer := otel.Tracer("circuit-breaker/" + name)
	meter := otel.Meter("circuit-breaker/" + name)

	cb := &CircuitBreaker{
		name:             name,
		maxFailures:      maxFailures,
		timeout:          timeout,
		halfOpenMaxCalls: 3,
		state:            StateClosed,
		lastStateChange:  time.Now(),
		tracer:           tracer,
		meter:            meter,
	}

	// 初始化指标
	cb.initMetrics()

	return cb
}

// initMetrics 初始化 OpenTelemetry 指标
func (cb *CircuitBreaker) initMetrics() {
	var err error

	// 状态指标
	cb.stateGauge, err = cb.meter.Int64ObservableGauge(
		"circuit_breaker.state",
		metric.WithDescription("Circuit breaker state (0=closed, 1=open, 2=half-open)"),
		metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
			cb.mu.RLock()
			defer cb.mu.RUnlock()
			observer.Observe(int64(cb.state), metric.WithAttributes(
				attribute.String("circuit_breaker.name", cb.name),
			))
			return nil
		}),
	)
	if err != nil {
		// Handle error
	}

	// 请求计数器
	cb.requestCounter, _ = cb.meter.Int64Counter(
		"circuit_breaker.requests",
		metric.WithDescription("Total number of requests"),
	)

	// 失败计数器
	cb.failureCounter, _ = cb.meter.Int64Counter(
		"circuit_breaker.failures",
		metric.WithDescription("Total number of failures"),
	)

	// 超时计数器
	cb.timeoutCounter, _ = cb.meter.Int64Counter(
		"circuit_breaker.timeouts",
		metric.WithDescription("Total number of timeouts"),
	)
}

// Execute 执行操作（受熔断器保护）
func (cb *CircuitBreaker) Execute(ctx context.Context, operation func() error) error {
	ctx, span := cb.tracer.Start(ctx, "circuit_breaker.execute",
		trace.WithAttributes(
			attribute.String("circuit_breaker.name", cb.name),
		),
	)
	defer span.End()

	// 检查是否允许执行
	if err := cb.beforeCall(ctx); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		span.SetAttributes(attribute.String("circuit_breaker.state", cb.getState().String()))
		return err
	}

	// 记录请求
	cb.requestCounter.Add(ctx, 1, metric.WithAttributes(
		attribute.String("circuit_breaker.name", cb.name),
	))

	// 执行操作
	err := operation()

	// 记录结果
	cb.afterCall(ctx, err)

	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
	} else {
		span.SetStatus(codes.Ok, "success")
	}

	span.SetAttributes(
		attribute.String("circuit_breaker.state", cb.getState().String()),
		attribute.Int64("circuit_breaker.failures", atomic.LoadInt64(&cb.consecutiveFails)),
	)

	return err
}

// beforeCall 调用前检查
func (cb *CircuitBreaker) beforeCall(ctx context.Context) error {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	switch cb.state {
	case StateOpen:
		// 检查是否可以进入 Half-Open 状态
		if time.Since(cb.lastStateChange) > cb.timeout {
			cb.setState(StateHalfOpen, ctx)
			cb.halfOpenCalls = 0
			return nil
		}
		return ErrCircuitOpen

	case StateHalfOpen:
		// 限制 Half-Open 状态的调用次数
		if cb.halfOpenCalls >= int64(cb.halfOpenMaxCalls) {
			return ErrTooManyCalls
		}
		cb.halfOpenCalls++
		return nil

	case StateClosed:
		return nil

	default:
		return nil
	}
}

// afterCall 调用后处理
func (cb *CircuitBreaker) afterCall(ctx context.Context, err error) {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	if err != nil {
		// 失败
		atomic.AddInt64(&cb.failures, 1)
		atomic.AddInt64(&cb.consecutiveFails, 1)

		cb.failureCounter.Add(ctx, 1, metric.WithAttributes(
			attribute.String("circuit_breaker.name", cb.name),
		))

		switch cb.state {
		case StateClosed:
			if atomic.LoadInt64(&cb.consecutiveFails) >= int64(cb.maxFailures) {
				cb.setState(StateOpen, ctx)
			}

		case StateHalfOpen:
			// Half-Open 状态下失败，立即回到 Open
			cb.setState(StateOpen, ctx)
		}
	} else {
		// 成功
		atomic.AddInt64(&cb.successes, 1)
		atomic.StoreInt64(&cb.consecutiveFails, 0)

		switch cb.state {
		case StateHalfOpen:
			// Half-Open 状态下成功，检查是否可以关闭
			if cb.halfOpenCalls >= int64(cb.halfOpenMaxCalls) {
				cb.setState(StateClosed, ctx)
			}
		}
	}
}

// setState 设置状态
func (cb *CircuitBreaker) setState(newState State, ctx context.Context) {
	oldState := cb.state
	cb.state = newState
	cb.lastStateChange = time.Now()

	// 记录状态变更事件
	_, span := cb.tracer.Start(ctx, "circuit_breaker.state_change",
		trace.WithAttributes(
			attribute.String("circuit_breaker.name", cb.name),
			attribute.String("old_state", oldState.String()),
			attribute.String("new_state", newState.String()),
		),
	)
	span.End()

	// 状态转换到 Closed 时重置计数器
	if newState == StateClosed {
		atomic.StoreInt64(&cb.consecutiveFails, 0)
		cb.halfOpenCalls = 0
	}
}

// getState 获取当前状态
func (cb *CircuitBreaker) getState() State {
	cb.mu.RLock()
	defer cb.mu.RUnlock()
	return cb.state
}

// GetStats 获取统计信息
func (cb *CircuitBreaker) GetStats() CircuitBreakerStats {
	cb.mu.RLock()
	defer cb.mu.RUnlock()

	return CircuitBreakerStats{
		Name:             cb.name,
		State:            cb.state.String(),
		Failures:         atomic.LoadInt64(&cb.failures),
		Successes:        atomic.LoadInt64(&cb.successes),
		ConsecutiveFails: atomic.LoadInt64(&cb.consecutiveFails),
		LastStateChange:  cb.lastStateChange,
	}
}

// CircuitBreakerStats 熔断器统计信息
type CircuitBreakerStats struct {
	Name             string
	State            string
	Failures         int64
	Successes        int64
	ConsecutiveFails int64
	LastStateChange  time.Time
}

// Reset 重置熔断器
func (cb *CircuitBreaker) Reset(ctx context.Context) {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	atomic.StoreInt64(&cb.failures, 0)
	atomic.StoreInt64(&cb.successes, 0)
	atomic.StoreInt64(&cb.consecutiveFails, 0)
	cb.setState(StateClosed, ctx)
}

// CircuitBreakerGroup 熔断器组
// 管理多个熔断器
type CircuitBreakerGroup struct {
	breakers map[string]*CircuitBreaker
	mu       sync.RWMutex
}

// NewCircuitBreakerGroup 创建熔断器组
func NewCircuitBreakerGroup() *CircuitBreakerGroup {
	return &CircuitBreakerGroup{
		breakers: make(map[string]*CircuitBreaker),
	}
}

// Get 获取或创建熔断器
func (cbg *CircuitBreakerGroup) Get(name string, maxFailures int, timeout time.Duration) *CircuitBreaker {
	cbg.mu.RLock()
	if cb, exists := cbg.breakers[name]; exists {
		cbg.mu.RUnlock()
		return cb
	}
	cbg.mu.RUnlock()

	cbg.mu.Lock()
	defer cbg.mu.Unlock()

	// 双重检查
	if cb, exists := cbg.breakers[name]; exists {
		return cb
	}

	cb := NewCircuitBreaker(name, maxFailures, timeout)
	cbg.breakers[name] = cb
	return cb
}

// GetStats 获取所有熔断器统计
func (cbg *CircuitBreakerGroup) GetStats() []CircuitBreakerStats {
	cbg.mu.RLock()
	defer cbg.mu.RUnlock()

	stats := make([]CircuitBreakerStats, 0, len(cbg.breakers))
	for _, cb := range cbg.breakers {
		stats = append(stats, cb.GetStats())
	}
	return stats
}

// Example: 使用示例
func ExampleCircuitBreaker() {
	ctx := context.Background()

	// 创建熔断器
	cb := NewCircuitBreaker(
		"payment-service",
		5,              // 连续失败 5 次后熔断
		10*time.Second, // 10 秒后尝试恢复
	)

	// 执行操作
	err := cb.Execute(ctx, func() error {
		// 调用外部服务
		return callPaymentService()
	})

	if err != nil {
		if errors.Is(err, ErrCircuitOpen) {
			// 熔断器打开，快速失败
			return
		}
		// 其他错误
		return
	}

	// 查看统计
	stats := cb.GetStats()
	_ = stats
}

func callPaymentService() error {
	// 模拟服务调用
	return nil
}

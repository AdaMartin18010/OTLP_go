package concurrency

import (
	"context"
	"fmt"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
	"golang.org/x/sync/semaphore"
)

// Semaphore 带监控的信号量
// 包装 golang.org/x/sync/semaphore，添加 OTLP 集成
type Semaphore struct {
	sem       *semaphore.Weighted
	name      string
	maxWeight int64
	tracer    trace.Tracer
	meter     metric.Meter

	// Metrics
	acquiresCtr  metric.Int64Counter
	releasesCtr  metric.Int64Counter
	waitTimeDist metric.Float64Histogram
	activeGauge  metric.Int64ObservableGauge
}

// NewSemaphore 创建带监控的信号量
func NewSemaphore(name string, maxWeight int64) *Semaphore {
	tracer := otel.Tracer("concurrency/semaphore")
	meter := otel.Meter("concurrency/semaphore")

	s := &Semaphore{
		sem:       semaphore.NewWeighted(maxWeight),
		name:      name,
		maxWeight: maxWeight,
		tracer:    tracer,
		meter:     meter,
	}

	// 初始化指标
	s.acquiresCtr, _ = meter.Int64Counter(
		"semaphore.acquires",
		metric.WithDescription("Number of acquire operations"),
	)

	s.releasesCtr, _ = meter.Int64Counter(
		"semaphore.releases",
		metric.WithDescription("Number of release operations"),
	)

	s.waitTimeDist, _ = meter.Float64Histogram(
		"semaphore.wait_time",
		metric.WithDescription("Time spent waiting to acquire"),
		metric.WithUnit("s"),
	)

	return s
}

// Acquire 获取指定权重的信号量
func (s *Semaphore) Acquire(ctx context.Context, weight int64) error {
	start := time.Now()

	ctx, span := s.tracer.Start(ctx, "semaphore.acquire",
		trace.WithAttributes(
			attribute.String("semaphore.name", s.name),
			attribute.Int64("weight", weight),
		),
	)
	defer span.End()

	// 尝试获取
	err := s.sem.Acquire(ctx, weight)
	waitTime := time.Since(start).Seconds()

	attrs := metric.WithAttributes(
		attribute.String("semaphore.name", s.name),
	)

	s.waitTimeDist.Record(ctx, waitTime, attrs)

	if err != nil {
		span.RecordError(err)
		return err
	}

	s.acquiresCtr.Add(ctx, 1, attrs)
	span.SetAttributes(attribute.Float64("wait_time_seconds", waitTime))

	return nil
}

// TryAcquire 尝试获取信号量（非阻塞）
func (s *Semaphore) TryAcquire(weight int64) bool {
	ctx, span := s.tracer.Start(context.Background(), "semaphore.try_acquire",
		trace.WithAttributes(
			attribute.String("semaphore.name", s.name),
			attribute.Int64("weight", weight),
		),
	)
	defer span.End()

	acquired := s.sem.TryAcquire(weight)

	if acquired {
		attrs := metric.WithAttributes(
			attribute.String("semaphore.name", s.name),
		)
		s.acquiresCtr.Add(ctx, 1, attrs)
	}

	span.SetAttributes(attribute.Bool("acquired", acquired))
	return acquired
}

// Release 释放指定权重的信号量
func (s *Semaphore) Release(weight int64) {
	ctx, span := s.tracer.Start(context.Background(), "semaphore.release",
		trace.WithAttributes(
			attribute.String("semaphore.name", s.name),
			attribute.Int64("weight", weight),
		),
	)
	defer span.End()

	s.sem.Release(weight)

	attrs := metric.WithAttributes(
		attribute.String("semaphore.name", s.name),
	)
	s.releasesCtr.Add(ctx, 1, attrs)
}

// WithSemaphore 使用信号量执行函数
func (s *Semaphore) WithSemaphore(ctx context.Context, weight int64, fn func() error) error {
	if err := s.Acquire(ctx, weight); err != nil {
		return fmt.Errorf("failed to acquire semaphore: %w", err)
	}
	defer s.Release(weight)

	return fn()
}

// Example: 并发限制
func ExampleSemaphore() {
	ctx := context.Background()

	// 最多 10 个并发
	sem := NewSemaphore("api-calls", 10)

	// 并发处理任务
	for i := 0; i < 100; i++ {
		i := i
		go func() {
			// 获取信号量（超时 5 秒）
			ctx, cancel := context.WithTimeout(ctx, 5*time.Second)
			defer cancel()

			if err := sem.Acquire(ctx, 1); err != nil {
				fmt.Printf("Failed to acquire: %v\n", err)
				return
			}
			defer sem.Release(1)

			// 执行任务
			fmt.Printf("Processing task %d\n", i)
			time.Sleep(100 * time.Millisecond)
		}()
	}
}

// Example: 使用辅助函数
func ExampleWithSemaphore() {
	ctx := context.Background()
	sem := NewSemaphore("file-operations", 5)

	// 限制并发文件操作
	err := sem.WithSemaphore(ctx, 1, func() error {
		// 文件操作
		fmt.Println("Reading file...")
		return nil
	})

	if err != nil {
		fmt.Printf("Error: %v\n", err)
	}
}

// RateLimiter 速率限制器
// 使用令牌桶算法实现
type RateLimiter struct {
	mu           sync.Mutex
	tokens       int64
	maxTokens    int64
	refillRate   int64         // 每次补充的令牌数
	refillPeriod time.Duration // 补充周期
	lastRefill   time.Time
	stopCh       chan struct{}
	tracer       trace.Tracer
}

// NewRateLimiter 创建速率限制器
// maxTokens: 最大令牌数（突发容量）
// refillRate: 每个周期补充的令牌数
// refillPeriod: 补充周期
func NewRateLimiter(name string, maxTokens int64, refillPeriod time.Duration) *RateLimiter {
	rl := &RateLimiter{
		tokens:       maxTokens, // 初始满令牌
		maxTokens:    maxTokens,
		refillRate:   1, // 每个周期补充 1 个令牌
		refillPeriod: refillPeriod,
		lastRefill:   time.Now(),
		stopCh:       make(chan struct{}),
		tracer:       otel.Tracer("concurrency/ratelimiter"),
	}

	// 启动定期补充令牌的 goroutine
	go rl.refillLoop()

	return rl
}

// refillLoop 定期补充令牌
func (rl *RateLimiter) refillLoop() {
	ticker := time.NewTicker(rl.refillPeriod)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			rl.refill()
		case <-rl.stopCh:
			return
		}
	}
}

// refill 补充令牌（内部方法）
func (rl *RateLimiter) refill() {
	rl.mu.Lock()
	defer rl.mu.Unlock()

	now := time.Now()
	elapsed := now.Sub(rl.lastRefill)

	// 计算应该补充的令牌数
	tokensToAdd := int64(elapsed / rl.refillPeriod)
	if tokensToAdd > 0 {
		rl.tokens = min(rl.tokens+tokensToAdd, rl.maxTokens)
		rl.lastRefill = now
	}
}

// Wait 等待获取令牌
func (rl *RateLimiter) Wait(ctx context.Context) error {
	_, span := rl.tracer.Start(ctx, "ratelimiter.wait")
	defer span.End()

	for {
		// 先尝试获取
		if rl.tryTakeToken() {
			return nil
		}

		// 等待一个补充周期
		select {
		case <-time.After(rl.refillPeriod / 10): // 短暂等待后重试
			continue
		case <-ctx.Done():
			span.RecordError(ctx.Err())
			return ctx.Err()
		}
	}
}

// Allow 尝试获取令牌（非阻塞）
func (rl *RateLimiter) Allow() bool {
	_, span := rl.tracer.Start(context.Background(), "ratelimiter.allow")
	defer span.End()

	allowed := rl.tryTakeToken()
	span.SetAttributes(attribute.Bool("allowed", allowed))
	return allowed
}

// tryTakeToken 尝试获取一个令牌（内部方法）
func (rl *RateLimiter) tryTakeToken() bool {
	rl.mu.Lock()
	defer rl.mu.Unlock()

	// 先尝试补充（基于时间的自然补充）
	now := time.Now()
	elapsed := now.Sub(rl.lastRefill)
	tokensToAdd := int64(elapsed / rl.refillPeriod)
	if tokensToAdd > 0 {
		rl.tokens = min(rl.tokens+tokensToAdd, rl.maxTokens)
		rl.lastRefill = now
	}

	// 检查是否有令牌
	if rl.tokens > 0 {
		rl.tokens--
		return true
	}
	return false
}

// Stop 停止 RateLimiter
func (rl *RateLimiter) Stop() {
	close(rl.stopCh)
}

// min 返回两个 int64 的最小值
func min(a, b int64) int64 {
	if a < b {
		return a
	}
	return b
}

// Example: 速率限制
func ExampleRateLimiter() {
	// 每秒最多 10 个请求，允许突发 20 个
	limiter := NewRateLimiter("api", 20, 100*time.Millisecond)

	ctx := context.Background()

	// 发送请求
	for i := 0; i < 100; i++ {
		if err := limiter.Wait(ctx); err != nil {
			fmt.Printf("Rate limit error: %v\n", err)
			return
		}

		fmt.Printf("Request %d sent\n", i)
	}
}

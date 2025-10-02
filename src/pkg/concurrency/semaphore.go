package concurrency

import (
	"context"
	"fmt"
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
type RateLimiter struct {
	sem      *Semaphore
	interval time.Duration
	burst    int64
}

// NewRateLimiter 创建速率限制器
// burst: 突发请求数量
// interval: 补充间隔
func NewRateLimiter(name string, burst int64, interval time.Duration) *RateLimiter {
	rl := &RateLimiter{
		sem:      NewSemaphore(name, burst),
		interval: interval,
		burst:    burst,
	}

	// 定期补充令牌
	go rl.refillLoop()

	return rl
}

// refillLoop 定期补充令牌
func (rl *RateLimiter) refillLoop() {
	ticker := time.NewTicker(rl.interval)
	defer ticker.Stop()

	for range ticker.C {
		// 尝试释放一个令牌
		if rl.sem.TryAcquire(0) {
			// 如果可以获取 0 权重，说明未满
			rl.sem.Release(1)
		}
	}
}

// Wait 等待获取令牌
func (rl *RateLimiter) Wait(ctx context.Context) error {
	return rl.sem.Acquire(ctx, 1)
}

// Allow 尝试获取令牌（非阻塞）
func (rl *RateLimiter) Allow() bool {
	return rl.sem.TryAcquire(1)
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

package patterns

import (
	"context"
	"fmt"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// WorkerPool 实现可观测的 Worker Pool 模式
// CSP 模型: Workers 从共享 Channel 接收任务并并发处理

// Task 定义工作任务
type Task interface {
	Execute(context.Context) error
	GetID() string
}

// WorkerPool Worker 池实现
type WorkerPool struct {
	name        string
	workerCount int
	queueSize   int
	tasks       chan Task
	wg          sync.WaitGroup
	ctx         context.Context
	cancel      context.CancelFunc
	tracer      trace.Tracer
	meter       metric.Meter

	// Metrics
	queueLength   metric.Int64ObservableGauge
	activeWorkers metric.Int64ObservableGauge
	taskLatency   metric.Float64Histogram
	taskCounter   metric.Int64Counter
	errorCounter  metric.Int64Counter

	// Internal state
	mu           sync.RWMutex
	currentQueue int64
	activeCount  int64
}

// NewWorkerPool 创建新的 Worker Pool
// 优化：支持自定义 context，增加配置验证
func NewWorkerPool(name string, workerCount, queueSize int) *WorkerPool {
	return NewWorkerPoolWithContext(context.Background(), name, workerCount, queueSize)
}

// NewWorkerPoolWithContext 使用自定义 context 创建 Worker Pool
func NewWorkerPoolWithContext(parentCtx context.Context, name string, workerCount, queueSize int) *WorkerPool {
	// 参数验证
	if workerCount <= 0 {
		workerCount = 10 // 默认值
	}
	if queueSize <= 0 {
		queueSize = 100 // 默认值
	}

	ctx, cancel := context.WithCancel(parentCtx)
	tracer := otel.Tracer(fmt.Sprintf("worker-pool/%s", name))
	meter := otel.Meter(fmt.Sprintf("worker-pool/%s", name))

	wp := &WorkerPool{
		name:        name,
		workerCount: workerCount,
		queueSize:   queueSize,
		tasks:       make(chan Task, queueSize),
		ctx:         ctx,
		cancel:      cancel,
		tracer:      tracer,
		meter:       meter,
	}

	// 初始化指标
	wp.initMetrics()

	return wp
}

// initMetrics 初始化 OpenTelemetry 指标
func (wp *WorkerPool) initMetrics() {
	var err error

	// 队列长度
	wp.queueLength, err = wp.meter.Int64ObservableGauge(
		"worker_pool.queue.length",
		metric.WithDescription("Current number of tasks in queue"),
		metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
			wp.mu.RLock()
			defer wp.mu.RUnlock()
			observer.Observe(wp.currentQueue, metric.WithAttributes(
				attribute.String("pool.name", wp.name),
			))
			return nil
		}),
	)
	if err != nil {
		// Handle error
	}

	// 活跃 Worker 数量
	wp.activeWorkers, err = wp.meter.Int64ObservableGauge(
		"worker_pool.workers.active",
		metric.WithDescription("Number of currently active workers"),
		metric.WithInt64Callback(func(ctx context.Context, observer metric.Int64Observer) error {
			wp.mu.RLock()
			defer wp.mu.RUnlock()
			observer.Observe(wp.activeCount, metric.WithAttributes(
				attribute.String("pool.name", wp.name),
			))
			return nil
		}),
	)
	if err != nil {
		// Handle error
	}

	// 任务延迟
	wp.taskLatency, _ = wp.meter.Float64Histogram(
		"worker_pool.task.latency",
		metric.WithDescription("Task processing latency in seconds"),
		metric.WithUnit("s"),
	)

	// 任务计数器
	wp.taskCounter, _ = wp.meter.Int64Counter(
		"worker_pool.tasks.processed",
		metric.WithDescription("Total number of tasks processed"),
		metric.WithUnit("1"),
	)

	// 错误计数器
	wp.errorCounter, _ = wp.meter.Int64Counter(
		"worker_pool.errors",
		metric.WithDescription("Total number of errors"),
		metric.WithUnit("1"),
	)
}

// Start 启动 Worker Pool
func (wp *WorkerPool) Start() {
	ctx, span := wp.tracer.Start(wp.ctx, "worker_pool.start",
		trace.WithAttributes(
			attribute.String("pool.name", wp.name),
			attribute.Int("worker.count", wp.workerCount),
			attribute.Int("queue.size", wp.queueSize),
		),
	)
	defer span.End()

	for i := 0; i < wp.workerCount; i++ {
		wp.wg.Add(1)
		go wp.worker(ctx, i)
	}

	span.AddEvent("workers.started")
}

// worker 工作协程
func (wp *WorkerPool) worker(ctx context.Context, workerID int) {
	defer wp.wg.Done()

	ctx, span := wp.tracer.Start(ctx, "worker.lifecycle",
		trace.WithAttributes(
			attribute.Int("worker.id", workerID),
			attribute.String("pool.name", wp.name),
		),
	)
	defer span.End()

	span.AddEvent("worker.ready")

	for {
		select {
		case task, ok := <-wp.tasks:
			if !ok {
				span.AddEvent("channel.closed")
				return
			}

			wp.incrementActive()
			wp.processTask(ctx, workerID, task)
			wp.decrementActive()

		case <-ctx.Done():
			span.AddEvent("context.cancelled")
			return
		}
	}
}

// processTask 处理单个任务
func (wp *WorkerPool) processTask(ctx context.Context, workerID int, task Task) {
	start := time.Now()

	ctx, span := wp.tracer.Start(ctx, "worker.process_task",
		trace.WithAttributes(
			attribute.Int("worker.id", workerID),
			attribute.String("task.id", task.GetID()),
			attribute.String("pool.name", wp.name),
		),
	)
	defer span.End()

	// 执行任务
	err := task.Execute(ctx)
	duration := time.Since(start).Seconds()

	// 记录指标
	attrs := metric.WithAttributes(
		attribute.String("pool.name", wp.name),
		attribute.String("task.type", fmt.Sprintf("%T", task)),
	)

	wp.taskLatency.Record(ctx, duration, attrs)

	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		wp.errorCounter.Add(ctx, 1, attrs)

		span.AddEvent("task.failed", trace.WithAttributes(
			attribute.String("error", err.Error()),
		))
	} else {
		span.SetStatus(codes.Ok, "completed")
		span.AddEvent("task.completed", trace.WithAttributes(
			attribute.Float64("duration.seconds", duration),
		))
	}

	wp.taskCounter.Add(ctx, 1, attrs)
}

// Submit 提交任务到 Worker Pool
// 优化：使用 context 的 deadline，避免硬编码超时
func (wp *WorkerPool) Submit(ctx context.Context, task Task) error {
	ctx, span := wp.tracer.Start(ctx, "worker_pool.submit",
		trace.WithAttributes(
			attribute.String("pool.name", wp.name),
			attribute.String("task.id", task.GetID()),
		),
	)
	defer span.End()

	wp.incrementQueue()
	defer wp.decrementQueue()

	// 检查 context 是否已设置 deadline
	_, hasDeadline := ctx.Deadline()
	if !hasDeadline {
		// 如果没有设置 deadline，使用默认超时
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, 5*time.Second)
		defer cancel()
	}

	select {
	case wp.tasks <- task:
		span.SetStatus(codes.Ok, "task submitted")
		return nil
	case <-ctx.Done():
		err := ctx.Err()
		span.RecordError(err)
		if err == context.DeadlineExceeded {
			span.SetStatus(codes.Error, "submit timeout: queue full")
		} else {
			span.SetStatus(codes.Error, "context cancelled")
		}
		return err
	}
}

// SubmitBatch 批量提交任务
func (wp *WorkerPool) SubmitBatch(ctx context.Context, tasks []Task) error {
	ctx, span := wp.tracer.Start(ctx, "worker_pool.submit_batch",
		trace.WithAttributes(
			attribute.String("pool.name", wp.name),
			attribute.Int("batch.size", len(tasks)),
		),
	)
	defer span.End()

	submitted := 0
	for _, task := range tasks {
		if err := wp.Submit(ctx, task); err != nil {
			span.RecordError(err)
			span.SetAttributes(
				attribute.Int("submitted.count", submitted),
				attribute.Int("failed.count", len(tasks)-submitted),
			)
			return fmt.Errorf("failed to submit task %s: %w", task.GetID(), err)
		}
		submitted++
	}

	span.SetStatus(codes.Ok, "all tasks submitted")
	span.SetAttributes(attribute.Int("submitted.count", submitted))
	return nil
}

// Shutdown 优雅关闭 Worker Pool
func (wp *WorkerPool) Shutdown(ctx context.Context) error {
	ctx, span := wp.tracer.Start(ctx, "worker_pool.shutdown",
		trace.WithAttributes(
			attribute.String("pool.name", wp.name),
		),
	)
	defer span.End()

	// 关闭任务通道
	close(wp.tasks)
	span.AddEvent("tasks.channel.closed")

	// 等待所有 worker 完成（带超时）
	done := make(chan struct{})
	go func() {
		wp.wg.Wait()
		close(done)
	}()

	select {
	case <-done:
		span.SetStatus(codes.Ok, "all workers finished")
		span.AddEvent("workers.finished")
		return nil
	case <-ctx.Done():
		wp.cancel() // 强制取消
		span.RecordError(ctx.Err())
		span.SetStatus(codes.Error, "shutdown timeout")
		return ctx.Err()
	}
}

// Internal helper methods
func (wp *WorkerPool) incrementQueue() {
	wp.mu.Lock()
	wp.currentQueue++
	wp.mu.Unlock()
}

func (wp *WorkerPool) decrementQueue() {
	wp.mu.Lock()
	wp.currentQueue--
	wp.mu.Unlock()
}

func (wp *WorkerPool) incrementActive() {
	wp.mu.Lock()
	wp.activeCount++
	wp.mu.Unlock()
}

func (wp *WorkerPool) decrementActive() {
	wp.mu.Lock()
	wp.activeCount--
	wp.mu.Unlock()
}

// GetStats 获取 Worker Pool 统计信息
func (wp *WorkerPool) GetStats() PoolStats {
	wp.mu.RLock()
	defer wp.mu.RUnlock()

	return PoolStats{
		Name:          wp.name,
		WorkerCount:   wp.workerCount,
		QueueSize:     wp.queueSize,
		CurrentQueue:  wp.currentQueue,
		ActiveWorkers: wp.activeCount,
	}
}

// PoolStats Worker Pool 统计信息
type PoolStats struct {
	Name          string
	WorkerCount   int
	QueueSize     int
	CurrentQueue  int64
	ActiveWorkers int64
}

// Example: 具体任务实现
type EmailTask struct {
	ID      string
	To      string
	Subject string
	Body    string
	tracer  trace.Tracer
}

func NewEmailTask(id, to, subject, body string) *EmailTask {
	return &EmailTask{
		ID:      id,
		To:      to,
		Subject: subject,
		Body:    body,
		tracer:  otel.Tracer("tasks/email"),
	}
}

func (t *EmailTask) GetID() string {
	return t.ID
}

func (t *EmailTask) Execute(ctx context.Context) error {
	ctx, span := t.tracer.Start(ctx, "email.send",
		trace.WithAttributes(
			attribute.String("email.to", t.To),
			attribute.String("email.subject", t.Subject),
		),
	)
	defer span.End()

	// 模拟发送邮件
	time.Sleep(100 * time.Millisecond)

	span.AddEvent("email.sent")
	return nil
}

// Example: 使用 Worker Pool
func ExampleWorkerPool() {
	ctx := context.Background()

	// 创建 Worker Pool
	pool := NewWorkerPool("email-sender", 10, 100)
	pool.Start()

	// 提交任务
	tasks := make([]Task, 50)
	for i := 0; i < 50; i++ {
		tasks[i] = NewEmailTask(
			fmt.Sprintf("email-%d", i),
			fmt.Sprintf("user%d@example.com", i),
			"Hello",
			"This is a test email",
		)
	}

	// 批量提交
	if err := pool.SubmitBatch(ctx, tasks); err != nil {
		fmt.Printf("Failed to submit tasks: %v\n", err)
		return
	}

	// 等待处理完成
	shutdownCtx, cancel := context.WithTimeout(ctx, 30*time.Second)
	defer cancel()

	if err := pool.Shutdown(shutdownCtx); err != nil {
		fmt.Printf("Shutdown error: %v\n", err)
		return
	}

	// 打印统计
	stats := pool.GetStats()
	fmt.Printf("Pool %s: %d workers, queue: %d/%d\n",
		stats.Name, stats.WorkerCount, stats.CurrentQueue, stats.QueueSize)
}

package patterns

import (
	"context"
	"fmt"
	"sync"
	"time"

	"OTLP_go/src/pkg/concurrency"
	"OTLP_go/src/pkg/pool"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// Fan-Out/Fan-In 模式：CSP + OTLP 完整实现
// 模式说明：将任务分发给多个 worker 并行处理，最后聚合结果

// Job 定义处理任务
type Job struct {
	ID      string
	Payload interface{}
}

// Result 定义处理结果
type Result struct {
	JobID    string
	Output   interface{}
	Duration time.Duration
	Error    error
}

// FanOutFanIn 实现 Fan-Out/Fan-In 模式
// 优化：添加并发控制、对象池化
type FanOutFanIn struct {
	workerCount int
	tracer      trace.Tracer
	sem         *concurrency.Semaphore // 并发控制
	bufferPool  *pool.Pool[*Result]    // 结果池
}

// NewFanOutFanIn 创建新的 Fan-Out/Fan-In 处理器
// 优化：添加并发控制，防止 goroutine 泄露
func NewFanOutFanIn(workerCount int) *FanOutFanIn {
	// 参数验证
	if workerCount <= 0 {
		workerCount = 10
	}

	return &FanOutFanIn{
		workerCount: workerCount,
		tracer:      otel.Tracer("patterns/fanout-fanin"),
		sem:         concurrency.NewSemaphore("fanout-fanin", int64(workerCount)),
		bufferPool: pool.NewPool("fanout-result", func() *Result {
			return &Result{}
		}),
	}
}

// Process 执行 Fan-Out/Fan-In 处理
func (f *FanOutFanIn) Process(ctx context.Context, jobs []Job) ([]Result, error) {
	ctx, span := f.tracer.Start(ctx, "FanOutFanIn.Process")
	defer span.End()

	span.SetAttributes(
		attribute.Int("job.count", len(jobs)),
		attribute.Int("worker.count", f.workerCount),
	)

	// Fan-Out: 分发任务到多个 worker
	jobsCh := make(chan Job, len(jobs))
	resultsCh := make(chan Result, len(jobs))

	// 启动 workers
	var wg sync.WaitGroup
	for i := 0; i < f.workerCount; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()
			f.worker(ctx, workerID, jobsCh, resultsCh)
		}(i)
	}

	// 发送所有任务
	go func() {
		for _, job := range jobs {
			jobsCh <- job
		}
		close(jobsCh)
	}()

	// 等待所有 worker 完成
	go func() {
		wg.Wait()
		close(resultsCh)
	}()

	// Fan-In: 收集所有结果（使用预分配）
	results := make([]Result, 0, len(jobs))
	for result := range resultsCh {
		// 复制结果（避免引用问题）
		resultCopy := Result{
			JobID:    result.JobID,
			Output:   result.Output,
			Duration: result.Duration,
			Error:    result.Error,
		}
		results = append(results, resultCopy)

		// 记录每个结果的 Span Event
		span.AddEvent("job.completed",
			trace.WithAttributes(
				attribute.String("job.id", result.JobID),
				attribute.Int64("duration.ms", result.Duration.Milliseconds()),
				attribute.Bool("success", result.Error == nil),
			),
		)
	}

	span.SetAttributes(attribute.Int("results.count", len(results)))
	return results, nil
}

// worker 处理单个任务
func (f *FanOutFanIn) worker(ctx context.Context, workerID int, jobs <-chan Job, results chan<- Result) {
	for job := range jobs {
		// 为每个 job 创建子 Span
		ctx, span := f.tracer.Start(ctx, "worker.process",
			trace.WithAttributes(
				attribute.Int("worker.id", workerID),
				attribute.String("job.id", job.ID),
			),
		)

		start := time.Now()

		// 模拟处理（实际应用中替换为真实逻辑）
		output, err := f.processJob(ctx, job)
		duration := time.Since(start)

		if err != nil {
			span.RecordError(err)
			span.SetAttributes(attribute.Bool("job.failed", true))
		} else {
			span.SetAttributes(attribute.Bool("job.success", true))
		}

		span.End()

		results <- Result{
			JobID:    job.ID,
			Output:   output,
			Duration: duration,
			Error:    err,
		}
	}
}

// processJob 处理单个任务的业务逻辑
func (f *FanOutFanIn) processJob(ctx context.Context, job Job) (interface{}, error) {
	_, span := f.tracer.Start(ctx, "processJob.businessLogic")
	defer span.End()

	// 模拟耗时操作
	select {
	case <-time.After(50 * time.Millisecond):
		return fmt.Sprintf("processed-%s", job.ID), nil
	case <-ctx.Done():
		return nil, ctx.Err()
	}
}

// ProcessWithTimeout 带超时的处理
func (f *FanOutFanIn) ProcessWithTimeout(ctx context.Context, jobs []Job, timeout time.Duration) ([]Result, error) {
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	ctx, span := f.tracer.Start(ctx, "FanOutFanIn.ProcessWithTimeout")
	defer span.End()

	span.SetAttributes(
		attribute.Int64("timeout.ms", timeout.Milliseconds()),
	)

	results, err := f.Process(ctx, jobs)

	if err != nil {
		span.RecordError(err)
	}

	return results, err
}

// Example: 使用示例
func ExampleFanOutFanIn() {
	ctx := context.Background()

	// 创建 Fan-Out/Fan-In 处理器
	processor := NewFanOutFanIn(10) // 10 个 worker

	// 准备任务
	jobs := make([]Job, 100)
	for i := 0; i < 100; i++ {
		jobs[i] = Job{
			ID:      fmt.Sprintf("job-%d", i),
			Payload: map[string]interface{}{"index": i},
		}
	}

	// 执行处理
	results, err := processor.ProcessWithTimeout(ctx, jobs, 10*time.Second)
	if err != nil {
		fmt.Printf("Error: %v\n", err)
		return
	}

	// 输出结果
	successCount := 0
	for _, result := range results {
		if result.Error == nil {
			successCount++
		}
	}
	fmt.Printf("Processed %d/%d jobs successfully\n", successCount, len(jobs))
}

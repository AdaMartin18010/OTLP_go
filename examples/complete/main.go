// complete - OTLP Go SDK 完整使用示例
//
// 本示例展示如何使用 OTLP Go SDK 的所有核心功能:
//   - OpenTelemetry 完整配置 (Traces + Metrics + Logs)
//   - 资源检测与自定义属性
//   - 上下文传播
//   - 错误处理与重试
//   - 性能优化
//   - 优雅关闭
//
// 运行方式:
//
//	go run main.go
//
// 或者使用 OTLP Collector:
//
//	OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 go run main.go
package main

import (
	"context"
	"errors"
	"fmt"
	"log"
	"math/rand/v2"
	"os"
	"os/signal"
	"sync"
	"syscall"
	"time"

	"github.com/OTLP_go/pkg/config"
	otelerrors "github.com/OTLP_go/pkg/errors"
	"github.com/OTLP_go/pkg/logs"
	"github.com/OTLP_go/pkg/otel"
	"github.com/OTLP_go/pkg/performance"
	"github.com/OTLP_go/pkg/resource"
	"github.com/OTLP_go/pkg/shutdown"
)

func main() {
	// ========== 1. 配置初始化 ==========
	ctx := context.Background()

	// 创建配置
	cfg := &config.OTelConfig{
		ServiceName:           "complete-demo-service",
		ServiceVersion:        "1.0.0",
		DeploymentEnvironment: "development",
		Exporter: config.OTLPExporterConfig{
			Endpoint:    getEnv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317"),
			Protocol:    "grpc",
			Compression: "gzip",
			Timeout:     10 * time.Second,
			Headers: map[string]string{
				"x-custom-header": "complete-demo",
			},
			Retry: config.RetryConfig{
				Enabled:         true,
				InitialInterval: 1 * time.Second,
				MaxInterval:     5 * time.Second,
				MaxElapsedTime:  30 * time.Second,
			},
		},
		Batch: config.BatchConfig{
			TracesMaxQueueSize:       2048,
			TracesMaxExportBatchSize: 512,
			TracesScheduleDelay:      5 * time.Second,
			MetricsExportInterval:    60 * time.Second,
		},
		Resource: config.ResourceConfig{
			Attributes: map[string]string{
				"service.namespace":   "otlp-examples",
				"service.instance.id": generateInstanceID(),
			},
		},
		Tracer: config.TracerConfig{
			Enabled: true,
		},
		Meter: config.MeterConfig{
			Enabled: true,
		},
		Logger: config.LoggerConfig{
			Enabled: true,
			Level:   "info",
		},
		Sampling: config.SamplingConfig{
			Strategy: "parentbased_always_on",
			Ratio:    1.0,
		},
	}

	// ========== 2. 初始化 OpenTelemetry SDK ==========
	sdk, err := otel.Setup(ctx, cfg)
	if err != nil {
		log.Fatalf("Failed to setup OpenTelemetry SDK: %v", err)
	}

	// 设置全局 SDK
	otel.SetGlobalSDK(sdk)

	// 创建日志记录器
	logger := logs.New("complete-demo",
		logs.WithLevel(logs.LevelInfo),
		logs.WithCaller(true),
	)
	logs.SetGlobalLogger(logger)

	logger.Info("OpenTelemetry SDK initialized",
		logs.String("service", cfg.ServiceName),
		logs.String("version", cfg.ServiceVersion),
	)

	// ========== 3. 资源检测示例 ==========
	demonstrateResourceDetection(ctx, logger)

	// ========== 4. 设置优雅关闭 ==========
	shutdownManager := setupGracefulShutdown(sdk, logger)
	defer shutdownManager.Execute(ctx)

	// ========== 5. 演示追踪功能 ==========
	demonstrateTracing(ctx, sdk, logger)

	// ========== 6. 演示指标功能 ==========
	demonstrateMetrics(ctx, sdk, logger)

	// ========== 7. 演示错误处理 ==========
	demonstrateErrorHandling(ctx, sdk, logger)

	// ========== 8. 演示性能优化 ==========
	demonstratePerformanceOptimizations(ctx, sdk, logger)

	// ========== 9. 演示并发处理 ==========
	demonstrateConcurrency(ctx, sdk, logger)

	// 等待信号
	waitForSignal(logger)

	fmt.Println("\n✅ Complete demo finished successfully!")
}

// demonstrateResourceDetection 演示资源检测功能
func demonstrateResourceDetection(ctx context.Context, logger *logs.Logger) {
	logger.Info("=== Resource Detection Demo ===")

	// 创建主机资源检测器
	hostDetector := &resource.HostDetector{}

	// 检测资源
	res, err := hostDetector.Detect(ctx)
	if err != nil {
		logger.Warn("Failed to detect host resources", logs.Error(err))
		return
	}

	logger.Info("Detected resources",
		logs.String("source", hostDetector.DetectorType()),
		logs.Any("attributes", res.Attributes.ToMap()),
	)
}

// demonstrateTracing 演示分布式追踪功能
func demonstrateTracing(ctx context.Context, sdk *otel.SDK, logger *logs.Logger) {
	logger.Info("=== Tracing Demo ===")

	tracer := sdk.Tracer("complete-demo")

	// 创建主 Span
	ctx, span := tracer.Start(ctx, "demo-operation")
	defer span.End()

	// 设置属性
	span.SetAttributes(
		logs.String("operation.type", "demo"),
		logs.Int("operation.priority", 1),
	)

	// 模拟嵌套操作
	simulateDatabaseQuery(ctx, tracer)
	simulateHTTPRequest(ctx, tracer)
	simulateCacheOperation(ctx, tracer)

	logger.InfoContext(ctx, "Tracing operations completed")
}

func simulateDatabaseQuery(ctx context.Context, tracer *otel.Tracer) {
	ctx, span := tracer.Start(ctx, "db.query")
	defer span.End()

	span.SetAttributes(
		logs.String("db.system", "postgresql"),
		logs.String("db.statement", "SELECT * FROM users"),
	)

	// 模拟查询时间
	time.Sleep(50 * time.Millisecond)

	span.AddEvent("query.completed")
}

func simulateHTTPRequest(ctx context.Context, tracer *otel.Tracer) {
	ctx, span := tracer.Start(ctx, "http.request")
	defer span.End()

	span.SetAttributes(
		logs.String("http.method", "GET"),
		logs.String("http.url", "https://api.example.com/users"),
	)

	// 模拟请求时间
	time.Sleep(30 * time.Millisecond)

	span.SetAttributes(logs.Int("http.status_code", 200))
	span.AddEvent("response.received")
}

func simulateCacheOperation(ctx context.Context, tracer *otel.Tracer) {
	ctx, span := tracer.Start(ctx, "cache.operation")
	defer span.End()

	span.SetAttributes(
		logs.String("cache.system", "redis"),
		logs.String("cache.operation", "get"),
	)

	// 模拟缓存操作
	time.Sleep(5 * time.Millisecond)

	span.SetAttributes(logs.Bool("cache.hit", true))
}

// demonstrateMetrics 演示指标收集功能
func demonstrateMetrics(ctx context.Context, sdk *otel.SDK, logger *logs.Logger) {
	logger.Info("=== Metrics Demo ===")

	meter := sdk.Meter("complete-demo")

	// 创建计数器
	requestCounter, err := meter.Int64Counter("demo.requests.total")
	if err != nil {
		logger.Error("Failed to create counter", logs.Error(err))
		return
	}

	// 创建直方图
	durationHistogram, err := meter.Int64Histogram("demo.request.duration_ms")
	if err != nil {
		logger.Error("Failed to create histogram", logs.Error(err))
		return
	}

	// 记录一些指标
	for i := range 5 {
		start := time.Now()

		// 模拟工作
		time.Sleep(time.Duration(10+i*5) * time.Millisecond)

		// 记录指标
		duration := time.Since(start)
		requestCounter.Add(ctx, 1)
		durationHistogram.Record(ctx, duration.Milliseconds())
	}

	logger.Info("Metrics recorded",
		logs.Int("request_count", 5),
	)
}

// demonstrateErrorHandling 演示错误处理功能
func demonstrateErrorHandling(ctx context.Context, sdk *otel.SDK, logger *logs.Logger) {
	logger.Info("=== Error Handling Demo ===")

	// 创建结构化错误
	err := otelerrors.New("failed to process request").
		WithCode(otelerrors.CodeInternal).
		WithCategory(otelerrors.CategorySystem).
		WithRetryable(true).
		WithMetadata("request_id", "req-123").
		WithMetadata("user_id", "user-456")

	logger.Error("Structured error created",
		logs.String("error", err.Error()),
		logs.String("code", err.Code().String()),
		logs.String("category", err.Category().String()),
		logs.Bool("retryable", err.IsRetryable()),
	)

	// 包装错误
	originalErr := errors.New("connection refused")
	wrappedErr := otelerrors.Wrap(originalErr, "database connection failed").
		WithCode(otelerrors.CodeUnavailable).
		WithCategory(otelerrors.CategoryNetwork)

	logger.Error("Wrapped error",
		logs.String("error", wrappedErr.Error()),
		logs.String("cause", otelerrors.Cause(wrappedErr).Error()),
	)

	// 检查错误是否可以重试
	if otelerrors.IsRetryable(wrappedErr) {
		logger.Info("Error is retryable")
	}

	// 在 Span 中记录错误
	tracer := sdk.Tracer("complete-demo")
	_, span := tracer.Start(ctx, "error-demo")
	span.RecordError(err)
	span.End()
}

// demonstratePerformanceOptimizations 演示性能优化功能
func demonstratePerformanceOptimizations(ctx context.Context, sdk *otel.SDK, logger *logs.Logger) {
	logger.Info("=== Performance Optimizations Demo ===")

	// 使用性能分析器
	profiler := performance.NewProfiler(performance.ProfilerConfig{
		Enabled:     true,
		SampleRate:  1.0,
		MaxDepth:    32,
		RecordAlloc: true,
	})

	// 开始分析
	profiler.Start()

	// 使用对象池
	pool := performance.NewSpanPool(100)

	// 从池中获取对象
	span := pool.Get()
	span.Name = "pooled-span"
	span.StartTime = time.Now()

	// 模拟工作
	time.Sleep(10 * time.Millisecond)

	span.EndTime = time.Now()

	// 归还到池中
	pool.Put(span)

	logger.Info("Performance optimization demo completed",
		logs.Int("pool_size", 100),
	)

	// 停止分析器
	profiler.Stop()
}

// demonstrateConcurrency 演示并发处理
func demonstrateConcurrency(ctx context.Context, sdk *otel.SDK, logger *logs.Logger) {
	logger.Info("=== Concurrency Demo ===")

	tracer := sdk.Tracer("complete-demo")
	meter := sdk.Meter("complete-demo")

	// 创建计数器
	taskCounter, _ := meter.Int64Counter("demo.concurrent_tasks")

	var wg sync.WaitGroup
	numTasks := 5

	for i := range numTasks {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()

			// 每个 goroutine 有自己的 Span
			ctx, span := tracer.Start(ctx, fmt.Sprintf("concurrent-task-%d", id))
			defer span.End()

			span.SetAttributes(logs.Int("task.id", id))

			// 模拟工作
			duration := time.Duration(rand.IntN(50)+10) * time.Millisecond
			time.Sleep(duration)

			taskCounter.Add(ctx, 1)

			logger.InfoContext(ctx, "Task completed",
				logs.Int("task_id", id),
				logs.Duration("duration", duration),
			)
		}(i)
	}

	wg.Wait()
	logger.Info("All concurrent tasks completed", logs.Int("task_count", numTasks))
}

// setupGracefulShutdown 设置优雅关闭
func setupGracefulShutdown(sdk *otel.SDK, logger *logs.Logger) *shutdown.Orchestrator {
	orchestrator := shutdown.NewOrchestrator(
		shutdown.WithTimeout(30*time.Second),
		shutdown.WithErrorHandler(func(stage shutdown.Stage, hook string, err error) {
			logger.Error("Shutdown error",
				logs.String("stage", stage.String()),
				logs.String("hook", hook),
				logs.Error(err),
			)
		}),
	)

	// 注册关闭钩子
	orchestrator.RegisterPreShutdown("flush-telemetry", 1, func(ctx context.Context) error {
		logger.Info("Flushing telemetry data...")
		return sdk.Shutdown(ctx)
	})

	orchestrator.RegisterShutdown("cleanup-resources", 1, func(ctx context.Context) error {
		logger.Info("Cleaning up resources...")
		return nil
	})

	orchestrator.RegisterPostShutdown("final-cleanup", 1, func(ctx context.Context) error {
		logger.Info("Final cleanup completed")
		return nil
	})

	return orchestrator
}

// waitForSignal 等待系统信号
func waitForSignal(logger *logs.Logger) {
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)

	logger.Info("Waiting for signal (press Ctrl+C to exit)...")

	select {
	case sig := <-sigCh:
		logger.Info("Received signal", logs.String("signal", sig.String()))
	case <-time.After(5 * time.Second):
		logger.Info("Timeout reached, continuing...")
	}
}

// getEnv 获取环境变量，如果不存在则返回默认值
func getEnv(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

// generateInstanceID 生成实例 ID
func generateInstanceID() string {
	return fmt.Sprintf("instance-%d", time.Now().UnixNano())
}

// otlp-demo - OTLP Go SDK 主演示程序
//
// 本程序展示 OTLP Go SDK 的完整功能，包括:
//   - OpenTelemetry 集成 (Traces + Metrics + Logs)
//   - 资源检测与自动配置
//   - 错误处理与重试机制
//   - 性能优化与对象池
//   - 优雅关闭与信号处理
//   - 并发安全与上下文传播
//
// 使用方法:
//
//	# 运行基本演示
//	go run ./cmd/otlp-demo
//
//	# 指定 OTLP Collector 端点
//	OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317 go run ./cmd/otlp-demo
//
//	# 指定服务名称和版本
//	OTEL_SERVICE_NAME=my-service OTEL_SERVICE_VERSION=1.0.0 go run ./cmd/otlp-demo
//
// 命令行参数:
//
//	--endpoint string    OTLP Collector 端点 (默认: http://localhost:4317)
//	--service string     服务名称 (默认: otlp-demo)
//	--duration duration  演示运行时长 (默认: 30s)
//	--workers int        并发工作线程数 (默认: 3)
package main

import (
	"context"
	"flag"
	"fmt"
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

// Config 保存命令行配置
type AppConfig struct {
	Endpoint    string
	ServiceName string
	Duration    time.Duration
	Workers     int
}

func main() {
	// 解析命令行参数
	cfg := parseFlags()

	// 创建上下文
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// 初始化并运行演示
	if err := runDemo(ctx, cfg); err != nil {
		fmt.Fprintf(os.Stderr, "Demo failed: %v\n", err)
		os.Exit(1)
	}
}

// parseFlags 解析命令行参数
func parseFlags() *AppConfig {
	cfg := &AppConfig{}

	flag.StringVar(&cfg.Endpoint, "endpoint",
		getEnv("OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317"),
		"OTLP Collector endpoint")
	flag.StringVar(&cfg.ServiceName, "service",
		getEnv("OTEL_SERVICE_NAME", "otlp-demo"),
		"Service name")
	flag.DurationVar(&cfg.Duration, "duration", 30*time.Second,
		"Demo duration")
	flag.IntVar(&cfg.Workers, "workers", 3,
		"Number of concurrent workers")

	flag.Parse()

	return cfg
}

// runDemo 运行演示程序
func runDemo(ctx context.Context, cfg *AppConfig) error {
	fmt.Println("╔════════════════════════════════════════════════════════════╗")
	fmt.Println("║          OTLP Go SDK 主演示程序                             ║")
	fmt.Println("║     OpenTelemetry Protocol (OTLP) Go Implementation        ║")
	fmt.Println("╚════════════════════════════════════════════════════════════╝")
	fmt.Println()

	// ========== 1. 初始化 OpenTelemetry SDK ==========
	logger := logs.NewConsoleLogger(logs.LevelInfo)
	logger.Info("Initializing OpenTelemetry SDK...",
		logs.String("service", cfg.ServiceName),
		logs.String("endpoint", cfg.Endpoint),
	)

	otelConfig := &config.OTelConfig{
		ServiceName:           cfg.ServiceName,
		ServiceVersion:        "1.0.0",
		DeploymentEnvironment: "demo",
		Exporter: config.OTLPExporterConfig{
			Endpoint:    cfg.Endpoint,
			Protocol:    "grpc",
			Compression: "gzip",
			Timeout:     10 * time.Second,
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
			MetricsExportInterval:    10 * time.Second,
			MetricsExportTimeout:     30 * time.Second,
		},
		Tracer: config.TracerConfig{Enabled: true},
		Meter:  config.MeterConfig{Enabled: true},
		Logger: config.LoggerConfig{Enabled: true, Level: "info"},
		Sampling: config.SamplingConfig{
			Strategy: "parentbased_always_on",
			Ratio:    1.0,
		},
	}

	sdk, err := otel.Setup(ctx, otelConfig)
	if err != nil {
		return otelerrors.Wrap(err, "failed to setup OpenTelemetry SDK").
			WithCode(otelerrors.CodeInternal)
	}

	// 设置全局 SDK
	otel.SetGlobalSDK(sdk)

	// 确保优雅关闭
	defer func() {
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		if err := sdk.Shutdown(shutdownCtx); err != nil {
			logger.Error("Failed to shutdown SDK", logs.Error(err))
		}
	}()

	logger.Info("OpenTelemetry SDK initialized successfully")

	// ========== 2. 资源检测 ==========
	fmt.Println("\n📋 资源检测结果:")
	detectResources(ctx, logger)

	// ========== 3. 设置优雅关闭 ==========
	shutdownOrchestrator := setupShutdownHandler(sdk, logger)
	defer shutdownOrchestrator.Execute(ctx)

	// ========== 4. 运行演示任务 ==========
	fmt.Println("\n🚀 开始运行演示任务...")

	// 创建带超时的上下文
	demoCtx, demoCancel := context.WithTimeout(ctx, cfg.Duration)
	defer demoCancel()

	// 启动工作线程
	var wg sync.WaitGroup
	resultCh := make(chan TaskResult, cfg.Workers)

	for i := range cfg.Workers {
		wg.Add(1)
		go worker(demoCtx, &wg, sdk, i, resultCh)
	}

	// 启动指标收集器
	metricsTicker := time.NewTicker(5 * time.Second)
	defer metricsTicker.Stop()

	go collectMetrics(demoCtx, metricsTicker, sdk, logger)

	// 等待所有工作线程完成或超时
	go func() {
		wg.Wait()
		close(resultCh)
	}()

	// 收集结果
	totalTasks := 0
	successfulTasks := 0
	failedTasks := 0

	for result := range resultCh {
		totalTasks++
		if result.Success {
			successfulTasks++
		} else {
			failedTasks++
		}
	}

	// ========== 5. 性能分析 ==========
	fmt.Println("\n📊 性能分析结果:")
	runPerformanceAnalysis(logger)

	// ========== 6. 输出摘要 ==========
	fmt.Println("\n" + "═"*60)
	fmt.Println("📈 演示摘要:")
	fmt.Println("═" * 60)
	fmt.Printf("  总任务数:     %d\n", totalTasks)
	fmt.Printf("  成功任务:     %d\n", successfulTasks)
	fmt.Printf("  失败任务:     %d\n", failedTasks)
	fmt.Printf("  运行时长:     %v\n", cfg.Duration)
	fmt.Printf("  工作线程:     %d\n", cfg.Workers)
	fmt.Println("═" * 60)

	logger.Info("Demo completed successfully",
		logs.Int("total_tasks", totalTasks),
		logs.Int("successful", successfulTasks),
		logs.Int("failed", failedTasks),
	)

	fmt.Println("\n✅ 演示程序成功完成!")

	return nil
}

// TaskResult 表示任务执行结果
type TaskResult struct {
	WorkerID int
	TaskID   int
	Success  bool
	Duration time.Duration
	Error    error
}

// worker 工作线程
func worker(ctx context.Context, wg *sync.WaitGroup, sdk *otel.SDK, workerID int, resultCh chan<- TaskResult) {
	defer wg.Done()

	tracer := sdk.Tracer("demo-worker")
	meter := sdk.Meter("demo-worker")

	// 创建计数器
	taskCounter, _ := meter.Int64Counter("demo.tasks.completed")
	errorCounter, _ := meter.Int64Counter("demo.tasks.errors")

	taskID := 0

	for {
		select {
		case <-ctx.Done():
			return
		default:
		}

		start := time.Now()
		result := TaskResult{
			WorkerID: workerID,
			TaskID:   taskID,
		}

		// 创建任务 Span
		_, span := tracer.Start(ctx, fmt.Sprintf("worker-%d-task-%d", workerID, taskID))

		// 模拟工作
		if err := simulateWork(workerID, taskID); err != nil {
			result.Success = false
			result.Error = err
			span.RecordError(err)
			errorCounter.Add(ctx, 1)
		} else {
			result.Success = true
			taskCounter.Add(ctx, 1)
		}

		result.Duration = time.Since(start)
		span.SetAttributes(
			logs.Int("worker.id", workerID),
			logs.Int("task.id", taskID),
			logs.Bool("task.success", result.Success),
			logs.Int64("task.duration_ms", result.Duration.Milliseconds()),
		)
		span.End()

		resultCh <- result

		taskID++

		// 短暂休息
		select {
		case <-ctx.Done():
			return
		case <-time.After(500 * time.Millisecond):
		}
	}
}

// simulateWork 模拟工作任务
func simulateWork(workerID, taskID int) error {
	// 模拟随机延迟
	delay := time.Duration(50+taskID*10) * time.Millisecond
	time.Sleep(delay)

	// 模拟随机错误 (10% 概率)
	if taskID%10 == 0 {
		return otelerrors.Newf("simulated error in worker %d, task %d", workerID, taskID).
			WithCode(otelerrors.CodeInternal).
			WithCategory(otelerrors.CategorySystem).
			WithRetryable(true)
	}

	return nil
}

// collectMetrics 定期收集和报告指标
func collectMetrics(ctx context.Context, ticker *time.Ticker, sdk *otel.SDK, logger *logs.StructuredLogger) {
	meter := sdk.Meter("demo-metrics")

	// 创建运行时指标
	memoryGauge, _ := meter.Int64ObservableGauge("demo.memory.usage_bytes")
	goroutineGauge, _ := meter.Int64ObservableGauge("demo.goroutine.count")

	_ = memoryGauge
	_ = goroutineGauge

	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			// 记录当前指标
			var m syscall.Rusage
			if err := syscall.Getrusage(syscall.RUSAGE_SELF, &m); err == nil {
				logger.Info("Metrics snapshot",
					logs.Int64("memory_kb", m.Maxrss),
				)
			}
		}
	}
}

// detectResources 检测并显示资源信息
func detectResources(ctx context.Context, logger *logs.StructuredLogger) {
	detectors := []resource.Detector{
		&resource.HostDetector{},
		&resource.EnvironmentDetector{},
	}

	for _, detector := range detectors {
		res, err := detector.Detect(ctx)
		if err != nil {
			logger.Warn("Failed to detect resources",
				logs.String("detector", detector.DetectorType()),
				logs.Error(err),
			)
			continue
		}

		fmt.Printf("  ✓ %s: ", detector.DetectorType())
		if res != nil && !res.IsEmpty() {
			attrs := res.Attributes.ToMap()
			if len(attrs) > 0 {
				fmt.Printf("%d attributes detected\n", len(attrs))
			} else {
				fmt.Println("no attributes")
			}
		} else {
			fmt.Println("empty")
		}
	}
}

// runPerformanceAnalysis 运行性能分析
func runPerformanceAnalysis(logger *logs.StructuredLogger) {
	// 创建性能分析器
	profiler := performance.NewProfiler(performance.ProfilerConfig{
		Enabled:     true,
		SampleRate:  1.0,
		MaxDepth:    32,
		RecordAlloc: true,
	})

	profiler.Start()

	// 使用对象池进行性能测试
	pool := performance.NewSpanPool(1000)

	// 测试对象池性能
	start := time.Now()
	iterations := 10000

	for i := range iterations {
		span := pool.Get()
		span.Name = fmt.Sprintf("span-%d", i)
		span.StartTime = time.Now()
		span.EndTime = time.Now()
		pool.Put(span)
	}

	duration := time.Since(start)
	opsPerSecond := float64(iterations) / duration.Seconds()

	profiler.Stop()

	fmt.Printf("  对象池性能: %d 操作 in %v (%.0f ops/sec)\n",
		iterations, duration, opsPerSecond)

	logger.Info("Performance analysis completed",
		logs.Int("iterations", iterations),
		logs.Duration("duration", duration),
		logs.Float64("ops_per_second", opsPerSecond),
	)
}

// setupShutdownHandler 设置优雅关闭处理器
func setupShutdownHandler(sdk *otel.SDK, logger *logs.StructuredLogger) *shutdown.Orchestrator {
	orchestrator := shutdown.NewOrchestrator(
		shutdown.WithTimeout(30*time.Second),
		shutdown.WithErrorHandler(func(stage shutdown.Stage, hook string, err error) {
			logger.Error("Shutdown error",
				logs.String("stage", stage.String()),
				logs.String("hook", hook),
				logs.Error(err),
			)
		}),
		shutdown.WithCompleteHandler(func() {
			fmt.Println("\n👋 优雅关闭完成")
		}),
	)

	// 注册关闭钩子
	orchestrator.RegisterPreShutdown("flush-telemetry", 1, func(ctx context.Context) error {
		fmt.Println("\n🔄 正在刷新遥测数据...")
		return sdk.Shutdown(ctx)
	})

	orchestrator.RegisterShutdown("cleanup-resources", 1, func(ctx context.Context) error {
		logger.Info("Cleaning up resources")
		return nil
	})

	// 设置信号处理
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)

	go func() {
		sig := <-sigCh
		logger.Info("Received shutdown signal", logs.String("signal", sig.String()))

		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()

		if err := orchestrator.Execute(ctx); err != nil {
			logger.Error("Shutdown failed", logs.Error(err))
			os.Exit(1)
		}

		os.Exit(0)
	}()

	return orchestrator
}

// getEnv 获取环境变量，如果不存在则返回默认值
func getEnv(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

// init 初始化函数
func init() {
	// 设置时区
	time.Local = time.UTC
}

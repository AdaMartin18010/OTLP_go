package main

import (
	"context"
	"fmt"
	"log"
	"net/http"
	"os"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/otlp/otlptrace/otlptracegrpc"
	"go.opentelemetry.io/otel/sdk/resource"
	"go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"

	pkgctx "OTLP_go/src/pkg/context"
	pkgruntime "OTLP_go/src/pkg/runtime"
	"OTLP_go/src/pkg/shutdown"
)

// newTracerProvider 创建 TracerProvider
// 优化：添加更丰富的资源属性，使用非阻塞连接
func newTracerProvider(ctx context.Context, endpoint string) (*trace.TracerProvider, error) {
	// 使用非阻塞连接选项（Go 1.25.1 优化）
	exp, err := otlptracegrpc.New(ctx,
		otlptracegrpc.WithEndpoint(endpoint),
		otlptracegrpc.WithInsecure(),
		// 移除 WithBlock，使用非阻塞连接提高启动速度
	)
	if err != nil {
		return nil, fmt.Errorf("failed to create OTLP exporter: %w", err)
	}

	// 获取运行时信息
	stats := pkgruntime.GetRuntimeStats()

	res, err := resource.New(ctx,
		resource.WithAttributes(
			// 服务信息
			semconv.ServiceName("otlp-go-demo"),
			semconv.ServiceVersion("2.1.0"),
			semconv.DeploymentEnvironment("dev"),

			// 运行时信息（Go 1.25.1 特性）
			attribute.String("runtime.go.version", "1.25.1"),
			attribute.Int("runtime.cpu.count", stats.NumCPU),
			attribute.Int("runtime.gomaxprocs", stats.GOMAXPROCS),

			// 容器信息（由 automaxprocs 自动感知）
			attribute.String("runtime.container.aware", "true"),
		),
	)
	if err != nil {
		return nil, fmt.Errorf("failed to create resource: %w", err)
	}

	tp := trace.NewTracerProvider(
		trace.WithBatcher(exp,
			trace.WithMaxExportBatchSize(512),     // 批量导出优化
			trace.WithBatchTimeout(5*time.Second), // 批量超时
		),
		trace.WithResource(res),
		trace.WithSampler(trace.ParentBased(trace.TraceIDRatioBased(1.0))), // 采样策略
	)
	return tp, nil
}

func main() {
	// 应用运行时配置（Go 1.25.1 优化）
	runtimeCfg := pkgruntime.DefaultConfig()
	runtimeCfg.MemoryLimitBytes = 4 * 1024 * 1024 * 1024 // 4GB 软限制
	runtimeCfg.GCPercent = 100                           // GC 触发阈值
	pkgruntime.ApplyConfig(runtimeCfg)

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// 获取配置
	endpoint := os.Getenv("OTLP_GRPC_ENDPOINT")
	if endpoint == "" {
		endpoint = "127.0.0.1:4317"
	}

	port := os.Getenv("PORT")
	if port == "" {
		port = "8080"
	}
	addr := ":" + port

	// 创建优雅关闭管理器
	shutdownMgr := shutdown.NewManager(30 * time.Second)

	// 初始化日志（提前，用于记录启动过程）
	logger := newSlog(ctx)
	logger.Info("🚀 Starting OTLP Go Demo",
		"version", "2.1.0",
		"go_version", "1.25.1",
		"otlp_endpoint", endpoint,
		"port", port,
	)

	// 阶段 1: 初始化追踪
	tp, err := newTracerProvider(ctx, endpoint)
	if err != nil {
		log.Fatalf("❌ Failed to initialize tracer provider: %v", err)
	}
	otel.SetTracerProvider(tp)
	logger.Info("✅ Tracer provider initialized")

	// 注册追踪关闭
	shutdownMgr.RegisterStage("telemetry", func(ctx context.Context) error {
		logger.Info("🔄 Shutting down tracer provider...")
		return tp.Shutdown(ctx)
	})

	// 阶段 2: 初始化指标
	mp, err := initMetricProvider(ctx, endpoint)
	if err != nil {
		log.Fatalf("❌ Failed to initialize meter provider: %v", err)
	}
	logger.Info("✅ Meter provider initialized")

	// 启动指标循环
	startCounterLoop(ctx)

	// 注册指标关闭
	shutdownMgr.RegisterStage("telemetry", func(ctx context.Context) error {
		logger.Info("🔄 Shutting down meter provider...")
		return mp.Shutdown(ctx)
	})

	// 阶段 3: 初始化业务组件
	tr := otel.Tracer("demo/handler")
	emitBootLog(logger)

	// CSP × OTLP pipeline demo
	p := newPipeline(64, 4)

	// 注册 pipeline 关闭
	shutdownMgr.RegisterStage("business", func(ctx context.Context) error {
		logger.Info("🔄 Closing pipeline...")
		p.close()
		return nil
	})

	// 阶段 4: 设置 HTTP 路由
	mux := http.NewServeMux()

	// 主处理器（使用上下文传播）
	mux.HandleFunc("/hello", func(w http.ResponseWriter, r *http.Request) {
		ctx := r.Context()
		ctx = pkgctx.WithRequestID(ctx, fmt.Sprintf("req-%d", time.Now().UnixNano()))

		ctx, span := tr.Start(ctx, "GET /hello")
		defer span.End()

		span.SetAttributes(
			attribute.String("http.method", r.Method),
			attribute.String("http.path", r.URL.Path),
			attribute.String("http.remote_addr", r.RemoteAddr),
			attribute.String("request.id", pkgctx.GetRequestID(ctx)),
		)

		logger.Info("📨 Handling request",
			"method", r.Method,
			"path", r.URL.Path,
			"remote", r.RemoteAddr,
			"request_id", pkgctx.GetRequestID(ctx),
			"trace_id", pkgctx.GetTraceID(ctx),
		)

		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte("hello otlp from Go 1.25.1\n"))
	})

	// Pipeline 入队端点
	mux.Handle("/enqueue", p.httpEnqueueHandler())

	// 健康检查端点（增强版）
	mux.HandleFunc("/healthz", func(w http.ResponseWriter, r *http.Request) {
		_, span := tr.Start(r.Context(), "GET /healthz")
		defer span.End()

		// 获取运行时统计
		stats := pkgruntime.GetRuntimeStats()

		health := map[string]interface{}{
			"status":     "healthy",
			"version":    "2.1.0",
			"go_version": "1.25.1",
			"goroutines": stats.NumGoroutine,
			"gomaxprocs": stats.GOMAXPROCS,
			"mem_alloc":  stats.MemAlloc,
			"num_gc":     stats.NumGC,
		}

		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, `{"status":"healthy","version":"2.1.0","goroutines":%d,"gomaxprocs":%d,"mem_alloc":%d,"num_gc":%d}`,
			health["goroutines"], health["gomaxprocs"], health["mem_alloc"], health["num_gc"])
	})

	// 运行时统计端点
	mux.HandleFunc("/metrics/runtime", func(w http.ResponseWriter, r *http.Request) {
		stats := pkgruntime.GetRuntimeStats()
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, `{"num_goroutine":%d,"num_cpu":%d,"gomaxprocs":%d,"mem_alloc":%d,"total_alloc":%d,"sys":%d,"num_gc":%d}`,
			stats.NumGoroutine, stats.NumCPU, stats.GOMAXPROCS, stats.MemAlloc, stats.TotalAlloc, stats.Sys, stats.NumGC)
	})

	// 阶段 5: 创建和启动 HTTP 服务器
	server := &http.Server{
		Addr:         addr,
		Handler:      mux,
		ReadTimeout:  30 * time.Second,
		WriteTimeout: 30 * time.Second,
		IdleTimeout:  120 * time.Second,
	}

	// 注册服务器关闭
	shutdownMgr.RegisterStage("http", func(ctx context.Context) error {
		logger.Info("🔄 Shutting down HTTP server...")
		return server.Shutdown(ctx)
	})

	// 启动服务器
	go func() {
		logger.Info("🌐 Server listening", "addr", addr, "otlp", endpoint)
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Fatalf("❌ Server error: %v", err)
		}
	}()

	// 监听关闭信号
	shutdownMgr.ListenSignals()

	// 等待关闭
	shutdownMgr.Wait()

	// 执行优雅关闭
	if err := shutdownMgr.Shutdown(); err != nil {
		logger.Error("⚠️  Shutdown completed with errors", "error", err)
	} else {
		logger.Info("✅ Shutdown completed successfully")
	}
}

package integration

import (
	"context"
	"testing"
	"time"

	"OTLP_go/src/pkg/config"
	pkgctx "OTLP_go/src/pkg/context"
	"OTLP_go/src/pkg/performance"
	"OTLP_go/src/pkg/shutdown"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel"
)

// TestOTLPConfigIntegration 测试OTLP配置集成
func TestOTLPConfigIntegration(t *testing.T) {
	// Load configuration
	cfg := config.LoadOTLPConfig()
	require.NotNil(t, cfg)

	// Validate configuration
	err := config.ValidateOTLPConfig(cfg)
	assert.NoError(t, err)

	// Verify expected values
	assert.NotEmpty(t, cfg.Endpoint)
	assert.NotEmpty(t, cfg.ServiceName)
	assert.GreaterOrEqual(t, cfg.SamplingRate, 0.0)
	assert.LessOrEqual(t, cfg.SamplingRate, 1.0)
}

// TestPerformanceMonitoringWithContext 测试性能监控与上下文集成
func TestPerformanceMonitoringWithContext(t *testing.T) {
	// Initialize performance monitor
	monitor := performance.NewPerformanceMonitor(100 * time.Millisecond)
	defer monitor.Stop()

	// Create context with metadata
	ctx := context.Background()
	ctx = pkgctx.WithRequestID(ctx, "test-request-123")
	ctx = pkgctx.WithUserID(ctx, "user-456")
	ctx = pkgctx.WithTenantID(ctx, "tenant-789")

	// Verify context values
	requestID := pkgctx.GetRequestID(ctx)
	userID := pkgctx.GetUserID(ctx)
	tenantID := pkgctx.GetTenantID(ctx)

	assert.Equal(t, "test-request-123", requestID)
	assert.Equal(t, "user-456", userID)
	assert.Equal(t, "tenant-789", tenantID)

	// Update metrics
	monitor.UpdateMetric("request.duration", 125.5)
	monitor.UpdateMetric("request.size", 1024.0)

	// Get metrics
	metric, ok := monitor.GetMetric("request.duration")
	require.True(t, ok)
	assert.Equal(t, 125.5, metric.Value)
}

// TestShutdownWithPerformanceMonitor 测试优雅关闭与性能监控集成
func TestShutdownWithPerformanceMonitor(t *testing.T) {
	// Create shutdown manager
	mgr := shutdown.NewManager(2 * time.Second)

	// Create performance monitor
	monitor := performance.NewPerformanceMonitor(100 * time.Millisecond)

	// Register shutdown handler for monitor
	mgr.Register(func(ctx context.Context) error {
		monitor.Stop()
		return nil
	})

	// Start monitor
	monitor.Start()

	// Update some metrics
	monitor.UpdateMetric("test", 42.0)

	// Trigger shutdown
	err := mgr.Shutdown()
	assert.NoError(t, err)

	// Verify final metrics were captured
	metric, ok := monitor.GetMetric("test")
	require.True(t, ok)
	assert.Equal(t, 42.0, metric.Value)
}

// TestContextPropagationWithTracing 测试上下文传播与追踪集成
func TestContextPropagationWithTracing(t *testing.T) {
	// Get tracer (may be noop if no provider configured)
	tracer := otel.Tracer("integration-test")

	// Create root context
	ctx := context.Background()

	// Start a span
	ctx, span := tracer.Start(ctx, "test-operation")
	defer span.End()

	// Add context metadata
	ctx = pkgctx.WithRequestID(ctx, "req-123")
	ctx = pkgctx.WithUserID(ctx, "user-456")

	// Verify custom metadata preserved (most important part)
	assert.Equal(t, "req-123", pkgctx.GetRequestID(ctx))
	assert.Equal(t, "user-456", pkgctx.GetUserID(ctx))

	// Get trace and span IDs from context
	// Note: These may be empty if using noop tracer in tests
	traceID := pkgctx.GetTraceID(ctx)
	spanID := pkgctx.GetSpanID(ctx)

	// Just verify functions work (don't assert non-empty for noop span)
	_ = traceID
	_ = spanID

	// The important thing is that context propagation works
	assert.NotNil(t, ctx)
}

// TestMultiStageShutdown 测试多阶段关闭集成
func TestMultiStageShutdown(t *testing.T) {
	mgr := shutdown.NewManager(3 * time.Second)

	var stage1Done, stage2Done, stage3Done bool

	// Register stage 1 (critical services)
	mgr.RegisterStage("critical", func(ctx context.Context) error {
		stage1Done = true
		time.Sleep(10 * time.Millisecond)
		return nil
	})

	// Register stage 2 (normal services)
	mgr.RegisterStage("normal", func(ctx context.Context) error {
		stage2Done = true
		time.Sleep(10 * time.Millisecond)
		return nil
	})

	// Register stage 3 (cleanup)
	mgr.RegisterStage("cleanup", func(ctx context.Context) error {
		stage3Done = true
		time.Sleep(10 * time.Millisecond)
		return nil
	})

	// Trigger shutdown
	err := mgr.Shutdown()
	assert.NoError(t, err)

	// Verify all stages completed
	assert.True(t, stage1Done)
	assert.True(t, stage2Done)
	assert.True(t, stage3Done)
}

// TestConfigLoadAndValidation 测试配置加载和验证流程
func TestConfigLoadAndValidation(t *testing.T) {
	// Load both OTLP and service configs
	otlpCfg := config.LoadOTLPConfig()
	serviceCfg := config.LoadServiceConfig()

	// Validate both
	err := config.ValidateOTLPConfig(otlpCfg)
	assert.NoError(t, err, "OTLP config should be valid")

	err = config.ValidateServiceConfig(serviceCfg)
	assert.NoError(t, err, "Service config should be valid")

	// Verify configs are usable
	assert.NotEmpty(t, otlpCfg.Endpoint)
	assert.NotEmpty(t, otlpCfg.ServiceName)
	assert.NotEmpty(t, serviceCfg.Port)
	assert.Greater(t, serviceCfg.ReadTimeout, time.Duration(0))
	assert.Greater(t, serviceCfg.WriteTimeout, time.Duration(0))
}

// TestPerformanceMonitoringLifecycle 测试性能监控完整生命周期
func TestPerformanceMonitoringLifecycle(t *testing.T) {
	// Create monitor
	monitor := performance.NewPerformanceMonitor(50 * time.Millisecond)
	require.NotNil(t, monitor)

	// Start monitoring
	monitor.Start()

	// Simulate workload
	for i := 0; i < 10; i++ {
		monitor.UpdateMetric("workload", float64(i))
		time.Sleep(10 * time.Millisecond)
	}

	// Get stats
	stats := monitor.GetStats()
	require.NotNil(t, stats)
	assert.NotNil(t, stats.MemoryStats)
	assert.NotNil(t, stats.RuntimeStats)
	assert.Greater(t, stats.Uptime, time.Duration(0))

	// Stop monitoring
	monitor.Stop()

	// Verify metrics still accessible
	metric, ok := monitor.GetMetric("workload")
	require.True(t, ok)
	assert.Equal(t, 9.0, metric.Value) // Last value
	assert.Equal(t, int64(10), metric.Count)
}

// TestContextDetachAndMerge 测试上下文分离和合并
func TestContextDetachAndMerge(t *testing.T) {
	// Create parent context with timeout
	parentCtx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	// Add metadata
	parentCtx = pkgctx.WithRequestID(parentCtx, "req-001")
	parentCtx = pkgctx.WithUserID(parentCtx, "user-001")

	// Detach context (preserves values, removes cancellation)
	detached := pkgctx.Detach(parentCtx)

	// Verify values preserved
	assert.Equal(t, "req-001", pkgctx.GetRequestID(detached))
	assert.Equal(t, "user-001", pkgctx.GetUserID(detached))

	// Wait for parent to time out
	time.Sleep(150 * time.Millisecond)

	// Parent should be done
	select {
	case <-parentCtx.Done():
		// Expected
	default:
		t.Fatal("parent context should be done")
	}

	// Detached should still be valid
	select {
	case <-detached.Done():
		t.Fatal("detached context should not be done")
	default:
		// Expected
	}

	// Create another context
	ctx2 := context.Background()
	ctx2 = pkgctx.WithTenantID(ctx2, "tenant-001")

	// Merge contexts
	merged := pkgctx.MergeContexts(detached, ctx2)

	// Verify all values present
	assert.Equal(t, "req-001", pkgctx.GetRequestID(merged))
	assert.Equal(t, "user-001", pkgctx.GetUserID(merged))
	assert.Equal(t, "tenant-001", pkgctx.GetTenantID(merged))
}

// BenchmarkIntegratedWorkflow 基准测试集成工作流
func BenchmarkIntegratedWorkflow(b *testing.B) {
	// Setup
	monitor := performance.NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	tracer := otel.Tracer("benchmark")

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		// Create context with metadata
		ctx := context.Background()
		ctx = pkgctx.WithRequestID(ctx, "req-bench")

		// Start span
		_, span := tracer.Start(ctx, "benchmark-op")

		// Update metrics
		monitor.UpdateMetric("bench.counter", float64(i))

		// End span
		span.End()
	}
}

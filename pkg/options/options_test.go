package options

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestApply 测试Apply函数
func TestApply(t *testing.T) {
	type TestConfig struct {
		Value int
		Name  string
	}

	cfg := &TestConfig{}

	Apply(cfg,
		func(c *TestConfig) { c.Value = 42 },
		func(c *TestConfig) { c.Name = "test" },
	)

	assert.Equal(t, 42, cfg.Value)
	assert.Equal(t, "test", cfg.Name)
}

// TestDefaultServerConfig 测试默认服务器配置
func TestDefaultServerConfig(t *testing.T) {
	cfg := DefaultServerConfig()

	require.NotNil(t, cfg)
	assert.Equal(t, ":8080", cfg.Addr)
	assert.Equal(t, 30*time.Second, cfg.ReadTimeout)
	assert.Equal(t, 30*time.Second, cfg.WriteTimeout)
	assert.Equal(t, 120*time.Second, cfg.IdleTimeout)
	assert.Equal(t, 1<<20, cfg.MaxHeaderBytes)
	assert.True(t, cfg.EnableKeepalive)
	assert.False(t, cfg.EnableTLS)
}

// TestWithAddr 测试设置地址
func TestWithAddr(t *testing.T) {
	cfg := DefaultServerConfig()
	Apply(cfg, WithAddr(":9090"))

	assert.Equal(t, ":9090", cfg.Addr)
}

// TestWithReadTimeout 测试设置读超时
func TestWithReadTimeout(t *testing.T) {
	cfg := DefaultServerConfig()
	Apply(cfg, WithReadTimeout(60*time.Second))

	assert.Equal(t, 60*time.Second, cfg.ReadTimeout)
}

// TestWithWriteTimeout 测试设置写超时
func TestWithWriteTimeout(t *testing.T) {
	cfg := DefaultServerConfig()
	Apply(cfg, WithWriteTimeout(45*time.Second))

	assert.Equal(t, 45*time.Second, cfg.WriteTimeout)
}

// TestWithIdleTimeout 测试设置空闲超时
func TestWithIdleTimeout(t *testing.T) {
	cfg := DefaultServerConfig()
	Apply(cfg, WithIdleTimeout(180*time.Second))

	assert.Equal(t, 180*time.Second, cfg.IdleTimeout)
}

// TestWithMaxHeaderBytes 测试设置最大头部大小
func TestWithMaxHeaderBytes(t *testing.T) {
	cfg := DefaultServerConfig()
	Apply(cfg, WithMaxHeaderBytes(2<<20))

	assert.Equal(t, 2<<20, cfg.MaxHeaderBytes)
}

// TestWithKeepalive 测试启用/禁用Keepalive
func TestWithKeepalive(t *testing.T) {
	cfg := DefaultServerConfig()

	// Disable keepalive
	Apply(cfg, WithKeepalive(false))
	assert.False(t, cfg.EnableKeepalive)

	// Enable keepalive
	Apply(cfg, WithKeepalive(true))
	assert.True(t, cfg.EnableKeepalive)
}

// TestWithTLS 测试配置TLS
func TestWithTLS(t *testing.T) {
	cfg := DefaultServerConfig()
	Apply(cfg, WithTLS("/path/to/cert.pem", "/path/to/key.pem"))

	assert.True(t, cfg.EnableTLS)
	assert.Equal(t, "/path/to/cert.pem", cfg.TLSCertFile)
	assert.Equal(t, "/path/to/key.pem", cfg.TLSKeyFile)
}

// TestMultipleServerOptions 测试多个服务器选项
func TestMultipleServerOptions(t *testing.T) {
	cfg := DefaultServerConfig()

	Apply(cfg,
		WithAddr(":3000"),
		WithReadTimeout(15*time.Second),
		WithWriteTimeout(20*time.Second),
		WithKeepalive(false),
	)

	assert.Equal(t, ":3000", cfg.Addr)
	assert.Equal(t, 15*time.Second, cfg.ReadTimeout)
	assert.Equal(t, 20*time.Second, cfg.WriteTimeout)
	assert.False(t, cfg.EnableKeepalive)
}

// TestDefaultClientConfig 测试默认客户端配置
func TestDefaultClientConfig(t *testing.T) {
	cfg := DefaultClientConfig()

	require.NotNil(t, cfg)
	assert.Equal(t, 30*time.Second, cfg.Timeout)
	assert.Equal(t, 3, cfg.MaxRetries)
	assert.Equal(t, 1*time.Second, cfg.RetryDelay)
	assert.Equal(t, 100, cfg.MaxIdleConns)
	assert.Equal(t, 10, cfg.MaxConnsPerHost)
	assert.True(t, cfg.EnableTrace)
	assert.True(t, cfg.EnableMetrics)
}

// TestWithTimeout 测试设置超时
func TestWithTimeout(t *testing.T) {
	cfg := DefaultClientConfig()
	Apply(cfg, WithTimeout(60*time.Second))

	assert.Equal(t, 60*time.Second, cfg.Timeout)
}

// TestWithRetries 测试设置重试次数和延迟
func TestWithRetries(t *testing.T) {
	cfg := DefaultClientConfig()
	Apply(cfg, WithRetries(5, 2*time.Second))

	assert.Equal(t, 5, cfg.MaxRetries)
	assert.Equal(t, 2*time.Second, cfg.RetryDelay)
}

// TestWithTrace 测试启用/禁用追踪
func TestWithTrace(t *testing.T) {
	cfg := DefaultClientConfig()

	// Disable trace
	Apply(cfg, WithTrace(false))
	assert.False(t, cfg.EnableTrace)

	// Enable trace
	Apply(cfg, WithTrace(true))
	assert.True(t, cfg.EnableTrace)
}

// TestWithClientMetrics 测试启用/禁用指标
func TestWithClientMetrics(t *testing.T) {
	cfg := DefaultClientConfig()

	// Disable metrics
	Apply(cfg, WithMetrics(false))
	assert.False(t, cfg.EnableMetrics)

	// Enable metrics
	Apply(cfg, WithMetrics(true))
	assert.True(t, cfg.EnableMetrics)
}

// TestWithConnectionPool 测试配置连接池
func TestWithConnectionPool(t *testing.T) {
	cfg := DefaultClientConfig()
	Apply(cfg, WithConnectionPool(200, 20))

	assert.Equal(t, 200, cfg.MaxIdleConns)
	assert.Equal(t, 20, cfg.MaxConnsPerHost)
}

// TestMultipleClientOptions 测试多个客户端选项
func TestMultipleClientOptions(t *testing.T) {
	cfg := DefaultClientConfig()

	Apply(cfg,
		WithTimeout(20*time.Second),
		WithRetries(10, 3*time.Second),
		WithTrace(false),
		WithMetrics(true),
		WithConnectionPool(150, 15),
	)

	assert.Equal(t, 20*time.Second, cfg.Timeout)
	assert.Equal(t, 10, cfg.MaxRetries)
	assert.Equal(t, 3*time.Second, cfg.RetryDelay)
	assert.False(t, cfg.EnableTrace)
	assert.True(t, cfg.EnableMetrics)
	assert.Equal(t, 150, cfg.MaxIdleConns)
	assert.Equal(t, 15, cfg.MaxConnsPerHost)
}

// TestDefaultWorkerPoolConfig 测试默认工作池配置
func TestDefaultWorkerPoolConfig(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()

	require.NotNil(t, cfg)
	assert.Equal(t, 10, cfg.WorkerCount)
	assert.Equal(t, 100, cfg.QueueSize)
	assert.Equal(t, 3, cfg.MaxRetries)
	assert.Equal(t, 30*time.Second, cfg.TaskTimeout)
	assert.True(t, cfg.EnableMetrics)
	assert.True(t, cfg.EnableTrace)
}

// TestWithWorkers 测试设置工作者数量
func TestWithWorkers(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()
	Apply(cfg, WithWorkers(20))

	assert.Equal(t, 20, cfg.WorkerCount)
}

// TestWithQueueSize 测试设置队列大小
func TestWithQueueSize(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()
	Apply(cfg, WithQueueSize(500))

	assert.Equal(t, 500, cfg.QueueSize)
}

// TestWithTaskTimeout 测试设置任务超时
func TestWithTaskTimeout(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()
	Apply(cfg, WithTaskTimeout(60*time.Second))

	assert.Equal(t, 60*time.Second, cfg.TaskTimeout)
}

// TestWithMaxRetriesWorkerPool 测试设置最大重试次数
func TestWithMaxRetriesWorkerPool(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()
	Apply(cfg, WithMaxRetries(5))

	assert.Equal(t, 5, cfg.MaxRetries)
}

// TestWithTelemetry 测试配置遥测
func TestWithTelemetry(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()

	// Disable both
	Apply(cfg, WithTelemetry(false, false))
	assert.False(t, cfg.EnableMetrics)
	assert.False(t, cfg.EnableTrace)

	// Enable metrics only
	Apply(cfg, WithTelemetry(true, false))
	assert.True(t, cfg.EnableMetrics)
	assert.False(t, cfg.EnableTrace)

	// Enable both
	Apply(cfg, WithTelemetry(true, true))
	assert.True(t, cfg.EnableMetrics)
	assert.True(t, cfg.EnableTrace)
}

// TestMultipleWorkerPoolOptions 测试多个工作池选项
func TestMultipleWorkerPoolOptions(t *testing.T) {
	cfg := DefaultWorkerPoolConfig()

	Apply(cfg,
		WithWorkers(50),
		WithQueueSize(1000),
		WithTaskTimeout(45*time.Second),
		WithMaxRetries(10),
		WithTelemetry(false, true),
	)

	assert.Equal(t, 50, cfg.WorkerCount)
	assert.Equal(t, 1000, cfg.QueueSize)
	assert.Equal(t, 45*time.Second, cfg.TaskTimeout)
	assert.Equal(t, 10, cfg.MaxRetries)
	assert.False(t, cfg.EnableMetrics)
	assert.True(t, cfg.EnableTrace)
}

// TestOptionOrder 测试选项顺序（后者覆盖前者）
func TestOptionOrder(t *testing.T) {
	cfg := DefaultServerConfig()

	Apply(cfg,
		WithAddr(":8080"),
		WithAddr(":9090"), // Should override
		WithReadTimeout(10*time.Second),
		WithReadTimeout(20*time.Second), // Should override
	)

	assert.Equal(t, ":9090", cfg.Addr)
	assert.Equal(t, 20*time.Second, cfg.ReadTimeout)
}

// TestEmptyOptions 测试空选项
func TestEmptyOptions(t *testing.T) {
	cfg := DefaultServerConfig()
	original := *cfg

	Apply(cfg) // No options

	assert.Equal(t, original, *cfg)
}

// TestGenericOptionPattern 测试泛型选项模式
func TestGenericOptionPattern(t *testing.T) {
	type CustomConfig struct {
		Field1 string
		Field2 int
		Field3 bool
	}

	cfg := &CustomConfig{}

	opt1 := func(c *CustomConfig) { c.Field1 = "value1" }
	opt2 := func(c *CustomConfig) { c.Field2 = 42 }
	opt3 := func(c *CustomConfig) { c.Field3 = true }

	Apply(cfg, opt1, opt2, opt3)

	assert.Equal(t, "value1", cfg.Field1)
	assert.Equal(t, 42, cfg.Field2)
	assert.True(t, cfg.Field3)
}

// BenchmarkApply 基准测试Apply函数
func BenchmarkApply(b *testing.B) {
	cfg := DefaultServerConfig()
	opts := []ServerOption{
		WithAddr(":8080"),
		WithReadTimeout(30 * time.Second),
		WithWriteTimeout(30 * time.Second),
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		Apply(cfg, opts...)
	}
}

// BenchmarkServerOptions 基准测试服务器选项
func BenchmarkServerOptions(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		cfg := DefaultServerConfig()
		Apply(cfg,
			WithAddr(":8080"),
			WithReadTimeout(30*time.Second),
			WithWriteTimeout(30*time.Second),
			WithKeepalive(true),
		)
	}
}

// BenchmarkClientOptions 基准测试客户端选项
func BenchmarkClientOptions(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		cfg := DefaultClientConfig()
		Apply(cfg,
			WithTimeout(10*time.Second),
			WithRetries(3, 1*time.Second),
			WithTrace(true),
		)
	}
}

// BenchmarkWorkerPoolOptions 基准测试工作池选项
func BenchmarkWorkerPoolOptions(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		cfg := DefaultWorkerPoolConfig()
		Apply(cfg,
			WithWorkers(10),
			WithQueueSize(100),
			WithTelemetry(true, true),
		)
	}
}

// BenchmarkOptionAllocation 基准测试选项分配
func BenchmarkOptionAllocation(b *testing.B) {
	b.ReportAllocs()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		cfg := DefaultServerConfig()
		Apply(cfg,
			WithAddr(":8080"),
			WithReadTimeout(30*time.Second),
		)
	}
}

package options

import (
	"time"
)

// Option 通用的 Options 模式类型
type Option[T any] func(*T)

// Apply 应用所有选项到目标对象
func Apply[T any](target *T, opts ...Option[T]) {
	for _, opt := range opts {
		opt(target)
	}
}

// --- 示例：Server Options ---

// ServerConfig 服务器配置
type ServerConfig struct {
	Addr            string
	ReadTimeout     time.Duration
	WriteTimeout    time.Duration
	IdleTimeout     time.Duration
	MaxHeaderBytes  int
	EnableKeepalive bool
	EnableTLS       bool
	TLSCertFile     string
	TLSKeyFile      string
}

// DefaultServerConfig 默认服务器配置
func DefaultServerConfig() *ServerConfig {
	return &ServerConfig{
		Addr:            ":8080",
		ReadTimeout:     30 * time.Second,
		WriteTimeout:    30 * time.Second,
		IdleTimeout:     120 * time.Second,
		MaxHeaderBytes:  1 << 20, // 1MB
		EnableKeepalive: true,
		EnableTLS:       false,
	}
}

// ServerOption 服务器选项函数
type ServerOption = Option[ServerConfig]

// WithAddr 设置监听地址
func WithAddr(addr string) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.Addr = addr
	}
}

// WithReadTimeout 设置读超时
func WithReadTimeout(timeout time.Duration) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.ReadTimeout = timeout
	}
}

// WithWriteTimeout 设置写超时
func WithWriteTimeout(timeout time.Duration) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.WriteTimeout = timeout
	}
}

// WithIdleTimeout 设置空闲超时
func WithIdleTimeout(timeout time.Duration) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.IdleTimeout = timeout
	}
}

// WithMaxHeaderBytes 设置最大头部大小
func WithMaxHeaderBytes(bytes int) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.MaxHeaderBytes = bytes
	}
}

// WithKeepalive 启用/禁用 Keepalive
func WithKeepalive(enable bool) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.EnableKeepalive = enable
	}
}

// WithTLS 配置 TLS
func WithTLS(certFile, keyFile string) ServerOption {
	return func(cfg *ServerConfig) {
		cfg.EnableTLS = true
		cfg.TLSCertFile = certFile
		cfg.TLSKeyFile = keyFile
	}
}

// --- 示例：Client Options ---

// ClientConfig 客户端配置
type ClientConfig struct {
	Timeout         time.Duration
	MaxRetries      int
	RetryDelay      time.Duration
	EnableTrace     bool
	EnableMetrics   bool
	MaxIdleConns    int
	MaxConnsPerHost int
}

// DefaultClientConfig 默认客户端配置
func DefaultClientConfig() *ClientConfig {
	return &ClientConfig{
		Timeout:         30 * time.Second,
		MaxRetries:      3,
		RetryDelay:      1 * time.Second,
		EnableTrace:     true,
		EnableMetrics:   true,
		MaxIdleConns:    100,
		MaxConnsPerHost: 10,
	}
}

// ClientOption 客户端选项
type ClientOption = Option[ClientConfig]

// WithTimeout 设置超时
func WithTimeout(timeout time.Duration) ClientOption {
	return func(cfg *ClientConfig) {
		cfg.Timeout = timeout
	}
}

// WithRetries 设置重试次数和延迟
func WithRetries(maxRetries int, delay time.Duration) ClientOption {
	return func(cfg *ClientConfig) {
		cfg.MaxRetries = maxRetries
		cfg.RetryDelay = delay
	}
}

// WithTrace 启用/禁用追踪
func WithTrace(enable bool) ClientOption {
	return func(cfg *ClientConfig) {
		cfg.EnableTrace = enable
	}
}

// WithMetrics 启用/禁用指标
func WithMetrics(enable bool) ClientOption {
	return func(cfg *ClientConfig) {
		cfg.EnableMetrics = enable
	}
}

// WithConnectionPool 配置连接池
func WithConnectionPool(maxIdle, maxPerHost int) ClientOption {
	return func(cfg *ClientConfig) {
		cfg.MaxIdleConns = maxIdle
		cfg.MaxConnsPerHost = maxPerHost
	}
}

// --- 示例：Worker Pool Options ---

// WorkerPoolConfig Worker Pool 配置
type WorkerPoolConfig struct {
	WorkerCount   int
	QueueSize     int
	MaxRetries    int
	EnableMetrics bool
	EnableTrace   bool
	TaskTimeout   time.Duration
}

// DefaultWorkerPoolConfig 默认 Worker Pool 配置
func DefaultWorkerPoolConfig() *WorkerPoolConfig {
	return &WorkerPoolConfig{
		WorkerCount:   10,
		QueueSize:     100,
		MaxRetries:    3,
		EnableMetrics: true,
		EnableTrace:   true,
		TaskTimeout:   30 * time.Second,
	}
}

// WorkerPoolOption Worker Pool 选项
type WorkerPoolOption = Option[WorkerPoolConfig]

// WithWorkers 设置 worker 数量
func WithWorkers(count int) WorkerPoolOption {
	return func(cfg *WorkerPoolConfig) {
		cfg.WorkerCount = count
	}
}

// WithQueueSize 设置队列大小
func WithQueueSize(size int) WorkerPoolOption {
	return func(cfg *WorkerPoolConfig) {
		cfg.QueueSize = size
	}
}

// WithTaskTimeout 设置任务超时
func WithTaskTimeout(timeout time.Duration) WorkerPoolOption {
	return func(cfg *WorkerPoolConfig) {
		cfg.TaskTimeout = timeout
	}
}

// WithMaxRetries 设置最大重试次数
func WithMaxRetries(retries int) WorkerPoolOption {
	return func(cfg *WorkerPoolConfig) {
		cfg.MaxRetries = retries
	}
}

// WithTelemetry 配置遥测
func WithTelemetry(enableMetrics, enableTrace bool) WorkerPoolOption {
	return func(cfg *WorkerPoolConfig) {
		cfg.EnableMetrics = enableMetrics
		cfg.EnableTrace = enableTrace
	}
}

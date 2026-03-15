// Package options provides functional options pattern implementations
// for configuring OTLP Go SDK components.
package options

import (
	"fmt"
	"time"
)

// ProtocolType represents the transport protocol type.
type ProtocolType string

const (
	// ProtocolGRPC uses gRPC transport.
	ProtocolGRPC ProtocolType = "grpc"
	// ProtocolHTTP uses HTTP transport.
	ProtocolHTTP ProtocolType = "http"
)

// IsValid returns true if the protocol type is valid.
func (p ProtocolType) IsValid() bool {
	switch p {
	case ProtocolGRPC, ProtocolHTTP:
		return true
	default:
		return false
	}
}

// String returns the string representation of the protocol type.
func (p ProtocolType) String() string {
	return string(p)
}

// EncodingType represents the payload encoding type.
type EncodingType string

const (
	// EncodingProtobuf uses Protocol Buffers encoding.
	EncodingProtobuf EncodingType = "protobuf"
	// EncodingJSON uses JSON encoding.
	EncodingJSON EncodingType = "json"
)

// IsValid returns true if the encoding type is valid.
func (e EncodingType) IsValid() bool {
	switch e {
	case EncodingProtobuf, EncodingJSON:
		return true
	default:
		return false
	}
}

// String returns the string representation of the encoding type.
func (e EncodingType) String() string {
	return string(e)
}

// ExporterType represents the type of telemetry exporter.
type ExporterType string

const (
	// ExporterTypeTrace exports trace data.
	ExporterTypeTrace ExporterType = "trace"
	// ExporterTypeMetric exports metric data.
	ExporterTypeMetric ExporterType = "metric"
	// ExporterTypeLog exports log data.
	ExporterTypeLog ExporterType = "log"
)

// IsValid returns true if the exporter type is valid.
func (e ExporterType) IsValid() bool {
	switch e {
	case ExporterTypeTrace, ExporterTypeMetric, ExporterTypeLog:
		return true
	default:
		return false
	}
}

// String returns the string representation of the exporter type.
func (e ExporterType) String() string {
	return string(e)
}

// ExporterConfig holds configuration specific to exporters.
type ExporterConfig struct {
	BaseConfig

	// Protocol is the transport protocol to use.
	Protocol ProtocolType

	// Encoding is the payload encoding to use.
	Encoding EncodingType

	// ExporterType is the type of telemetry being exported.
	ExporterType ExporterType

	// URLPath is the URL path for HTTP exports (overrides default).
	URLPath string

	// MaxAttempts is the maximum number of export attempts.
	MaxAttempts int

	// QueueConfig holds the queue configuration.
	QueueConfig *QueueConfig

	// ConnectionConfig holds connection-specific configuration.
	ConnectionConfig *ConnectionConfig

	// ProxyURL is the proxy URL for HTTP connections.
	ProxyURL string

	// UserAgent is the custom user agent string.
	UserAgent string

	// DisableKeepAlive disables HTTP keep-alive.
	DisableKeepAlive bool
}

// QueueConfig holds configuration for the export queue.
type QueueConfig struct {
	// Enabled determines if queuing is enabled.
	Enabled bool

	// Size is the maximum queue size.
	Size int

	// FullAction determines behavior when queue is full.
	FullAction QueueFullAction
}

// QueueFullAction represents the action to take when the queue is full.
type QueueFullAction string

const (
	// QueueFullActionDrop drops new items when queue is full.
	QueueFullActionDrop QueueFullAction = "drop"
	// QueueFullActionBlock blocks until space is available.
	QueueFullActionBlock QueueFullAction = "block"
)

// IsValid returns true if the queue full action is valid.
func (q QueueFullAction) IsValid() bool {
	switch q {
	case QueueFullActionDrop, QueueFullActionBlock:
		return true
	default:
		return false
	}
}

// DefaultQueueConfig returns the default queue configuration.
func DefaultQueueConfig() *QueueConfig {
	return &QueueConfig{
		Enabled:    true,
		Size:       2048,
		FullAction: QueueFullActionDrop,
	}
}

// Validate validates the queue configuration.
func (q *QueueConfig) Validate() error {
	if q == nil {
		return nil
	}
	if q.Size <= 0 {
		return fmt.Errorf("queue size must be positive: %d", q.Size)
	}
	if !q.FullAction.IsValid() {
		return fmt.Errorf("invalid queue full action: %s", q.FullAction)
	}
	return nil
}

// ConnectionConfig holds connection-specific configuration.
type ConnectionConfig struct {
	// KeepAlive enables TCP keep-alive.
	KeepAlive bool

	// KeepAlivePeriod is the TCP keep-alive period.
	KeepAlivePeriod time.Duration

	// ConnectTimeout is the connection timeout.
	ConnectTimeout time.Duration

	// IdleConnTimeout is the idle connection timeout.
	IdleConnTimeout time.Duration

	// MaxIdleConns is the maximum number of idle connections.
	MaxIdleConns int

	// MaxConnsPerHost is the maximum connections per host.
	MaxConnsPerHost int
}

// DefaultConnectionConfig returns the default connection configuration.
func DefaultConnectionConfig() *ConnectionConfig {
	return &ConnectionConfig{
		KeepAlive:       true,
		KeepAlivePeriod: 15 * time.Second,
		ConnectTimeout:  10 * time.Second,
		IdleConnTimeout: 90 * time.Second,
		MaxIdleConns:    100,
		MaxConnsPerHost: 10,
	}
}

// Validate validates the connection configuration.
func (c *ConnectionConfig) Validate() error {
	if c == nil {
		return nil
	}
	if c.KeepAlive {
		if c.KeepAlivePeriod <= 0 {
			return fmt.Errorf("keep-alive period must be positive: %v", c.KeepAlivePeriod)
		}
	}
	if c.ConnectTimeout <= 0 {
		return fmt.Errorf("connect timeout must be positive: %v", c.ConnectTimeout)
	}
	if c.IdleConnTimeout <= 0 {
		return fmt.Errorf("idle connection timeout must be positive: %v", c.IdleConnTimeout)
	}
	if c.MaxIdleConns < 0 {
		return fmt.Errorf("max idle connections must be non-negative: %d", c.MaxIdleConns)
	}
	if c.MaxConnsPerHost <= 0 {
		return fmt.Errorf("max connections per host must be positive: %d", c.MaxConnsPerHost)
	}
	return nil
}

// DefaultExporterConfig returns the default exporter configuration.
func DefaultExporterConfig() *ExporterConfig {
	return &ExporterConfig{
		BaseConfig:        *DefaultBaseConfig(),
		Protocol:          ProtocolGRPC,
		Encoding:          EncodingProtobuf,
		ExporterType:      ExporterTypeTrace,
		URLPath:           "",
		MaxAttempts:       3,
		QueueConfig:       DefaultQueueConfig(),
		ConnectionConfig:  DefaultConnectionConfig(),
		ProxyURL:          "",
		UserAgent:         "OTLP-Go-SDK/1.0",
		DisableKeepAlive:  false,
	}
}

// Validate validates the exporter configuration.
func (c *ExporterConfig) Validate() error {
	if err := c.BaseConfig.Validate(); err != nil {
		return fmt.Errorf("base config validation failed: %w", err)
	}
	if !c.Protocol.IsValid() {
		return fmt.Errorf("invalid protocol: %s", c.Protocol)
	}
	if !c.Encoding.IsValid() {
		return fmt.Errorf("invalid encoding: %s", c.Encoding)
	}
	if !c.ExporterType.IsValid() {
		return fmt.Errorf("invalid exporter type: %s", c.ExporterType)
	}
	if c.MaxAttempts <= 0 {
		return fmt.Errorf("max attempts must be positive: %d", c.MaxAttempts)
	}
	if err := c.QueueConfig.Validate(); err != nil {
		return fmt.Errorf("queue config validation failed: %w", err)
	}
	if err := c.ConnectionConfig.Validate(); err != nil {
		return fmt.Errorf("connection config validation failed: %w", err)
	}
	return nil
}

// ExporterOption is a functional option for configuring exporters.
type ExporterOption func(*ExporterConfig) error

// Apply implements the Option interface.
func (o ExporterOption) Apply(cfg interface{}) error {
	if c, ok := cfg.(*ExporterConfig); ok {
		return o(c)
	}
	return fmt.Errorf("expected *ExporterConfig, got %T", cfg)
}

// WithProtocol sets the transport protocol.
func WithProtocol(protocol ProtocolType) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if !protocol.IsValid() {
			return fmt.Errorf("invalid protocol: %s", protocol)
		}
		cfg.Protocol = protocol
		return nil
	}
}

// WithGRPCProtocol sets the protocol to gRPC.
func WithGRPCProtocol() ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.Protocol = ProtocolGRPC
		return nil
	}
}

// WithHTTPProtocol sets the protocol to HTTP.
func WithHTTPProtocol() ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.Protocol = ProtocolHTTP
		return nil
	}
}

// WithEncoding sets the payload encoding.
func WithEncoding(encoding EncodingType) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if !encoding.IsValid() {
			return fmt.Errorf("invalid encoding: %s", encoding)
		}
		cfg.Encoding = encoding
		return nil
	}
}

// WithProtobufEncoding sets the encoding to Protocol Buffers.
func WithProtobufEncoding() ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.Encoding = EncodingProtobuf
		return nil
	}
}

// WithJSONEncoding sets the encoding to JSON.
func WithJSONEncoding() ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.Encoding = EncodingJSON
		return nil
	}
}

// WithExporterType sets the exporter type.
func WithExporterType(exporterType ExporterType) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if !exporterType.IsValid() {
			return fmt.Errorf("invalid exporter type: %s", exporterType)
		}
		cfg.ExporterType = exporterType
		return nil
	}
}

// WithURLPath sets the URL path for HTTP exports.
func WithURLPath(path string) ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.URLPath = path
		return nil
	}
}

// WithMaxAttempts sets the maximum number of export attempts.
func WithMaxAttempts(attempts int) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if attempts <= 0 {
			return fmt.Errorf("max attempts must be positive: %d", attempts)
		}
		cfg.MaxAttempts = attempts
		return nil
	}
}

// WithQueueConfig sets the queue configuration.
func WithQueueConfig(queue *QueueConfig) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if err := queue.Validate(); err != nil {
			return fmt.Errorf("invalid queue config: %w", err)
		}
		cfg.QueueConfig = queue
		return nil
	}
}

// WithQueueSize sets the queue size.
func WithQueueSize(size int) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if size <= 0 {
			return fmt.Errorf("queue size must be positive: %d", size)
		}
		if cfg.QueueConfig == nil {
			cfg.QueueConfig = DefaultQueueConfig()
		}
		cfg.QueueConfig.Size = size
		return nil
	}
}

// WithQueueFullAction sets the queue full action.
func WithQueueFullAction(action QueueFullAction) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if !action.IsValid() {
			return fmt.Errorf("invalid queue full action: %s", action)
		}
		if cfg.QueueConfig == nil {
			cfg.QueueConfig = DefaultQueueConfig()
		}
		cfg.QueueConfig.FullAction = action
		return nil
	}
}

// WithQueueDisabled disables the queue.
func WithQueueDisabled() ExporterOption {
	return func(cfg *ExporterConfig) error {
		if cfg.QueueConfig == nil {
			cfg.QueueConfig = DefaultQueueConfig()
		}
		cfg.QueueConfig.Enabled = false
		return nil
	}
}

// WithConnectionConfig sets the connection configuration.
func WithConnectionConfig(conn *ConnectionConfig) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if err := conn.Validate(); err != nil {
			return fmt.Errorf("invalid connection config: %w", err)
		}
		cfg.ConnectionConfig = conn
		return nil
	}
}

// WithKeepAlive enables or disables TCP keep-alive.
func WithKeepAlive(enabled bool) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if cfg.ConnectionConfig == nil {
			cfg.ConnectionConfig = DefaultConnectionConfig()
		}
		cfg.ConnectionConfig.KeepAlive = enabled
		return nil
	}
}

// WithKeepAlivePeriod sets the TCP keep-alive period.
func WithKeepAlivePeriod(period time.Duration) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if period <= 0 {
			return fmt.Errorf("keep-alive period must be positive: %v", period)
		}
		if cfg.ConnectionConfig == nil {
			cfg.ConnectionConfig = DefaultConnectionConfig()
		}
		cfg.ConnectionConfig.KeepAlivePeriod = period
		return nil
	}
}

// WithConnectTimeout sets the connection timeout.
func WithConnectTimeout(timeout time.Duration) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("connect timeout must be positive: %v", timeout)
		}
		if cfg.ConnectionConfig == nil {
			cfg.ConnectionConfig = DefaultConnectionConfig()
		}
		cfg.ConnectionConfig.ConnectTimeout = timeout
		return nil
	}
}

// WithIdleConnTimeout sets the idle connection timeout.
func WithIdleConnTimeout(timeout time.Duration) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("idle connection timeout must be positive: %v", timeout)
		}
		if cfg.ConnectionConfig == nil {
			cfg.ConnectionConfig = DefaultConnectionConfig()
		}
		cfg.ConnectionConfig.IdleConnTimeout = timeout
		return nil
	}
}

// WithMaxIdleConns sets the maximum number of idle connections.
func WithMaxIdleConns(max int) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if max < 0 {
			return fmt.Errorf("max idle connections must be non-negative: %d", max)
		}
		if cfg.ConnectionConfig == nil {
			cfg.ConnectionConfig = DefaultConnectionConfig()
		}
		cfg.ConnectionConfig.MaxIdleConns = max
		return nil
	}
}

// WithMaxConnsPerHost sets the maximum connections per host.
func WithMaxConnsPerHost(max int) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if max <= 0 {
			return fmt.Errorf("max connections per host must be positive: %d", max)
		}
		if cfg.ConnectionConfig == nil {
			cfg.ConnectionConfig = DefaultConnectionConfig()
		}
		cfg.ConnectionConfig.MaxConnsPerHost = max
		return nil
	}
}

// WithProxyURL sets the proxy URL.
func WithProxyURL(url string) ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.ProxyURL = url
		return nil
	}
}

// WithUserAgent sets the custom user agent.
func WithUserAgent(userAgent string) ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.UserAgent = userAgent
		return nil
	}
}

// WithKeepAliveDisabled disables HTTP keep-alive.
func WithKeepAliveDisabled() ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.DisableKeepAlive = true
		return nil
	}
}

// ApplyExporterOptions applies exporter options and returns the configuration.
func ApplyExporterOptions(opts ...ExporterOption) (*ExporterConfig, error) {
	cfg := DefaultExporterConfig()
	for _, opt := range opts {
		if err := opt(cfg); err != nil {
			return nil, err
		}
	}
	if err := cfg.Validate(); err != nil {
		return nil, err
	}
	return cfg, nil
}

// ExporterBaseEndpoint sets the exporter endpoint (wrapper around WithEndpoint).
func ExporterBaseEndpoint(endpoint string) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if endpoint == "" {
			return fmt.Errorf("endpoint cannot be empty")
		}
		cfg.Endpoint = endpoint
		return nil
	}
}

// ExporterBaseTimeout sets the exporter timeout (wrapper around WithTimeout).
func ExporterBaseTimeout(timeout time.Duration) ExporterOption {
	return func(cfg *ExporterConfig) error {
		if timeout <= 0 {
			return fmt.Errorf("timeout must be positive: %v", timeout)
		}
		cfg.Timeout = timeout
		return nil
	}
}

// ExporterBaseHeaders sets the exporter headers (wrapper around WithHeaders).
func ExporterBaseHeaders(headers map[string]string) ExporterOption {
	return func(cfg *ExporterConfig) error {
		cfg.Headers = make(map[string]string)
		for k, v := range headers {
			cfg.Headers[k] = v
		}
		return nil
	}
}

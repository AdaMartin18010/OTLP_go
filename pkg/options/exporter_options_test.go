package options

import (
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestProtocolType_IsValid(t *testing.T) {
	tests := []struct {
		name     string
		protocol ProtocolType
		want     bool
	}{
		{"grpc", ProtocolGRPC, true},
		{"http", ProtocolHTTP, true},
		{"invalid", ProtocolType("invalid"), false},
		{"empty", ProtocolType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.protocol.IsValid())
		})
	}
}

func TestProtocolType_String(t *testing.T) {
	assert.Equal(t, "grpc", ProtocolGRPC.String())
	assert.Equal(t, "http", ProtocolHTTP.String())
}

func TestEncodingType_IsValid(t *testing.T) {
	tests := []struct {
		name     string
		encoding EncodingType
		want     bool
	}{
		{"protobuf", EncodingProtobuf, true},
		{"json", EncodingJSON, true},
		{"invalid", EncodingType("invalid"), false},
		{"empty", EncodingType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.encoding.IsValid())
		})
	}
}

func TestEncodingType_String(t *testing.T) {
	assert.Equal(t, "protobuf", EncodingProtobuf.String())
	assert.Equal(t, "json", EncodingJSON.String())
}

func TestExporterType_IsValid(t *testing.T) {
	tests := []struct {
		name     string
		exporter ExporterType
		want     bool
	}{
		{"trace", ExporterTypeTrace, true},
		{"metric", ExporterTypeMetric, true},
		{"log", ExporterTypeLog, true},
		{"invalid", ExporterType("invalid"), false},
		{"empty", ExporterType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.exporter.IsValid())
		})
	}
}

func TestExporterType_String(t *testing.T) {
	assert.Equal(t, "trace", ExporterTypeTrace.String())
	assert.Equal(t, "metric", ExporterTypeMetric.String())
	assert.Equal(t, "log", ExporterTypeLog.String())
}

func TestQueueFullAction_IsValid(t *testing.T) {
	tests := []struct {
		name   string
		action QueueFullAction
		want   bool
	}{
		{"drop", QueueFullActionDrop, true},
		{"block", QueueFullActionBlock, true},
		{"invalid", QueueFullAction("invalid"), false},
		{"empty", QueueFullAction(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.action.IsValid())
		})
	}
}

func TestDefaultQueueConfig(t *testing.T) {
	cfg := DefaultQueueConfig()
	require.NotNil(t, cfg)

	assert.True(t, cfg.Enabled)
	assert.Equal(t, 2048, cfg.Size)
	assert.Equal(t, QueueFullActionDrop, cfg.FullAction)
}

func TestQueueConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *QueueConfig
		wantErr bool
		errMsg  string
	}{
		{
			name:    "nil config",
			config:  nil,
			wantErr: false,
		},
		{
			name:    "valid config",
			config:  DefaultQueueConfig(),
			wantErr: false,
		},
		{
			name: "zero size",
			config: &QueueConfig{
				Enabled:    true,
				Size:       0,
				FullAction: QueueFullActionDrop,
			},
			wantErr: true,
			errMsg:  "queue size must be positive",
		},
		{
			name: "negative size",
			config: &QueueConfig{
				Enabled:    true,
				Size:       -1,
				FullAction: QueueFullActionDrop,
			},
			wantErr: true,
			errMsg:  "queue size must be positive",
		},
		{
			name: "invalid action",
			config: &QueueConfig{
				Enabled:    true,
				Size:       2048,
				FullAction: QueueFullAction("invalid"),
			},
			wantErr: true,
			errMsg:  "invalid queue full action",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestDefaultConnectionConfig(t *testing.T) {
	cfg := DefaultConnectionConfig()
	require.NotNil(t, cfg)

	assert.True(t, cfg.KeepAlive)
	assert.Equal(t, 15*time.Second, cfg.KeepAlivePeriod)
	assert.Equal(t, 10*time.Second, cfg.ConnectTimeout)
	assert.Equal(t, 90*time.Second, cfg.IdleConnTimeout)
	assert.Equal(t, 100, cfg.MaxIdleConns)
	assert.Equal(t, 10, cfg.MaxConnsPerHost)
}

func TestConnectionConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *ConnectionConfig
		wantErr bool
		errMsg  string
	}{
		{
			name:    "nil config",
			config:  nil,
			wantErr: false,
		},
		{
			name:    "valid config",
			config:  DefaultConnectionConfig(),
			wantErr: false,
		},
		{
			name: "zero keep-alive period",
			config: &ConnectionConfig{
				KeepAlive:       true,
				KeepAlivePeriod: 0,
				ConnectTimeout:  10 * time.Second,
				IdleConnTimeout: 90 * time.Second,
				MaxConnsPerHost: 10,
			},
			wantErr: true,
			errMsg:  "keep-alive period must be positive",
		},
		{
			name: "zero connect timeout",
			config: &ConnectionConfig{
				KeepAlive:       true,
				KeepAlivePeriod: 15 * time.Second,
				ConnectTimeout:  0,
				IdleConnTimeout: 90 * time.Second,
				MaxConnsPerHost: 10,
			},
			wantErr: true,
			errMsg:  "connect timeout must be positive",
		},
		{
			name: "zero idle timeout",
			config: &ConnectionConfig{
				KeepAlive:       true,
				KeepAlivePeriod: 15 * time.Second,
				ConnectTimeout:  10 * time.Second,
				IdleConnTimeout: 0,
				MaxConnsPerHost: 10,
			},
			wantErr: true,
			errMsg:  "idle connection timeout must be positive",
		},
		{
			name: "negative max idle conns",
			config: &ConnectionConfig{
				KeepAlive:       true,
				KeepAlivePeriod: 15 * time.Second,
				ConnectTimeout:  10 * time.Second,
				IdleConnTimeout: 90 * time.Second,
				MaxIdleConns:    -1,
				MaxConnsPerHost: 10,
			},
			wantErr: true,
			errMsg:  "max idle connections must be non-negative",
		},
		{
			name: "zero max conns per host",
			config: &ConnectionConfig{
				KeepAlive:       true,
				KeepAlivePeriod: 15 * time.Second,
				ConnectTimeout:  10 * time.Second,
				IdleConnTimeout: 90 * time.Second,
				MaxConnsPerHost: 0,
			},
			wantErr: true,
			errMsg:  "max connections per host must be positive",
		},
		{
			name: "keep-alive disabled allows zero period",
			config: &ConnectionConfig{
				KeepAlive:       false,
				KeepAlivePeriod: 0,
				ConnectTimeout:  10 * time.Second,
				IdleConnTimeout: 90 * time.Second,
				MaxConnsPerHost: 10,
			},
			wantErr: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestDefaultExporterConfig(t *testing.T) {
	cfg := DefaultExporterConfig()
	require.NotNil(t, cfg)

	assert.Equal(t, ProtocolGRPC, cfg.Protocol)
	assert.Equal(t, EncodingProtobuf, cfg.Encoding)
	assert.Equal(t, ExporterTypeTrace, cfg.ExporterType)
	assert.Equal(t, "", cfg.URLPath)
	assert.Equal(t, 3, cfg.MaxAttempts)
	assert.NotNil(t, cfg.QueueConfig)
	assert.NotNil(t, cfg.ConnectionConfig)
	assert.Equal(t, "", cfg.ProxyURL)
	assert.Equal(t, "OTLP-Go-SDK/1.0", cfg.UserAgent)
	assert.False(t, cfg.DisableKeepAlive)

	// Check base config
	assert.Equal(t, "localhost:4317", cfg.Endpoint)
	assert.Equal(t, 10*time.Second, cfg.Timeout)
}

func TestExporterConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *ExporterConfig
		wantErr bool
		errMsg  string
	}{
		{
			name:    "valid default config",
			config:  DefaultExporterConfig(),
			wantErr: false,
		},
		{
			name: "invalid protocol",
			config: func() *ExporterConfig {
				c := DefaultExporterConfig()
				c.Protocol = ProtocolType("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid protocol",
		},
		{
			name: "invalid encoding",
			config: func() *ExporterConfig {
				c := DefaultExporterConfig()
				c.Encoding = EncodingType("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid encoding",
		},
		{
			name: "invalid exporter type",
			config: func() *ExporterConfig {
				c := DefaultExporterConfig()
				c.ExporterType = ExporterType("invalid")
				return c
			}(),
			wantErr: true,
			errMsg:  "invalid exporter type",
		},
		{
			name: "zero max attempts",
			config: func() *ExporterConfig {
				c := DefaultExporterConfig()
				c.MaxAttempts = 0
				return c
			}(),
			wantErr: true,
			errMsg:  "max attempts must be positive",
		},
		{
			name: "invalid queue config",
			config: func() *ExporterConfig {
				c := DefaultExporterConfig()
				c.QueueConfig = &QueueConfig{Size: 0}
				return c
			}(),
			wantErr: true,
			errMsg:  "queue config validation failed",
		},
		{
			name: "invalid connection config",
			config: func() *ExporterConfig {
				c := DefaultExporterConfig()
				c.ConnectionConfig = &ConnectionConfig{MaxConnsPerHost: 0}
				return c
			}(),
			wantErr: true,
			errMsg:  "connection config validation failed",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.config.Validate()
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
			}
		})
	}
}

func TestExporterOption_Apply_WrongType(t *testing.T) {
	opt := ExporterOption(func(cfg *ExporterConfig) error {
		return nil
	})

	err := opt.Apply("wrong type")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "expected *ExporterConfig")
}

func TestWithProtocol(t *testing.T) {
	tests := []struct {
		name     string
		protocol ProtocolType
		wantErr  bool
		errMsg   string
	}{
		{"grpc", ProtocolGRPC, false, ""},
		{"http", ProtocolHTTP, false, ""},
		{"invalid", ProtocolType("invalid"), true, "invalid protocol"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithProtocol(tt.protocol)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.protocol, cfg.Protocol)
			}
		})
	}
}

func TestWithGRPCProtocol(t *testing.T) {
	cfg := &ExporterConfig{Protocol: ProtocolHTTP}
	err := WithGRPCProtocol()(cfg)
	require.NoError(t, err)
	assert.Equal(t, ProtocolGRPC, cfg.Protocol)
}

func TestWithHTTPProtocol(t *testing.T) {
	cfg := &ExporterConfig{Protocol: ProtocolGRPC}
	err := WithHTTPProtocol()(cfg)
	require.NoError(t, err)
	assert.Equal(t, ProtocolHTTP, cfg.Protocol)
}

func TestWithEncoding(t *testing.T) {
	tests := []struct {
		name     string
		encoding EncodingType
		wantErr  bool
		errMsg   string
	}{
		{"protobuf", EncodingProtobuf, false, ""},
		{"json", EncodingJSON, false, ""},
		{"invalid", EncodingType("invalid"), true, "invalid encoding"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithEncoding(tt.encoding)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.encoding, cfg.Encoding)
			}
		})
	}
}

func TestWithProtobufEncoding(t *testing.T) {
	cfg := &ExporterConfig{Encoding: EncodingJSON}
	err := WithProtobufEncoding()(cfg)
	require.NoError(t, err)
	assert.Equal(t, EncodingProtobuf, cfg.Encoding)
}

func TestWithJSONEncoding(t *testing.T) {
	cfg := &ExporterConfig{Encoding: EncodingProtobuf}
	err := WithJSONEncoding()(cfg)
	require.NoError(t, err)
	assert.Equal(t, EncodingJSON, cfg.Encoding)
}

func TestWithExporterType(t *testing.T) {
	tests := []struct {
		name     string
		exporter ExporterType
		wantErr  bool
		errMsg   string
	}{
		{"trace", ExporterTypeTrace, false, ""},
		{"metric", ExporterTypeMetric, false, ""},
		{"log", ExporterTypeLog, false, ""},
		{"invalid", ExporterType("invalid"), true, "invalid exporter type"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithExporterType(tt.exporter)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.exporter, cfg.ExporterType)
			}
		})
	}
}

func TestWithURLPath(t *testing.T) {
	cfg := &ExporterConfig{}
	err := WithURLPath("/v1/traces")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "/v1/traces", cfg.URLPath)
}

func TestWithMaxAttempts(t *testing.T) {
	tests := []struct {
		name     string
		attempts int
		wantErr  bool
		errMsg   string
	}{
		{"valid attempts", 5, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max attempts must be positive"},
		{"negative", -1, true, "max attempts must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithMaxAttempts(tt.attempts)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.attempts, cfg.MaxAttempts)
			}
		})
	}
}

func TestWithQueueConfig(t *testing.T) {
	t.Run("valid config", func(t *testing.T) {
		cfg := &ExporterConfig{}
		queueCfg := &QueueConfig{
			Enabled:    true,
			Size:       1024,
			FullAction: QueueFullActionBlock,
		}
		opt := WithQueueConfig(queueCfg)
		err := opt(cfg)
		require.NoError(t, err)
		assert.Equal(t, 1024, cfg.QueueConfig.Size)
		assert.Equal(t, QueueFullActionBlock, cfg.QueueConfig.FullAction)
	})

	t.Run("invalid config", func(t *testing.T) {
		cfg := &ExporterConfig{}
		queueCfg := &QueueConfig{Size: 0}
		opt := WithQueueConfig(queueCfg)
		err := opt(cfg)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid queue config")
	})
}

func TestWithQueueSize(t *testing.T) {
	tests := []struct {
		name    string
		size    int
		wantErr bool
		errMsg  string
	}{
		{"valid size", 1024, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "queue size must be positive"},
		{"negative", -1, true, "queue size must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithQueueSize(tt.size)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.size, cfg.QueueConfig.Size)
			}
		})
	}
}

func TestWithQueueFullAction(t *testing.T) {
	tests := []struct {
		name    string
		action  QueueFullAction
		wantErr bool
		errMsg  string
	}{
		{"drop", QueueFullActionDrop, false, ""},
		{"block", QueueFullActionBlock, false, ""},
		{"invalid", QueueFullAction("invalid"), true, "invalid queue full action"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithQueueFullAction(tt.action)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.action, cfg.QueueConfig.FullAction)
			}
		})
	}
}

func TestWithQueueDisabled(t *testing.T) {
	cfg := &ExporterConfig{QueueConfig: &QueueConfig{Enabled: true}}
	err := WithQueueDisabled()(cfg)
	require.NoError(t, err)
	assert.False(t, cfg.QueueConfig.Enabled)
}

func TestWithConnectionConfig(t *testing.T) {
	t.Run("valid config", func(t *testing.T) {
		cfg := &ExporterConfig{}
		connCfg := &ConnectionConfig{
			KeepAlive:       true,
			KeepAlivePeriod: 30 * time.Second,
			ConnectTimeout:  5 * time.Second,
			IdleConnTimeout: 60 * time.Second,
			MaxIdleConns:    50,
			MaxConnsPerHost: 20,
		}
		opt := WithConnectionConfig(connCfg)
		err := opt(cfg)
		require.NoError(t, err)
		assert.Equal(t, 30*time.Second, cfg.ConnectionConfig.KeepAlivePeriod)
	})

	t.Run("invalid config", func(t *testing.T) {
		cfg := &ExporterConfig{}
		connCfg := &ConnectionConfig{MaxConnsPerHost: 0}
		opt := WithConnectionConfig(connCfg)
		err := opt(cfg)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid connection config")
	})
}

func TestWithKeepAlive(t *testing.T) {
	t.Run("enable", func(t *testing.T) {
		cfg := &ExporterConfig{ConnectionConfig: nil}
		opt := WithKeepAlive(true)
		err := opt(cfg)
		require.NoError(t, err)
		assert.True(t, cfg.ConnectionConfig.KeepAlive)
	})

	t.Run("disable", func(t *testing.T) {
		cfg := &ExporterConfig{ConnectionConfig: nil}
		opt := WithKeepAlive(false)
		err := opt(cfg)
		require.NoError(t, err)
		assert.False(t, cfg.ConnectionConfig.KeepAlive)
	})
}

func TestWithKeepAlivePeriod(t *testing.T) {
	tests := []struct {
		name    string
		period  time.Duration
		wantErr bool
		errMsg  string
	}{
		{"valid period", 30 * time.Second, false, ""},
		{"one second", 1 * time.Second, false, ""},
		{"zero", 0, true, "keep-alive period must be positive"},
		{"negative", -1 * time.Second, true, "keep-alive period must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithKeepAlivePeriod(tt.period)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.period, cfg.ConnectionConfig.KeepAlivePeriod)
			}
		})
	}
}

func TestWithConnectTimeout(t *testing.T) {
	tests := []struct {
		name    string
		timeout time.Duration
		wantErr bool
		errMsg  string
	}{
		{"valid timeout", 5 * time.Second, false, ""},
		{"zero", 0, true, "connect timeout must be positive"},
		{"negative", -1 * time.Second, true, "connect timeout must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithConnectTimeout(tt.timeout)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.timeout, cfg.ConnectionConfig.ConnectTimeout)
			}
		})
	}
}

func TestWithIdleConnTimeout(t *testing.T) {
	tests := []struct {
		name    string
		timeout time.Duration
		wantErr bool
		errMsg  string
	}{
		{"valid timeout", 60 * time.Second, false, ""},
		{"zero", 0, true, "idle connection timeout must be positive"},
		{"negative", -1 * time.Second, true, "idle connection timeout must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithIdleConnTimeout(tt.timeout)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.timeout, cfg.ConnectionConfig.IdleConnTimeout)
			}
		})
	}
}

func TestWithMaxIdleConns(t *testing.T) {
	tests := []struct {
		name    string
		max     int
		wantErr bool
		errMsg  string
	}{
		{"valid max", 50, false, ""},
		{"zero", 0, false, ""},
		{"negative", -1, true, "max idle connections must be non-negative"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithMaxIdleConns(tt.max)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.max, cfg.ConnectionConfig.MaxIdleConns)
			}
		})
	}
}

func TestWithMaxConnsPerHost(t *testing.T) {
	tests := []struct {
		name    string
		max     int
		wantErr bool
		errMsg  string
	}{
		{"valid max", 20, false, ""},
		{"one", 1, false, ""},
		{"zero", 0, true, "max connections per host must be positive"},
		{"negative", -1, true, "max connections per host must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &ExporterConfig{}
			opt := WithMaxConnsPerHost(tt.max)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.max, cfg.ConnectionConfig.MaxConnsPerHost)
			}
		})
	}
}

func TestWithProxyURL(t *testing.T) {
	cfg := &ExporterConfig{}
	err := WithProxyURL("http://proxy.example.com:8080")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "http://proxy.example.com:8080", cfg.ProxyURL)
}

func TestWithUserAgent(t *testing.T) {
	cfg := &ExporterConfig{}
	err := WithUserAgent("Custom-Agent/1.0")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "Custom-Agent/1.0", cfg.UserAgent)
}

func TestWithKeepAliveDisabled(t *testing.T) {
	cfg := &ExporterConfig{DisableKeepAlive: false}
	err := WithKeepAliveDisabled()(cfg)
	require.NoError(t, err)
	assert.True(t, cfg.DisableKeepAlive)
}

func TestApplyExporterOptions(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		cfg, err := ApplyExporterOptions(
			WithProtocol(ProtocolHTTP),
			WithEncoding(EncodingJSON),
			WithMaxAttempts(5),
		)
		require.NoError(t, err)
		assert.Equal(t, ProtocolHTTP, cfg.Protocol)
		assert.Equal(t, EncodingJSON, cfg.Encoding)
		assert.Equal(t, 5, cfg.MaxAttempts)
	})

	t.Run("option error", func(t *testing.T) {
		cfg, err := ApplyExporterOptions(
			WithProtocol(ProtocolType("invalid")),
		)
		require.Error(t, err)
		assert.Nil(t, cfg)
		assert.Contains(t, err.Error(), "invalid protocol")
	})

	t.Run("validation error", func(t *testing.T) {
		cfg, err := ApplyExporterOptions(
			WithMaxAttempts(5),
			func(c *ExporterConfig) error {
				c.MaxAttempts = 0
				return nil
			},
		)
		require.Error(t, err)
		assert.Nil(t, cfg)
		assert.Contains(t, err.Error(), "max attempts must be positive")
	})
}

func TestExporterBaseEndpoint(t *testing.T) {
	cfg := &ExporterConfig{}
	err := ExporterBaseEndpoint("custom:4318")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "custom:4318", cfg.Endpoint)
}

func TestExporterBaseTimeout(t *testing.T) {
	cfg := &ExporterConfig{}
	err := ExporterBaseTimeout(5 * time.Second)(cfg)
	require.NoError(t, err)
	assert.Equal(t, 5*time.Second, cfg.Timeout)
}

func TestExporterBaseHeaders(t *testing.T) {
	cfg := &ExporterConfig{}
	headers := map[string]string{"X-Custom": "value"}
	err := ExporterBaseHeaders(headers)(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value", cfg.Headers["X-Custom"])
}

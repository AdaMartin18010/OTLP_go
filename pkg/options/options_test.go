package options

import (
	"errors"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestOptionFunc_Apply(t *testing.T) {
	called := false
	opt := OptionFunc(func(cfg interface{}) error {
		called = true
		return nil
	})

	err := opt.Apply(struct{}{})
	require.NoError(t, err)
	assert.True(t, called)
}

func TestOptionFunc_Apply_Error(t *testing.T) {
	expectedErr := errors.New("test error")
	opt := OptionFunc(func(cfg interface{}) error {
		return expectedErr
	})

	err := opt.Apply(struct{}{})
	assert.ErrorIs(t, err, expectedErr)
}

func TestCompressionType_IsValid(t *testing.T) {
	tests := []struct {
		name        string
		compression CompressionType
		want        bool
	}{
		{"none", CompressionNone, true},
		{"gzip", CompressionGzip, true},
		{"invalid", CompressionType("invalid"), false},
		{"empty", CompressionType(""), false},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.want, tt.compression.IsValid())
		})
	}
}

func TestDefaultRetryConfig(t *testing.T) {
	cfg := DefaultRetryConfig()
	require.NotNil(t, cfg)

	assert.True(t, cfg.Enabled)
	assert.Equal(t, 3, cfg.MaxRetries)
	assert.Equal(t, 1*time.Second, cfg.InitialInterval)
	assert.Equal(t, 30*time.Second, cfg.MaxInterval)
	assert.Equal(t, 2.0, cfg.Multiplier)
}

func TestRetryConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *RetryConfig
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
			config:  DefaultRetryConfig(),
			wantErr: false,
		},
		{
			name: "negative max retries",
			config: &RetryConfig{
				MaxRetries:      -1,
				InitialInterval: 1 * time.Second,
				MaxInterval:     30 * time.Second,
				Multiplier:      2.0,
			},
			wantErr: true,
			errMsg:  "max retries cannot be negative",
		},
		{
			name: "negative initial interval",
			config: &RetryConfig{
				MaxRetries:      3,
				InitialInterval: -1 * time.Second,
				MaxInterval:     30 * time.Second,
				Multiplier:      2.0,
			},
			wantErr: true,
			errMsg:  "initial interval cannot be negative",
		},
		{
			name: "max interval less than initial",
			config: &RetryConfig{
				MaxRetries:      3,
				InitialInterval: 30 * time.Second,
				MaxInterval:     1 * time.Second,
				Multiplier:      2.0,
			},
			wantErr: true,
			errMsg:  "max interval",
		},
		{
			name: "multiplier less than 1.0",
			config: &RetryConfig{
				MaxRetries:      3,
				InitialInterval: 1 * time.Second,
				MaxInterval:     30 * time.Second,
				Multiplier:      0.5,
			},
			wantErr: true,
			errMsg:  "multiplier must be >= 1.0",
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

func TestTLSConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *TLSConfig
		wantErr bool
		errMsg  string
	}{
		{
			name:    "nil config",
			config:  nil,
			wantErr: false,
		},
		{
			name: "valid insecure",
			config: &TLSConfig{
				Insecure: true,
			},
			wantErr: false,
		},
		{
			name: "valid secure no certs",
			config: &TLSConfig{
				Insecure: false,
			},
			wantErr: false,
		},
		{
			name: "cert without key",
			config: &TLSConfig{
				Insecure: false,
				CertFile: "/path/to/cert.pem",
			},
			wantErr: true,
			errMsg:  "key file is required",
		},
		{
			name: "key without cert",
			config: &TLSConfig{
				Insecure: false,
				KeyFile:  "/path/to/key.pem",
			},
			wantErr: true,
			errMsg:  "cert file is required",
		},
		{
			name: "valid with both certs",
			config: &TLSConfig{
				Insecure: false,
				CertFile: "/path/to/cert.pem",
				KeyFile:  "/path/to/key.pem",
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

func TestDefaultBaseConfig(t *testing.T) {
	cfg := DefaultBaseConfig()
	require.NotNil(t, cfg)

	assert.Equal(t, "localhost:4317", cfg.Endpoint)
	assert.Equal(t, 10*time.Second, cfg.Timeout)
	assert.NotNil(t, cfg.Headers)
	assert.Equal(t, CompressionGzip, cfg.Compression)
	assert.NotNil(t, cfg.RetryConfig)
	assert.NotNil(t, cfg.TLSConfig)
	assert.False(t, cfg.TLSConfig.Insecure)
}

func TestBaseConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  *BaseConfig
		wantErr bool
		errMsg  string
	}{
		{
			name:    "valid default config",
			config:  DefaultBaseConfig(),
			wantErr: false,
		},
		{
			name: "empty endpoint",
			config: &BaseConfig{
				Endpoint:    "",
				Timeout:     10 * time.Second,
				Compression: CompressionGzip,
				RetryConfig: DefaultRetryConfig(),
				TLSConfig:   &TLSConfig{},
			},
			wantErr: true,
			errMsg:  "endpoint is required",
		},
		{
			name: "zero timeout",
			config: &BaseConfig{
				Endpoint:    "localhost:4317",
				Timeout:     0,
				Compression: CompressionGzip,
				RetryConfig: DefaultRetryConfig(),
				TLSConfig:   &TLSConfig{},
			},
			wantErr: true,
			errMsg:  "timeout must be positive",
		},
		{
			name: "invalid compression",
			config: &BaseConfig{
				Endpoint:    "localhost:4317",
				Timeout:     10 * time.Second,
				Compression: CompressionType("invalid"),
				RetryConfig: DefaultRetryConfig(),
				TLSConfig:   &TLSConfig{},
			},
			wantErr: true,
			errMsg:  "invalid compression type",
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

func TestBaseConfig_ApplyOptions(t *testing.T) {
	t.Run("apply single option", func(t *testing.T) {
		cfg := DefaultBaseConfig()
		err := cfg.ApplyOptions(func(c *BaseConfig) error {
			c.Endpoint = "new-endpoint:4317"
			return nil
		})
		require.NoError(t, err)
		assert.Equal(t, "new-endpoint:4317", cfg.Endpoint)
	})

	t.Run("apply multiple options", func(t *testing.T) {
		cfg := DefaultBaseConfig()
		err := cfg.ApplyOptions(
			func(c *BaseConfig) error {
				c.Endpoint = "host:8080"
				return nil
			},
			func(c *BaseConfig) error {
				c.Timeout = 5 * time.Second
				return nil
			},
		)
		require.NoError(t, err)
		assert.Equal(t, "host:8080", cfg.Endpoint)
		assert.Equal(t, 5*time.Second, cfg.Timeout)
	})

	t.Run("apply invalid option", func(t *testing.T) {
		cfg := DefaultBaseConfig()
		err := cfg.ApplyOptions(func(c *BaseConfig) error {
			return errors.New("option error")
		})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "option error")
	})
}

func TestWithEndpoint(t *testing.T) {
	tests := []struct {
		name     string
		endpoint string
		wantErr  bool
		errMsg   string
	}{
		{"valid endpoint", "localhost:4317", false, ""},
		{"another endpoint", "collector.example.com:4317", false, ""},
		{"empty endpoint", "", true, "endpoint cannot be empty"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &BaseConfig{}
			opt := WithEndpoint(tt.endpoint)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.endpoint, cfg.Endpoint)
			}
		})
	}
}

func TestWithTimeout(t *testing.T) {
	tests := []struct {
		name    string
		timeout time.Duration
		wantErr bool
		errMsg  string
	}{
		{"valid timeout", 10 * time.Second, false, ""},
		{"one second", 1 * time.Second, false, ""},
		{"zero timeout", 0, true, "timeout must be positive"},
		{"negative timeout", -1 * time.Second, true, "timeout must be positive"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &BaseConfig{}
			opt := WithTimeout(tt.timeout)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.timeout, cfg.Timeout)
			}
		})
	}
}

func TestWithHeaders(t *testing.T) {
	headers := map[string]string{
		"X-Custom-Header": "value",
		"Authorization":   "Bearer token",
	}

	cfg := &BaseConfig{Headers: make(map[string]string)}
	opt := WithHeaders(headers)
	err := opt(cfg)
	require.NoError(t, err)
	assert.Equal(t, headers, cfg.Headers)
}

func TestWithHeader(t *testing.T) {
	cfg := &BaseConfig{}

	// Add first header
	err := WithHeader("X-Custom", "value1")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value1", cfg.Headers["X-Custom"])

	// Add second header
	err = WithHeader("Authorization", "Bearer token")(cfg)
	require.NoError(t, err)
	assert.Equal(t, "value1", cfg.Headers["X-Custom"])
	assert.Equal(t, "Bearer token", cfg.Headers["Authorization"])
}

func TestWithCompression(t *testing.T) {
	tests := []struct {
		name        string
		compression CompressionType
		wantErr     bool
		errMsg      string
	}{
		{"gzip", CompressionGzip, false, ""},
		{"none", CompressionNone, false, ""},
		{"invalid", CompressionType("invalid"), true, "invalid compression type"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := &BaseConfig{}
			opt := WithCompression(tt.compression)
			err := opt(cfg)
			if tt.wantErr {
				require.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				require.NoError(t, err)
				assert.Equal(t, tt.compression, cfg.Compression)
			}
		})
	}
}

func TestWithRetryConfig(t *testing.T) {
	t.Run("valid config", func(t *testing.T) {
		cfg := &BaseConfig{}
		retryCfg := DefaultRetryConfig()
		retryCfg.MaxRetries = 5
		opt := WithRetryConfig(retryCfg)
		err := opt(cfg)
		require.NoError(t, err)
		assert.Equal(t, 5, cfg.RetryConfig.MaxRetries)
	})

	t.Run("invalid config", func(t *testing.T) {
		cfg := &BaseConfig{}
		retryCfg := &RetryConfig{MaxRetries: -1}
		opt := WithRetryConfig(retryCfg)
		err := opt(cfg)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid retry config")
	})
}

func TestWithTLSConfig(t *testing.T) {
	t.Run("valid config", func(t *testing.T) {
		cfg := &BaseConfig{}
		tlsCfg := &TLSConfig{Insecure: true}
		opt := WithTLSConfig(tlsCfg)
		err := opt(cfg)
		require.NoError(t, err)
		assert.True(t, cfg.TLSConfig.Insecure)
	})

	t.Run("invalid config", func(t *testing.T) {
		cfg := &BaseConfig{}
		tlsCfg := &TLSConfig{CertFile: "/path/to/cert", KeyFile: ""}
		opt := WithTLSConfig(tlsCfg)
		err := opt(cfg)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "invalid TLS config")
	})
}

func TestInsecure(t *testing.T) {
	t.Run("nil tls config", func(t *testing.T) {
		cfg := &BaseConfig{TLSConfig: nil}
		opt := Insecure()
		err := opt(cfg)
		require.NoError(t, err)
		assert.NotNil(t, cfg.TLSConfig)
		assert.True(t, cfg.TLSConfig.Insecure)
	})

	t.Run("existing tls config", func(t *testing.T) {
		cfg := &BaseConfig{TLSConfig: &TLSConfig{Insecure: false}}
		opt := Insecure()
		err := opt(cfg)
		require.NoError(t, err)
		assert.True(t, cfg.TLSConfig.Insecure)
	})
}

func TestMergeOptions(t *testing.T) {
	opt1 := OptionFunc(func(cfg interface{}) error { return nil })
	opt2 := OptionFunc(func(cfg interface{}) error { return nil })
	opt3 := OptionFunc(func(cfg interface{}) error { return nil })

	result := MergeOptions(
		[]Option{opt1, opt2},
		[]Option{opt3},
	)

	assert.Len(t, result, 3)
}

func TestContextOption(t *testing.T) {
	called := false
	opt := ContextOption(func(ctx interface{}, cfg interface{}) error {
		called = true
		return nil
	})

	err := opt.Apply(struct{}{})
	require.NoError(t, err)
	assert.True(t, called)
}

func TestLazyOption(t *testing.T) {
	t.Run("lazy evaluation", func(t *testing.T) {
		called := false
		opt := LazyOption(func() Option {
			called = true
			return OptionFunc(func(cfg interface{}) error {
				return nil
			})
		})

		err := opt.Apply(struct{}{})
		require.NoError(t, err)
		assert.True(t, called)
	})

	t.Run("nil option", func(t *testing.T) {
		opt := LazyOption(func() Option {
			return nil
		})

		err := opt.Apply(struct{}{})
		require.NoError(t, err)
	})
}

func TestConditionalOption(t *testing.T) {
	t.Run("condition true", func(t *testing.T) {
		called := false
		innerOpt := OptionFunc(func(cfg interface{}) error {
			called = true
			return nil
		})

		opt := ConditionalOption(true, innerOpt)
		err := opt.Apply(struct{}{})
		require.NoError(t, err)
		assert.True(t, called)
	})

	t.Run("condition false", func(t *testing.T) {
		called := false
		innerOpt := OptionFunc(func(cfg interface{}) error {
			called = true
			return nil
		})

		opt := ConditionalOption(false, innerOpt)
		err := opt.Apply(struct{}{})
		require.NoError(t, err)
		assert.False(t, called)
	})
}

func TestComposeOptions(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		callOrder := []int{}
		opt1 := OptionFunc(func(cfg interface{}) error {
			callOrder = append(callOrder, 1)
			return nil
		})
		opt2 := OptionFunc(func(cfg interface{}) error {
			callOrder = append(callOrder, 2)
			return nil
		})

		composed := ComposeOptions(opt1, opt2)
		err := composed.Apply(struct{}{})
		require.NoError(t, err)
		assert.Equal(t, []int{1, 2}, callOrder)
	})

	t.Run("first error", func(t *testing.T) {
		expectedErr := errors.New("first error")
		opt1 := OptionFunc(func(cfg interface{}) error {
			return expectedErr
		})
		opt2 := OptionFunc(func(cfg interface{}) error {
			return nil
		})

		composed := ComposeOptions(opt1, opt2)
		err := composed.Apply(struct{}{})
		assert.ErrorIs(t, err, expectedErr)
	})

	t.Run("second error", func(t *testing.T) {
		expectedErr := errors.New("second error")
		opt1 := OptionFunc(func(cfg interface{}) error {
			return nil
		})
		opt2 := OptionFunc(func(cfg interface{}) error {
			return expectedErr
		})

		composed := ComposeOptions(opt1, opt2)
		err := composed.Apply(struct{}{})
		assert.ErrorIs(t, err, expectedErr)
	})
}

func TestBaseOption_Apply_WrongType(t *testing.T) {
	opt := BaseOption(func(cfg *BaseConfig) error {
		return nil
	})

	err := opt.Apply("wrong type")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "expected *BaseConfig")
}

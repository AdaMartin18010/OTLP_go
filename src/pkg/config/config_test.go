package config

import (
	"os"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestLoadOTLPConfig 测试加载OTLP配置
func TestLoadOTLPConfig(t *testing.T) {
	// Clear environment
	os.Clearenv()

	config := LoadOTLPConfig()

	require.NotNil(t, config)
	assert.Equal(t, "localhost:4317", config.Endpoint)
	assert.True(t, config.Insecure)
	assert.Equal(t, 0.1, config.SamplingRate)
	assert.Equal(t, "microservices-demo", config.ServiceName)
	assert.Equal(t, "1.0.0", config.ServiceVersion)
	assert.Equal(t, "dev", config.Environment)
}

// TestLoadOTLPConfigWithEnv 测试使用环境变量加载OTLP配置
func TestLoadOTLPConfigWithEnv(t *testing.T) {
	// Set environment variables
	os.Setenv("OTEL_ENDPOINT", "collector:4317")
	os.Setenv("OTEL_INSECURE", "false")
	os.Setenv("SAMPLING_RATE", "0.5")
	os.Setenv("SERVICE_NAME", "test-service")
	os.Setenv("SERVICE_VERSION", "2.0.0")
	os.Setenv("ENVIRONMENT", "prod")
	defer os.Clearenv()

	config := LoadOTLPConfig()

	require.NotNil(t, config)
	assert.Equal(t, "collector:4317", config.Endpoint)
	assert.False(t, config.Insecure)
	assert.Equal(t, 0.5, config.SamplingRate)
	assert.Equal(t, "test-service", config.ServiceName)
	assert.Equal(t, "2.0.0", config.ServiceVersion)
	assert.Equal(t, "prod", config.Environment)
}

// TestLoadServiceConfig 测试加载服务配置
func TestLoadServiceConfig(t *testing.T) {
	os.Clearenv()

	config := LoadServiceConfig()

	require.NotNil(t, config)
	assert.Equal(t, "8080", config.Port)
	assert.Equal(t, 10*time.Second, config.ReadTimeout)
	assert.Equal(t, 10*time.Second, config.WriteTimeout)
	assert.Equal(t, 60*time.Second, config.IdleTimeout)
}

// TestLoadServiceConfigWithEnv 测试使用环境变量加载服务配置
func TestLoadServiceConfigWithEnv(t *testing.T) {
	os.Setenv("PORT", "9090")
	os.Setenv("READ_TIMEOUT", "30s")
	os.Setenv("WRITE_TIMEOUT", "20s")
	os.Setenv("IDLE_TIMEOUT", "120s")
	defer os.Clearenv()

	config := LoadServiceConfig()

	require.NotNil(t, config)
	assert.Equal(t, "9090", config.Port)
	assert.Equal(t, 30*time.Second, config.ReadTimeout)
	assert.Equal(t, 20*time.Second, config.WriteTimeout)
	assert.Equal(t, 120*time.Second, config.IdleTimeout)
}

// TestGetEnv 测试获取环境变量
func TestGetEnv(t *testing.T) {
	tests := []struct {
		name         string
		key          string
		envValue     string
		defaultValue string
		expected     string
	}{
		{
			name:         "existing env var",
			key:          "TEST_KEY",
			envValue:     "test_value",
			defaultValue: "default",
			expected:     "test_value",
		},
		{
			name:         "missing env var",
			key:          "MISSING_KEY",
			envValue:     "",
			defaultValue: "default",
			expected:     "default",
		},
		{
			name:         "empty env var",
			key:          "EMPTY_KEY",
			envValue:     "",
			defaultValue: "default",
			expected:     "default",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			os.Clearenv()
			if tt.envValue != "" {
				os.Setenv(tt.key, tt.envValue)
			}

			result := getEnv(tt.key, tt.defaultValue)
			assert.Equal(t, tt.expected, result)
		})
	}
}

// TestGetEnvBool 测试获取布尔类型环境变量
func TestGetEnvBool(t *testing.T) {
	tests := []struct {
		name         string
		key          string
		envValue     string
		defaultValue bool
		expected     bool
	}{
		{
			name:         "true value",
			key:          "BOOL_TRUE",
			envValue:     "true",
			defaultValue: false,
			expected:     true,
		},
		{
			name:         "false value",
			key:          "BOOL_FALSE",
			envValue:     "false",
			defaultValue: true,
			expected:     false,
		},
		{
			name:         "1 as true",
			key:          "BOOL_ONE",
			envValue:     "1",
			defaultValue: false,
			expected:     true,
		},
		{
			name:         "0 as false",
			key:          "BOOL_ZERO",
			envValue:     "0",
			defaultValue: true,
			expected:     false,
		},
		{
			name:         "invalid value uses default",
			key:          "BOOL_INVALID",
			envValue:     "invalid",
			defaultValue: true,
			expected:     true,
		},
		{
			name:         "missing env uses default",
			key:          "BOOL_MISSING",
			envValue:     "",
			defaultValue: false,
			expected:     false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			os.Clearenv()
			if tt.envValue != "" {
				os.Setenv(tt.key, tt.envValue)
			}

			result := getEnvBool(tt.key, tt.defaultValue)
			assert.Equal(t, tt.expected, result)
		})
	}
}

// TestGetEnvFloat 测试获取浮点数类型环境变量
func TestGetEnvFloat(t *testing.T) {
	tests := []struct {
		name         string
		key          string
		envValue     string
		defaultValue float64
		expected     float64
	}{
		{
			name:         "valid float",
			key:          "FLOAT_VAL",
			envValue:     "3.14",
			defaultValue: 1.0,
			expected:     3.14,
		},
		{
			name:         "integer as float",
			key:          "FLOAT_INT",
			envValue:     "42",
			defaultValue: 1.0,
			expected:     42.0,
		},
		{
			name:         "negative float",
			key:          "FLOAT_NEG",
			envValue:     "-2.5",
			defaultValue: 1.0,
			expected:     -2.5,
		},
		{
			name:         "invalid value uses default",
			key:          "FLOAT_INVALID",
			envValue:     "not_a_number",
			defaultValue: 5.5,
			expected:     5.5,
		},
		{
			name:         "missing env uses default",
			key:          "FLOAT_MISSING",
			envValue:     "",
			defaultValue: 7.7,
			expected:     7.7,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			os.Clearenv()
			if tt.envValue != "" {
				os.Setenv(tt.key, tt.envValue)
			}

			result := getEnvFloat(tt.key, tt.defaultValue)
			assert.Equal(t, tt.expected, result)
		})
	}
}

// TestGetEnvInt 测试获取整数类型环境变量
func TestGetEnvInt(t *testing.T) {
	tests := []struct {
		name         string
		key          string
		envValue     string
		defaultValue int
		expected     int
	}{
		{
			name:         "valid int",
			key:          "INT_VAL",
			envValue:     "42",
			defaultValue: 10,
			expected:     42,
		},
		{
			name:         "negative int",
			key:          "INT_NEG",
			envValue:     "-100",
			defaultValue: 10,
			expected:     -100,
		},
		{
			name:         "zero",
			key:          "INT_ZERO",
			envValue:     "0",
			defaultValue: 10,
			expected:     0,
		},
		{
			name:         "invalid value uses default",
			key:          "INT_INVALID",
			envValue:     "not_a_number",
			defaultValue: 99,
			expected:     99,
		},
		{
			name:         "float value uses default",
			key:          "INT_FLOAT",
			envValue:     "3.14",
			defaultValue: 50,
			expected:     50,
		},
		{
			name:         "missing env uses default",
			key:          "INT_MISSING",
			envValue:     "",
			defaultValue: 123,
			expected:     123,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			os.Clearenv()
			if tt.envValue != "" {
				os.Setenv(tt.key, tt.envValue)
			}

			result := getEnvInt(tt.key, tt.defaultValue)
			assert.Equal(t, tt.expected, result)
		})
	}
}

// TestGetEnvDuration 测试获取时间间隔类型环境变量
func TestGetEnvDuration(t *testing.T) {
	tests := []struct {
		name         string
		key          string
		envValue     string
		defaultValue time.Duration
		expected     time.Duration
	}{
		{
			name:         "seconds",
			key:          "DUR_SEC",
			envValue:     "30s",
			defaultValue: 10 * time.Second,
			expected:     30 * time.Second,
		},
		{
			name:         "minutes",
			key:          "DUR_MIN",
			envValue:     "5m",
			defaultValue: 1 * time.Minute,
			expected:     5 * time.Minute,
		},
		{
			name:         "milliseconds",
			key:          "DUR_MS",
			envValue:     "500ms",
			defaultValue: 100 * time.Millisecond,
			expected:     500 * time.Millisecond,
		},
		{
			name:         "hours",
			key:          "DUR_HOUR",
			envValue:     "2h",
			defaultValue: 1 * time.Hour,
			expected:     2 * time.Hour,
		},
		{
			name:         "invalid value uses default",
			key:          "DUR_INVALID",
			envValue:     "invalid",
			defaultValue: 15 * time.Second,
			expected:     15 * time.Second,
		},
		{
			name:         "missing env uses default",
			key:          "DUR_MISSING",
			envValue:     "",
			defaultValue: 20 * time.Second,
			expected:     20 * time.Second,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			os.Clearenv()
			if tt.envValue != "" {
				os.Setenv(tt.key, tt.envValue)
			}

			result := getEnvDuration(tt.key, tt.defaultValue)
			assert.Equal(t, tt.expected, result)
		})
	}
}

// BenchmarkLoadOTLPConfig 基准测试加载OTLP配置
func BenchmarkLoadOTLPConfig(b *testing.B) {
	os.Clearenv()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = LoadOTLPConfig()
	}
}

// BenchmarkLoadServiceConfig 基准测试加载服务配置
func BenchmarkLoadServiceConfig(b *testing.B) {
	os.Clearenv()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = LoadServiceConfig()
	}
}

// BenchmarkGetEnv 基准测试获取环境变量
func BenchmarkGetEnv(b *testing.B) {
	os.Setenv("BENCH_KEY", "bench_value")
	defer os.Clearenv()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = getEnv("BENCH_KEY", "default")
	}
}

// BenchmarkGetEnvBool 基准测试获取布尔环境变量
func BenchmarkGetEnvBool(b *testing.B) {
	os.Setenv("BENCH_BOOL", "true")
	defer os.Clearenv()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = getEnvBool("BENCH_BOOL", false)
	}
}

// BenchmarkGetEnvFloat 基准测试获取浮点数环境变量
func BenchmarkGetEnvFloat(b *testing.B) {
	os.Setenv("BENCH_FLOAT", "3.14")
	defer os.Clearenv()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = getEnvFloat("BENCH_FLOAT", 1.0)
	}
}

// TestValidateOTLPConfig 测试验证OTLP配置
func TestValidateOTLPConfig(t *testing.T) {
	tests := []struct {
		name    string
		config  *OTLPConfig
		wantErr bool
		errMsg  string
	}{
		{
			name: "valid config",
			config: &OTLPConfig{
				Endpoint:       "localhost:4317",
				Insecure:       true,
				SamplingRate:   0.5,
				ServiceName:    "test-service",
				ServiceVersion: "1.0.0",
				Environment:    "dev",
			},
			wantErr: false,
		},
		{
			name: "empty endpoint",
			config: &OTLPConfig{
				Endpoint:     "",
				SamplingRate: 0.5,
				ServiceName:  "test-service",
			},
			wantErr: true,
			errMsg:  "Endpoint",
		},
		{
			name: "invalid sampling rate - negative",
			config: &OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: -0.1,
				ServiceName:  "test-service",
			},
			wantErr: true,
			errMsg:  "SamplingRate",
		},
		{
			name: "invalid sampling rate - too high",
			config: &OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 1.5,
				ServiceName:  "test-service",
			},
			wantErr: true,
			errMsg:  "SamplingRate",
		},
		{
			name: "empty service name",
			config: &OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 0.5,
				ServiceName:  "",
			},
			wantErr: true,
			errMsg:  "ServiceName",
		},
		{
			name: "boundary sampling rate - 0.0",
			config: &OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 0.0,
				ServiceName:  "test-service",
			},
			wantErr: false,
		},
		{
			name: "boundary sampling rate - 1.0",
			config: &OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 1.0,
				ServiceName:  "test-service",
			},
			wantErr: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := ValidateOTLPConfig(tt.config)
			if tt.wantErr {
				assert.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				assert.NoError(t, err)
			}
		})
	}
}

// TestValidateServiceConfig 测试验证服务配置
func TestValidateServiceConfig(t *testing.T) {
	tests := []struct {
		name    string
		config  *ServiceConfig
		wantErr bool
		errMsg  string
	}{
		{
			name: "valid config",
			config: &ServiceConfig{
				Port:         "8080",
				ReadTimeout:  10 * time.Second,
				WriteTimeout: 10 * time.Second,
				IdleTimeout:  60 * time.Second,
			},
			wantErr: false,
		},
		{
			name: "empty port",
			config: &ServiceConfig{
				Port:         "",
				ReadTimeout:  10 * time.Second,
				WriteTimeout: 10 * time.Second,
			},
			wantErr: true,
			errMsg:  "Port",
		},
		{
			name: "zero read timeout",
			config: &ServiceConfig{
				Port:         "8080",
				ReadTimeout:  0,
				WriteTimeout: 10 * time.Second,
			},
			wantErr: true,
			errMsg:  "ReadTimeout",
		},
		{
			name: "negative read timeout",
			config: &ServiceConfig{
				Port:         "8080",
				ReadTimeout:  -5 * time.Second,
				WriteTimeout: 10 * time.Second,
			},
			wantErr: true,
			errMsg:  "ReadTimeout",
		},
		{
			name: "zero write timeout",
			config: &ServiceConfig{
				Port:         "8080",
				ReadTimeout:  10 * time.Second,
				WriteTimeout: 0,
			},
			wantErr: true,
			errMsg:  "WriteTimeout",
		},
		{
			name: "negative write timeout",
			config: &ServiceConfig{
				Port:         "8080",
				ReadTimeout:  10 * time.Second,
				WriteTimeout: -5 * time.Second,
			},
			wantErr: true,
			errMsg:  "WriteTimeout",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := ValidateServiceConfig(tt.config)
			if tt.wantErr {
				assert.Error(t, err)
				assert.Contains(t, err.Error(), tt.errMsg)
			} else {
				assert.NoError(t, err)
			}
		})
	}
}

// TestConfigError 测试配置错误
func TestConfigError(t *testing.T) {
	err := &ConfigError{
		Field:   "TestField",
		Message: "Test error message",
	}

	errStr := err.Error()
	assert.Contains(t, errStr, "TestField")
	assert.Contains(t, errStr, "Test error message")
	assert.Equal(t, "TestField: Test error message", errStr)
}

// TestDefaultOTLPConfig 测试默认OTLP配置
func TestDefaultOTLPConfig(t *testing.T) {
	config := DefaultOTLPConfig()

	require.NotNil(t, config)
	assert.Equal(t, "localhost:4317", config.Endpoint)
	assert.True(t, config.Insecure)
	assert.Equal(t, 0.1, config.SamplingRate)
	assert.Equal(t, "microservices-demo", config.ServiceName)
	assert.Equal(t, "1.0.0", config.ServiceVersion)
	assert.Equal(t, "dev", config.Environment)

	// Should pass validation
	err := ValidateOTLPConfig(config)
	assert.NoError(t, err)
}

// TestDefaultServiceConfig 测试默认服务配置
func TestDefaultServiceConfig(t *testing.T) {
	config := DefaultServiceConfig()

	require.NotNil(t, config)
	assert.Equal(t, "8080", config.Port)
	assert.Equal(t, 10*time.Second, config.ReadTimeout)
	assert.Equal(t, 10*time.Second, config.WriteTimeout)
	assert.Equal(t, 60*time.Second, config.IdleTimeout)

	// Should pass validation
	err := ValidateServiceConfig(config)
	assert.NoError(t, err)
}

// TestConfigValidationIntegration 测试配置验证集成
func TestConfigValidationIntegration(t *testing.T) {
	// Load config from environment
	os.Setenv("OTEL_ENDPOINT", "collector:4317")
	os.Setenv("SAMPLING_RATE", "0.8")
	os.Setenv("SERVICE_NAME", "integration-test")
	os.Setenv("PORT", "9090")
	defer os.Clearenv()

	otlpConfig := LoadOTLPConfig()
	err := ValidateOTLPConfig(otlpConfig)
	assert.NoError(t, err)

	serviceConfig := LoadServiceConfig()
	err = ValidateServiceConfig(serviceConfig)
	assert.NoError(t, err)
}

// TestConfigErrorTypes 测试不同类型的配置错误
func TestConfigErrorTypes(t *testing.T) {
	errors := []*ConfigError{
		{Field: "Endpoint", Message: "cannot be empty"},
		{Field: "SamplingRate", Message: "out of range"},
		{Field: "ServiceName", Message: "invalid format"},
	}

	for _, err := range errors {
		errStr := err.Error()
		assert.Contains(t, errStr, err.Field)
		assert.Contains(t, errStr, err.Message)
	}
}

// BenchmarkValidateOTLPConfig 基准测试OTLP配置验证
func BenchmarkValidateOTLPConfig(b *testing.B) {
	config := DefaultOTLPConfig()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = ValidateOTLPConfig(config)
	}
}

// BenchmarkValidateServiceConfig 基准测试服务配置验证
func BenchmarkValidateServiceConfig(b *testing.B) {
	config := DefaultServiceConfig()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = ValidateServiceConfig(config)
	}
}

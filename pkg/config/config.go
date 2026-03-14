package config

import (
	"os"
	"strconv"
	"strings"
	"time"
)

// LoadOTLPConfig 加载 OpenTelemetry 配置
func LoadOTLPConfig() *OTLPConfig {
	return &OTLPConfig{
		Endpoint:       getEnv("OTEL_ENDPOINT", "localhost:4317"),
		Insecure:       getEnvBool("OTEL_INSECURE", true),
		SamplingRate:   getEnvFloat("SAMPLING_RATE", 0.1),
		ServiceName:    getEnv("SERVICE_NAME", "microservices-demo"),
		ServiceVersion: getEnv("SERVICE_VERSION", "1.0.0"),
		Environment:    getEnv("ENVIRONMENT", "dev"),
	}
}

// LoadServiceConfig 加载服务配置
func LoadServiceConfig() *ServiceConfig {
	return &ServiceConfig{
		Port:         getEnv("PORT", "8080"),
		ReadTimeout:  getEnvDuration("READ_TIMEOUT", 10*time.Second),
		WriteTimeout: getEnvDuration("WRITE_TIMEOUT", 10*time.Second),
		IdleTimeout:  getEnvDuration("IDLE_TIMEOUT", 60*time.Second),
	}
}

// OTLPConfig OpenTelemetry 配置
type OTLPConfig struct {
	Endpoint       string
	Insecure       bool
	SamplingRate   float64
	ServiceName    string
	ServiceVersion string
	Environment    string
}

// ServiceConfig 服务配置
type ServiceConfig struct {
	Port         string
	ReadTimeout  time.Duration
	WriteTimeout time.Duration
	IdleTimeout  time.Duration
}

// 辅助函数

// getEnv 获取环境变量，如果不存在则返回默认值
func getEnv(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

// getEnvBool 获取布尔类型环境变量
func getEnvBool(key string, defaultValue bool) bool {
	if value := os.Getenv(key); value != "" {
		if parsed, err := strconv.ParseBool(value); err == nil {
			return parsed
		}
	}
	return defaultValue
}

// getEnvFloat 获取浮点数类型环境变量
func getEnvFloat(key string, defaultValue float64) float64 {
	if value := os.Getenv(key); value != "" {
		if parsed, err := strconv.ParseFloat(value, 64); err == nil {
			return parsed
		}
	}
	return defaultValue
}

// getEnvInt 获取整数类型环境变量
func getEnvInt(key string, defaultValue int) int {
	if value := os.Getenv(key); value != "" {
		if parsed, err := strconv.Atoi(value); err == nil {
			return parsed
		}
	}
	return defaultValue
}

// getEnvDuration 获取时间间隔类型环境变量
func getEnvDuration(key string, defaultValue time.Duration) time.Duration {
	if value := os.Getenv(key); value != "" {
		if parsed, err := time.ParseDuration(value); err == nil {
			return parsed
		}
	}
	return defaultValue
}

// ValidateOTLPConfig 验证 OTLP 配置
func ValidateOTLPConfig(config *OTLPConfig) error {
	if config.Endpoint == "" {
		return &ConfigError{Field: "Endpoint", Message: "OTLP endpoint cannot be empty"}
	}

	if config.SamplingRate < 0.0 || config.SamplingRate > 1.0 {
		return &ConfigError{Field: "SamplingRate", Message: "Sampling rate must be between 0.0 and 1.0"}
	}

	if config.ServiceName == "" {
		return &ConfigError{Field: "ServiceName", Message: "Service name cannot be empty"}
	}

	return nil
}

// ValidateServiceConfig 验证服务配置
func ValidateServiceConfig(config *ServiceConfig) error {
	if config.Port == "" {
		return &ConfigError{Field: "Port", Message: "Port cannot be empty"}
	}

	if config.ReadTimeout <= 0 {
		return &ConfigError{Field: "ReadTimeout", Message: "Read timeout must be positive"}
	}

	if config.WriteTimeout <= 0 {
		return &ConfigError{Field: "WriteTimeout", Message: "Write timeout must be positive"}
	}

	return nil
}

// ConfigError 配置错误
type ConfigError struct {
	Field   string
	Message string
}

func (e *ConfigError) Error() string {
	return e.Field + ": " + e.Message
}

// 配置默认值

// DefaultOTLPConfig 默认 OTLP 配置
func DefaultOTLPConfig() *OTLPConfig {
	return &OTLPConfig{
		Endpoint:       "localhost:4317",
		Insecure:       true,
		SamplingRate:   0.1,
		ServiceName:    "microservices-demo",
		ServiceVersion: "1.0.0",
		Environment:    "dev",
	}
}

// DefaultServiceConfig 默认服务配置
func DefaultServiceConfig() *ServiceConfig {
	return &ServiceConfig{
		Port:         "8080",
		ReadTimeout:  10 * time.Second,
		WriteTimeout: 10 * time.Second,
		IdleTimeout:  60 * time.Second,
	}
}

// 配置合并

// MergeOTLPConfig 合并 OTLP 配置
func MergeOTLPConfig(base, override *OTLPConfig) *OTLPConfig {
	result := *base

	if override.Endpoint != "" {
		result.Endpoint = override.Endpoint
	}
	if override.Insecure != base.Insecure {
		result.Insecure = override.Insecure
	}
	if override.SamplingRate != 0 {
		result.SamplingRate = override.SamplingRate
	}
	if override.ServiceName != "" {
		result.ServiceName = override.ServiceName
	}
	if override.ServiceVersion != "" {
		result.ServiceVersion = override.ServiceVersion
	}
	if override.Environment != "" {
		result.Environment = override.Environment
	}

	return &result
}

// MergeServiceConfig 合并服务配置
func MergeServiceConfig(base, override *ServiceConfig) *ServiceConfig {
	result := *base

	if override.Port != "" {
		result.Port = override.Port
	}
	if override.ReadTimeout != 0 {
		result.ReadTimeout = override.ReadTimeout
	}
	if override.WriteTimeout != 0 {
		result.WriteTimeout = override.WriteTimeout
	}
	if override.IdleTimeout != 0 {
		result.IdleTimeout = override.IdleTimeout
	}

	return &result
}

// 配置导出

// ExportToEnv 导出配置到环境变量
func (c *OTLPConfig) ExportToEnv() {
	os.Setenv("OTEL_ENDPOINT", c.Endpoint)
	os.Setenv("OTEL_INSECURE", strconv.FormatBool(c.Insecure))
	os.Setenv("SAMPLING_RATE", strconv.FormatFloat(c.SamplingRate, 'f', -1, 64))
	os.Setenv("SERVICE_NAME", c.ServiceName)
	os.Setenv("SERVICE_VERSION", c.ServiceVersion)
	os.Setenv("ENVIRONMENT", c.Environment)
}

// ExportToEnv 导出服务配置到环境变量
func (c *ServiceConfig) ExportToEnv() {
	os.Setenv("PORT", c.Port)
	os.Setenv("READ_TIMEOUT", c.ReadTimeout.String())
	os.Setenv("WRITE_TIMEOUT", c.WriteTimeout.String())
	os.Setenv("IDLE_TIMEOUT", c.IdleTimeout.String())
}

// 配置字符串表示

// String 返回 OTLP 配置的字符串表示
func (c *OTLPConfig) String() string {
	return strings.Join([]string{
		"Endpoint: " + c.Endpoint,
		"Insecure: " + strconv.FormatBool(c.Insecure),
		"SamplingRate: " + strconv.FormatFloat(c.SamplingRate, 'f', -1, 64),
		"ServiceName: " + c.ServiceName,
		"ServiceVersion: " + c.ServiceVersion,
		"Environment: " + c.Environment,
	}, ", ")
}

// String 返回服务配置的字符串表示
func (c *ServiceConfig) String() string {
	return strings.Join([]string{
		"Port: " + c.Port,
		"ReadTimeout: " + c.ReadTimeout.String(),
		"WriteTimeout: " + c.WriteTimeout.String(),
		"IdleTimeout: " + c.IdleTimeout.String(),
	}, ", ")
}

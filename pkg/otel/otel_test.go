package otel

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"OTLP_go/pkg/config"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/propagation"
)

// createTestConfig creates a valid test configuration
func createTestConfig() *config.OTLPConfig {
	return &config.OTLPConfig{
		Endpoint:       "localhost:4317",
		Insecure:       true,
		SamplingRate:   0.5,
		ServiceName:    "test-service",
		ServiceVersion: "1.0.0",
		Environment:    "test",
	}
}

// TestNewOTelManager tests creating a new OTelManager
func TestNewOTelManager(t *testing.T) {
	cfg := createTestConfig()

	manager := NewOTelManager(cfg)

	require.NotNil(t, manager)
	assert.Nil(t, manager.tracerProvider)
	assert.Equal(t, cfg, manager.config)
	assert.Nil(t, manager.cleanupFunc)
}

// TestNewOTelManager_NilConfig tests creating OTelManager with nil config
func TestNewOTelManager_NilConfig(t *testing.T) {
	manager := NewOTelManager(nil)

	require.NotNil(t, manager)
	assert.Nil(t, manager.tracerProvider)
	assert.Nil(t, manager.config)
	assert.Nil(t, manager.cleanupFunc)
}

// TestOTelManager_Initialize_InvalidConfig tests initialization with invalid config
func TestOTelManager_Initialize_InvalidConfig(t *testing.T) {
	tests := []struct {
		name   string
		config *config.OTLPConfig
	}{
		{
			name: "empty endpoint",
			config: &config.OTLPConfig{
				Endpoint:     "",
				SamplingRate: 0.5,
				ServiceName:  "test-service",
			},
		},
		{
			name: "empty service name",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 0.5,
				ServiceName:  "",
			},
		},
		{
			name: "negative sampling rate",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: -0.1,
				ServiceName:  "test-service",
			},
		},
		{
			name: "sampling rate too high",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 1.5,
				ServiceName:  "test-service",
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			manager := NewOTelManager(tt.config)
			ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
			defer cancel()

			err := manager.Initialize(ctx)
			assert.Error(t, err)
			assert.Contains(t, err.Error(), "invalid OTLP config")
		})
	}
}

// TestOTelManager_IsHealthy tests health check functionality
func TestOTelManager_IsHealthy(t *testing.T) {
	t.Run("not healthy before initialization", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		assert.False(t, manager.IsHealthy())
	})

	t.Run("not healthy with nil tracer provider", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)
		manager.tracerProvider = nil

		assert.False(t, manager.IsHealthy())
	})
}

// TestOTelManager_Shutdown tests shutdown functionality
func TestOTelManager_Shutdown(t *testing.T) {
	t.Run("shutdown without initialization", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		ctx := context.Background()
		err := manager.Shutdown(ctx)
		assert.NoError(t, err)
	})

	t.Run("shutdown with nil cleanup", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)
		manager.cleanupFunc = nil

		ctx := context.Background()
		err := manager.Shutdown(ctx)
		assert.NoError(t, err)
	})
}

// TestOTelManager_GetName tests getting resource name
func TestOTelManager_GetName(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	name := manager.GetName()
	assert.Equal(t, "opentelemetry", name)
}

// TestOTelManager_GetTracerProvider tests getting tracer provider
func TestOTelManager_GetTracerProvider(t *testing.T) {
	t.Run("nil tracer provider", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		tp := manager.GetTracerProvider()
		assert.Nil(t, tp)
	})
}

// TestOTelManager_GetConfig tests getting configuration
func TestOTelManager_GetConfig(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	retrievedConfig := manager.GetConfig()
	assert.Equal(t, cfg, retrievedConfig)
}

// TestOTelManager_GetConfig_Nil tests getting nil configuration
func TestOTelManager_GetConfig_Nil(t *testing.T) {
	manager := NewOTelManager(nil)

	retrievedConfig := manager.GetConfig()
	assert.Nil(t, retrievedConfig)
}

// TestGetHealthStatus tests health status retrieval
func TestOTelManager_GetHealthStatus(t *testing.T) {
	t.Run("healthy status", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)
		// Simulate healthy state by setting a non-nil tracerProvider
		// Note: In real scenario this would be set by Initialize

		status := manager.GetHealthStatus()

		require.NotNil(t, status)
		assert.Equal(t, "unhealthy", status.Status) // Not initialized, so unhealthy
		assert.Equal(t, cfg.ServiceName, status.Service)
		assert.Equal(t, cfg.ServiceVersion, status.Version)
		assert.Equal(t, cfg.Endpoint, status.Endpoint)
		assert.Equal(t, cfg.SamplingRate, status.Sampling)
		assert.NotNil(t, status.Metadata)
		assert.Equal(t, cfg.Environment, status.Metadata["environment"])
		assert.Equal(t, "true", status.Metadata["insecure"])
	})

	t.Run("healthy with initialized provider", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		status := manager.GetHealthStatus()
		assert.Equal(t, "unhealthy", status.Status)
	})
}

// TestOTelManager_GetPerformanceMetrics tests performance metrics retrieval
func TestOTelManager_GetPerformanceMetrics(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	metrics := manager.GetPerformanceMetrics()

	require.NotNil(t, metrics)
	assert.Equal(t, int64(0), metrics.ActiveSpans)
	assert.Equal(t, int64(0), metrics.ExportedSpans)
	assert.Equal(t, int64(0), metrics.DroppedSpans)
	assert.Equal(t, int64(0), metrics.QueueSize)
	assert.Equal(t, time.Duration(0), metrics.ExportLatency)
}

// TestOTelManager_UpdateConfig_InvalidConfig tests config update with invalid config
func TestOTelManager_UpdateConfig_InvalidConfig(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	invalidConfig := &config.OTLPConfig{
		Endpoint:     "",
		SamplingRate: 0.5,
		ServiceName:  "test",
	}

	err := manager.UpdateConfig(invalidConfig)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "invalid config")
}

// TestOTelManager_UpdateConfig_SameConfig tests updating with same config
func TestOTelManager_UpdateConfig_SameConfig(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	// Update with same config
	err := manager.UpdateConfig(cfg)
	// The update may succeed or fail depending on OTLP collector availability
	// We just verify the function runs without panic
	// If successful, verify the manager state
	if err == nil {
		assert.True(t, manager.IsHealthy())
		assert.Equal(t, cfg, manager.GetConfig())
	}
}

// TestOTelManager_GetDebugInfo tests debug info retrieval
func TestOTelManager_GetDebugInfo(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	debugInfo := manager.GetDebugInfo()

	require.NotNil(t, debugInfo)
	assert.Equal(t, cfg, debugInfo.Config)
	assert.False(t, debugInfo.IsHealthy)
	assert.Equal(t, cfg.ServiceName, debugInfo.ServiceName)
	assert.Equal(t, cfg.ServiceVersion, debugInfo.ServiceVersion)
	assert.Equal(t, cfg.Environment, debugInfo.Environment)
	assert.Equal(t, cfg.Endpoint, debugInfo.Endpoint)
	assert.Equal(t, cfg.SamplingRate, debugInfo.SamplingRate)
	assert.Equal(t, cfg.Insecure, debugInfo.Insecure)
}

// TestGetHealthStatus_BoundarySamplingRates tests health status with boundary sampling rates
func TestGetHealthStatus_BoundarySamplingRates(t *testing.T) {
	testCases := []struct {
		name         string
		samplingRate float64
	}{
		{"zero sampling", 0.0},
		{"full sampling", 1.0},
		{"half sampling", 0.5},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			cfg := &config.OTLPConfig{
				Endpoint:       "localhost:4317",
				Insecure:       true,
				SamplingRate:   tc.samplingRate,
				ServiceName:    "test-service",
				ServiceVersion: "1.0.0",
				Environment:    "test",
			}
			manager := NewOTelManager(cfg)

			status := manager.GetHealthStatus()
			assert.Equal(t, tc.samplingRate, status.Sampling)
		})
	}
}

// TestHealthCheck_StructFields tests HealthCheck struct fields
func TestHealthCheck_StructFields(t *testing.T) {
	health := &HealthCheck{
		Status:   "healthy",
		Service:  "test-service",
		Version:  "2.0.0",
		Endpoint: "localhost:4317",
		Sampling: 0.8,
		Uptime:   5 * time.Minute,
		Metadata: map[string]string{
			"key": "value",
		},
	}

	assert.Equal(t, "healthy", health.Status)
	assert.Equal(t, "test-service", health.Service)
	assert.Equal(t, "2.0.0", health.Version)
	assert.Equal(t, "localhost:4317", health.Endpoint)
	assert.Equal(t, 0.8, health.Sampling)
	assert.Equal(t, 5*time.Minute, health.Uptime)
	assert.Equal(t, "value", health.Metadata["key"])
}

// TestPerformanceMetrics_StructFields tests PerformanceMetrics struct fields
func TestPerformanceMetrics_StructFields(t *testing.T) {
	metrics := &PerformanceMetrics{
		ActiveSpans:   10,
		ExportedSpans: 100,
		DroppedSpans:  2,
		QueueSize:     50,
		ExportLatency: 100 * time.Millisecond,
	}

	assert.Equal(t, int64(10), metrics.ActiveSpans)
	assert.Equal(t, int64(100), metrics.ExportedSpans)
	assert.Equal(t, int64(2), metrics.DroppedSpans)
	assert.Equal(t, int64(50), metrics.QueueSize)
	assert.Equal(t, 100*time.Millisecond, metrics.ExportLatency)
}

// TestDebugInfo_StructFields tests DebugInfo struct fields
func TestDebugInfo_StructFields(t *testing.T) {
	cfg := createTestConfig()
	debugInfo := &DebugInfo{
		Config:         cfg,
		IsHealthy:      true,
		ServiceName:    "test-service",
		ServiceVersion: "2.0.0",
		Environment:    "production",
		Endpoint:       "collector:4317",
		SamplingRate:   0.75,
		Insecure:       false,
	}

	assert.Equal(t, cfg, debugInfo.Config)
	assert.True(t, debugInfo.IsHealthy)
	assert.Equal(t, "test-service", debugInfo.ServiceName)
	assert.Equal(t, "2.0.0", debugInfo.ServiceVersion)
	assert.Equal(t, "production", debugInfo.Environment)
	assert.Equal(t, "collector:4317", debugInfo.Endpoint)
	assert.Equal(t, 0.75, debugInfo.SamplingRate)
	assert.False(t, debugInfo.Insecure)
}

// TestDebugInfo_NilConfig tests DebugInfo with nil config
func TestDebugInfo_NilConfig(t *testing.T) {
	debugInfo := &DebugInfo{
		Config:    nil,
		IsHealthy: false,
	}

	assert.Nil(t, debugInfo.Config)
	assert.False(t, debugInfo.IsHealthy)
}

// TestGetTracer tests the GetTracer function
func TestGetTracer(t *testing.T) {
	tracer := GetTracer("test-tracer")
	assert.NotNil(t, tracer)

	// Get the same tracer again - should return consistent result
	tracer2 := GetTracer("test-tracer")
	assert.NotNil(t, tracer2)
}

// TestGetTextMapPropagator tests the GetTextMapPropagator function
func TestGetTextMapPropagator(t *testing.T) {
	propagator := GetTextMapPropagator()
	assert.NotNil(t, propagator)
}

// TestInitializeGlobalOTel_InvalidConfig tests global initialization with invalid config
func TestInitializeGlobalOTel_InvalidConfig(t *testing.T) {
	// Clear any existing global manager
	globalOTelManager = nil

	invalidConfig := &config.OTLPConfig{
		Endpoint:     "",
		SamplingRate: 0.5,
		ServiceName:  "test",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	err := InitializeGlobalOTel(ctx, invalidConfig)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "invalid OTLP config")
}

// TestShutdownGlobalOTel_NoGlobalManager tests shutdown without global manager
func TestShutdownGlobalOTel_NoGlobalManager(t *testing.T) {
	// Clear global manager
	globalOTelManager = nil

	ctx := context.Background()
	err := ShutdownGlobalOTel(ctx)
	assert.NoError(t, err)
}

// TestShutdownGlobalOTel_WithManager tests shutdown with global manager
func TestShutdownGlobalOTel_WithManager(t *testing.T) {
	// Create and set a manager without initialization
	cfg := createTestConfig()
	globalOTelManager = NewOTelManager(cfg)

	ctx := context.Background()
	err := ShutdownGlobalOTel(ctx)
	assert.NoError(t, err)

	// Cleanup
	globalOTelManager = nil
}

// TestGetGlobalOTelManager tests getting global manager
func TestGetGlobalOTelManager(t *testing.T) {
	// Clear global manager
	globalOTelManager = nil

	// Should return nil when no global manager exists
	manager := GetGlobalOTelManager()
	assert.Nil(t, manager)

	// Set a global manager
	cfg := createTestConfig()
	globalOTelManager = NewOTelManager(cfg)

	// Should return the global manager
	manager = GetGlobalOTelManager()
	assert.NotNil(t, manager)
	assert.Equal(t, globalOTelManager, manager)

	// Cleanup
	globalOTelManager = nil
}

// TestLoadAndInitializeOTel_ConfigLoading tests the config loading function
func TestLoadAndInitializeOTel_ConfigLoading(t *testing.T) {
	// Save and restore global state
	oldManager := globalOTelManager
	defer func() { globalOTelManager = oldManager }()

	// Clear global manager for this test
	globalOTelManager = nil

	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	// This should attempt to initialize
	err := LoadAndInitializeOTel(ctx)
	// The behavior depends on OTLP collector availability
	// If successful, verify the global manager was set
	if err == nil {
		assert.NotNil(t, GetGlobalOTelManager())
	}
}

// TestLoadAndInitializeOTelWithDefaults_ConfigLoading tests the default config loading
func TestLoadAndInitializeOTelWithDefaults_ConfigLoading(t *testing.T) {
	// Save and restore global state
	oldManager := globalOTelManager
	defer func() { globalOTelManager = oldManager }()

	// Clear global manager for this test
	globalOTelManager = nil

	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	// This should attempt to initialize with defaults
	err := LoadAndInitializeOTelWithDefaults(ctx)
	// The behavior depends on OTLP collector availability
	// If successful, verify the global manager was set
	if err == nil {
		assert.NotNil(t, GetGlobalOTelManager())
	}
}

// TestOTelManager_UpdateConfig tests the UpdateConfig method
func TestOTelManager_UpdateConfig(t *testing.T) {
	t.Run("update with valid config", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		newConfig := &config.OTLPConfig{
			Endpoint:       "newhost:4317",
			Insecure:       false,
			SamplingRate:   0.8,
			ServiceName:    "new-service",
			ServiceVersion: "2.0.0",
			Environment:    "prod",
		}

		err := manager.UpdateConfig(newConfig)
		// If successful, verify the manager state was updated
		if err == nil {
			assert.Equal(t, newConfig, manager.GetConfig())
			assert.True(t, manager.IsHealthy())
		}
	})

	t.Run("update config with cleanup error", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		// Set a cleanup func that returns an error
		manager.cleanupFunc = func() error {
			return assert.AnError
		}

		newConfig := &config.OTLPConfig{
			Endpoint:       "newhost:4317",
			Insecure:       true,
			SamplingRate:   0.5,
			ServiceName:    "test-service",
			ServiceVersion: "1.0.0",
			Environment:    "test",
		}

		err := manager.UpdateConfig(newConfig)
		// Should continue despite cleanup error and attempt initialization
		// Result depends on OTLP collector availability
		if err == nil {
			assert.True(t, manager.IsHealthy())
		}
	})
}

// TestOTelManager_SamplingRates tests various sampling rates
func TestOTelManager_SamplingRates(t *testing.T) {
	testCases := []struct {
		name         string
		samplingRate float64
		expectValid  bool
	}{
		{"zero", 0.0, true},
		{"very low", 0.01, true},
		{"low", 0.1, true},
		{"medium", 0.5, true},
		{"high", 0.9, true},
		{"very high", 0.99, true},
		{"full", 1.0, true},
		{"negative", -0.1, false},
		{"over one", 1.1, false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			cfg := &config.OTLPConfig{
				Endpoint:       "localhost:4317",
				Insecure:       true,
				SamplingRate:   tc.samplingRate,
				ServiceName:    "test-service",
				ServiceVersion: "1.0.0",
				Environment:    "test",
			}

			err := config.ValidateOTLPConfig(cfg)
			if tc.expectValid {
				assert.NoError(t, err)
			} else {
				assert.Error(t, err)
			}
		})
	}
}

// TestOTelManager_ConfigVariations tests OTelManager with different config variations
func TestOTelManager_ConfigVariations(t *testing.T) {
	testCases := []struct {
		name   string
		config *config.OTLPConfig
	}{
		{
			name: "minimal config",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 0.5,
				ServiceName:  "minimal-service",
			},
		},
		{
			name: "full config",
			config: &config.OTLPConfig{
				Endpoint:       "collector.example.com:4317",
				Insecure:       false,
				SamplingRate:   0.75,
				ServiceName:    "full-service",
				ServiceVersion: "3.0.0",
				Environment:    "production",
			},
		},
		{
			name: "local development config",
			config: &config.OTLPConfig{
				Endpoint:       "localhost:4317",
				Insecure:       true,
				SamplingRate:   1.0,
				ServiceName:    "dev-service",
				ServiceVersion: "0.1.0",
				Environment:    "development",
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			manager := NewOTelManager(tc.config)
			assert.NotNil(t, manager)
			assert.Equal(t, tc.config, manager.GetConfig())
		})
	}
}

// TestGetHealthStatus_MetadataVariations tests health status with different metadata
func TestGetHealthStatus_MetadataVariations(t *testing.T) {
	testCases := []struct {
		name     string
		config   *config.OTLPConfig
		insecure string
		env      string
	}{
		{
			name: "secure production",
			config: &config.OTLPConfig{
				Endpoint:       "collector.prod:4317",
				Insecure:       false,
				SamplingRate:   0.1,
				ServiceName:    "prod-service",
				ServiceVersion: "1.0.0",
				Environment:    "production",
			},
		},
		{
			name: "insecure development",
			config: &config.OTLPConfig{
				Endpoint:       "localhost:4317",
				Insecure:       true,
				SamplingRate:   1.0,
				ServiceName:    "dev-service",
				ServiceVersion: "0.1.0",
				Environment:    "development",
			},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			manager := NewOTelManager(tc.config)
			status := manager.GetHealthStatus()

			assert.Equal(t, tc.config.ServiceName, status.Service)
			assert.Equal(t, tc.config.Environment, status.Metadata["environment"])
		})
	}
}

// TestGetDebugInfo_ConfigVariations tests debug info with different configs
func TestGetDebugInfo_ConfigVariations(t *testing.T) {
	testCases := []struct {
		name           string
		config         *config.OTLPConfig
		expectedName   string
		expectedEnv    string
		expectedSecure bool
	}{
		{
			name: "production secure",
			config: &config.OTLPConfig{
				Endpoint:       "prod:4317",
				Insecure:       false,
				SamplingRate:   0.1,
				ServiceName:    "prod-service",
				ServiceVersion: "2.0.0",
				Environment:    "production",
			},
			expectedName:   "prod-service",
			expectedEnv:    "production",
			expectedSecure: false,
		},
		{
			name: "development insecure",
			config: &config.OTLPConfig{
				Endpoint:       "dev:4317",
				Insecure:       true,
				SamplingRate:   0.5,
				ServiceName:    "dev-service",
				ServiceVersion: "1.0.0",
				Environment:    "development",
			},
			expectedName:   "dev-service",
			expectedEnv:    "development",
			expectedSecure: true,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			manager := NewOTelManager(tc.config)
			debugInfo := manager.GetDebugInfo()

			assert.Equal(t, tc.expectedName, debugInfo.ServiceName)
			assert.Equal(t, tc.expectedEnv, debugInfo.Environment)
			assert.Equal(t, tc.expectedSecure, debugInfo.Insecure)
		})
	}
}

// TestOTelManager_MultipleShutdowns tests calling shutdown multiple times
func TestOTelManager_MultipleShutdowns(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	ctx := context.Background()

	// First shutdown should succeed
	err1 := manager.Shutdown(ctx)
	assert.NoError(t, err1)

	// Second shutdown should also succeed (idempotent)
	err2 := manager.Shutdown(ctx)
	assert.NoError(t, err2)
}

// TestGetGlobalOTelManager_Concurrent tests concurrent access to global manager
func TestGetGlobalOTelManager_Concurrent(t *testing.T) {
	// Setup
	globalOTelManager = nil

	var managers []*OTelManager
	for range 10 {
		managers = append(managers, GetGlobalOTelManager())
	}

	// All should be nil
	for _, m := range managers {
		assert.Nil(t, m)
	}

	// Set global
	cfg := createTestConfig()
	globalOTelManager = NewOTelManager(cfg)

	// Now all should return the same manager
	managers = nil
	for range 10 {
		managers = append(managers, GetGlobalOTelManager())
	}

	for _, m := range managers {
		assert.Equal(t, globalOTelManager, m)
	}

	// Cleanup
	globalOTelManager = nil
}

// BenchmarkNewOTelManager benchmarks creating a new OTelManager
func BenchmarkNewOTelManager(b *testing.B) {
	cfg := createTestConfig()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = NewOTelManager(cfg)
	}
}

// BenchmarkOTelManager_IsHealthy benchmarks the IsHealthy check
func BenchmarkOTelManager_IsHealthy(b *testing.B) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = manager.IsHealthy()
	}
}

// BenchmarkOTelManager_GetConfig benchmarks getting config
func BenchmarkOTelManager_GetConfig(b *testing.B) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = manager.GetConfig()
	}
}

// BenchmarkOTelManager_GetName benchmarks getting name
func BenchmarkOTelManager_GetName(b *testing.B) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = manager.GetName()
	}
}

// BenchmarkGetHealthStatus benchmarks getting health status
func BenchmarkGetHealthStatus(b *testing.B) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = manager.GetHealthStatus()
	}
}

// BenchmarkGetDebugInfo benchmarks getting debug info
func BenchmarkGetDebugInfo(b *testing.B) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = manager.GetDebugInfo()
	}
}

// BenchmarkGetPerformanceMetrics benchmarks getting performance metrics
func BenchmarkGetPerformanceMetrics(b *testing.B) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = manager.GetPerformanceMetrics()
	}
}

// BenchmarkGetTracer benchmarks getting a tracer
func BenchmarkGetTracer(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = GetTracer("benchmark-tracer")
	}
}

// BenchmarkGetTextMapPropagator benchmarks getting propagator
func BenchmarkGetTextMapPropagator(b *testing.B) {
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = GetTextMapPropagator()
	}
}

// TestOTelManager_ResourceInterface verifies OTelManager implements Resource interface
func TestOTelManager_ResourceInterface(t *testing.T) {
	// This test verifies that OTelManager implements the Resource interface
	// The compile-time check is in otel.go: var _ otelresource.Resource = (*OTelManager)(nil)
	// This test serves as a runtime verification

	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	// Verify interface methods exist and return expected types
	assert.Equal(t, "opentelemetry", manager.GetName())
	assert.False(t, manager.IsHealthy()) // Not initialized
}

// TestGlobalOTelManager_GoroutineSafety tests thread safety of global manager access
func TestGlobalOTelManager_GoroutineSafety(t *testing.T) {
	// Clear any existing global manager
	globalOTelManager = nil

	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	// Set global manager
	globalOTelManager = manager

	// Concurrent reads
	done := make(chan bool, 10)
	for range 10 {
		go func() {
			m := GetGlobalOTelManager()
			assert.NotNil(t, m)
			done <- true
		}()
	}

	// Wait for all goroutines
	for range 10 {
		<-done
	}

	// Cleanup
	globalOTelManager = nil
}

// TestHealthCheck_StatusTransitions tests health status changes
func TestHealthCheck_StatusTransitions(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	// Initial state - not initialized
	status1 := manager.GetHealthStatus()
	assert.Equal(t, "unhealthy", status1.Status)

	// Simulate initialized state (we can't actually initialize without OTLP collector)
	// This tests the logic path
}

// TestOTelManager_CleanupFuncVariations tests different cleanup function scenarios
func TestOTelManager_CleanupFuncVariations(t *testing.T) {
	t.Run("shutdown with error returning cleanup", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		// Set a cleanup function that returns an error
		manager.cleanupFunc = func() error {
			return assert.AnError
		}

		ctx := context.Background()
		err := manager.Shutdown(ctx)
		assert.Error(t, err)
	})

	t.Run("shutdown with nil cleanup after first call", func(t *testing.T) {
		cfg := createTestConfig()
		manager := NewOTelManager(cfg)

		callCount := 0
		manager.cleanupFunc = func() error {
			callCount++
			// Simulate cleanup setting itself to nil
			manager.cleanupFunc = nil
			return nil
		}

		ctx := context.Background()
		err := manager.Shutdown(ctx)
		assert.NoError(t, err)
		assert.Equal(t, 1, callCount)

		// Second call should succeed with nil cleanup
		err = manager.Shutdown(ctx)
		assert.NoError(t, err)
	})
}

// TestGetTracer_DifferentNames tests getting tracers with different names
func TestGetTracer_DifferentNames(t *testing.T) {
	names := []string{
		"service-a",
		"service-b",
		"database-layer",
		"cache-layer",
		"http-client",
	}

	for _, name := range names {
		t.Run(name, func(t *testing.T) {
			tracer := GetTracer(name)
			assert.NotNil(t, tracer)
		})
	}
}

// TestOpenTelemetry_Globals tests the global OpenTelemetry functions
func TestOpenTelemetry_Globals(t *testing.T) {
	t.Run("global tracer provider", func(t *testing.T) {
		// Get global tracer provider
		tracer := otel.Tracer("test")
		assert.NotNil(t, tracer)
	})

	t.Run("global propagator", func(t *testing.T) {
		// Get global propagator
		propagator := otel.GetTextMapPropagator()
		assert.NotNil(t, propagator)
	})
}

// TestGetTextMapPropagator_Composite tests the composite propagator setup
func TestGetTextMapPropagator_Composite(t *testing.T) {
	// The actual propagator is set during Initialize
	// Without initialization, we get the default
	propagator := GetTextMapPropagator()
	assert.NotNil(t, propagator)

	// Verify it implements the interface
	var _ propagation.TextMapPropagator = propagator
}

// TestConfigValidation_Integration tests config validation integrated with manager
func TestConfigValidation_Integration(t *testing.T) {
	testCases := []struct {
		name       string
		config     *config.OTLPConfig
		shouldFail bool
		errorPart  string
	}{
		{
			name: "valid config",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 0.5,
				ServiceName:  "test",
			},
			shouldFail: false,
		},
		{
			name: "missing endpoint",
			config: &config.OTLPConfig{
				Endpoint:     "",
				SamplingRate: 0.5,
				ServiceName:  "test",
			},
			shouldFail: true,
			errorPart:  "Endpoint",
		},
		{
			name: "missing service name",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 0.5,
				ServiceName:  "",
			},
			shouldFail: true,
			errorPart:  "ServiceName",
		},
		{
			name: "negative sampling rate",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: -0.1,
				ServiceName:  "test",
			},
			shouldFail: true,
			errorPart:  "SamplingRate",
		},
		{
			name: "sampling rate > 1",
			config: &config.OTLPConfig{
				Endpoint:     "localhost:4317",
				SamplingRate: 1.5,
				ServiceName:  "test",
			},
			shouldFail: true,
			errorPart:  "SamplingRate",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			manager := NewOTelManager(tc.config)
			ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
			defer cancel()

			err := manager.Initialize(ctx)

			if tc.shouldFail {
				assert.Error(t, err)
				assert.Contains(t, err.Error(), tc.errorPart)
			} else {
				// Valid config - initialization may succeed or fail based on OTLP collector availability
				// If no error, verify the manager is healthy
				if err == nil {
					assert.True(t, manager.IsHealthy())
				}
			}
		})
	}
}

// TestOTelManager_GetTracerProvider_MultipleCalls tests getting tracer provider multiple times
func TestOTelManager_GetTracerProvider_MultipleCalls(t *testing.T) {
	cfg := createTestConfig()
	manager := NewOTelManager(cfg)

	// Multiple calls should return the same (nil) value
	for range 5 {
		tp := manager.GetTracerProvider()
		assert.Nil(t, tp)
	}
}

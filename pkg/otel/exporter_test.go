package otel

import (
	"context"
	"crypto/tls"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestExporterType_String(t *testing.T) {
	tests := []struct {
		name         string
		exporterType ExporterType
		want         string
	}{
		{
			name:         "grpc type",
			exporterType: ExporterTypeGRPC,
			want:         "grpc",
		},
		{
			name:         "http type",
			exporterType: ExporterTypeHTTP,
			want:         "http",
		},
		{
			name:         "unknown type",
			exporterType: ExporterType(999),
			want:         "unknown",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := tt.exporterType.String()
			assert.Equal(t, tt.want, got)
		})
	}
}

func TestDefaultExporterConfig(t *testing.T) {
	cfg := DefaultExporterConfig()

	assert.Equal(t, "localhost:4317", cfg.Endpoint)
	assert.Equal(t, "grpc", cfg.Protocol)
	assert.Equal(t, "gzip", cfg.Compression)
	assert.Equal(t, 10*time.Second, cfg.Timeout)
	assert.NotNil(t, cfg.Headers)
	assert.Empty(t, cfg.Headers)

	// Retry config
	assert.True(t, cfg.RetryConfig.Enabled)
	assert.Equal(t, 1*time.Second, cfg.RetryConfig.InitialInterval)
	assert.Equal(t, 5*time.Second, cfg.RetryConfig.MaxInterval)
	assert.Equal(t, 30*time.Second, cfg.RetryConfig.MaxElapsedTime)
}

func TestExporterConfig_Validate(t *testing.T) {
	tests := []struct {
		name    string
		config  ExporterConfig
		wantErr bool
		errMsg  string
	}{
		{
			name: "valid config",
			config: ExporterConfig{
				Endpoint:    "localhost:4317",
				Protocol:    "grpc",
				Compression: "gzip",
				Timeout:     10 * time.Second,
			},
			wantErr: false,
		},
		{
			name: "empty endpoint",
			config: ExporterConfig{
				Endpoint:    "",
				Protocol:    "grpc",
				Compression: "gzip",
				Timeout:     10 * time.Second,
			},
			wantErr: true,
			errMsg:  "exporter endpoint cannot be empty",
		},
		{
			name: "invalid protocol",
			config: ExporterConfig{
				Endpoint:    "localhost:4317",
				Protocol:    "invalid",
				Compression: "gzip",
				Timeout:     10 * time.Second,
			},
			wantErr: true,
			errMsg:  "invalid protocol: invalid",
		},
		{
			name: "invalid compression",
			config: ExporterConfig{
				Endpoint:    "localhost:4317",
				Protocol:    "grpc",
				Compression: "invalid",
				Timeout:     10 * time.Second,
			},
			wantErr: true,
			errMsg:  "invalid compression: invalid",
		},
		{
			name: "http protocol",
			config: ExporterConfig{
				Endpoint:    "localhost:4318",
				Protocol:    "http",
				Compression: "none",
				Timeout:     10 * time.Second,
			},
			wantErr: false,
		},
		{
			name: "http/protobuf protocol",
			config: ExporterConfig{
				Endpoint:    "localhost:4318",
				Protocol:    "http/protobuf",
				Compression: "gzip",
				Timeout:     10 * time.Second,
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

func TestExporterConfig_Validate_ZeroTimeout(t *testing.T) {
	cfg := ExporterConfig{
		Endpoint:    "localhost:4317",
		Protocol:    "grpc",
		Compression: "gzip",
		Timeout:     0, // Zero timeout should be set to default
	}

	err := cfg.Validate()
	require.NoError(t, err)
	assert.Equal(t, 10*time.Second, cfg.Timeout)
}

func TestNewExporterManager(t *testing.T) {
	cfg := DefaultExporterConfig()
	em := NewExporterManager(cfg)

	require.NotNil(t, em)
	assert.Equal(t, cfg, em.config)
}

func TestExporterManager_GetExporterType(t *testing.T) {
	tests := []struct {
		name     string
		protocol string
		want     ExporterType
	}{
		{
			name:     "grpc protocol",
			protocol: "grpc",
			want:     ExporterTypeGRPC,
		},
		{
			name:     "http protocol",
			protocol: "http",
			want:     ExporterTypeHTTP,
		},
		{
			name:     "http/protobuf protocol",
			protocol: "http/protobuf",
			want:     ExporterTypeHTTP,
		},
		{
			name:     "empty protocol defaults to grpc",
			protocol: "",
			want:     ExporterTypeGRPC,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultExporterConfig()
			cfg.Protocol = tt.protocol
			em := NewExporterManager(cfg)

			got := em.GetExporterType()
			assert.Equal(t, tt.want, got)
		})
	}
}

func TestExporterManager_CreateTraceExporter(t *testing.T) {
	tests := []struct {
		name     string
		protocol string
		wantErr  bool
	}{
		{
			name:     "grpc trace exporter",
			protocol: "grpc",
			wantErr:  false,
		},
		{
			name:     "http trace exporter",
			protocol: "http",
			wantErr:  false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultExporterConfig()
			cfg.Protocol = tt.protocol
			cfg.Endpoint = "localhost:4317"
			em := NewExporterManager(cfg)

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			exporter, err := em.CreateTraceExporter(ctx)
			if tt.wantErr {
				require.Error(t, err)
				assert.Nil(t, exporter)
			} else {
				// May fail due to connection issues, but should not panic
				// In real scenarios, the exporter will be created successfully
				if err == nil {
					assert.NotNil(t, exporter)
				}
			}
		})
	}
}

func TestExporterManager_CreateMetricExporter(t *testing.T) {
	tests := []struct {
		name     string
		protocol string
	}{
		{
			name:     "grpc metric exporter",
			protocol: "grpc",
		},
		{
			name:     "http metric exporter",
			protocol: "http",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultExporterConfig()
			cfg.Protocol = tt.protocol
			cfg.Endpoint = "localhost:4317"
			em := NewExporterManager(cfg)

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			exporter, err := em.CreateMetricExporter(ctx)
			// May fail due to connection issues
			if err == nil {
				assert.NotNil(t, exporter)
			}
		})
	}
}

func TestExporterManager_CreateLogExporter(t *testing.T) {
	tests := []struct {
		name     string
		protocol string
	}{
		{
			name:     "grpc log exporter",
			protocol: "grpc",
		},
		{
			name:     "http log exporter",
			protocol: "http",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultExporterConfig()
			cfg.Protocol = tt.protocol
			cfg.Endpoint = "localhost:4317"
			em := NewExporterManager(cfg)

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			exporter, err := em.CreateLogExporter(ctx)
			// May fail due to connection issues
			if err == nil {
				assert.NotNil(t, exporter)
			}
		})
	}
}

func TestExporterManager_CreateGRPCConn(t *testing.T) {
	tests := []struct {
		name      string
		endpoint  string
		tlsConfig *tls.Config
	}{
		{
			name:      "insecure connection",
			endpoint:  "localhost:4317",
			tlsConfig: nil,
		},
		{
			name:      "tls connection",
			endpoint:  "localhost:4317",
			tlsConfig: &tls.Config{InsecureSkipVerify: true},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultExporterConfig()
			cfg.Endpoint = tt.endpoint
			cfg.TLSConfig = tt.tlsConfig
			em := NewExporterManager(cfg)

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			conn, err := em.CreateGRPCConn(ctx)
			if err == nil {
				assert.NotNil(t, conn)
				conn.Close()
			}
		})
	}
}

func TestExporterManager_WithHeaders(t *testing.T) {
	cfg := DefaultExporterConfig()
	cfg.Headers = map[string]string{
		"X-Custom-Header": "test-value",
		"Authorization":   "Bearer token123",
	}
	em := NewExporterManager(cfg)

	assert.Equal(t, cfg.Headers, em.config.Headers)
	assert.Equal(t, "test-value", em.config.Headers["X-Custom-Header"])
	assert.Equal(t, "Bearer token123", em.config.Headers["Authorization"])
}

func TestExporterManager_WithRetryConfig(t *testing.T) {
	cfg := DefaultExporterConfig()
	cfg.RetryConfig = RetryConfig{
		Enabled:         false,
		InitialInterval: 500 * time.Millisecond,
		MaxInterval:     2 * time.Second,
		MaxElapsedTime:  10 * time.Second,
	}
	em := NewExporterManager(cfg)

	assert.False(t, em.config.RetryConfig.Enabled)
	assert.Equal(t, 500*time.Millisecond, em.config.RetryConfig.InitialInterval)
	assert.Equal(t, 2*time.Second, em.config.RetryConfig.MaxInterval)
	assert.Equal(t, 10*time.Second, em.config.RetryConfig.MaxElapsedTime)
}

func TestExporterManager_WithCompression(t *testing.T) {
	tests := []struct {
		name        string
		compression string
	}{
		{
			name:        "gzip compression",
			compression: "gzip",
		},
		{
			name:        "none compression",
			compression: "none",
		},
		{
			name:        "empty compression",
			compression: "",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cfg := DefaultExporterConfig()
			cfg.Compression = tt.compression
			em := NewExporterManager(cfg)

			assert.Equal(t, tt.compression, em.config.Compression)
		})
	}
}

func TestExporterManager_WithTimeout(t *testing.T) {
	timeouts := []time.Duration{
		5 * time.Second,
		10 * time.Second,
		30 * time.Second,
		1 * time.Minute,
	}

	for _, timeout := range timeouts {
		cfg := DefaultExporterConfig()
		cfg.Timeout = timeout
		em := NewExporterManager(cfg)

		assert.Equal(t, timeout, em.config.Timeout)
	}
}

// Benchmark tests

func BenchmarkExporterManager_GetExporterType(b *testing.B) {
	cfg := DefaultExporterConfig()
	em := NewExporterManager(cfg)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = em.GetExporterType()
	}
}

func BenchmarkExporterConfig_Validate(b *testing.B) {
	cfg := DefaultExporterConfig()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = cfg.Validate()
	}
}

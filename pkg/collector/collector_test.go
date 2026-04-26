package collector

import (
	"context"
	"crypto/rand"
	"crypto/rsa"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"fmt"
	"math/big"
	"net"
	"os"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
	"gopkg.in/yaml.v3"
)

// --- Component Tests ---

func TestComponentID(t *testing.T) {
	id := ComponentID{Type: "otlp", Name: "traces"}
	assert.Equal(t, "otlp/traces", id.String())

	id2 := ComponentID{Type: "otlp"}
	assert.Equal(t, "otlp", id2.String())
	assert.True(t, id2.IsEmpty() == false)

	empty := ComponentID{}
	assert.True(t, empty.IsEmpty())
}

func TestComponentIDUnmarshal(t *testing.T) {
	var id ComponentID
	err := id.UnmarshalString("otlp/metrics")
	require.NoError(t, err)
	assert.Equal(t, "otlp", id.Type)
	assert.Equal(t, "metrics", id.Name)

	err = id.UnmarshalString("")
	assert.Error(t, err)

	err = id.UnmarshalString("/name")
	assert.Error(t, err)
}

func TestKindString(t *testing.T) {
	assert.Equal(t, "receiver", KindReceiver.String())
	assert.Equal(t, "processor", KindProcessor.String())
	assert.Equal(t, "exporter", KindExporter.String())
	assert.Equal(t, "connector", KindConnector.String())
	assert.Equal(t, "extension", KindExtension.String())
	assert.Equal(t, "unknown", Kind(99).String())
}

// --- Pipeline Tests ---

func TestPipelineID(t *testing.T) {
	pid := PipelineID{Type: DataTypeTraces, Name: "main"}
	assert.Equal(t, "traces/main", pid.String())

	pid2 := PipelineID{Type: DataTypeMetrics}
	assert.Equal(t, "metrics", pid2.String())
}

func TestPipelineIDUnmarshal(t *testing.T) {
	var pid PipelineID
	err := pid.UnmarshalString("logs")
	require.NoError(t, err)
	assert.Equal(t, DataTypeLogs, pid.Type)

	err = pid.UnmarshalString("profiles/custom")
	require.NoError(t, err)
	assert.Equal(t, DataTypeProfiles, pid.Type)
	assert.Equal(t, "custom", pid.Name)

	err = pid.UnmarshalString("unknown")
	assert.Error(t, err)
}

func TestPipelineValidate(t *testing.T) {
	valid := Pipeline{
		Receivers: []ComponentID{{Type: "otlp"}},
		Exporters: []ComponentID{{Type: "otlp"}},
	}
	assert.NoError(t, valid.Validate())

	noReceiver := Pipeline{Exporters: []ComponentID{{Type: "otlp"}}}
	assert.Error(t, noReceiver.Validate())

	noExporter := Pipeline{Receivers: []ComponentID{{Type: "otlp"}}}
	assert.Error(t, noExporter.Validate())

	emptyReceiver := Pipeline{
		Receivers: []ComponentID{{}},
		Exporters: []ComponentID{{Type: "otlp"}},
	}
	assert.Error(t, emptyReceiver.Validate())
}

func TestPipelineConfigMarshalUnmarshal(t *testing.T) {
	cfg := PipelineConfig{
		Pipelines: map[PipelineID]Pipeline{
			{Type: DataTypeTraces}: {
				Receivers:  []ComponentID{{Type: "otlp"}},
				Processors: []ComponentID{{Type: "batch"}},
				Exporters:  []ComponentID{{Type: "otlp", Name: "out"}},
			},
		},
	}

	data, err := yaml.Marshal(cfg)
	require.NoError(t, err)

	var decoded PipelineConfig
	err = yaml.Unmarshal(data, &decoded)
	require.NoError(t, err)
	assert.Len(t, decoded.Pipelines, 1)
	pipeline := decoded.Pipelines[PipelineID{Type: DataTypeTraces}]
	assert.Len(t, pipeline.Receivers, 1)
	assert.Len(t, pipeline.Processors, 1)
	assert.Len(t, pipeline.Exporters, 1)
}

// --- Connector Tests ---

func TestSpanCountConnector(t *testing.T) {
	set := CreateSettings{
		ID:     ComponentID{Type: "span_count"},
		Logger: zap.NewNop(),
	}
	conn, err := NewSpanCountConnector(set)
	require.NoError(t, err)
	assert.Equal(t, DataTypeTraces, conn.InputDataType())
	assert.Equal(t, DataTypeMetrics, conn.OutputDataType())

	ctx := context.Background()
	require.NoError(t, conn.Start(ctx))
	assert.Error(t, conn.Start(ctx)) // already started

	sc := conn.(*spanCountConnector)
	sc.RecordSpan("svc", "server")
	sc.RecordSpan("svc", "server")
	counts := sc.GetCounts()
	assert.Equal(t, int64(2), counts["svc/server"])

	require.NoError(t, conn.Shutdown(ctx))
	require.NoError(t, conn.Shutdown(ctx)) // idempotent
}

func TestErrorCountConnector(t *testing.T) {
	set := CreateSettings{
		ID:     ComponentID{Type: "error_count"},
		Logger: zap.NewNop(),
	}
	conn, err := NewErrorCountConnector(set)
	require.NoError(t, err)

	ctx := context.Background()
	require.NoError(t, conn.Start(ctx))

	ec := conn.(*errorCountConnector)
	ec.RecordError("svc-a")
	ec.RecordError("svc-a")
	ec.RecordError("svc-b")
	errors := ec.GetErrors()
	assert.Equal(t, int64(2), errors["svc-a"])
	assert.Equal(t, int64(1), errors["svc-b"])

	require.NoError(t, conn.Shutdown(ctx))
}

func TestMetricToLogConnector(t *testing.T) {
	set := CreateSettings{
		ID:     ComponentID{Type: "metric_to_log"},
		Logger: zap.NewNop(),
	}
	conn, err := NewMetricToLogConnector(set, 100.0)
	require.NoError(t, err)
	assert.Equal(t, DataTypeMetrics, conn.InputDataType())
	assert.Equal(t, DataTypeLogs, conn.OutputDataType())

	ctx := context.Background()
	require.NoError(t, conn.Start(ctx))

	ml := conn.(*metricToLogConnector)
	alert := ml.EvaluateMetric("cpu", 50.0)
	assert.Nil(t, alert)

	alert = ml.EvaluateMetric("cpu", 150.0)
	require.NotNil(t, alert)
	assert.Equal(t, "cpu", alert.MetricName)
	assert.Equal(t, "WARNING", alert.Severity)

	alerts := ml.GetAlerts()
	assert.Len(t, alerts, 1)

	require.NoError(t, conn.Shutdown(ctx))
}

// --- Extension Tests ---

func TestHealthCheckExtension(t *testing.T) {
	set := CreateSettings{
		ID:     ComponentID{Type: "health_check"},
		Logger: zap.NewNop(),
	}
	ext, err := NewHealthCheckExtension(set, HealthCheckConfig{Endpoint: "127.0.0.1:0"})
	require.NoError(t, err)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	require.NoError(t, ext.Start(ctx))
	defer ext.Shutdown(ctx)

	he := ext.(*healthCheckExtension)
	assert.True(t, he.ready.Load())

	he.SetReady(false)
	assert.False(t, he.ready.Load())

	he.SetReady(true)
	assert.True(t, he.ready.Load())
}

func TestPprofExtension(t *testing.T) {
	set := CreateSettings{
		ID:     ComponentID{Type: "pprof"},
		Logger: zap.NewNop(),
	}
	ext, err := NewPprofExtension(set, PprofConfig{Endpoint: "127.0.0.1:0"})
	require.NoError(t, err)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	require.NoError(t, ext.Start(ctx))
	require.NoError(t, ext.Shutdown(ctx))
}

func TestZPagesExtension(t *testing.T) {
	set := CreateSettings{
		ID:     ComponentID{Type: "zpages"},
		Logger: zap.NewNop(),
	}
	ext, err := NewZPagesExtension(set, ZPagesConfig{Endpoint: "127.0.0.1:0"})
	require.NoError(t, err)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	require.NoError(t, ext.Start(ctx))
	require.NoError(t, ext.Shutdown(ctx))
}

// --- Config Tests ---

func TestConfigValidate(t *testing.T) {
	cfg := &Config{
		Receivers: ComponentMap{
			{Type: "otlp"}: map[string]interface{}{"endpoint": "0.0.0.0:4317"},
		},
		Exporters: ComponentMap{
			{Type: "otlp", Name: "out"}: map[string]interface{}{"endpoint": "backend:4317"},
		},
		Service: ServiceConfig{
			Pipelines: PipelineConfig{
				Pipelines: map[PipelineID]Pipeline{
					{Type: DataTypeTraces}: {
						Receivers: []ComponentID{{Type: "otlp"}},
						Exporters: []ComponentID{{Type: "otlp", Name: "out"}},
					},
				},
			},
		},
	}
	assert.NoError(t, cfg.Validate())

	// Missing receiver in config.
	cfg2 := &Config{
		Exporters: ComponentMap{
			{Type: "otlp"}: map[string]interface{}{},
		},
		Service: ServiceConfig{
			Pipelines: PipelineConfig{
				Pipelines: map[PipelineID]Pipeline{
					{Type: DataTypeTraces}: {
						Receivers: []ComponentID{{Type: "otlp"}},
						Exporters: []ComponentID{{Type: "otlp"}},
					},
				},
			},
		},
	}
	assert.Error(t, cfg2.Validate())
}

func TestConfigEnvExpansion(t *testing.T) {
	os.Setenv("TEST_COLLECTOR_ENDPOINT", "backend:4317")
	defer os.Unsetenv("TEST_COLLECTOR_ENDPOINT")

	raw := `
receivers:
  otlp:
    endpoint: 0.0.0.0:4317
exporters:
  otlp/out:
    endpoint: ${env:TEST_COLLECTOR_ENDPOINT}
service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [otlp/out]
`
	var cfg Config
	err := yaml.Unmarshal([]byte(raw), &cfg)
	require.NoError(t, err)

	exporterCfg, ok := cfg.Exporters[ComponentID{Type: "otlp", Name: "out"}].(map[string]interface{})
	require.True(t, ok)
	assert.Equal(t, "backend:4317", exporterCfg["endpoint"])
}

func TestConfigEnvExpansionWithDefault(t *testing.T) {
	os.Unsetenv("NONEXISTENT_VAR")
	raw := `
exporters:
  otlp:
    endpoint: ${env:NONEXISTENT_VAR:-default:4317}
`
	var cfg Config
	err := yaml.Unmarshal([]byte(raw), &cfg)
	require.NoError(t, err)

	exporterCfg, ok := cfg.Exporters[ComponentID{Type: "otlp"}].(map[string]interface{})
	require.True(t, ok)
	assert.Equal(t, "default:4317", exporterCfg["endpoint"])
}

func TestConfigRedactedString(t *testing.T) {
	cfg := &Config{
		Exporters: ComponentMap{
			{Type: "otlp"}: map[string]interface{}{
				"endpoint":  "backend:4317",
				"api_key":   "super-secret",
				"token":     "bearer-token",
				"password":  "hunter2",
				"client_secret": "shh",
			},
		},
	}
	str, err := cfg.RedactedString()
	require.NoError(t, err)
	assert.Contains(t, str, "[REDACTED]")
	assert.NotContains(t, str, "super-secret")
	assert.NotContains(t, str, "bearer-token")
	assert.NotContains(t, str, "hunter2")
	assert.NotContains(t, str, "shh")
	assert.Contains(t, str, "backend:4317")
}

// --- Provider Tests ---

func TestFileProvider(t *testing.T) {
	f, err := os.CreateTemp("", "config-*.yaml")
	require.NoError(t, err)
	defer os.Remove(f.Name())

	_, err = f.WriteString("receivers:\n  otlp:\n    endpoint: 0.0.0.0:4317\n")
	require.NoError(t, err)
	f.Close()

	provider := NewFileProvider(f.Name())
	ctx := context.Background()
	data, err := provider.Retrieve(ctx)
	require.NoError(t, err)
	assert.Contains(t, string(data), "otlp")
	assert.Equal(t, "file", provider.Scheme())
}

func TestEnvProvider(t *testing.T) {
	os.Setenv("TEST_CONFIG", "exporters:\n  otlp:\n    endpoint: localhost:4317")
	defer os.Unsetenv("TEST_CONFIG")

	provider := NewEnvProvider("TEST_CONFIG")
	ctx := context.Background()
	data, err := provider.Retrieve(ctx)
	require.NoError(t, err)
	assert.Contains(t, string(data), "otlp")
	assert.Equal(t, "env", provider.Scheme())
}

func TestEnvProviderMissing(t *testing.T) {
	provider := NewEnvProvider("MISSING_VAR_XYZ")
	ctx := context.Background()
	_, err := provider.Retrieve(ctx)
	assert.Error(t, err)
}

func TestMultiConfigProviderOverlay(t *testing.T) {
	base := map[string]interface{}{
		"receivers": map[string]interface{}{
			"otlp": map[string]interface{}{"endpoint": "0.0.0.0:4317"},
		},
	}
	overlay := map[string]interface{}{
		"receivers": map[string]interface{}{
			"otlp": map[string]interface{}{"endpoint": "0.0.0.0:4318"},
		},
	}

	baseYAML, _ := yaml.Marshal(base)
	overlayYAML, _ := yaml.Marshal(overlay)

	f1, _ := os.CreateTemp("", "base-*.yaml")
	f2, _ := os.CreateTemp("", "overlay-*.yaml")
	defer os.Remove(f1.Name())
	defer os.Remove(f2.Name())
	f1.Write(baseYAML)
	f2.Write(overlayYAML)
	f1.Close()
	f2.Close()

	multi := NewMultiConfigProvider(MergeStrategyOverlay,
		NewFileProvider(f1.Name()),
		NewFileProvider(f2.Name()),
	)
	ctx := context.Background()
	data, err := multi.Retrieve(ctx)
	require.NoError(t, err)

	var cfg map[string]interface{}
	err = yaml.Unmarshal(data, &cfg)
	require.NoError(t, err)

	receivers := cfg["receivers"].(map[string]interface{})
	otlp := receivers["otlp"].(map[string]interface{})
	assert.Equal(t, "0.0.0.0:4318", otlp["endpoint"])
}

func TestParseProviderURI(t *testing.T) {
	p, err := ParseProviderURI("file:///tmp/config.yaml")
	require.NoError(t, err)
	assert.Equal(t, "file", p.Scheme())

	p, err = ParseProviderURI("env://MY_CONFIG")
	require.NoError(t, err)
	assert.Equal(t, "env", p.Scheme())

	_, err = ParseProviderURI("unknown://host/config.yaml")
	assert.Error(t, err)
}

// --- Security Tests ---

func TestTLSConfigValidate(t *testing.T) {
	valid := &TLSConfig{CertFile: "cert.pem", KeyFile: "key.pem"}
	assert.NoError(t, valid.Validate())

	insecure := &TLSConfig{Insecure: true}
	assert.NoError(t, insecure.Validate())

	missingKey := &TLSConfig{CertFile: "cert.pem"}
	assert.Error(t, missingKey.Validate())
}

func generateTestCert(t *testing.T) (certFile, keyFile string) {
	t.Helper()
	priv, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)

	template := x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject: pkix.Name{
			Organization: []string{"Test"},
		},
		NotBefore:             time.Now(),
		NotAfter:              time.Now().Add(time.Hour),
		KeyUsage:              x509.KeyUsageKeyEncipherment | x509.KeyUsageDigitalSignature,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
		BasicConstraintsValid: true,
		IPAddresses:           []net.IP{net.ParseIP("127.0.0.1")},
	}

	certDER, err := x509.CreateCertificate(rand.Reader, &template, &template, &priv.PublicKey, priv)
	require.NoError(t, err)

	certF, err := os.CreateTemp("", "cert-*.pem")
	require.NoError(t, err)
	defer certF.Close()
	require.NoError(t, pem.Encode(certF, &pem.Block{Type: "CERTIFICATE", Bytes: certDER}))

	keyF, err := os.CreateTemp("", "key-*.pem")
	require.NoError(t, err)
	defer keyF.Close()
	require.NoError(t, pem.Encode(keyF, &pem.Block{Type: "RSA PRIVATE KEY", Bytes: x509.MarshalPKCS1PrivateKey(priv)}))

	return certF.Name(), keyF.Name()
}

func TestTLSConfigLoad(t *testing.T) {
	certFile, keyFile := generateTestCert(t)
	defer os.Remove(certFile)
	defer os.Remove(keyFile)

	cfg := &TLSConfig{
		CertFile: certFile,
		KeyFile:  keyFile,
	}
	tlsCfg, err := cfg.LoadTLSConfig()
	require.NoError(t, err)
	assert.NotNil(t, tlsCfg)
	assert.Len(t, tlsCfg.Certificates, 1)
}

func TestAutoReloadingTLSConfig(t *testing.T) {
	certFile, keyFile := generateTestCert(t)
	defer os.Remove(certFile)
	defer os.Remove(keyFile)

	cfg := TLSConfig{
		CertFile:       certFile,
		KeyFile:        keyFile,
		ReloadInterval: 100 * time.Millisecond,
	}
	arc, err := NewAutoReloadingTLSConfig(cfg)
	require.NoError(t, err)
	defer arc.Stop()

	assert.NotNil(t, arc.GetConfig())

	// Wait for a reload cycle.
	time.Sleep(150 * time.Millisecond)
	assert.NotNil(t, arc.GetConfig())
}

func TestOIDCAuthExtension(t *testing.T) {
	set := CreateSettings{ID: ComponentID{Type: "oidc"}, Logger: zap.NewNop()}
	ext, err := NewOIDCAuthExtension(set, OIDCAuthConfig{IssuerURL: "https://issuer.example.com", Audience: "aud"})
	require.NoError(t, err)

	ctx := context.Background()
	require.NoError(t, ext.Start(ctx))

	oe := ext.(*oidcAuthExtension)
	assert.Error(t, oe.ValidateToken(""))
	assert.Error(t, oe.ValidateToken("invalid"))
	assert.NoError(t, oe.ValidateToken("eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.dozjgNryP4J3jVmNHl0w5N_XgL0n3I9PlFUP0THsR8U"))

	require.NoError(t, ext.Shutdown(ctx))
}

func TestOAuth2ClientExtension(t *testing.T) {
	set := CreateSettings{ID: ComponentID{Type: "oauth2"}, Logger: zap.NewNop()}
	ext, err := NewOAuth2ClientExtension(set, OAuth2ClientConfig{
		ClientID:     "id",
		ClientSecret: "secret",
		TokenURL:     "https://auth.example.com/token",
		Scopes:       []string{"read", "write"},
	})
	require.NoError(t, err)

	ctx := context.Background()
	require.NoError(t, ext.Start(ctx))

	oe := ext.(*oauth2ClientExtension)
	assert.Equal(t, "", oe.GetAccessToken())

	oe.SetAccessToken("token123", time.Hour)
	assert.Equal(t, "token123", oe.GetAccessToken())

	require.NoError(t, ext.Shutdown(ctx))
}

// --- Command Tests ---

func TestBuildInfoCommand(t *testing.T) {
	cmd := &BuildInfoCommand{BuildInfo: DefaultBuildInfo()}
	assert.NoError(t, cmd.Run())
}

func TestComponentsCommand(t *testing.T) {
	registry := NewComponentRegistry()
	registry.RegisterExtension(&mockExtensionFactory{typ: "health_check"})
	registry.RegisterExtension(&mockExtensionFactory{typ: "pprof"})
	registry.RegisterConnector(&mockConnectorFactory{typ: "span_count"})

	cmd := registry.ToCommand()
	assert.NoError(t, cmd.Run())
}

func TestValidateCommand(t *testing.T) {
	configContent := `
receivers:
  otlp:
    endpoint: 0.0.0.0:4317
exporters:
  otlp:
    endpoint: backend:4317
service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [otlp]
`
	f, _ := os.CreateTemp("", "valid-*.yaml")
	defer os.Remove(f.Name())
	f.WriteString(configContent)
	f.Close()

	cmd := &ValidateCommand{Provider: NewFileProvider(f.Name())}
	assert.NoError(t, cmd.Run())
}

func TestValidateCommandInvalid(t *testing.T) {
	configContent := `
service:
  pipelines:
    traces:
      receivers: []
      exporters: [otlp]
`
	f, _ := os.CreateTemp("", "invalid-*.yaml")
	defer os.Remove(f.Name())
	f.WriteString(configContent)
	f.Close()

	cmd := &ValidateCommand{Provider: NewFileProvider(f.Name())}
	assert.Error(t, cmd.Run())
}

func TestPrintConfigCommand(t *testing.T) {
	configContent := `
receivers:
  otlp:
    endpoint: 0.0.0.0:4317
exporters:
  otlp:
    endpoint: backend:4317
    api_key: secret123
service:
  pipelines:
    traces:
      receivers: [otlp]
      exporters: [otlp]
`
	f, _ := os.CreateTemp("", "print-*.yaml")
	defer os.Remove(f.Name())
	f.WriteString(configContent)
	f.Close()

	cmd := &PrintConfigCommand{Provider: NewFileProvider(f.Name())}
	assert.NoError(t, cmd.Run())

	cmdRedacted := &PrintConfigCommand{Provider: NewFileProvider(f.Name()), Redacted: true}
	assert.NoError(t, cmdRedacted.Run())

	cmdJSON := &PrintConfigCommand{Provider: NewFileProvider(f.Name()), JSON: true}
	assert.NoError(t, cmdJSON.Run())
}

// --- Builder Tests ---

func TestCollectorBuilder(t *testing.T) {
	registry := NewComponentRegistry()
	registry.RegisterExtension(&mockExtensionFactory{typ: "health_check"})
	registry.RegisterConnector(&mockConnectorFactory{typ: "span_count"})

	cfg := &Config{
		Receivers: ComponentMap{
			{Type: "otlp"}: map[string]interface{}{"endpoint": "0.0.0.0:4317"},
		},
		Exporters: ComponentMap{
			{Type: "otlp"}: map[string]interface{}{"endpoint": "backend:4317"},
		},
		Connectors: ComponentMap{
			{Type: "span_count"}: map[string]interface{}{},
		},
		Extensions: ComponentMap{
			{Type: "health_check"}: map[string]interface{}{"endpoint": "127.0.0.1:0"},
		},
		Service: ServiceConfig{
			Pipelines: PipelineConfig{
				Pipelines: map[PipelineID]Pipeline{
					{Type: DataTypeTraces}: {
						Receivers:  []ComponentID{{Type: "otlp"}},
						Exporters:  []ComponentID{{Type: "otlp"}},
						Connectors: []ComponentID{{Type: "span_count"}},
					},
				},
			},
			Extensions: []ComponentID{{Type: "health_check"}},
		},
	}

	builder := NewCollectorBuilder(registry, zap.NewNop(), DefaultBuildInfo())
	col, err := builder.Build(cfg)
	require.NoError(t, err)
	assert.NotNil(t, col)
	assert.Len(t, col.Extensions, 1)
	assert.Len(t, col.Connectors, 1)
	assert.Len(t, col.Pipelines, 1)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	require.NoError(t, col.Start(ctx))
	require.NoError(t, col.Shutdown(ctx))
}

func TestCollectorBuilderMissingFactory(t *testing.T) {
	registry := NewComponentRegistry()
	cfg := &Config{
		Extensions: ComponentMap{
			{Type: "unknown"}: map[string]interface{}{},
		},
		Service: ServiceConfig{
			Pipelines: PipelineConfig{},
			Extensions: []ComponentID{{Type: "unknown"}},
		},
	}

	builder := NewCollectorBuilder(registry, zap.NewNop(), DefaultBuildInfo())
	_, err := builder.Build(cfg)
	assert.Error(t, err)
}

func TestCollectorPipelineIDs(t *testing.T) {
	col := &Collector{
		Pipelines: map[PipelineID]*PipelineInstance{
			{Type: DataTypeMetrics}: {ID: PipelineID{Type: DataTypeMetrics}},
			{Type: DataTypeTraces}:  {ID: PipelineID{Type: DataTypeTraces}},
		},
	}
	ids := col.PipelineIDs()
	require.Len(t, ids, 2)
	assert.Equal(t, DataTypeMetrics, ids[0].Type)
	assert.Equal(t, DataTypeTraces, ids[1].Type)
}

// --- Mock Factories ---

type mockExtensionFactory struct {
	typ string
}

func (m *mockExtensionFactory) Type() string { return m.typ }
func (m *mockExtensionFactory) CreateExtension(ctx context.Context, set CreateSettings, cfg interface{}) (Extension, error) {
	switch m.typ {
	case "health_check":
		return NewHealthCheckExtension(set, HealthCheckConfig{Endpoint: "127.0.0.1:0"})
	case "pprof":
		return NewPprofExtension(set, PprofConfig{Endpoint: "127.0.0.1:0"})
	case "zpages":
		return NewZPagesExtension(set, ZPagesConfig{Endpoint: "127.0.0.1:0"})
	case "oidc":
		return NewOIDCAuthExtension(set, OIDCAuthConfig{})
	case "oauth2":
		return NewOAuth2ClientExtension(set, OAuth2ClientConfig{})
	default:
		return &stubComponent{id: set.ID, logger: set.Logger, kind: "extension"}, nil
	}
}

type mockConnectorFactory struct {
	typ string
}

func (m *mockConnectorFactory) Type() string { return m.typ }
func (m *mockConnectorFactory) CreateDefaultConfig() interface{} { return nil }
func (m *mockConnectorFactory) CreateTracesToMetrics(ctx context.Context, set CreateSettings, cfg interface{}) (TracesToMetrics, error) {
	return NewSpanCountConnector(set)
}
func (m *mockConnectorFactory) CreateTracesToLogs(ctx context.Context, set CreateSettings, cfg interface{}) (TracesToLogs, error) {
	return nil, fmt.Errorf("not implemented")
}
func (m *mockConnectorFactory) CreateMetricsToLogs(ctx context.Context, set CreateSettings, cfg interface{}) (MetricsToLogs, error) {
	return nil, fmt.Errorf("not implemented")
}
func (m *mockConnectorFactory) CreateMetricsToMetrics(ctx context.Context, set CreateSettings, cfg interface{}) (MetricsToMetrics, error) {
	return nil, fmt.Errorf("not implemented")
}

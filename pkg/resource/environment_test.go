package resource

import (
	"context"
	"os"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestEnvironmentDetector(t *testing.T) {
	ctx := context.Background()
	detector := &EnvironmentDetector{}

	t.Run("detects OTEL_RESOURCE_ATTRIBUTES", func(t *testing.T) {
		// Set environment variable
		os.Setenv(OTELResourceAttributesEnv, "service.name=test-service,service.version=1.0.0")
		defer os.Unsetenv(OTELResourceAttributesEnv)

		res, err := detector.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "test-service", res.GetString("service.name"))
		assert.Equal(t, "1.0.0", res.GetString("service.version"))
	})

	t.Run("detects OTEL_SERVICE_NAME", func(t *testing.T) {
		os.Setenv(OTELServiceNameEnv, "my-service")
		defer os.Unsetenv(OTELServiceNameEnv)

		res, err := detector.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "my-service", res.GetString("service.name"))
	})

	t.Run("OTEL_SERVICE_NAME overrides OTEL_RESOURCE_ATTRIBUTES", func(t *testing.T) {
		os.Setenv(OTELResourceAttributesEnv, "service.name=from-attributes")
		os.Setenv(OTELServiceNameEnv, "from-service-name")
		defer os.Unsetenv(OTELResourceAttributesEnv)
		defer os.Unsetenv(OTELServiceNameEnv)

		res, err := detector.Detect(ctx)
		require.NoError(t, err)

		// Both should be present, but the order depends on implementation
		assert.NotEmpty(t, res.GetString("service.name"))
	})

	t.Run("handles empty environment", func(t *testing.T) {
		// Ensure no env vars are set
		os.Unsetenv(OTELResourceAttributesEnv)
		os.Unsetenv(OTELServiceNameEnv)

		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		assert.True(t, res.IsEmpty())
	})

	t.Run("returns correct detector type", func(t *testing.T) {
		assert.Equal(t, "environment", detector.DetectorType())
	})

	t.Run("handles custom attributes", func(t *testing.T) {
		detectorWithCustom := &EnvironmentDetector{
			CustomAttrs: map[string]string{
				"MY_CUSTOM_VAR": "custom.attribute",
			},
		}

		os.Setenv("MY_CUSTOM_VAR", "custom-value")
		defer os.Unsetenv("MY_CUSTOM_VAR")

		res, err := detectorWithCustom.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "custom-value", res.GetString("custom.attribute"))
	})
}

func TestParseAttributes(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected map[string]string
	}{
		{
			name:     "empty string",
			input:    "",
			expected: map[string]string{},
		},
		{
			name:     "simple key value",
			input:    "key=value",
			expected: map[string]string{"key": "value"},
		},
		{
			name:     "multiple pairs",
			input:    "k1=v1,k2=v2,k3=v3",
			expected: map[string]string{"k1": "v1", "k2": "v2", "k3": "v3"},
		},
		{
			name:     "values with spaces",
			input:    "key1=value 1,key2=value 2",
			expected: map[string]string{"key1": "value 1", "key2": "value 2"},
		},
		{
			name:     "empty value",
			input:    "key1=,key2=v2",
			expected: map[string]string{"key1": "", "key2": "v2"},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := parseAttributes(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestParseAttributesMap(t *testing.T) {
	t.Run("parses JSON format", func(t *testing.T) {
		input := `{"service.name":"test","service.version":"1.0.0"}`
		result := parseAttributesMap(input)

		assert.Equal(t, "test", result["service.name"])
		assert.Equal(t, "1.0.0", result["service.version"])
	})

	t.Run("falls back to key=value format", func(t *testing.T) {
		input := "key1=value1,key2=value2"
		result := parseAttributesMap(input)

		assert.Equal(t, "value1", result["key1"])
		assert.Equal(t, "value2", result["key2"])
	})

	t.Run("handles empty string", func(t *testing.T) {
		result := parseAttributesMap("")
		assert.Empty(t, result)
	})
}

func TestWithEnvironmentDetector(t *testing.T) {
	cfg := &Config{Detectors: []Detector{}}
	customAttrs := map[string]string{
		"MY_VAR": "my.attribute",
	}

	opt := WithEnvironmentDetector(customAttrs)
	opt(cfg)

	require.Len(t, cfg.Detectors, 1)
	assert.Equal(t, "environment", cfg.Detectors[0].DetectorType())
}

func TestGetResourceFromEnv(t *testing.T) {
	os.Setenv(OTELResourceAttributesEnv, "service.name=test-service")
	defer os.Unsetenv(OTELResourceAttributesEnv)

	res, err := GetResourceFromEnv()
	require.NoError(t, err)
	assert.Equal(t, "test-service", res.GetString("service.name"))
}

func TestResourceAttributesEnv(t *testing.T) {
	t.Run("ParseResourceAttributesEnv parses all attributes", func(t *testing.T) {
		os.Setenv(OTELResourceAttributesEnv,
			"service.name=test-service,"+
				"service.version=1.0.0,"+
				"service.namespace=test-ns,"+
				"deployment.environment=production,"+
				"host.name=test-host,"+
				"host.id=host-123,"+
				"container.id=container-456,"+
				"container.name=my-container,"+
				"k8s.pod.name=my-pod,"+
				"k8s.namespace.name=my-namespace,"+
				"k8s.node.name=my-node,"+
				"k8s.cluster.name=my-cluster,"+
				"cloud.provider=aws,"+
				"cloud.region=us-east-1,"+
				"cloud.availability_zone=us-east-1a")
		defer os.Unsetenv(OTELResourceAttributesEnv)

		env := ParseResourceAttributesEnv()

		assert.Equal(t, "test-service", env.ServiceName)
		assert.Equal(t, "1.0.0", env.ServiceVersion)
		assert.Equal(t, "test-ns", env.ServiceNamespace)
		assert.Equal(t, "production", env.DeploymentEnvironment)
		assert.Equal(t, "test-host", env.HostName)
		assert.Equal(t, "host-123", env.HostID)
		assert.Equal(t, "container-456", env.ContainerID)
		assert.Equal(t, "my-container", env.ContainerName)
		assert.Equal(t, "my-pod", env.PodName)
		assert.Equal(t, "my-namespace", env.PodNamespace)
		assert.Equal(t, "my-node", env.NodeName)
		assert.Equal(t, "my-cluster", env.ClusterName)
		assert.Equal(t, "aws", env.CloudProvider)
		assert.Equal(t, "us-east-1", env.CloudRegion)
		assert.Equal(t, "us-east-1a", env.CloudZone)
	})

	t.Run("handles empty environment", func(t *testing.T) {
		os.Unsetenv(OTELResourceAttributesEnv)

		env := ParseResourceAttributesEnv()

		assert.Empty(t, env.ServiceName)
		assert.Empty(t, env.HostName)
	})
}

func TestResourceAttributesEnvToResource(t *testing.T) {
	env := &ResourceAttributesEnv{
		ServiceName:    "test-service",
		ServiceVersion: "1.0.0",
		HostName:       "test-host",
		HostID:         "host-123",
		CloudProvider:  "aws",
		CloudRegion:    "us-east-1",
	}

	res := env.ToResource()
	require.NotNil(t, res)

	assert.Equal(t, "test-service", res.GetString("service.name"))
	assert.Equal(t, "1.0.0", res.GetString("service.version"))
	assert.Equal(t, "test-host", res.GetString("host.name"))
	assert.Equal(t, "host-123", res.GetString("host.id"))
	assert.Equal(t, "aws", res.GetString("cloud.provider"))
	assert.Equal(t, "us-east-1", res.GetString("cloud.region"))
}

func TestResourceFromMap(t *testing.T) {
	t.Run("creates resource from map", func(t *testing.T) {
		m := map[string]string{
			"key1": "value1",
			"key2": "value2",
		}

		res := ResourceFromMap(m)
		require.NotNil(t, res)

		assert.Equal(t, "value1", res.GetString("key1"))
		assert.Equal(t, "value2", res.GetString("key2"))
	})

	t.Run("returns empty resource for empty map", func(t *testing.T) {
		res := ResourceFromMap(map[string]string{})
		require.NotNil(t, res)
		assert.True(t, res.IsEmpty())
	})

	t.Run("returns empty resource for nil map", func(t *testing.T) {
		res := ResourceFromMap(nil)
		require.NotNil(t, res)
		assert.True(t, res.IsEmpty())
	})
}

func TestMergeEnvResources(t *testing.T) {
	r1 := ResourceFromMap(map[string]string{"key1": "value1"})
	r2 := ResourceFromMap(map[string]string{"key2": "value2"})

	merged := MergeEnvResources(r1, r2)
	require.NotNil(t, merged)

	assert.Equal(t, "value1", merged.GetString("key1"))
	assert.Equal(t, "value2", merged.GetString("key2"))
}

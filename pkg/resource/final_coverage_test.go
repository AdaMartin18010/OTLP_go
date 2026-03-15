package resource

import (
	"context"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Additional tests to reach 80% coverage

func TestEmptyResource(t *testing.T) {
	r := Empty()
	require.NotNil(t, r)
	assert.True(t, r.IsEmpty())
	assert.Equal(t, 0, r.AttributeCount())
}

func TestDefaultResourceFunc(t *testing.T) {
	r := Default()
	require.NotNil(t, r)
	
	// Check SDK attributes
	assert.Equal(t, "OTLP_go", r.GetString("telemetry.sdk.name"))
	assert.Equal(t, "go", r.GetString("telemetry.sdk.language"))
	assert.NotEmpty(t, r.GetString("telemetry.sdk.version"))
}

func TestMergeLastNil(t *testing.T) {
	r1 := types.NewResource(types.NewAttribute("key", "value"))
	merged := Merge(r1, nil)
	assert.Equal(t, "value", merged.GetString("key"))
}

func TestMergeFirstNil(t *testing.T) {
	r2 := types.NewResource(types.NewAttribute("key", "value"))
	merged := Merge(nil, r2)
	assert.Equal(t, "value", merged.GetString("key"))
}



func TestNewWithNoDetectors(t *testing.T) {
	ctx := context.Background()
	
	// Create with empty detectors list - should use defaults
	res, err := New(ctx, WithDetectors())
	require.NoError(t, err)
	require.NotNil(t, res)
	
	// Should have SDK attributes
	assert.NotEmpty(t, res.GetString("telemetry.sdk.name"))
}

func TestNewResourceWithDefaultAttrsOverride(t *testing.T) {
	ctx := context.Background()
	
	customDetector := DetectorFunc{
		Type: "custom",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(
				types.NewAttribute("custom", "from-detector"),
			), nil
		},
	}
	
	res, err := New(ctx,
		WithDetectors(customDetector),
		WithDefaultAttributes(map[string]interface{}{
			"default": "from-default",
		}),
	)
	require.NoError(t, err)
	require.NotNil(t, res)
	
	// Both should be present
	assert.Equal(t, "from-detector", res.GetString("custom"))
	assert.Equal(t, "from-default", res.GetString("default"))
}

func TestCloudProviderValues(t *testing.T) {
	assert.Equal(t, CloudProvider(0), CloudProviderUnknown)
	assert.Equal(t, CloudProvider(1), CloudProviderAWS)
	assert.Equal(t, CloudProvider(2), CloudProviderGCP)
	assert.Equal(t, CloudProvider(3), CloudProviderAzure)
}

func TestCloudProviderStringAllTypes(t *testing.T) {
	tests := []struct {
		provider CloudProvider
		expected string
	}{
		{CloudProviderUnknown, "unknown"},
		{CloudProviderAWS, "aws"},
		{CloudProviderGCP, "gcp"},
		{CloudProviderAzure, "azure"},
	}
	
	for _, tc := range tests {
		t.Run(tc.expected, func(t *testing.T) {
			assert.Equal(t, tc.expected, tc.provider.String())
		})
	}
}

func TestCloudProviderDetectorConstructors(t *testing.T) {
	tests := []string{"aws", "gcp", "azure"}
	
	for _, provider := range tests {
		t.Run(provider, func(t *testing.T) {
			detector := NewCloudProviderDetector(provider)
			require.NotNil(t, detector)
			assert.Equal(t, "cloud", detector.DetectorType())
			assert.Equal(t, provider, detector.provider)
		})
	}
}

func TestWithCloudProviderOption(t *testing.T) {
	tests := []struct {
		name     string
		provider string
	}{
		{"aws", "aws"},
		{"gcp", "gcp"},
		{"azure", "azure"},
	}
	
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			cfg := &Config{Detectors: []Detector{}}
			opt := WithCloudProvider(tc.provider)
			opt(cfg)
			
			found := false
			for _, d := range cfg.Detectors {
				if d.DetectorType() == "cloud" {
					found = true
					break
				}
			}
			assert.True(t, found)
		})
	}
}

func TestResourceAttributesEnvAllFields(t *testing.T) {
	env := &ResourceAttributesEnv{
		ServiceName:           "my-service",
		ServiceVersion:        "1.0.0",
		ServiceNamespace:      "my-namespace",
		DeploymentEnvironment: "production",
		HostName:              "my-host",
		HostID:                "host-123",
		ContainerID:           "container-456",
		ContainerName:         "my-container",
		PodName:               "my-pod",
		PodNamespace:          "my-pod-ns",
		NodeName:              "my-node",
		ClusterName:           "my-cluster",
		CloudProvider:         "aws",
		CloudRegion:           "us-west-2",
		CloudZone:             "us-west-2a",
	}
	
	res := env.ToResource()
	require.NotNil(t, res)
	
	assert.Equal(t, "my-service", res.GetString("service.name"))
	assert.Equal(t, "1.0.0", res.GetString("service.version"))
	assert.Equal(t, "my-namespace", res.GetString("service.namespace"))
	assert.Equal(t, "production", res.GetString("deployment.environment"))
	assert.Equal(t, "my-host", res.GetString("host.name"))
	assert.Equal(t, "host-123", res.GetString("host.id"))
	assert.Equal(t, "container-456", res.GetString("container.id"))
	assert.Equal(t, "my-container", res.GetString("container.name"))
	assert.Equal(t, "my-pod", res.GetString("k8s.pod.name"))
	assert.Equal(t, "my-pod-ns", res.GetString("k8s.namespace.name"))
	assert.Equal(t, "my-node", res.GetString("k8s.node.name"))
	assert.Equal(t, "my-cluster", res.GetString("k8s.cluster.name"))
	assert.Equal(t, "aws", res.GetString("cloud.provider"))
	assert.Equal(t, "us-west-2", res.GetString("cloud.region"))
	assert.Equal(t, "us-west-2a", res.GetString("cloud.availability_zone"))
}

func TestParseAttributesMapInvalidCases(t *testing.T) {
	// Test with invalid JSON that looks like it could be JSON
	input := "{not valid json}"
	result := parseAttributesMap(input)
	// Should fall back to key=value parsing
	// Since it doesn't contain "=", it should be empty
	assert.Empty(t, result)
}

func TestDetectorFuncAllScenarios(t *testing.T) {
	ctx := context.Background()
	
	t.Run("returns resource", func(t *testing.T) {
		detector := DetectorFunc{
			Type: "success",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(types.NewAttribute("key", "value")), nil
			},
		}
		
		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, "value", res.GetString("key"))
		assert.Equal(t, "success", detector.DetectorType())
	})
	
	t.Run("returns error", func(t *testing.T) {
		detector := DetectorFunc{
			Type: "error",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, assert.AnError
			},
		}
		
		res, err := detector.Detect(ctx)
		assert.Error(t, err)
		assert.Nil(t, res)
	})
	
	t.Run("returns nil resource no error", func(t *testing.T) {
		detector := DetectorFunc{
			Type: "nil",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, nil
			},
		}
		
		res, err := detector.Detect(ctx)
		assert.NoError(t, err)
		assert.Nil(t, res)
	})
}

func TestCompositeDetectorAllNil(t *testing.T) {
	ctx := context.Background()
	
	d1 := DetectorFunc{
		Type: "nil1",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, nil
		},
	}
	d2 := DetectorFunc{
		Type: "nil2",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, nil
		},
	}
	
	composite := NewCompositeDetector(MergeLastWins, d1, d2)
	res, err := composite.Detect(ctx)
	require.NoError(t, err)
	assert.True(t, res.IsEmpty())
}

func TestChainedDetectorMultipleScenarios(t *testing.T) {
	ctx := context.Background()
	
	t.Run("all return error", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "err1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, assert.AnError
			},
		}
		d2 := DetectorFunc{
			Type: "err2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, assert.AnError
			},
		}
		
		chained := NewChainedDetector(d1, d2)
		_, err := chained.Detect(ctx)
		assert.Error(t, err)
	})
	
	t.Run("last succeeds", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "err",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, assert.AnError
			},
		}
		d2 := DetectorFunc{
			Type: "success",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(types.NewAttribute("key", "value")), nil
			},
		}
		
		chained := NewChainedDetector(d1, d2)
		res, err := chained.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, "value", res.GetString("key"))
	})
}

func TestDetectAllVariations(t *testing.T) {
	ctx := context.Background()
	
	t.Run("single detector", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "single",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(types.NewAttribute("k", "v")), nil
			},
		}
		
		results := DetectAll(ctx, d1)
		require.Len(t, results, 1)
		assert.Equal(t, "v", results[0].Resource.GetString("k"))
	})
	
	t.Run("no detectors", func(t *testing.T) {
		results := DetectAll(ctx)
		assert.Empty(t, results)
	})
}

func TestFilterDetectorsMore(t *testing.T) {
	t.Run("empty", func(t *testing.T) {
		result := FilterDetectors([]DetectorResult{})
		assert.Empty(t, result)
	})
	
	t.Run("all nil resources", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: nil, Error: nil},
			{Resource: nil, Error: assert.AnError},
		}
		filtered := FilterDetectors(results)
		assert.Empty(t, filtered)
	})
}

func TestMergeResultsMore(t *testing.T) {
	t.Run("empty list", func(t *testing.T) {
		res := MergeResults([]DetectorResult{})
		assert.True(t, res.IsEmpty())
	})
	
	t.Run("nil input", func(t *testing.T) {
		res := MergeResults(nil)
		assert.True(t, res.IsEmpty())
	})
}

func TestAsyncDetectorEmpty(t *testing.T) {
	ctx := context.Background()
	
	async := NewAsyncDetector()
	res, err := async.Detect(ctx)
	require.NoError(t, err)
	assert.True(t, res.IsEmpty())
}



func TestDetectParallelMultiple(t *testing.T) {
	ctx := context.Background()
	
	d1 := DetectorFunc{
		Type: "d1",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("k1", "v1")), nil
		},
	}
	d2 := DetectorFunc{
		Type: "d2",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("k2", "v2")), nil
		},
	}
	
	results := DetectParallel(ctx, d1, d2)
	require.Len(t, results, 2)
	
	// Both should be successful
	for _, r := range results {
		assert.NoError(t, r.Error)
		assert.NotNil(t, r.Resource)
	}
}

func TestWithFromEnvDuplicate(t *testing.T) {
	// Test that WithFromEnv doesn't add duplicate
	cfg := &Config{
		Detectors: []Detector{&EnvironmentDetector{}},
	}
	
	WithFromEnv()(cfg)
	
	// Should still only have one environment detector
	count := 0
	for _, d := range cfg.Detectors {
		if d.DetectorType() == "environment" {
			count++
		}
	}
	assert.Equal(t, 1, count)
}

func TestWithHostDuplicate(t *testing.T) {
	cfg := &Config{
		Detectors: []Detector{&HostDetector{}},
	}
	
	WithHost()(cfg)
	
	count := 0
	for _, d := range cfg.Detectors {
		if d.DetectorType() == "host" {
			count++
		}
	}
	assert.Equal(t, 1, count)
}

func TestWithProcessDuplicate(t *testing.T) {
	cfg := &Config{
		Detectors: []Detector{&ProcessDetector{}},
	}
	
	WithProcess()(cfg)
	
	count := 0
	for _, d := range cfg.Detectors {
		if d.DetectorType() == "process" {
			count++
		}
	}
	assert.Equal(t, 1, count)
}

func TestWithContainerDuplicate(t *testing.T) {
	cfg := &Config{
		Detectors: []Detector{&ContainerDetector{}},
	}
	
	WithContainer()(cfg)
	
	count := 0
	for _, d := range cfg.Detectors {
		if d.DetectorType() == "container" {
			count++
		}
	}
	assert.Equal(t, 1, count)
}

func TestWithOSDuplicate(t *testing.T) {
	cfg := &Config{
		Detectors: []Detector{&OSDetector{}},
	}
	
	WithOS()(cfg)
	
	count := 0
	for _, d := range cfg.Detectors {
		if d.DetectorType() == "os" {
			count++
		}
	}
	assert.Equal(t, 1, count)
}

func TestMustNewDoesNotPanic(t *testing.T) {
	ctx := context.Background()
	
	// This should not panic
	assert.NotPanics(t, func() {
		r := MustNew(ctx)
		assert.NotNil(t, r)
	})
}

func TestResourceFromMapCases(t *testing.T) {
	t.Run("nil map", func(t *testing.T) {
		res := ResourceFromMap(nil)
		assert.NotNil(t, res)
		assert.True(t, res.IsEmpty())
	})
	
	t.Run("empty map", func(t *testing.T) {
		res := ResourceFromMap(map[string]string{})
		assert.NotNil(t, res)
		assert.True(t, res.IsEmpty())
	})
	
	t.Run("multiple entries", func(t *testing.T) {
		m := map[string]string{
			"k1": "v1",
			"k2": "v2",
			"k3": "v3",
		}
		res := ResourceFromMap(m)
		assert.Equal(t, "v1", res.GetString("k1"))
		assert.Equal(t, "v2", res.GetString("k2"))
		assert.Equal(t, "v3", res.GetString("k3"))
	})
}



func TestEnvironmentDetectorEmptyCustomAttrs(t *testing.T) {
	detector := &EnvironmentDetector{
		CustomAttrs: map[string]string{},
	}
	
	ctx := context.Background()
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestHostInfoToResourceAllFields(t *testing.T) {
	info := &HostInfo{
		Hostname:    "host1",
		OS:          "linux",
		OSVersion:   "20.04",
		Arch:        "amd64",
		HostID:      "id123",
		NumCPU:      8,
		Container:   true,
		ContainerID: "container123",
	}
	
	res := info.ToResource()
	
	assert.Equal(t, "host1", res.GetString("host.name"))
	assert.Equal(t, "linux", res.GetString("os.type"))
	assert.Equal(t, "20.04", res.GetString("os.version"))
	assert.Equal(t, "amd64", res.GetString("host.arch"))
	assert.Equal(t, "id123", res.GetString("host.id"))
	assert.Equal(t, "container123", res.GetString("container.id"))
}

func TestHostInfoToResourceNotContainer(t *testing.T) {
	info := &HostInfo{
		Hostname:    "host1",
		OS:          "linux",
		Arch:        "amd64",
		Container:   false,
		ContainerID: "",
	}
	
	res := info.ToResource()
	
	// Should not have container.id
	_, hasContainerID := res.Get("container.id")
	assert.False(t, hasContainerID)
}

func TestCachingDetectorError(t *testing.T) {
	ctx := context.Background()
	
	callCount := 0
	inner := DetectorFunc{
		Type: "error",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			callCount++
			return nil, assert.AnError
		},
	}
	
	caching := NewCachingDetector(inner)
	
	// First call - should call inner
	_, err1 := caching.Detect(ctx)
	assert.Error(t, err1)
	assert.Equal(t, 1, callCount)
	
	// Second call - should use cached error
	_, err2 := caching.Detect(ctx)
	assert.Error(t, err2)
	assert.Equal(t, 1, callCount) // Should not increase
}

func TestConditionalDetectorTypes(t *testing.T) {
	inner := DetectorFunc{
		Type: "inner",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.EmptyResource(), nil
		},
	}
	
	conditional := NewConditionalDetector(func() bool { return true }, inner)
	assert.Equal(t, "conditional(inner)", conditional.DetectorType())
}

func TestDetectCloudProviderWhenNotOnCloud(t *testing.T) {
	// When not on any cloud, should return Unknown
	provider := DetectCloudProvider()
	// Result depends on environment, but should be a valid value
	assert.True(t, provider >= CloudProviderUnknown && provider <= CloudProviderAzure)
}

func TestResourceDetectorWithHostType(t *testing.T) {
	ctx := context.Background()
	detector := &HostDetector{IncludeHostType: true}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
	
	// May or may not have host.type depending on environment
	// Just ensure it doesn't error
}

func TestResourceDetectorWithHostID(t *testing.T) {
	ctx := context.Background()
	detector := &HostDetector{IncludeHostID: true}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
	
	// May or may not have host.id depending on environment
	// Just ensure it doesn't error
}

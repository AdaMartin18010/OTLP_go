package resource

import (
	"context"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Additional tests to improve coverage

func TestResourceEmpty(t *testing.T) {
	// Test Empty() function
	r := Empty()
	require.NotNil(t, r)
	assert.True(t, r.IsEmpty())
}

func TestDefaultResource(t *testing.T) {
	// Test Default() function
	r := Default()
	require.NotNil(t, r)
	assert.Equal(t, "OTLP_go", r.GetString("telemetry.sdk.name"))
	assert.Equal(t, "go", r.GetString("telemetry.sdk.language"))
}

func TestDefaultDetectorsCoverage(t *testing.T) {
	// Test DefaultDetectors() function
	detectors := DefaultDetectors()
	require.NotEmpty(t, detectors)
	
	// Should have at least 3 detectors
	assert.GreaterOrEqual(t, len(detectors), 3)
}

func TestResourceDetectorTypes(t *testing.T) {
	// Test all detector types are set correctly
	detectors := []struct {
		detector Detector
		wantType string
	}{
		{&EnvironmentDetector{}, "environment"},
		{&HostDetector{}, "host"},
		{&ProcessDetector{}, "process"},
		{&OSDetector{}, "os"},
		{&ContainerDetector{}, "container"},
	}

	for _, tc := range detectors {
		t.Run(tc.wantType, func(t *testing.T) {
			assert.Equal(t, tc.wantType, tc.detector.DetectorType())
		})
	}
}

func TestCloudProviderStringAll(t *testing.T) {
	// Test all cloud provider string representations
	tests := []struct {
		provider CloudProvider
		want     string
	}{
		{CloudProviderUnknown, "unknown"},
		{CloudProviderAWS, "aws"},
		{CloudProviderGCP, "gcp"},
		{CloudProviderAzure, "azure"},
	}

	for _, tc := range tests {
		t.Run(tc.want, func(t *testing.T) {
			got := tc.provider.String()
			assert.Equal(t, tc.want, got)
		})
	}
}

func TestMergeWithMultipleResources(t *testing.T) {
	// Test merging more than 2 resources
	r1 := types.NewResource(types.NewAttribute("k1", "v1"))
	r2 := types.NewResource(types.NewAttribute("k2", "v2"))
	r3 := types.NewResource(types.NewAttribute("k3", "v3"))
	r4 := types.NewResource(types.NewAttribute("k1", "v1-override"))

	merged := Merge(r1, r2, r3, r4)
	
	assert.Equal(t, "v1-override", merged.GetString("k1")) // Last wins
	assert.Equal(t, "v2", merged.GetString("k2"))
	assert.Equal(t, "v3", merged.GetString("k3"))
}



func TestDetectorResultTypes(t *testing.T) {
	// Test DetectorResult struct usage
	ctx := context.Background()
	
	detector := DetectorFunc{
		Type: "test",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("test", "value")), nil
		},
	}
	
	res, err := detector.Detect(ctx)
	result := DetectorResult{
		Resource: res,
		Error:    err,
		Source:   detector.DetectorType(),
	}
	
	assert.NotNil(t, result.Resource)
	assert.NoError(t, result.Error)
	assert.Equal(t, "test", result.Source)
}

func TestCloudProviderDetectorWithProvider(t *testing.T) {
	// Test creating cloud provider detector for each provider
	providers := []string{"aws", "gcp", "azure"}
	
	for _, provider := range providers {
		t.Run(provider, func(t *testing.T) {
			detector := NewCloudProviderDetector(provider)
			require.NotNil(t, detector)
			assert.Equal(t, "cloud", detector.DetectorType())
			assert.Equal(t, provider, detector.provider)
		})
	}
}

func TestMergeStrategyValues(t *testing.T) {
	// Test that merge strategy constants have correct values
	assert.Equal(t, MergeStrategy(0), MergeFirstWins)
	assert.Equal(t, MergeStrategy(1), MergeLastWins)
}

func TestConfigOptions(t *testing.T) {
	// Test all config options work together
	cfg := &Config{
		Detectors:         []Detector{},
		DefaultAttributes: make(map[string]interface{}),
	}
	
	// Apply multiple options
	opt1 := WithDetectors(&EnvironmentDetector{})
	opt2 := WithDefaultAttributes(map[string]interface{}{"key": "value"})
	
	opt1(cfg)
	opt2(cfg)
	
	assert.Len(t, cfg.Detectors, 1)
	assert.Equal(t, "value", cfg.DefaultAttributes["key"])
}

func TestResourceAttributesEnvFull(t *testing.T) {
	// Test all fields of ResourceAttributesEnv
	env := &ResourceAttributesEnv{
		ServiceName:           "svc",
		ServiceVersion:        "1.0",
		ServiceNamespace:      "ns",
		DeploymentEnvironment: "prod",
		HostName:              "host1",
		HostID:                "id1",
		ContainerID:           "cid1",
		ContainerName:         "cname",
		PodName:               "pod1",
		PodNamespace:          "podns",
		NodeName:              "node1",
		ClusterName:           "cluster1",
		CloudProvider:         "aws",
		CloudRegion:           "us-east-1",
		CloudZone:             "us-east-1a",
	}
	
	res := env.ToResource()
	
	assert.Equal(t, "svc", res.GetString("service.name"))
	assert.Equal(t, "1.0", res.GetString("service.version"))
	assert.Equal(t, "ns", res.GetString("service.namespace"))
	assert.Equal(t, "prod", res.GetString("deployment.environment"))
	assert.Equal(t, "host1", res.GetString("host.name"))
	assert.Equal(t, "id1", res.GetString("host.id"))
	assert.Equal(t, "cid1", res.GetString("container.id"))
	assert.Equal(t, "cname", res.GetString("container.name"))
	assert.Equal(t, "pod1", res.GetString("k8s.pod.name"))
	assert.Equal(t, "podns", res.GetString("k8s.namespace.name"))
	assert.Equal(t, "node1", res.GetString("k8s.node.name"))
	assert.Equal(t, "cluster1", res.GetString("k8s.cluster.name"))
	assert.Equal(t, "aws", res.GetString("cloud.provider"))
	assert.Equal(t, "us-east-1", res.GetString("cloud.region"))
	assert.Equal(t, "us-east-1a", res.GetString("cloud.availability_zone"))
}

func TestEnvironmentDetectorWithCustomAttrs(t *testing.T) {
	// Create detector with custom attributes
	detector := &EnvironmentDetector{
		CustomAttrs: map[string]string{
			"MY_VAR":         "my.attr",
			"ANOTHER_VAR":    "another.attr",
			"NON_EXISTENT":   "nonexistent.attr",
		},
	}
	
	// Note: We can't set env vars in this test easily, but we can verify
	// the detector structure is correct
	assert.NotNil(t, detector.CustomAttrs)
	assert.Equal(t, "my.attr", detector.CustomAttrs["MY_VAR"])
}

func TestResourceFromMapVariations(t *testing.T) {
	t.Run("normal map", func(t *testing.T) {
		m := map[string]string{
			"k1": "v1",
			"k2": "v2",
		}
		res := ResourceFromMap(m)
		assert.Equal(t, "v1", res.GetString("k1"))
		assert.Equal(t, "v2", res.GetString("k2"))
	})
	
	t.Run("single entry", func(t *testing.T) {
		m := map[string]string{"key": "value"}
		res := ResourceFromMap(m)
		assert.Equal(t, "value", res.GetString("key"))
	})
}

func TestDetectAllWithMultiple(t *testing.T) {
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
	
	results := DetectAll(ctx, d1, d2)
	require.Len(t, results, 2)
	
	// Verify both results
	assert.Equal(t, "v1", results[0].Resource.GetString("k1"))
	assert.Equal(t, "v2", results[1].Resource.GetString("k2"))
}

func TestFilterDetectorsVariations(t *testing.T) {
	t.Run("all successful", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(), Error: nil},
			{Resource: types.NewResource(), Error: nil},
		}
		filtered := FilterDetectors(results)
		assert.Len(t, filtered, 2)
	})
	
	t.Run("all failed", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: nil, Error: assert.AnError},
			{Resource: nil, Error: assert.AnError},
		}
		filtered := FilterDetectors(results)
		assert.Empty(t, filtered)
	})
	
	t.Run("mixed", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(), Error: nil},
			{Resource: nil, Error: assert.AnError},
			{Resource: types.NewResource(), Error: nil},
		}
		filtered := FilterDetectors(results)
		assert.Len(t, filtered, 2)
	})
}

func TestMergeResultsVariations(t *testing.T) {
	t.Run("empty input", func(t *testing.T) {
		merged := MergeResults(nil)
		assert.True(t, merged.IsEmpty())
	})
	
	t.Run("all nil resources", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: nil, Error: nil},
			{Resource: nil, Error: assert.AnError},
		}
		merged := MergeResults(results)
		assert.True(t, merged.IsEmpty())
	})
}

func TestCompositeDetectorVariations(t *testing.T) {
	ctx := context.Background()
	
	t.Run("single detector", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(types.NewAttribute("k", "v")), nil
			},
		}
		
		composite := NewCompositeDetector(MergeLastWins, d1)
		res, err := composite.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, "v", res.GetString("k"))
	})
	
	t.Run("detector returning nil resource with no error", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(types.NewAttribute("k", "v")), nil
			},
		}
		
		composite := NewCompositeDetector(MergeLastWins, d1, d2)
		res, err := composite.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, "v", res.GetString("k"))
	})
}



func TestNewResourceWithNilResult(t *testing.T) {
	ctx := context.Background()
	
	// Create a detector that returns nil
	nilDetector := DetectorFunc{
		Type: "nil",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, nil
		},
	}
	
	res, err := New(ctx, WithDetectors(nilDetector))
	require.NoError(t, err)
	require.NotNil(t, res)
	
	// Should still have default SDK attributes
	assert.NotEmpty(t, res.GetString("telemetry.sdk.name"))
}

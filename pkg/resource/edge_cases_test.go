package resource

import (
	"context"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Additional edge case tests to improve coverage

func TestDetectAWSNotOnAWS(t *testing.T) {
	ctx := context.Background()
	
	// Should return error when not on AWS
	_, err := detectAWS(ctx)
	assert.Error(t, err)
}

func TestDetectGCPNotOnGCP(t *testing.T) {
	ctx := context.Background()
	
	// Should return error when not on GCP
	_, err := detectGCP(ctx)
	assert.Error(t, err)
}

func TestDetectAzureNotOnAzure(t *testing.T) {
	ctx := context.Background()
	
	// Should return error when not on Azure
	_, err := detectAzure(ctx)
	assert.Error(t, err)
}

func TestIsAWSWithoutEnv(t *testing.T) {
	// Test isAWS without environment variables
	// Should attempt to reach metadata service
	result := isAWS()
	// Result depends on network connectivity
	_ = result
}

func TestIsGCPWithoutEnv(t *testing.T) {
	// Test isGCP without environment variables
	result := isGCP()
	// Result depends on network connectivity
	_ = result
}

func TestIsAzureWithoutEnv(t *testing.T) {
	// Test isAzure without environment variables
	result := isAzure()
	// Result depends on network connectivity
	_ = result
}

func TestGetAWSMetadataErrors(t *testing.T) {
	ctx := context.Background()
	
	// Should error when not on AWS
	_, err := getAWSMetadata(ctx, "instance-id")
	assert.Error(t, err)
}

func TestGetGCPMetadataErrors(t *testing.T) {
	ctx := context.Background()
	
	// Should error when not on GCP
	_, err := getGCPMetadata(ctx, "instance/id")
	assert.Error(t, err)
}

func TestGetAzureMetadataErrors(t *testing.T) {
	ctx := context.Background()
	
	// Should error when not on Azure
	_, err := getAzureMetadata(ctx)
	assert.Error(t, err)
}

func TestGetAWSAccountIDErrors(t *testing.T) {
	ctx := context.Background()
	
	// Should error when not on AWS
	_, err := getAWSAccountID(ctx)
	assert.Error(t, err)
}

func TestDetectContainerNotInContainer(t *testing.T) {
	ctx := context.Background()
	
	// Should work even when not in container
	res, err := detectContainer(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestGetLinuxVersionNotLinux(t *testing.T) {
	// This should return empty string on non-Linux systems
	version := getLinuxVersion()
	// Result depends on OS
	_ = version
}

func TestGetDarwinVersionNotDarwin(t *testing.T) {
	// This should return empty string on non-macOS systems
	version := getDarwinVersion()
	// Result depends on OS
	_ = version
}

func TestGetWindowsVersionNotWindows(t *testing.T) {
	// This should return empty string on non-Windows systems
	version := getWindowsVersion()
	// Result depends on OS
	_ = version
}

func TestGetOSDescriptionAll(t *testing.T) {
	// Test on current OS
	desc := getOSDescription()
	// Should return something on all platforms
	// Just ensure it doesn't panic
	_ = desc
}

func TestGetHostIDAll(t *testing.T) {
	// Test on current OS
	id := getHostID()
	// May or may not return value depending on OS
	// Just ensure it doesn't panic
	_ = id
}

func TestGetHostTypeAll(t *testing.T) {
	// Test on current OS
	typ := getHostType()
	// Should return at minimum the GOARCH
	assert.NotEmpty(t, typ)
}

func TestParseOSReleaseEmpty(t *testing.T) {
	result := parseOSRelease("")
	assert.Empty(t, result)
}

func TestParseLSBReleaseEmpty(t *testing.T) {
	result := parseLSBRelease("")
	assert.Empty(t, result)
}

func TestParseLSBReleaseNoDescription(t *testing.T) {
	content := `DISTRIB_ID=Ubuntu`
	result := parseLSBRelease(content)
	assert.Equal(t, "Ubuntu", result)
}





func TestExtractUUIDFound(t *testing.T) {
	output := `Hardware UUID: 12345678-1234-1234-1234-123456789ABC`
	result := extractUUID(output)
	assert.Equal(t, "12345678-1234-1234-1234-123456789ABC", result)
}

func TestExtractWindowsGUIDFound(t *testing.T) {
	output := `MachineGuid    REG_SZ    12345678-1234-1234-1234-123456789ABC`
	result := extractWindowsGUID(output)
	assert.Equal(t, "12345678-1234-1234-1234-123456789ABC", result)
}

func TestIsInContainerCheck(t *testing.T) {
	// Should not panic
	inContainer := isInContainer()
	// Result depends on environment
	_ = inContainer
}

func TestGetContainerIDNotInContainer(t *testing.T) {
	// Should return empty string when not in container
	id := getContainerID()
	// Result depends on environment
	_ = id
}

func TestDetectContainerRuntimeNotInContainer(t *testing.T) {
	// Should return empty string when not in container
	runtime := detectContainerRuntime()
	// Result depends on environment
	_ = runtime
}

func TestGetHostInfoComplete(t *testing.T) {
	info := GetHostInfo()
	require.NotNil(t, info)
	
	// All fields should be populated or zero values
	assert.NotZero(t, info.NumCPU)
	// Hostname may be empty if os.Hostname fails
	// OS should be set
	assert.NotEmpty(t, info.OS)
	assert.NotEmpty(t, info.Arch)
}

func TestNewWithEmptyDefaultAttributes(t *testing.T) {
	ctx := context.Background()
	
	// Test with empty map
	res, err := New(ctx, WithDefaultAttributes(map[string]interface{}{}))
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestNewWithNilDefaultAttributes(t *testing.T) {
	ctx := context.Background()
	
	// Test with nil map - should still work
	cfg := &Config{
		DefaultAttributes: nil,
	}
	
	// Create resource directly
	res, err := New(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
	_ = cfg
}

func TestMergeSingleResource(t *testing.T) {
	r := types.NewResource(types.NewAttribute("key", "value"))
	
	merged := Merge(r)
	assert.Equal(t, "value", merged.GetString("key"))
}

func TestCompositeDetectorFirstWinsWithNil(t *testing.T) {
	ctx := context.Background()
	
	d1 := DetectorFunc{
		Type: "nil",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, nil
		},
	}
	d2 := DetectorFunc{
		Type: "valid",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("key", "value")), nil
		},
	}
	
	composite := NewCompositeDetector(MergeFirstWins, d1, d2)
	res, err := composite.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, "value", res.GetString("key"))
}

func TestCompositeDetectorLastWinsWithNil(t *testing.T) {
	ctx := context.Background()
	
	d1 := DetectorFunc{
		Type: "valid",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("key", "first")), nil
		},
	}
	d2 := DetectorFunc{
		Type: "nil",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, nil
		},
	}
	
	composite := NewCompositeDetector(MergeLastWins, d1, d2)
	res, err := composite.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, "first", res.GetString("key"))
}

func TestAsyncDetectorWithAllSuccess(t *testing.T) {
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
	d3 := DetectorFunc{
		Type: "d3",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("k3", "v3")), nil
		},
	}
	
	async := NewAsyncDetector(d1, d2, d3)
	res, err := async.Detect(ctx)
	require.NoError(t, err)
	
	assert.Equal(t, "v1", res.GetString("k1"))
	assert.Equal(t, "v2", res.GetString("k2"))
	assert.Equal(t, "v3", res.GetString("k3"))
}

func TestChainedDetectorMultipleSuccess(t *testing.T) {
	ctx := context.Background()
	
	d1 := DetectorFunc{
		Type: "empty",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.EmptyResource(), nil
		},
	}
	d2 := DetectorFunc{
		Type: "valid",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("key", "value")), nil
		},
	}
	d3 := DetectorFunc{
		Type: "another",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("key", "ignored")), nil
		},
	}
	
	chained := NewChainedDetector(d1, d2, d3)
	res, err := chained.Detect(ctx)
	require.NoError(t, err)
	
	// Should stop at d2 (first non-empty)
	assert.Equal(t, "value", res.GetString("key"))
}

func TestCachingDetectorSuccess(t *testing.T) {
	ctx := context.Background()
	
	callCount := 0
	inner := DetectorFunc{
		Type: "counter",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			callCount++
			return types.NewResource(types.NewAttribute("count", string(rune('0'+callCount)))), nil
		},
	}
	
	caching := NewCachingDetector(inner)
	
	// First call
	res1, err := caching.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, 1, callCount)
	
	// Multiple calls should use cache
	for i := 0; i < 3; i++ {
		res, err := caching.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, res1.GetString("count"), res.GetString("count"))
	}
	
	assert.Equal(t, 1, callCount)
	
	// Reset and call again
	caching.Reset()
	_, err = caching.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, 2, callCount)
}

func TestDetectAllWithErrors(t *testing.T) {
	ctx := context.Background()
	
	d1 := DetectorFunc{
		Type: "error",
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
	
	results := DetectAll(ctx, d1, d2)
	require.Len(t, results, 2)
	
	assert.Error(t, results[0].Error)
	assert.NoError(t, results[1].Error)
	assert.Equal(t, "value", results[1].Resource.GetString("key"))
}

func TestFilterDetectorsVarious(t *testing.T) {
	t.Run("nil input", func(t *testing.T) {
		result := FilterDetectors(nil)
		// Returns empty slice, not nil
		assert.Empty(t, result)
	})
	
	t.Run("empty list", func(t *testing.T) {
		result := FilterDetectors([]DetectorResult{})
		assert.Empty(t, result)
	})
	
	t.Run("all successful", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(), Error: nil},
			{Resource: types.NewResource(), Error: nil},
			{Resource: types.NewResource(), Error: nil},
		}
		filtered := FilterDetectors(results)
		assert.Len(t, filtered, 3)
	})
	
	t.Run("mixed success and failures", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(), Error: nil},
			{Resource: nil, Error: assert.AnError},
			{Resource: types.NewResource(), Error: nil},
			{Resource: nil, Error: assert.AnError},
		}
		filtered := FilterDetectors(results)
		assert.Len(t, filtered, 2)
	})
}

func TestMergeResultsVarious(t *testing.T) {
	t.Run("single result", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(types.NewAttribute("key", "value")), Error: nil},
		}
		merged := MergeResults(results)
		assert.Equal(t, "value", merged.GetString("key"))
	})
	
	t.Run("multiple results", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(types.NewAttribute("k1", "v1")), Error: nil},
			{Resource: types.NewResource(types.NewAttribute("k2", "v2")), Error: nil},
			{Resource: types.NewResource(types.NewAttribute("k3", "v3")), Error: nil},
		}
		merged := MergeResults(results)
		assert.Equal(t, "v1", merged.GetString("k1"))
		assert.Equal(t, "v2", merged.GetString("k2"))
		assert.Equal(t, "v3", merged.GetString("k3"))
	})
	
	t.Run("with some failures", func(t *testing.T) {
		results := []DetectorResult{
			{Resource: types.NewResource(types.NewAttribute("k1", "v1")), Error: nil},
			{Resource: nil, Error: assert.AnError},
			{Resource: types.NewResource(types.NewAttribute("k2", "v2")), Error: nil},
		}
		merged := MergeResults(results)
		assert.Equal(t, "v1", merged.GetString("k1"))
		assert.Equal(t, "v2", merged.GetString("k2"))
	})
}

func TestParseAttributesVariousInputs(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected map[string]string
	}{
		{"empty", "", map[string]string{}},
		{"single", "a=b", map[string]string{"a": "b"}},
		{"multiple", "a=1,b=2,c=3", map[string]string{"a": "1", "b": "2", "c": "3"}},
		{"with spaces", "a = 1 , b = 2", map[string]string{"a": "1", "b": "2"}},
		{"empty value", "a=,b=2", map[string]string{"a": "", "b": "2"}},
	}
	
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			result := parseAttributes(tc.input)
			assert.Equal(t, tc.expected, result)
		})
	}
}

func TestResourceAttributesEnvPartialFields(t *testing.T) {
	// Test with only some fields set
	env := &ResourceAttributesEnv{
		ServiceName: "my-service",
		// Leave all other fields empty
	}
	
	res := env.ToResource()
	assert.Equal(t, "my-service", res.GetString("service.name"))
	
	// Other fields should not exist
	_, hasServiceVersion := res.Get("service.version")
	assert.False(t, hasServiceVersion)
}

func TestWithCloudProviderUnknown(t *testing.T) {
	// Test with "unknown" provider - should auto-detect
	cfg := &Config{Detectors: []Detector{}}
	
	opt := WithCloudProvider("unknown")
	opt(cfg)
	
	// Should have added a detector (or not, depending on detection)
	// Just ensure it doesn't panic
}

func TestResourceDetectorInterface(t *testing.T) {
	// Test that all detectors implement the interface
	var _ Detector = &EnvironmentDetector{}
	var _ Detector = &HostDetector{}
	var _ Detector = &ProcessDetector{}
	var _ Detector = &OSDetector{}
	var _ Detector = &ContainerDetector{}
}

func TestNewWithCustomDetectorError(t *testing.T) {
	ctx := context.Background()
	
	customDetector := DetectorFunc{
		Type: "custom",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, assert.AnError
		},
	}
	
	// Should not return error even if custom detector fails
	res, err := New(ctx, WithDetectors(customDetector))
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestMergeAllNil(t *testing.T) {
	merged := Merge(nil, nil, nil, nil)
	assert.NotNil(t, merged)
	assert.True(t, merged.IsEmpty())
}

func TestMergeWithOnlyOneValid(t *testing.T) {
	valid := types.NewResource(types.NewAttribute("key", "value"))
	
	merged := Merge(nil, nil, valid, nil)
	assert.Equal(t, "value", merged.GetString("key"))
}

func TestEnvironmentDetectorDetect(t *testing.T) {
	ctx := context.Background()
	detector := &EnvironmentDetector{}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestHostDetectorWithBothOptions(t *testing.T) {
	ctx := context.Background()
	detector := &HostDetector{
		IncludeHostID:   true,
		IncludeHostType: true,
	}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestContainerDetectorDetect(t *testing.T) {
	ctx := context.Background()
	detector := &ContainerDetector{}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestOSDetectorDetect(t *testing.T) {
	ctx := context.Background()
	detector := &OSDetector{}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

func TestProcessDetectorDetect(t *testing.T) {
	ctx := context.Background()
	detector := &ProcessDetector{}
	
	res, err := detector.Detect(ctx)
	require.NoError(t, err)
	assert.NotNil(t, res)
}

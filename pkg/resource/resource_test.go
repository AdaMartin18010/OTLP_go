package resource

import (
	"context"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNew(t *testing.T) {
	ctx := context.Background()

	t.Run("creates resource with default detectors", func(t *testing.T) {
		res, err := New(ctx)
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should have SDK attributes
		assert.NotEmpty(t, res.GetString("telemetry.sdk.name"))
		assert.Equal(t, "OTLP_go", res.GetString("telemetry.sdk.name"))
		assert.Equal(t, "go", res.GetString("telemetry.sdk.language"))
	})

	t.Run("creates resource with custom detectors", func(t *testing.T) {
		customDetector := DetectorFunc{
			Type: "custom",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("custom.attr", "value"),
				), nil
			},
		}

		res, err := New(ctx, WithDetectors(customDetector))
		require.NoError(t, err)
		require.NotNil(t, res)

		assert.Equal(t, "value", res.GetString("custom.attr"))
	})

	t.Run("creates resource with default attributes", func(t *testing.T) {
		res, err := New(ctx, WithDefaultAttributes(map[string]interface{}{
			"service.name":    "test-service",
			"service.version": "1.0.0",
		}))
		require.NoError(t, err)
		require.NotNil(t, res)

		assert.Equal(t, "test-service", res.GetString("service.name"))
		assert.Equal(t, "1.0.0", res.GetString("service.version"))
	})

	t.Run("detector failure is not fatal", func(t *testing.T) {
		failingDetector := DetectorFunc{
			Type: "failing",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, ErrDetectorFailed
			},
		}

		res, err := New(ctx, WithDetectors(failingDetector))
		require.NoError(t, err)
		require.NotNil(t, res)
	})
}

func TestMustNew(t *testing.T) {
	ctx := context.Background()

	t.Run("returns resource on success", func(t *testing.T) {
		res := MustNew(ctx)
		require.NotNil(t, res)
		assert.NotEmpty(t, res.GetString("telemetry.sdk.name"))
	})
}

func TestMerge(t *testing.T) {
	t.Run("merges multiple resources", func(t *testing.T) {
		r1 := types.NewResource(
			types.NewAttribute("key1", "value1"),
			types.NewAttribute("key2", "value2"),
		)
		r2 := types.NewResource(
			types.NewAttribute("key2", "overridden"),
			types.NewAttribute("key3", "value3"),
		)

		merged := Merge(r1, r2)
		require.NotNil(t, merged)

		assert.Equal(t, "value1", merged.GetString("key1"))
		assert.Equal(t, "overridden", merged.GetString("key2")) // Last wins
		assert.Equal(t, "value3", merged.GetString("key3"))
	})

	t.Run("handles nil resources", func(t *testing.T) {
		r1 := types.NewResource(types.NewAttribute("key", "value"))

		merged := Merge(nil, r1, nil)
		require.NotNil(t, merged)
		assert.Equal(t, "value", merged.GetString("key"))
	})

	t.Run("returns empty resource for empty input", func(t *testing.T) {
		merged := Merge()
		require.NotNil(t, merged)
		assert.True(t, merged.IsEmpty())
	})
}

func TestDefaultDetectors(t *testing.T) {
	detectors := DefaultDetectors()
	require.NotEmpty(t, detectors)

	// Check that we have the expected detector types
	types := make(map[string]bool)
	for _, d := range detectors {
		types[d.DetectorType()] = true
	}

	assert.True(t, types["environment"], "should have environment detector")
	assert.True(t, types["host"], "should have host detector")
	assert.True(t, types["process"], "should have process detector")
}

func TestDefault(t *testing.T) {
	res := Default()
	require.NotNil(t, res)

	assert.Equal(t, "OTLP_go", res.GetString("telemetry.sdk.name"))
	assert.Equal(t, "go", res.GetString("telemetry.sdk.language"))
	assert.NotEmpty(t, res.GetString("telemetry.sdk.version"))
}

func TestEmpty(t *testing.T) {
	res := Empty()
	require.NotNil(t, res)
	assert.True(t, res.IsEmpty())
}

func TestProcessDetector(t *testing.T) {
	ctx := context.Background()
	detector := &ProcessDetector{}

	t.Run("detects process attributes", func(t *testing.T) {
		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should have process runtime info
		assert.Equal(t, "go", res.GetString("process.runtime.name"))
		assert.NotEmpty(t, res.GetString("process.runtime.version"))
	})

	t.Run("returns correct detector type", func(t *testing.T) {
		assert.Equal(t, "process", detector.DetectorType())
	})
}

func TestWithOptions(t *testing.T) {
	ctx := context.Background()

	t.Run("WithFromEnv adds environment detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithFromEnv()
		opt(cfg)

		hasEnv := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "environment" {
				hasEnv = true
				break
			}
		}
		assert.True(t, hasEnv)
	})

	t.Run("WithHost adds host detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithHost()
		opt(cfg)

		hasHost := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "host" {
				hasHost = true
				break
			}
		}
		assert.True(t, hasHost)
	})

	t.Run("WithProcess adds process detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithProcess()
		opt(cfg)

		hasProcess := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "process" {
				hasProcess = true
				break
			}
		}
		assert.True(t, hasProcess)
	})

	t.Run("WithContainer adds container detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithContainer()
		opt(cfg)

		hasContainer := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "container" {
				hasContainer = true
				break
			}
		}
		assert.True(t, hasContainer)
	})

	t.Run("WithOS adds OS detector", func(t *testing.T) {
		cfg := &Config{Detectors: []Detector{}}
		opt := WithOS()
		opt(cfg)

		hasOS := false
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "os" {
				hasOS = true
				break
			}
		}
		assert.True(t, hasOS)
	})

	t.Run("duplicate detectors are not added", func(t *testing.T) {
		hostDetector := &HostDetector{}
		cfg := &Config{Detectors: []Detector{hostDetector}}
		opt := WithHost()
		opt(cfg)

		count := 0
		for _, d := range cfg.Detectors {
			if d.DetectorType() == "host" {
				count++
			}
		}
		assert.Equal(t, 1, count)
	})
}

func TestOSDetector(t *testing.T) {
	ctx := context.Background()
	detector := &OSDetector{}

	t.Run("detects OS attributes", func(t *testing.T) {
		res, err := detector.Detect(ctx)
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should have OS info
		assert.NotEmpty(t, res.GetString("os.type"))
	})

	t.Run("returns correct detector type", func(t *testing.T) {
		assert.Equal(t, "os", detector.DetectorType())
	})
}

func TestContainerDetector(t *testing.T) {
	ctx := context.Background()
	detector := &ContainerDetector{}

	t.Run("runs without error", func(t *testing.T) {
		// This may or may not detect container info depending on environment
		res, err := detector.Detect(ctx)
		// Should not error, even if not in container
		assert.NoError(t, err)
		assert.NotNil(t, res)
	})

	t.Run("returns correct detector type", func(t *testing.T) {
		assert.Equal(t, "container", detector.DetectorType())
	})
}

func TestCloudProviderDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("returns correct detector type", func(t *testing.T) {
		detector := NewCloudProviderDetector("aws")
		assert.Equal(t, "cloud", detector.DetectorType())
	})

	t.Run("returns error for unknown provider", func(t *testing.T) {
		detector := NewCloudProviderDetector("unknown")
		_, err := detector.Detect(ctx)
		assert.Error(t, err)
	})
}

func TestDetectorFunc(t *testing.T) {
	ctx := context.Background()

	t.Run("implements Detector interface", func(t *testing.T) {
		called := false
		detector := DetectorFunc{
			Type: "test",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				called = true
				return types.EmptyResource(), nil
			},
		}

		assert.Equal(t, "test", detector.DetectorType())

		res, err := detector.Detect(ctx)
		assert.NoError(t, err)
		assert.NotNil(t, res)
		assert.True(t, called)
	})
}

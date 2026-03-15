package resource

import (
	"context"
	"errors"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewWithMultipleOptions(t *testing.T) {
	ctx := context.Background()

	t.Run("with multiple detectors", func(t *testing.T) {
		customDetector := DetectorFunc{
			Type: "custom",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("custom.key", "custom-value"),
				), nil
			},
		}

		res, err := New(ctx,
			WithDetectors(customDetector),
			WithDefaultAttributes(map[string]interface{}{
				"default.key": "default-value",
			}),
		)
		require.NoError(t, err)
		require.NotNil(t, res)

		assert.Equal(t, "custom-value", res.GetString("custom.key"))
	})

	t.Run("with empty default attributes", func(t *testing.T) {
		res, err := New(ctx, WithDefaultAttributes(map[string]interface{}{}))
		require.NoError(t, err)
		require.NotNil(t, res)
	})
}

func TestMergeWithNilResources(t *testing.T) {
	t.Run("all nil resources", func(t *testing.T) {
		merged := Merge(nil, nil, nil)
		require.NotNil(t, merged)
		assert.True(t, merged.IsEmpty())
	})

	t.Run("single non-nil resource", func(t *testing.T) {
		r1 := types.NewResource(types.NewAttribute("key", "value"))
		merged := Merge(nil, r1, nil)
		assert.Equal(t, "value", merged.GetString("key"))
	})
}

func TestDetectorFuncVariations(t *testing.T) {
	ctx := context.Background()

	t.Run("detector that returns error", func(t *testing.T) {
		detector := DetectorFunc{
			Type: "error-detector",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, errors.New("detection failed")
			},
		}

		res, err := detector.Detect(ctx)
		assert.Error(t, err)
		assert.Nil(t, res)
		assert.Equal(t, "error-detector", detector.DetectorType())
	})

	t.Run("detector that returns nil resource", func(t *testing.T) {
		detector := DetectorFunc{
			Type: "nil-detector",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, nil
			},
		}

		res, err := detector.Detect(ctx)
		assert.NoError(t, err)
		assert.Nil(t, res)
	})
}

func TestNewResourceEdgeCases(t *testing.T) {
	ctx := context.Background()

	t.Run("all detectors fail", func(t *testing.T) {
		failingDetector := DetectorFunc{
			Type: "failing",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, errors.New("always fails")
			},
		}

		// Should still return a resource with SDK defaults
		res, err := New(ctx, WithDetectors(failingDetector))
		require.NoError(t, err)
		require.NotNil(t, res)

		// Should have default SDK attributes
		assert.Equal(t, "OTLP_go", res.GetString("telemetry.sdk.name"))
	})

	t.Run("detector returns empty resource", func(t *testing.T) {
		emptyDetector := DetectorFunc{
			Type: "empty",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.EmptyResource(), nil
			},
		}

		res, err := New(ctx, WithDetectors(emptyDetector))
		require.NoError(t, err)
		require.NotNil(t, res)
	})
}

func TestDefaultAttributesOverride(t *testing.T) {
	ctx := context.Background()

	// Create a detector that sets an attribute
	detector := DetectorFunc{
		Type: "test",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(
				types.NewAttribute("service.name", "from-detector"),
			), nil
		},
	}

	// Default attributes should not override detector values
	res, err := New(ctx,
		WithDetectors(detector),
		WithDefaultAttributes(map[string]interface{}{
			"service.name": "from-default",
		}),
	)
	require.NoError(t, err)

	// Detector value should win
	assert.Equal(t, "from-detector", res.GetString("service.name"))
}

func TestMustNewPanic(t *testing.T) {
	// Note: MustNew should never panic with current implementation
	// since New doesn't return errors in most cases
	t.Run("does not panic on valid config", func(t *testing.T) {
		ctx := context.Background()
		assert.NotPanics(t, func() {
			res := MustNew(ctx)
			assert.NotNil(t, res)
		})
	})
}

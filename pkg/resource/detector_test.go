package resource

import (
	"context"
	"errors"
	"testing"

	"OTLP_go/pkg/types"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestCompositeDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("merges resources from multiple detectors", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "value1"),
					types.NewAttribute("key2", "value2"),
				), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key2", "overridden"),
					types.NewAttribute("key3", "value3"),
				), nil
			},
		}

		composite := NewCompositeDetector(MergeLastWins, d1, d2)
		assert.Equal(t, "composite", composite.DetectorType())

		res, err := composite.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "value1", res.GetString("key1"))
		assert.Equal(t, "overridden", res.GetString("key2"))
		assert.Equal(t, "value3", res.GetString("key3"))
	})

	t.Run("MergeFirstWins strategy", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "first"),
				), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "second"),
				), nil
			},
		}

		composite := NewCompositeDetector(MergeFirstWins, d1, d2)
		res, err := composite.Detect(ctx)
		require.NoError(t, err)

		// First detector's value should win
		assert.Equal(t, "first", res.GetString("key1"))
	})

	t.Run("handles failing detectors", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "value1"),
				), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, errors.New("detector failed")
			},
		}
		d3 := DetectorFunc{
			Type: "d3",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key2", "value2"),
				), nil
			},
		}

		composite := NewCompositeDetector(MergeLastWins, d1, d2, d3)
		res, err := composite.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "value1", res.GetString("key1"))
		assert.Equal(t, "value2", res.GetString("key2"))
	})

	t.Run("returns error for no detectors", func(t *testing.T) {
		composite := NewCompositeDetector(MergeLastWins)
		_, err := composite.Detect(ctx)
		assert.Error(t, err)
	})

	t.Run("handles nil resources", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "value1"),
				), nil
			},
		}

		composite := NewCompositeDetector(MergeLastWins, d1, d2)
		res, err := composite.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "value1", res.GetString("key1"))
	})
}

func TestAsyncDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("runs detectors concurrently", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "value1"),
				), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key2", "value2"),
				), nil
			},
		}

		async := NewAsyncDetector(d1, d2)
		assert.Equal(t, "async", async.DetectorType())

		res, err := async.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "value1", res.GetString("key1"))
		assert.Equal(t, "value2", res.GetString("key2"))
	})

	t.Run("returns empty resource for no detectors", func(t *testing.T) {
		async := NewAsyncDetector()
		res, err := async.Detect(ctx)
		require.NoError(t, err)
		assert.True(t, res.IsEmpty())
	})

	t.Run("handles detector errors", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, errors.New("failed")
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key1", "value1"),
				), nil
			},
		}

		async := NewAsyncDetector(d1, d2)
		res, err := async.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "value1", res.GetString("key1"))
	})
}

func TestConditionalDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("runs detector when condition is true", func(t *testing.T) {
		called := false
		inner := DetectorFunc{
			Type: "inner",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				called = true
				return types.NewResource(
					types.NewAttribute("key", "value"),
				), nil
			},
		}

		conditional := NewConditionalDetector(func() bool { return true }, inner)
		assert.Equal(t, "conditional(inner)", conditional.DetectorType())

		res, err := conditional.Detect(ctx)
		require.NoError(t, err)
		assert.True(t, called)
		assert.Equal(t, "value", res.GetString("key"))
	})

	t.Run("skips detector when condition is false", func(t *testing.T) {
		called := false
		inner := DetectorFunc{
			Type: "inner",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				called = true
				return types.NewResource(
					types.NewAttribute("key", "value"),
				), nil
			},
		}

		conditional := NewConditionalDetector(func() bool { return false }, inner)
		res, err := conditional.Detect(ctx)
		require.NoError(t, err)
		assert.False(t, called)
		assert.True(t, res.IsEmpty())
	})
}

func TestCachingDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("caches detector result", func(t *testing.T) {
		callCount := 0
		inner := DetectorFunc{
			Type: "inner",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				callCount++
				return types.NewResource(
					types.NewAttribute("calls", string(rune('0'+callCount))),
				), nil
			},
		}

		caching := NewCachingDetector(inner)
		assert.Equal(t, "cached(inner)", caching.DetectorType())

		// First call
		res1, err := caching.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, 1, callCount)

		// Second call should use cache
		res2, err := caching.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, 1, callCount) // Should not increase

		// Results should be the same
		assert.Equal(t, res1.GetString("calls"), res2.GetString("calls"))
	})

	t.Run("Reset clears cache", func(t *testing.T) {
		callCount := 0
		inner := DetectorFunc{
			Type: "inner",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				callCount++
				return types.NewResource(
					types.NewAttribute("key", "value"),
				), nil
			},
		}

		caching := NewCachingDetector(inner)

		// First call
		_, err := caching.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, 1, callCount)

		// Reset cache
		caching.Reset()

		// Second call should invoke detector again
		_, err = caching.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, 2, callCount)
	})
}

func TestChainedDetector(t *testing.T) {
	ctx := context.Background()

	t.Run("stops on first success", func(t *testing.T) {
		callCount := 0
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				callCount++
				return types.NewResource(
					types.NewAttribute("source", "first"),
				), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				callCount++
				return types.NewResource(
					types.NewAttribute("source", "second"),
				), nil
			},
		}

		chained := NewChainedDetector(d1, d2)
		assert.Equal(t, "chained", chained.DetectorType())

		res, err := chained.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "first", res.GetString("source"))
		assert.Equal(t, 1, callCount) // Should only call first detector
	})

	t.Run("continues on failure", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, errors.New("failed")
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("source", "second"),
				), nil
			},
		}

		chained := NewChainedDetector(d1, d2)
		res, err := chained.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "second", res.GetString("source"))
	})

	t.Run("continues on empty resource", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.EmptyResource(), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("source", "second"),
				), nil
			},
		}

		chained := NewChainedDetector(d1, d2)
		res, err := chained.Detect(ctx)
		require.NoError(t, err)

		assert.Equal(t, "second", res.GetString("source"))
	})

	t.Run("returns error when all fail", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return nil, errors.New("failed")
			},
		}

		chained := NewChainedDetector(d1)
		_, err := chained.Detect(ctx)
		assert.Error(t, err)
	})
}

func TestDetectAll(t *testing.T) {
	ctx := context.Background()

	d1 := DetectorFunc{
		Type: "d1",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(
				types.NewAttribute("key1", "value1"),
			), nil
		},
	}
	d2 := DetectorFunc{
		Type: "d2",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, errors.New("failed")
		},
	}
	d3 := DetectorFunc{
		Type: "d3",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(
				types.NewAttribute("key3", "value3"),
			), nil
		},
	}

	results := DetectAll(ctx, d1, d2, d3)
	require.Len(t, results, 3)

	assert.Nil(t, results[0].Error)
	assert.Equal(t, "value1", results[0].Resource.GetString("key1"))
	assert.Equal(t, "d1", results[0].Source)

	assert.NotNil(t, results[1].Error)
	assert.Nil(t, results[1].Resource)
	assert.Equal(t, "d2", results[1].Source)

	assert.Nil(t, results[2].Error)
	assert.Equal(t, "value3", results[2].Resource.GetString("key3"))
	assert.Equal(t, "d3", results[2].Source)
}

func TestFilterDetectors(t *testing.T) {
	results := []DetectorResult{
		{Resource: types.NewResource(types.NewAttribute("k", "v")), Error: nil},
		{Resource: nil, Error: errors.New("failed")},
		{Resource: types.NewResource(types.NewAttribute("k2", "v2")), Error: nil},
	}

	filtered := FilterDetectors(results)
	require.Len(t, filtered, 2)
	assert.NotNil(t, filtered[0].Resource)
	assert.NotNil(t, filtered[1].Resource)
}

func TestMergeResults(t *testing.T) {
	results := []DetectorResult{
		{Resource: types.NewResource(types.NewAttribute("k1", "v1")), Error: nil},
		{Resource: nil, Error: errors.New("failed")},
		{Resource: types.NewResource(types.NewAttribute("k2", "v2")), Error: nil},
	}

	merged := MergeResults(results)
	require.NotNil(t, merged)
	assert.Equal(t, "v1", merged.GetString("k1"))
	assert.Equal(t, "v2", merged.GetString("k2"))
}

func TestDetectParallel(t *testing.T) {
	ctx := context.Background()

	d1 := DetectorFunc{
		Type: "d1",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("key", "value1")), nil
		},
	}
	d2 := DetectorFunc{
		Type: "d2",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(types.NewAttribute("key", "value2")), nil
		},
	}

	results := DetectParallel(ctx, d1, d2)
	require.Len(t, results, 2)

	// One of them should be value1 and other value2
	values := map[string]bool{
		results[0].Resource.GetString("key"): true,
		results[1].Resource.GetString("key"): true,
	}
	assert.True(t, values["value1"])
	assert.True(t, values["value2"])
}

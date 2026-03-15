package resource

import (
	"context"
	"errors"
	"testing"

	"OTLP_go/pkg/types"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestCompositeDetectorWithAllNil(t *testing.T) {
	ctx := context.Background()

	// All detectors return nil
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

func TestCompositeDetectorMergeStrategies(t *testing.T) {
	ctx := context.Background()

	t.Run("FirstWins with overlapping keys", func(t *testing.T) {
		d1 := DetectorFunc{
			Type: "d1",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key", "first"),
					types.NewAttribute("only-first", "value1"),
				), nil
			},
		}
		d2 := DetectorFunc{
			Type: "d2",
			Fn: func(ctx context.Context) (*types.Resource, error) {
				return types.NewResource(
					types.NewAttribute("key", "second"),
					types.NewAttribute("only-second", "value2"),
				), nil
			},
		}

		composite := NewCompositeDetector(MergeFirstWins, d1, d2)
		res, err := composite.Detect(ctx)
		require.NoError(t, err)

		// First detector's value should win for overlapping key
		assert.Equal(t, "first", res.GetString("key"))
		// Both unique keys should be present
		assert.Equal(t, "value1", res.GetString("only-first"))
		assert.Equal(t, "value2", res.GetString("only-second"))
	})
}

func TestAsyncDetectorAllFail(t *testing.T) {
	ctx := context.Background()

	d1 := DetectorFunc{
		Type: "failing1",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, errors.New("fail 1")
		},
	}
	d2 := DetectorFunc{
		Type: "failing2",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, errors.New("fail 2")
		},
	}

	async := NewAsyncDetector(d1, d2)
	res, err := async.Detect(ctx)
	require.NoError(t, err)
	assert.True(t, res.IsEmpty())
}

func TestChainedDetectorAllEmpty(t *testing.T) {
	ctx := context.Background()

	d1 := DetectorFunc{
		Type: "empty1",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.EmptyResource(), nil
		},
	}
	d2 := DetectorFunc{
		Type: "empty2",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.EmptyResource(), nil
		},
	}
	d3 := DetectorFunc{
		Type: "empty3",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return nil, errors.New("failed")
		},
	}

	chained := NewChainedDetector(d1, d2, d3)
	_, err := chained.Detect(ctx)
	// All failed or empty, should return error
	assert.Error(t, err)
}

func TestDetectAllEmpty(t *testing.T) {
	ctx := context.Background()

	results := DetectAll(ctx)
	assert.Empty(t, results)
}

func TestFilterDetectorsEmpty(t *testing.T) {
	results := FilterDetectors(nil)
	assert.Empty(t, results)

	results = FilterDetectors([]DetectorResult{})
	assert.Empty(t, results)
}

func TestMergeResultsEmpty(t *testing.T) {
	results := MergeResults(nil)
	assert.True(t, results.IsEmpty())

	results = MergeResults([]DetectorResult{})
	assert.True(t, results.IsEmpty())
}

func TestMergeResultsAllFailed(t *testing.T) {
	results := []DetectorResult{
		{Resource: nil, Error: errors.New("failed")},
		{Resource: nil, Error: errors.New("failed")},
	}

	merged := MergeResults(results)
	assert.True(t, merged.IsEmpty())
}

func TestCachingDetectorMultipleCalls(t *testing.T) {
	ctx := context.Background()

	callCount := 0
	inner := DetectorFunc{
		Type: "inner",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			callCount++
			return types.NewResource(
				types.NewAttribute("count", string(rune('0'+callCount))),
			), nil
		},
	}

	caching := NewCachingDetector(inner)

	// First call
	res1, err := caching.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, 1, callCount)

	// Multiple subsequent calls should use cache
	for i := 0; i < 5; i++ {
		res, err := caching.Detect(ctx)
		require.NoError(t, err)
		assert.Equal(t, res1.GetString("count"), res.GetString("count"))
	}
	assert.Equal(t, 1, callCount) // Should still be 1
}

func TestConditionalDetectorTrueCondition(t *testing.T) {
	ctx := context.Background()

	inner := DetectorFunc{
		Type: "inner",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(
				types.NewAttribute("key", "value"),
			), nil
		},
	}

	conditional := NewConditionalDetector(func() bool { return true }, inner)
	res, err := conditional.Detect(ctx)
	require.NoError(t, err)
	assert.Equal(t, "value", res.GetString("key"))
}

func TestConditionalDetectorFalseCondition(t *testing.T) {
	ctx := context.Background()

	inner := DetectorFunc{
		Type: "inner",
		Fn: func(ctx context.Context) (*types.Resource, error) {
			return types.NewResource(
				types.NewAttribute("key", "value"),
			), nil
		},
	}

	conditional := NewConditionalDetector(func() bool { return false }, inner)
	res, err := conditional.Detect(ctx)
	require.NoError(t, err)
	assert.True(t, res.IsEmpty())
}

func TestDetectParallelEmpty(t *testing.T) {
	ctx := context.Background()

	results := DetectParallel(ctx)
	assert.Empty(t, results)
}

package metric

import (
	"testing"

	"github.com/stretchr/testify/assert"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
)

func TestDropAggregation(t *testing.T) {
	agg := DropAggregation()
	assert.IsType(t, sdkmetric.AggregationDrop{}, agg)
}

func TestSumAggregation(t *testing.T) {
	agg := SumAggregation()
	assert.IsType(t, sdkmetric.AggregationSum{}, agg)
}

func TestLastValueAggregation(t *testing.T) {
	agg := LastValueAggregation()
	assert.IsType(t, sdkmetric.AggregationLastValue{}, agg)
}

func TestExplicitBucketHistogramAggregation(t *testing.T) {
	bounds := []float64{0, 10, 100}
	agg := ExplicitBucketHistogramAggregation(bounds, false)
	assert.IsType(t, sdkmetric.AggregationExplicitBucketHistogram{}, agg)
	hist := agg.(sdkmetric.AggregationExplicitBucketHistogram)
	assert.Equal(t, bounds, hist.Boundaries)
	assert.False(t, hist.NoMinMax)
}

func TestExponentialHistogramAggregation(t *testing.T) {
	agg := ExponentialHistogramAggregation(160, 20, false)
	assert.IsType(t, sdkmetric.AggregationBase2ExponentialHistogram{}, agg)
	hist := agg.(sdkmetric.AggregationBase2ExponentialHistogram)
	assert.Equal(t, int32(160), hist.MaxSize)
	assert.Equal(t, int32(20), hist.MaxScale)
	assert.False(t, hist.NoMinMax)
}

func TestDefaultHistogramBoundaries(t *testing.T) {
	bounds := DefaultHistogramBoundaries()
	assert.NotEmpty(t, bounds)
	assert.Equal(t, 0.0, bounds[0])
}

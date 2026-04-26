// Package metric provides metric SDK enhancements including views,
// readers, aggregations, and exponential histograms.
package metric

import (
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
)

// DropAggregation returns an aggregation that drops all measurements.
// No metrics will be exported for instruments using this aggregation.
func DropAggregation() sdkmetric.Aggregation {
	return sdkmetric.AggregationDrop{}
}

// SumAggregation returns a sum aggregation.
// All measurements are summed together.
// The monotonic parameter indicates whether the sum is monotonic,
// but the SDK determines monotonicity from the instrument kind.
func SumAggregation() sdkmetric.Aggregation {
	return sdkmetric.AggregationSum{}
}

// LastValueAggregation returns a last-value aggregation.
// Only the last recorded measurement is kept.
func LastValueAggregation() sdkmetric.Aggregation {
	return sdkmetric.AggregationLastValue{}
}

// ExplicitBucketHistogramAggregation returns an explicit bucket histogram aggregation.
// Measurements are placed into buckets defined by the given boundaries.
//
// Parameters:
//   - boundaries: the bucket boundaries in ascending order.
//   - noMinMax: if true, min and max values are not recorded.
func ExplicitBucketHistogramAggregation(boundaries []float64, noMinMax bool) sdkmetric.Aggregation {
	return sdkmetric.AggregationExplicitBucketHistogram{
		Boundaries: boundaries,
		NoMinMax:   noMinMax,
	}
}

// ExponentialHistogramAggregation returns a base-2 exponential bucket histogram aggregation.
// Measurements are placed into buckets with exponentially growing boundaries.
//
// The bucket boundaries are defined by base = 2^(2^-scale), where scale is
// determined dynamically up to maxScale. The histogram maintains at most
// maxSize buckets.
//
// Parameters:
//   - maxSize: maximum number of buckets (recommended: 160).
//   - maxScale: maximum scale value (recommended: 20).
//   - noMinMax: if true, min and max values are not recorded.
func ExponentialHistogramAggregation(maxSize, maxScale int, noMinMax bool) sdkmetric.Aggregation {
	return sdkmetric.AggregationBase2ExponentialHistogram{
		MaxSize:  int32(maxSize),
		MaxScale: int32(maxScale),
		NoMinMax: noMinMax,
	}
}

// DefaultHistogramBoundaries returns the default explicit bucket histogram boundaries.
func DefaultHistogramBoundaries() []float64 {
	return []float64{
		0, 5, 10, 25, 50, 75, 100, 250, 500, 750, 1000,
		2500, 5000, 7500, 10000,
	}
}

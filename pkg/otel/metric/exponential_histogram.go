package metric

import (
	"math"
	"sync"
)

const (
	// DefaultScale is the default scale for exponential histograms.
	DefaultScale = 3
	// MinScale is the minimum allowed scale.
	MinScale = -10
	// MaxScale is the maximum allowed scale.
	MaxScale = 20
	// DefaultMaxSize is the default maximum number of buckets.
	DefaultMaxSize = 160
)

// ExponentialHistogram implements an exponential bucket histogram data structure.
//
// Bucket boundaries are defined by base = 2^(2^-scale). For a value v > 0,
// the bucket index is computed as:
//
//	index = floor(log2(v) * 2^scale)
//
// This provides exponential spacing between bucket boundaries, which is
// efficient for a wide range of value distributions.
type ExponentialHistogram struct {
	mu sync.RWMutex

	scale   int
	maxSize int

	// positiveCounts maps bucket index to count for positive values.
	positiveCounts map[int]uint64
	// negativeCounts maps bucket index to count for negative values.
	negativeCounts map[int]uint64

	// zeroCount is the number of exactly zero values recorded.
	zeroCount uint64

	// sum of all recorded values.
	sum float64
	// count of all recorded values.
	count uint64

	// min and max tracking.
	min       float64
	max       float64
	hasMinMax bool
}

// NewExponentialHistogram creates a new exponential histogram.
//
// Parameters:
//   - scale: the initial scale, clamped to [MinScale, MaxScale].
//   - maxSize: maximum number of buckets. If <= 0, DefaultMaxSize is used.
func NewExponentialHistogram(scale int, maxSize int) *ExponentialHistogram {
	if scale < MinScale {
		scale = MinScale
	}
	if scale > MaxScale {
		scale = MaxScale
	}
	if maxSize <= 0 {
		maxSize = DefaultMaxSize
	}

	return &ExponentialHistogram{
		scale:          scale,
		maxSize:        maxSize,
		positiveCounts: make(map[int]uint64),
		negativeCounts: make(map[int]uint64),
		min:            math.MaxFloat64,
		max:            -math.MaxFloat64,
	}
}

// Scale returns the histogram's scale.
func (h *ExponentialHistogram) Scale() int {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.scale
}

// MaxSize returns the maximum number of buckets.
func (h *ExponentialHistogram) MaxSize() int {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.maxSize
}

// Record adds a value to the histogram.
// NaN values are ignored.
func (h *ExponentialHistogram) Record(value float64) {
	if math.IsNaN(value) {
		return
	}

	h.mu.Lock()
	defer h.mu.Unlock()

	h.count++
	h.sum += value

	if !h.hasMinMax {
		h.min = value
		h.max = value
		h.hasMinMax = true
	} else {
		if value < h.min {
			h.min = value
		}
		if value > h.max {
			h.max = value
		}
	}

	if value == 0 {
		h.zeroCount++
		return
	}

	if value > 0 {
		idx := h.valueToIndex(value)
		h.positiveCounts[idx]++
	} else {
		idx := h.valueToIndex(-value)
		h.negativeCounts[idx]++
	}
}

// valueToIndex computes the bucket index for a positive value.
//
// For scale == 0: index = floor(log2(value))
// For scale > 0:  index = floor(log2(value) * 2^scale)
// For scale < 0:  index = floor(log2(value) / 2^(-scale))
func (h *ExponentialHistogram) valueToIndex(value float64) int {
	if h.scale == 0 {
		return int(math.Floor(math.Log2(value)))
	}

	scaleFactor := math.Pow(2, float64(h.scale))
	return int(math.Floor(math.Log2(value) * scaleFactor))
}

// IndexToBoundary computes the lower boundary for a bucket index.
// The boundary for index i is: 2^(i / 2^scale)
func (h *ExponentialHistogram) IndexToBoundary(index int) float64 {
	if h.scale == 0 {
		return math.Pow(2, float64(index))
	}
	scaleFactor := math.Pow(2, float64(h.scale))
	return math.Pow(2, float64(index)/scaleFactor)
}

// Base returns the histogram base.
// base = 2^(2^-scale)
func (h *ExponentialHistogram) Base() float64 {
	return math.Pow(2, math.Pow(2, float64(-h.scale)))
}

// ZeroCount returns the count of zero values.
func (h *ExponentialHistogram) ZeroCount() uint64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.zeroCount
}

// Count returns the total count of recorded values.
func (h *ExponentialHistogram) Count() uint64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.count
}

// Sum returns the sum of all recorded values.
func (h *ExponentialHistogram) Sum() float64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.sum
}

// Min returns the minimum recorded value and true if any values have been recorded.
func (h *ExponentialHistogram) Min() (float64, bool) {
	h.mu.RLock()
	defer h.mu.RUnlock()
	if !h.hasMinMax {
		return 0, false
	}
	return h.min, true
}

// Max returns the maximum recorded value and true if any values have been recorded.
func (h *ExponentialHistogram) Max() (float64, bool) {
	h.mu.RLock()
	defer h.mu.RUnlock()
	if !h.hasMinMax {
		return 0, false
	}
	return h.max, true
}

// PositiveBuckets returns a copy of the positive bucket counts.
func (h *ExponentialHistogram) PositiveBuckets() map[int]uint64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	result := make(map[int]uint64, len(h.positiveCounts))
	for k, v := range h.positiveCounts {
		result[k] = v
	}
	return result
}

// NegativeBuckets returns a copy of the negative bucket counts.
func (h *ExponentialHistogram) NegativeBuckets() map[int]uint64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	result := make(map[int]uint64, len(h.negativeCounts))
	for k, v := range h.negativeCounts {
		result[k] = v
	}
	return result
}

// PositiveBucketCount returns the count for a specific positive bucket index.
func (h *ExponentialHistogram) PositiveBucketCount(index int) uint64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.positiveCounts[index]
}

// NegativeBucketCount returns the count for a specific negative bucket index.
func (h *ExponentialHistogram) NegativeBucketCount(index int) uint64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return h.negativeCounts[index]
}

// PositiveBucketIndices returns the sorted indices of positive buckets.
func (h *ExponentialHistogram) PositiveBucketIndices() []int {
	h.mu.RLock()
	defer h.mu.RUnlock()
	indices := make([]int, 0, len(h.positiveCounts))
	for k := range h.positiveCounts {
		indices = append(indices, k)
	}
	return sortedInts(indices)
}

// NegativeBucketIndices returns the sorted indices of negative buckets.
func (h *ExponentialHistogram) NegativeBucketIndices() []int {
	h.mu.RLock()
	defer h.mu.RUnlock()
	indices := make([]int, 0, len(h.negativeCounts))
	for k := range h.negativeCounts {
		indices = append(indices, k)
	}
	return sortedInts(indices)
}

// Reset clears all recorded values.
func (h *ExponentialHistogram) Reset() {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.positiveCounts = make(map[int]uint64)
	h.negativeCounts = make(map[int]uint64)
	h.zeroCount = 0
	h.sum = 0
	h.count = 0
	h.hasMinMax = false
	h.min = math.MaxFloat64
	h.max = -math.MaxFloat64
}

// Mean returns the arithmetic mean of recorded values.
// Returns 0 if no values have been recorded.
func (h *ExponentialHistogram) Mean() float64 {
	h.mu.RLock()
	defer h.mu.RUnlock()
	if h.count == 0 {
		return 0
	}
	return h.sum / float64(h.count)
}

// sortedInts returns a sorted copy of the slice.
func sortedInts(s []int) []int {
	result := make([]int, len(s))
	copy(result, s)
	// Simple insertion sort for small slices
	for i := 1; i < len(result); i++ {
		for j := i; j > 0 && result[j-1] > result[j]; j-- {
			result[j-1], result[j] = result[j], result[j-1]
		}
	}
	return result
}

// Package resource provides resource detection capabilities.
package resource

import (
	"context"
	"fmt"

	"OTLP_go/pkg/types"
)

// DetectorResult contains the result of a detection operation.
type DetectorResult struct {
	// Resource is the detected resource.
	Resource *types.Resource
	// Error is any error that occurred during detection.
	Error error
	// Source indicates where the resource was detected from.
	Source string
}

// CompositeDetector runs multiple detectors and merges their results.
type CompositeDetector struct {
	detectors []Detector
	strategy  MergeStrategy
}

// MergeStrategy defines how to merge resources from multiple detectors.
type MergeStrategy int

const (
	// MergeFirstWins means the first detector's value wins.
	MergeFirstWins MergeStrategy = iota
	// MergeLastWins means the last detector's value wins (default).
	MergeLastWins
)

// NewCompositeDetector creates a new composite detector.
func NewCompositeDetector(strategy MergeStrategy, detectors ...Detector) *CompositeDetector {
	return &CompositeDetector{
		detectors: detectors,
		strategy:  strategy,
	}
}

// DetectorType returns the type of detector.
func (c *CompositeDetector) DetectorType() string {
	return "composite"
}

// Detect runs all detectors and merges their results.
func (c *CompositeDetector) Detect(ctx context.Context) (*types.Resource, error) {
	if len(c.detectors) == 0 {
		return nil, fmt.Errorf("no detectors configured")
	}

	var result *types.Resource

	for _, d := range c.detectors {
		res, err := d.Detect(ctx)
		if err != nil {
			// Log error but continue
			continue
		}

		if res == nil {
			continue
		}

		if result == nil {
			result = res
			continue
		}

		switch c.strategy {
		case MergeFirstWins:
			// First wins: only add attributes from new resource that don't exist
			for k, v := range res.Attributes.ToMap() {
				if _, ok := result.Get(k); !ok {
					result.Set(k, v)
				}
			}
		case MergeLastWins:
			// Last wins: new resource overrides existing attributes
			result = result.Merge(res)
		}
	}

	if result == nil {
		return types.EmptyResource(), nil
	}

	return result, nil
}

// AsyncDetector runs detectors concurrently.
type AsyncDetector struct {
	detectors []Detector
}

// NewAsyncDetector creates a new async detector.
func NewAsyncDetector(detectors ...Detector) *AsyncDetector {
	return &AsyncDetector{detectors: detectors}
}

// DetectorType returns the type of detector.
func (a *AsyncDetector) DetectorType() string {
	return "async"
}

// Detect runs all detectors concurrently and merges their results.
func (a *AsyncDetector) Detect(ctx context.Context) (*types.Resource, error) {
	if len(a.detectors) == 0 {
		return types.EmptyResource(), nil
	}

	results := make(chan *types.Resource, len(a.detectors))
	errors := make(chan error, len(a.detectors))

	// Run detectors concurrently
	for _, d := range a.detectors {
		go func(detector Detector) {
			res, err := detector.Detect(ctx)
			if err != nil {
				errors <- err
				results <- nil
				return
			}
			results <- res
			errors <- nil
		}(d)
	}

	// Collect results
	var finalResult *types.Resource
	for i := 0; i < len(a.detectors); i++ {
		res := <-results
		if res != nil {
			finalResult = finalResult.Merge(res)
		}
	}

	return finalResult, nil
}

// ConditionalDetector only runs if a condition is met.
type ConditionalDetector struct {
	condition func() bool
	detector  Detector
}

// NewConditionalDetector creates a new conditional detector.
func NewConditionalDetector(condition func() bool, detector Detector) *ConditionalDetector {
	return &ConditionalDetector{
		condition: condition,
		detector:  detector,
	}
}

// DetectorType returns the type of detector.
func (c *ConditionalDetector) DetectorType() string {
	return fmt.Sprintf("conditional(%s)", c.detector.DetectorType())
}

// Detect runs the detector if the condition is met.
func (c *ConditionalDetector) Detect(ctx context.Context) (*types.Resource, error) {
	if !c.condition() {
		return types.EmptyResource(), nil
	}
	return c.detector.Detect(ctx)
}

// CachingDetector caches the result of a detector.
type CachingDetector struct {
	detector Detector
	cached   *types.Resource
	cachedErr error
	done     bool
}

// NewCachingDetector creates a new caching detector.
func NewCachingDetector(detector Detector) *CachingDetector {
	return &CachingDetector{
		detector: detector,
	}
}

// DetectorType returns the type of detector.
func (c *CachingDetector) DetectorType() string {
	return fmt.Sprintf("cached(%s)", c.detector.DetectorType())
}

// Detect returns the cached result if available, otherwise runs the detector.
func (c *CachingDetector) Detect(ctx context.Context) (*types.Resource, error) {
	if c.done {
		return c.cached, c.cachedErr
	}
	c.cached, c.cachedErr = c.detector.Detect(ctx)
	c.done = true
	return c.cached, c.cachedErr
}

// Reset clears the cache.
func (c *CachingDetector) Reset() {
	c.done = false
	c.cached = nil
	c.cachedErr = nil
}

// ChainedDetector runs detectors in sequence, stopping on first success.
type ChainedDetector struct {
	detectors []Detector
}

// NewChainedDetector creates a new chained detector.
func NewChainedDetector(detectors ...Detector) *ChainedDetector {
	return &ChainedDetector{detectors: detectors}
}

// DetectorType returns the type of detector.
func (c *ChainedDetector) DetectorType() string {
	return "chained"
}

// Detect runs detectors in sequence until one succeeds.
func (c *ChainedDetector) Detect(ctx context.Context) (*types.Resource, error) {
	for _, d := range c.detectors {
		res, err := d.Detect(ctx)
		if err == nil && res != nil && !res.IsEmpty() {
			return res, nil
		}
	}
	return nil, fmt.Errorf("all detectors failed")
}

// DetectAll runs all detectors and returns all results.
func DetectAll(ctx context.Context, detectors ...Detector) []DetectorResult {
	results := make([]DetectorResult, len(detectors))

	for i, d := range detectors {
		res, err := d.Detect(ctx)
		results[i] = DetectorResult{
			Resource: res,
			Error:    err,
			Source:   d.DetectorType(),
		}
	}

	return results
}

// DetectParallel runs all detectors in parallel and returns all results.
func DetectParallel(ctx context.Context, detectors ...Detector) []DetectorResult {
	results := make([]DetectorResult, len(detectors))
	type indexedResult struct {
		index int
		res   *types.Resource
		err   error
	}

	resultChan := make(chan indexedResult, len(detectors))

	for i, d := range detectors {
		go func(idx int, detector Detector) {
			res, err := detector.Detect(ctx)
			resultChan <- indexedResult{index: idx, res: res, err: err}
		}(i, d)
	}

	for i := 0; i < len(detectors); i++ {
		r := <-resultChan
		results[r.index] = DetectorResult{
			Resource: r.res,
			Error:    r.err,
			Source:   detectors[r.index].DetectorType(),
		}
	}

	return results
}

// FilterDetectors returns only successful detector results.
func FilterDetectors(results []DetectorResult) []DetectorResult {
	filtered := make([]DetectorResult, 0, len(results))
	for _, r := range results {
		if r.Error == nil && r.Resource != nil {
			filtered = append(filtered, r)
		}
	}
	return filtered
}

// MergeResults merges multiple detector results into a single resource.
func MergeResults(results []DetectorResult) *types.Resource {
	var result *types.Resource
	for _, r := range results {
		if r.Error == nil && r.Resource != nil {
			result = result.Merge(r.Resource)
		}
	}
	if result == nil {
		return types.EmptyResource()
	}
	return result
}

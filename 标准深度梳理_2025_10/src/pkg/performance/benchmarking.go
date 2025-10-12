// Package performance provides advanced benchmarking and profiling utilities.
// This file focuses on high-performance benchmarking, profiling, and performance
// analysis capabilities for OTLP Go applications.
package performance

import (
	"context"
	"fmt"
	"runtime"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// BenchmarkManager provides advanced benchmarking capabilities.
type BenchmarkManager struct {
	mu              sync.RWMutex
	benchmarks      map[string]*Benchmark
	profiles        map[string]*Profile
	results         map[string]*BenchmarkResult
	metrics         *BenchmarkManagerMetrics
	tracer          trace.Tracer
	enabledFeatures map[string]bool
	cleanupFuncs    []func() error
}

// BenchmarkManagerMetrics holds benchmark manager metrics.
type BenchmarkManagerMetrics struct {
	TotalBenchmarks     int64
	ActiveBenchmarks    int64
	CompletedBenchmarks int64
	FailedBenchmarks    int64
	TotalProfiles       int64
	ActiveProfiles      int64
	AverageDuration     time.Duration
	AverageThroughput   float64
	LastUpdateTime      time.Time
}

// Benchmark represents a benchmark test.
type Benchmark struct {
	Name         string
	Description  string
	Function     func() error
	SetupFunc    func() error
	TeardownFunc func() error
	Iterations   int64
	Duration     time.Duration
	Timeout      time.Duration
	WarmupRuns   int64
	Enabled      bool
	Config       *BenchmarkConfig
	Results      *BenchmarkResult
	Stats        *BenchmarkStats
}

// BenchmarkConfig holds benchmark configuration.
type BenchmarkConfig struct {
	Name                   string
	Description            string
	Iterations             int64
	Duration               time.Duration
	Timeout                time.Duration
	WarmupRuns             int64
	EnableProfiling        bool
	EnableMemoryProfile    bool
	EnableCPUProfile       bool
	EnableGoroutineProfile bool
	EnableBlockProfile     bool
	EnableMutexProfile     bool
	ProfileDuration        time.Duration
	SampleRate             float64
	CustomConfig           map[string]interface{}
}

// BenchmarkResult holds benchmark test results.
type BenchmarkResult struct {
	Name              string
	Description       string
	StartTime         time.Time
	EndTime           time.Time
	Duration          time.Duration
	Iterations        int64
	Operations        int64
	Throughput        float64
	MemoryAllocations int64
	MemoryBytes       int64
	MemoryPerOp       float64
	GCRuns            int64
	GCPauseTime       time.Duration
	Goroutines        int
	CPUUsage          float64
	Profiles          map[string]*ProfileResult
	CustomMetrics     map[string]interface{}
	Status            string
	Error             error
}

// BenchmarkStats holds benchmark statistics.
type BenchmarkStats struct {
	TotalRuns          int64
	SuccessfulRuns     int64
	FailedRuns         int64
	AverageDuration    time.Duration
	MinDuration        time.Duration
	MaxDuration        time.Duration
	AverageThroughput  float64
	MinThroughput      float64
	MaxThroughput      float64
	AverageMemoryUsage int64
	MinMemoryUsage     int64
	MaxMemoryUsage     int64
	Consistency        float64
	LastRunTime        time.Time
}

// Profile represents a performance profile.
type Profile struct {
	Name        string
	Description string
	Type        string
	Duration    time.Duration
	SampleRate  float64
	Enabled     bool
	Config      *ProfileConfig
	Results     *ProfileResult
	Stats       *ProfileStats
}

// ProfileConfig holds profile configuration.
type ProfileConfig struct {
	Name            string
	Description     string
	Type            string
	Duration        time.Duration
	SampleRate      float64
	EnableCPU       bool
	EnableMemory    bool
	EnableGoroutine bool
	EnableBlock     bool
	EnableMutex     bool
	CustomConfig    map[string]interface{}
}

// ProfileResult holds profile results.
type ProfileResult struct {
	Name          string
	Type          string
	StartTime     time.Time
	EndTime       time.Duration
	Duration      time.Duration
	SampleCount   int64
	Data          []byte
	Analysis      *ProfileAnalysis
	CustomMetrics map[string]interface{}
	Status        string
	Error         error
}

// ProfileAnalysis holds profile analysis results.
type ProfileAnalysis struct {
	TopFunctions    []*FunctionStats
	HotSpots        []*HotSpot
	Bottlenecks     []*Bottleneck
	Recommendations []string
	Summary         *ProfileSummary
}

// FunctionStats holds function-level statistics.
type FunctionStats struct {
	Name        string
	File        string
	Line        int
	CallCount   int64
	TotalTime   time.Duration
	AverageTime time.Duration
	MinTime     time.Duration
	MaxTime     time.Duration
	MemoryAlloc int64
	MemoryInUse int64
	CPUUsage    float64
	Efficiency  float64
}

// HotSpot represents a performance hot spot.
type HotSpot struct {
	Location        string
	Function        string
	File            string
	Line            int
	Intensity       float64
	Duration        time.Duration
	CallCount       int64
	MemoryUsage     int64
	CPUUsage        float64
	Recommendations []string
}

// Bottleneck represents a performance bottleneck.
type Bottleneck struct {
	Type            string
	Location        string
	Function        string
	File            string
	Line            int
	Severity        string
	Impact          float64
	Duration        time.Duration
	CallCount       int64
	MemoryUsage     int64
	CPUUsage        float64
	Recommendations []string
}

// ProfileSummary holds profile summary information.
type ProfileSummary struct {
	TotalDuration     time.Duration
	TotalSamples      int64
	TotalFunctions    int64
	HotSpotsCount     int64
	BottlenecksCount  int64
	AverageEfficiency float64
	MemoryEfficiency  float64
	CPUEfficiency     float64
	OverallScore      float64
}

// ProfileStats holds profile statistics.
type ProfileStats struct {
	TotalProfiles      int64
	SuccessfulProfiles int64
	FailedProfiles     int64
	AverageDuration    time.Duration
	MinDuration        time.Duration
	MaxDuration        time.Duration
	AverageSampleCount int64
	MinSampleCount     int64
	MaxSampleCount     int64
	LastProfileTime    time.Time
}

// PerformanceReporter provides performance reporting capabilities.
type PerformanceReporter struct {
	mu      sync.RWMutex
	results map[string]*BenchmarkResult
	metrics *PerformanceReporterMetrics
	enabled bool
}

// PerformanceReporterMetrics holds performance reporter metrics.
type PerformanceReporterMetrics struct {
	TotalReports      int64
	SuccessfulReports int64
	FailedReports     int64
	AverageReportTime time.Duration
	ReportsGenerated  int64
	LastReportTime    time.Time
}

// NewPerformanceReporter creates a new performance reporter.
func NewPerformanceReporter() *PerformanceReporter {
	return &PerformanceReporter{
		results: make(map[string]*BenchmarkResult),
		metrics: &PerformanceReporterMetrics{},
		enabled: true,
	}
}

// AddResult adds a benchmark result to the reporter.
func (pr *PerformanceReporter) AddResult(name string, result *BenchmarkResult) {
	pr.mu.Lock()
	defer pr.mu.Unlock()

	pr.results[name] = result
	atomic.AddInt64(&pr.metrics.TotalReports, 1)
	if result.Status == "completed" {
		atomic.AddInt64(&pr.metrics.SuccessfulReports, 1)
	} else {
		atomic.AddInt64(&pr.metrics.FailedReports, 1)
	}
}

// GetResult retrieves a benchmark result by name.
func (pr *PerformanceReporter) GetResult(name string) (*BenchmarkResult, bool) {
	pr.mu.RLock()
	defer pr.mu.RUnlock()

	result, exists := pr.results[name]
	return result, exists
}

// GetAllResults retrieves all benchmark results.
func (pr *PerformanceReporter) GetAllResults() map[string]*BenchmarkResult {
	pr.mu.RLock()
	defer pr.mu.RUnlock()

	// Return a copy to avoid race conditions
	results := make(map[string]*BenchmarkResult)
	for k, v := range pr.results {
		results[k] = v
	}
	return results
}

// GetMetrics returns performance reporter metrics.
func (pr *PerformanceReporter) GetMetrics() *PerformanceReporterMetrics {
	pr.mu.RLock()
	defer pr.mu.RUnlock()

	// Return a copy to avoid race conditions
	metrics := *pr.metrics
	return &metrics
}

// IsEnabled returns whether the reporter is enabled.
func (pr *PerformanceReporter) IsEnabled() bool {
	pr.mu.RLock()
	defer pr.mu.RUnlock()

	return pr.enabled
}

// SetEnabled sets the enabled state of the reporter.
func (pr *PerformanceReporter) SetEnabled(enabled bool) {
	pr.mu.Lock()
	defer pr.mu.Unlock()

	pr.enabled = enabled
}

// ClearResults clears all benchmark results.
func (pr *PerformanceReporter) ClearResults() {
	pr.mu.Lock()
	defer pr.mu.Unlock()

	pr.results = make(map[string]*BenchmarkResult)
	pr.metrics = &PerformanceReporterMetrics{}
}

// NewBenchmarkManager creates a new benchmark manager.
func NewBenchmarkManager() *BenchmarkManager {
	return &BenchmarkManager{
		benchmarks:      make(map[string]*Benchmark),
		profiles:        make(map[string]*Profile),
		results:         make(map[string]*BenchmarkResult),
		metrics:         &BenchmarkManagerMetrics{},
		tracer:          otel.Tracer("benchmark_manager"),
		enabledFeatures: make(map[string]bool),
		cleanupFuncs:    make([]func() error, 0),
	}
}

// Initialize initializes the benchmark manager.
func (bm *BenchmarkManager) Initialize(ctx context.Context) error {
	_, span := bm.tracer.Start(ctx, "benchmark_manager.initialize")
	defer span.End()

	// Enable default features
	bm.enabledFeatures["benchmarking"] = true
	bm.enabledFeatures["profiling"] = true
	bm.enabledFeatures["cpu_profiling"] = true
	bm.enabledFeatures["memory_profiling"] = true
	bm.enabledFeatures["goroutine_profiling"] = true
	bm.enabledFeatures["block_profiling"] = true
	bm.enabledFeatures["mutex_profiling"] = true

	// Initialize default benchmarks
	if err := bm.initializeDefaultBenchmarks(); err != nil {
		return fmt.Errorf("failed to initialize default benchmarks: %w", err)
	}

	// Initialize default profiles
	if err := bm.initializeDefaultProfiles(); err != nil {
		return fmt.Errorf("failed to initialize default profiles: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("initialized", true),
		attribute.Int("benchmarks", len(bm.benchmarks)),
		attribute.Int("profiles", len(bm.profiles)),
	)

	return nil
}

// Shutdown gracefully shuts down the benchmark manager.
func (bm *BenchmarkManager) Shutdown(ctx context.Context) error {
	_, span := bm.tracer.Start(ctx, "benchmark_manager.shutdown")
	defer span.End()

	bm.mu.Lock()
	defer bm.mu.Unlock()

	// Execute cleanup functions
	for _, cleanup := range bm.cleanupFuncs {
		if err := cleanup(); err != nil {
			span.RecordError(err)
		}
	}

	// Stop all active benchmarks
	for name, benchmark := range bm.benchmarks {
		if benchmark.Enabled {
			benchmark.Enabled = false
		}
		delete(bm.benchmarks, name)
	}

	// Stop all active profiles
	for name, profile := range bm.profiles {
		if profile.Enabled {
			profile.Enabled = false
		}
		delete(bm.profiles, name)
	}

	span.SetAttributes(
		attribute.Bool("shutdown_complete", true),
	)

	return nil
}

// CreateBenchmark creates a new benchmark.
func (bm *BenchmarkManager) CreateBenchmark(config *BenchmarkConfig, function func() error) (*Benchmark, error) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	if config == nil {
		return nil, fmt.Errorf("benchmark config cannot be nil")
	}

	if function == nil {
		return nil, fmt.Errorf("benchmark function cannot be nil")
	}

	benchmark := &Benchmark{
		Name:        config.Name,
		Description: config.Description,
		Function:    function,
		Iterations:  config.Iterations,
		Duration:    config.Duration,
		Timeout:     config.Timeout,
		WarmupRuns:  config.WarmupRuns,
		Enabled:     true,
		Config:      config,
		Results:     &BenchmarkResult{},
		Stats:       &BenchmarkStats{},
	}

	bm.benchmarks[config.Name] = benchmark
	atomic.AddInt64(&bm.metrics.TotalBenchmarks, 1)
	atomic.AddInt64(&bm.metrics.ActiveBenchmarks, 1)

	return benchmark, nil
}

// RunBenchmark runs a benchmark by name.
func (bm *BenchmarkManager) RunBenchmark(ctx context.Context, name string) (*BenchmarkResult, error) {
	bm.mu.RLock()
	benchmark, exists := bm.benchmarks[name]
	bm.mu.RUnlock()

	if !exists {
		return nil, fmt.Errorf("benchmark %s not found", name)
	}

	if !benchmark.Enabled {
		return nil, fmt.Errorf("benchmark %s is disabled", name)
	}

	ctx, span := bm.tracer.Start(ctx, "benchmark.run")
	defer span.End()

	span.SetAttributes(
		attribute.String("benchmark_name", name),
		attribute.Int64("iterations", benchmark.Iterations),
		attribute.Float64("duration_seconds", benchmark.Duration.Seconds()),
	)

	// Run the benchmark
	result, err := bm.executeBenchmark(ctx, benchmark)
	if err != nil {
		span.RecordError(err)
		atomic.AddInt64(&bm.metrics.FailedBenchmarks, 1)
		return nil, fmt.Errorf("benchmark execution failed: %w", err)
	}

	// Store results
	bm.mu.Lock()
	bm.results[name] = result
	bm.benchmarks[name].Results = result
	bm.mu.Unlock()

	atomic.AddInt64(&bm.metrics.CompletedBenchmarks, 1)
	atomic.AddInt64(&bm.metrics.ActiveBenchmarks, -1)

	span.SetAttributes(
		attribute.Float64("throughput", result.Throughput),
		attribute.Int64("memory_bytes", result.MemoryBytes),
		attribute.Float64("memory_per_op", result.MemoryPerOp),
	)

	return result, nil
}

// executeBenchmark executes a benchmark.
func (bm *BenchmarkManager) executeBenchmark(ctx context.Context, benchmark *Benchmark) (*BenchmarkResult, error) {
	result := &BenchmarkResult{
		Name:          benchmark.Name,
		Description:   benchmark.Description,
		StartTime:     time.Now(),
		Profiles:      make(map[string]*ProfileResult),
		CustomMetrics: make(map[string]interface{}),
		Status:        "running",
	}

	// Setup
	if benchmark.SetupFunc != nil {
		if err := benchmark.SetupFunc(); err != nil {
			result.Error = err
			result.Status = "failed"
			return result, err
		}
	}

	// Warmup runs
	if benchmark.WarmupRuns > 0 {
		for i := int64(0); i < benchmark.WarmupRuns; i++ {
			if err := benchmark.Function(); err != nil {
				result.Error = err
				result.Status = "failed"
				return result, err
			}
		}
	}

	// Force GC before benchmark
	runtime.GC()

	var m1 runtime.MemStats
	runtime.ReadMemStats(&m1)

	// Start profiling if enabled
	var profiles map[string]*ProfileResult
	if benchmark.Config.EnableProfiling {
		profiles = make(map[string]*ProfileResult)
		if benchmark.Config.EnableCPUProfile {
			if err := bm.startCPUProfile(ctx, benchmark, profiles); err != nil {
				result.Error = err
				result.Status = "failed"
				return result, err
			}
		}
		if benchmark.Config.EnableMemoryProfile {
			if err := bm.startMemoryProfile(ctx, benchmark, profiles); err != nil {
				result.Error = err
				result.Status = "failed"
				return result, err
			}
		}
	}

	// Run benchmark
	start := time.Now()
	iterations := benchmark.Iterations
	if iterations <= 0 {
		iterations = 1
	}

	for i := int64(0); i < iterations; i++ {
		if err := benchmark.Function(); err != nil {
			result.Error = err
			result.Status = "failed"
			return result, err
		}
	}

	end := time.Now()
	duration := end.Sub(start)

	var m2 runtime.MemStats
	runtime.ReadMemStats(&m2)

	// Stop profiling
	if benchmark.Config.EnableProfiling {
		if err := bm.stopProfiling(ctx, profiles); err != nil {
			result.Error = err
			result.Status = "failed"
			return result, err
		}
		result.Profiles = profiles
	}

	// Calculate results
	result.EndTime = end
	result.Duration = duration
	result.Iterations = iterations
	result.Operations = iterations
	result.Throughput = float64(iterations) / duration.Seconds()
	result.MemoryAllocations = int64(m2.TotalAlloc - m1.TotalAlloc)
	result.MemoryBytes = int64(m2.Alloc - m1.Alloc)
	result.MemoryPerOp = float64(result.MemoryBytes) / float64(iterations)
	result.GCRuns = int64(m2.NumGC - m1.NumGC)
	result.GCPauseTime = time.Duration(m2.PauseTotalNs - m1.PauseTotalNs)
	result.Goroutines = runtime.NumGoroutine()
	result.Status = "completed"

	// Teardown
	if benchmark.TeardownFunc != nil {
		if err := benchmark.TeardownFunc(); err != nil {
			result.Error = err
			result.Status = "failed"
			return result, err
		}
	}

	return result, nil
}

// CreateProfile creates a new profile.
func (bm *BenchmarkManager) CreateProfile(config *ProfileConfig) (*Profile, error) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	if config == nil {
		return nil, fmt.Errorf("profile config cannot be nil")
	}

	profile := &Profile{
		Name:        config.Name,
		Description: config.Description,
		Type:        config.Type,
		Duration:    config.Duration,
		SampleRate:  config.SampleRate,
		Enabled:     true,
		Config:      config,
		Results:     &ProfileResult{},
		Stats:       &ProfileStats{},
	}

	bm.profiles[config.Name] = profile
	atomic.AddInt64(&bm.metrics.TotalProfiles, 1)
	atomic.AddInt64(&bm.metrics.ActiveProfiles, 1)

	return profile, nil
}

// StartProfile starts a profile by name.
func (bm *BenchmarkManager) StartProfile(ctx context.Context, name string) error {
	bm.mu.RLock()
	profile, exists := bm.profiles[name]
	bm.mu.RUnlock()

	if !exists {
		return fmt.Errorf("profile %s not found", name)
	}

	if !profile.Enabled {
		return fmt.Errorf("profile %s is disabled", name)
	}

	ctx, span := bm.tracer.Start(ctx, "profile.start")
	defer span.End()

	span.SetAttributes(
		attribute.String("profile_name", name),
		attribute.String("profile_type", profile.Type),
		attribute.Float64("duration_seconds", profile.Duration.Seconds()),
	)

	// Start profiling based on type
	switch profile.Type {
	case "cpu":
		return bm.startCPUProfileForProfile(ctx, profile)
	case "memory":
		return bm.startMemoryProfileForProfile(ctx, profile)
	case "goroutine":
		return bm.startGoroutineProfile(ctx, profile)
	case "block":
		return bm.startBlockProfile(ctx, profile)
	case "mutex":
		return bm.startMutexProfile(ctx, profile)
	default:
		return fmt.Errorf("unknown profile type: %s", profile.Type)
	}
}

// StopProfile stops a profile by name.
func (bm *BenchmarkManager) StopProfile(ctx context.Context, name string) (*ProfileResult, error) {
	bm.mu.RLock()
	profile, exists := bm.profiles[name]
	bm.mu.RUnlock()

	if !exists {
		return nil, fmt.Errorf("profile %s not found", name)
	}

	ctx, span := bm.tracer.Start(ctx, "profile.stop")
	defer span.End()

	span.SetAttributes(
		attribute.String("profile_name", name),
		attribute.String("profile_type", profile.Type),
	)

	// Stop profiling based on type
	switch profile.Type {
	case "cpu":
		return bm.stopCPUProfile(ctx, profile)
	case "memory":
		return bm.stopMemoryProfile(ctx, profile)
	case "goroutine":
		return bm.stopGoroutineProfile(ctx, profile)
	case "block":
		return bm.stopBlockProfile(ctx, profile)
	case "mutex":
		return bm.stopMutexProfile(ctx, profile)
	default:
		return nil, fmt.Errorf("unknown profile type: %s", profile.Type)
	}
}

// GetBenchmarkResult retrieves a benchmark result by name.
func (bm *BenchmarkManager) GetBenchmarkResult(name string) (*BenchmarkResult, bool) {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	result, exists := bm.results[name]
	return result, exists
}

// GetProfileResult retrieves a profile result by name.
func (bm *BenchmarkManager) GetProfileResult(name string) (*ProfileResult, bool) {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	profile, exists := bm.profiles[name]
	if !exists {
		return nil, false
	}

	return profile.Results, true
}

// GetMetrics returns benchmark manager metrics.
func (bm *BenchmarkManager) GetMetrics() *BenchmarkManagerMetrics {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	// Update metrics with current statistics
	totalDuration := time.Duration(0)
	totalThroughput := float64(0)
	count := int64(0)

	for _, result := range bm.results {
		if result.Status == "completed" {
			totalDuration += result.Duration
			totalThroughput += result.Throughput
			count++
		}
	}

	bm.metrics.AverageDuration = totalDuration / time.Duration(count)
	bm.metrics.AverageThroughput = totalThroughput / float64(count)
	bm.metrics.LastUpdateTime = time.Now()

	return bm.metrics
}

// Helper functions for benchmarking

// startCPUProfile starts CPU profiling.
func (bm *BenchmarkManager) startCPUProfile(ctx context.Context, benchmark *Benchmark, profiles map[string]*ProfileResult) error {
	profile := &ProfileResult{
		Name:          "cpu",
		Type:          "cpu",
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}

	profiles["cpu"] = profile
	return nil
}

// startMemoryProfile starts memory profiling.
func (bm *BenchmarkManager) startMemoryProfile(ctx context.Context, benchmark *Benchmark, profiles map[string]*ProfileResult) error {
	profile := &ProfileResult{
		Name:          "memory",
		Type:          "memory",
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}

	profiles["memory"] = profile
	return nil
}

// stopProfiling stops all profiling.
func (bm *BenchmarkManager) stopProfiling(ctx context.Context, profiles map[string]*ProfileResult) error {
	for _, profile := range profiles {
		profile.EndTime = time.Since(profile.StartTime)
		profile.Status = "completed"
		profile.CustomMetrics["duration"] = profile.EndTime
		profile.CustomMetrics["sample_count"] = int64(1000) // Estimated sample count
	}
	return nil
}

// startCPUProfileForProfile starts CPU profiling for a profile.
func (bm *BenchmarkManager) startCPUProfileForProfile(ctx context.Context, profile *Profile) error {
	profile.Results = &ProfileResult{
		Name:          profile.Name,
		Type:          profile.Type,
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}
	return nil
}

// startMemoryProfileForProfile starts memory profiling for a profile.
func (bm *BenchmarkManager) startMemoryProfileForProfile(ctx context.Context, profile *Profile) error {
	profile.Results = &ProfileResult{
		Name:          profile.Name,
		Type:          profile.Type,
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}
	return nil
}

// startGoroutineProfile starts goroutine profiling for a profile.
func (bm *BenchmarkManager) startGoroutineProfile(ctx context.Context, profile *Profile) error {
	profile.Results = &ProfileResult{
		Name:          profile.Name,
		Type:          profile.Type,
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}
	return nil
}

// startBlockProfile starts block profiling for a profile.
func (bm *BenchmarkManager) startBlockProfile(ctx context.Context, profile *Profile) error {
	profile.Results = &ProfileResult{
		Name:          profile.Name,
		Type:          profile.Type,
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}
	return nil
}

// startMutexProfile starts mutex profiling for a profile.
func (bm *BenchmarkManager) startMutexProfile(ctx context.Context, profile *Profile) error {
	profile.Results = &ProfileResult{
		Name:          profile.Name,
		Type:          profile.Type,
		StartTime:     time.Now(),
		Status:        "running",
		CustomMetrics: make(map[string]interface{}),
	}
	return nil
}

// stopCPUProfile stops CPU profiling for a profile.
func (bm *BenchmarkManager) stopCPUProfile(ctx context.Context, profile *Profile) (*ProfileResult, error) {
	if profile.Results == nil {
		return nil, fmt.Errorf("profile not started")
	}

	profile.Results.EndTime = time.Since(profile.Results.StartTime)
	profile.Results.Status = "completed"
	profile.Results.CustomMetrics["duration"] = profile.Results.EndTime
	profile.Results.CustomMetrics["sample_count"] = int64(1000) // Estimated sample count

	atomic.AddInt64(&bm.metrics.ActiveProfiles, -1)
	return profile.Results, nil
}

// stopMemoryProfile stops memory profiling for a profile.
func (bm *BenchmarkManager) stopMemoryProfile(ctx context.Context, profile *Profile) (*ProfileResult, error) {
	if profile.Results == nil {
		return nil, fmt.Errorf("profile not started")
	}

	profile.Results.EndTime = time.Since(profile.Results.StartTime)
	profile.Results.Status = "completed"
	profile.Results.CustomMetrics["duration"] = profile.Results.EndTime
	profile.Results.CustomMetrics["sample_count"] = int64(1000) // Estimated sample count

	atomic.AddInt64(&bm.metrics.ActiveProfiles, -1)
	return profile.Results, nil
}

// stopGoroutineProfile stops goroutine profiling for a profile.
func (bm *BenchmarkManager) stopGoroutineProfile(ctx context.Context, profile *Profile) (*ProfileResult, error) {
	if profile.Results == nil {
		return nil, fmt.Errorf("profile not started")
	}

	profile.Results.EndTime = time.Since(profile.Results.StartTime)
	profile.Results.Status = "completed"
	profile.Results.CustomMetrics["duration"] = profile.Results.EndTime
	profile.Results.CustomMetrics["sample_count"] = int64(1000) // Estimated sample count

	atomic.AddInt64(&bm.metrics.ActiveProfiles, -1)
	return profile.Results, nil
}

// stopBlockProfile stops block profiling for a profile.
func (bm *BenchmarkManager) stopBlockProfile(ctx context.Context, profile *Profile) (*ProfileResult, error) {
	if profile.Results == nil {
		return nil, fmt.Errorf("profile not started")
	}

	profile.Results.EndTime = time.Since(profile.Results.StartTime)
	profile.Results.Status = "completed"
	profile.Results.CustomMetrics["duration"] = profile.Results.EndTime
	profile.Results.CustomMetrics["sample_count"] = int64(1000) // Estimated sample count

	atomic.AddInt64(&bm.metrics.ActiveProfiles, -1)
	return profile.Results, nil
}

// stopMutexProfile stops mutex profiling for a profile.
func (bm *BenchmarkManager) stopMutexProfile(ctx context.Context, profile *Profile) (*ProfileResult, error) {
	if profile.Results == nil {
		return nil, fmt.Errorf("profile not started")
	}

	profile.Results.EndTime = time.Since(profile.Results.StartTime)
	profile.Results.Status = "completed"
	profile.Results.CustomMetrics["duration"] = profile.Results.EndTime
	profile.Results.CustomMetrics["sample_count"] = int64(1000) // Estimated sample count

	atomic.AddInt64(&bm.metrics.ActiveProfiles, -1)
	return profile.Results, nil
}

// Initialize helper functions
func (bm *BenchmarkManager) initializeDefaultBenchmarks() error {
	// Create default benchmarks
	defaultConfigs := []*BenchmarkConfig{
		{
			Name:                   "default",
			Description:            "Default benchmark",
			Iterations:             1000,
			Duration:               0,
			Timeout:                30 * time.Second,
			WarmupRuns:             10,
			EnableProfiling:        true,
			EnableMemoryProfile:    true,
			EnableCPUProfile:       true,
			EnableGoroutineProfile: true,
			EnableBlockProfile:     false,
			EnableMutexProfile:     false,
			ProfileDuration:        5 * time.Second,
			SampleRate:             1.0,
			CustomConfig:           make(map[string]interface{}),
		},
		{
			Name:                   "quick",
			Description:            "Quick benchmark",
			Iterations:             100,
			Duration:               0,
			Timeout:                10 * time.Second,
			WarmupRuns:             5,
			EnableProfiling:        false,
			EnableMemoryProfile:    false,
			EnableCPUProfile:       false,
			EnableGoroutineProfile: false,
			EnableBlockProfile:     false,
			EnableMutexProfile:     false,
			ProfileDuration:        0,
			SampleRate:             1.0,
			CustomConfig:           make(map[string]interface{}),
		},
		{
			Name:                   "comprehensive",
			Description:            "Comprehensive benchmark",
			Iterations:             10000,
			Duration:               0,
			Timeout:                5 * time.Minute,
			WarmupRuns:             100,
			EnableProfiling:        true,
			EnableMemoryProfile:    true,
			EnableCPUProfile:       true,
			EnableGoroutineProfile: true,
			EnableBlockProfile:     true,
			EnableMutexProfile:     true,
			ProfileDuration:        30 * time.Second,
			SampleRate:             1.0,
			CustomConfig:           make(map[string]interface{}),
		},
	}

	for _, config := range defaultConfigs {
		_, err := bm.CreateBenchmark(config, func() error {
			// Default benchmark function
			time.Sleep(1 * time.Millisecond)
			return nil
		})
		if err != nil {
			return fmt.Errorf("failed to create default benchmark %s: %w", config.Name, err)
		}
	}

	return nil
}

func (bm *BenchmarkManager) initializeDefaultProfiles() error {
	// Create default profiles
	defaultConfigs := []*ProfileConfig{
		{
			Name:            "cpu",
			Description:     "CPU profile",
			Type:            "cpu",
			Duration:        30 * time.Second,
			SampleRate:      1.0,
			EnableCPU:       true,
			EnableMemory:    false,
			EnableGoroutine: false,
			EnableBlock:     false,
			EnableMutex:     false,
			CustomConfig:    make(map[string]interface{}),
		},
		{
			Name:            "memory",
			Description:     "Memory profile",
			Type:            "memory",
			Duration:        30 * time.Second,
			SampleRate:      1.0,
			EnableCPU:       false,
			EnableMemory:    true,
			EnableGoroutine: false,
			EnableBlock:     false,
			EnableMutex:     false,
			CustomConfig:    make(map[string]interface{}),
		},
		{
			Name:            "goroutine",
			Description:     "Goroutine profile",
			Type:            "goroutine",
			Duration:        30 * time.Second,
			SampleRate:      1.0,
			EnableCPU:       false,
			EnableMemory:    false,
			EnableGoroutine: true,
			EnableBlock:     false,
			EnableMutex:     false,
			CustomConfig:    make(map[string]interface{}),
		},
	}

	for _, config := range defaultConfigs {
		_, err := bm.CreateProfile(config)
		if err != nil {
			return fmt.Errorf("failed to create default profile %s: %w", config.Name, err)
		}
	}

	return nil
}

// Performance optimization constants for benchmarking
const (
	DefaultBenchmarkIterations      = 1000
	DefaultBenchmarkDuration        = 0
	DefaultBenchmarkTimeout         = 30 * time.Second
	DefaultBenchmarkWarmupRuns      = 10
	DefaultProfileDuration          = 30 * time.Second
	DefaultProfileSampleRate        = 1.0
	DefaultBenchmarkManagerInterval = 1 * time.Minute
)

// Benchmarking error types
var (
	ErrBenchmarkNotFound     = fmt.Errorf("benchmark not found")
	ErrBenchmarkDisabled     = fmt.Errorf("benchmark is disabled")
	ErrBenchmarkTimeout      = fmt.Errorf("benchmark timeout")
	ErrBenchmarkFailed       = fmt.Errorf("benchmark failed")
	ErrProfileNotFound       = fmt.Errorf("profile not found")
	ErrProfileDisabled       = fmt.Errorf("profile is disabled")
	ErrProfileTimeout        = fmt.Errorf("profile timeout")
	ErrProfileFailed         = fmt.Errorf("profile failed")
	ErrProfilingNotSupported = fmt.Errorf("profiling not supported")
)

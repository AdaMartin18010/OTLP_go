// Package performance provides performance optimization utilities for OTLP Go applications.
// It includes memory allocation optimization, concurrency patterns, string operations,
// object pooling, benchmarking, and performance monitoring capabilities.
package performance

import (
	"context"
	"fmt"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

// Task interface defines the contract for executable tasks.
type Task interface {
	Execute(ctx context.Context) error
	GetID() string
	GetPriority() int
}

// DefaultTask provides a basic task implementation.
type DefaultTask struct {
	id       string
	priority int
	executor func(ctx context.Context) error
}

// NewDefaultTask creates a new default task.
func NewDefaultTask(id string, priority int, executor func(ctx context.Context) error) *DefaultTask {
	return &DefaultTask{
		id:       id,
		priority: priority,
		executor: executor,
	}
}

// Execute executes the task.
func (dt *DefaultTask) Execute(ctx context.Context) error {
	if dt.executor != nil {
		return dt.executor(ctx)
	}
	return nil
}

// GetID returns the task ID.
func (dt *DefaultTask) GetID() string {
	return dt.id
}

// GetPriority returns the task priority.
func (dt *DefaultTask) GetPriority() int {
	return dt.priority
}

// PerformanceManager manages performance optimization utilities and monitoring.
type PerformanceManager struct {
	mu              sync.RWMutex
	objectPools     map[string]*ObjectPool
	metrics         *PerformanceMetrics
	tracer          trace.Tracer
	meter           metric.Meter
	enabledFeatures map[string]bool
	cleanupFuncs    []func() error
}

// PerformanceMetrics holds performance-related metrics.
type PerformanceMetrics struct {
	MemoryAllocations   int64
	MemoryDeallocations int64
	PoolHits            int64
	PoolMisses          int64
	GCRuns              int64
	GCAllocations       int64
	StringOps           int64
	ConcurrentOps       int64
	LastUpdateTime      time.Time
}

// ObjectPool provides object pooling for frequently allocated objects.
type ObjectPool struct {
	pool        sync.Pool
	name        string
	newFunc     func() interface{}
	resetFunc   func(interface{})
	maxSize     int
	currentSize int64
	hits        int64
	misses      int64
}

// MemoryOptimizer provides memory allocation optimization utilities.
type MemoryOptimizer struct {
	allocator   Allocator
	poolManager *ObjectPoolManager
	monitor     *MemoryMonitor
	config      *MemoryConfig
}

// Allocator interface for custom memory allocation strategies.
type Allocator interface {
	Allocate(size int) []byte
	Deallocate(buf []byte)
	GetStats() AllocatorStats
}

// AllocatorStats holds allocation statistics.
type AllocatorStats struct {
	TotalAllocations   int64
	TotalDeallocations int64
	CurrentAllocated   int64
	PeakAllocated      int64
	AllocationCount    int64
}

// MemoryConfig holds memory optimization configuration.
type MemoryConfig struct {
	EnablePooling     bool
	PoolSize          int
	MaxPoolSize       int
	GCThreshold       int64
	MonitoringEnabled bool
	ProfilingEnabled  bool
}

// StringStats holds string operation statistics.
type StringStats struct {
	Concatenations int64
	Conversions    int64
	PoolHits       int64
	PoolMisses     int64
	BuilderReuses  int64
	Optimizations  int64
}

// ConcurrencyOptimizer provides concurrency optimization utilities.
type ConcurrencyOptimizer struct {
	workerPool    *WorkerPool
	semaphore     *Semaphore
	rateLimiter   *RateLimiter
	optimizations map[string]bool
	stats         *ConcurrencyStats
}

// ConcurrencyStats holds concurrency operation statistics.
type ConcurrencyStats struct {
	TasksProcessed    int64
	TasksQueued       int64
	TasksRejected     int64
	WorkersActive     int64
	WorkersIdle       int64
	RateLimitHits     int64
	SemaphoreAcquired int64
	SemaphoreReleased int64
}

// WorkerPool manages a pool of workers for concurrent task processing.
type WorkerPool struct {
	workers    chan chan Task
	taskQueue  chan Task
	quit       chan bool
	wg         sync.WaitGroup
	numWorkers int
	active     int64
	idle       int64
}

// Semaphore provides a counting semaphore for resource control.
type Semaphore struct {
	permits chan struct{}
	count   int64
	max     int64
}

// RateLimiter provides rate limiting functionality.
type RateLimiter struct {
	tokens     chan struct{}
	interval   time.Duration
	lastRefill time.Time
	mu         sync.Mutex
}

// Profiler provides performance profiling capabilities.
type Profiler struct {
	enabled   bool
	startTime time.Time
	samples   []ProfileSample
	mu        sync.RWMutex
	config    *ProfilerConfig
}

// ProfileSample represents a single profiling sample.
type ProfileSample struct {
	Timestamp   time.Time
	Function    string
	Duration    time.Duration
	MemoryAlloc int64
	MemoryInUse int64
	Goroutines  int
}

// ProfilerConfig holds profiler configuration.
type ProfilerConfig struct {
	SampleInterval  time.Duration
	MaxSamples      int
	EnableMemory    bool
	EnableCPU       bool
	EnableGoroutine bool
}

// NewPerformanceManager creates a new PerformanceManager instance.
func NewPerformanceManager() *PerformanceManager {
	return &PerformanceManager{
		objectPools:     make(map[string]*ObjectPool),
		metrics:         &PerformanceMetrics{},
		tracer:          otel.Tracer("performance"),
		meter:           otel.Meter("performance"),
		enabledFeatures: make(map[string]bool),
		cleanupFuncs:    make([]func() error, 0),
	}
}

// Initialize initializes the performance manager with default settings.
func (pm *PerformanceManager) Initialize(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "performance.initialize")
	defer span.End()

	// Enable default features
	pm.enabledFeatures["memory_optimization"] = true
	pm.enabledFeatures["string_optimization"] = true
	pm.enabledFeatures["concurrency_optimization"] = true
	pm.enabledFeatures["object_pooling"] = true
	pm.enabledFeatures["monitoring"] = true

	// Initialize object pools
	if err := pm.initializeObjectPools(); err != nil {
		return fmt.Errorf("failed to initialize object pools: %w", err)
	}

	// Initialize performance monitoring
	if err := pm.initializeMonitoring(); err != nil {
		return fmt.Errorf("failed to initialize monitoring: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("initialized", true),
		attribute.Int("pools_created", len(pm.objectPools)),
	)

	return nil
}

// Shutdown gracefully shuts down the performance manager.
func (pm *PerformanceManager) Shutdown(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "performance.shutdown")
	defer span.End()

	pm.mu.Lock()
	defer pm.mu.Unlock()

	// Execute cleanup functions
	for _, cleanup := range pm.cleanupFuncs {
		if err := cleanup(); err != nil {
			span.RecordError(err)
		}
	}

	// Clear object pools
	for name, pool := range pm.objectPools {
		pool.Close()
		delete(pm.objectPools, name)
	}

	span.SetAttributes(
		attribute.Bool("shutdown_complete", true),
		attribute.Int("cleanup_functions", len(pm.cleanupFuncs)),
	)

	return nil
}

// GetMetrics returns current performance metrics.
func (pm *PerformanceManager) GetMetrics() *PerformanceMetrics {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	// Update metrics with current runtime stats
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	pm.metrics.GCRuns = int64(m.NumGC)
	pm.metrics.GCAllocations = int64(m.TotalAlloc)
	pm.metrics.LastUpdateTime = time.Now()

	return pm.metrics
}

// CreateObjectPool creates a new object pool with the specified configuration.
func (pm *PerformanceManager) CreateObjectPool(name string, newFunc func() interface{}, resetFunc func(interface{}), maxSize int) *ObjectPool {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	pool := &ObjectPool{
		pool: sync.Pool{
			New: newFunc,
		},
		name:        name,
		newFunc:     newFunc,
		resetFunc:   resetFunc,
		maxSize:     maxSize,
		currentSize: 0,
		hits:        0,
		misses:      0,
	}

	pm.objectPools[name] = pool
	return pool
}

// GetObjectPool retrieves an object pool by name.
func (pm *PerformanceManager) GetObjectPool(name string) (*ObjectPool, bool) {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	pool, exists := pm.objectPools[name]
	return pool, exists
}

// NewMemoryOptimizer creates a new MemoryOptimizer instance.
func NewMemoryOptimizer(config *MemoryConfig) *MemoryOptimizer {
	if config == nil {
		config = &MemoryConfig{
			EnablePooling:     true,
			PoolSize:          100,
			MaxPoolSize:       1000,
			GCThreshold:       100 * 1024 * 1024, // 100MB
			MonitoringEnabled: true,
			ProfilingEnabled:  false,
		}
	}

	return &MemoryOptimizer{
		allocator:   NewDefaultAllocator(),
		poolManager: NewObjectPoolManager(),
		monitor:     NewMemoryMonitor(),
		config:      config,
	}
}

// OptimizeAllocation optimizes memory allocation using various strategies.
func (mo *MemoryOptimizer) OptimizeAllocation(size int) []byte {
	if mo.config.EnablePooling {
		if pool, exists := mo.poolManager.GetPool("buffer"); exists {
			if buf := pool.Get(); buf != nil {
				if len(buf.([]byte)) >= size {
					return buf.([]byte)[:size]
				}
			}
		}
	}

	return mo.allocator.Allocate(size)
}

// ReleaseAllocation releases allocated memory back to the pool.
func (mo *MemoryOptimizer) ReleaseAllocation(buf []byte) {
	if mo.config.EnablePooling {
		if pool, exists := mo.poolManager.GetPool("buffer"); exists {
			pool.Put(buf)
			return
		}
	}

	mo.allocator.Deallocate(buf)
}

// NewStringOptimizerSimple creates a new StringOptimizer instance with default manager.
func NewStringOptimizerSimple() *StringOptimizer {
	manager := NewStringOptimizationManager()
	return NewStringOptimizer(manager)
}

// NewConcurrencyOptimizer creates a new ConcurrencyOptimizer instance.
func NewConcurrencyOptimizer(numWorkers int) *ConcurrencyOptimizer {
	return &ConcurrencyOptimizer{
		workerPool:    NewWorkerPool(numWorkers),
		semaphore:     NewSemaphore(100),                // Default limit
		rateLimiter:   NewRateLimiter(100, time.Second), // 100 ops/sec
		optimizations: make(map[string]bool),
		stats:         &ConcurrencyStats{},
	}
}

// ExecuteConcurrent executes tasks concurrently with optimization.
func (co *ConcurrencyOptimizer) ExecuteConcurrent(ctx context.Context, tasks []Task) error {
	_, span := otel.Tracer("concurrency").Start(ctx, "execute_concurrent")
	defer span.End()

	// Rate limiting
	if !co.rateLimiter.Allow() {
		atomic.AddInt64(&co.stats.RateLimitHits, 1)
		return fmt.Errorf("rate limit exceeded")
	}

	// Semaphore control
	if !co.semaphore.TryAcquire() {
		return fmt.Errorf("semaphore limit exceeded")
	}
	defer co.semaphore.Release()

	// Submit tasks to worker pool
	for _, task := range tasks {
		if err := co.workerPool.Submit(ctx, task); err != nil {
			span.RecordError(err)
			return err
		}
		atomic.AddInt64(&co.stats.TasksQueued, 1)
	}

	span.SetAttributes(
		attribute.Int("tasks_count", len(tasks)),
		attribute.Int64("tasks_queued", atomic.LoadInt64(&co.stats.TasksQueued)),
	)

	return nil
}

// RunBenchmark runs a performance benchmark for the given function.
func RunBenchmark(name string, iterations int, fn func() error) (*BenchmarkResult, error) {
	_, span := otel.Tracer("benchmark").Start(context.Background(), "run_benchmark")
	defer span.End()

	start := time.Now()
	var totalAllocations int64
	var totalMemory int64

	// Force GC before benchmark
	runtime.GC()

	var m1 runtime.MemStats
	runtime.ReadMemStats(&m1)

	for i := 0; i < iterations; i++ {
		if err := fn(); err != nil {
			return nil, fmt.Errorf("benchmark function failed: %w", err)
		}
	}

	var m2 runtime.MemStats
	runtime.ReadMemStats(&m2)

	duration := time.Since(start)
	totalAllocations = int64(m2.TotalAlloc - m1.TotalAlloc)
	totalMemory = int64(m2.Alloc - m1.Alloc)

	result := &BenchmarkResult{
		Name:              name,
		Duration:          duration,
		MemoryAllocations: totalAllocations,
		MemoryBytes:       totalMemory,
		Iterations:        int64(iterations),
		Operations:        int64(iterations),
		Throughput:        float64(iterations) / duration.Seconds(),
		MemoryPerOp:       float64(totalMemory) / float64(iterations),
		StartTime:         start,
		EndTime:           time.Now(),
		Status:            "completed",
	}

	span.SetAttributes(
		attribute.String("benchmark_name", name),
		attribute.Int64("iterations", int64(iterations)),
		attribute.Float64("duration_seconds", duration.Seconds()),
		attribute.Float64("throughput", result.Throughput),
		attribute.Int64("memory_bytes", totalMemory),
	)

	return result, nil
}

// NewProfiler creates a new Profiler instance.
func NewProfiler(config *ProfilerConfig) *Profiler {
	if config == nil {
		config = &ProfilerConfig{
			SampleInterval:  100 * time.Millisecond,
			MaxSamples:      1000,
			EnableMemory:    true,
			EnableCPU:       true,
			EnableGoroutine: true,
		}
	}

	return &Profiler{
		enabled:   true,
		startTime: time.Now(),
		samples:   make([]ProfileSample, 0, config.MaxSamples),
		config:    config,
	}
}

// StartProfiling starts the profiling process.
func (p *Profiler) StartProfiling() error {
	if !p.enabled {
		return fmt.Errorf("profiler is disabled")
	}

	p.startTime = time.Now()
	go p.profilingLoop()

	return nil
}

// StopProfiling stops the profiling process and returns results.
func (p *Profiler) StopProfiling() []ProfileSample {
	p.mu.Lock()
	defer p.mu.Unlock()

	p.enabled = false
	return p.samples
}

// profilingLoop runs the profiling loop.
func (p *Profiler) profilingLoop() {
	ticker := time.NewTicker(p.config.SampleInterval)
	defer ticker.Stop()

	for p.enabled {
		select {
		case <-ticker.C:
			p.takeSample()
		}
	}
}

// takeSample takes a profiling sample.
func (p *Profiler) takeSample() {
	p.mu.Lock()
	defer p.mu.Unlock()

	if len(p.samples) >= p.config.MaxSamples {
		return
	}

	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	sample := ProfileSample{
		Timestamp:   time.Now(),
		Function:    "system",
		Duration:    time.Since(p.startTime),
		MemoryAlloc: int64(m.Alloc),
		MemoryInUse: int64(m.Sys),
		Goroutines:  runtime.NumGoroutine(),
	}

	p.samples = append(p.samples, sample)
}

// Utility functions for object pools

// NewStringPool creates a new string object pool.
func NewStringPool() *ObjectPool {
	return &ObjectPool{
		pool: sync.Pool{
			New: func() interface{} {
				return ""
			},
		},
		name:      "string",
		newFunc:   func() interface{} { return "" },
		resetFunc: func(obj interface{}) { /* strings are immutable */ },
		maxSize:   1000,
	}
}

// NewStringBuilderPool creates a new string builder object pool.
func NewStringBuilderPool() *ObjectPool {
	return &ObjectPool{
		pool: sync.Pool{
			New: func() interface{} {
				return &strings.Builder{}
			},
		},
		name: "string_builder",
		newFunc: func() interface{} {
			return &strings.Builder{}
		},
		resetFunc: func(obj interface{}) {
			if sb, ok := obj.(*strings.Builder); ok {
				sb.Reset()
			}
		},
		maxSize: 100,
	}
}

// Get retrieves an object from the pool.
func (op *ObjectPool) Get() interface{} {
	obj := op.pool.Get()
	if obj != nil {
		atomic.AddInt64(&op.hits, 1)
		atomic.AddInt64(&op.currentSize, -1)
	} else {
		atomic.AddInt64(&op.misses, 1)
	}
	return obj
}

// Put returns an object to the pool.
func (op *ObjectPool) Put(obj interface{}) {
	if obj == nil {
		return
	}

	if atomic.LoadInt64(&op.currentSize) >= int64(op.maxSize) {
		return
	}

	if op.resetFunc != nil {
		op.resetFunc(obj)
	}

	op.pool.Put(obj)
	atomic.AddInt64(&op.currentSize, 1)
}

// Close closes the object pool.
func (op *ObjectPool) Close() {
	// Clear the pool
	for {
		if obj := op.pool.Get(); obj == nil {
			break
		}
	}
}

// Stats returns pool statistics.
func (op *ObjectPool) Stats() (hits, misses, currentSize int64) {
	return atomic.LoadInt64(&op.hits), atomic.LoadInt64(&op.misses), atomic.LoadInt64(&op.currentSize)
}

// Additional utility functions and implementations

// DefaultAllocator provides a default memory allocator implementation.
type DefaultAllocator struct {
	stats AllocatorStats
}

// NewDefaultAllocator creates a new default allocator.
func NewDefaultAllocator() *DefaultAllocator {
	return &DefaultAllocator{}
}

// Allocate allocates memory of the specified size.
func (da *DefaultAllocator) Allocate(size int) []byte {
	buf := make([]byte, size)
	atomic.AddInt64(&da.stats.TotalAllocations, 1)
	atomic.AddInt64(&da.stats.CurrentAllocated, int64(size))

	if current := atomic.LoadInt64(&da.stats.CurrentAllocated); current > atomic.LoadInt64(&da.stats.PeakAllocated) {
		atomic.StoreInt64(&da.stats.PeakAllocated, current)
	}

	return buf
}

// Deallocate deallocates the given buffer.
func (da *DefaultAllocator) Deallocate(buf []byte) {
	size := len(buf)
	atomic.AddInt64(&da.stats.TotalDeallocations, 1)
	atomic.AddInt64(&da.stats.CurrentAllocated, -int64(size))
}

// GetStats returns allocation statistics.
func (da *DefaultAllocator) GetStats() AllocatorStats {
	return AllocatorStats{
		TotalAllocations:   atomic.LoadInt64(&da.stats.TotalAllocations),
		TotalDeallocations: atomic.LoadInt64(&da.stats.TotalDeallocations),
		CurrentAllocated:   atomic.LoadInt64(&da.stats.CurrentAllocated),
		PeakAllocated:      atomic.LoadInt64(&da.stats.PeakAllocated),
		AllocationCount:    atomic.LoadInt64(&da.stats.TotalAllocations),
	}
}

// ObjectPoolManager manages multiple object pools.
type ObjectPoolManager struct {
	pools map[string]*ObjectPool
	mu    sync.RWMutex
}

// NewObjectPoolManager creates a new object pool manager.
func NewObjectPoolManager() *ObjectPoolManager {
	return &ObjectPoolManager{
		pools: make(map[string]*ObjectPool),
	}
}

// GetPool retrieves a pool by name.
func (opm *ObjectPoolManager) GetPool(name string) (*ObjectPool, bool) {
	opm.mu.RLock()
	defer opm.mu.RUnlock()

	pool, exists := opm.pools[name]
	return pool, exists
}

// MemoryMonitor provides memory monitoring capabilities.
type MemoryMonitor struct {
	enabled bool
	stats   runtime.MemStats
	mu      sync.RWMutex
}

// NewMemoryMonitor creates a new memory monitor.
func NewMemoryMonitor() *MemoryMonitor {
	return &MemoryMonitor{
		enabled: true,
	}
}

// WorkerPool implementation

// NewWorkerPool creates a new worker pool.
func NewWorkerPool(numWorkers int) *WorkerPool {
	return &WorkerPool{
		workers:    make(chan chan Task, numWorkers),
		taskQueue:  make(chan Task, 1000),
		quit:       make(chan bool),
		numWorkers: numWorkers,
	}
}

// Start starts the worker pool.
func (wp *WorkerPool) Start() {
	for i := 0; i < wp.numWorkers; i++ {
		worker := NewWorker(wp.workers, wp.taskQueue)
		worker.Start()
		wp.wg.Add(1)
	}
}

// Stop stops the worker pool.
func (wp *WorkerPool) Stop() {
	close(wp.quit)
	wp.wg.Wait()
}

// Submit submits a task to the worker pool.
func (wp *WorkerPool) Submit(ctx context.Context, task Task) error {
	select {
	case wp.taskQueue <- task:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	default:
		return fmt.Errorf("task queue is full")
	}
}

// Worker represents a single worker in the pool.
type Worker struct {
	workerPool chan chan Task
	taskQueue  chan Task
	quit       chan bool
}

// NewWorker creates a new worker.
func NewWorker(workerPool chan chan Task, taskQueue chan Task) *Worker {
	return &Worker{
		workerPool: workerPool,
		taskQueue:  taskQueue,
		quit:       make(chan bool),
	}
}

// Start starts the worker.
func (w *Worker) Start() {
	go func() {
		for {
			w.workerPool <- w.taskQueue

			select {
			case task := <-w.taskQueue:
				task.Execute(context.Background())
			case <-w.quit:
				return
			}
		}
	}()
}

// Stop stops the worker.
func (w *Worker) Stop() {
	w.quit <- true
}

// Semaphore implementation

// NewSemaphore creates a new semaphore.
func NewSemaphore(max int64) *Semaphore {
	return &Semaphore{
		permits: make(chan struct{}, max),
		max:     max,
	}
}

// Acquire acquires a permit from the semaphore.
func (s *Semaphore) Acquire() {
	s.permits <- struct{}{}
	atomic.AddInt64(&s.count, 1)
}

// TryAcquire tries to acquire a permit without blocking.
func (s *Semaphore) TryAcquire() bool {
	select {
	case s.permits <- struct{}{}:
		atomic.AddInt64(&s.count, 1)
		return true
	default:
		return false
	}
}

// Release releases a permit back to the semaphore.
func (s *Semaphore) Release() {
	<-s.permits
	atomic.AddInt64(&s.count, -1)
}

// RateLimiter implementation

// NewRateLimiter creates a new rate limiter.
func NewRateLimiter(rate int, interval time.Duration) *RateLimiter {
	return &RateLimiter{
		tokens:     make(chan struct{}, rate),
		interval:   interval,
		lastRefill: time.Now(),
	}
}

// Allow checks if a request is allowed by the rate limiter.
func (rl *RateLimiter) Allow() bool {
	rl.mu.Lock()
	defer rl.mu.Unlock()

	now := time.Now()
	if now.Sub(rl.lastRefill) >= rl.interval {
		// Refill tokens
		for len(rl.tokens) < cap(rl.tokens) {
			select {
			case rl.tokens <- struct{}{}:
			default:
				break
			}
		}
		rl.lastRefill = now
	}

	select {
	case <-rl.tokens:
		return true
	default:
		return false
	}
}

// Helper functions for performance optimization

// ForceGC forces garbage collection and returns GC statistics.
func ForceGC() (int64, time.Duration) {
	start := time.Now()
	runtime.GC()
	duration := time.Since(start)

	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return int64(m.NumGC), duration
}

// GetMemoryStats returns current memory statistics.
func GetMemoryStats() runtime.MemStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m
}

// OptimizeStringBuilder optimizes string builder usage.
func OptimizeStringBuilder() *strings.Builder {
	// This would typically use a pool in a real implementation
	return &strings.Builder{}
}

// SafeStringConversion safely converts unsafe.Pointer to string.
func SafeStringConversion(ptr unsafe.Pointer, length int) string {
	if ptr == nil || length <= 0 {
		return ""
	}

	// Convert unsafe.Pointer to []byte first
	bytes := (*[1 << 30]byte)(ptr)[:length:length]
	return string(bytes)
}

// BatchProcess processes items in batches for better performance.
func BatchProcess[T any](items []T, batchSize int, processor func([]T) error) error {
	for i := 0; i < len(items); i += batchSize {
		end := i + batchSize
		if end > len(items) {
			end = len(items)
		}

		batch := items[i:end]
		if err := processor(batch); err != nil {
			return err
		}
	}
	return nil
}

// ConcurrentMap provides a concurrent map implementation.
type ConcurrentMap[K comparable, V any] struct {
	mu   sync.RWMutex
	data map[K]V
}

// NewConcurrentMap creates a new concurrent map.
func NewConcurrentMap[K comparable, V any]() *ConcurrentMap[K, V] {
	return &ConcurrentMap[K, V]{
		data: make(map[K]V),
	}
}

// Set sets a key-value pair.
func (cm *ConcurrentMap[K, V]) Set(key K, value V) {
	cm.mu.Lock()
	defer cm.mu.Unlock()
	cm.data[key] = value
}

// Get gets a value by key.
func (cm *ConcurrentMap[K, V]) Get(key K) (V, bool) {
	cm.mu.RLock()
	defer cm.mu.RUnlock()
	value, exists := cm.data[key]
	return value, exists
}

// Delete deletes a key-value pair.
func (cm *ConcurrentMap[K, V]) Delete(key K) {
	cm.mu.Lock()
	defer cm.mu.Unlock()
	delete(cm.data, key)
}

// Size returns the number of elements in the map.
func (cm *ConcurrentMap[K, V]) Size() int {
	cm.mu.RLock()
	defer cm.mu.RUnlock()
	return len(cm.data)
}

// Performance optimization constants
const (
	DefaultPoolSize      = 100
	DefaultMaxPoolSize   = 1000
	DefaultGCThreshold   = 100 * 1024 * 1024 // 100MB
	DefaultWorkerCount   = 10
	DefaultSemaphoreSize = 100
	DefaultRateLimit     = 100
	DefaultRateInterval  = time.Second
)

// Performance optimization error types
var (
	ErrRateLimitExceeded = fmt.Errorf("rate limit exceeded")
	ErrSemaphoreFull     = fmt.Errorf("semaphore is full")
	ErrWorkerPoolFull    = fmt.Errorf("worker pool queue is full")
	ErrProfilerDisabled  = fmt.Errorf("profiler is disabled")
)

// Initialize helper functions
func (pm *PerformanceManager) initializeObjectPools() error {
	// Initialize common object pools
	pm.CreateObjectPool("buffer", func() interface{} {
		return make([]byte, 0, 1024)
	}, func(obj interface{}) {
		if buf, ok := obj.([]byte); ok {
			buf = buf[:0] // Reset length but keep capacity
		}
	}, DefaultMaxPoolSize)

	pm.CreateObjectPool("string", func() interface{} {
		return ""
	}, func(obj interface{}) {
		// Strings are immutable, no reset needed
	}, DefaultMaxPoolSize)

	return nil
}

func (pm *PerformanceManager) initializeMonitoring() error {
	// Initialize performance monitoring
	pm.cleanupFuncs = append(pm.cleanupFuncs, func() error {
		// Cleanup monitoring resources
		return nil
	})

	return nil
}

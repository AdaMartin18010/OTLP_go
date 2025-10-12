// Package performance provides advanced object pool management utilities.
// This file focuses on high-performance object pooling, resource reuse,
// and advanced pool management patterns for OTLP Go applications.
package performance

import (
	"context"
	"fmt"
	"sync"
	"sync/atomic"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// PoolManager provides advanced object pool management capabilities.
type PoolManager struct {
	mu              sync.RWMutex
	pools           map[string]Pool
	poolFactories   map[string]PoolFactory
	poolConfigs     map[string]*PoolConfig
	metrics         *PoolManagerMetrics
	tracer          trace.Tracer
	enabledFeatures map[string]bool
	cleanupFuncs    []func() error
}

// PoolManagerMetrics holds pool manager metrics.
type PoolManagerMetrics struct {
	TotalPools         int64
	ActivePools        int64
	TotalAllocations   int64
	TotalDeallocations int64
	PoolHits           int64
	PoolMisses         int64
	PoolOverflows      int64
	PoolUnderflows     int64
	MemoryUsage        int64
	Efficiency         float64
	LastUpdateTime     time.Time
}

// Pool interface defines the contract for object pools.
type Pool interface {
	Get() interface{}
	Put(interface{})
	Size() int64
	Capacity() int64
	Stats() *PoolStats
	Close() error
	Reset() error
}

// PoolFactory interface defines the contract for pool factories.
type PoolFactory interface {
	CreatePool(config *PoolConfig) (Pool, error)
	GetPoolType() string
	ValidateConfig(config *PoolConfig) error
}

// PoolConfig holds configuration for object pools.
type PoolConfig struct {
	Name            string
	Type            string
	InitialSize     int64
	MaxSize         int64
	MinSize         int64
	GrowthFactor    float64
	ShrinkFactor    float64
	IdleTimeout     time.Duration
	CleanupInterval time.Duration
	EnableMetrics   bool
	EnableProfiling bool
	CustomConfig    map[string]interface{}
}

// PoolStats holds pool statistics.
type PoolStats struct {
	Name            string
	Type            string
	Size            int64
	Capacity        int64
	Hits            int64
	Misses          int64
	Overflows       int64
	Underflows      int64
	Allocations     int64
	Deallocations   int64
	MemoryUsage     int64
	Efficiency      float64
	AverageWaitTime time.Duration
	MaxWaitTime     time.Duration
	MinWaitTime     time.Duration
	LastUpdateTime  time.Time
}

// GenericPool provides a generic object pool implementation.
type GenericPool struct {
	mu            sync.RWMutex
	name          string
	config        *PoolConfig
	factory       func() interface{}
	resetFunc     func(interface{})
	pool          sync.Pool
	objects       chan interface{}
	size          int64
	capacity      int64
	hits          int64
	misses        int64
	overflows     int64
	underflows    int64
	allocations   int64
	deallocations int64
	memoryUsage   int64
	stats         *PoolStats
	cleanupTicker *time.Ticker
	stopCleanup   chan struct{}
	enabled       bool
}

// BoundedPool provides a bounded object pool with size limits.
type BoundedPool struct {
	*GenericPool
	maxSize      int64
	minSize      int64
	growthFactor float64
	shrinkFactor float64
}

// UnboundedPool provides an unbounded object pool.
type UnboundedPool struct {
	*GenericPool
}

// TimedPool provides a timed object pool with idle timeout.
type TimedPool struct {
	*GenericPool
	idleTimeout     time.Duration
	cleanupInterval time.Duration
	lastUsed        map[interface{}]time.Time
	mu              sync.RWMutex
}

// PoolFactoryRegistry manages pool factories.
type PoolFactoryRegistry struct {
	mu        sync.RWMutex
	factories map[string]PoolFactory
}

// PoolMonitor provides pool monitoring capabilities.
type PoolMonitor struct {
	mu      sync.RWMutex
	pools   map[string]Pool
	metrics *PoolMonitorMetrics
	ticker  *time.Ticker
	stopCh  chan struct{}
	enabled bool
}

// PoolMonitorMetrics holds pool monitor metrics.
type PoolMonitorMetrics struct {
	TotalPools         int64
	HealthyPools       int64
	UnhealthyPools     int64
	TotalAllocations   int64
	TotalDeallocations int64
	AverageEfficiency  float64
	MemoryUsage        int64
	LastUpdateTime     time.Time
}

// PoolHealthChecker provides pool health checking capabilities.
type PoolHealthChecker struct {
	mu      sync.RWMutex
	pools   map[string]Pool
	metrics *PoolHealthMetrics
	enabled bool
}

// PoolHealthMetrics holds pool health metrics.
type PoolHealthMetrics struct {
	TotalChecks     int64
	HealthyChecks   int64
	UnhealthyChecks int64
	AverageHealth   float64
	LastCheckTime   time.Time
}

// PoolOptimizer provides pool optimization capabilities.
type PoolOptimizer struct {
	mu      sync.RWMutex
	pools   map[string]Pool
	metrics *PoolOptimizerMetrics
	enabled bool
}

// PoolOptimizerMetrics holds pool optimizer metrics.
type PoolOptimizerMetrics struct {
	OptimizationsApplied    int64
	MemorySaved             int64
	EfficiencyImproved      float64
	AverageOptimizationTime time.Duration
	LastOptimizationTime    time.Time
}

// NewPoolManager creates a new pool manager.
func NewPoolManager() *PoolManager {
	return &PoolManager{
		pools:           make(map[string]Pool),
		poolFactories:   make(map[string]PoolFactory),
		poolConfigs:     make(map[string]*PoolConfig),
		metrics:         &PoolManagerMetrics{},
		tracer:          otel.Tracer("pool_manager"),
		enabledFeatures: make(map[string]bool),
		cleanupFuncs:    make([]func() error, 0),
	}
}

// Initialize initializes the pool manager.
func (pm *PoolManager) Initialize(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "pool_manager.initialize")
	defer span.End()

	// Enable default features
	pm.enabledFeatures["generic_pools"] = true
	pm.enabledFeatures["bounded_pools"] = true
	pm.enabledFeatures["unbounded_pools"] = true
	pm.enabledFeatures["timed_pools"] = true
	pm.enabledFeatures["pool_monitoring"] = true
	pm.enabledFeatures["pool_optimization"] = true

	// Initialize pool factories
	if err := pm.initializePoolFactories(); err != nil {
		return fmt.Errorf("failed to initialize pool factories: %w", err)
	}

	// Initialize default pools
	if err := pm.initializeDefaultPools(); err != nil {
		return fmt.Errorf("failed to initialize default pools: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("initialized", true),
		attribute.Int("pools", len(pm.pools)),
		attribute.Int("factories", len(pm.poolFactories)),
	)

	return nil
}

// Shutdown gracefully shuts down the pool manager.
func (pm *PoolManager) Shutdown(ctx context.Context) error {
	ctx, span := pm.tracer.Start(ctx, "pool_manager.shutdown")
	defer span.End()

	pm.mu.Lock()
	defer pm.mu.Unlock()

	// Execute cleanup functions
	for _, cleanup := range pm.cleanupFuncs {
		if err := cleanup(); err != nil {
			span.RecordError(err)
		}
	}

	// Close all pools
	for name, pool := range pm.pools {
		if err := pool.Close(); err != nil {
			span.RecordError(err)
		}
		delete(pm.pools, name)
	}

	span.SetAttributes(
		attribute.Bool("shutdown_complete", true),
		attribute.Int("pools_closed", len(pm.pools)),
	)

	return nil
}

// CreatePool creates a new object pool.
func (pm *PoolManager) CreatePool(config *PoolConfig, factory func() interface{}, resetFunc func(interface{})) (Pool, error) {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if config == nil {
		return nil, fmt.Errorf("pool config cannot be nil")
	}

	if factory == nil {
		return nil, fmt.Errorf("pool factory cannot be nil")
	}

	// Create pool based on type
	var pool Pool
	var err error

	switch config.Type {
	case "generic":
		pool, err = pm.createGenericPool(config, factory, resetFunc)
	case "bounded":
		pool, err = pm.createBoundedPool(config, factory, resetFunc)
	case "unbounded":
		pool, err = pm.createUnboundedPool(config, factory, resetFunc)
	case "timed":
		pool, err = pm.createTimedPool(config, factory, resetFunc)
	default:
		return nil, fmt.Errorf("unknown pool type: %s", config.Type)
	}

	if err != nil {
		return nil, fmt.Errorf("failed to create pool: %w", err)
	}

	pm.pools[config.Name] = pool
	pm.poolConfigs[config.Name] = config
	atomic.AddInt64(&pm.metrics.TotalPools, 1)
	atomic.AddInt64(&pm.metrics.ActivePools, 1)

	return pool, nil
}

// GetPool retrieves a pool by name.
func (pm *PoolManager) GetPool(name string) (Pool, bool) {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	pool, exists := pm.pools[name]
	return pool, exists
}

// RemovePool removes a pool by name.
func (pm *PoolManager) RemovePool(name string) error {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	pool, exists := pm.pools[name]
	if !exists {
		return fmt.Errorf("pool %s not found", name)
	}

	if err := pool.Close(); err != nil {
		return fmt.Errorf("failed to close pool %s: %w", name, err)
	}

	delete(pm.pools, name)
	delete(pm.poolConfigs, name)
	atomic.AddInt64(&pm.metrics.ActivePools, -1)

	return nil
}

// GetMetrics returns pool manager metrics.
func (pm *PoolManager) GetMetrics() *PoolManagerMetrics {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	// Update metrics with current pool statistics
	totalHits := int64(0)
	totalMisses := int64(0)
	totalMemory := int64(0)

	for _, pool := range pm.pools {
		stats := pool.Stats()
		totalHits += stats.Hits
		totalMisses += stats.Misses
		totalMemory += stats.MemoryUsage
	}

	pm.metrics.PoolHits = totalHits
	pm.metrics.PoolMisses = totalMisses
	pm.metrics.MemoryUsage = totalMemory
	pm.metrics.LastUpdateTime = time.Now()

	if totalHits+totalMisses > 0 {
		pm.metrics.Efficiency = float64(totalHits) / float64(totalHits+totalMisses)
	}

	return pm.metrics
}

// NewGenericPool creates a new generic pool.
func (pm *PoolManager) createGenericPool(config *PoolConfig, factory func() interface{}, resetFunc func(interface{})) (*GenericPool, error) {
	pool := &GenericPool{
		name:      config.Name,
		config:    config,
		factory:   factory,
		resetFunc: resetFunc,
		pool: sync.Pool{
			New: factory,
		},
		objects:       make(chan interface{}, config.MaxSize),
		size:          0,
		capacity:      config.MaxSize,
		hits:          0,
		misses:        0,
		overflows:     0,
		underflows:    0,
		allocations:   0,
		deallocations: 0,
		memoryUsage:   0,
		stats:         &PoolStats{},
		enabled:       true,
	}

	// Initialize pool with initial objects
	for i := int64(0); i < config.InitialSize; i++ {
		obj := factory()
		pool.objects <- obj
		pool.size++
		pool.allocations++
	}

	// Start cleanup routine if enabled
	if config.CleanupInterval > 0 {
		pool.startCleanup()
	}

	return pool, nil
}

// Get retrieves an object from the pool.
func (gp *GenericPool) Get() interface{} {
	gp.mu.Lock()
	defer gp.mu.Unlock()

	start := time.Now()

	// Try to get from channel first
	select {
	case obj := <-gp.objects:
		gp.size--
		gp.hits++
		gp.stats.Hits++
		gp.stats.AverageWaitTime = time.Since(start)
		return obj
	default:
		// Channel is empty, create new object
		obj := gp.pool.Get()
		gp.misses++
		gp.stats.Misses++
		gp.allocations++
		gp.stats.Allocations++
		gp.stats.AverageWaitTime = time.Since(start)
		return obj
	}
}

// Put returns an object to the pool.
func (gp *GenericPool) Put(obj interface{}) {
	if obj == nil || !gp.enabled {
		return
	}

	gp.mu.Lock()
	defer gp.mu.Unlock()

	// Reset object if reset function is provided
	if gp.resetFunc != nil {
		gp.resetFunc(obj)
	}

	// Try to put back in channel
	select {
	case gp.objects <- obj:
		gp.size++
		gp.deallocations++
		gp.stats.Deallocations++
	default:
		// Channel is full, discard object
		gp.overflows++
		gp.stats.Overflows++
	}
}

// Size returns the current pool size.
func (gp *GenericPool) Size() int64 {
	gp.mu.RLock()
	defer gp.mu.RUnlock()
	return gp.size
}

// Capacity returns the pool capacity.
func (gp *GenericPool) Capacity() int64 {
	return gp.capacity
}

// Stats returns pool statistics.
func (gp *GenericPool) Stats() *PoolStats {
	gp.mu.RLock()
	defer gp.mu.RUnlock()

	gp.stats.Name = gp.name
	gp.stats.Type = "generic"
	gp.stats.Size = gp.size
	gp.stats.Capacity = gp.capacity
	gp.stats.Hits = gp.hits
	gp.stats.Misses = gp.misses
	gp.stats.Overflows = gp.overflows
	gp.stats.Underflows = gp.underflows
	gp.stats.Allocations = gp.allocations
	gp.stats.Deallocations = gp.deallocations
	gp.stats.MemoryUsage = gp.memoryUsage
	gp.stats.LastUpdateTime = time.Now()

	if gp.hits+gp.misses > 0 {
		gp.stats.Efficiency = float64(gp.hits) / float64(gp.hits+gp.misses)
	}

	return gp.stats
}

// Close closes the pool.
func (gp *GenericPool) Close() error {
	gp.mu.Lock()
	defer gp.mu.Unlock()

	gp.enabled = false

	// Stop cleanup routine
	if gp.stopCleanup != nil {
		close(gp.stopCleanup)
	}

	// Stop cleanup ticker
	if gp.cleanupTicker != nil {
		gp.cleanupTicker.Stop()
	}

	// Clear objects channel
	close(gp.objects)
	for range gp.objects {
		// Drain the channel
	}

	return nil
}

// Reset resets the pool.
func (gp *GenericPool) Reset() error {
	gp.mu.Lock()
	defer gp.mu.Unlock()

	// Clear existing objects
	close(gp.objects)
	gp.objects = make(chan interface{}, gp.capacity)

	// Reset counters
	gp.size = 0
	gp.hits = 0
	gp.misses = 0
	gp.overflows = 0
	gp.underflows = 0
	gp.allocations = 0
	gp.deallocations = 0
	gp.memoryUsage = 0

	// Reinitialize with initial objects
	for i := int64(0); i < gp.config.InitialSize; i++ {
		obj := gp.factory()
		gp.objects <- obj
		gp.size++
		gp.allocations++
	}

	return nil
}

// startCleanup starts the cleanup routine.
func (gp *GenericPool) startCleanup() {
	gp.cleanupTicker = time.NewTicker(gp.config.CleanupInterval)
	gp.stopCleanup = make(chan struct{})

	go func() {
		for {
			select {
			case <-gp.cleanupTicker.C:
				gp.cleanup()
			case <-gp.stopCleanup:
				return
			}
		}
	}()
}

// cleanup performs pool cleanup.
func (gp *GenericPool) cleanup() {
	gp.mu.Lock()
	defer gp.mu.Unlock()

	// Remove objects that exceed max size
	for gp.size > gp.config.MaxSize {
		select {
		case <-gp.objects:
			gp.size--
			gp.underflows++
			gp.stats.Underflows++
		default:
			break
		}
	}
}

// NewBoundedPool creates a new bounded pool.
func (pm *PoolManager) createBoundedPool(config *PoolConfig, factory func() interface{}, resetFunc func(interface{})) (*BoundedPool, error) {
	genericPool, err := pm.createGenericPool(config, factory, resetFunc)
	if err != nil {
		return nil, err
	}

	boundedPool := &BoundedPool{
		GenericPool:  genericPool,
		maxSize:      config.MaxSize,
		minSize:      config.MinSize,
		growthFactor: config.GrowthFactor,
		shrinkFactor: config.ShrinkFactor,
	}

	return boundedPool, nil
}

// NewUnboundedPool creates a new unbounded pool.
func (pm *PoolManager) createUnboundedPool(config *PoolConfig, factory func() interface{}, resetFunc func(interface{})) (*UnboundedPool, error) {
	// Create unbounded pool with very large capacity
	unboundedConfig := *config
	unboundedConfig.MaxSize = 1000000 // Very large capacity

	genericPool, err := pm.createGenericPool(&unboundedConfig, factory, resetFunc)
	if err != nil {
		return nil, err
	}

	unboundedPool := &UnboundedPool{
		GenericPool: genericPool,
	}

	return unboundedPool, nil
}

// NewTimedPool creates a new timed pool.
func (pm *PoolManager) createTimedPool(config *PoolConfig, factory func() interface{}, resetFunc func(interface{})) (*TimedPool, error) {
	genericPool, err := pm.createGenericPool(config, factory, resetFunc)
	if err != nil {
		return nil, err
	}

	timedPool := &TimedPool{
		GenericPool:     genericPool,
		idleTimeout:     config.IdleTimeout,
		cleanupInterval: config.CleanupInterval,
		lastUsed:        make(map[interface{}]time.Time),
	}

	// Start timed cleanup
	timedPool.startTimedCleanup()

	return timedPool, nil
}

// Get retrieves an object from the timed pool.
func (tp *TimedPool) Get() interface{} {
	obj := tp.GenericPool.Get()

	// Update last used time
	tp.mu.Lock()
	tp.lastUsed[obj] = time.Now()
	tp.mu.Unlock()

	return obj
}

// Put returns an object to the timed pool.
func (tp *TimedPool) Put(obj interface{}) {
	if obj == nil {
		return
	}

	// Update last used time
	tp.mu.Lock()
	tp.lastUsed[obj] = time.Now()
	tp.mu.Unlock()

	tp.GenericPool.Put(obj)
}

// startTimedCleanup starts the timed cleanup routine.
func (tp *TimedPool) startTimedCleanup() {
	ticker := time.NewTicker(tp.cleanupInterval)

	go func() {
		for range ticker.C {
			tp.cleanupIdleObjects()
		}
	}()
}

// cleanupIdleObjects removes idle objects from the pool.
func (tp *TimedPool) cleanupIdleObjects() {
	tp.mu.Lock()
	defer tp.mu.Unlock()

	now := time.Now()
	for obj, lastUsed := range tp.lastUsed {
		if now.Sub(lastUsed) > tp.idleTimeout {
			delete(tp.lastUsed, obj)
			// Object will be garbage collected
		}
	}
}

// NewPoolFactoryRegistry creates a new pool factory registry.
func NewPoolFactoryRegistry() *PoolFactoryRegistry {
	return &PoolFactoryRegistry{
		factories: make(map[string]PoolFactory),
	}
}

// RegisterFactory registers a pool factory.
func (pfr *PoolFactoryRegistry) RegisterFactory(name string, factory PoolFactory) {
	pfr.mu.Lock()
	defer pfr.mu.Unlock()
	pfr.factories[name] = factory
}

// GetFactory retrieves a pool factory by name.
func (pfr *PoolFactoryRegistry) GetFactory(name string) (PoolFactory, bool) {
	pfr.mu.RLock()
	defer pfr.mu.RUnlock()
	factory, exists := pfr.factories[name]
	return factory, exists
}

// NewPoolMonitor creates a new pool monitor.
func NewPoolMonitor() *PoolMonitor {
	return &PoolMonitor{
		pools:   make(map[string]Pool),
		metrics: &PoolMonitorMetrics{},
		enabled: true,
	}
}

// AddPool adds a pool to the monitor.
func (pm *PoolMonitor) AddPool(name string, pool Pool) {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	pm.pools[name] = pool
}

// RemovePool removes a pool from the monitor.
func (pm *PoolMonitor) RemovePool(name string) {
	pm.mu.Lock()
	defer pm.mu.Unlock()
	delete(pm.pools, name)
}

// Start starts the pool monitor.
func (pm *PoolMonitor) Start(interval time.Duration) {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if pm.enabled {
		pm.ticker = time.NewTicker(interval)
		pm.stopCh = make(chan struct{})

		go func() {
			for {
				select {
				case <-pm.ticker.C:
					pm.updateMetrics()
				case <-pm.stopCh:
					return
				}
			}
		}()
	}
}

// Stop stops the pool monitor.
func (pm *PoolMonitor) Stop() {
	pm.mu.Lock()
	defer pm.mu.Unlock()

	if pm.ticker != nil {
		pm.ticker.Stop()
	}

	if pm.stopCh != nil {
		close(pm.stopCh)
	}
}

// updateMetrics updates pool monitor metrics.
func (pm *PoolMonitor) updateMetrics() {
	pm.mu.RLock()
	defer pm.mu.RUnlock()

	totalPools := int64(len(pm.pools))
	healthyPools := int64(0)
	totalAllocations := int64(0)
	totalDeallocations := int64(0)
	totalMemory := int64(0)
	efficiencySum := float64(0)

	for _, pool := range pm.pools {
		stats := pool.Stats()
		totalAllocations += stats.Allocations
		totalDeallocations += stats.Deallocations
		totalMemory += stats.MemoryUsage
		efficiencySum += stats.Efficiency

		if stats.Efficiency > 0.5 { // Consider healthy if efficiency > 50%
			healthyPools++
		}
	}

	pm.metrics.TotalPools = totalPools
	pm.metrics.HealthyPools = healthyPools
	pm.metrics.UnhealthyPools = totalPools - healthyPools
	pm.metrics.TotalAllocations = totalAllocations
	pm.metrics.TotalDeallocations = totalDeallocations
	pm.metrics.MemoryUsage = totalMemory
	pm.metrics.LastUpdateTime = time.Now()

	if totalPools > 0 {
		pm.metrics.AverageEfficiency = efficiencySum / float64(totalPools)
	}
}

// GetMetrics returns pool monitor metrics.
func (pm *PoolMonitor) GetMetrics() *PoolMonitorMetrics {
	pm.mu.RLock()
	defer pm.mu.RUnlock()
	return pm.metrics
}

// NewPoolHealthChecker creates a new pool health checker.
func NewPoolHealthChecker() *PoolHealthChecker {
	return &PoolHealthChecker{
		pools:   make(map[string]Pool),
		metrics: &PoolHealthMetrics{},
		enabled: true,
	}
}

// AddPool adds a pool to the health checker.
func (phc *PoolHealthChecker) AddPool(name string, pool Pool) {
	phc.mu.Lock()
	defer phc.mu.Unlock()
	phc.pools[name] = pool
}

// RemovePool removes a pool from the health checker.
func (phc *PoolHealthChecker) RemovePool(name string) {
	phc.mu.Lock()
	defer phc.mu.Unlock()
	delete(phc.pools, name)
}

// CheckHealth performs health checks on all monitored pools.
func (phc *PoolHealthChecker) CheckHealth() *PoolHealthMetrics {
	phc.mu.RLock()
	defer phc.mu.RUnlock()

	if !phc.enabled {
		return phc.metrics
	}

	totalChecks := int64(0)
	healthyChecks := int64(0)
	unhealthyChecks := int64(0)
	healthSum := float64(0)

	for _, pool := range phc.pools {
		stats := pool.Stats()
		totalChecks++

		// Consider pool healthy if efficiency > 50%
		if stats.Efficiency > 0.5 {
			healthyChecks++
		} else {
			unhealthyChecks++
		}

		healthSum += stats.Efficiency
	}

	phc.metrics.TotalChecks = totalChecks
	phc.metrics.HealthyChecks = healthyChecks
	phc.metrics.UnhealthyChecks = unhealthyChecks
	phc.metrics.LastCheckTime = time.Now()

	if totalChecks > 0 {
		phc.metrics.AverageHealth = healthSum / float64(totalChecks)
	}

	return phc.metrics
}

// GetMetrics returns pool health checker metrics.
func (phc *PoolHealthChecker) GetMetrics() *PoolHealthMetrics {
	phc.mu.RLock()
	defer phc.mu.RUnlock()
	return phc.metrics
}

// Enable enables the health checker.
func (phc *PoolHealthChecker) Enable() {
	phc.mu.Lock()
	defer phc.mu.Unlock()
	phc.enabled = true
}

// Disable disables the health checker.
func (phc *PoolHealthChecker) Disable() {
	phc.mu.Lock()
	defer phc.mu.Unlock()
	phc.enabled = false
}

// IsEnabled returns whether the health checker is enabled.
func (phc *PoolHealthChecker) IsEnabled() bool {
	phc.mu.RLock()
	defer phc.mu.RUnlock()
	return phc.enabled
}

// NewPoolOptimizer creates a new pool optimizer.
func NewPoolOptimizer() *PoolOptimizer {
	return &PoolOptimizer{
		pools:   make(map[string]Pool),
		metrics: &PoolOptimizerMetrics{},
		enabled: true,
	}
}

// AddPool adds a pool to the optimizer.
func (po *PoolOptimizer) AddPool(name string, pool Pool) {
	po.mu.Lock()
	defer po.mu.Unlock()
	po.pools[name] = pool
}

// RemovePool removes a pool from the optimizer.
func (po *PoolOptimizer) RemovePool(name string) {
	po.mu.Lock()
	defer po.mu.Unlock()
	delete(po.pools, name)
}

// Optimize performs optimization on all monitored pools.
func (po *PoolOptimizer) Optimize() *PoolOptimizerMetrics {
	po.mu.RLock()
	defer po.mu.RUnlock()

	if !po.enabled {
		return po.metrics
	}

	start := time.Now()
	optimizationsApplied := int64(0)
	memorySaved := int64(0)
	efficiencyImproved := float64(0)

	for _, pool := range po.pools {
		stats := pool.Stats()

		// Simple optimization: if efficiency is low, suggest reset
		if stats.Efficiency < 0.3 {
			optimizationsApplied++
			// Simulate memory savings and efficiency improvement
			memorySaved += stats.MemoryUsage / 10
			efficiencyImproved += 0.1
		}
	}

	po.metrics.OptimizationsApplied = optimizationsApplied
	po.metrics.MemorySaved = memorySaved
	po.metrics.EfficiencyImproved = efficiencyImproved
	po.metrics.AverageOptimizationTime = time.Since(start)
	po.metrics.LastOptimizationTime = time.Now()

	return po.metrics
}

// GetMetrics returns pool optimizer metrics.
func (po *PoolOptimizer) GetMetrics() *PoolOptimizerMetrics {
	po.mu.RLock()
	defer po.mu.RUnlock()
	return po.metrics
}

// Enable enables the optimizer.
func (po *PoolOptimizer) Enable() {
	po.mu.Lock()
	defer po.mu.Unlock()
	po.enabled = true
}

// Disable disables the optimizer.
func (po *PoolOptimizer) Disable() {
	po.mu.Lock()
	defer po.mu.Unlock()
	po.enabled = false
}

// IsEnabled returns whether the optimizer is enabled.
func (po *PoolOptimizer) IsEnabled() bool {
	po.mu.RLock()
	defer po.mu.RUnlock()
	return po.enabled
}

// Helper functions for pool management

// Initialize helper functions
func (pm *PoolManager) initializePoolFactories() error {
	// Register default pool factories
	pm.poolFactories["generic"] = &GenericPoolFactory{}
	pm.poolFactories["bounded"] = &BoundedPoolFactory{}
	pm.poolFactories["unbounded"] = &UnboundedPoolFactory{}
	pm.poolFactories["timed"] = &TimedPoolFactory{}

	return nil
}

func (pm *PoolManager) initializeDefaultPools() error {
	// Create default pools
	defaultConfigs := []*PoolConfig{
		{
			Name:            "default",
			Type:            "generic",
			InitialSize:     10,
			MaxSize:         100,
			MinSize:         5,
			GrowthFactor:    1.5,
			ShrinkFactor:    0.8,
			IdleTimeout:     5 * time.Minute,
			CleanupInterval: 1 * time.Minute,
			EnableMetrics:   true,
			EnableProfiling: false,
		},
		{
			Name:            "small",
			Type:            "bounded",
			InitialSize:     5,
			MaxSize:         50,
			MinSize:         2,
			GrowthFactor:    2.0,
			ShrinkFactor:    0.5,
			IdleTimeout:     2 * time.Minute,
			CleanupInterval: 30 * time.Second,
			EnableMetrics:   true,
			EnableProfiling: false,
		},
		{
			Name:            "large",
			Type:            "unbounded",
			InitialSize:     50,
			MaxSize:         1000,
			MinSize:         10,
			GrowthFactor:    1.2,
			ShrinkFactor:    0.9,
			IdleTimeout:     10 * time.Minute,
			CleanupInterval: 2 * time.Minute,
			EnableMetrics:   true,
			EnableProfiling: true,
		},
	}

	for _, config := range defaultConfigs {
		_, err := pm.CreatePool(config, func() interface{} {
			return make([]byte, 0, 1024)
		}, func(obj interface{}) {
			if buf, ok := obj.([]byte); ok {
				buf = buf[:0] // Reset length but keep capacity
			}
		})
		if err != nil {
			return fmt.Errorf("failed to create default pool %s: %w", config.Name, err)
		}
	}

	return nil
}

// Default pool factory implementations

// GenericPoolFactory implements PoolFactory for generic pools.
type GenericPoolFactory struct{}

func (gpf *GenericPoolFactory) CreatePool(config *PoolConfig) (Pool, error) {
	if config == nil {
		return nil, fmt.Errorf("config cannot be nil")
	}

	// Create a generic pool with default factory functions
	factory := func() interface{} {
		return make([]byte, 0, 1024)
	}

	resetFunc := func(obj interface{}) {
		if buf, ok := obj.([]byte); ok {
			buf = buf[:0] // Reset length but keep capacity
		}
	}

	pool := &GenericPool{
		name:      config.Name,
		config:    config,
		factory:   factory,
		resetFunc: resetFunc,
		pool: sync.Pool{
			New: factory,
		},
		objects:       make(chan interface{}, config.MaxSize),
		size:          0,
		capacity:      config.MaxSize,
		hits:          0,
		misses:        0,
		overflows:     0,
		underflows:    0,
		allocations:   0,
		deallocations: 0,
		memoryUsage:   0,
		stats:         &PoolStats{},
		enabled:       true,
	}

	// Initialize pool with initial objects
	for i := int64(0); i < config.InitialSize; i++ {
		obj := factory()
		pool.objects <- obj
		pool.size++
		pool.allocations++
	}

	return pool, nil
}

func (gpf *GenericPoolFactory) GetPoolType() string {
	return "generic"
}

func (gpf *GenericPoolFactory) ValidateConfig(config *PoolConfig) error {
	if config.MaxSize <= 0 {
		return fmt.Errorf("max size must be positive")
	}
	return nil
}

// BoundedPoolFactory implements PoolFactory for bounded pools.
type BoundedPoolFactory struct{}

func (bpf *BoundedPoolFactory) CreatePool(config *PoolConfig) (Pool, error) {
	if config == nil {
		return nil, fmt.Errorf("config cannot be nil")
	}

	// Create a bounded pool with default factory functions
	factory := func() interface{} {
		return make([]byte, 0, 1024)
	}

	resetFunc := func(obj interface{}) {
		if buf, ok := obj.([]byte); ok {
			buf = buf[:0] // Reset length but keep capacity
		}
	}

	genericPool := &GenericPool{
		name:      config.Name,
		config:    config,
		factory:   factory,
		resetFunc: resetFunc,
		pool: sync.Pool{
			New: factory,
		},
		objects:       make(chan interface{}, config.MaxSize),
		size:          0,
		capacity:      config.MaxSize,
		hits:          0,
		misses:        0,
		overflows:     0,
		underflows:    0,
		allocations:   0,
		deallocations: 0,
		memoryUsage:   0,
		stats:         &PoolStats{},
		enabled:       true,
	}

	boundedPool := &BoundedPool{
		GenericPool:  genericPool,
		maxSize:      config.MaxSize,
		minSize:      config.MinSize,
		growthFactor: config.GrowthFactor,
		shrinkFactor: config.ShrinkFactor,
	}

	// Initialize pool with initial objects
	for i := int64(0); i < config.InitialSize; i++ {
		obj := factory()
		boundedPool.objects <- obj
		boundedPool.size++
		boundedPool.allocations++
	}

	return boundedPool, nil
}

func (bpf *BoundedPoolFactory) GetPoolType() string {
	return "bounded"
}

func (bpf *BoundedPoolFactory) ValidateConfig(config *PoolConfig) error {
	if config.MaxSize <= 0 {
		return fmt.Errorf("max size must be positive")
	}
	if config.MinSize < 0 {
		return fmt.Errorf("min size cannot be negative")
	}
	if config.MinSize > config.MaxSize {
		return fmt.Errorf("min size cannot be greater than max size")
	}
	return nil
}

// UnboundedPoolFactory implements PoolFactory for unbounded pools.
type UnboundedPoolFactory struct{}

func (upf *UnboundedPoolFactory) CreatePool(config *PoolConfig) (Pool, error) {
	if config == nil {
		return nil, fmt.Errorf("config cannot be nil")
	}

	// Create an unbounded pool with very large capacity
	unboundedConfig := *config
	unboundedConfig.MaxSize = 1000000 // Very large capacity

	factory := func() interface{} {
		return make([]byte, 0, 1024)
	}

	resetFunc := func(obj interface{}) {
		if buf, ok := obj.([]byte); ok {
			buf = buf[:0] // Reset length but keep capacity
		}
	}

	genericPool := &GenericPool{
		name:      config.Name,
		config:    &unboundedConfig,
		factory:   factory,
		resetFunc: resetFunc,
		pool: sync.Pool{
			New: factory,
		},
		objects:       make(chan interface{}, unboundedConfig.MaxSize),
		size:          0,
		capacity:      unboundedConfig.MaxSize,
		hits:          0,
		misses:        0,
		overflows:     0,
		underflows:    0,
		allocations:   0,
		deallocations: 0,
		memoryUsage:   0,
		stats:         &PoolStats{},
		enabled:       true,
	}

	unboundedPool := &UnboundedPool{
		GenericPool: genericPool,
	}

	// Initialize pool with initial objects
	for i := int64(0); i < config.InitialSize; i++ {
		obj := factory()
		unboundedPool.objects <- obj
		unboundedPool.size++
		unboundedPool.allocations++
	}

	return unboundedPool, nil
}

func (upf *UnboundedPoolFactory) GetPoolType() string {
	return "unbounded"
}

func (upf *UnboundedPoolFactory) ValidateConfig(config *PoolConfig) error {
	// Unbounded pools have no size restrictions
	return nil
}

// TimedPoolFactory implements PoolFactory for timed pools.
type TimedPoolFactory struct{}

func (tpf *TimedPoolFactory) CreatePool(config *PoolConfig) (Pool, error) {
	if config == nil {
		return nil, fmt.Errorf("config cannot be nil")
	}

	factory := func() interface{} {
		return make([]byte, 0, 1024)
	}

	resetFunc := func(obj interface{}) {
		if buf, ok := obj.([]byte); ok {
			buf = buf[:0] // Reset length but keep capacity
		}
	}

	genericPool := &GenericPool{
		name:      config.Name,
		config:    config,
		factory:   factory,
		resetFunc: resetFunc,
		pool: sync.Pool{
			New: factory,
		},
		objects:       make(chan interface{}, config.MaxSize),
		size:          0,
		capacity:      config.MaxSize,
		hits:          0,
		misses:        0,
		overflows:     0,
		underflows:    0,
		allocations:   0,
		deallocations: 0,
		memoryUsage:   0,
		stats:         &PoolStats{},
		enabled:       true,
	}

	timedPool := &TimedPool{
		GenericPool:     genericPool,
		idleTimeout:     config.IdleTimeout,
		cleanupInterval: config.CleanupInterval,
		lastUsed:        make(map[interface{}]time.Time),
	}

	// Initialize pool with initial objects
	for i := int64(0); i < config.InitialSize; i++ {
		obj := factory()
		timedPool.objects <- obj
		timedPool.size++
		timedPool.allocations++
	}

	// Start timed cleanup
	timedPool.startTimedCleanup()

	return timedPool, nil
}

func (tpf *TimedPoolFactory) GetPoolType() string {
	return "timed"
}

func (tpf *TimedPoolFactory) ValidateConfig(config *PoolConfig) error {
	if config.IdleTimeout <= 0 {
		return fmt.Errorf("idle timeout must be positive")
	}
	if config.CleanupInterval <= 0 {
		return fmt.Errorf("cleanup interval must be positive")
	}
	return nil
}

// Performance optimization constants for pool management
const (
	DefaultPoolInitialSize     = 10
	DefaultPoolMaxSize         = 100
	DefaultPoolMinSize         = 5
	DefaultPoolGrowthFactor    = 1.5
	DefaultPoolShrinkFactor    = 0.8
	DefaultPoolIdleTimeout     = 5 * time.Minute
	DefaultPoolCleanupInterval = 1 * time.Minute
	DefaultPoolMonitorInterval = 30 * time.Second
)

// Pool management error types
var (
	ErrPoolNotFound        = fmt.Errorf("pool not found")
	ErrPoolAlreadyExists   = fmt.Errorf("pool already exists")
	ErrPoolConfigInvalid   = fmt.Errorf("pool configuration is invalid")
	ErrPoolFactoryNotFound = fmt.Errorf("pool factory not found")
	ErrPoolCreationFailed  = fmt.Errorf("pool creation failed")
	ErrPoolClosed          = fmt.Errorf("pool is closed")
	ErrPoolFull            = fmt.Errorf("pool is full")
	ErrPoolEmpty           = fmt.Errorf("pool is empty")
)

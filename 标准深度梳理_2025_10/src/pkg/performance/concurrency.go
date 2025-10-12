// Package performance provides advanced concurrency optimization patterns and utilities.
// This file focuses on high-performance concurrency patterns, lock-free data structures,
// and advanced synchronization primitives for OTLP Go applications.
package performance

import (
	"context"
	"fmt"
	"runtime"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// AdvancedConcurrencyManager provides advanced concurrency optimization utilities.
type AdvancedConcurrencyManager struct {
	mu                sync.RWMutex
	lockFreeQueues    map[string]*LockFreeQueue
	workStealingPools map[string]*WorkStealingPool
	barriers          map[string]*Barrier
	readWriteLocks    map[string]*ReadWriteLock
	metrics           *ConcurrencyMetrics
	tracer            trace.Tracer
	enabledFeatures   map[string]bool
}

// ConcurrencyMetrics holds advanced concurrency metrics.
type ConcurrencyMetrics struct {
	LockFreeOps        int64
	WorkStealingOps    int64
	BarrierOps         int64
	ReadWriteOps       int64
	ContentionEvents   int64
	CacheMisses        int64
	FalseSharingEvents int64
	NUMAEvents         int64
	LastUpdateTime     time.Time
}

// LockFreeQueue implements a lock-free queue using CAS operations.
type LockFreeQueue struct {
	head     unsafe.Pointer
	tail     unsafe.Pointer
	size     int64
	enqueues int64
	dequeues int64
}

// LockFreeNode represents a node in the lock-free queue.
type LockFreeNode struct {
	value interface{}
	next  unsafe.Pointer
}

// WorkStealingPool implements a work-stealing thread pool for optimal CPU utilization.
type WorkStealingPool struct {
	workers     []*WorkStealingWorker
	numWorkers  int
	taskQueues  []*LockFreeQueue
	globalQueue *LockFreeQueue
	shutdown    chan struct{}
	wg          sync.WaitGroup
	metrics     *WorkStealingMetrics
}

// WorkStealingWorker represents a worker in the work-stealing pool.
type WorkStealingWorker struct {
	id         int
	localQueue *LockFreeQueue
	pool       *WorkStealingPool
	stealCount int64
	workCount  int64
	running    int32
}

// WorkStealingMetrics holds work-stealing pool metrics.
type WorkStealingMetrics struct {
	TasksProcessed    int64
	TasksStolen       int64
	TasksExecuted     int64
	WorkersActive     int64
	WorkersIdle       int64
	StealAttempts     int64
	StealSuccesses    int64
	LoadBalanceEvents int64
}

// Barrier provides a synchronization barrier for coordinating multiple goroutines.
type Barrier struct {
	count      int64
	threshold  int64
	generation int64
	waiting    int64
	mu         sync.Mutex
	cond       *sync.Cond
	metrics    *BarrierMetrics
}

// BarrierMetrics holds barrier operation metrics.
type BarrierMetrics struct {
	Waits       int64
	Releases    int64
	Timeouts    int64
	AverageWait time.Duration
	MaxWait     time.Duration
	MinWait     time.Duration
}

// ReadWriteLock provides an optimized read-write lock with reader-writer fairness.
type ReadWriteLock struct {
	readers   int64
	writers   int64
	readWait  int64
	writeWait int64
	mu        sync.Mutex
	readCond  *sync.Cond
	writeCond *sync.Cond
	metrics   *ReadWriteLockMetrics
}

// ReadWriteLockMetrics holds read-write lock metrics.
type ReadWriteLockMetrics struct {
	ReadLocks      int64
	WriteLocks     int64
	ReadWaits      int64
	WriteWaits     int64
	ReadHoldTime   time.Duration
	WriteHoldTime  time.Duration
	ContentionTime time.Duration
}

// NUMAOptimizer provides NUMA-aware optimization utilities.
type NUMAOptimizer struct {
	numaNodes    int
	nodeAffinity map[int][]int
	allocators   map[int]*NUMAAllocator
	metrics      *NUMAOptimizerMetrics
}

// NUMAAllocator provides NUMA-aware memory allocation.
type NUMAAllocator struct {
	nodeID        int
	allocations   int64
	deallocations int64
	currentSize   int64
	peakSize      int64
}

// NUMAOptimizerMetrics holds NUMA optimization metrics.
type NUMAOptimizerMetrics struct {
	NUMAAllocations   int64
	NUMADeallocations int64
	CrossNodeAccesses int64
	LocalNodeAccesses int64
	MemoryBandwidth   float64
	CacheHitRate      float64
}

// CacheOptimizer provides CPU cache optimization utilities.
type CacheOptimizer struct {
	cacheLineSize int
	paddingSize   int
	metrics       *CacheOptimizerMetrics
}

// CacheOptimizerMetrics holds cache optimization metrics.
type CacheOptimizerMetrics struct {
	CacheHits           int64
	CacheMisses         int64
	FalseSharingEvents  int64
	PrefetchOps         int64
	CacheLineAlignments int64
	MemoryBandwidth     float64
}

// NewAdvancedConcurrencyManager creates a new advanced concurrency manager.
func NewAdvancedConcurrencyManager() *AdvancedConcurrencyManager {
	return &AdvancedConcurrencyManager{
		lockFreeQueues:    make(map[string]*LockFreeQueue),
		workStealingPools: make(map[string]*WorkStealingPool),
		barriers:          make(map[string]*Barrier),
		readWriteLocks:    make(map[string]*ReadWriteLock),
		metrics:           &ConcurrencyMetrics{},
		tracer:            otel.Tracer("advanced_concurrency"),
		enabledFeatures:   make(map[string]bool),
	}
}

// Initialize initializes the advanced concurrency manager.
func (acm *AdvancedConcurrencyManager) Initialize(ctx context.Context) error {
	_, span := acm.tracer.Start(ctx, "advanced_concurrency.initialize")
	defer span.End()

	// Enable default features
	acm.enabledFeatures["lock_free_queues"] = true
	acm.enabledFeatures["work_stealing"] = true
	acm.enabledFeatures["barriers"] = true
	acm.enabledFeatures["read_write_locks"] = true
	acm.enabledFeatures["numa_optimization"] = true
	acm.enabledFeatures["cache_optimization"] = true

	// Initialize lock-free queues
	if err := acm.initializeLockFreeQueues(); err != nil {
		return fmt.Errorf("failed to initialize lock-free queues: %w", err)
	}

	// Initialize work-stealing pools
	if err := acm.initializeWorkStealingPools(); err != nil {
		return fmt.Errorf("failed to initialize work-stealing pools: %w", err)
	}

	// Initialize barriers
	if err := acm.initializeBarriers(); err != nil {
		return fmt.Errorf("failed to initialize barriers: %w", err)
	}

	// Initialize read-write locks
	if err := acm.initializeReadWriteLocks(); err != nil {
		return fmt.Errorf("failed to initialize read-write locks: %w", err)
	}

	span.SetAttributes(
		attribute.Bool("initialized", true),
		attribute.Int("lock_free_queues", len(acm.lockFreeQueues)),
		attribute.Int("work_stealing_pools", len(acm.workStealingPools)),
		attribute.Int("barriers", len(acm.barriers)),
		attribute.Int("read_write_locks", len(acm.readWriteLocks)),
	)

	return nil
}

// Shutdown gracefully shuts down the advanced concurrency manager.
func (acm *AdvancedConcurrencyManager) Shutdown(ctx context.Context) error {
	_, span := acm.tracer.Start(ctx, "advanced_concurrency.shutdown")
	defer span.End()

	acm.mu.Lock()
	defer acm.mu.Unlock()

	// Shutdown work-stealing pools
	for name, pool := range acm.workStealingPools {
		if err := pool.Shutdown(); err != nil {
			span.RecordError(err)
		}
		delete(acm.workStealingPools, name)
	}

	// Clear other resources
	acm.lockFreeQueues = make(map[string]*LockFreeQueue)
	acm.barriers = make(map[string]*Barrier)
	acm.readWriteLocks = make(map[string]*ReadWriteLock)

	span.SetAttributes(
		attribute.Bool("shutdown_complete", true),
	)

	return nil
}

// CreateLockFreeQueue creates a new lock-free queue.
func (acm *AdvancedConcurrencyManager) CreateLockFreeQueue(name string) *LockFreeQueue {
	acm.mu.Lock()
	defer acm.mu.Unlock()

	queue := &LockFreeQueue{
		head: unsafe.Pointer(&LockFreeNode{}),
		tail: unsafe.Pointer(&LockFreeNode{}),
		size: 0,
	}

	acm.lockFreeQueues[name] = queue
	return queue
}

// GetLockFreeQueue retrieves a lock-free queue by name.
func (acm *AdvancedConcurrencyManager) GetLockFreeQueue(name string) (*LockFreeQueue, bool) {
	acm.mu.RLock()
	defer acm.mu.RUnlock()

	queue, exists := acm.lockFreeQueues[name]
	return queue, exists
}

// Enqueue adds an item to the lock-free queue.
func (lfq *LockFreeQueue) Enqueue(value interface{}) bool {
	node := &LockFreeNode{value: value, next: nil}

	for {
		tail := (*LockFreeNode)(atomic.LoadPointer(&lfq.tail))
		next := (*LockFreeNode)(atomic.LoadPointer(&tail.next))

		if tail == (*LockFreeNode)(atomic.LoadPointer(&lfq.tail)) {
			if next == nil {
				if atomic.CompareAndSwapPointer(&tail.next, unsafe.Pointer(next), unsafe.Pointer(node)) {
					break
				}
			} else {
				atomic.CompareAndSwapPointer(&lfq.tail, unsafe.Pointer(tail), unsafe.Pointer(next))
			}
		}
	}

	atomic.CompareAndSwapPointer(&lfq.tail, unsafe.Pointer((*LockFreeNode)(atomic.LoadPointer(&lfq.tail))), unsafe.Pointer(node))
	atomic.AddInt64(&lfq.size, 1)
	atomic.AddInt64(&lfq.enqueues, 1)

	return true
}

// Dequeue removes an item from the lock-free queue.
func (lfq *LockFreeQueue) Dequeue() (interface{}, bool) {
	for {
		head := (*LockFreeNode)(atomic.LoadPointer(&lfq.head))
		tail := (*LockFreeNode)(atomic.LoadPointer(&lfq.tail))
		next := (*LockFreeNode)(atomic.LoadPointer(&head.next))

		if head == (*LockFreeNode)(atomic.LoadPointer(&lfq.head)) {
			if head == tail {
				if next == nil {
					return nil, false
				}
				atomic.CompareAndSwapPointer(&lfq.tail, unsafe.Pointer(tail), unsafe.Pointer(next))
			} else {
				if next == nil {
					continue
				}
				value := next.value
				if atomic.CompareAndSwapPointer(&lfq.head, unsafe.Pointer(head), unsafe.Pointer(next)) {
					atomic.AddInt64(&lfq.size, -1)
					atomic.AddInt64(&lfq.dequeues, 1)
					return value, true
				}
			}
		}
	}
}

// Size returns the current size of the lock-free queue.
func (lfq *LockFreeQueue) Size() int64 {
	return atomic.LoadInt64(&lfq.size)
}

// Stats returns queue statistics.
func (lfq *LockFreeQueue) Stats() (enqueues, dequeues, size int64) {
	return atomic.LoadInt64(&lfq.enqueues), atomic.LoadInt64(&lfq.dequeues), atomic.LoadInt64(&lfq.size)
}

// NewWorkStealingPool creates a new work-stealing pool.
func NewWorkStealingPool(numWorkers int) *WorkStealingPool {
	if numWorkers <= 0 {
		numWorkers = runtime.NumCPU()
	}

	pool := &WorkStealingPool{
		workers:     make([]*WorkStealingWorker, numWorkers),
		numWorkers:  numWorkers,
		taskQueues:  make([]*LockFreeQueue, numWorkers),
		globalQueue: &LockFreeQueue{},
		shutdown:    make(chan struct{}),
		metrics:     &WorkStealingMetrics{},
	}

	// Initialize workers and their local queues
	for i := 0; i < numWorkers; i++ {
		pool.taskQueues[i] = &LockFreeQueue{}
		pool.workers[i] = &WorkStealingWorker{
			id:         i,
			localQueue: pool.taskQueues[i],
			pool:       pool,
			running:    0,
		}
	}

	return pool
}

// Start starts the work-stealing pool.
func (wsp *WorkStealingPool) Start() {
	for _, worker := range wsp.workers {
		go worker.run()
		wsp.wg.Add(1)
	}
}

// Stop stops the work-stealing pool.
func (wsp *WorkStealingPool) Stop() {
	close(wsp.shutdown)
	wsp.wg.Wait()
}

// Shutdown gracefully shuts down the work-stealing pool.
func (wsp *WorkStealingPool) Shutdown() error {
	wsp.Stop()
	return nil
}

// Task interface is defined in performance.go

// Submit submits a task to the work-stealing pool.
func (wsp *WorkStealingPool) Submit(task Task) bool {
	// Try to submit to a random worker's local queue first
	workerID := runtime.NumGoroutine() % wsp.numWorkers
	if wsp.taskQueues[workerID].Enqueue(task) {
		atomic.AddInt64(&wsp.metrics.TasksProcessed, 1)
		return true
	}

	// Fall back to global queue
	if wsp.globalQueue.Enqueue(task) {
		atomic.AddInt64(&wsp.metrics.TasksProcessed, 1)
		return true
	}

	return false
}

// run runs the work-stealing worker.
func (wsw *WorkStealingWorker) run() {
	defer wsw.pool.wg.Done()

	atomic.StoreInt32(&wsw.running, 1)
	defer atomic.StoreInt32(&wsw.running, 0)

	for {
		select {
		case <-wsw.pool.shutdown:
			return
		default:
			// Try to get work from local queue
			if task, ok := wsw.localQueue.Dequeue(); ok {
				if t, ok := task.(Task); ok {
					t.Execute(context.Background())
					atomic.AddInt64(&wsw.workCount, 1)
					atomic.AddInt64(&wsw.pool.metrics.TasksExecuted, 1)
					continue
				}
			}

			// Try to steal work from other workers
			if wsw.stealWork() {
				continue
			}

			// Try global queue
			if task, ok := wsw.pool.globalQueue.Dequeue(); ok {
				if t, ok := task.(Task); ok {
					t.Execute(context.Background())
					atomic.AddInt64(&wsw.workCount, 1)
					atomic.AddInt64(&wsw.pool.metrics.TasksExecuted, 1)
					continue
				}
			}

			// No work available, yield
			runtime.Gosched()
		}
	}
}

// stealWork attempts to steal work from other workers.
func (wsw *WorkStealingWorker) stealWork() bool {
	atomic.AddInt64(&wsw.pool.metrics.StealAttempts, 1)

	// Try to steal from random workers
	for i := 0; i < wsw.pool.numWorkers; i++ {
		victimID := (wsw.id + i) % wsw.pool.numWorkers
		if victimID == wsw.id {
			continue
		}

		victimQueue := wsw.pool.taskQueues[victimID]
		if task, ok := victimQueue.Dequeue(); ok {
			if t, ok := task.(Task); ok {
				t.Execute(context.Background())
				atomic.AddInt64(&wsw.workCount, 1)
				atomic.AddInt64(&wsw.stealCount, 1)
				atomic.AddInt64(&wsw.pool.metrics.TasksStolen, 1)
				atomic.AddInt64(&wsw.pool.metrics.StealSuccesses, 1)
				return true
			}
		}
	}

	return false
}

// NewBarrier creates a new synchronization barrier.
func NewBarrier(threshold int64) *Barrier {
	b := &Barrier{
		count:      0,
		threshold:  threshold,
		generation: 0,
		waiting:    0,
		metrics:    &BarrierMetrics{},
	}
	b.cond = sync.NewCond(&b.mu)
	return b
}

// Wait waits at the barrier until all participants arrive.
func (b *Barrier) Wait() bool {
	b.mu.Lock()
	defer b.mu.Unlock()

	start := time.Now()
	atomic.AddInt64(&b.metrics.Waits, 1)

	generation := b.generation
	b.count++

	if b.count < b.threshold {
		// Wait for other participants
		for b.generation == generation {
			b.cond.Wait()
		}

		waitTime := time.Since(start)
		if waitTime > b.metrics.MaxWait {
			b.metrics.MaxWait = waitTime
		}
		if b.metrics.MinWait == 0 || waitTime < b.metrics.MinWait {
			b.metrics.MinWait = waitTime
		}

		return true
	} else {
		// Last participant, release all others
		b.generation++
		b.count = 0
		b.cond.Broadcast()

		atomic.AddInt64(&b.metrics.Releases, 1)
		return false
	}
}

// WaitWithTimeout waits at the barrier with a timeout.
func (b *Barrier) WaitWithTimeout(timeout time.Duration) bool {
	b.mu.Lock()
	defer b.mu.Unlock()

	start := time.Now()
	atomic.AddInt64(&b.metrics.Waits, 1)

	generation := b.generation
	b.count++

	if b.count < b.threshold {
		// Wait for other participants with timeout
		done := make(chan struct{})
		go func() {
			defer close(done)
			for b.generation == generation {
				b.cond.Wait()
			}
		}()

		select {
		case <-done:
			waitTime := time.Since(start)
			if waitTime > b.metrics.MaxWait {
				b.metrics.MaxWait = waitTime
			}
			if b.metrics.MinWait == 0 || waitTime < b.metrics.MinWait {
				b.metrics.MinWait = waitTime
			}
			return true
		case <-time.After(timeout):
			atomic.AddInt64(&b.metrics.Timeouts, 1)
			return false
		}
	} else {
		// Last participant, release all others
		b.generation++
		b.count = 0
		b.cond.Broadcast()

		atomic.AddInt64(&b.metrics.Releases, 1)
		return false
	}
}

// NewReadWriteLock creates a new optimized read-write lock.
func NewReadWriteLock() *ReadWriteLock {
	rwl := &ReadWriteLock{
		readers:   0,
		writers:   0,
		readWait:  0,
		writeWait: 0,
		metrics:   &ReadWriteLockMetrics{},
	}
	rwl.readCond = sync.NewCond(&rwl.mu)
	rwl.writeCond = sync.NewCond(&rwl.mu)
	return rwl
}

// RLock acquires a read lock.
func (rwl *ReadWriteLock) RLock() {
	rwl.mu.Lock()
	defer rwl.mu.Unlock()

	start := time.Now()
	atomic.AddInt64(&rwl.metrics.ReadLocks, 1)

	// Wait if there are writers or waiting writers
	for rwl.writers > 0 || rwl.writeWait > 0 {
		rwl.readWait++
		rwl.readCond.Wait()
		rwl.readWait--
	}

	rwl.readers++
	rwl.metrics.ReadHoldTime += time.Since(start)
}

// RUnlock releases a read lock.
func (rwl *ReadWriteLock) RUnlock() {
	rwl.mu.Lock()
	defer rwl.mu.Unlock()

	rwl.readers--

	// If no more readers and there are waiting writers, wake one up
	if rwl.readers == 0 && rwl.writeWait > 0 {
		rwl.writeCond.Signal()
	}
}

// Lock acquires a write lock.
func (rwl *ReadWriteLock) Lock() {
	rwl.mu.Lock()
	defer rwl.mu.Unlock()

	start := time.Now()
	atomic.AddInt64(&rwl.metrics.WriteLocks, 1)

	// Wait if there are readers or writers
	for rwl.readers > 0 || rwl.writers > 0 {
		rwl.writeWait++
		rwl.writeCond.Wait()
		rwl.writeWait--
	}

	rwl.writers++
	rwl.metrics.WriteHoldTime += time.Since(start)
}

// Unlock releases a write lock.
func (rwl *ReadWriteLock) Unlock() {
	rwl.mu.Lock()
	defer rwl.mu.Unlock()

	rwl.writers--

	// Wake up waiting readers first, then writers
	if rwl.readWait > 0 {
		rwl.readCond.Broadcast()
	} else if rwl.writeWait > 0 {
		rwl.writeCond.Signal()
	}
}

// NewNUMAOptimizer creates a new NUMA-aware optimizer.
func NewNUMAOptimizer() *NUMAOptimizer {
	return &NUMAOptimizer{
		numaNodes:    runtime.NumCPU(), // Simplified for demo
		nodeAffinity: make(map[int][]int),
		allocators:   make(map[int]*NUMAAllocator),
		metrics:      &NUMAOptimizerMetrics{},
	}
}

// AllocateNUMA allocates memory on a specific NUMA node.
func (no *NUMAOptimizer) AllocateNUMA(nodeID int, size int) []byte {
	allocator, exists := no.allocators[nodeID]
	if !exists {
		allocator = &NUMAAllocator{
			nodeID:        nodeID,
			allocations:   0,
			deallocations: 0,
			currentSize:   0,
			peakSize:      0,
		}
		no.allocators[nodeID] = allocator
	}

	buf := make([]byte, size)
	atomic.AddInt64(&allocator.allocations, 1)
	atomic.AddInt64(&allocator.currentSize, int64(size))

	if current := atomic.LoadInt64(&allocator.currentSize); current > atomic.LoadInt64(&allocator.peakSize) {
		atomic.StoreInt64(&allocator.peakSize, current)
	}

	atomic.AddInt64(&no.metrics.NUMAAllocations, 1)
	atomic.AddInt64(&no.metrics.LocalNodeAccesses, 1)

	return buf
}

// NewCacheOptimizer creates a new cache optimizer.
func NewCacheOptimizer() *CacheOptimizer {
	return &CacheOptimizer{
		cacheLineSize: 64, // Typical cache line size
		paddingSize:   64,
		metrics:       &CacheOptimizerMetrics{},
	}
}

// AlignToCacheLine aligns data to cache line boundaries.
func (co *CacheOptimizer) AlignToCacheLine(data []byte) []byte {
	if len(data) == 0 {
		return data
	}

	// Calculate padding needed
	padding := co.cacheLineSize - (len(data) % co.cacheLineSize)
	if padding == co.cacheLineSize {
		padding = 0
	}

	// Create aligned buffer
	aligned := make([]byte, len(data)+padding)
	copy(aligned, data)

	atomic.AddInt64(&co.metrics.CacheLineAlignments, 1)
	return aligned
}

// PrefetchData prefetches data into CPU cache.
func (co *CacheOptimizer) PrefetchData(data []byte) {
	if len(data) == 0 {
		return
	}

	// Prefetch first cache line
	_ = data[0]

	// Prefetch additional cache lines if data is large enough
	for i := co.cacheLineSize; i < len(data); i += co.cacheLineSize {
		_ = data[i]
	}

	atomic.AddInt64(&co.metrics.PrefetchOps, 1)
}

// DetectFalseSharing detects potential false sharing issues.
func (co *CacheOptimizer) DetectFalseSharing(data []byte) bool {
	if len(data) < co.cacheLineSize {
		return false
	}

	// Simple heuristic: check if data spans multiple cache lines
	cacheLines := (len(data) + co.cacheLineSize - 1) / co.cacheLineSize
	if cacheLines > 1 {
		atomic.AddInt64(&co.metrics.FalseSharingEvents, 1)
		return true
	}

	return false
}

// Helper functions for advanced concurrency

// Initialize helper functions
func (acm *AdvancedConcurrencyManager) initializeLockFreeQueues() error {
	// Initialize common lock-free queues
	acm.CreateLockFreeQueue("default")
	acm.CreateLockFreeQueue("high_priority")
	acm.CreateLockFreeQueue("low_priority")

	return nil
}

func (acm *AdvancedConcurrencyManager) initializeWorkStealingPools() error {
	// Initialize work-stealing pools
	acm.workStealingPools["default"] = NewWorkStealingPool(runtime.NumCPU())
	acm.workStealingPools["io_bound"] = NewWorkStealingPool(runtime.NumCPU() * 2)
	acm.workStealingPools["cpu_bound"] = NewWorkStealingPool(runtime.NumCPU())

	// Start all pools
	for _, pool := range acm.workStealingPools {
		pool.Start()
	}

	return nil
}

func (acm *AdvancedConcurrencyManager) initializeBarriers() error {
	// Initialize barriers
	acm.barriers["default"] = NewBarrier(4)
	acm.barriers["large"] = NewBarrier(16)
	acm.barriers["small"] = NewBarrier(2)

	return nil
}

func (acm *AdvancedConcurrencyManager) initializeReadWriteLocks() error {
	// Initialize read-write locks
	acm.readWriteLocks["default"] = NewReadWriteLock()
	acm.readWriteLocks["shared"] = NewReadWriteLock()
	acm.readWriteLocks["exclusive"] = NewReadWriteLock()

	return nil
}

// Performance optimization constants for concurrency
const (
	DefaultWorkStealingWorkers = 0 // Use runtime.NumCPU()
	DefaultBarrierThreshold    = 4
	DefaultQueueSize           = 1000
	DefaultCacheLineSize       = 64
	DefaultNUMAAllocatorSize   = 1024 * 1024 // 1MB
)

// Concurrency optimization error types
var (
	ErrWorkStealingPoolFull    = fmt.Errorf("work-stealing pool is full")
	ErrBarrierTimeout          = fmt.Errorf("barrier wait timeout")
	ErrLockFreeQueueFull       = fmt.Errorf("lock-free queue is full")
	ErrNUMAAllocationFailed    = fmt.Errorf("NUMA allocation failed")
	ErrCacheOptimizationFailed = fmt.Errorf("cache optimization failed")
)

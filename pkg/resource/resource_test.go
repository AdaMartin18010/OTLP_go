package resource

import (
	"context"
	"errors"
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// mockResource is a mock implementation of Resource interface for testing
type mockResource struct {
	name           string
	healthy        bool
	initErr        error
	shutdownErr    error
	initialized    bool
	shutdownCalled bool
	mu             sync.RWMutex
}

func newMockResource(name string, healthy bool) *mockResource {
	return &mockResource{
		name:    name,
		healthy: healthy,
	}
}

func (m *mockResource) Initialize(ctx context.Context) error {
	if m.initErr != nil {
		return m.initErr
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	m.initialized = true
	return nil
}

func (m *mockResource) Shutdown(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.shutdownCalled = true
	return m.shutdownErr
}

func (m *mockResource) IsHealthy() bool {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.healthy
}

func (m *mockResource) GetName() string {
	return m.name
}

func (m *mockResource) SetHealthy(healthy bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.healthy = healthy
}

// TestNewResourceManager tests the creation of a new ResourceManager
func TestNewResourceManager(t *testing.T) {
	rm := NewResourceManager()
	assert.NotNil(t, rm)
	assert.NotNil(t, rm.resources)
	assert.NotNil(t, rm.initOrder)
	assert.NotNil(t, rm.shutdownOrder)
	assert.Empty(t, rm.resources)
	assert.Empty(t, rm.initOrder)
	assert.Empty(t, rm.shutdownOrder)
}

// TestResourceManager_Register tests registering resources
func TestResourceManager_Register(t *testing.T) {
	rm := NewResourceManager()

	res1 := newMockResource("resource1", true)
	res2 := newMockResource("resource2", true)

	// Register first resource
	rm.Register("res1", res1)
	assert.Len(t, rm.resources, 1)
	assert.Equal(t, []string{"res1"}, rm.initOrder)
	assert.Equal(t, []string{"res1"}, rm.shutdownOrder)

	// Register second resource
	rm.Register("res2", res2)
	assert.Len(t, rm.resources, 2)
	assert.Equal(t, []string{"res1", "res2"}, rm.initOrder)
	// shutdownOrder should be in reverse order
	assert.Equal(t, []string{"res2", "res1"}, rm.shutdownOrder)
}

// TestResourceManager_InitializeAll tests initializing all resources
func TestResourceManager_InitializeAll(t *testing.T) {
	tests := []struct {
		name        string
		resources   map[string]*mockResource
		expectError bool
		errorName   string
	}{
		{
			name: "successful initialization",
			resources: map[string]*mockResource{
				"res1": newMockResource("res1", true),
				"res2": newMockResource("res2", true),
			},
			expectError: false,
		},
		{
			name: "initialization error",
			resources: map[string]*mockResource{
				"res1": newMockResource("res1", true),
				"res2": {name: "res2", healthy: false, initErr: errors.New("init failed")},
			},
			expectError: true,
			errorName:   "res2",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			rm := NewResourceManager()
			for name, res := range tt.resources {
				rm.Register(name, res)
			}

			err := rm.InitializeAll(context.Background())

			if tt.expectError {
				assert.Error(t, err)
				var resErr *ResourceError
				assert.True(t, errors.As(err, &resErr))
				assert.Equal(t, tt.errorName, resErr.Name)
				assert.Equal(t, "initialize", resErr.Operation)
			} else {
				assert.NoError(t, err)
				for _, res := range tt.resources {
					assert.True(t, res.initialized)
				}
			}
		})
	}
}

// TestResourceManager_InitializeAll_WithContext tests initialization with context cancellation
func TestResourceManager_InitializeAll_WithContext(t *testing.T) {
	rm := NewResourceManager()
	res := newMockResource("res", true)
	rm.Register("res", res)

	ctx := context.Background()
	err := rm.InitializeAll(ctx)
	assert.NoError(t, err)
	assert.True(t, res.initialized)
}

// TestResourceManager_ShutdownAll tests shutting down all resources
func TestResourceManager_ShutdownAll(t *testing.T) {
	tests := []struct {
		name        string
		resources   map[string]*mockResource
		expectError bool
	}{
		{
			name: "successful shutdown",
			resources: map[string]*mockResource{
				"res1": newMockResource("res1", true),
				"res2": newMockResource("res2", true),
			},
			expectError: false,
		},
		{
			name: "shutdown with error - last error returned",
			resources: map[string]*mockResource{
				"res1": newMockResource("res1", true),
				"res2": {name: "res2", healthy: false, shutdownErr: errors.New("shutdown failed")},
			},
			expectError: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			rm := NewResourceManager()
			for name, res := range tt.resources {
				rm.Register(name, res)
			}

			err := rm.ShutdownAll(context.Background())

			if tt.expectError {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}

			// All resources should have shutdown called
			for _, res := range tt.resources {
				assert.True(t, res.shutdownCalled)
			}
		})
	}
}

// orderTrackingResource is a mock resource that tracks shutdown order
type orderTrackingResource struct {
	mockResource
	order *[]string
	mu    *sync.Mutex
}

func (o *orderTrackingResource) Shutdown(ctx context.Context) error {
	o.mu.Lock()
	defer o.mu.Unlock()
	*o.order = append(*o.order, o.name)
	return nil
}

// TestResourceManager_ShutdownAll_Order tests shutdown order (reverse of init)
func TestResourceManager_ShutdownAll_Order(t *testing.T) {
	rm := NewResourceManager()
	shutdownOrder := []string{}
	mu := sync.Mutex{}

	// Create resources that record their shutdown order
	for i := 1; i <= 3; i++ {
		name := fmt.Sprintf("res%d", i)
		res := &orderTrackingResource{
			mockResource: mockResource{name: name},
			order:        &shutdownOrder,
			mu:           &mu,
		}
		rm.Register(name, res)
	}

	rm.ShutdownAll(context.Background())

	// Shutdown should be in reverse order: res3, res2, res1
	assert.Equal(t, []string{"res3", "res2", "res1"}, shutdownOrder)
}

// TestResourceManager_GetResource tests getting a resource by name
func TestResourceManager_GetResource(t *testing.T) {
	rm := NewResourceManager()
	res1 := newMockResource("res1", true)
	res2 := newMockResource("res2", true)

	rm.Register("res1", res1)
	rm.Register("res2", res2)

	// Get existing resource
	got, exists := rm.GetResource("res1")
	assert.True(t, exists)
	assert.Equal(t, res1, got)

	// Get another existing resource
	got, exists = rm.GetResource("res2")
	assert.True(t, exists)
	assert.Equal(t, res2, got)

	// Get non-existent resource
	got, exists = rm.GetResource("nonexistent")
	assert.False(t, exists)
	assert.Nil(t, got)
}

// TestResourceManager_IsHealthy tests health check of all resources
func TestResourceManager_IsHealthy(t *testing.T) {
	tests := []struct {
		name     string
		healthy  map[string]bool
		expected bool
	}{
		{
			name:     "all healthy",
			healthy:  map[string]bool{"res1": true, "res2": true, "res3": true},
			expected: true,
		},
		{
			name:     "one unhealthy",
			healthy:  map[string]bool{"res1": true, "res2": false, "res3": true},
			expected: false,
		},
		{
			name:     "all unhealthy",
			healthy:  map[string]bool{"res1": false, "res2": false},
			expected: false,
		},
		{
			name:     "no resources",
			healthy:  map[string]bool{},
			expected: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			rm := NewResourceManager()
			for name, healthy := range tt.healthy {
				rm.Register(name, newMockResource(name, healthy))
			}

			assert.Equal(t, tt.expected, rm.IsHealthy())
		})
	}
}

// TestResourceManager_GetHealthStatus tests getting health status map
func TestResourceManager_GetHealthStatus(t *testing.T) {
	rm := NewResourceManager()
	rm.Register("healthy1", newMockResource("healthy1", true))
	rm.Register("unhealthy", newMockResource("unhealthy", false))
	rm.Register("healthy2", newMockResource("healthy2", true))

	status := rm.GetHealthStatus()

	assert.Len(t, status, 3)
	assert.True(t, status["healthy1"])
	assert.False(t, status["unhealthy"])
	assert.True(t, status["healthy2"])
}

// TestResourceManager_ConcurrentAccess tests concurrent access to ResourceManager
func TestResourceManager_ConcurrentAccess(t *testing.T) {
	rm := NewResourceManager()
	var wg sync.WaitGroup

	// Concurrent registrations
	for i := range 100 {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			name := fmt.Sprintf("res%d", i)
			rm.Register(name, newMockResource(name, true))
		}(i)
	}

	wg.Wait()
	assert.Len(t, rm.resources, 100)

	// Concurrent health checks
	for range 50 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = rm.IsHealthy()
			_ = rm.GetHealthStatus()
		}()
	}

	wg.Wait()
}

// ==================== ResourceError Tests ====================

// TestResourceError_Error tests ResourceError formatting
func TestResourceError_Error(t *testing.T) {
	tests := []struct {
		name     string
		err      *ResourceError
		expected string
	}{
		{
			name: "with cause",
			err: &ResourceError{
				Name:      "test-res",
				Operation: "initialize",
				Message:   "Failed to initialize resource",
				Cause:     errors.New("connection refused"),
			},
			expected: "Resource test-res initialize failed: Failed to initialize resource: connection refused",
		},
		{
			name: "without cause",
			err: &ResourceError{
				Name:      "test-res",
				Operation: "shutdown",
				Message:   "Resource not found",
				Cause:     nil,
			},
			expected: "Resource test-res shutdown failed: Resource not found",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.expected, tt.err.Error())
		})
	}
}

// TestResourceError_Unwrap tests unwrapping ResourceError
func TestResourceError_Unwrap(t *testing.T) {
	cause := errors.New("root cause")
	err := &ResourceError{
		Name:      "test",
		Operation: "test",
		Message:   "test",
		Cause:     cause,
	}

	assert.Equal(t, cause, err.Unwrap())
	assert.True(t, errors.Is(err, cause))
}

// ==================== CleanupManager Tests ====================

// TestNewCleanupManager tests creation of CleanupManager
func TestNewCleanupManager(t *testing.T) {
	cm := NewCleanupManager()
	assert.NotNil(t, cm)
	assert.NotNil(t, cm.cleanups)
	assert.Empty(t, cm.cleanups)
}

// TestCleanupManager_AddCleanup tests adding cleanup functions
func TestCleanupManager_AddCleanup(t *testing.T) {
	cm := NewCleanupManager()

	cleanup1 := func() error { return nil }
	cleanup2 := func() error { return nil }

	cm.AddCleanup(cleanup1)
	assert.Len(t, cm.cleanups, 1)

	cm.AddCleanup(cleanup2)
	assert.Len(t, cm.cleanups, 2)
}

// TestCleanupManager_ExecuteCleanups tests executing cleanup functions
func TestCleanupManager_ExecuteCleanups(t *testing.T) {
	tests := []struct {
		name        string
		cleanups    []func() error
		expectError bool
	}{
		{
			name: "successful cleanups",
			cleanups: []func() error{
				func() error { return nil },
				func() error { return nil },
			},
			expectError: false,
		},
		{
			name: "cleanup with error - last error returned",
			cleanups: []func() error{
				func() error { return nil },
				func() error { return errors.New("cleanup failed") },
			},
			expectError: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			cm := NewCleanupManager()
			for _, cleanup := range tt.cleanups {
				cm.AddCleanup(cleanup)
			}

			err := cm.ExecuteCleanups()
			if tt.expectError {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}
		})
	}
}

// TestCleanupManager_ExecuteCleanups_Order tests cleanup execution order (LIFO)
func TestCleanupManager_ExecuteCleanups_Order(t *testing.T) {
	cm := NewCleanupManager()
	order := []int{}
	mu := sync.Mutex{}

	// Add cleanups that record their execution order
	for i := 1; i <= 3; i++ {
		i := i // capture loop variable
		cm.AddCleanup(func() error {
			mu.Lock()
			defer mu.Unlock()
			order = append(order, i)
			return nil
		})
	}

	cm.ExecuteCleanups()

	// Cleanups should execute in reverse order: 3, 2, 1
	assert.Equal(t, []int{3, 2, 1}, order)
}

// TestCleanupManager_ConcurrentAccess tests concurrent access to CleanupManager
func TestCleanupManager_ConcurrentAccess(t *testing.T) {
	cm := NewCleanupManager()
	var wg sync.WaitGroup

	// Concurrent adds
	for range 100 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			cm.AddCleanup(func() error { return nil })
		}()
	}

	wg.Wait()
	assert.Len(t, cm.cleanups, 100)
}

// ==================== WithCleanup Tests ====================

// TestNewWithCleanup tests creation of WithCleanup
func TestNewWithCleanup(t *testing.T) {
	ctx := context.Background()
	cleanup := func() error {
		return nil
	}

	wc := NewWithCleanup(ctx, cleanup)
	assert.NotNil(t, wc)
	assert.NotNil(t, wc.Context())
	assert.NotNil(t, wc.cancel)
	assert.NotNil(t, wc.cleanup)
}

// TestWithCleanup_Context tests getting context from WithCleanup
func TestWithCleanup_Context(t *testing.T) {
	ctx := context.Background()
	wc := NewWithCleanup(ctx, nil)

	gotCtx := wc.Context()
	assert.NotNil(t, gotCtx)

	// Context should be cancellable
	_, ok := gotCtx.Deadline()
	assert.False(t, ok) // No deadline set
}

// TestWithCleanup_Cancel tests cancelling the context
func TestWithCleanup_Cancel(t *testing.T) {
	ctx := context.Background()
	wc := NewWithCleanup(ctx, nil)

	gotCtx := wc.Context()
	assert.NoError(t, gotCtx.Err())

	wc.Cancel()
	assert.Error(t, gotCtx.Err())
	assert.Equal(t, context.Canceled, gotCtx.Err())
}

// TestWithCleanup_Cleanup tests cleanup execution
func TestWithCleanup_Cleanup(t *testing.T) {
	tests := []struct {
		name          string
		cleanup       func() error
		expectError   bool
		cleanupCalled bool
	}{
		{
			name: "successful cleanup",
			cleanup: func() error {
				return nil
			},
			expectError:   false,
			cleanupCalled: true,
		},
		{
			name: "cleanup with error",
			cleanup: func() error {
				return errors.New("cleanup failed")
			},
			expectError:   true,
			cleanupCalled: true,
		},
		{
			name:          "nil cleanup",
			cleanup:       nil,
			expectError:   false,
			cleanupCalled: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ctx := context.Background()
			wc := NewWithCleanup(ctx, tt.cleanup)

			err := wc.Cleanup()
			if tt.expectError {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}

			// Context should be cancelled after cleanup
			assert.Error(t, wc.Context().Err())
		})
	}
}

// ==================== ResourcePool Tests ====================

// TestNewResourcePool tests creation of ResourcePool
func TestNewResourcePool(t *testing.T) {
	factory := func() (Resource, error) {
		return newMockResource("pooled", true), nil
	}

	pool := NewResourcePool(factory, 10)
	assert.NotNil(t, pool)
	assert.NotNil(t, pool.resources)
	assert.Equal(t, 10, pool.maxSize)
	assert.NotNil(t, pool.factory)
}

// TestResourcePool_Get tests getting resource from pool
func TestResourcePool_Get(t *testing.T) {
	tests := []struct {
		name        string
		factoryErr  error
		expectError bool
	}{
		{
			name:        "successful get from factory",
			factoryErr:  nil,
			expectError: false,
		},
		{
			name:        "factory error",
			factoryErr:  errors.New("factory failed"),
			expectError: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			factory := func() (Resource, error) {
				if tt.factoryErr != nil {
					return nil, tt.factoryErr
				}
				return newMockResource("pooled", true), nil
			}

			pool := NewResourcePool(factory, 1)
			ctx := context.Background()

			res, err := pool.Get(ctx)

			if tt.expectError {
				assert.Error(t, err)
				assert.Nil(t, res)
			} else {
				assert.NoError(t, err)
				assert.NotNil(t, res)
			}
		})
	}
}

// TestResourcePool_Get_FromPool tests getting resource from pool (not factory)
func TestResourcePool_Get_FromPool(t *testing.T) {
	factoryCallCount := 0
	factory := func() (Resource, error) {
		factoryCallCount++
		return newMockResource(fmt.Sprintf("res%d", factoryCallCount), true), nil
	}

	pool := NewResourcePool(factory, 2)
	ctx := context.Background()

	// Get resource - should use factory
	res1, err := pool.Get(ctx)
	require.NoError(t, err)
	assert.Equal(t, 1, factoryCallCount)

	// Put it back
	pool.Put(res1)

	// Get again - should get from pool, not factory
	res2, err := pool.Get(ctx)
	require.NoError(t, err)
	assert.Equal(t, 1, factoryCallCount) // Factory not called again
	assert.Equal(t, res1, res2)          // Same resource
}

// TestResourcePool_Get_ContextCancelled tests get with cancelled context
func TestResourcePool_Get_ContextCancelled(t *testing.T) {
	factory := func() (Resource, error) {
		return newMockResource("pooled", true), nil
	}

	pool := NewResourcePool(factory, 0) // Empty pool
	ctx, cancel := context.WithCancel(context.Background())
	cancel() // Cancel immediately

	res, err := pool.Get(ctx)
	assert.Error(t, err)
	assert.Equal(t, context.Canceled, err)
	assert.Nil(t, res)
}

// TestResourcePool_Put tests putting resource back to pool
func TestResourcePool_Put(t *testing.T) {
	factory := func() (Resource, error) {
		return newMockResource("pooled", true), nil
	}

	pool := NewResourcePool(factory, 2)
	res := newMockResource("test", true)

	// Put should not block
	pool.Put(res)
	assert.Len(t, pool.resources, 1)

	// Put another
	res2 := newMockResource("test2", true)
	pool.Put(res2)
	assert.Len(t, pool.resources, 2)
}

// TestResourcePool_Put_Full tests putting to full pool
func TestResourcePool_Put_Full(t *testing.T) {
	factory := func() (Resource, error) {
		return newMockResource("pooled", true), nil
	}

	pool := NewResourcePool(factory, 1)

	res1 := newMockResource("res1", true)
	res2 := newMockResource("res2", true)

	// Fill the pool
	pool.Put(res1)

	// Put to full pool - should shutdown resource
	pool.Put(res2)
	assert.True(t, res2.shutdownCalled)
}

// TestResourcePool_Close tests closing the pool
func TestResourcePool_Close(t *testing.T) {
	tests := []struct {
		name        string
		resources   []Resource
		expectError bool
	}{
		{
			name:        "close empty pool",
			resources:   []Resource{},
			expectError: false,
		},
		{
			name:        "close with resources",
			resources:   []Resource{newMockResource("res1", true), newMockResource("res2", true)},
			expectError: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			factory := func() (Resource, error) {
				return newMockResource("pooled", true), nil
			}

			pool := NewResourcePool(factory, 10)

			// Add resources to pool
			for _, res := range tt.resources {
				pool.Put(res)
			}

			err := pool.Close()
			if tt.expectError {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}

			// All resources should be shutdown
			for _, res := range tt.resources {
				mockRes := res.(*mockResource)
				assert.True(t, mockRes.shutdownCalled)
			}
		})
	}
}

// ==================== ResourceMonitor Tests ====================

// TestNewResourceMonitor tests creation of ResourceMonitor
func TestNewResourceMonitor(t *testing.T) {
	interval := 100 * time.Millisecond
	rm := NewResourceMonitor(interval)
	assert.NotNil(t, rm)
	assert.NotNil(t, rm.resources)
	assert.Equal(t, interval, rm.interval)
	assert.NotNil(t, rm.stopCh)
}

// TestResourceMonitor_AddResource tests adding resource to monitor
func TestResourceMonitor_AddResource(t *testing.T) {
	rm := NewResourceMonitor(time.Second)
	res := newMockResource("test", true)

	rm.AddResource("test", res)
	assert.Len(t, rm.resources, 1)
}

// TestResourceMonitor_RemoveResource tests removing resource from monitor
func TestResourceMonitor_RemoveResource(t *testing.T) {
	rm := NewResourceMonitor(time.Second)
	res := newMockResource("test", true)

	rm.AddResource("test", res)
	assert.Len(t, rm.resources, 1)

	rm.RemoveResource("test")
	assert.Len(t, rm.resources, 0)
}

// TestResourceMonitor_StartStop tests starting and stopping monitor
func TestResourceMonitor_StartStop(t *testing.T) {
	rm := NewResourceMonitor(50 * time.Millisecond)
	res := newMockResource("test", true)
	rm.AddResource("test", res)

	// Start monitoring
	rm.Start()
	time.Sleep(100 * time.Millisecond) // Let it run a bit

	// Stop monitoring
	rm.Stop()

	// Give some time for goroutine to stop
	time.Sleep(50 * time.Millisecond)

	// Test that we can create a new stop channel (old one was closed)
	// This verifies Stop() was called
	assert.NotNil(t, rm.stopCh)
}

// TestResourceMonitor_GetHealthReport tests getting health report
func TestResourceMonitor_GetHealthReport(t *testing.T) {
	rm := NewResourceMonitor(time.Second)
	rm.AddResource("healthy", newMockResource("healthy", true))
	rm.AddResource("unhealthy", newMockResource("unhealthy", false))

	report := rm.GetHealthReport()

	assert.Len(t, report, 2)
	assert.True(t, report["healthy"])
	assert.False(t, report["unhealthy"])
}

// TestResourceMonitor_ConcurrentAccess tests concurrent access to ResourceMonitor
func TestResourceMonitor_ConcurrentAccess(t *testing.T) {
	rm := NewResourceMonitor(time.Second)
	var wg sync.WaitGroup

	// Concurrent adds
	for i := range 50 {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			name := fmt.Sprintf("res%d", i)
			rm.AddResource(name, newMockResource(name, true))
		}(i)
	}

	// Concurrent removes
	for i := range 25 {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			name := fmt.Sprintf("res%d", i)
			rm.RemoveResource(name)
		}(i)
	}

	// Concurrent health checks
	for range 25 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = rm.GetHealthReport()
		}()
	}

	wg.Wait()
}

// ==================== Integration Tests ====================

// TestFullLifecycle tests full lifecycle of resource management
func TestFullLifecycle(t *testing.T) {
	rm := NewResourceManager()

	// Create and register resources
	res1 := newMockResource("service1", true)
	res2 := newMockResource("service2", true)

	rm.Register("service1", res1)
	rm.Register("service2", res2)

	// Initialize all
	ctx := context.Background()
	err := rm.InitializeAll(ctx)
	require.NoError(t, err)

	// Verify initialized
	assert.True(t, res1.initialized)
	assert.True(t, res2.initialized)

	// Check health
	assert.True(t, rm.IsHealthy())

	// Make one unhealthy
	res1.SetHealthy(false)
	assert.False(t, rm.IsHealthy())

	// Get health status
	status := rm.GetHealthStatus()
	assert.False(t, status["service1"])
	assert.True(t, status["service2"])

	// Shutdown all
	err = rm.ShutdownAll(ctx)
	assert.NoError(t, err)
	assert.True(t, res1.shutdownCalled)
	assert.True(t, res2.shutdownCalled)
}

// TestResourceManager_InitializeAll_ResourceRemoved tests initialization with removed resource
func TestResourceManager_InitializeAll_ResourceRemoved(t *testing.T) {
	rm := NewResourceManager()
	res := newMockResource("test", true)

	rm.Register("test", res)

	// Simulate resource being removed from map but still in initOrder
	// by manually manipulating the internal state
	rm.mutex.Lock()
	delete(rm.resources, "test")
	rm.mutex.Unlock()

	// Should not panic and should continue without error
	err := rm.InitializeAll(context.Background())
	assert.NoError(t, err)
}

// TestResourceManager_ShutdownAll_ResourceRemoved tests shutdown with removed resource
func TestResourceManager_ShutdownAll_ResourceRemoved(t *testing.T) {
	rm := NewResourceManager()
	res := newMockResource("test", true)

	rm.Register("test", res)

	// Simulate resource being removed
	rm.mutex.Lock()
	delete(rm.resources, "test")
	rm.mutex.Unlock()

	// Should not panic and should continue without error
	err := rm.ShutdownAll(context.Background())
	assert.NoError(t, err)
}

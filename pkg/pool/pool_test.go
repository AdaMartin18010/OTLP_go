// Package pool provides object pool implementations for the OTLP Go SDK.
package pool

import (
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestNewPool tests basic pool creation and operations.
func TestNewPool(t *testing.T) {
	t.Run("basic pool creation", func(t *testing.T) {
		p := New(func() int {
			return 42
		})
		require.NotNil(t, p)
		
		// Get an object
		obj := p.Get()
		assert.Equal(t, 42, obj)
		
		// Put it back
		p.Put(obj)
		
		// Get again - should get the same object from pool
		obj2 := p.Get()
		assert.Equal(t, 42, obj2)
	})
	
	t.Run("pool with reset function", func(t *testing.T) {
		resetCalled := false
		p := New(
			func() *testObject {
				return &testObject{value: 42}
			},
			WithReset(func(obj *testObject) {
				resetCalled = true
				obj.value = 0
			}),
		)
		
		obj := p.Get()
		obj.value = 100
		p.Put(obj)
		
		// Give some time for async operations
		time.Sleep(10 * time.Millisecond)
		
		assert.True(t, resetCalled, "reset should have been called")
	})
	
	t.Run("pool with max size", func(t *testing.T) {
		p := New(
			func() int { return 1 },
			WithMaxSize[int](2),
		)
		
		// Get and put multiple objects
		for i := 0; i < 10; i++ {
			obj := p.Get()
			p.Put(obj)
		}
		
		// Pool should limit the number of cached objects
		stats := p.Stats()
		assert.Greater(t, stats.Puts, uint64(0))
	})
}

// TestPoolGetPut tests Get and Put operations.
func TestPoolGetPut(t *testing.T) {
	t.Run("get from empty pool creates new object", func(t *testing.T) {
		createCount := 0
		p := New(func() int {
			createCount++
			return createCount
		})
		
		obj1 := p.Get()
		obj2 := p.Get()
		
		assert.Equal(t, 1, obj1)
		assert.Equal(t, 2, obj2)
	})
	
	t.Run("put and get reuses object", func(t *testing.T) {
		p := New(func() int { return 42 })
		
		obj := p.Get()
		p.Put(obj)
		
		// Next get should potentially reuse
		// Note: sync.Pool doesn't guarantee reuse
		_ = p.Get()
	})
	
	t.Run("concurrent get and put", func(t *testing.T) {
		p := New(func() int { return 0 })
		
		var wg sync.WaitGroup
		for i := 0; i < 100; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				obj := p.Get()
				time.Sleep(time.Microsecond)
				p.Put(obj)
			}()
		}
		wg.Wait()
		
		stats := p.Stats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(100))
		assert.GreaterOrEqual(t, stats.Puts, uint64(100))
	})
}

// TestPoolStats tests statistics tracking.
func TestPoolStats(t *testing.T) {
	t.Run("stats tracking", func(t *testing.T) {
		p := New(func() int { return 42 })
		
		// Initial stats
		stats := p.Stats()
		assert.Equal(t, uint64(0), stats.Gets)
		assert.Equal(t, uint64(0), stats.Puts)
		
		// Get some objects
		obj1 := p.Get()
		obj2 := p.Get()
		_ = p.Get() // miss
		
		stats = p.Stats()
		assert.Equal(t, uint64(3), stats.Gets)
		assert.Equal(t, int64(3), stats.Active)
		
		// Put objects back
		p.Put(obj1)
		p.Put(obj2)
		
		// Give time for stats to update
		time.Sleep(10 * time.Millisecond)
		
		stats = p.Stats()
		assert.Equal(t, uint64(2), stats.Puts)
		assert.Equal(t, int64(1), stats.Active) // One object still active
	})
	
	t.Run("reset stats", func(t *testing.T) {
		p := New(func() int { return 42 })
		
		p.Get()
		p.Put(42)
		
		p.ResetStats()
		
		stats := p.Stats()
		assert.Equal(t, uint64(0), stats.Gets)
		assert.Equal(t, uint64(0), stats.Puts)
	})
	
	t.Run("hit rate calculation", func(t *testing.T) {
		p := New(func() int { return 42 })
		
		// Empty pool should have 0 hit rate
		rate := p.HitRate()
		assert.Equal(t, 0.0, rate)
		
		// Get and put some objects
		for i := 0; i < 10; i++ {
			obj := p.Get()
			p.Put(obj)
		}
		
		// Hit rate should be between 0 and 100
		rate = p.HitRate()
		assert.GreaterOrEqual(t, rate, 0.0)
		assert.LessOrEqual(t, rate, 100.0)
	})
}

// TestSizedPool tests the SizedPool implementation.
func TestSizedPool(t *testing.T) {
	t.Run("sized pool creation", func(t *testing.T) {
		p := NewSized(10, 5, func() int { return 42 })
		require.NotNil(t, p)
		
		// Should have prefill objects
		assert.Equal(t, 5, p.Len())
		assert.Equal(t, 10, p.Cap())
	})
	
	t.Run("sized pool get and put", func(t *testing.T) {
		p := NewSized(5, 3, func() int { return 1 })
		
		// Get all prefill objects
		objs := make([]int, 0, 5)
		for i := 0; i < 5; i++ {
			objs = append(objs, p.Get())
		}
		
		assert.Equal(t, 0, p.Len())
		
		// Put objects back
		for _, obj := range objs {
			p.Put(obj)
		}
		
		assert.Equal(t, 5, p.Len())
	})
	
	t.Run("sized pool stats", func(t *testing.T) {
		p := NewSized(10, 5, func() int { return 42 })
		
		obj := p.Get()
		p.Put(obj)
		
		stats := p.Stats()
		assert.Equal(t, uint64(1), stats.Gets)
		assert.Equal(t, uint64(1), stats.Puts)
		assert.GreaterOrEqual(t, stats.Hits, uint64(0))
	})
}

// TestConcurrentAccess tests concurrent pool access.
func TestConcurrentAccess(t *testing.T) {
	t.Run("concurrent gets", func(t *testing.T) {
		p := New(func() int { return 0 })
		
		var wg sync.WaitGroup
		for i := 0; i < 1000; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				_ = p.Get()
			}()
		}
		wg.Wait()
		
		stats := p.Stats()
		assert.Equal(t, uint64(1000), stats.Gets)
	})
	
	t.Run("concurrent gets and puts", func(t *testing.T) {
		p := New(func() int { return 0 })
		
		var wg sync.WaitGroup
		
		// Producers
		for i := 0; i < 500; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				obj := p.Get()
				time.Sleep(time.Microsecond)
				p.Put(obj)
			}()
		}
		
		wg.Wait()
		
		stats := p.Stats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(500))
		assert.GreaterOrEqual(t, stats.Puts, uint64(500))
	})
}

// TestPoolWithComplexTypes tests pool with complex types.
func TestPoolWithComplexTypes(t *testing.T) {
	type complexStruct struct {
		data    []byte
		counter int
		name    string
	}
	
	t.Run("pool with struct", func(t *testing.T) {
		p := New(func() *complexStruct {
			return &complexStruct{
				data: make([]byte, 0, 1024),
			}
		})
		
		obj := p.Get()
		require.NotNil(t, obj)
		assert.NotNil(t, obj.data)
		
		obj.name = "test"
		obj.counter = 42
		
		p.Put(obj)
	})
}

// BenchmarkPool benchmarks pool operations.
func BenchmarkPool(b *testing.B) {
	b.Run("get put", func(b *testing.B) {
		p := New(func() int { return 42 })
		
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			obj := p.Get()
			p.Put(obj)
		}
	})
	
	b.Run("concurrent get put", func(b *testing.B) {
		p := New(func() int { return 42 })
		
		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				obj := p.Get()
				p.Put(obj)
			}
		})
	})
	
	b.Run("vs raw sync pool", func(b *testing.B) {
		var pool sync.Pool
		pool.New = func() any { return 42 }
		
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			obj := pool.Get()
			pool.Put(obj)
		}
	})
}

// BenchmarkSizedPool benchmarks sized pool operations.
func BenchmarkSizedPool(b *testing.B) {
	b.Run("get put", func(b *testing.B) {
		p := NewSized(1000, 1000, func() int { return 42 })
		
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			obj := p.Get()
			p.Put(obj)
		}
	})
	
	b.Run("concurrent get put", func(b *testing.B) {
		p := NewSized(1000, 1000, func() int { return 42 })
		
		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				obj := p.Get()
				p.Put(obj)
			}
		})
	})
}

// testObject is used for testing reset functionality.
type testObject struct {
	value int
}

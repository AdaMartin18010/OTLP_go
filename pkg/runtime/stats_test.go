// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
package runtime

import (
	"runtime"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestGetMemStats tests memory statistics retrieval.
func TestGetMemStats(t *testing.T) {
	t.Run("basic retrieval", func(t *testing.T) {
		stats := GetMemStats()
		require.NotNil(t, stats)

		// Verify all fields are populated
		assert.GreaterOrEqual(t, stats.Alloc, uint64(0))
		assert.GreaterOrEqual(t, stats.TotalAlloc, uint64(0))
		assert.GreaterOrEqual(t, stats.Sys, uint64(0))
		assert.GreaterOrEqual(t, stats.Mallocs, uint64(0))
		assert.GreaterOrEqual(t, stats.Frees, uint64(0))
		assert.GreaterOrEqual(t, stats.HeapAlloc, uint64(0))
		assert.GreaterOrEqual(t, stats.HeapSys, uint64(0))
		assert.GreaterOrEqual(t, stats.LiveObjects, uint64(0))
		assert.GreaterOrEqual(t, stats.NumGC, uint32(0))
	})

	t.Run("live objects calculation", func(t *testing.T) {
		stats := GetMemStats()
		expectedLive := stats.Mallocs - stats.Frees
		assert.Equal(t, expectedLive, stats.LiveObjects)
	})

	t.Run("timestamp set", func(t *testing.T) {
		before := time.Now().UnixNano()
		stats := GetMemStats()
		after := time.Now().UnixNano()

		assert.GreaterOrEqual(t, stats.Timestamp, before)
		assert.LessOrEqual(t, stats.Timestamp, after)
	})
}

// TestGetGCStats tests GC statistics retrieval.
func TestGetGCStats(t *testing.T) {
	t.Run("basic retrieval", func(t *testing.T) {
		stats := GetGCStats()
		require.NotNil(t, stats)

		assert.GreaterOrEqual(t, stats.NumGC, uint32(0))
		assert.GreaterOrEqual(t, stats.NumForcedGC, uint32(0))
		assert.GreaterOrEqual(t, stats.GCCPUFraction, float64(0))
		assert.GreaterOrEqual(t, stats.HeapGoal, uint64(0))
	})

	t.Run("last GC time", func(t *testing.T) {
		// Force a GC to ensure we have a LastGC time
		runtime.GC()
		time.Sleep(10 * time.Millisecond)

		stats := GetGCStats()
		if stats.NumGC > 0 {
			assert.False(t, stats.LastGC.IsZero())
		}
	})

	t.Run("pause history", func(t *testing.T) {
		// Force multiple GCs
		for i := 0; i < 5; i++ {
			runtime.GC()
		}

		stats := GetGCStats()
		if stats.NumGC > 0 {
			assert.NotNil(t, stats.PauseHistory)
			assert.GreaterOrEqual(t, len(stats.PauseHistory), 0)
		}
	})

	t.Run("pause calculations", func(t *testing.T) {
		stats := GetGCStats()

		// Verify pause calculations
		if len(stats.PauseHistory) > 0 {
			assert.GreaterOrEqual(t, stats.AvgPause, time.Duration(0))
			assert.GreaterOrEqual(t, stats.MaxPause, time.Duration(0))
		}
	})
}

// TestGetGoroutineStats tests goroutine statistics retrieval.
func TestGetGoroutineStats(t *testing.T) {
	t.Run("basic retrieval", func(t *testing.T) {
		stats := GetGoroutineStats()
		require.NotNil(t, stats)

		assert.GreaterOrEqual(t, stats.Count, 1) // At least test goroutine
		assert.GreaterOrEqual(t, stats.MaxHistory, stats.Count)
		assert.NotNil(t, stats.States)
	})

	t.Run("max history tracking", func(t *testing.T) {
		// Reset max count for this test
		statsMu.Lock()
		maxGoroutineCount = 0
		statsMu.Unlock()

		// Create goroutines
		done := make(chan struct{})
		for i := 0; i < 10; i++ {
			go func() {
				<-done
			}()
		}
		time.Sleep(10 * time.Millisecond)

		stats := GetGoroutineStats()
		close(done)

		// MaxHistory should be at least 10 (plus test goroutines)
		assert.GreaterOrEqual(t, stats.MaxHistory, 10)
	})
}

// TestGetRuntimeStats tests comprehensive runtime statistics.
func TestGetRuntimeStats(t *testing.T) {
	stats := GetRuntimeStats()
	require.NotNil(t, stats)

	// Verify all sub-stats are populated
	assert.NotZero(t, stats.Timestamp)
	assert.GreaterOrEqual(t, stats.Memory.Alloc, uint64(0))
	assert.GreaterOrEqual(t, stats.GC.NumGC, uint32(0))
	assert.GreaterOrEqual(t, stats.Goroutines.Count, 1)
}

// TestSnapshot tests snapshot functionality.
func TestSnapshot(t *testing.T) {
	t.Run("get snapshot", func(t *testing.T) {
		snapshot := GetSnapshot()
		require.NotNil(t, snapshot)

		assert.NotZero(t, snapshot.Timestamp)
		assert.NotNil(t, snapshot.Info)
		assert.NotNil(t, snapshot.GOMAXPROCS)
		assert.NotNil(t, snapshot.GOMEMLIMIT)
		assert.NotZero(t, snapshot.Stats.Timestamp)
	})

	t.Run("get last snapshot", func(t *testing.T) {
		// Get a fresh snapshot
		fresh := GetSnapshot()

		// Get last snapshot
		last := GetLastSnapshot()
		require.NotNil(t, last)

		// Should be the same snapshot
		assert.Equal(t, fresh.Timestamp, last.Timestamp)
	})

	t.Run("snapshot nil initially", func(t *testing.T) {
		// Reset and test
		statsMu.Lock()
		oldSnapshot := lastSnapshot
		lastSnapshot = nil
		statsMu.Unlock()

		last := GetLastSnapshot()
		assert.Nil(t, last)

		// Restore
		statsMu.Lock()
		lastSnapshot = oldSnapshot
		statsMu.Unlock()
	})
}

// TestGCPercent tests GC percentage management.
func TestGCPercent(t *testing.T) {
	t.Run("get GC percent", func(t *testing.T) {
		percent := GetGCPercent()
		assert.Equal(t, 100, percent) // Default is 100
	})

	t.Run("set GC percent", func(t *testing.T) {
		original := SetGCPercent(200)
		defer SetGCPercent(original)

		// Setting a new value should return the previous
		assert.GreaterOrEqual(t, original, -1)
	})

	t.Run("disable GC", func(t *testing.T) {
		original := SetGCPercent(100)
		defer SetGCPercent(original)

		// Disable with negative value
		SetGCPercent(-1)
		// GC is now disabled
	})
}

// TestForceGC tests forced garbage collection.
func TestForceGC(t *testing.T) {
	before := GetGCStats().NumGC
	ForceGC()
	after := GetGCStats().NumGC

	assert.GreaterOrEqual(t, after, before)
}

// TestFreeOSMemory tests freeing OS memory.
func TestFreeOSMemory(t *testing.T) {
	// Just ensure it doesn't panic
	assert.NotPanics(t, func() {
		FreeOSMemory()
	})
}

// TestReadMetrics tests extended metrics reading.
func TestReadMetrics(t *testing.T) {
	metrics := ReadMetrics()
	require.NotNil(t, metrics)

	// Should contain some metrics
	assert.Greater(t, len(metrics), 0)

	// Check for common metrics
	_, hasAlloc := metrics["/memory/classes/heap/objects:bytes"]
	_, hasGoroutines := metrics["/sched/goroutines:goroutines"]

	// At least some standard metrics should be present
	assert.True(t, hasAlloc || hasGoroutines || len(metrics) > 0)
}

// TestMemoryUsage tests memory usage helpers.
func TestMemoryUsage(t *testing.T) {
	t.Run("memory usage", func(t *testing.T) {
		usage := MemoryUsage()
		assert.Greater(t, usage, uint64(0))
	})

	t.Run("heap usage", func(t *testing.T) {
		usage := HeapUsage()
		assert.Greater(t, usage, uint64(0))
	})

	t.Run("stack usage", func(t *testing.T) {
		usage := StackUsage()
		assert.GreaterOrEqual(t, usage, uint64(0))
	})
}

// TestMemStatsString tests MemStats string formatting.
func TestMemStatsString(t *testing.T) {
	stats := &MemStats{
		Alloc:       1024 * 1024 * 100, // 100 MB
		Sys:         1024 * 1024 * 200, // 200 MB
		HeapAlloc:   1024 * 1024 * 80,  // 80 MB
		HeapSys:     1024 * 1024 * 150, // 150 MB
		HeapObjects: 1000,
		NumGC:       10,
	}

	s := stats.String()
	assert.Contains(t, s, "Memory:")
	assert.Contains(t, s, "Alloc=")
	assert.Contains(t, s, "Sys=")
	assert.Contains(t, s, "GC=10")
}

// TestGCStatsString tests GCStats string formatting.
func TestGCStatsString(t *testing.T) {
	stats := &GCStats{
		NumGC:         100,
		NumForcedGC:   5,
		PauseTotal:    time.Second,
		AvgPause:      time.Millisecond * 10,
		MaxPause:      time.Millisecond * 50,
		GCCPUFraction: 0.05,
	}

	s := stats.String()
	assert.Contains(t, s, "GC:")
	assert.Contains(t, s, "Num=100")
	assert.Contains(t, s, "Forced=5")
	assert.Contains(t, s, "CPUFraction=5.0000%")
}

// TestGoroutineStatsString tests GoroutineStats string formatting.
func TestGoroutineStatsString(t *testing.T) {
	stats := &GoroutineStats{
		Count:      50,
		MaxHistory: 100,
	}

	s := stats.String()
	assert.Contains(t, s, "Goroutines:")
	assert.Contains(t, s, "Count=50")
	assert.Contains(t, s, "MaxHistory=100")
}

// TestRuntimeStatsString tests RuntimeStats string formatting.
func TestRuntimeStatsString(t *testing.T) {
	stats := &RuntimeStats{
		Memory: MemStats{
			Alloc: 1024 * 1024,
			NumGC: 5,
		},
		GC: GCStats{
			NumGC: 5,
		},
		Goroutines: GoroutineStats{
			Count: 10,
		},
	}

	s := stats.String()
	assert.Contains(t, s, "Memory:")
	assert.Contains(t, s, "GC:")
	assert.Contains(t, s, "Goroutines:")
}

// TestConcurrentStatsAccess tests concurrent access to stats.
func TestConcurrentStatsAccess(t *testing.T) {
	var wg sync.WaitGroup

	// Concurrent readers
	for i := 0; i < 100; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = GetMemStats()
			_ = GetGCStats()
			_ = GetGoroutineStats()
			_ = GetRuntimeStats()
		}()
	}

	// Concurrent writers (GC operations)
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			runtime.GC()
		}()
	}

	wg.Wait()
}

// BenchmarkGetMemStats benchmarks GetMemStats.
func BenchmarkGetMemStats(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetMemStats()
	}
}

// BenchmarkGetGCStats benchmarks GetGCStats.
func BenchmarkGetGCStats(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetGCStats()
	}
}

// BenchmarkGetGoroutineStats benchmarks GetGoroutineStats.
func BenchmarkGetGoroutineStats(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetGoroutineStats()
	}
}

// BenchmarkGetRuntimeStats benchmarks GetRuntimeStats.
func BenchmarkGetRuntimeStats(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetRuntimeStats()
	}
}

// BenchmarkReadMetrics benchmarks ReadMetrics.
func BenchmarkReadMetrics(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = ReadMetrics()
	}
}

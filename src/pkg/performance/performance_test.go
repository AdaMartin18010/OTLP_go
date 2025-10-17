package performance

import (
	"runtime"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestNewPerformanceMonitor 测试创建性能监控器
func TestNewPerformanceMonitor(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)

	assert.NotNil(t, monitor)
	assert.NotNil(t, monitor.metrics)
	assert.NotNil(t, monitor.stopCh)
	assert.Equal(t, time.Second, monitor.interval)

	// Cleanup
	monitor.Stop()
}

// TestUpdateMetric 测试更新指标
func TestUpdateMetric(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	// Update a metric
	monitor.UpdateMetric("test_metric", 42.5)

	// Get the metric
	metric, ok := monitor.GetMetric("test_metric")
	require.True(t, ok)
	require.NotNil(t, metric)
	assert.Equal(t, "test_metric", metric.Name)
	assert.Equal(t, 42.5, metric.Value)
	assert.Equal(t, int64(1), metric.Count)
	assert.Equal(t, 42.5, metric.Min)
	assert.Equal(t, 42.5, metric.Max)
	assert.Equal(t, 42.5, metric.Sum)
}

// TestUpdateMultipleMetrics 测试更新多个指标
func TestUpdateMultipleMetrics(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	// Update multiple values
	monitor.UpdateMetric("test", 10.0)
	monitor.UpdateMetric("test", 20.0)
	monitor.UpdateMetric("test", 30.0)

	metric, ok := monitor.GetMetric("test")
	require.True(t, ok)
	require.NotNil(t, metric)
	assert.Equal(t, int64(3), metric.Count)
	assert.Equal(t, 60.0, metric.Sum)
	assert.Equal(t, 10.0, metric.Min)
	assert.Equal(t, 30.0, metric.Max)
}

// TestGetMetricNotFound 测试获取不存在的指标
func TestGetMetricNotFound(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	metric, ok := monitor.GetMetric("nonexistent")
	assert.False(t, ok)
	assert.Nil(t, metric)
}

// TestGetAllMetrics 测试获取所有指标
func TestGetAllMetrics(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	// Update multiple different metrics
	monitor.UpdateMetric("metric1", 10.0)
	monitor.UpdateMetric("metric2", 20.0)
	monitor.UpdateMetric("metric3", 30.0)

	metrics := monitor.GetAllMetrics()
	assert.Len(t, metrics, 3)
	assert.Contains(t, metrics, "metric1")
	assert.Contains(t, metrics, "metric2")
	assert.Contains(t, metrics, "metric3")
}

// TestGetStats 测试获取性能统计
func TestGetStats(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	// Update some metrics
	monitor.UpdateMetric("test1", 42.0)
	monitor.UpdateMetric("test2", 84.0)

	stats := monitor.GetStats()
	require.NotNil(t, stats)
	assert.NotNil(t, stats.MemoryStats)
	assert.NotNil(t, stats.RuntimeStats)
	assert.NotNil(t, stats.CustomMetrics)
	assert.Len(t, stats.CustomMetrics, 2)
	assert.Greater(t, stats.Uptime, time.Duration(0))
}

// TestMemoryStats 测试内存统计
func TestMemoryStats(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	stats := monitor.GetStats()
	mem := stats.MemoryStats

	require.NotNil(t, mem)
	assert.Greater(t, mem.Alloc, uint64(0))
	assert.Greater(t, mem.TotalAlloc, uint64(0))
	assert.Greater(t, mem.Sys, uint64(0))
}

// TestRuntimeStats 测试运行时统计
func TestRuntimeStats(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	stats := monitor.GetStats()
	rt := stats.RuntimeStats

	require.NotNil(t, rt)
	assert.Greater(t, rt.NumGoroutine, 0)
	assert.GreaterOrEqual(t, rt.NumCPU, 1)
	assert.Greater(t, rt.NumCgoCall, int64(0))
}

// TestMetricAverage 测试指标平均值
func TestMetricAverage(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	// Update multiple values
	monitor.UpdateMetric("avg_test", 10.0)
	monitor.UpdateMetric("avg_test", 20.0)
	monitor.UpdateMetric("avg_test", 30.0)
	monitor.UpdateMetric("avg_test", 40.0)

	metric, ok := monitor.GetMetric("avg_test")
	require.True(t, ok)
	require.NotNil(t, metric)

	avg := metric.GetAverage()
	assert.Equal(t, 25.0, avg) // (10+20+30+40)/4 = 25
}

// TestMetricGetAverage 测试获取平均值
func TestMetricGetAverage(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	monitor.UpdateMetric("test", 100.0)

	metric, ok := monitor.GetMetric("test")
	require.True(t, ok)

	avg := metric.GetAverage()
	assert.Equal(t, 100.0, avg)
}

// TestMonitorStop 测试停止监控
func TestMonitorStop(t *testing.T) {
	monitor := NewPerformanceMonitor(100 * time.Millisecond)

	// Update some metrics
	monitor.UpdateMetric("test", 42.0)

	// Stop monitor
	monitor.Stop()
}

// TestConcurrentUpdating 测试并发更新
func TestConcurrentUpdating(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	const goroutines = 100
	const updatesPerGoroutine = 10

	done := make(chan bool)

	for i := 0; i < goroutines; i++ {
		go func(id int) {
			for j := 0; j < updatesPerGoroutine; j++ {
				monitor.UpdateMetric("concurrent_test", float64(id*10+j))
			}
			done <- true
		}(i)
	}

	// Wait for all goroutines
	for i := 0; i < goroutines; i++ {
		<-done
	}

	metric, ok := monitor.GetMetric("concurrent_test")
	require.True(t, ok)
	require.NotNil(t, metric)
	assert.Equal(t, int64(goroutines*updatesPerGoroutine), metric.Count)
}

// TestConcurrentMetricsAccess 测试并发访问指标
func TestConcurrentMetricsAccess(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	// Prepare some metrics
	for i := 0; i < 10; i++ {
		monitor.UpdateMetric("metric", float64(i))
	}

	done := make(chan bool)

	// Concurrent readers
	for i := 0; i < 50; i++ {
		go func() {
			_, _ = monitor.GetMetric("metric")
			_ = monitor.GetAllMetrics()
			_ = monitor.GetStats()
			done <- true
		}()
	}

	// Concurrent writers
	for i := 0; i < 50; i++ {
		go func(val float64) {
			monitor.UpdateMetric("metric", val)
			done <- true
		}(float64(i))
	}

	// Wait for all
	for i := 0; i < 100; i++ {
		<-done
	}
}

// BenchmarkUpdateMetric 基准测试更新指标
func BenchmarkUpdateMetric(b *testing.B) {
	monitor := NewPerformanceMonitor(time.Hour)
	defer monitor.Stop()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		monitor.UpdateMetric("bench_metric", float64(i))
	}
}

// BenchmarkGetMetric 基准测试获取指标
func BenchmarkGetMetric(b *testing.B) {
	monitor := NewPerformanceMonitor(time.Hour)
	defer monitor.Stop()

	monitor.UpdateMetric("bench_metric", 42.0)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, _ = monitor.GetMetric("bench_metric")
	}
}

// BenchmarkGetStats 基准测试获取统计
func BenchmarkGetStats(b *testing.B) {
	monitor := NewPerformanceMonitor(time.Hour)
	defer monitor.Stop()

	// Prepare some metrics
	for i := 0; i < 10; i++ {
		monitor.UpdateMetric("metric", float64(i))
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = monitor.GetStats()
	}
}

// BenchmarkConcurrentUpdate 基准测试并发更新
func BenchmarkConcurrentUpdate(b *testing.B) {
	monitor := NewPerformanceMonitor(time.Hour)
	defer monitor.Stop()

	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		i := 0
		for pb.Next() {
			monitor.UpdateMetric("bench_metric", float64(i))
			i++
		}
	})
}

// BenchmarkMemoryAllocation 基准测试内存分配
func BenchmarkMemoryAllocation(b *testing.B) {
	b.ReportAllocs()

	monitor := NewPerformanceMonitor(time.Hour)
	defer monitor.Stop()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		monitor.UpdateMetric("test", float64(i))
	}
}

// TestRealMemoryUsage 测试真实内存使用
func TestRealMemoryUsage(t *testing.T) {
	var m1, m2 runtime.MemStats

	runtime.GC()
	runtime.ReadMemStats(&m1)

	monitor := NewPerformanceMonitor(time.Second)

	// Update many metrics
	for i := 0; i < 1000; i++ {
		monitor.UpdateMetric("test", float64(i))
	}

	runtime.GC()
	runtime.ReadMemStats(&m2)

	monitor.Stop()

	// Memory should have increased
	assert.Greater(t, m2.TotalAlloc, m1.TotalAlloc)
}

// TestStartMonitor 测试启动监控
func TestStartMonitor(t *testing.T) {
	monitor := NewPerformanceMonitor(100 * time.Millisecond)

	// Start monitoring
	monitor.Start()

	// Wait for some collection cycles
	time.Sleep(250 * time.Millisecond)

	// Should have collected some runtime metrics
	_, ok := monitor.GetMetric("memory.alloc")
	assert.True(t, ok, "should have collected memory metrics")

	monitor.Stop()
}

// TestCollectStats 测试自动收集统计
func TestCollectStats(t *testing.T) {
	monitor := NewPerformanceMonitor(50 * time.Millisecond)
	monitor.Start()
	defer monitor.Stop()

	// Wait for collection
	time.Sleep(150 * time.Millisecond)

	// Check that runtime metrics were collected
	_, hasMemory := monitor.GetMetric("memory.alloc")
	_, hasGoroutines := monitor.GetMetric("runtime.goroutines")

	assert.True(t, hasMemory, "should collect memory metrics")
	assert.True(t, hasGoroutines, "should collect goroutine metrics")
}

// TestMetricString 测试指标字符串表示
func TestMetricString(t *testing.T) {
	monitor := NewPerformanceMonitor(time.Second)
	defer monitor.Stop()

	monitor.UpdateMetric("test_metric", 10.0)
	monitor.UpdateMetric("test_metric", 20.0)
	monitor.UpdateMetric("test_metric", 30.0)

	metric, ok := monitor.GetMetric("test_metric")
	require.True(t, ok)

	str := metric.String()
	assert.Contains(t, str, "test_metric")
	assert.Contains(t, str, "Value:")
	assert.Contains(t, str, "Count:")
	assert.Contains(t, str, "Avg:")
}

// TestNewStringPool 测试字符串池创建
func TestNewStringPool(t *testing.T) {
	pool := NewStringPool()
	assert.NotNil(t, pool)
}

// TestStringPoolGetPut 测试字符串池获取和归还
func TestStringPoolGetPut(t *testing.T) {
	pool := NewStringPool()

	// Get a StringBuilder
	sb := pool.Get()
	assert.NotNil(t, sb)

	// Use it
	sb.WriteString("test")
	assert.Equal(t, "test", sb.String())
	assert.Equal(t, 4, sb.Len())

	// Put it back
	pool.Put(sb)

	// Get another one (might be the same recycled one)
	sb2 := pool.Get()
	assert.NotNil(t, sb2)
	// Should be reset
	assert.Equal(t, 0, sb2.Len())
}

// TestStringBuilder 测试字符串构建器
func TestStringBuilder(t *testing.T) {
	sb := &StringBuilder{}

	// Write operations
	n, err := sb.WriteString("Hello")
	assert.NoError(t, err)
	assert.Equal(t, 5, n)

	n, err = sb.WriteString(" World")
	assert.NoError(t, err)
	assert.Equal(t, 6, n)

	// Check result
	assert.Equal(t, "Hello World", sb.String())
	assert.Equal(t, 11, sb.Len())
	assert.GreaterOrEqual(t, sb.Cap(), 11)

	// Reset
	sb.Reset()
	assert.Equal(t, 0, sb.Len())
	assert.Equal(t, "", sb.String())
}

// TestStringBuilderWrite 测试字符串构建器Write方法
func TestStringBuilderWrite(t *testing.T) {
	sb := &StringBuilder{}

	n, err := sb.Write([]byte("test"))
	assert.NoError(t, err)
	assert.Equal(t, 4, n)
	assert.Equal(t, "test", sb.String())
}

// TestStringBuilderWriteByte 测试字符串构建器WriteByte方法
func TestStringBuilderWriteByte(t *testing.T) {
	sb := &StringBuilder{}

	err := sb.WriteByte('a')
	assert.NoError(t, err)
	err = sb.WriteByte('b')
	assert.NoError(t, err)
	err = sb.WriteByte('c')
	assert.NoError(t, err)

	assert.Equal(t, "abc", sb.String())
}

// TestStringBuilderGrow 测试字符串构建器Grow方法
func TestStringBuilderGrow(t *testing.T) {
	sb := &StringBuilder{}

	originalCap := sb.Cap()
	sb.Grow(100)
	newCap := sb.Cap()

	assert.GreaterOrEqual(t, newCap, originalCap+100)
}

// TestNewObjectPool 测试对象池创建
func TestNewObjectPool(t *testing.T) {
	pool := NewObjectPool(func() interface{} {
		return &struct{ Value int }{}
	})

	assert.NotNil(t, pool)
}

// TestObjectPoolGetPut 测试对象池获取和归还
func TestObjectPoolGetPut(t *testing.T) {
	pool := NewObjectPool(func() interface{} {
		return &struct{ Value int }{Value: 42}
	})

	// Get an object
	obj := pool.Get()
	assert.NotNil(t, obj)

	// Type assertion
	typed, ok := obj.(*struct{ Value int })
	assert.True(t, ok)
	assert.Equal(t, 42, typed.Value)

	// Modify and put back
	typed.Value = 100
	pool.Put(obj)

	// Get another (might be recycled)
	obj2 := pool.Get()
	assert.NotNil(t, obj2)
}

// BenchmarkStringPool 基准测试字符串池
func BenchmarkStringPool(b *testing.B) {
	pool := NewStringPool()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		sb := pool.Get()
		sb.WriteString("test")
		_ = sb.String()
		pool.Put(sb)
	}
}

// BenchmarkObjectPool 基准测试对象池
func BenchmarkObjectPool(b *testing.B) {
	pool := NewObjectPool(func() interface{} {
		return &struct{ Value int }{}
	})

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		obj := pool.Get()
		pool.Put(obj)
	}
}

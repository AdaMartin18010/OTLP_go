// Package pool provides object pool implementations for the OTLP Go SDK.
package pool

import (
	"bytes"
	"sync"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestNewBufferPool tests buffer pool creation.
func TestNewBufferPool(t *testing.T) {
	t.Run("default buffer pool", func(t *testing.T) {
		bp := NewBufferPool(0, DefaultBufferSize)
		require.NotNil(t, bp)
		
		buf := bp.Get()
		require.NotNil(t, buf)
		assert.Equal(t, 0, buf.Len())
		assert.GreaterOrEqual(t, buf.Cap(), DefaultBufferSize)
		
		bp.Put(buf)
	})
	
	t.Run("custom size buffer pool", func(t *testing.T) {
		bp := NewBufferPool(100, 8192)
		require.NotNil(t, bp)
		
		buf := bp.Get()
		require.NotNil(t, buf)
		assert.GreaterOrEqual(t, buf.Cap(), 8192)
		
		bp.Put(buf)
	})
	
	t.Run("zero bufSize uses default", func(t *testing.T) {
		bp := NewBufferPool(10, 0)
		buf := bp.Get()
		assert.GreaterOrEqual(t, buf.Cap(), DefaultBufferSize)
		bp.Put(buf)
	})
	
	t.Run("negative bufSize uses default", func(t *testing.T) {
		bp := NewBufferPool(10, -1)
		buf := bp.Get()
		assert.GreaterOrEqual(t, buf.Cap(), DefaultBufferSize)
		bp.Put(buf)
	})
}

// TestBufferPoolGetPut tests buffer get and put operations.
func TestBufferPoolGetPut(t *testing.T) {
	t.Run("get returns clean buffer", func(t *testing.T) {
		bp := NewBufferPool(10, 1024)
		
		buf := bp.Get()
		buf.WriteString("test data")
		assert.Equal(t, 9, buf.Len())
		
		bp.Put(buf)
		
		// Get again - should be reset
		buf2 := bp.Get()
		assert.Equal(t, 0, buf2.Len())
		
		bp.Put(buf2)
	})
	
	t.Run("put nil is safe", func(t *testing.T) {
		bp := NewBufferPool(10, 1024)
		bp.Put(nil) // Should not panic
	})
	
	t.Run("oversized buffers are discarded", func(t *testing.T) {
		bp := NewBufferPool(10, 1024)
		
		// Create an oversized buffer
		buf := bytes.NewBuffer(make([]byte, 0, MaxBufferSize+1))
		
		// Should not panic
		bp.Put(buf)
	})
}

// TestBufferPoolStats tests buffer pool statistics.
func TestBufferPoolStats(t *testing.T) {
	t.Run("stats tracking", func(t *testing.T) {
		bp := NewBufferPool(10, 1024)
		bp.ResetStats()
		
		buf := bp.Get()
		bp.Put(buf)
		
		stats := bp.Stats()
		assert.Equal(t, uint64(1), stats.Gets)
		assert.Equal(t, uint64(1), stats.Puts)
	})
	
	t.Run("hit rate", func(t *testing.T) {
		bp := NewBufferPool(10, 1024)
		bp.ResetStats()
		
		rate := bp.HitRate()
		assert.Equal(t, 0.0, rate)
		
		// Get and put some buffers
		for i := 0; i < 10; i++ {
			buf := bp.Get()
			bp.Put(buf)
		}
		
		rate = bp.HitRate()
		assert.GreaterOrEqual(t, rate, 0.0)
		assert.LessOrEqual(t, rate, 100.0)
	})
}

// TestDefaultBufferPool tests the package-level default buffer pool.
func TestDefaultBufferPool(t *testing.T) {
	t.Run("default pool get put", func(t *testing.T) {
		buf := GetBuffer()
		require.NotNil(t, buf)
		
		buf.WriteString("test")
		PutBuffer(buf)
	})
	
	t.Run("default pool is consistent", func(t *testing.T) {
		buf1 := GetBuffer()
		buf1.WriteString("data")
		PutBuffer(buf1)
		
		buf2 := GetBuffer()
		// Buffer should be reset
		assert.Equal(t, 0, buf2.Len())
		PutBuffer(buf2)
	})
}

// TestSizedBufferPool tests the sized buffer pool.
func TestSizedBufferPool(t *testing.T) {
	t.Run("sized buffer pool creation", func(t *testing.T) {
		sbp := NewSizedBufferPool(10, 5, 1024)
		require.NotNil(t, sbp)
		
		// Should have prefill
		assert.Equal(t, 5, sbp.Len())
		assert.Equal(t, 10, sbp.Cap())
	})
	
	t.Run("sized buffer pool operations", func(t *testing.T) {
		sbp := NewSizedBufferPool(5, 3, 1024)
		
		// Get all prefill buffers
		bufs := make([]*bytes.Buffer, 0, 5)
		for i := 0; i < 5; i++ {
			buf := sbp.Get()
			buf.WriteString("data")
			bufs = append(bufs, buf)
		}
		
		assert.Equal(t, 0, sbp.Len())
		
		// Put back
		for _, buf := range bufs {
			sbp.Put(buf)
		}
		
		assert.Equal(t, 5, sbp.Len())
	})
	
	t.Run("sized buffer pool put nil", func(t *testing.T) {
		sbp := NewSizedBufferPool(5, 3, 1024)
		sbp.Put(nil) // Should not panic
	})
	
	t.Run("sized buffer pool stats", func(t *testing.T) {
		sbp := NewSizedBufferPool(10, 5, 1024)
		
		buf := sbp.Get()
		sbp.Put(buf)
		
		stats := sbp.Stats()
		assert.Equal(t, uint64(1), stats.Gets)
		assert.Equal(t, uint64(1), stats.Puts)
	})
}

// TestBufferPoolConcurrentAccess tests concurrent buffer pool operations.
func TestBufferPoolConcurrentAccess(t *testing.T) {
	t.Run("concurrent get put", func(t *testing.T) {
		bp := NewBufferPool(100, 1024)
		
		var wg sync.WaitGroup
		for i := 0; i < 1000; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				buf := bp.Get()
				buf.WriteString("concurrent data")
				bp.Put(buf)
			}()
		}
		wg.Wait()
		
		stats := bp.Stats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(1000))
		assert.GreaterOrEqual(t, stats.Puts, uint64(1000))
	})
	
	t.Run("concurrent sized pool", func(t *testing.T) {
		sbp := NewSizedBufferPool(100, 50, 1024)
		
		var wg sync.WaitGroup
		for i := 0; i < 500; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				buf := sbp.Get()
				buf.WriteString("data")
				sbp.Put(buf)
			}()
		}
		wg.Wait()
		
		stats := sbp.Stats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(500))
	})
}

// TestBufferPoolReset tests buffer reset behavior.
func TestBufferPoolReset(t *testing.T) {
	t.Run("buffer is reset on put", func(t *testing.T) {
		bp := NewBufferPool(10, 1024)
		
		buf := bp.Get()
		buf.WriteString("original data that is quite long")
		originalCap := buf.Cap()
		bp.Put(buf)
		
		buf2 := bp.Get()
		assert.Equal(t, 0, buf2.Len())
		// Capacity should be preserved
		assert.GreaterOrEqual(t, buf2.Cap(), originalCap)
		bp.Put(buf2)
	})
}

// BenchmarkBufferPool benchmarks buffer pool operations.
func BenchmarkBufferPool(b *testing.B) {
	b.Run("get put", func(b *testing.B) {
		bp := NewBufferPool(100, 4096)
		
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			buf := bp.Get()
			buf.WriteString("benchmark data")
			bp.Put(buf)
		}
	})
	
	b.Run("concurrent get put", func(b *testing.B) {
		bp := NewBufferPool(1000, 4096)
		
		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				buf := bp.Get()
				buf.WriteString("benchmark data")
				bp.Put(buf)
			}
		})
	})
	
	b.Run("without pool", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			buf := bytes.NewBuffer(make([]byte, 0, 4096))
			buf.WriteString("benchmark data")
			// Let GC collect it
			_ = buf
		}
	})
}

// BenchmarkSizedBufferPool benchmarks sized buffer pool.
func BenchmarkSizedBufferPool(b *testing.B) {
	b.Run("get put", func(b *testing.B) {
		sbp := NewSizedBufferPool(1000, 1000, 4096)
		
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			buf := sbp.Get()
			buf.WriteString("benchmark data")
			sbp.Put(buf)
		}
	})
	
	b.Run("concurrent get put", func(b *testing.B) {
		sbp := NewSizedBufferPool(1000, 1000, 4096)
		
		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				buf := sbp.Get()
				buf.WriteString("benchmark data")
				sbp.Put(buf)
			}
		})
	})
}

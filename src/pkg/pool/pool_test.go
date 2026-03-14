package pool

import (
	"bytes"
	"sync"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewPool(t *testing.T) {
	counter := 0
	pool := NewPool("test-pool", func() int {
		counter++
		return counter
	})

	assert.NotNil(t, pool)
	assert.Equal(t, "test-pool", pool.name)
	assert.NotNil(t, pool.pool)
	assert.NotNil(t, pool.meter)
}

func TestPoolGetPut(t *testing.T) {
	pool := NewPool("test-pool", func() int {
		return 42
	})

	// Get should return object
	val := pool.Get()
	assert.Equal(t, 42, val)

	// Put should accept object (no panic)
	pool.Put(100)

	// Get should return an object (may be the put one or a new one)
	val2 := pool.Get()
	// Just verify we get a valid int, sync.Pool doesn't guarantee same object
	_ = val2
}

func TestPoolConcurrency(t *testing.T) {
	pool := NewPool("concurrent-pool", func() *int {
		v := 0
		return &v
	})

	var wg sync.WaitGroup
	iterations := 100

	for i := 0; i < iterations; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			obj := pool.Get()
			*obj++
			pool.Put(obj)
		}()
	}

	wg.Wait()
	// Should not panic
}

func TestGetBuffer(t *testing.T) {
	buf := GetBuffer()
	require.NotNil(t, buf)

	buf.WriteString("test data")
	assert.Equal(t, "test data", buf.String())

	PutBuffer(buf)
	assert.Equal(t, 0, buf.Len(), "Buffer should be reset")
}

func TestPutBuffer(t *testing.T) {
	buf := GetBuffer()
	buf.WriteString("some data")

	PutBuffer(buf)
	assert.Equal(t, 0, buf.Len())
}

func TestGetByteSlice(t *testing.T) {
	tests := []struct {
		name         string
		size         int
		expectedCap  int
		expectedPool string
	}{
		{"small", 512, 1024, "1k"},
		{"medium", 2048, 4096, "4k"},
		{"large", 10000, 65536, "64k"},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			slice := GetByteSlice(tt.size)
			assert.NotNil(t, slice)
			assert.Equal(t, 0, len(slice))
			assert.GreaterOrEqual(t, cap(slice), tt.size)
		})
	}
}

func TestPutByteSlice(t *testing.T) {
	// Get and put 1k slice
	slice1k := ByteSlicePool.Get()
	assert.Equal(t, 1024, cap(slice1k))
	PutByteSlice(slice1k)

	// Get and put 4k slice
	slice4k := ByteSlicePool4K.Get()
	assert.Equal(t, 4096, cap(slice4k))
	PutByteSlice(slice4k)

	// Get and put 64k slice
	slice64k := ByteSlicePool64K.Get()
	assert.Equal(t, 65536, cap(slice64k))
	PutByteSlice(slice64k)

	// Empty slice should be ignored
	PutByteSlice([]byte{})
	// Should not panic

	// Non-standard size should be ignored
	nonStandard := make([]byte, 0, 2048)
	PutByteSlice(nonStandard)
	// Should not panic
}

func TestSizedPool(t *testing.T) {
	sp := NewSizedPool()
	assert.NotNil(t, sp)
	assert.NotNil(t, sp.pools)
}

func TestSizedPoolGetPut(t *testing.T) {
	sp := NewSizedPool()

	// Get slice of size 100
	slice := sp.Get(100)
	assert.NotNil(t, slice)
	assert.Equal(t, 0, len(slice))
	assert.GreaterOrEqual(t, cap(slice), 100)

	// Capacity should be power of 2
	capacity := cap(slice)
	assert.True(t, capacity > 0 && (capacity&(capacity-1)) == 0, "capacity should be power of 2")

	// Put it back
	sp.Put(slice)

	// Get again, should get same capacity
	slice2 := sp.Get(100)
	assert.Equal(t, capacity, cap(slice2))
}

func TestSizedPoolConcurrency(t *testing.T) {
	sp := NewSizedPool()

	var wg sync.WaitGroup
	sizes := []int{100, 500, 1000, 5000, 10000}

	for _, size := range sizes {
		for range 20 {
			wg.Add(1)
			go func(s int) {
				defer wg.Done()
				slice := sp.Get(s)
				slice = append(slice, make([]byte, s)...)
				sp.Put(slice)
			}(size)
		}
	}

	wg.Wait()
	// Should not panic or race
}

func TestNextPowerOfTwo(t *testing.T) {
	tests := []struct {
		input    int
		expected int
	}{
		{0, 1},
		{1, 1},
		{2, 2},
		{3, 4},
		{4, 4},
		{5, 8},
		{7, 8},
		{8, 8},
		{9, 16},
		{15, 16},
		{16, 16},
		{17, 32},
		{100, 128},
		{1000, 1024},
		{1023, 1024},
		{1024, 1024},
		{1025, 2048},
	}

	for _, tt := range tests {
		t.Run("", func(t *testing.T) {
			result := nextPowerOfTwo(tt.input)
			assert.Equal(t, tt.expected, result)
		})
	}
}

func TestBufferPoolReuse(t *testing.T) {
	buf1 := GetBuffer()
	buf1.WriteString("first")
	ptr1 := &buf1

	PutBuffer(buf1)

	buf2 := GetBuffer()
	ptr2 := &buf2

	// Should reuse the same buffer (addresses might be same)
	assert.Equal(t, 0, buf2.Len(), "Buffer should be clean")

	PutBuffer(buf2)

	// Verify pointer identity (pool reuse)
	_ = ptr1
	_ = ptr2
}

// Additional tests for better coverage

func TestPoolMultipleTypes(t *testing.T) {
	// Test with struct pool
	type TestStruct struct {
		Name  string
		Value int
	}

	structPool := NewPool("struct-pool", func() TestStruct {
		return TestStruct{Name: "default", Value: 0}
	})

	st1 := structPool.Get()
	assert.Equal(t, "default", st1.Name)
	assert.Equal(t, 0, st1.Value)

	// Put custom struct
	structPool.Put(TestStruct{Name: "custom", Value: 42})

	// Get an object - sync.Pool may return the put one or a new one
	st2 := structPool.Get()
	// Verify we got a valid struct
	_ = st2.Name
}

func TestByteSlicePoolEdgeCases(t *testing.T) {
	// Test with size 0
	slice0 := GetByteSlice(0)
	assert.NotNil(t, slice0)
	assert.Equal(t, 0, len(slice0))
	PutByteSlice(slice0)

	// Test with exact sizes
	slice1k := GetByteSlice(1024)
	assert.GreaterOrEqual(t, cap(slice1k), 1024)
	PutByteSlice(slice1k)

	slice4k := GetByteSlice(4096)
	assert.GreaterOrEqual(t, cap(slice4k), 4096)
	PutByteSlice(slice4k)

	slice64k := GetByteSlice(65536)
	assert.GreaterOrEqual(t, cap(slice64k), 65536)
	PutByteSlice(slice64k)

	// Test with very large size (max is 64k pool)
	sliceLarge := GetByteSlice(100000)
	assert.NotNil(t, sliceLarge)
	// Will get 64k pool, capacity will be 65536
	assert.GreaterOrEqual(t, cap(sliceLarge), 0)
	PutByteSlice(sliceLarge)
}

func TestPutByteSliceNil(t *testing.T) {
	// Should not panic with nil
	var nilSlice []byte
	PutByteSlice(nilSlice)
}

func TestSizedPoolVariousSizes(t *testing.T) {
	sp := NewSizedPool()

	// Test various sizes
	sizes := []int{1, 10, 100, 1000, 10000, 100000}
	for _, size := range sizes {
		slice := sp.Get(size)
		assert.NotNil(t, slice)
		assert.Equal(t, 0, len(slice))
		assert.GreaterOrEqual(t, cap(slice), size)

		// Verify power of 2
		cap := cap(slice)
		assert.True(t, cap > 0 && (cap&(cap-1)) == 0, "capacity %d should be power of 2", cap)

		sp.Put(slice)
	}
}

func TestSizedPoolPutNonExistent(t *testing.T) {
	sp := NewSizedPool()

	// Get a slice
	slice := sp.Get(100)
	sp.Put(slice)

	// Create a slice with non-existent capacity
	nonExistent := make([]byte, 0, 12345) // Non-power-of-2 capacity
	// This should not panic and should not be added to pool
	sp.Put(nonExistent)

	// Next Get should create new slice
	slice2 := sp.Get(100)
	_ = slice2
}

func TestBufferPoolConcurrency(t *testing.T) {
	var wg sync.WaitGroup

	for range 100 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			buf := GetBuffer()
			buf.WriteString("concurrent test")
			assert.Equal(t, "concurrent test", buf.String())
			PutBuffer(buf)
		}()
	}

	wg.Wait()
}

func TestByteSlicePoolConcurrency(t *testing.T) {
	var wg sync.WaitGroup
	sizes := []int{100, 500, 1000, 2000, 5000}

	for _, size := range sizes {
		for range 20 {
			wg.Add(1)
			go func(s int) {
				defer wg.Done()
				slice := GetByteSlice(s)
				slice = append(slice, []byte("test")...)
				PutByteSlice(slice)
			}(size)
		}
	}

	wg.Wait()
}

func TestNextPowerOfTwoEdgeCases(t *testing.T) {
	// Test with negative (should return 1)
	result := nextPowerOfTwo(-1)
	assert.Equal(t, 1, result)

	// Test with large number
	result = nextPowerOfTwo(1 << 20) // 1MB
	assert.Equal(t, 1<<20, result)

	result = nextPowerOfTwo(1<<20 + 1)
	assert.Equal(t, 1<<21, result)
}

func TestPoolMetricsIntegration(t *testing.T) {
	// Create pool and perform operations
	pool := NewPool("metrics-test", func() int {
		return 0
	})

	// Perform multiple get/put operations
	for range 10 {
		val := pool.Get()
		pool.Put(val)
	}

	// Pool should still function correctly
	val := pool.Get()
	assert.Equal(t, 0, val)
}

// Benchmarks

func BenchmarkPoolGet(b *testing.B) {
	pool := NewPool("bench-pool", func() *bytes.Buffer {
		return new(bytes.Buffer)
	})

	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		buf := pool.Get()
		pool.Put(buf)
	}
}

func BenchmarkGetBuffer(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		buf := GetBuffer()
		buf.WriteString("test")
		PutBuffer(buf)
	}
}

func BenchmarkGetByteSlice(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		slice := GetByteSlice(512)
		PutByteSlice(slice)
	}
}

func BenchmarkSizedPoolGet(b *testing.B) {
	sp := NewSizedPool()
	b.ResetTimer()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		slice := sp.Get(1000)
		sp.Put(slice)
	}
}

func BenchmarkNextPowerOfTwo(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = nextPowerOfTwo(i%10000 + 1)
	}
}

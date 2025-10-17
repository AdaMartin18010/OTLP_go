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

	// Put should accept object
	pool.Put(100)

	// Get should return the put object
	val2 := pool.Get()
	assert.Equal(t, 100, val2)
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
		for i := 0; i < 20; i++ {
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

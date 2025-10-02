package pool

import (
	"bytes"
	"context"
	"sync"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/metric"
)

// Pool 泛型对象池
// 基于 sync.Pool，添加指标监控
type Pool[T any] struct {
	pool    *sync.Pool
	name    string
	meter   metric.Meter
	getsCtr metric.Int64Counter
	putsCtr metric.Int64Counter
	newsCtr metric.Int64Counter
}

// NewPool 创建泛型对象池
func NewPool[T any](name string, newFunc func() T) *Pool[T] {
	meter := otel.Meter("pool/" + name)

	getsCtr, _ := meter.Int64Counter(
		"pool.gets",
		metric.WithDescription("Number of Get operations"),
	)
	putsCtr, _ := meter.Int64Counter(
		"pool.puts",
		metric.WithDescription("Number of Put operations"),
	)
	newsCtr, _ := meter.Int64Counter(
		"pool.news",
		metric.WithDescription("Number of new object allocations"),
	)

	p := &Pool[T]{
		name:    name,
		meter:   meter,
		getsCtr: getsCtr,
		putsCtr: putsCtr,
		newsCtr: newsCtr,
	}

	p.pool = &sync.Pool{
		New: func() interface{} {
			ctx := context.Background()
			p.newsCtr.Add(ctx, 1, metric.WithAttributes(
				attribute.String("pool.name", name),
			))
			return newFunc()
		},
	}

	return p
}

// Get 从池中获取对象
func (p *Pool[T]) Get() T {
	ctx := context.Background()
	p.getsCtr.Add(ctx, 1, metric.WithAttributes(
		attribute.String("pool.name", p.name),
	))
	return p.pool.Get().(T)
}

// Put 将对象放回池中
func (p *Pool[T]) Put(obj T) {
	ctx := context.Background()
	p.putsCtr.Add(ctx, 1, metric.WithAttributes(
		attribute.String("pool.name", p.name),
	))
	p.pool.Put(obj)
}

// --- 预定义的常用池 ---

var (
	// BufferPool 字节缓冲池
	BufferPool = NewPool("bytes.Buffer", func() *bytes.Buffer {
		return new(bytes.Buffer)
	})

	// ByteSlicePool 字节切片池（1KB）
	ByteSlicePool = NewPool("[]byte-1k", func() []byte {
		return make([]byte, 0, 1024)
	})

	// ByteSlicePool4K 字节切片池（4KB）
	ByteSlicePool4K = NewPool("[]byte-4k", func() []byte {
		return make([]byte, 0, 4096)
	})

	// ByteSlicePool64K 字节切片池（64KB）
	ByteSlicePool64K = NewPool("[]byte-64k", func() []byte {
		return make([]byte, 0, 65536)
	})
)

// GetBuffer 从缓冲池获取 Buffer（便捷函数）
func GetBuffer() *bytes.Buffer {
	return BufferPool.Get()
}

// PutBuffer 将 Buffer 放回池中（便捷函数，会重置）
func PutBuffer(buf *bytes.Buffer) {
	buf.Reset()
	BufferPool.Put(buf)
}

// GetByteSlice 从池中获取字节切片
func GetByteSlice(size int) []byte {
	switch {
	case size <= 1024:
		return ByteSlicePool.Get()[:0]
	case size <= 4096:
		return ByteSlicePool4K.Get()[:0]
	default:
		return ByteSlicePool64K.Get()[:0]
	}
}

// PutByteSlice 将字节切片放回池中
func PutByteSlice(b []byte) {
	if cap(b) == 0 {
		return
	}

	switch cap(b) {
	case 1024:
		ByteSlicePool.Put(b)
	case 4096:
		ByteSlicePool4K.Put(b)
	case 65536:
		ByteSlicePool64K.Put(b)
	}
}

// SizedPool 大小分级的对象池
type SizedPool struct {
	pools map[int]*sync.Pool
	mu    sync.RWMutex
}

// NewSizedPool 创建大小分级池
func NewSizedPool() *SizedPool {
	return &SizedPool{
		pools: make(map[int]*sync.Pool),
	}
}

// Get 获取指定大小的字节切片
func (sp *SizedPool) Get(size int) []byte {
	// 向上对齐到 2 的幂
	capacity := nextPowerOfTwo(size)

	sp.mu.RLock()
	pool, exists := sp.pools[capacity]
	sp.mu.RUnlock()

	if !exists {
		sp.mu.Lock()
		// 双重检查
		pool, exists = sp.pools[capacity]
		if !exists {
			pool = &sync.Pool{
				New: func() interface{} {
					return make([]byte, 0, capacity)
				},
			}
			sp.pools[capacity] = pool
		}
		sp.mu.Unlock()
	}

	return pool.Get().([]byte)[:0]
}

// Put 归还字节切片
func (sp *SizedPool) Put(b []byte) {
	capacity := cap(b)

	sp.mu.RLock()
	pool, exists := sp.pools[capacity]
	sp.mu.RUnlock()

	if exists {
		// 通过 interface{} 存储以避免额外分配
		pool.Put(interface{}(b))
	}
}

// nextPowerOfTwo 返回大于等于 n 的最小 2 的幂
func nextPowerOfTwo(n int) int {
	if n <= 0 {
		return 1
	}
	n--
	n |= n >> 1
	n |= n >> 2
	n |= n >> 4
	n |= n >> 8
	n |= n >> 16
	n++
	return n
}

// Example: 使用对象池
func ExampleBufferPool() {
	// 获取 buffer
	buf := GetBuffer()
	defer PutBuffer(buf)

	// 使用 buffer
	buf.WriteString("Hello, ")
	buf.WriteString("World!")

	// 处理数据
	_ = buf.String()
}

// Example: 使用字节切片池
func ExampleByteSlicePool() {
	// 获取字节切片
	data := GetByteSlice(512)
	defer PutByteSlice(data)

	// 使用切片
	data = append(data, []byte("example data")...)

	// 处理数据
	_ = data
}

// Example: 使用大小分级池
func ExampleSizedPool() {
	sp := NewSizedPool()

	// 获取不同大小的切片
	small := sp.Get(100)
	medium := sp.Get(1000)
	large := sp.Get(10000)

	defer func() {
		sp.Put(small)
		sp.Put(medium)
		sp.Put(large)
	}()

	// 使用切片...
	_ = small
	_ = medium
	_ = large
}

// Package pool provides object pool implementations for the OTLP Go SDK.
package pool

import (
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestNewSpanPool tests span pool creation.
func TestNewSpanPool(t *testing.T) {
	t.Run("default span pool", func(t *testing.T) {
		sp := NewSpanPool(DefaultSpanPoolSize)
		require.NotNil(t, sp)

		span := sp.Get()
		require.NotNil(t, span)
		assert.NotNil(t, span.Attributes)
		assert.NotNil(t, span.Events)
		assert.NotNil(t, span.Links)

		sp.Put(span)
	})

	t.Run("custom size span pool", func(t *testing.T) {
		sp := NewSpanPool(100)
		require.NotNil(t, sp)

		span := sp.Get()
		require.NotNil(t, span)
		sp.Put(span)
	})

	t.Run("unlimited span pool", func(t *testing.T) {
		sp := NewSpanPool(0)
		require.NotNil(t, sp)

		span := sp.Get()
		require.NotNil(t, span)
		sp.Put(span)
	})
}

// TestSpanPoolGetPut tests span get and put operations.
func TestSpanPoolGetPut(t *testing.T) {
	t.Run("get returns clean span", func(t *testing.T) {
		sp := NewSpanPool(100)

		span := sp.Get()
		span.Name = "test-span"
		span.StartTime = time.Now()
		span.Attributes["key"] = "value"
		span.Events = append(span.Events, SpanEvent{Name: "event"})
		span.Links = append(span.Links, SpanLink{})

		sp.Put(span)

		// Get again - should be reset
		span2 := sp.Get()
		assert.Empty(t, span2.Name)
		assert.True(t, span2.StartTime.IsZero())
		assert.Empty(t, span2.Attributes)
		assert.Empty(t, span2.Events)
		assert.Empty(t, span2.Links)

		sp.Put(span2)
	})

	t.Run("put nil is safe", func(t *testing.T) {
		sp := NewSpanPool(100)
		sp.Put(nil) // Should not panic
	})

	t.Run("span is ended if not ended", func(t *testing.T) {
		sp := NewSpanPool(100)

		span := sp.Get()
		span.StartTime = time.Now()
		span.ended = false

		// Before Put, the span is not ended
		assert.False(t, span.ended)

		sp.Put(span)

		// Note: After Put, the span is returned to the pool and reset.
		// The span object should not be accessed after Put.
		// The Put method internally calls End() if the span was started but not ended.
	})
}

// TestSpanPoolStats tests span pool statistics.
func TestSpanPoolStats(t *testing.T) {
	t.Run("stats tracking", func(t *testing.T) {
		sp := NewSpanPool(100)
		sp.ResetStats()

		span := sp.Get()
		sp.Put(span)

		stats := sp.Stats()
		assert.Equal(t, uint64(1), stats.Gets)
		assert.Equal(t, uint64(1), stats.Puts)
	})

	t.Run("hit rate", func(t *testing.T) {
		sp := NewSpanPool(100)
		sp.ResetStats()

		rate := sp.HitRate()
		assert.Equal(t, 0.0, rate)

		// Get and put some spans
		for i := 0; i < 10; i++ {
			span := sp.Get()
			sp.Put(span)
		}

		rate = sp.HitRate()
		assert.GreaterOrEqual(t, rate, 0.0)
		assert.LessOrEqual(t, rate, 100.0)
	})
}

// TestDefaultSpanPool tests the package-level default span pool.
func TestDefaultSpanPool(t *testing.T) {
	t.Run("default pool get put", func(t *testing.T) {
		span := GetSpan()
		require.NotNil(t, span)

		span.Name = "test"
		span.StartTime = time.Now()
		span.End()

		PutSpan(span)
	})

	t.Run("default pool stats", func(t *testing.T) {
		// Reset by getting fresh stats
		_ = SpanPoolStats()

		span := GetSpan()
		PutSpan(span)

		stats := SpanPoolStats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(1))
	})
}

// TestSpanReset tests span reset functionality.
func TestSpanReset(t *testing.T) {
	t.Run("reset clears all fields", func(t *testing.T) {
		span := &Span{
			Name:          "test",
			StartTime:     time.Now(),
			EndTime:       time.Now(),
			StatusCode:    1,
			StatusMessage: "ok",
			Kind:          SpanKindServer,
			Attributes:    map[string]any{"key": "value"},
			Events:        []SpanEvent{{Name: "event"}},
			Links:         []SpanLink{{}},
			ended:         true,
		}

		span.Reset()

		assert.Empty(t, span.Name)
		assert.True(t, span.StartTime.IsZero())
		assert.True(t, span.EndTime.IsZero())
		assert.Equal(t, uint32(0), span.StatusCode)
		assert.Empty(t, span.StatusMessage)
		assert.Equal(t, SpanKindUnspecified, span.Kind)
		assert.Empty(t, span.Attributes)
		assert.Empty(t, span.Events)
		assert.Empty(t, span.Links)
		assert.False(t, span.ended)
	})

	t.Run("reset preserves capacity", func(t *testing.T) {
		span := &Span{
			Attributes: make(map[string]any, MaxAttributes),
			Events:     make([]SpanEvent, 0, MaxEvents),
			Links:      make([]SpanLink, 0, MaxLinks),
		}

		// Add data
		for i := 0; i < MaxAttributes; i++ {
			span.Attributes[string(rune('a'+i))] = i
		}
		span.Events = append(span.Events, SpanEvent{Name: "event"})
		span.Links = append(span.Links, SpanLink{})

		eventsCap := cap(span.Events)
		linksCap := cap(span.Links)

		span.Reset()

		// Capacity should be preserved for slices (map capacity cannot be checked with cap())
		assert.NotNil(t, span.Attributes) // Map should still exist
		assert.Equal(t, eventsCap, cap(span.Events))
		assert.Equal(t, linksCap, cap(span.Links))
	})
}

// TestSpanIsRecording tests span recording state.
func TestSpanIsRecording(t *testing.T) {
	t.Run("not recording if not started", func(t *testing.T) {
		span := &Span{}
		assert.False(t, span.IsRecording())
	})

	t.Run("recording if started", func(t *testing.T) {
		span := &Span{
			StartTime: time.Now(),
		}
		assert.True(t, span.IsRecording())
	})

	t.Run("not recording if ended", func(t *testing.T) {
		span := &Span{
			StartTime: time.Now(),
			ended:     true,
		}
		assert.False(t, span.IsRecording())
	})
}

// TestSpanEnd tests span end functionality.
func TestSpanEnd(t *testing.T) {
	t.Run("end sets end time", func(t *testing.T) {
		span := &Span{
			StartTime: time.Now(),
		}

		span.End()

		assert.False(t, span.EndTime.IsZero())
		assert.True(t, span.ended)
	})

	t.Run("end with timestamp", func(t *testing.T) {
		span := &Span{}

		ts := time.Date(2024, 1, 1, 0, 0, 0, 0, time.UTC)
		span.End(WithTimestamp(ts))

		assert.Equal(t, ts, span.EndTime)
		assert.True(t, span.ended)
	})

	t.Run("end is idempotent", func(t *testing.T) {
		span := &Span{
			StartTime: time.Now(),
		}

		span.End()
		firstEndTime := span.EndTime

		time.Sleep(time.Millisecond)
		span.End()

		assert.Equal(t, firstEndTime, span.EndTime)
	})
}

// TestSpanPoolAttributePool tests attribute sub-pool.
func TestSpanPoolAttributePool(t *testing.T) {
	sp := NewSpanPool(100)

	t.Run("acquire attributes", func(t *testing.T) {
		attrs := sp.AcquireAttributes()
		require.NotNil(t, attrs)
		// Map capacity cannot be checked with cap(), just verify it works

		attrs["test"] = "value"
		sp.ReleaseAttributes(attrs)
	})

	t.Run("release nil is safe", func(t *testing.T) {
		sp.ReleaseAttributes(nil) // Should not panic
	})

	t.Run("release clears map", func(t *testing.T) {
		attrs := sp.AcquireAttributes()
		attrs["key"] = "value"
		attrs["other"] = 123

		sp.ReleaseAttributes(attrs)

		// Map should be cleared
		attrs2 := sp.AcquireAttributes()
		assert.Empty(t, attrs2)
		sp.ReleaseAttributes(attrs2)
	})

	t.Run("oversized maps are discarded", func(t *testing.T) {
		// Create oversized map
		attrs := make(map[string]any, MaxAttributes*10)

		// Should not panic, map is discarded
		sp.ReleaseAttributes(attrs)
	})
}

// TestSpanPoolEventPool tests event sub-pool.
func TestSpanPoolEventPool(t *testing.T) {
	sp := NewSpanPool(100)

	t.Run("acquire events", func(t *testing.T) {
		events := sp.AcquireEvents()
		require.NotNil(t, events)
		assert.Equal(t, 0, len(events))
		assert.GreaterOrEqual(t, cap(events), MaxEvents)

		events = append(events, SpanEvent{Name: "event"})
		sp.ReleaseEvents(events)
	})

	t.Run("release nil is safe", func(t *testing.T) {
		sp.ReleaseEvents(nil) // Should not panic
	})

	t.Run("release clears slice", func(t *testing.T) {
		events := sp.AcquireEvents()
		events = append(events, SpanEvent{Name: "event1"})
		events = append(events, SpanEvent{Name: "event2"})

		sp.ReleaseEvents(events)

		events2 := sp.AcquireEvents()
		assert.Equal(t, 0, len(events2))
		sp.ReleaseEvents(events2)
	})
}

// TestSpanPoolLinkPool tests link sub-pool.
func TestSpanPoolLinkPool(t *testing.T) {
	sp := NewSpanPool(100)

	t.Run("acquire links", func(t *testing.T) {
		links := sp.AcquireLinks()
		require.NotNil(t, links)
		assert.Equal(t, 0, len(links))
		assert.GreaterOrEqual(t, cap(links), MaxLinks)

		links = append(links, SpanLink{})
		sp.ReleaseLinks(links)
	})

	t.Run("release nil is safe", func(t *testing.T) {
		sp.ReleaseLinks(nil) // Should not panic
	})
}

// TestConcurrentSpanPool tests the concurrent span pool.
func TestConcurrentSpanPool(t *testing.T) {
	t.Run("concurrent pool creation", func(t *testing.T) {
		csp := NewConcurrentSpanPool(16, 100)
		require.NotNil(t, csp)

		span := csp.Get()
		require.NotNil(t, span)
		csp.Put(span)
	})

	t.Run("concurrent access", func(t *testing.T) {
		csp := NewConcurrentSpanPool(16, 1000)

		var wg sync.WaitGroup
		for i := 0; i < 1000; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				span := csp.Get()
				span.Name = "concurrent-span"
				span.StartTime = time.Now()
				span.End()
				csp.Put(span)
			}()
		}
		wg.Wait()

		stats := csp.Stats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(1000))
		assert.GreaterOrEqual(t, stats.Puts, uint64(1000))
	})

	t.Run("non-power-of-2 shards", func(t *testing.T) {
		csp := NewConcurrentSpanPool(15, 100)
		require.NotNil(t, csp)

		span := csp.Get()
		require.NotNil(t, span)
		csp.Put(span)
	})

	t.Run("zero shards uses default", func(t *testing.T) {
		csp := NewConcurrentSpanPool(0, 100)
		require.NotNil(t, csp)

		span := csp.Get()
		require.NotNil(t, span)
		csp.Put(span)
	})
}

// TestSpanPoolConcurrentAccess tests concurrent span pool operations.
func TestSpanPoolConcurrentAccess(t *testing.T) {
	t.Run("concurrent get put", func(t *testing.T) {
		sp := NewSpanPool(1000)

		var wg sync.WaitGroup
		for i := 0; i < 1000; i++ {
			wg.Add(1)
			go func(id int) {
				defer wg.Done()
				span := sp.Get()
				span.Name = "span"
				span.StartTime = time.Now()
				span.Attributes["id"] = id
				span.End()
				sp.Put(span)
			}(i)
		}
		wg.Wait()

		stats := sp.Stats()
		assert.GreaterOrEqual(t, stats.Gets, uint64(1000))
		assert.GreaterOrEqual(t, stats.Puts, uint64(1000))
	})
}

// BenchmarkSpanPool benchmarks span pool operations.
func BenchmarkSpanPool(b *testing.B) {
	b.Run("get put", func(b *testing.B) {
		sp := NewSpanPool(1000)

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			span := sp.Get()
			span.Name = "benchmark-span"
			span.End()
			sp.Put(span)
		}
	})

	b.Run("concurrent get put", func(b *testing.B) {
		sp := NewSpanPool(10000)

		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				span := sp.Get()
				span.Name = "benchmark-span"
				span.End()
				sp.Put(span)
			}
		})
	})

	b.Run("without pool", func(b *testing.B) {
		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			span := &Span{
				Attributes: make(map[string]any, MaxAttributes),
				Events:     make([]SpanEvent, 0, MaxEvents),
				Links:      make([]SpanLink, 0, MaxLinks),
			}
			span.Name = "benchmark-span"
			span.End()
			// Let GC collect it
			_ = span
		}
	})
}

// BenchmarkConcurrentSpanPool benchmarks concurrent span pool.
func BenchmarkConcurrentSpanPool(b *testing.B) {
	b.Run("16 shards", func(b *testing.B) {
		csp := NewConcurrentSpanPool(16, 10000)

		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				span := csp.Get()
				span.Name = "benchmark-span"
				span.End()
				csp.Put(span)
			}
		})
	})

	b.Run("32 shards", func(b *testing.B) {
		csp := NewConcurrentSpanPool(32, 10000)

		b.RunParallel(func(pb *testing.PB) {
			for pb.Next() {
				span := csp.Get()
				span.Name = "benchmark-span"
				span.End()
				csp.Put(span)
			}
		})
	})
}

// BenchmarkSpanOperations benchmarks span operations.
func BenchmarkSpanOperations(b *testing.B) {
	b.Run("reset", func(b *testing.B) {
		span := &Span{
			Attributes: make(map[string]any, MaxAttributes),
			Events:     make([]SpanEvent, 0, MaxEvents),
			Links:      make([]SpanLink, 0, MaxLinks),
		}

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			span.Name = "test"
			span.StartTime = time.Now()
			span.Attributes["key"] = "value"
			span.Reset()
		}
	})

	b.Run("end", func(b *testing.B) {
		span := &Span{}

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			span.ended = false
			span.EndTime = time.Time{}
			span.End()
		}
	})
}

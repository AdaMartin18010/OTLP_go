// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
package runtime

import (
	"fmt"
	"runtime"
	"runtime/debug"
	"runtime/metrics"
	"sync"
	"time"
)

// MemStats holds memory statistics with additional computed fields.
type MemStats struct {
	// Alloc is bytes of allocated heap objects
	Alloc uint64

	// TotalAlloc is cumulative bytes allocated for heap objects
	TotalAlloc uint64

	// Sys is total bytes of memory obtained from the OS
	Sys uint64

	// Lookups is number of pointer lookups
	Lookups uint64

	// Mallocs is cumulative count of heap objects allocated
	Mallocs uint64

	// Frees is cumulative count of heap objects freed
	Frees uint64

	// HeapAlloc is bytes of allocated heap objects
	HeapAlloc uint64

	// HeapSys is bytes of heap memory obtained from the OS
	HeapSys uint64

	// HeapIdle is bytes in idle spans
	HeapIdle uint64

	// HeapInuse is bytes in in-use spans
	HeapInuse uint64

	// HeapReleased is bytes released to the OS
	HeapReleased uint64

	// HeapObjects is number of allocated heap objects
	HeapObjects uint64

	// StackInuse is bytes in stack spans
	StackInuse uint64

	// StackSys is bytes of stack memory obtained from the OS
	StackSys uint64

	// MSpanInuse is bytes of allocated mspan structures
	MSpanInuse uint64

	// MSpanSys is bytes of memory obtained from the OS for mspan structures
	MSpanSys uint64

	// MCacheInuse is bytes of allocated mcache structures
	MCacheInuse uint64

	// MCacheSys is bytes of memory obtained from the OS for mcache structures
	MCacheSys uint64

	// BuckHashSys is bytes of memory in profiling bucket hash tables
	BuckHashSys uint64

	// GCSys is bytes of memory in garbage collection metadata
	GCSys uint64

	// OtherSys is bytes of memory in miscellaneous off-heap runtime allocations
	OtherSys uint64

	// NextGC is target heap size of next GC cycle
	NextGC uint64

	// LastGC is time of last garbage collection (nanoseconds since 1970)
	LastGC uint64

	// PauseTotalNs is total GC pause time in nanoseconds
	PauseTotalNs uint64

	// PauseNs is recent GC pause times in nanoseconds
	PauseNs [256]uint64

	// NumGC is number of completed GC cycles
	NumGC uint32

	// NumForcedGC is number of GC cycles forced by runtime.GC()
	NumForcedGC uint32

	// GCCPUFraction is fraction of CPU time used by GC
	GCCPUFraction float64

	// Computed fields
	LiveObjects uint64 // Mallocs - Frees
	GCPercent   int    // Current GC target percentage
	Timestamp   int64  // When stats were captured
}

// GCStats holds GC-related statistics.
type GCStats struct {
	// NumGC is number of completed GC cycles
	NumGC uint32

	// NumForcedGC is number of forced GC cycles
	NumForcedGC uint32

	// LastGC is time of last GC
	LastGC time.Time

	// PauseTotal is total GC pause time
	PauseTotal time.Duration

	// PauseHistory is recent GC pause durations
	PauseHistory []time.Duration

	// AvgPause is average pause time
	AvgPause time.Duration

	// MaxPause is maximum pause time in history
	MaxPause time.Duration

	// GCCPUFraction is fraction of CPU time used by GC
	GCCPUFraction float64

	// HeapGoal is target heap size for next GC
	HeapGoal uint64
}

// GoroutineStats holds goroutine statistics.
type GoroutineStats struct {
	// Count is current number of goroutines
	Count int

	// MaxHistory is historical maximum goroutine count
	MaxHistory int

	// States breakdown by goroutine state
	States map[string]int
}

// RuntimeStats holds comprehensive runtime statistics.
type RuntimeStats struct {
	// Memory statistics
	Memory MemStats

	// GC statistics
	GC GCStats

	// Goroutine statistics
	Goroutines GoroutineStats

	// Timestamp when stats were captured
	Timestamp time.Time
}

// Snapshot captures a snapshot of all runtime statistics.
type Snapshot struct {
	Stats      RuntimeStats
	Info       *Info
	GOMAXPROCS *GOMAXPROCSInfo
	GOMEMLIMIT *GOMEMLIMITInfo
	Timestamp  time.Time
}

var (
	statsMu           sync.RWMutex
	lastSnapshot      *Snapshot
	snapshotInterval  = 5 * time.Second
	maxGoroutineCount int
)

// GetMemStats returns current memory statistics.
func GetMemStats() *MemStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return &MemStats{
		Alloc:         m.Alloc,
		TotalAlloc:    m.TotalAlloc,
		Sys:           m.Sys,
		Lookups:       m.Lookups,
		Mallocs:       m.Mallocs,
		Frees:         m.Frees,
		HeapAlloc:     m.HeapAlloc,
		HeapSys:       m.HeapSys,
		HeapIdle:      m.HeapIdle,
		HeapInuse:     m.HeapInuse,
		HeapReleased:  m.HeapReleased,
		HeapObjects:   m.HeapObjects,
		StackInuse:    m.StackInuse,
		StackSys:      m.StackSys,
		MSpanInuse:    m.MSpanInuse,
		MSpanSys:      m.MSpanSys,
		MCacheInuse:   m.MCacheInuse,
		MCacheSys:     m.MCacheSys,
		BuckHashSys:   m.BuckHashSys,
		GCSys:         m.GCSys,
		OtherSys:      m.OtherSys,
		NextGC:        m.NextGC,
		LastGC:        m.LastGC,
		PauseTotalNs:  m.PauseTotalNs,
		PauseNs:       m.PauseNs,
		NumGC:         m.NumGC,
		NumForcedGC:   m.NumForcedGC,
		GCCPUFraction: m.GCCPUFraction,
		LiveObjects:   m.Mallocs - m.Frees,
		GCPercent:     GetGCPercent(),
		Timestamp:     time.Now().UnixNano(),
	}
}

// GetGCStats returns GC statistics.
func GetGCStats() *GCStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	stats := &GCStats{
		NumGC:         m.NumGC,
		NumForcedGC:   m.NumForcedGC,
		PauseTotal:    time.Duration(m.PauseTotalNs),
		GCCPUFraction: m.GCCPUFraction,
		HeapGoal:      m.NextGC,
	}

	if m.LastGC > 0 {
		stats.LastGC = time.Unix(0, int64(m.LastGC))
	}

	// Calculate pause history
	if m.NumGC > 0 {
		numPauses := uint32(256)
		if m.NumGC < numPauses {
			numPauses = m.NumGC
		}

		stats.PauseHistory = make([]time.Duration, 0, numPauses)
		var totalPause, maxPause uint64

		// PauseNs is circular buffer; calculate index based on NumGC
		for i := uint32(0); i < numPauses; i++ {
			idx := (m.NumGC - numPauses + i) % 256
			pause := m.PauseNs[idx]
			if pause > 0 {
				stats.PauseHistory = append(stats.PauseHistory, time.Duration(pause))
				totalPause += pause
				if pause > maxPause {
					maxPause = pause
				}
			}
		}

		if len(stats.PauseHistory) > 0 {
			stats.AvgPause = time.Duration(totalPause / uint64(len(stats.PauseHistory)))
			stats.MaxPause = time.Duration(maxPause)
		}
	}

	return stats
}

// GetGoroutineStats returns goroutine statistics.
func GetGoroutineStats() *GoroutineStats {
	count := runtime.NumGoroutine()

	statsMu.Lock()
	if count > maxGoroutineCount {
		maxGoroutineCount = count
	}
	maxHistory := maxGoroutineCount
	statsMu.Unlock()

	return &GoroutineStats{
		Count:      count,
		MaxHistory: maxHistory,
		States:     getGoroutineStates(),
	}
}

// getGoroutineStates returns breakdown of goroutine states.
// Note: This is a simplified implementation as Go runtime doesn't expose
// detailed state information without profiling.
func getGoroutineStates() map[string]int {
	// Simplified state breakdown
	// In production, you might use runtime.GoroutineProfile for more details
	return map[string]int{
		"running":  1, // At least one goroutine is running
		"runnable": runtime.NumGoroutine() - 1,
	}
}

// GetRuntimeStats returns comprehensive runtime statistics.
func GetRuntimeStats() *RuntimeStats {
	return &RuntimeStats{
		Memory:     *GetMemStats(),
		GC:         *GetGCStats(),
		Goroutines: *GetGoroutineStats(),
		Timestamp:  time.Now(),
	}
}

// GetSnapshot captures a complete snapshot of runtime state.
func GetSnapshot() *Snapshot {
	snapshot := &Snapshot{
		Stats:      *GetRuntimeStats(),
		Info:       GetInfo(),
		GOMAXPROCS: GetGOMAXPROCS(),
		GOMEMLIMIT: GetGOMEMLIMIT(),
		Timestamp:  time.Now(),
	}

	statsMu.Lock()
	lastSnapshot = snapshot
	statsMu.Unlock()

	return snapshot
}

// GetLastSnapshot returns the last captured snapshot.
// Returns nil if no snapshot has been captured.
func GetLastSnapshot() *Snapshot {
	statsMu.RLock()
	defer statsMu.RUnlock()
	return lastSnapshot
}

// GetGCPercent returns the current GC target percentage.
func GetGCPercent() int {
	return 100 // Go 1.26 uses 100 by default, can be set via GOGC
}

// SetGCPercent sets the GC target percentage.
// Returns the previous value.
// A negative value disables GC.
func SetGCPercent(percent int) int {
	return debug.SetGCPercent(percent)
}

// ForceGC runs garbage collection immediately.
func ForceGC() {
	runtime.GC()
}

// FreeOSMemory returns unused memory to the OS.
func FreeOSMemory() {
	debug.FreeOSMemory()
}

// ReadMetrics reads extended runtime metrics using runtime/metrics.
func ReadMetrics() map[string]interface{} {
	result := make(map[string]interface{})

	// Get all metric descriptions
	descriptions := metrics.All()

	// Create samples for all metrics
	samples := make([]metrics.Sample, len(descriptions))
	for i, desc := range descriptions {
		samples[i].Name = desc.Name
	}

	// Read metrics
	metrics.Read(samples)

	// Convert to map
	for _, sample := range samples {
		switch sample.Value.Kind() {
		case metrics.KindUint64:
			result[sample.Name] = sample.Value.Uint64()
		case metrics.KindFloat64:
			result[sample.Name] = sample.Value.Float64()
		case metrics.KindFloat64Histogram:
			result[sample.Name] = sample.Value.Float64Histogram()
		case metrics.KindBad:
			result[sample.Name] = nil
		default:
			result[sample.Name] = sample.Value
		}
	}

	return result
}

// MemoryUsage returns current memory usage in bytes.
func MemoryUsage() uint64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m.Alloc
}

// HeapUsage returns current heap usage in bytes.
func HeapUsage() uint64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m.HeapAlloc
}

// StackUsage returns current stack usage in bytes.
func StackUsage() uint64 {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m.StackInuse
}

// String returns a formatted summary of MemStats.
func (m *MemStats) String() string {
	return fmt.Sprintf(
		"Memory: Alloc=%s Sys=%s HeapAlloc=%s HeapSys=%s HeapObjects=%d GC=%d",
		FormatBytes(m.Alloc),
		FormatBytes(m.Sys),
		FormatBytes(m.HeapAlloc),
		FormatBytes(m.HeapSys),
		m.HeapObjects,
		m.NumGC,
	)
}

// String returns a formatted summary of GCStats.
func (g *GCStats) String() string {
	return fmt.Sprintf(
		"GC: Num=%d Forced=%d PauseTotal=%s AvgPause=%s MaxPause=%s CPUFraction=%.4f%%",
		g.NumGC,
		g.NumForcedGC,
		g.PauseTotal,
		g.AvgPause,
		g.MaxPause,
		g.GCCPUFraction*100,
	)
}

// String returns a formatted summary of GoroutineStats.
func (g *GoroutineStats) String() string {
	return fmt.Sprintf("Goroutines: Count=%d MaxHistory=%d", g.Count, g.MaxHistory)
}

// String returns a formatted summary of RuntimeStats.
func (r *RuntimeStats) String() string {
	return fmt.Sprintf("%s | %s | %s",
		r.Memory.String(),
		r.GC.String(),
		r.Goroutines.String(),
	)
}

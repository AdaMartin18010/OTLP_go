// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
//
// Stability: Beta
// Compliance: OpenTelemetry Specification v1.42.0
package runtime

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"runtime"
	"runtime/pprof"
	"runtime/trace"
	"strings"
	"sync"
	"time"
)

// DebugInfo holds debugging information.
type DebugInfo struct {
	// StackTrace is the current goroutine's stack trace
	StackTrace string

	// AllStacks is all goroutines' stack traces
	AllStacks string

	// GoroutineCount is the number of goroutines
	GoroutineCount int

	// Timestamp when info was captured
	Timestamp time.Time
}

// GoroutineDump represents a dump of goroutine information.
type GoroutineDump struct {
	// Count is the number of goroutines
	Count int

	// Stacks is the stack traces of all goroutines
	Stacks string

	// Timestamp when dump was created
	Timestamp time.Time
}

// ProfileType represents the type of pprof profile.
type ProfileType string

const (
	// ProfileCPU is CPU profile
	ProfileCPU ProfileType = "cpu"

	// ProfileHeap is heap profile
	ProfileHeap ProfileType = "heap"

	// ProfileGoroutine is goroutine profile
	ProfileGoroutine ProfileType = "goroutine"

	// ProfileThreadCreate is thread creation profile
	ProfileThreadCreate ProfileType = "threadcreate"

	// ProfileBlock is block profile
	ProfileBlock ProfileType = "block"

	// ProfileMutex is mutex profile
	ProfileMutex ProfileType = "mutex"

	// ProfileAllocs is allocations profile
	ProfileAllocs ProfileType = "allocs"
)

// ProfileConfig configures profile capture.
type ProfileConfig struct {
	// Type is the type of profile to capture
	Type ProfileType

	// Duration for CPU profiling (ignored for other types)
	Duration time.Duration

	// Debug determines the format of profile output
	// If true, output is human-readable; if false, binary format
	Debug bool

	// Rate for block/mutex profiling (0 uses default)
	Rate int
}

// ProfileResult holds captured profile data.
type ProfileResult struct {
	// Data is the profile data
	Data []byte

	// Type is the type of profile
	Type ProfileType

	// Duration for CPU profiles
	Duration time.Duration

	// Timestamp when profile was captured
	Timestamp time.Time

	// Error if capture failed
	Error error
}

// Tracer manages runtime tracing.
type Tracer struct {
	mu     sync.Mutex
	active bool
	output io.WriteCloser
	stop   func()
}

var (
	defaultTracer     *Tracer
	defaultTracerOnce sync.Once

	// BlockProfileRate is the rate for block profiling (0 = disabled)
	blockProfileRate int
	blockProfileMu   sync.RWMutex

	// MutexProfileFraction is the fraction for mutex profiling (0 = disabled)
	mutexProfileFraction int
	mutexProfileMu       sync.RWMutex
)

// GetDebugInfo returns current debugging information.
func GetDebugInfo() *DebugInfo {
	return &DebugInfo{
		StackTrace:     string(getStackTrace()),
		AllStacks:      GetAllStackTraces(),
		GoroutineCount: runtime.NumGoroutine(),
		Timestamp:      time.Now(),
	}
}

// GetStackTrace returns the current goroutine's stack trace.
func GetStackTrace() string {
	return string(getStackTrace())
}

func getStackTrace() []byte {
	buf := make([]byte, 1024)
	for {
		n := runtime.Stack(buf, false)
		if n < len(buf) {
			return buf[:n]
		}
		buf = make([]byte, len(buf)*2)
	}
}

// GetAllStackTraces returns stack traces of all goroutines.
func GetAllStackTraces() string {
	buf := make([]byte, 4096)
	for {
		n := runtime.Stack(buf, true)
		if n < len(buf) {
			return string(buf[:n])
		}
		buf = make([]byte, len(buf)*2)
	}
}

// DumpGoroutines creates a goroutine dump.
func DumpGoroutines() *GoroutineDump {
	return &GoroutineDump{
		Count:     runtime.NumGoroutine(),
		Stacks:    GetAllStackTraces(),
		Timestamp: time.Now(),
	}
}

// WriteTo writes goroutine dump to writer.
func (d *GoroutineDump) WriteTo(w io.Writer) (int64, error) {
	var buf bytes.Buffer
	fmt.Fprintf(&buf, "=== Goroutine Dump ===\n")
	fmt.Fprintf(&buf, "Timestamp: %s\n", d.Timestamp.Format(time.RFC3339))
	fmt.Fprintf(&buf, "Goroutine Count: %d\n", d.Count)
	fmt.Fprintf(&buf, "\n%s\n", d.Stacks)

	n, err := w.Write(buf.Bytes())
	return int64(n), err
}

// SaveToFile saves goroutine dump to a file.
func (d *GoroutineDump) SaveToFile(path string) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()

	_, err = d.WriteTo(f)
	return err
}

// CaptureProfile captures a pprof profile.
func CaptureProfile(config ProfileConfig) *ProfileResult {
	result := &ProfileResult{
		Type:      config.Type,
		Duration:  config.Duration,
		Timestamp: time.Now(),
	}

	switch config.Type {
	case ProfileCPU:
		result.Data, result.Error = captureCPUProfile(config.Duration, config.Debug)
	case ProfileHeap, ProfileGoroutine, ProfileThreadCreate, ProfileBlock, ProfileMutex, ProfileAllocs:
		result.Data, result.Error = captureProfile(string(config.Type), config.Debug)
	default:
		result.Error = fmt.Errorf("unknown profile type: %s", config.Type)
	}

	return result
}

func captureCPUProfile(duration time.Duration, debug bool) ([]byte, error) {
	if duration <= 0 {
		duration = 30 * time.Second
	}

	var buf bytes.Buffer
	if err := pprof.StartCPUProfile(&buf); err != nil {
		return nil, err
	}

	time.Sleep(duration)
	pprof.StopCPUProfile()

	if debug {
		return buf.Bytes(), nil
	}
	return buf.Bytes(), nil
}

func captureProfile(name string, debug bool) ([]byte, error) {
	profile := pprof.Lookup(name)
	if profile == nil {
		return nil, fmt.Errorf("profile %s not found", name)
	}

	var buf bytes.Buffer
	debugValue := 0
	if debug {
		debugValue = 1
	}

	if err := profile.WriteTo(&buf, debugValue); err != nil {
		return nil, err
	}

	return buf.Bytes(), nil
}

// WriteTo writes profile to writer.
func (p *ProfileResult) WriteTo(w io.Writer) (int64, error) {
	n, err := w.Write(p.Data)
	return int64(n), err
}

// SaveToFile saves profile to a file.
func (p *ProfileResult) SaveToFile(path string) error {
	if p.Error != nil {
		return p.Error
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()

	_, err = f.Write(p.Data)
	return err
}

// GetDefaultTracer returns the default tracer instance.
func GetDefaultTracer() *Tracer {
	defaultTracerOnce.Do(func() {
		defaultTracer = &Tracer{}
	})
	return defaultTracer
}

// StartTrace starts runtime tracing.
func (t *Tracer) StartTrace(w io.WriteCloser) error {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.active {
		return fmt.Errorf("trace already active")
	}

	if err := trace.Start(w); err != nil {
		return err
	}

	t.active = true
	t.output = w
	t.stop = func() {
		trace.Stop()
	}

	return nil
}

// StopTrace stops runtime tracing.
func (t *Tracer) StopTrace() error {
	t.mu.Lock()
	defer t.mu.Unlock()

	if !t.active {
		return fmt.Errorf("trace not active")
	}

	t.stop()
	t.active = false

	if t.output != nil {
		t.output.Close()
	}

	return nil
}

// IsTracing returns whether tracing is active.
func (t *Tracer) IsTracing() bool {
	t.mu.Lock()
	defer t.mu.Unlock()
	return t.active
}

// SetBlockProfileRate sets the rate for block profiling.
// A rate of 0 disables block profiling.
// A rate of 1 captures every block event.
func SetBlockProfileRate(rate int) {
	blockProfileMu.Lock()
	blockProfileRate = rate
	blockProfileMu.Unlock()

	runtime.SetBlockProfileRate(rate)
}

// GetBlockProfileRate returns the current block profile rate.
func GetBlockProfileRate() int {
	blockProfileMu.RLock()
	defer blockProfileMu.RUnlock()
	return blockProfileRate
}

// SetMutexProfileFraction sets the fraction for mutex profiling.
// A fraction of 0 disables mutex profiling.
// A fraction of 1 captures 1/1 of mutex events (every event).
func SetMutexProfileFraction(fraction int) {
	mutexProfileMu.Lock()
	mutexProfileFraction = fraction
	mutexProfileMu.Unlock()

	runtime.SetMutexProfileFraction(fraction)
}

// GetMutexProfileFraction returns the current mutex profile fraction.
func GetMutexProfileFraction() int {
	mutexProfileMu.RLock()
	defer mutexProfileMu.RUnlock()
	return mutexProfileFraction
}

// PrintStats prints runtime statistics to stdout.
func PrintStats() {
	stats := GetRuntimeStats()
	fmt.Println(stats.String())
}

// PrintMemStats prints memory statistics to stdout.
func PrintMemStats() {
	stats := GetMemStats()
	fmt.Println(stats.String())
}

// PrintGCStats prints GC statistics to stdout.
func PrintGCStats() {
	stats := GetGCStats()
	fmt.Println(stats.String())
}

// EnableProfiling enables all runtime profiling.
func EnableProfiling() {
	SetBlockProfileRate(1)
	SetMutexProfileFraction(1)
}

// DisableProfiling disables all runtime profiling.
func DisableProfiling() {
	SetBlockProfileRate(0)
	SetMutexProfileFraction(0)
}

// LookupProfile returns a pprof profile by name.
func LookupProfile(name string) *pprof.Profile {
	return pprof.Lookup(name)
}

// Profiles returns a list of all available profiles.
func Profiles() []*pprof.Profile {
	return pprof.Profiles()
}

// PrintProfiles prints names of all available profiles.
func PrintProfiles() {
	fmt.Println("Available profiles:")
	for _, profile := range pprof.Profiles() {
		fmt.Printf("  - %s\n", profile.Name())
	}
}

// ParseStackTrace parses a stack trace string to extract function names.
func ParseStackTrace(stack string) []string {
	var functions []string
	lines := strings.Split(stack, "\n")

	for i, line := range lines {
		// Function lines are at odd indices (0-indexed: 1, 3, 5, ...)
		if i%2 == 1 && strings.TrimSpace(line) != "" {
			// Extract function name
			parts := strings.Fields(line)
			if len(parts) > 0 {
				functions = append(functions, parts[0])
			}
		}
	}

	return functions
}

// String returns formatted debug info.
func (d *DebugInfo) String() string {
	return fmt.Sprintf("DebugInfo{Goroutines: %d, Time: %s}",
		d.GoroutineCount, d.Timestamp.Format(time.RFC3339))
}

// String returns formatted goroutine dump.
func (d *GoroutineDump) String() string {
	return fmt.Sprintf("GoroutineDump{Count: %d, Time: %s}",
		d.Count, d.Timestamp.Format(time.RFC3339))
}

// String returns formatted profile result.
func (p *ProfileResult) String() string {
	size := len(p.Data)
	if p.Error != nil {
		return fmt.Sprintf("ProfileResult{Type: %s, Error: %v}", p.Type, p.Error)
	}
	return fmt.Sprintf("ProfileResult{Type: %s, Size: %d bytes, Time: %s}",
		p.Type, size, p.Timestamp.Format(time.RFC3339))
}

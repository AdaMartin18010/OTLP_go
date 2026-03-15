// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
package runtime

import (
	"bytes"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestGetDebugInfo tests debug info retrieval.
func TestGetDebugInfo(t *testing.T) {
	info := GetDebugInfo()
	require.NotNil(t, info)

	assert.NotEmpty(t, info.StackTrace)
	assert.NotEmpty(t, info.AllStacks)
	assert.GreaterOrEqual(t, info.GoroutineCount, 1)
	assert.False(t, info.Timestamp.IsZero())
}

// TestGetStackTrace tests stack trace retrieval.
func TestGetStackTrace(t *testing.T) {
	trace := GetStackTrace()
	require.NotEmpty(t, trace)

	// Should contain current function name
	assert.Contains(t, trace, "TestGetStackTrace")

	// Should contain file path
	assert.Contains(t, trace, "runtime")
}

// TestGetAllStackTraces tests all stack traces retrieval.
func TestGetAllStackTraces(t *testing.T) {
	// Create some goroutines
	done := make(chan struct{})
	for i := 0; i < 3; i++ {
		go func() {
			<-done
		}()
	}
	time.Sleep(10 * time.Millisecond)

	traces := GetAllStackTraces()
	require.NotEmpty(t, traces)

	// Should contain multiple goroutine headers
	assert.Contains(t, traces, "goroutine")

	close(done)
}

// TestDumpGoroutines tests goroutine dump creation.
func TestDumpGoroutines(t *testing.T) {
	dump := DumpGoroutines()
	require.NotNil(t, dump)

	assert.GreaterOrEqual(t, dump.Count, 1)
	assert.NotEmpty(t, dump.Stacks)
	assert.False(t, dump.Timestamp.IsZero())
}

// TestGoroutineDumpWriteTo tests writing dump to writer.
func TestGoroutineDumpWriteTo(t *testing.T) {
	dump := DumpGoroutines()

	var buf bytes.Buffer
	n, err := dump.WriteTo(&buf)
	require.NoError(t, err)
	assert.Greater(t, n, int64(0))

	content := buf.String()
	assert.Contains(t, content, "=== Goroutine Dump ===")
	assert.Contains(t, content, "Timestamp:")
	assert.Contains(t, content, "Goroutine Count:")
}

// TestGoroutineDumpSaveToFile tests saving dump to file.
func TestGoroutineDumpSaveToFile(t *testing.T) {
	dump := DumpGoroutines()

	tmpDir := t.TempDir()
	path := filepath.Join(tmpDir, "goroutine_dump.txt")

	err := dump.SaveToFile(path)
	require.NoError(t, err)

	// Verify file exists and has content
	content, err := os.ReadFile(path)
	require.NoError(t, err)
	assert.Contains(t, string(content), "=== Goroutine Dump ===")
}

// TestCaptureProfile tests profile capture.
func TestCaptureProfile(t *testing.T) {
	t.Run("heap profile", func(t *testing.T) {
		// Allocate some memory first
		data := make([]byte, 1024*1024)
		_ = data

		result := CaptureProfile(ProfileConfig{
			Type:  ProfileHeap,
			Debug: true,
		})
		require.NotNil(t, result)
		assert.NoError(t, result.Error)
		assert.NotEmpty(t, result.Data)
		assert.Equal(t, ProfileHeap, result.Type)
	})

	t.Run("goroutine profile", func(t *testing.T) {
		result := CaptureProfile(ProfileConfig{
			Type:  ProfileGoroutine,
			Debug: true,
		})
		require.NotNil(t, result)
		assert.NoError(t, result.Error)
		assert.NotEmpty(t, result.Data)
	})

	t.Run("allocs profile", func(t *testing.T) {
		result := CaptureProfile(ProfileConfig{
			Type:  ProfileAllocs,
			Debug: true,
		})
		require.NotNil(t, result)
		assert.NoError(t, result.Error)
		assert.NotEmpty(t, result.Data)
	})

	t.Run("unknown profile type", func(t *testing.T) {
		result := CaptureProfile(ProfileConfig{
			Type:  "unknown",
			Debug: true,
		})
		require.NotNil(t, result)
		assert.Error(t, result.Error)
	})
}

// TestProfileResultWriteTo tests writing profile to writer.
func TestProfileResultWriteTo(t *testing.T) {
	result := &ProfileResult{
		Type:      ProfileHeap,
		Data:      []byte("test profile data"),
		Timestamp: time.Now(),
	}

	var buf bytes.Buffer
	n, err := result.WriteTo(&buf)
	require.NoError(t, err)
	assert.Equal(t, int64(17), n)
	assert.Equal(t, "test profile data", buf.String())
}

// TestProfileResultSaveToFile tests saving profile to file.
func TestProfileResultSaveToFile(t *testing.T) {
	result := CaptureProfile(ProfileConfig{
		Type:  ProfileGoroutine,
		Debug: true,
	})

	tmpDir := t.TempDir()
	path := filepath.Join(tmpDir, "goroutine.prof")

	err := result.SaveToFile(path)
	require.NoError(t, err)

	// Verify file exists
	_, err = os.Stat(path)
	assert.NoError(t, err)
}

// TestProfileResultSaveToFileWithError tests error handling.
func TestProfileResultSaveToFileWithError(t *testing.T) {
	result := &ProfileResult{
		Type:  ProfileHeap,
		Error: assert.AnError,
	}

	err := result.SaveToFile("/tmp/test.prof")
	assert.Error(t, err)
}

// TestTracer tests the tracer functionality.
func TestTracer(t *testing.T) {
	t.Run("get default tracer", func(t *testing.T) {
		tracer := GetDefaultTracer()
		assert.NotNil(t, tracer)

		// Should return same instance
		tracer2 := GetDefaultTracer()
		assert.Equal(t, tracer, tracer2)
	})

	t.Run("start and stop trace", func(t *testing.T) {
		tracer := &Tracer{}

		tmpDir := t.TempDir()
		path := filepath.Join(tmpDir, "trace.out")

		file, err := os.Create(path)
		require.NoError(t, err)

		err = tracer.StartTrace(file)
		require.NoError(t, err)
		assert.True(t, tracer.IsTracing())

		// Do some work while tracing
		time.Sleep(10 * time.Millisecond)
		runtime.GC()

		err = tracer.StopTrace()
		require.NoError(t, err)
		assert.False(t, tracer.IsTracing())

		// Verify file has content
		info, err := os.Stat(path)
		require.NoError(t, err)
		assert.Greater(t, info.Size(), int64(0))
	})

	t.Run("start trace when already active", func(t *testing.T) {
		tracer := &Tracer{}

		tmpDir := t.TempDir()
		path := filepath.Join(tmpDir, "trace.out")

		file, err := os.Create(path)
		require.NoError(t, err)

		err = tracer.StartTrace(file)
		require.NoError(t, err)

		// Try to start again
		err = tracer.StartTrace(file)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "already active")

		tracer.StopTrace()
	})

	t.Run("stop trace when not active", func(t *testing.T) {
		tracer := &Tracer{}

		err := tracer.StopTrace()
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "not active")
	})
}

// TestBlockProfileRate tests block profile rate management.
func TestBlockProfileRate(t *testing.T) {
	t.Run("set and get block profile rate", func(t *testing.T) {
		SetBlockProfileRate(100)
		rate := GetBlockProfileRate()
		assert.Equal(t, 100, rate)

		// Disable
		SetBlockProfileRate(0)
		rate = GetBlockProfileRate()
		assert.Equal(t, 0, rate)
	})
}

// TestMutexProfileFraction tests mutex profile fraction management.
func TestMutexProfileFraction(t *testing.T) {
	t.Run("set and get mutex profile fraction", func(t *testing.T) {
		SetMutexProfileFraction(2)
		fraction := GetMutexProfileFraction()
		assert.Equal(t, 2, fraction)

		// Disable
		SetMutexProfileFraction(0)
		fraction = GetMutexProfileFraction()
		assert.Equal(t, 0, fraction)
	})
}

// TestPrintStats tests printing stats to stdout.
func TestPrintStats(t *testing.T) {
	// Just ensure it doesn't panic
	assert.NotPanics(t, func() {
		PrintStats()
	})
}

// TestPrintMemStats tests printing memory stats to stdout.
func TestPrintMemStats(t *testing.T) {
	assert.NotPanics(t, func() {
		PrintMemStats()
	})
}

// TestPrintGCStats tests printing GC stats to stdout.
func TestPrintGCStats(t *testing.T) {
	assert.NotPanics(t, func() {
		PrintGCStats()
	})
}

// TestEnableDisableProfiling tests enabling/disabling profiling.
func TestEnableDisableProfiling(t *testing.T) {
	t.Run("enable profiling", func(t *testing.T) {
		EnableProfiling()

		assert.Greater(t, GetBlockProfileRate(), 0)
		assert.Greater(t, GetMutexProfileFraction(), 0)
	})

	t.Run("disable profiling", func(t *testing.T) {
		DisableProfiling()

		assert.Equal(t, 0, GetBlockProfileRate())
		assert.Equal(t, 0, GetMutexProfileFraction())
	})
}

// TestLookupProfile tests profile lookup.
func TestLookupProfile(t *testing.T) {
	profiles := []string{"heap", "goroutine", "allocs"}

	for _, name := range profiles {
		profile := LookupProfile(name)
		assert.NotNil(t, profile, "profile %s should exist", name)
		assert.Equal(t, name, profile.Name())
	}

	// Non-existent profile
	profile := LookupProfile("nonexistent")
	assert.Nil(t, profile)
}

// TestProfiles tests getting all profiles.
func TestProfiles(t *testing.T) {
	profiles := Profiles()
	assert.Greater(t, len(profiles), 0)

	// Check that common profiles exist
	profileNames := make(map[string]bool)
	for _, p := range profiles {
		profileNames[p.Name()] = true
	}

	assert.Contains(t, profileNames, "heap")
	assert.Contains(t, profileNames, "goroutine")
}

// TestPrintProfiles tests printing profile names.
func TestPrintProfiles(t *testing.T) {
	assert.NotPanics(t, func() {
		PrintProfiles()
	})
}

// TestParseStackTrace tests stack trace parsing.
func TestParseStackTrace(t *testing.T) {
	stack := `
goroutine 1 [running]:
main.doSomething()
	/path/to/main.go:42 +0x39
main.main()
	/path/to/main.go:20 +0x25

goroutine 2 [sleeping]:
time.Sleep(0x3b9aca00)
	/usr/local/go/src/runtime/time.go:193 +0x12e
main.worker()
	/path/to/main.go:50 +0x25
`

	functions := ParseStackTrace(stack)
	// The parser should find function names from the stack trace
	assert.NotEmpty(t, functions)
	// Check that we found some function-like patterns
	foundFunc := false
	for _, fn := range functions {
		if strings.Contains(fn, "main.") || strings.Contains(fn, "time.") {
			foundFunc = true
			break
		}
	}
	assert.True(t, foundFunc, "should find at least one function name")
}

// TestParseStackTraceEmpty tests parsing empty stack trace.
func TestParseStackTraceEmpty(t *testing.T) {
	functions := ParseStackTrace("")
	assert.Empty(t, functions)
}

// TestDebugInfoString tests DebugInfo string formatting.
func TestDebugInfoString(t *testing.T) {
	info := &DebugInfo{
		GoroutineCount: 42,
		Timestamp:      time.Date(2024, 1, 1, 12, 0, 0, 0, time.UTC),
	}

	s := info.String()
	assert.Contains(t, s, "DebugInfo{")
	assert.Contains(t, s, "Goroutines: 42")
	assert.Contains(t, s, "2024-01-01T12:00:00")
}

// TestGoroutineDumpString tests GoroutineDump string formatting.
func TestGoroutineDumpString(t *testing.T) {
	dump := &GoroutineDump{
		Count:     100,
		Timestamp: time.Date(2024, 1, 1, 12, 0, 0, 0, time.UTC),
	}

	s := dump.String()
	assert.Contains(t, s, "GoroutineDump{")
	assert.Contains(t, s, "Count: 100")
	assert.Contains(t, s, "2024-01-01T12:00:00")
}

// TestProfileResultString tests ProfileResult string formatting.
func TestProfileResultString(t *testing.T) {
	t.Run("success", func(t *testing.T) {
		result := &ProfileResult{
			Type:      ProfileHeap,
			Data:      []byte("test data"),
			Timestamp: time.Date(2024, 1, 1, 12, 0, 0, 0, time.UTC),
		}

		s := result.String()
		assert.Contains(t, s, "ProfileResult{")
		assert.Contains(t, s, "Type: heap")
		assert.Contains(t, s, "Size: 9 bytes")
		assert.Contains(t, s, "2024-01-01T12:00:00")
	})

	t.Run("error", func(t *testing.T) {
		result := &ProfileResult{
			Type:  ProfileCPU,
			Error: assert.AnError,
		}

		s := result.String()
		assert.Contains(t, s, "ProfileResult{")
		assert.Contains(t, s, "Type: cpu")
		assert.Contains(t, s, "Error:")
	})
}

// TestConcurrentDebugAccess tests concurrent access to debug functions.
func TestConcurrentDebugAccess(t *testing.T) {
	var wg sync.WaitGroup

	for i := 0; i < 50; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_ = GetDebugInfo()
			_ = GetStackTrace()
			_ = DumpGoroutines()
		}()
	}

	wg.Wait()
}

// BenchmarkGetStackTrace benchmarks GetStackTrace.
func BenchmarkGetStackTrace(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetStackTrace()
	}
}

// BenchmarkGetAllStackTraces benchmarks GetAllStackTraces.
func BenchmarkGetAllStackTraces(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetAllStackTraces()
	}
}

// BenchmarkDumpGoroutines benchmarks DumpGoroutines.
func BenchmarkDumpGoroutines(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = DumpGoroutines()
	}
}

// BenchmarkParseStackTrace benchmarks ParseStackTrace.
func BenchmarkParseStackTrace(b *testing.B) {
	stack := strings.Repeat(`
goroutine 1 [running]:
main.doSomething()
	/path/to/main.go:42 +0x39
main.main()
	/path/to/main.go:20 +0x25
`, 10)

	for i := 0; i < b.N; i++ {
		_ = ParseStackTrace(stack)
	}
}

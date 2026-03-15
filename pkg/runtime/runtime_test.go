// Package runtime provides runtime introspection utilities for the OTLP Go SDK.
package runtime

import (
	"runtime"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestGetInfo tests the GetInfo function.
func TestGetInfo(t *testing.T) {
	t.Run("basic info retrieval", func(t *testing.T) {
		info := GetInfo()
		require.NotNil(t, info)

		// Verify all fields are populated
		assert.NotEmpty(t, info.GoVersion)
		assert.NotEmpty(t, info.Compiler)
		assert.NotEmpty(t, info.GOARCH)
		assert.NotEmpty(t, info.GOOS)
		assert.Greater(t, info.NumCPU, 0)
		assert.GreaterOrEqual(t, info.NumGoroutine, 1)
		assert.GreaterOrEqual(t, info.NumCgoCall, int64(0))
		assert.Greater(t, info.PID, 0)
		assert.False(t, info.StartTime.IsZero())
	})

	t.Run("info is cached", func(t *testing.T) {
		info1 := GetInfo()
		time.Sleep(10 * time.Millisecond)
		info2 := GetInfo()

		// Should return same cached info for static fields
		assert.Equal(t, info1.GoVersion, info2.GoVersion)
		assert.Equal(t, info1.GOARCH, info2.GOARCH)
		assert.Equal(t, info1.GOOS, info2.GOOS)
		assert.Equal(t, info1.PID, info2.PID)
		assert.Equal(t, info1.StartTime, info2.StartTime)
	})

	t.Run("dynamic values updated", func(t *testing.T) {
		info1 := GetInfo()

		// Create some goroutines
		done := make(chan struct{})
		for i := 0; i < 5; i++ {
			go func() {
				<-done
			}()
		}
		time.Sleep(10 * time.Millisecond)

		info2 := GetInfo()
		close(done)

		// Goroutine count should reflect changes
		assert.GreaterOrEqual(t, info2.NumGoroutine, info1.NumGoroutine)
	})
}

// TestGetGOMAXPROCS tests GOMAXPROCS management.
func TestGetGOMAXPROCS(t *testing.T) {
	t.Run("get GOMAXPROCS", func(t *testing.T) {
		info := GetGOMAXPROCS()
		require.NotNil(t, info)

		assert.Greater(t, info.Current, 0)
		assert.Greater(t, info.Default, 0)
		assert.Equal(t, runtime.NumCPU(), info.Default)
		assert.Equal(t, runtime.GOMAXPROCS(0), info.Current)
	})

	t.Run("set GOMAXPROCS", func(t *testing.T) {
		original := runtime.GOMAXPROCS(0)

		// Set to different value
		newVal := original
		if newVal > 1 {
			newVal = original - 1
		} else {
			newVal = original + 1
		}

		prev := SetGOMAXPROCS(newVal)
		assert.Equal(t, original, prev)
		assert.Equal(t, newVal, runtime.GOMAXPROCS(0))

		// Restore original
		SetGOMAXPROCS(original)
		assert.Equal(t, original, runtime.GOMAXPROCS(0))
	})

	t.Run("set GOMAXPROCS with invalid value", func(t *testing.T) {
		original := runtime.GOMAXPROCS(0)

		// Setting to 0 or negative should use NumCPU
		SetGOMAXPROCS(0)
		assert.Equal(t, runtime.NumCPU(), runtime.GOMAXPROCS(0))

		// Restore
		SetGOMAXPROCS(original)
	})
}

// TestGetGOMEMLIMIT tests GOMEMLIMIT management.
func TestGetGOMEMLIMIT(t *testing.T) {
	t.Run("get GOMEMLIMIT", func(t *testing.T) {
		info := GetGOMEMLIMIT()
		require.NotNil(t, info)

		// Should not panic and return valid struct
		assert.GreaterOrEqual(t, info.Current, int64(0))
	})

	t.Run("set GOMEMLIMIT", func(t *testing.T) {
		original := GetGOMEMLIMIT().Current

		// Set to 512 MB
		limit := int64(512 * 1024 * 1024)
		prev := SetGOMEMLIMIT(limit)
		assert.Equal(t, original, prev)

		current := GetGOMEMLIMIT()
		assert.Equal(t, limit, current.Current)
		assert.True(t, current.Enabled)

		// Restore
		SetGOMEMLIMIT(original)
	})

	t.Run("disable GOMEMLIMIT", func(t *testing.T) {
		original := GetGOMEMLIMIT().Current

		// Set a limit first
		SetGOMEMLIMIT(1024 * 1024 * 1024)

		// Disable with 0
		SetGOMEMLIMIT(0)

		info := GetGOMEMLIMIT()
		assert.False(t, info.Enabled)

		// Restore
		SetGOMEMLIMIT(original)
	})
}

// TestSetGOMEMLIMITString tests setting GOMEMLIMIT from string.
func TestSetGOMEMLIMITString(t *testing.T) {
	original := GetGOMEMLIMIT().Current
	defer SetGOMEMLIMIT(original)

	tests := []struct {
		name      string
		input     string
		wantBytes int64
		wantErr   bool
	}{
		{
			name:      "GiB suffix",
			input:     "1GiB",
			wantBytes: 1 << 30,
			wantErr:   false,
		},
		{
			name:      "MiB suffix",
			input:     "512MiB",
			wantBytes: 512 << 20,
			wantErr:   false,
		},
		{
			name:      "KiB suffix",
			input:     "1024KiB",
			wantBytes: 1024 << 10,
			wantErr:   false,
		},
		{
			name:      "M suffix",
			input:     "256M",
			wantBytes: 256 << 20,
			wantErr:   false,
		},
		{
			name:      "plain number",
			input:     "1073741824",
			wantBytes: 1073741824,
			wantErr:   false,
		},
		{
			name:    "empty string",
			input:   "",
			wantErr: true,
		},
		{
			name:    "invalid number",
			input:   "not-a-number",
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Reset to original before each test
			SetGOMEMLIMIT(original)
			
			prev, err := SetGOMEMLIMITString(tt.input)
			if tt.wantErr {
				assert.Error(t, err)
				return
			}
			require.NoError(t, err)
			// Previous value should be the original (reset at start of each test)
			assert.Equal(t, original, prev)

			info := GetGOMEMLIMIT()
			assert.Equal(t, tt.wantBytes, info.Current)
		})
	}
}

// TestParseMemoryLimit tests memory limit string parsing.
func TestParseMemoryLimit(t *testing.T) {
	tests := []struct {
		name    string
		input   string
		want    int64
		wantErr bool
	}{
		{
			name:  "GiB",
			input: "2GiB",
			want:  2 << 30,
		},
		{
			name:  "MiB",
			input: "100MiB",
			want:  100 << 20,
		},
		{
			name:  "KiB",
			input: "1024KiB",
			want:  1024 << 10,
		},
		{
			name:  "GB decimal",
			input: "1GB",
			want:  1e9,
		},
		{
			name:  "MB decimal",
			input: "500MB",
			want:  500e6,
		},
		{
			name:  "single G",
			input: "4G",
			want:  4 << 30,
		},
		{
			name:  "single M",
			input: "256M",
			want:  256 << 20,
		},
		{
			name:  "single K",
			input: "1024K",
			want:  1024 << 10,
		},
		{
			name:    "empty",
			input:   "",
			wantErr: true,
		},
		{
			name:    "invalid",
			input:   "abc",
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := parseMemoryLimit(tt.input)
			if tt.wantErr {
				assert.Error(t, err)
				return
			}
			require.NoError(t, err)
			assert.Equal(t, tt.want, got)
		})
	}
}

// TestGetBuildInfo tests build info retrieval.
func TestGetBuildInfo(t *testing.T) {
	// Build info may not be available in test environment
	info := GetBuildInfo()

	// Should not panic, may be nil in test environment
	if info != nil {
		assert.NotEmpty(t, info.GoVersion)
	}
}

// TestInfoMethods tests Info struct methods.
func TestInfoMethods(t *testing.T) {
	info := GetInfo()

	t.Run("uptime", func(t *testing.T) {
		uptime := info.Uptime()
		assert.GreaterOrEqual(t, uptime, time.Duration(0))
	})

	t.Run("string", func(t *testing.T) {
		s := info.String()
		assert.Contains(t, s, info.GoVersion)
		assert.Contains(t, s, info.GOOS)
		assert.Contains(t, s, info.GOARCH)
		assert.Contains(t, s, "PID")
	})
}

// TestGOMAXPROCSInfoString tests GOMAXPROCSInfo string representation.
func TestGOMAXPROCSInfoString(t *testing.T) {
	info := &GOMAXPROCSInfo{
		Current:          8,
		Default:          16,
		FromAutomaxprocs: false,
	}

	s := info.String()
	assert.Contains(t, s, "GOMAXPROCS=8")
	assert.Contains(t, s, "default=16")
	assert.Contains(t, s, "manual")
}

// TestGOMEMLIMITInfoString tests GOMEMLIMITInfo string representation.
func TestGOMEMLIMITInfoString(t *testing.T) {
	t.Run("enabled", func(t *testing.T) {
		info := &GOMEMLIMITInfo{
			Current: 1073741824,
			Enabled: true,
			Source:  "env",
		}

		s := info.String()
		assert.Contains(t, s, "GOMEMLIMIT=1073741824")
		assert.Contains(t, s, "env")
	})

	t.Run("disabled", func(t *testing.T) {
		info := &GOMEMLIMITInfo{
			Current: 0,
			Enabled: false,
		}

		s := info.String()
		assert.Contains(t, s, "GOMEMLIMIT=disabled")
	})
}

// TestFormatBytes tests byte formatting.
func TestFormatBytes(t *testing.T) {
	tests := []struct {
		bytes uint64
		want  string
	}{
		{0, "0 B"},
		{512, "512 B"},
		{1024, "1.00 KB"},
		{1536, "1.50 KB"},
		{1024 * 1024, "1.00 MB"},
		{1024 * 1024 * 1024, "1.00 GB"},
		{2 * 1024 * 1024 * 1024, "2.00 GB"},
		{uint64(1024) * 1024 * 1024 * 1024, "1.00 TB"},
	}

	for _, tt := range tests {
		t.Run(tt.want, func(t *testing.T) {
			got := FormatBytes(tt.bytes)
			assert.Equal(t, tt.want, got)
		})
	}
}

// TestReadMemStatsWithAlloc tests reading memory stats with allocation.
func TestReadMemStatsWithAlloc(t *testing.T) {
	// Allocate some memory
	data := make([]byte, 1024*1024) // 1MB
	_ = data

	stats := ReadMemStatsWithAlloc()
	require.NotNil(t, stats)
	assert.Greater(t, stats.Alloc, uint64(0))
	assert.Greater(t, stats.HeapAlloc, uint64(0))
}

// BenchmarkGetInfo benchmarks GetInfo.
func BenchmarkGetInfo(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetInfo()
	}
}

// BenchmarkGetGOMAXPROCS benchmarks GetGOMAXPROCS.
func BenchmarkGetGOMAXPROCS(b *testing.B) {
	for i := 0; i < b.N; i++ {
		_ = GetGOMAXPROCS()
	}
}

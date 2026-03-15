// Package runtime provides runtime introspection utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Go version detection
//   - Memory statistics
//   - GC metrics
//   - Goroutine monitoring
//   - GOMAXPROCS/GOMEMLIMIT management
//   - OpenTelemetry Resource integration
//
// Example usage:
//
//	stats := runtime.GetMemStats()
//	fmt.Printf("Alloc: %d MB\n", stats.Alloc/1024/1024)
//
//	// Get runtime info for OpenTelemetry Resource
//	info := runtime.GetInfo()
//	resource := runtime.ToResource(info)
package runtime

import (
	"fmt"
	"os"
	"runtime"
	"runtime/debug"
	"strconv"
	"sync"
	"time"
)

// Info holds comprehensive Go runtime information.
type Info struct {
	// GoVersion is the Go version (e.g., "go1.26")
	GoVersion string

	// Compiler is the compiler toolchain (e.g., "gc")
	Compiler string

	// GOARCH is the target architecture (e.g., "amd64")
	GOARCH string

	// GOOS is the target operating system (e.g., "linux")
	GOOS string

	// NumCPU is the number of logical CPUs available
	NumCPU int

	// NumGoroutine is the current number of goroutines
	NumGoroutine int

	// NumCgoCall returns the number of cgo calls made by the current process
	NumCgoCall int64

	// PID is the process ID
	PID int

	// StartTime is when the runtime info was first captured
	StartTime time.Time
}

// GOMAXPROCSInfo holds GOMAXPROCS configuration information.
type GOMAXPROCSInfo struct {
	// Current is the current GOMAXPROCS value
	Current int

	// Default is the default value (number of CPUs)
	Default int

	// FromAutomaxprocs indicates if set by automaxprocs
	FromAutomaxprocs bool
}

// GOMEMLIMITInfo holds GOMEMLIMIT configuration information.
type GOMEMLIMITInfo struct {
	// Current is the current memory limit in bytes
	Current int64

	// Enabled indicates if memory limit is set (> 0)
	Enabled bool

	// Source indicates how the limit was set ("env", "runtime", "default")
	Source string
}

// BuildInfo holds build information about the binary.
type BuildInfo struct {
	// Path is the main package path
	Path string

	// Main version
	Version string

	// Revision is the VCS revision
	Revision string

	// Time is the build time
	Time string

	// Modified indicates if there were uncommitted changes
	Modified bool

	// GoVersion used to build the binary
	GoVersion string
}

var (
	infoOnce        sync.Once
	cachedInfo      *Info
	buildInfoOnce   sync.Once
	cachedBuildInfo *BuildInfo
)

// GetInfo returns comprehensive runtime information.
// The result is cached after the first call.
func GetInfo() *Info {
	infoOnce.Do(func() {
		cachedInfo = &Info{
			GoVersion:    runtime.Version(),
			Compiler:     runtime.Compiler,
			GOARCH:       runtime.GOARCH,
			GOOS:         runtime.GOOS,
			NumCPU:       runtime.NumCPU(),
			NumGoroutine: runtime.NumGoroutine(),
			NumCgoCall:   runtime.NumCgoCall(),
			PID:          os.Getpid(),
			StartTime:    time.Now(),
		}
	})

	// Update dynamic values
	info := *cachedInfo
	info.NumGoroutine = runtime.NumGoroutine()
	info.NumCgoCall = runtime.NumCgoCall()
	return &info
}

// GetGOMAXPROCS returns GOMAXPROCS configuration.
func GetGOMAXPROCS() *GOMAXPROCSInfo {
	current := runtime.GOMAXPROCS(0)
	defaultProcs := runtime.NumCPU()

	return &GOMAXPROCSInfo{
		Current:          current,
		Default:          defaultProcs,
		FromAutomaxprocs: os.Getenv("GOMAXPROCS") == "" && current != defaultProcs,
	}
}

// SetGOMAXPROCS sets the GOMAXPROCS value.
// Returns the previous value.
func SetGOMAXPROCS(n int) int {
	if n <= 0 {
		n = runtime.NumCPU()
	}
	return runtime.GOMAXPROCS(n)
}

// GetGOMEMLIMIT returns GOMEMLIMIT configuration.
func GetGOMEMLIMIT() *GOMEMLIMITInfo {
	limit := debug.SetMemoryLimit(-1)

	source := "default"
	if envLimit := os.Getenv("GOMEMLIMIT"); envLimit != "" {
		source = "env"
	} else if limit > 0 {
		source = "runtime"
	}

	return &GOMEMLIMITInfo{
		Current: limit,
		Enabled: limit > 0 && limit < (1<<63-1),
		Source:  source,
	}
}

// SetGOMEMLIMIT sets the memory limit in bytes.
// Returns the previous limit. Use 0 to disable limit.
func SetGOMEMLIMIT(limit int64) int64 {
	if limit < 0 {
		limit = 0
	}
	return debug.SetMemoryLimit(limit)
}

// SetGOMEMLIMITString sets the memory limit from a string (supports units like "1GiB", "100MiB").
// Returns the limit in bytes or error if parsing fails.
func SetGOMEMLIMITString(s string) (int64, error) {
	limit, err := parseMemoryLimit(s)
	if err != nil {
		return 0, err
	}
	return debug.SetMemoryLimit(limit), nil
}

// parseMemoryLimit parses memory limit string (e.g., "1GiB", "100MiB", "1024KiB").
func parseMemoryLimit(s string) (int64, error) {
	if s == "" {
		return 0, fmt.Errorf("empty memory limit")
	}

	// Simple parsing: handle common suffixes
	var multiplier int64 = 1
	numStr := s

	switch {
	case len(s) > 3 && (s[len(s)-3:] == "GiB" || s[len(s)-3:] == "gib"):
		multiplier = 1 << 30
		numStr = s[:len(s)-3]
	case len(s) > 3 && (s[len(s)-3:] == "MiB" || s[len(s)-3:] == "mib"):
		multiplier = 1 << 20
		numStr = s[:len(s)-3]
	case len(s) > 3 && (s[len(s)-3:] == "KiB" || s[len(s)-3:] == "kib"):
		multiplier = 1 << 10
		numStr = s[:len(s)-3]
	case len(s) > 2 && (s[len(s)-2:] == "GB" || s[len(s)-2:] == "gb"):
		multiplier = 1e9
		numStr = s[:len(s)-2]
	case len(s) > 2 && (s[len(s)-2:] == "MB" || s[len(s)-2:] == "mb"):
		multiplier = 1e6
		numStr = s[:len(s)-2]
	case len(s) > 2 && (s[len(s)-2:] == "KB" || s[len(s)-2:] == "kb"):
		multiplier = 1e3
		numStr = s[:len(s)-2]
	case len(s) > 1 && (s[len(s)-1:] == "G" || s[len(s)-1:] == "g"):
		multiplier = 1 << 30
		numStr = s[:len(s)-1]
	case len(s) > 1 && (s[len(s)-1:] == "M" || s[len(s)-1:] == "m"):
		multiplier = 1 << 20
		numStr = s[:len(s)-1]
	case len(s) > 1 && (s[len(s)-1:] == "K" || s[len(s)-1:] == "k"):
		multiplier = 1 << 10
		numStr = s[:len(s)-1]
	}

	num, err := strconv.ParseInt(numStr, 10, 64)
	if err != nil {
		return 0, fmt.Errorf("invalid memory limit: %w", err)
	}

	return num * multiplier, nil
}

// GetBuildInfo returns build information about the binary.
// Returns nil if build info is not available.
func GetBuildInfo() *BuildInfo {
	buildInfoOnce.Do(func() {
		info, ok := debug.ReadBuildInfo()
		if !ok {
			return
		}

		cachedBuildInfo = &BuildInfo{
			Path:      info.Path,
			Version:   info.Main.Version,
			GoVersion: info.GoVersion,
		}

		// Extract VCS info from settings
		for _, setting := range info.Settings {
			switch setting.Key {
			case "vcs.revision":
				cachedBuildInfo.Revision = setting.Value
			case "vcs.time":
				cachedBuildInfo.Time = setting.Value
			case "vcs.modified":
				cachedBuildInfo.Modified = setting.Value == "true"
			}
		}
	})

	return cachedBuildInfo
}

// Uptime returns the duration since the runtime info was first captured.
func (i *Info) Uptime() time.Duration {
	return time.Since(i.StartTime)
}

// String returns a string representation of Info.
func (i *Info) String() string {
	return fmt.Sprintf("Go %s %s/%s (PID: %d, Goroutines: %d, CPUs: %d)",
		i.GoVersion, i.GOOS, i.GOARCH, i.PID, i.NumGoroutine, i.NumCPU)
}

// String returns a string representation of GOMAXPROCSInfo.
func (g *GOMAXPROCSInfo) String() string {
	source := "manual"
	if g.FromAutomaxprocs {
		source = "automaxprocs"
	}
	return fmt.Sprintf("GOMAXPROCS=%d (default=%d, source=%s)", g.Current, g.Default, source)
}

// String returns a string representation of GOMEMLIMITInfo.
func (g *GOMEMLIMITInfo) String() string {
	if !g.Enabled {
		return "GOMEMLIMIT=disabled"
	}
	return fmt.Sprintf("GOMEMLIMIT=%d (%s)", g.Current, g.Source)
}

// FormatBytes formats bytes to human-readable string.
func FormatBytes(bytes uint64) string {
	const (
		KB = 1024
		MB = KB * 1024
		GB = MB * 1024
		TB = GB * 1024
	)

	switch {
	case bytes >= TB:
		return fmt.Sprintf("%.2f TB", float64(bytes)/TB)
	case bytes >= GB:
		return fmt.Sprintf("%.2f GB", float64(bytes)/GB)
	case bytes >= MB:
		return fmt.Sprintf("%.2f MB", float64(bytes)/MB)
	case bytes >= KB:
		return fmt.Sprintf("%.2f KB", float64(bytes)/KB)
	default:
		return fmt.Sprintf("%d B", bytes)
	}
}

// ReadMemStatsWithAlloc triggers GC and reads memory stats.
// This is useful when you need accurate memory accounting.
func ReadMemStatsWithAlloc() *MemStats {
	runtime.GC()
	runtime.Gosched()
	return GetMemStats()
}

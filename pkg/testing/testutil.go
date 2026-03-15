// Package testing provides testing utilities for the OTLP Go SDK.
//
// This package includes:
//   - Test span exporters
//   - In-memory metric readers
//   - Trace validation helpers
//   - Test resource fixtures
//   - Temporary file/directory management
//   - Test timeout controls
//   - Parallel test support
//
// Example usage:
//
//	// Create test exporter
//	exporter := testing.NewTestExporter()
//	tp := sdktrace.NewTracerProvider(
//	    sdktrace.WithSyncer(exporter),
//	)
//
//	// Run code...
//
//	spans := exporter.GetSpans()
//	testing.AssertSpanCount(t, spans, 1)
package testing

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"
)

// TempDir creates a temporary directory for testing and returns its path.
// The directory is automatically cleaned up when the test completes.
func TempDir(t testing.TB) string {
	t.Helper()
	dir, err := os.MkdirTemp("", fmt.Sprintf("%s_*", t.Name()))
	if err != nil {
		t.Fatalf("Failed to create temp directory: %v", err)
	}
	t.Cleanup(func() {
		if err := os.RemoveAll(dir); err != nil {
			t.Logf("Warning: failed to remove temp directory %s: %v", dir, err)
		}
	})
	return dir
}

// TempFile creates a temporary file with the given content and returns its path.
// The file is automatically cleaned up when the test completes.
func TempFile(t testing.TB, pattern string, content []byte) string {
	t.Helper()
	file, err := os.CreateTemp("", pattern)
	if err != nil {
		t.Fatalf("Failed to create temp file: %v", err)
	}
	defer file.Close()

	if len(content) > 0 {
		if _, err := file.Write(content); err != nil {
			t.Fatalf("Failed to write to temp file: %v", err)
		}
	}

	path := file.Name()
	t.Cleanup(func() {
		if err := os.Remove(path); err != nil && !os.IsNotExist(err) {
			t.Logf("Warning: failed to remove temp file %s: %v", path, err)
		}
	})
	return path
}

// WithTimeout runs a test function with a timeout.
// If the function does not complete within the timeout, the test fails.
func WithTimeout(t testing.TB, timeout time.Duration, fn func(ctx context.Context)) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	done := make(chan struct{})
	go func() {
		defer close(done)
		fn(ctx)
	}()

	select {
	case <-done:
		// Test completed successfully
	case <-ctx.Done():
		t.Fatalf("Test timed out after %v", timeout)
	}
}

// RunParallel runs the test function in parallel with multiple goroutines.
// This is useful for testing concurrent access patterns.
func RunParallel(t testing.TB, count int, fn func(i int)) {
	t.Helper()
	var wg sync.WaitGroup
	wg.Add(count)

	for i := 0; i < count; i++ {
		go func(index int) {
			defer wg.Done()
			fn(index)
		}(i)
	}

	wg.Wait()
}

// BenchmarkWithIterations runs a benchmark with a fixed number of iterations.
// This is useful for consistent performance comparisons.
func BenchmarkWithIterations(b *testing.B, iterations int, fn func()) {
	b.Helper()
	b.ResetTimer()
	for i := 0; i < iterations; i++ {
		fn()
	}
	b.ReportMetric(float64(iterations*b.N)/b.Elapsed().Seconds(), "ops/sec")
}

// SkipIfShort skips the test if running in short mode.
func SkipIfShort(t testing.TB) {
	t.Helper()
	if testing.Short() {
		t.Skip("Skipping test in short mode")
	}
}

// SkipIfRace skips the test if running with race detector.
func SkipIfRace(t testing.TB) {
	t.Helper()
	if isRaceDetectorEnabled() {
		t.Skip("Skipping test with race detector")
	}
}

// RequireEnv skips the test if the specified environment variable is not set.
func RequireEnv(t testing.TB, key string) string {
	t.Helper()
	value := os.Getenv(key)
	if value == "" {
		t.Skipf("Skipping test: %s environment variable not set", key)
	}
	return value
}

// CaptureOutput captures stdout and stderr during the execution of fn.
// Returns the captured output as strings.
func CaptureOutput(t testing.TB, fn func()) (stdout, stderr string) {
	t.Helper()

	// Create pipes for stdout and stderr
	oldStdout := os.Stdout
	oldStderr := os.Stderr
	rStdout, wStdout, err := os.Pipe()
	if err != nil {
		t.Fatalf("Failed to create stdout pipe: %v", err)
	}
	rStderr, wStderr, err := os.Pipe()
	if err != nil {
		t.Fatalf("Failed to create stderr pipe: %v", err)
	}

	os.Stdout = wStdout
	os.Stderr = wStderr

	// Run the function
	fn()

	// Close writers and restore stdout/stderr
	wStdout.Close()
	wStderr.Close()
	os.Stdout = oldStdout
	os.Stderr = oldStderr

	// Read captured output
	var outBuf, errBuf strings.Builder
	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		buf := make([]byte, 1024)
		for {
			n, err := rStdout.Read(buf)
			if n > 0 {
				outBuf.Write(buf[:n])
			}
			if err != nil {
				break
			}
		}
	}()

	go func() {
		defer wg.Done()
		buf := make([]byte, 1024)
		for {
			n, err := rStderr.Read(buf)
			if n > 0 {
				errBuf.Write(buf[:n])
			}
			if err != nil {
				break
			}
		}
	}()

	wg.Wait()
	rStdout.Close()
	rStderr.Close()

	return outBuf.String(), errBuf.String()
}

// Eventually asserts that a condition becomes true within the specified timeout.
// It polls the condition at regular intervals.
func Eventually(t testing.TB, condition func() bool, timeout, interval time.Duration, msgAndArgs ...interface{}) bool {
	t.Helper()

	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if condition() {
			return true
		}
		time.Sleep(interval)
	}

	t.Fatalf("Condition never became true within %v: %s", timeout, formatMessage(msgAndArgs...))
	return false
}

// Never asserts that a condition never becomes true within the specified duration.
func Never(t testing.TB, condition func() bool, duration, interval time.Duration, msgAndArgs ...interface{}) bool {
	t.Helper()

	deadline := time.Now().Add(duration)
	for time.Now().Before(deadline) {
		if condition() {
			t.Fatalf("Condition became true unexpectedly within %v: %s", duration, formatMessage(msgAndArgs...))
			return false
		}
		time.Sleep(interval)
	}

	return true
}

// WaitFor asserts that a channel receives a value within the specified timeout.
func WaitFor[T any](t testing.TB, ch <-chan T, timeout time.Duration, msgAndArgs ...interface{}) (T, bool) {
	t.Helper()

	var zero T
	select {
	case val := <-ch:
		return val, true
	case <-time.After(timeout):
		t.Fatalf("Timed out waiting for channel value after %v: %s", timeout, formatMessage(msgAndArgs...))
		return zero, false
	}
}

// MustNotTimeout ensures that a context does not timeout during the execution of fn.
func MustNotTimeout(t testing.TB, ctx context.Context, fn func() error, msgAndArgs ...interface{}) {
	t.Helper()

	errChan := make(chan error, 1)
	go func() {
		errChan <- fn()
	}()

	select {
	case err := <-errChan:
		if err != nil {
			t.Fatalf("Function returned error: %v", err)
		}
	case <-ctx.Done():
		t.Fatalf("Context timed out: %s", formatMessage(msgAndArgs...))
	}
}

// GetProjectRoot returns the absolute path to the project root directory.
// This is useful for finding test data files relative to the project root.
func GetProjectRoot(t testing.TB) string {
	t.Helper()

	_, filename, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("Failed to get caller information")
	}

	// Walk up the directory tree to find the project root
	// (directory containing go.mod)
	dir := filepath.Dir(filename)
	for {
		goModPath := filepath.Join(dir, "go.mod")
		if _, err := os.Stat(goModPath); err == nil {
			// Check if this is the root go.mod (module name should be OTLP_go)
			content, err := os.ReadFile(goModPath)
			if err == nil && strings.Contains(string(content), "module OTLP_go") {
				return dir
			}
		}

		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatal("Could not find project root")
		}
		dir = parent
	}
}

// JoinPath joins path elements relative to the project root.
func JoinPath(t testing.TB, elems ...string) string {
	t.Helper()
	return filepath.Join(GetProjectRoot(t), filepath.Join(elems...))
}

// Repeat runs the given function n times and returns any errors encountered.
func Repeat(t testing.TB, n int, fn func(i int) error) {
	t.Helper()
	for i := 0; i < n; i++ {
		if err := fn(i); err != nil {
			t.Fatalf("Iteration %d failed: %v", i, err)
		}
	}
}

// ParallelTest runs tests in parallel with a limit on concurrent executions.
func ParallelTest(t testing.TB, count, concurrency int, fn func(t *testing.T, i int)) {
	t.Helper()

	semaphore := make(chan struct{}, concurrency)
	var wg sync.WaitGroup

	for i := 0; i < count; i++ {
		wg.Add(1)
		go func(index int) {
			defer wg.Done()
			semaphore <- struct{}{}
			defer func() { <-semaphore }()

			// Create a subtest
			tName := fmt.Sprintf("Parallel_%d", index)
			if tt, ok := t.(*testing.T); ok {
				tt.Run(tName, func(t *testing.T) {
					fn(t, index)
				})
			}
		}(i)
	}

	wg.Wait()
}

// formatMessage formats a message with optional arguments.
func formatMessage(msgAndArgs ...interface{}) string {
	if len(msgAndArgs) == 0 {
		return ""
	}
	if len(msgAndArgs) == 1 {
		if msg, ok := msgAndArgs[0].(string); ok {
			return msg
		}
		return fmt.Sprintf("%v", msgAndArgs[0])
	}
	return fmt.Sprintf(msgAndArgs[0].(string), msgAndArgs[1:]...)
}

// isRaceDetectorEnabled returns true if the race detector is enabled.
func isRaceDetectorEnabled() bool {
	// This is a simple heuristic: if the race build tag is set,
	// the race detector is enabled. We check this by looking at
	// the build info, but a simpler approach is to use a known
	// race-detection specific behavior.
	return strings.Contains(os.Getenv("GOFLAGS"), "-race")
}

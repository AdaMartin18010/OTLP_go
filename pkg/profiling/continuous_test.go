package profiling

import (
	"context"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"
)

func TestDefaultContinuousProfilerConfig(t *testing.T) {
	config := DefaultContinuousProfilerConfig()

	if config == nil {
		t.Fatal("expected non-nil config")
	}

	if !config.Enabled {
		t.Error("expected Enabled to be true")
	}

	if config.Interval != 60*time.Second {
		t.Errorf("expected Interval 60s, got %v", config.Interval)
	}

	if config.Duration != 10*time.Second {
		t.Errorf("expected Duration 10s, got %v", config.Duration)
	}

	if config.OutputDir != "./profiles/continuous" {
		t.Errorf("expected OutputDir './profiles/continuous', got %s", config.OutputDir)
	}

	if config.MaxAge != 7*24*time.Hour {
		t.Errorf("expected MaxAge 7 days, got %v", config.MaxAge)
	}

	if len(config.ProfileTypes) != 2 {
		t.Errorf("expected 2 profile types, got %d", len(config.ProfileTypes))
	}
}

func TestNewContinuousProfiler(t *testing.T) {
	config := DefaultContinuousProfilerConfig()
	profiler := NewContinuousProfiler(config)

	if profiler == nil {
		t.Fatal("expected non-nil profiler")
	}

	if profiler.config != config {
		t.Error("expected profiler to use provided config")
	}

	if profiler.pprofMgr == nil {
		t.Error("expected pprofMgr to be initialized")
	}

	if profiler.profileTimes == nil {
		t.Error("expected profileTimes to be initialized")
	}
}

func TestNewContinuousProfilerWithNilConfig(t *testing.T) {
	profiler := NewContinuousProfiler(nil)

	if profiler == nil {
		t.Fatal("expected non-nil profiler")
	}

	if profiler.config == nil {
		t.Fatal("expected default config to be set")
	}
}

func TestContinuousProfilerStartStop(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	err := profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	if !profiler.IsRunning() {
		t.Error("expected profiler to be running")
	}

	// 等待一段时间让剖析执行
	time.Sleep(200 * time.Millisecond)

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}

	if profiler.IsRunning() {
		t.Error("expected profiler to be stopped")
	}
}

func TestContinuousProfilerStartAlreadyRunning(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     1 * time.Second,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	err := profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}
	defer profiler.Stop()

	// 尝试再次启动
	err = profiler.Start()
	if err == nil {
		t.Error("expected error when starting already running profiler")
	}
}

func TestContinuousProfilerStartDisabled(t *testing.T) {
	config := &ContinuousProfilerConfig{
		Enabled: false,
	}

	profiler := NewContinuousProfiler(config)

	err := profiler.Start()
	if err == nil {
		t.Error("expected error when starting disabled profiler")
	}
}

func TestContinuousProfilerStopNotRunning(t *testing.T) {
	profiler := NewContinuousProfiler(nil)

	err := profiler.Stop()
	if err == nil {
		t.Error("expected error when stopping profiler that is not running")
	}
}

func TestContinuousProfilerCallbacks(t *testing.T) {
	tempDir := t.TempDir()
	var profileCount int
	var mu sync.Mutex
	var errors []error

	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
		OnProfile: func(result *PProfResult) {
			mu.Lock()
			profileCount++
			mu.Unlock()
		},
		OnError: func(err error) {
			mu.Lock()
			errors = append(errors, err)
			mu.Unlock()
		},
	}

	profiler := NewContinuousProfiler(config)

	err := profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	// 等待剖析执行
	time.Sleep(300 * time.Millisecond)

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}

	mu.Lock()
	count := profileCount
	mu.Unlock()

	if count == 0 {
		t.Error("expected at least one profile to be captured")
	}
}

func TestContinuousProfilerGetLastProfileTime(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	// 开始前应该返回零时间
	if !profiler.GetLastProfileTime(ContinuousMemory).IsZero() {
		t.Error("expected zero time before start")
	}

	err := profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	// 等待剖析执行
	time.Sleep(200 * time.Millisecond)

	lastTime := profiler.GetLastProfileTime(ContinuousMemory)
	if lastTime.IsZero() {
		t.Error("expected non-zero time after profile capture")
	}

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}
}

func TestContinuousProfilerGetProfileFiles(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	// 开始时应该没有文件
	files, err := profiler.GetProfileFiles()
	if err != nil {
		t.Fatalf("failed to get profile files: %v", err)
	}

	if len(files) != 0 {
		t.Errorf("expected 0 files before start, got %d", len(files))
	}

	err = profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	// 等待剖析执行
	time.Sleep(200 * time.Millisecond)

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}

	// 停止后应该有一些文件
	files, err = profiler.GetProfileFiles()
	if err != nil {
		t.Fatalf("failed to get profile files: %v", err)
	}

	if len(files) == 0 {
		t.Error("expected some profile files after stop")
	}
}

func TestContinuousProfilerGetStats(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	stats, err := profiler.GetStats()
	if err != nil {
		t.Fatalf("failed to get stats: %v", err)
	}

	if stats == nil {
		t.Fatal("expected non-nil stats")
	}

	if stats["running"].(bool) {
		t.Error("expected running to be false before start")
	}

	err = profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	stats, err = profiler.GetStats()
	if err != nil {
		t.Fatalf("failed to get stats: %v", err)
	}

	if !stats["running"].(bool) {
		t.Error("expected running to be true after start")
	}

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}
}

func TestStartContinuousProfiler(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler, err := StartContinuousProfiler(config)
	if err != nil {
		t.Fatalf("failed to start continuous profiler: %v", err)
	}

	if profiler == nil {
		t.Fatal("expected non-nil profiler")
	}

	if !profiler.IsRunning() {
		t.Error("expected profiler to be running")
	}

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}
}

func TestStartWithContext(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     100 * time.Millisecond,
		Duration:     50 * time.Millisecond,
		OutputDir:    tempDir,
	}

	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()

	profiler, err := StartWithContext(ctx, config)
	if err != nil {
		t.Fatalf("failed to start continuous profiler with context: %v", err)
	}

	if profiler == nil {
		t.Fatal("expected non-nil profiler")
	}

	// 等待上下文取消
	<-ctx.Done()
	time.Sleep(100 * time.Millisecond) // 给 goroutine 一点时间处理
}

func TestCleanupOldProfiles(t *testing.T) {
	tempDir := t.TempDir()

	// 创建一些旧文件
	oldFile := filepath.Join(tempDir, "old.prof")
	newFile := filepath.Join(tempDir, "new.prof")

	if err := os.WriteFile(oldFile, []byte("old"), 0644); err != nil {
		t.Fatalf("failed to create old file: %v", err)
	}

	if err := os.WriteFile(newFile, []byte("new"), 0644); err != nil {
		t.Fatalf("failed to create new file: %v", err)
	}

	// 修改旧文件的修改时间
	oldTime := time.Now().Add(-30 * 24 * time.Hour) // 30 天前
	if err := os.Chtimes(oldFile, oldTime, oldTime); err != nil {
		t.Fatalf("failed to change file time: %v", err)
	}

	config := &ContinuousProfilerConfig{
		Enabled:   true,
		OutputDir: tempDir,
		MaxAge:    7 * 24 * time.Hour, // 7 天
		MaxSize:   1024 * 1024 * 1024, // 1GB
	}

	profiler := NewContinuousProfiler(config)

	// 手动执行清理
	if err := profiler.cleanupOldProfiles(); err != nil {
		t.Fatalf("failed to cleanup old profiles: %v", err)
	}

	// 旧文件应该被删除
	if _, err := os.Stat(oldFile); !os.IsNotExist(err) {
		t.Error("expected old file to be deleted")
	}

	// 新文件应该还在
	if _, err := os.Stat(newFile); os.IsNotExist(err) {
		t.Error("expected new file to still exist")
	}
}

func TestRemoveOldestFiles(t *testing.T) {
	tempDir := t.TempDir()

	// 创建一些文件
	files := []string{
		"oldest.prof",
		"middle.prof",
		"newest.prof",
	}

	for _, name := range files {
		path := filepath.Join(tempDir, name)
		if err := os.WriteFile(path, []byte(name), 0644); err != nil {
			t.Fatalf("failed to create file: %v", err)
		}
	}

	// 设置不同的修改时间
	times := []time.Time{
		time.Now().Add(-3 * time.Hour),
		time.Now().Add(-2 * time.Hour),
		time.Now().Add(-1 * time.Hour),
	}

	for i, name := range files {
		path := filepath.Join(tempDir, name)
		if err := os.Chtimes(path, times[i], times[i]); err != nil {
			t.Fatalf("failed to change file time: %v", err)
		}
	}

	config := &ContinuousProfilerConfig{
		OutputDir: tempDir,
	}

	profiler := NewContinuousProfiler(config)

	// 删除最旧的文件
	if err := profiler.removeOldestFiles(100); err != nil {
		t.Fatalf("failed to remove oldest files: %v", err)
	}

	// 最旧的文件应该被删除
	oldestPath := filepath.Join(tempDir, "oldest.prof")
	if _, err := os.Stat(oldestPath); !os.IsNotExist(err) {
		t.Error("expected oldest file to be deleted")
	}
}

func TestContinuousProfilerWithCPUProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousCPU},
		Interval:     200 * time.Millisecond,
		Duration:     100 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	err := profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	// 等待 CPU 剖析执行
	time.Sleep(400 * time.Millisecond)

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}

	// 检查是否有 CPU 剖析文件
	files, err := profiler.GetProfileFiles()
	if err != nil {
		t.Fatalf("failed to get profile files: %v", err)
	}

	hasCPUProfile := false
	for _, f := range files {
		if filepath.Base(f)[:4] == "cpu_" {
			hasCPUProfile = true
			break
		}
	}

	if !hasCPUProfile {
		t.Error("expected at least one CPU profile file")
	}
}

func TestContinuousProfilerWithGoroutineProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousGoroutine},
		Interval:     100 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	err := profiler.Start()
	if err != nil {
		t.Fatalf("failed to start profiler: %v", err)
	}

	// 等待 Goroutine 剖析执行
	time.Sleep(300 * time.Millisecond)

	err = profiler.Stop()
	if err != nil {
		t.Fatalf("failed to stop profiler: %v", err)
	}

	// 检查是否有 Goroutine 剖析文件
	files, err := profiler.GetProfileFiles()
	if err != nil {
		t.Fatalf("failed to get profile files: %v", err)
	}

	hasGoroutineProfile := false
	for _, f := range files {
		if len(filepath.Base(f)) >= 10 && filepath.Base(f)[:10] == "goroutine_" {
			hasGoroutineProfile = true
			break
		}
	}

	if !hasGoroutineProfile {
		t.Error("expected at least one Goroutine profile file")
	}
}

func TestContinuousProfilerConcurrency(t *testing.T) {
	tempDir := t.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     50 * time.Millisecond,
		Duration:     25 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	// 并发启动和停止
	var wg sync.WaitGroup
	for i := 0; i < 5; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			profiler.Start()
		}()
	}
	wg.Wait()

	if !profiler.IsRunning() {
		t.Error("expected profiler to be running")
	}

	time.Sleep(150 * time.Millisecond)

	for i := 0; i < 5; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			profiler.Stop()
		}()
	}
	wg.Wait()
}

func BenchmarkContinuousProfiler(b *testing.B) {
	tempDir := b.TempDir()
	config := &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousMemory},
		Interval:     10 * time.Millisecond,
		Duration:     5 * time.Millisecond,
		OutputDir:    tempDir,
	}

	profiler := NewContinuousProfiler(config)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		profiler.Start()
		time.Sleep(20 * time.Millisecond)
		profiler.Stop()
	}
}

func TestHandleError(t *testing.T) {
	var capturedError error
	var mu sync.Mutex

	config := &ContinuousProfilerConfig{
		Enabled: true,
		OnError: func(err error) {
			mu.Lock()
			capturedError = err
			mu.Unlock()
		},
	}

	profiler := NewContinuousProfiler(config)

	testError := os.ErrInvalid
	profiler.handleError(testError)

	mu.Lock()
	if capturedError != testError {
		t.Error("expected error to be captured")
	}
	mu.Unlock()
}

func TestHandleErrorNilCallback(t *testing.T) {
	config := &ContinuousProfilerConfig{
		Enabled: true,
		OnError: nil,
	}

	profiler := NewContinuousProfiler(config)

	// 不应该 panic
	profiler.handleError(os.ErrInvalid)
}

func TestContinuousProfilerMaxSize(t *testing.T) {
	tempDir := t.TempDir()

	// 创建一些文件
	for i := 0; i < 5; i++ {
		path := filepath.Join(tempDir, "profile_"+string(rune('a'+i))+".prof")
		if err := os.WriteFile(path, []byte("test data for profile"), 0644); err != nil {
			t.Fatalf("failed to create file: %v", err)
		}
		// 设置不同的修改时间
		modTime := time.Now().Add(-time.Duration(5-i) * time.Hour)
		if err := os.Chtimes(path, modTime, modTime); err != nil {
			t.Fatalf("failed to change file time: %v", err)
		}
	}

	config := &ContinuousProfilerConfig{
		Enabled:   true,
		OutputDir: tempDir,
		MaxSize:   50, // 很小的限制，确保会触发清理
	}

	profiler := NewContinuousProfiler(config)

	// 执行清理
	if err := profiler.cleanupOldProfiles(); err != nil {
		t.Fatalf("failed to cleanup profiles: %v", err)
	}

	// 验证文件被清理
	entries, err := os.ReadDir(tempDir)
	if err != nil {
		t.Fatalf("failed to read directory: %v", err)
	}

	// 应该只剩下一些文件
	if len(entries) >= 5 {
		t.Error("expected some files to be deleted")
	}
}

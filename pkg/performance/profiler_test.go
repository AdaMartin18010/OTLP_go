package performance

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestDefaultProfilerConfig(t *testing.T) {
	config := DefaultProfilerConfig()
	if config == nil {
		t.Fatal("config should not be nil")
	}
	if config.CPUProfileRate != 100 {
		t.Errorf("CPUProfileRate = %d, want 100", config.CPUProfileRate)
	}
	if config.MemProfileRate != 0 {
		t.Errorf("MemProfileRate = %d, want 0", config.MemProfileRate)
	}
	if config.BlockProfileRate != 0 {
		t.Errorf("BlockProfileRate = %d, want 0", config.BlockProfileRate)
	}
	if config.MutexProfileFraction != 0 {
		t.Errorf("MutexProfileFraction = %d, want 0", config.MutexProfileFraction)
	}
	if config.OutputDir != "./profiles" {
		t.Errorf("OutputDir = %s, want ./profiles", config.OutputDir)
	}
	if config.Duration != 30*time.Second {
		t.Errorf("Duration = %v, want 30s", config.Duration)
	}
}

func TestNewProfiler(t *testing.T) {
	config := DefaultProfilerConfig()
	profiler := NewProfiler(config)
	
	if profiler == nil {
		t.Fatal("profiler should not be nil")
	}
	if profiler.config != config {
		t.Error("config mismatch")
	}
	if profiler.running == nil {
		t.Error("running map should not be nil")
	}
	if profiler.results == nil {
		t.Error("results slice should not be nil")
	}
	if profiler.stopCh == nil {
		t.Error("stopCh should not be nil")
	}
}

func TestNewProfilerWithNilConfig(t *testing.T) {
	profiler := NewProfiler(nil)
	if profiler == nil {
		t.Fatal("profiler should not be nil")
	}
	if profiler.config == nil {
		t.Error("config should not be nil")
	}
}

func TestStartCPUProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		CPUProfileRate: 100,
		OutputDir:      tempDir,
	}
	
	profiler := NewProfiler(config)
	err := profiler.StartCPUProfile()
	if err != nil {
		t.Fatalf("StartCPUProfile failed: %v", err)
	}
	
	// 验证 CPU 剖析已启动
	if !profiler.IsRunning(ProfileTypeCPU) {
		t.Error("CPU profile should be running")
	}
	if profiler.cpuFile == nil {
		t.Error("cpuFile should not be nil")
	}
	
	// 停止剖析
	result, err := profiler.StopCPUProfile()
	if err != nil {
		t.Fatalf("StopCPUProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeCPU {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeCPU)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
	if profiler.IsRunning(ProfileTypeCPU) {
		t.Error("CPU profile should not be running after stop")
	}
	
	// 验证文件存在
	if _, err := os.Stat(result.FilePath); err != nil {
		t.Errorf("profile file not found: %v", err)
	}
}

func TestStartCPUProfileAlreadyRunning(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		CPUProfileRate: 100,
		OutputDir:      tempDir,
	}
	
	profiler := NewProfiler(config)
	err := profiler.StartCPUProfile()
	if err != nil {
		t.Fatalf("StartCPUProfile failed: %v", err)
	}
	defer profiler.StopCPUProfile()
	
	// 再次启动应该失败
	err = profiler.StartCPUProfile()
	if err == nil {
		t.Error("should fail when CPU profile is already running")
	}
}

func TestStopCPUProfileNotRunning(t *testing.T) {
	profiler := NewProfiler(DefaultProfilerConfig())
	
	result, err := profiler.StopCPUProfile()
	if err == nil {
		t.Error("should fail when CPU profile is not running")
	}
	if result != nil {
		t.Error("result should be nil when not running")
	}
}

func TestWriteHeapProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		MemProfileRate: 1,
		OutputDir:      tempDir,
	}
	
	profiler := NewProfiler(config)
	result, err := profiler.WriteHeapProfile()
	
	if err != nil {
		t.Fatalf("WriteHeapProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeMemory {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeMemory)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
	
	// 验证文件存在
	if _, err := os.Stat(result.FilePath); err != nil {
		t.Errorf("profile file not found: %v", err)
	}
	
	// 验证结果已记录
	results := profiler.GetResults()
	if len(results) != 1 {
		t.Errorf("results count = %d, want 1", len(results))
	}
}

func TestWriteGoroutineProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		OutputDir: tempDir,
	}
	
	profiler := NewProfiler(config)
	result, err := profiler.WriteGoroutineProfile()
	
	if err != nil {
		t.Fatalf("WriteGoroutineProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeGoroutine {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeGoroutine)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
	
	// 验证文件存在
	if _, err := os.Stat(result.FilePath); err != nil {
		t.Errorf("profile file not found: %v", err)
	}
}

func TestWriteBlockProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		BlockProfileRate: 1,
		OutputDir:        tempDir,
	}
	
	profiler := NewProfiler(config)
	result, err := profiler.WriteBlockProfile()
	
	if err != nil {
		t.Fatalf("WriteBlockProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeBlock {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeBlock)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
}

func TestWriteMutexProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		MutexProfileFraction: 1,
		OutputDir:            tempDir,
	}
	
	profiler := NewProfiler(config)
	result, err := profiler.WriteMutexProfile()
	
	if err != nil {
		t.Fatalf("WriteMutexProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeMutex {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeMutex)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
}

func TestWriteThreadCreateProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		OutputDir: tempDir,
	}
	
	profiler := NewProfiler(config)
	result, err := profiler.WriteThreadCreateProfile()
	
	if err != nil {
		t.Fatalf("WriteThreadCreateProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeThreadCreate {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeThreadCreate)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
}

func TestProfilerStartWithCPU(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		CPUProfileRate: 100,
		OutputDir:      tempDir,
		Duration:       100 * time.Millisecond,
	}
	
	profiler := NewProfiler(config)
	err := profiler.Start([]ProfileType{ProfileTypeCPU})
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	
	// 等待自动停止
	time.Sleep(200 * time.Millisecond)
	
	// 验证已停止
	if profiler.IsRunning(ProfileTypeCPU) {
		t.Error("CPU profile should have stopped automatically")
	}
}

func TestProfilerStartWithUnsupportedType(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		OutputDir: tempDir,
	}
	
	profiler := NewProfiler(config)
	err := profiler.Start([]ProfileType{ProfileTypeMemory})
	
	if err == nil {
		t.Error("should fail when using unsupported profile type")
	}
}

func TestProfilerStop(t *testing.T) {
	tempDir := t.TempDir()
	config := &ProfilerConfig{
		CPUProfileRate: 100,
		OutputDir:      tempDir,
	}
	
	profiler := NewProfiler(config)
	err := profiler.StartCPUProfile()
	if err != nil {
		t.Fatalf("StartCPUProfile failed: %v", err)
	}
	
	results := profiler.Stop()
	
	// 验证已停止
	if profiler.IsRunning(ProfileTypeCPU) {
		t.Error("CPU profile should be stopped")
	}
	if len(results) != 1 {
		t.Errorf("results count = %d, want 1", len(results))
	}
	if results[0].Type != ProfileTypeCPU {
		t.Errorf("Type = %v, want %v", results[0].Type, ProfileTypeCPU)
	}
}

func TestGetResults(t *testing.T) {
	tempDir := t.TempDir()
	profiler := NewProfiler(&ProfilerConfig{
		OutputDir: tempDir,
	})
	
	// 初始为空
	results := profiler.GetResults()
	if len(results) != 0 {
		t.Errorf("initial results count = %d, want 0", len(results))
	}
	
	// 添加结果
	_, err := profiler.WriteHeapProfile()
	if err != nil {
		t.Fatalf("WriteHeapProfile failed: %v", err)
	}
	
	_, err = profiler.WriteGoroutineProfile()
	if err != nil {
		t.Fatalf("WriteGoroutineProfile failed: %v", err)
	}
	
	results = profiler.GetResults()
	if len(results) != 2 {
		t.Errorf("results count = %d, want 2", len(results))
	}
}

func TestSimpleProfile(t *testing.T) {
	tempDir := t.TempDir()
	
	// 测试堆内存剖析
	result, err := SimpleProfile(ProfileTypeMemory, tempDir)
	if err != nil {
		t.Fatalf("SimpleProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeMemory {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeMemory)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
	
	// 验证文件存在
	if _, err := os.Stat(result.FilePath); err != nil {
		t.Errorf("profile file not found: %v", err)
	}
}

func TestSimpleProfileCPU(t *testing.T) {
	tempDir := t.TempDir()
	
	// 测试 CPU 剖析
	result, err := SimpleProfile(ProfileTypeCPU, tempDir)
	if err != nil {
		t.Fatalf("SimpleProfile failed: %v", err)
	}
	if result == nil {
		t.Fatal("result should not be nil")
	}
	if result.Type != ProfileTypeCPU {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeCPU)
	}
	if result.FilePath == "" {
		t.Error("FilePath should not be empty")
	}
	
	// 验证文件存在
	if _, err := os.Stat(result.FilePath); err != nil {
		t.Errorf("profile file not found: %v", err)
	}
}

func TestSimpleProfileUnknownType(t *testing.T) {
	tempDir := t.TempDir()
	
	// 测试未知类型
	_, err := SimpleProfile(ProfileType("unknown"), tempDir)
	if err == nil {
		t.Error("should fail for unknown profile type")
	}
}

func TestEnableAllProfiles(t *testing.T) {
	config := &ProfilerConfig{
		BlockProfileRate:     1,
		MutexProfileFraction: 1,
		MemProfileRate:       1,
	}
	
	err := EnableAllProfiles(config)
	if err != nil {
		t.Errorf("EnableAllProfiles failed: %v", err)
	}
}

func TestProfileResultFields(t *testing.T) {
	now := time.Now()
	result := ProfileResult{
		Type:      ProfileTypeCPU,
		FilePath:  "/tmp/test.prof",
		StartTime: now,
		EndTime:   now.Add(time.Second),
		Duration:  time.Second,
		Error:     nil,
	}
	
	if result.Type != ProfileTypeCPU {
		t.Errorf("Type = %v, want %v", result.Type, ProfileTypeCPU)
	}
	if result.FilePath != "/tmp/test.prof" {
		t.Errorf("FilePath = %s, want /tmp/test.prof", result.FilePath)
	}
	if result.StartTime != now {
		t.Error("StartTime mismatch")
	}
	if !result.EndTime.Equal(now.Add(time.Second)) {
		t.Error("EndTime mismatch")
	}
	if result.Duration != time.Second {
		t.Errorf("Duration = %v, want 1s", result.Duration)
	}
	if result.Error != nil {
		t.Error("Error should be nil")
	}
}

func TestGetProfileStats(t *testing.T) {
	stats := GetProfileStats()
	if stats == nil {
		t.Fatal("stats should not be nil")
	}
	if _, ok := stats["cpu_profile_rate"]; !ok {
		t.Error("should contain cpu_profile_rate")
	}
	if _, ok := stats["mem_profile_rate"]; !ok {
		t.Error("should contain mem_profile_rate")
	}
	if _, ok := stats["block_profile_rate"]; !ok {
		t.Error("should contain block_profile_rate")
	}
	if _, ok := stats["mutex_profile_fraction"]; !ok {
		t.Error("should contain mutex_profile_fraction")
	}
}

func TestProfileTypeConstants(t *testing.T) {
	if ProfileTypeCPU != ProfileType("cpu") {
		t.Error("ProfileTypeCPU mismatch")
	}
	if ProfileTypeMemory != ProfileType("memory") {
		t.Error("ProfileTypeMemory mismatch")
	}
	if ProfileTypeGoroutine != ProfileType("goroutine") {
		t.Error("ProfileTypeGoroutine mismatch")
	}
	if ProfileTypeBlock != ProfileType("block") {
		t.Error("ProfileTypeBlock mismatch")
	}
	if ProfileTypeMutex != ProfileType("mutex") {
		t.Error("ProfileTypeMutex mismatch")
	}
	if ProfileTypeThreadCreate != ProfileType("threadcreate") {
		t.Error("ProfileTypeThreadCreate mismatch")
	}
}

func TestProfilerCreateDirectory(t *testing.T) {
	tempDir := t.TempDir()
	nestedDir := filepath.Join(tempDir, "nested", "profiles")
	
	config := &ProfilerConfig{
		OutputDir: nestedDir,
	}
	
	profiler := NewProfiler(config)
	_, err := profiler.WriteHeapProfile()
	
	if err != nil {
		t.Fatalf("WriteHeapProfile failed: %v", err)
	}
	
	// 验证目录已创建
	if _, err := os.Stat(nestedDir); err != nil {
		t.Errorf("output directory not created: %v", err)
	}
}

func BenchmarkNewProfiler(b *testing.B) {
	config := DefaultProfilerConfig()
	for i := 0; i < b.N; i++ {
		_ = NewProfiler(config)
	}
}

func BenchmarkStartStopCPUProfile(b *testing.B) {
	tempDir := b.TempDir()
	config := &ProfilerConfig{
		CPUProfileRate: 100,
		OutputDir:      tempDir,
	}
	
	for i := 0; i < b.N; i++ {
		profiler := NewProfiler(config)
		profiler.StartCPUProfile()
		profiler.StopCPUProfile()
	}
}

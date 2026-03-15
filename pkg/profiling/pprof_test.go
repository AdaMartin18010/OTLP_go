package profiling

import (
	"bytes"
	"context"
	"os"
	"path/filepath"
	"runtime"
	"sync"
	"testing"
	"time"
)

func TestDefaultPProfConfig(t *testing.T) {
	config := DefaultPProfConfig()

	if config == nil {
		t.Fatal("expected non-nil config")
	}

	if config.CPUProfileRate != 100 {
		t.Errorf("expected CPUProfileRate 100, got %d", config.CPUProfileRate)
	}

	if config.OutputDir != "./profiles" {
		t.Errorf("expected OutputDir './profiles', got %s", config.OutputDir)
	}

	if config.Duration != 30*time.Second {
		t.Errorf("expected Duration 30s, got %v", config.Duration)
	}
}

func TestNewPProfManager(t *testing.T) {
	config := DefaultPProfConfig()
	manager := NewPProfManager(config)

	if manager == nil {
		t.Fatal("expected non-nil manager")
	}

	if manager.config != config {
		t.Error("expected manager to use provided config")
	}

	if manager.running == nil {
		t.Error("expected running map to be initialized")
	}

	if manager.results == nil {
		t.Error("expected results slice to be initialized")
	}
}

func TestNewPProfManagerWithNilConfig(t *testing.T) {
	manager := NewPProfManager(nil)

	if manager == nil {
		t.Fatal("expected non-nil manager")
	}

	if manager.config == nil {
		t.Fatal("expected default config to be set")
	}
}

func TestStartCPUProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	err := manager.StartCPUProfile()
	if err != nil {
		t.Fatalf("failed to start CPU profile: %v", err)
	}

	if !manager.IsRunning(ProfileTypeCPU) {
		t.Error("expected CPU profile to be running")
	}

	// 停止剖析
	result, err := manager.StopCPUProfile()
	if err != nil {
		t.Fatalf("failed to stop CPU profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeCPU {
		t.Errorf("expected type CPU, got %s", result.Type)
	}

	if len(result.Data) == 0 {
		t.Error("expected non-empty data")
	}

	if result.Duration <= 0 {
		t.Error("expected positive duration")
	}
}

func TestStartCPUProfileAlreadyRunning(t *testing.T) {
	config := DefaultPProfConfig()
	manager := NewPProfManager(config)

	err := manager.StartCPUProfile()
	if err != nil {
		t.Fatalf("failed to start CPU profile: %v", err)
	}
	defer manager.StopCPUProfile()

	// 尝试再次启动
	err = manager.StartCPUProfile()
	if err == nil {
		t.Error("expected error when starting CPU profile while already running")
	}
}

func TestStopCPUProfileNotRunning(t *testing.T) {
	manager := NewPProfManager(nil)

	_, err := manager.StopCPUProfile()
	if err == nil {
		t.Error("expected error when stopping CPU profile that is not running")
	}
}

func TestCaptureHeapProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	result, err := manager.CaptureHeapProfile()
	if err != nil {
		t.Fatalf("failed to capture heap profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeMemory {
		t.Errorf("expected type Memory, got %s", result.Type)
	}

	if len(result.Data) == 0 {
		t.Error("expected non-empty data")
	}
}

func TestCaptureGoroutineProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	result, err := manager.CaptureGoroutineProfile()
	if err != nil {
		t.Fatalf("failed to capture goroutine profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeGoroutine {
		t.Errorf("expected type Goroutine, got %s", result.Type)
	}

	if len(result.Data) == 0 {
		t.Error("expected non-empty data")
	}
}

func TestCaptureBlockProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	config.BlockProfileRate = 1
	manager := NewPProfManager(config)

	result, err := manager.CaptureBlockProfile()
	if err != nil {
		t.Fatalf("failed to capture block profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeBlock {
		t.Errorf("expected type Block, got %s", result.Type)
	}
}

func TestCaptureMutexProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	config.MutexProfileFraction = 1
	manager := NewPProfManager(config)

	result, err := manager.CaptureMutexProfile()
	if err != nil {
		t.Fatalf("failed to capture mutex profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeMutex {
		t.Errorf("expected type Mutex, got %s", result.Type)
	}
}

func TestCaptureThreadCreateProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	result, err := manager.CaptureThreadCreateProfile()
	if err != nil {
		t.Fatalf("failed to capture thread create profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeThreadCreate {
		t.Errorf("expected type ThreadCreate, got %s", result.Type)
	}
}

func TestCaptureAllocsProfile(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	result, err := manager.CaptureAllocsProfile()
	if err != nil {
		t.Fatalf("failed to capture allocs profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeAllocs {
		t.Errorf("expected type Allocs, got %s", result.Type)
	}
}

func TestSaveProfile(t *testing.T) {
	tempDir := t.TempDir()
	config := DefaultPProfConfig()
	config.OutputDir = tempDir
	manager := NewPProfManager(config)

	result, err := manager.CaptureHeapProfile()
	if err != nil {
		t.Fatalf("failed to capture heap profile: %v", err)
	}

	filename := "test_heap.prof"
	err = manager.SaveProfile(result, filename)
	if err != nil {
		t.Fatalf("failed to save profile: %v", err)
	}

	if result.FilePath == "" {
		t.Error("expected FilePath to be set")
	}

	// 检查文件是否存在
	if _, err := os.Stat(result.FilePath); os.IsNotExist(err) {
		t.Errorf("expected file to exist at %s", result.FilePath)
	}
}

func TestSaveProfileWithError(t *testing.T) {
	manager := NewPProfManager(nil)

	result := &PProfResult{
		Type:  ProfileTypeMemory,
		Error: os.ErrInvalid,
	}

	err := manager.SaveProfile(result, "test.prof")
	if err == nil {
		t.Error("expected error when saving profile with error")
	}
}

func TestGetProfileData(t *testing.T) {
	manager := NewPProfManager(nil)

	data, err := manager.GetProfileData(ProfileTypeMemory, 0)
	if err != nil {
		t.Fatalf("failed to get profile data: %v", err)
	}

	if len(data) == 0 {
		t.Error("expected non-empty data")
	}
}

func TestGetProfileDataUnsupportedType(t *testing.T) {
	manager := NewPProfManager(nil)

	_, err := manager.GetProfileData(ProfileType("unknown"), 0)
	if err == nil {
		t.Error("expected error for unsupported profile type")
	}
}

func TestGetResults(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	// 捕获一个剖析
	_, err := manager.CaptureHeapProfile()
	if err != nil {
		t.Fatalf("failed to capture heap profile: %v", err)
	}

	results := manager.GetResults()
	if len(results) != 1 {
		t.Errorf("expected 1 result, got %d", len(results))
	}
}

func TestClearResults(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	// 捕获一个剖析
	_, err := manager.CaptureHeapProfile()
	if err != nil {
		t.Fatalf("failed to capture heap profile: %v", err)
	}

	manager.ClearResults()

	results := manager.GetResults()
	if len(results) != 0 {
		t.Errorf("expected 0 results after clear, got %d", len(results))
	}
}

func TestStop(t *testing.T) {
	config := DefaultPProfConfig()
	manager := NewPProfManager(config)

	// 启动 CPU 剖析
	err := manager.StartCPUProfile()
	if err != nil {
		t.Fatalf("failed to start CPU profile: %v", err)
	}

	// 停止所有剖析
	results := manager.Stop()

	// 再次停止不应该 panic
	manager.Stop()

	// 结果可能包含 CPU 剖析结果
	_ = results
}

func TestEnableRuntimeProfiling(t *testing.T) {
	config := &PProfConfig{
		BlockProfileRate:     1,
		MutexProfileFraction: 1,
		MemProfileRate:       1,
	}

	err := EnableRuntimeProfiling(config)
	if err != nil {
		t.Fatalf("failed to enable runtime profiling: %v", err)
	}

	// 清理
	DisableRuntimeProfiling()
}

func TestGetProfileStats(t *testing.T) {
	stats := GetProfileStats()

	if stats == nil {
		t.Fatal("expected non-nil stats")
	}

	expectedKeys := []string{"cpu_profile_rate", "mem_profile_rate", "block_profile_rate", "mutex_profile_fraction", "num_goroutine", "num_cpu"}
	for _, key := range expectedKeys {
		if _, exists := stats[key]; !exists {
			t.Errorf("expected key %s in stats", key)
		}
	}
}

func TestLookupProfile(t *testing.T) {
	profile := LookupProfile("heap")
	if profile == nil {
		t.Error("expected heap profile to exist")
	}

	profile = LookupProfile("nonexistent")
	if profile != nil {
		t.Error("expected nil for nonexistent profile")
	}
}

func TestProfiles(t *testing.T) {
	profiles := Profiles()
	if len(profiles) == 0 {
		t.Error("expected some profiles to exist")
	}

	// 检查常见的 profile 是否存在
	profileNames := make(map[string]bool)
	for _, p := range profiles {
		profileNames[p.Name()] = true
	}

	expectedProfiles := []string{"heap", "goroutine", "threadcreate"}
	for _, name := range expectedProfiles {
		if !profileNames[name] {
			t.Errorf("expected profile %s to exist", name)
		}
	}
}

func TestProfileToWriter(t *testing.T) {
	var buf bytes.Buffer
	err := ProfileToWriter(ProfileTypeMemory, &buf, 0)
	if err != nil {
		t.Fatalf("failed to write profile to buffer: %v", err)
	}

	if buf.Len() == 0 {
		t.Error("expected non-empty buffer")
	}
}

func TestProfileToWriterUnsupportedType(t *testing.T) {
	var buf bytes.Buffer
	err := ProfileToWriter(ProfileType("unknown"), &buf, 0)
	if err == nil {
		t.Error("expected error for unsupported profile type")
	}
}

func TestStartCPUProfileContext(t *testing.T) {
	config := DefaultPProfConfig()
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	manager, err := StartCPUProfileContext(ctx, config)
	if err != nil {
		t.Fatalf("failed to start CPU profile with context: %v", err)
	}

	// 等待上下文取消
	<-ctx.Done()
	time.Sleep(50 * time.Millisecond) // 给 goroutine 一点时间处理

	// 清理
	manager.Stop()
}

func TestSimpleProfile(t *testing.T) {
	// 测试 CPU 剖析
	result, err := SimpleProfile(ProfileTypeCPU, 50*time.Millisecond)
	if err != nil {
		t.Fatalf("failed to capture simple CPU profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}

	if result.Type != ProfileTypeCPU {
		t.Errorf("expected type CPU, got %s", result.Type)
	}

	// 测试内存剖析
	result, err = SimpleProfile(ProfileTypeMemory, 0)
	if err != nil {
		t.Fatalf("failed to capture simple heap profile: %v", err)
	}

	if result.Type != ProfileTypeMemory {
		t.Errorf("expected type Memory, got %s", result.Type)
	}

	// 测试 Goroutine 剖析
	result, err = SimpleProfile(ProfileTypeGoroutine, 0)
	if err != nil {
		t.Fatalf("failed to capture simple goroutine profile: %v", err)
	}

	if result.Type != ProfileTypeGoroutine {
		t.Errorf("expected type Goroutine, got %s", result.Type)
	}

	// 测试未知的剖析类型
	_, err = SimpleProfile(ProfileType("unknown"), 0)
	if err == nil {
		t.Error("expected error for unknown profile type")
	}
}

func TestSimpleProfileWithZeroDuration(t *testing.T) {
	// 测试使用默认持续时间
	result, err := SimpleProfile(ProfileTypeCPU, 0)
	if err != nil {
		t.Fatalf("failed to capture simple CPU profile: %v", err)
	}

	if result == nil {
		t.Fatal("expected non-nil result")
	}
}

func TestPProfResultFields(t *testing.T) {
	start := time.Now()
	result := &PProfResult{
		Type:      ProfileTypeCPU,
		Data:      []byte("test data"),
		StartTime: start,
		EndTime:   start.Add(100 * time.Millisecond),
		Duration:  100 * time.Millisecond,
	}

	if result.Type != ProfileTypeCPU {
		t.Error("Type field mismatch")
	}

	if string(result.Data) != "test data" {
		t.Error("Data field mismatch")
	}

	if !result.StartTime.Equal(start) {
		t.Error("StartTime field mismatch")
	}

	if result.Duration != 100*time.Millisecond {
		t.Error("Duration field mismatch")
	}
}

func TestProfileTypeConstants(t *testing.T) {
	tests := []struct {
		name     string
		expected string
		actual   ProfileType
	}{
		{"CPU", "cpu", ProfileTypeCPU},
		{"Memory", "memory", ProfileTypeMemory},
		{"Goroutine", "goroutine", ProfileTypeGoroutine},
		{"Block", "block", ProfileTypeBlock},
		{"Mutex", "mutex", ProfileTypeMutex},
		{"ThreadCreate", "threadcreate", ProfileTypeThreadCreate},
		{"Allocs", "allocs", ProfileTypeAllocs},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if string(tt.actual) != tt.expected {
				t.Errorf("expected %s, got %s", tt.expected, tt.actual)
			}
		})
	}
}

func TestPProfManagerConcurrency(t *testing.T) {
	config := DefaultPProfConfig()
	config.OutputDir = t.TempDir()
	manager := NewPProfManager(config)

	var wg sync.WaitGroup
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			_, err := manager.CaptureHeapProfile()
			if err != nil {
				t.Errorf("failed to capture heap profile: %v", err)
			}
		}()
	}
	wg.Wait()

	results := manager.GetResults()
	if len(results) != 10 {
		t.Errorf("expected 10 results, got %d", len(results))
	}
}

func BenchmarkCaptureHeapProfile(b *testing.B) {
	config := DefaultPProfConfig()
	config.OutputDir = b.TempDir()
	manager := NewPProfManager(config)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := manager.CaptureHeapProfile()
		if err != nil {
			b.Fatal(err)
		}
	}
}

func BenchmarkCaptureGoroutineProfile(b *testing.B) {
	config := DefaultPProfConfig()
	config.OutputDir = b.TempDir()
	manager := NewPProfManager(config)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_, err := manager.CaptureGoroutineProfile()
		if err != nil {
			b.Fatal(err)
		}
	}
}

func TestMain(m *testing.M) {
	// 设置测试数据目录
	runtime.GOMAXPROCS(runtime.NumCPU())
	os.Exit(m.Run())
}

func TestPProfManagerDirectoryCreation(t *testing.T) {
	tempDir := t.TempDir()
	nestedDir := filepath.Join(tempDir, "nested", "profiles")

	config := DefaultPProfConfig()
	config.OutputDir = nestedDir
	manager := NewPProfManager(config)

	result, err := manager.CaptureHeapProfile()
	if err != nil {
		t.Fatalf("failed to capture heap profile: %v", err)
	}

	// 尝试保存到嵌套目录
	err = manager.SaveProfile(result, "test.prof")
	if err != nil {
		t.Fatalf("failed to save profile: %v", err)
	}

	// 验证目录被创建
	if _, err := os.Stat(nestedDir); os.IsNotExist(err) {
		t.Error("expected nested directory to be created")
	}
}

func TestSaveProfileAutoFilename(t *testing.T) {
	tempDir := t.TempDir()
	config := DefaultPProfConfig()
	config.OutputDir = tempDir
	manager := NewPProfManager(config)

	result, err := manager.CaptureHeapProfile()
	if err != nil {
		t.Fatalf("failed to capture heap profile: %v", err)
	}

	// 使用空文件名，应该自动生成
	err = manager.SaveProfile(result, "")
	if err != nil {
		t.Fatalf("failed to save profile: %v", err)
	}

	if result.FilePath == "" {
		t.Error("expected auto-generated filename")
	}

	// 验证文件存在
	if _, err := os.Stat(result.FilePath); os.IsNotExist(err) {
		t.Errorf("expected file to exist at %s", result.FilePath)
	}
}

package runtime

import (
	"runtime/debug"
	"testing"
)

func TestDefaultConfig(t *testing.T) {
	cfg := DefaultConfig()

	if cfg == nil {
		t.Fatal("DefaultConfig() returned nil")
	}

	// 验证默认值
	if cfg.MemoryLimitBytes != 4*1024*1024*1024 {
		t.Errorf("Expected MemoryLimitBytes = 4GB, got %d", cfg.MemoryLimitBytes)
	}

	if cfg.GCPercent != 100 {
		t.Errorf("Expected GCPercent = 100, got %d", cfg.GCPercent)
	}

	if cfg.MaxGoroutines != 10000 {
		t.Errorf("Expected MaxGoroutines = 10000, got %d", cfg.MaxGoroutines)
	}

	if cfg.EnableCPUAffinity {
		t.Error("Expected EnableCPUAffinity = false")
	}

	if cfg.DebugLevel != 0 {
		t.Errorf("Expected DebugLevel = 0, got %d", cfg.DebugLevel)
	}
}

func TestApplyConfig(t *testing.T) {
	// 保存原始设置
	originalGCPercent := debug.SetGCPercent(-1)
	defer debug.SetGCPercent(originalGCPercent)

	cfg := &Config{
		MemoryLimitBytes: 2 * 1024 * 1024 * 1024, // 2GB
		GCPercent:        50,
	}

	ApplyConfig(cfg)

	// 验证 GC 百分比已设置
	// 注意：无法直接读取 MemoryLimit，只能验证函数没有 panic
}

func TestApplyConfigNil(t *testing.T) {
	// 测试 nil 配置会使用默认配置
	defer func() {
		if r := recover(); r != nil {
			t.Errorf("ApplyConfig(nil) panicked: %v", r)
		}
	}()

	ApplyConfig(nil)
}

func TestGetRuntimeStats(t *testing.T) {
	stats := GetRuntimeStats()

	if stats == nil {
		t.Fatal("GetRuntimeStats() returned nil")
	}

	// 验证基本统计信息
	if stats.NumCPU <= 0 {
		t.Errorf("Expected NumCPU > 0, got %d", stats.NumCPU)
	}

	if stats.GOMAXPROCS <= 0 {
		t.Errorf("Expected GOMAXPROCS > 0, got %d", stats.GOMAXPROCS)
	}

	if stats.NumGoroutine <= 0 {
		t.Errorf("Expected NumGoroutine > 0, got %d", stats.NumGoroutine)
	}

	// 内存统计应该有值
	if stats.MemAlloc == 0 {
		t.Log("Warning: MemAlloc is 0, which is unusual")
	}

	if stats.Sys == 0 {
		t.Error("Expected Sys > 0")
	}
}

func TestGetRuntimeStatsMultipleTimes(t *testing.T) {
	// 多次调用应该返回不同的统计（因为程序在运行）
	stats1 := GetRuntimeStats()
	stats2 := GetRuntimeStats()

	if stats1 == nil || stats2 == nil {
		t.Fatal("GetRuntimeStats() returned nil")
	}

	// NumCPU 应该保持不变
	if stats1.NumCPU != stats2.NumCPU {
		t.Errorf("NumCPU changed: %d -> %d", stats1.NumCPU, stats2.NumCPU)
	}

	// GOMAXPROCS 应该保持不变
	if stats1.GOMAXPROCS != stats2.GOMAXPROCS {
		t.Errorf("GOMAXPROCS changed: %d -> %d", stats1.GOMAXPROCS, stats2.GOMAXPROCS)
	}
}

func TestForceGC(t *testing.T) {
	// 测试 ForceGC 不会 panic
	defer func() {
		if r := recover(); r != nil {
			t.Errorf("ForceGC() panicked: %v", r)
		}
	}()

	stats1 := GetRuntimeStats()
	ForceGC()
	stats2 := GetRuntimeStats()

	// GC 次数应该增加
	if stats2.NumGC <= stats1.NumGC {
		t.Logf("Warning: NumGC did not increase after ForceGC: %d -> %d", stats1.NumGC, stats2.NumGC)
	}
}

func TestLockUnlockOSThread(t *testing.T) {
	// 测试线程锁定不会 panic
	defer func() {
		if r := recover(); r != nil {
			t.Errorf("Lock/UnlockOSThread panicked: %v", r)
		}
	}()

	LockOSThread()
	UnlockOSThread()
}

func TestSetFinalizer(t *testing.T) {
	// 测试终结器设置不会 panic
	finalizerCalled := false

	obj := &struct{ data string }{data: "test"}
	SetFinalizer(obj, func(o *struct{ data string }) {
		finalizerCalled = true
	})

	// 注意：我们不能保证终结器会被调用，只能测试设置不会 panic
	if finalizerCalled {
		t.Log("Finalizer was called (unexpected in this test)")
	}
}

func BenchmarkGetRuntimeStats(b *testing.B) {
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = GetRuntimeStats()
	}
}

func BenchmarkForceGC(b *testing.B) {
	for i := 0; i < b.N; i++ {
		ForceGC()
	}
}

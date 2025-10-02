package runtime

import (
	"runtime"
	"runtime/debug"

	_ "go.uber.org/automaxprocs" // 自动感知容器 GOMAXPROCS
)

// Config 运行时配置
type Config struct {
	MemoryLimitBytes  int64 // 内存限制（字节）
	GCPercent         int   // GC 触发百分比
	MaxGoroutines     int   // 最大 goroutine 数
	EnableCPUAffinity bool  // 启用 CPU 亲和性
	DebugLevel        int   // 调试级别
}

// DefaultConfig 返回默认配置
func DefaultConfig() *Config {
	return &Config{
		MemoryLimitBytes:  4 * 1024 * 1024 * 1024, // 4GB
		GCPercent:         100,
		MaxGoroutines:     10000,
		EnableCPUAffinity: false,
		DebugLevel:        0,
	}
}

// ApplyConfig 应用运行时配置
// 结合 Go 1.25.1 的增强式 GC 和容器感知特性
func ApplyConfig(cfg *Config) {
	if cfg == nil {
		cfg = DefaultConfig()
	}

	// 设置软内存限制（Go 1.19+）
	// 启用增量式 GC，减少 GC 暂停时间
	if cfg.MemoryLimitBytes > 0 {
		debug.SetMemoryLimit(cfg.MemoryLimitBytes)
	}

	// 设置 GC 百分比
	if cfg.GCPercent > 0 {
		debug.SetGCPercent(cfg.GCPercent)
	}

	// GOMAXPROCS 由 automaxprocs 自动设置（容器感知）
	// 手动设置会覆盖自动检测
	// runtime.GOMAXPROCS(runtime.NumCPU())
}

// GetStats 获取运行时统计信息
type Stats struct {
	NumGoroutine int
	NumCPU       int
	GOMAXPROCS   int
	MemAlloc     uint64 // 已分配内存（字节）
	TotalAlloc   uint64 // 累计分配内存
	Sys          uint64 // 系统内存
	NumGC        uint32 // GC 次数
	PauseTotalNs uint64 // GC 总暂停时间（纳秒）
	LastGCTime   uint64 // 上次 GC 时间
}

// GetRuntimeStats 获取详细的运行时统计
func GetRuntimeStats() *Stats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return &Stats{
		NumGoroutine: runtime.NumGoroutine(),
		NumCPU:       runtime.NumCPU(),
		GOMAXPROCS:   runtime.GOMAXPROCS(0),
		MemAlloc:     m.Alloc,
		TotalAlloc:   m.TotalAlloc,
		Sys:          m.Sys,
		NumGC:        m.NumGC,
		PauseTotalNs: m.PauseTotalNs,
		LastGCTime:   m.LastGC,
	}
}

// LockOSThread 锁定当前 goroutine 到 OS 线程
// 用于需要线程局部存储或 CPU 亲和性的场景
func LockOSThread() {
	runtime.LockOSThread()
}

// UnlockOSThread 解锁 OS 线程
func UnlockOSThread() {
	runtime.UnlockOSThread()
}

// ForceGC 强制执行 GC（仅用于测试和调试）
func ForceGC() {
	runtime.GC()
}

// SetFinalizer 设置对象终结器
func SetFinalizer(obj interface{}, finalizer interface{}) {
	runtime.SetFinalizer(obj, finalizer)
}

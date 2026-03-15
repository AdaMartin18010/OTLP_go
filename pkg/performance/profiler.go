// Package performance provides performance optimization utilities
// for the OTLP Go SDK.
package performance

import (
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"sync"
	"time"
)

// ProfileType 定义剖析类型
type ProfileType string

const (
	// ProfileTypeCPU CPU 剖析
	ProfileTypeCPU ProfileType = "cpu"
	// ProfileTypeMemory 内存剖析
	ProfileTypeMemory ProfileType = "memory"
	// ProfileTypeGoroutine Goroutine 剖析
	ProfileTypeGoroutine ProfileType = "goroutine"
	// ProfileTypeBlock 阻塞剖析
	ProfileTypeBlock ProfileType = "block"
	// ProfileTypeMutex 互斥锁剖析
	ProfileTypeMutex ProfileType = "mutex"
	// ProfileTypeThreadCreate 线程创建剖析
	ProfileTypeThreadCreate ProfileType = "threadcreate"
)

// ProfilerConfig 性能剖析配置
type ProfilerConfig struct {
	// CPUProfileRate CPU 采样频率（Hz）
	CPUProfileRate int
	// MemProfileRate 内存分配采样频率（每分配 n 个字节采样一次，0 表示使用默认）
	MemProfileRate int
	// BlockProfileRate 阻塞剖析采样频率（纳秒）
	BlockProfileRate int
	// MutexProfileFraction 互斥锁剖析采样比例（1/n）
	MutexProfileFraction int
	// OutputDir 剖析文件输出目录
	OutputDir string
	// Duration 自动剖析持续时间
	Duration time.Duration
}

// DefaultProfilerConfig 返回默认配置
func DefaultProfilerConfig() *ProfilerConfig {
	return &ProfilerConfig{
		CPUProfileRate:       100,
		MemProfileRate:       0, // 使用默认
		BlockProfileRate:     0,
		MutexProfileFraction: 0,
		OutputDir:            "./profiles",
		Duration:             30 * time.Second,
	}
}

// ProfileResult 剖析结果
type ProfileResult struct {
	Type      ProfileType
	FilePath  string
	StartTime time.Time
	EndTime   time.Time
	Duration  time.Duration
	Error     error
}

// Profiler 性能剖析管理器
type Profiler struct {
	config    *ProfilerConfig
	mu        sync.RWMutex
	running   map[ProfileType]bool
	results   []ProfileResult
	cpuFile   *os.File
	startTime time.Time
	stopCh    chan struct{}
}

// NewProfiler 创建新的性能剖析管理器
func NewProfiler(config *ProfilerConfig) *Profiler {
	if config == nil {
		config = DefaultProfilerConfig()
	}
	return &Profiler{
		config:  config,
		running: make(map[ProfileType]bool),
		results: make([]ProfileResult, 0),
		stopCh:  make(chan struct{}),
	}
}

// StartCPUProfile 开始 CPU 剖析
func (p *Profiler) StartCPUProfile() error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.running[ProfileTypeCPU] {
		return fmt.Errorf("CPU profile already running")
	}

	// 确保输出目录存在
	if err := os.MkdirAll(p.config.OutputDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	// 设置 CPU 采样频率
	if p.config.CPUProfileRate > 0 {
		runtime.SetCPUProfileRate(p.config.CPUProfileRate)
	}

	// 创建剖析文件
	filename := filepath.Join(p.config.OutputDir, fmt.Sprintf("cpu_%d.prof", time.Now().Unix()))
	file, err := os.Create(filename)
	if err != nil {
		return fmt.Errorf("failed to create CPU profile file: %w", err)
	}

	// 开始 CPU 剖析
	if err := pprof.StartCPUProfile(file); err != nil {
		file.Close()
		return fmt.Errorf("failed to start CPU profile: %w", err)
	}

	p.cpuFile = file
	p.running[ProfileTypeCPU] = true
	p.startTime = time.Now()

	return nil
}

// StopCPUProfile 停止 CPU 剖析
func (p *Profiler) StopCPUProfile() (*ProfileResult, error) {
	p.mu.Lock()
	defer p.mu.Unlock()

	if !p.running[ProfileTypeCPU] {
		return nil, fmt.Errorf("CPU profile not running")
	}

	pprof.StopCPUProfile()
	p.cpuFile.Close()

	result := ProfileResult{
		Type:      ProfileTypeCPU,
		FilePath:  p.cpuFile.Name(),
		StartTime: p.startTime,
		EndTime:   time.Now(),
		Duration:  time.Since(p.startTime),
	}

	p.running[ProfileTypeCPU] = false
	p.results = append(p.results, result)

	return &result, nil
}

// WriteHeapProfile 写入堆内存剖析
func (p *Profiler) WriteHeapProfile() (*ProfileResult, error) {
	p.mu.Lock()
	defer p.mu.Unlock()

	// 确保输出目录存在
	if err := os.MkdirAll(p.config.OutputDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create output directory: %w", err)
	}

	// 设置内存采样频率
	if p.config.MemProfileRate >= 0 {
		runtime.MemProfileRate = p.config.MemProfileRate
	}

	// 创建剖析文件
	filename := filepath.Join(p.config.OutputDir, fmt.Sprintf("heap_%d.prof", time.Now().Unix()))
	file, err := os.Create(filename)
	if err != nil {
		return nil, fmt.Errorf("failed to create heap profile file: %w", err)
	}
	defer file.Close()

	// 写入堆内存剖析
	startTime := time.Now()
	if err := pprof.WriteHeapProfile(file); err != nil {
		return nil, fmt.Errorf("failed to write heap profile: %w", err)
	}

	result := ProfileResult{
		Type:      ProfileTypeMemory,
		FilePath:  filename,
		StartTime: startTime,
		EndTime:   time.Now(),
		Duration:  time.Since(startTime),
	}

	p.results = append(p.results, result)

	return &result, nil
}

// WriteGoroutineProfile 写入 Goroutine 剖析
func (p *Profiler) WriteGoroutineProfile() (*ProfileResult, error) {
	return p.writeProfile("goroutine", ProfileTypeGoroutine)
}

// WriteBlockProfile 写入阻塞剖析
func (p *Profiler) WriteBlockProfile() (*ProfileResult, error) {
	// 设置阻塞剖析采样频率
	if p.config.BlockProfileRate > 0 {
		runtime.SetBlockProfileRate(p.config.BlockProfileRate)
	}
	return p.writeProfile("block", ProfileTypeBlock)
}

// WriteMutexProfile 写入互斥锁剖析
func (p *Profiler) WriteMutexProfile() (*ProfileResult, error) {
	// 设置互斥锁剖析采样比例
	if p.config.MutexProfileFraction > 0 {
		runtime.SetMutexProfileFraction(p.config.MutexProfileFraction)
	}
	return p.writeProfile("mutex", ProfileTypeMutex)
}

// WriteThreadCreateProfile 写入线程创建剖析
func (p *Profiler) WriteThreadCreateProfile() (*ProfileResult, error) {
	return p.writeProfile("threadcreate", ProfileTypeThreadCreate)
}

// writeProfile 通用剖析写入方法
func (p *Profiler) writeProfile(name string, profileType ProfileType) (*ProfileResult, error) {
	p.mu.Lock()
	defer p.mu.Unlock()

	// 确保输出目录存在
	if err := os.MkdirAll(p.config.OutputDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create output directory: %w", err)
	}

	// 获取剖析数据
	profile := pprof.Lookup(name)
	if profile == nil {
		return nil, fmt.Errorf("profile %s not found", name)
	}

	// 创建剖析文件
	filename := filepath.Join(p.config.OutputDir, fmt.Sprintf("%s_%d.prof", profileType, time.Now().Unix()))
	file, err := os.Create(filename)
	if err != nil {
		return nil, fmt.Errorf("failed to create %s profile file: %w", profileType, err)
	}
	defer file.Close()

	// 写入剖析数据
	startTime := time.Now()
	if err := profile.WriteTo(file, 0); err != nil {
		return nil, fmt.Errorf("failed to write %s profile: %w", profileType, err)
	}

	result := ProfileResult{
		Type:      profileType,
		FilePath:  filename,
		StartTime: startTime,
		EndTime:   time.Now(),
		Duration:  time.Since(startTime),
	}

	p.results = append(p.results, result)

	return &result, nil
}

// Start 启动自动剖析
func (p *Profiler) Start(types []ProfileType) error {
	if len(types) == 0 {
		types = []ProfileType{ProfileTypeCPU}
	}

	for _, t := range types {
		switch t {
		case ProfileTypeCPU:
			if err := p.StartCPUProfile(); err != nil {
				return err
			}
			// CPU 剖析需要在 Duration 后自动停止
			go func() {
				select {
				case <-time.After(p.config.Duration):
					p.StopCPUProfile()
				case <-p.stopCh:
				}
			}()
		default:
			// 其他类型的剖析不支持持续模式
			return fmt.Errorf("profile type %s does not support continuous mode", t)
		}
	}

	return nil
}

// Stop 停止所有剖析
func (p *Profiler) Stop() []ProfileResult {
	p.mu.Lock()
	defer p.mu.Unlock()

	close(p.stopCh)

	// 停止正在运行的 CPU 剖析
	if p.running[ProfileTypeCPU] {
		pprof.StopCPUProfile()
		if p.cpuFile != nil {
			p.cpuFile.Close()
			result := ProfileResult{
				Type:      ProfileTypeCPU,
				FilePath:  p.cpuFile.Name(),
				StartTime: p.startTime,
				EndTime:   time.Now(),
				Duration:  time.Since(p.startTime),
			}
			p.results = append(p.results, result)
		}
		p.running[ProfileTypeCPU] = false
	}

	return p.GetResults()
}

// GetResults 获取所有剖析结果
func (p *Profiler) GetResults() []ProfileResult {
	p.mu.RLock()
	defer p.mu.RUnlock()

	results := make([]ProfileResult, len(p.results))
	copy(results, p.results)
	return results
}

// IsRunning 检查指定类型的剖析是否正在运行
func (p *Profiler) IsRunning(profileType ProfileType) bool {
	p.mu.RLock()
	defer p.mu.RUnlock()
	return p.running[profileType]
}

// ProfileToWriter 将指定类型的剖析数据写入 writer
func ProfileToWriter(profileType ProfileType, w io.Writer, debug int) error {
	var name string
	switch profileType {
	case ProfileTypeMemory:
		name = "heap"
	case ProfileTypeGoroutine:
		name = "goroutine"
	case ProfileTypeBlock:
		name = "block"
	case ProfileTypeMutex:
		name = "mutex"
	case ProfileTypeThreadCreate:
		name = "threadcreate"
	default:
		return fmt.Errorf("unsupported profile type: %s", profileType)
	}

	profile := pprof.Lookup(name)
	if profile == nil {
		return fmt.Errorf("profile %s not found", name)
	}

	return profile.WriteTo(w, debug)
}

// GetProfileStats 获取剖析统计信息
func GetProfileStats() map[string]interface{} {
	stats := make(map[string]interface{})

	// CPU 统计
	stats["cpu_profile_rate"] = runtime.SetCPUProfileRate

	// 内存统计
	stats["mem_profile_rate"] = runtime.MemProfileRate

	// 阻塞统计
	stats["block_profile_rate"] = "use runtime.SetBlockProfileRate"

	// 互斥锁统计
	stats["mutex_profile_fraction"] = "use runtime.SetMutexProfileFraction"

	return stats
}

// EnableAllProfiles 启用所有类型的剖析
func EnableAllProfiles(config *ProfilerConfig) error {
	if config.BlockProfileRate > 0 {
		runtime.SetBlockProfileRate(config.BlockProfileRate)
	}
	if config.MutexProfileFraction > 0 {
		runtime.SetMutexProfileFraction(config.MutexProfileFraction)
	}
	if config.MemProfileRate >= 0 {
		runtime.MemProfileRate = config.MemProfileRate
	}
	return nil
}

// SimpleProfile 简单的一次性剖析函数
func SimpleProfile(profileType ProfileType, outputPath string) (*ProfileResult, error) {
	config := DefaultProfilerConfig()
	config.OutputDir = outputPath

	profiler := NewProfiler(config)

	switch profileType {
	case ProfileTypeCPU:
		if err := profiler.StartCPUProfile(); err != nil {
			return nil, err
		}
		time.Sleep(config.Duration)
		return profiler.StopCPUProfile()
	case ProfileTypeMemory:
		return profiler.WriteHeapProfile()
	case ProfileTypeGoroutine:
		return profiler.WriteGoroutineProfile()
	case ProfileTypeBlock:
		return profiler.WriteBlockProfile()
	case ProfileTypeMutex:
		return profiler.WriteMutexProfile()
	case ProfileTypeThreadCreate:
		return profiler.WriteThreadCreateProfile()
	default:
		return nil, fmt.Errorf("unknown profile type: %s", profileType)
	}
}

// Package profiling provides profiling and debugging utilities
// for the OTLP Go SDK.
//
// This file contains pprof integration for CPU, memory, goroutine,
// and other runtime profiling capabilities.
package profiling

import (
	"bytes"
	"context"
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
	// ProfileTypeAllocs 分配剖析
	ProfileTypeAllocs ProfileType = "allocs"
)

// PProfConfig pprof 配置
type PProfConfig struct {
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
	// BufferSize 缓冲区大小
	BufferSize int
}

// DefaultPProfConfig 返回默认配置
func DefaultPProfConfig() *PProfConfig {
	return &PProfConfig{
		CPUProfileRate:       100,
		MemProfileRate:       0, // 使用默认
		BlockProfileRate:     0,
		MutexProfileFraction: 0,
		OutputDir:            "./profiles",
		Duration:             30 * time.Second,
		BufferSize:           4096,
	}
}

// PProfResult pprof 剖析结果
type PProfResult struct {
	Type      ProfileType
	Data      []byte
	FilePath  string
	StartTime time.Time
	EndTime   time.Time
	Duration  time.Duration
	Error     error
}

// PProfManager pprof 管理器
type PProfManager struct {
	config    *PProfConfig
	mu        sync.RWMutex
	running   map[ProfileType]bool
	results   []PProfResult
	cpuBuf    *bytes.Buffer
	cpuFile   *os.File
	startTime time.Time
	stopCh    chan struct{}
}

// NewPProfManager 创建新的 pprof 管理器
func NewPProfManager(config *PProfConfig) *PProfManager {
	if config == nil {
		config = DefaultPProfConfig()
	}
	return &PProfManager{
		config:  config,
		running: make(map[ProfileType]bool),
		results: make([]PProfResult, 0),
		stopCh:  make(chan struct{}),
	}
}

// StartCPUProfile 开始 CPU 剖析
func (p *PProfManager) StartCPUProfile() error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if p.running[ProfileTypeCPU] {
		return fmt.Errorf("CPU profile already running")
	}

	// 设置 CPU 采样频率
	if p.config.CPUProfileRate > 0 {
		runtime.SetCPUProfileRate(p.config.CPUProfileRate)
	}

	// 创建缓冲区
	p.cpuBuf = new(bytes.Buffer)

	// 开始 CPU 剖析
	if err := pprof.StartCPUProfile(p.cpuBuf); err != nil {
		return fmt.Errorf("failed to start CPU profile: %w", err)
	}

	p.running[ProfileTypeCPU] = true
	p.startTime = time.Now()

	return nil
}

// StopCPUProfile 停止 CPU 剖析
func (p *PProfManager) StopCPUProfile() (*PProfResult, error) {
	p.mu.Lock()
	defer p.mu.Unlock()

	if !p.running[ProfileTypeCPU] {
		return nil, fmt.Errorf("CPU profile not running")
	}

	pprof.StopCPUProfile()

	data := make([]byte, p.cpuBuf.Len())
	copy(data, p.cpuBuf.Bytes())

	result := &PProfResult{
		Type:      ProfileTypeCPU,
		Data:      data,
		StartTime: p.startTime,
		EndTime:   time.Now(),
		Duration:  time.Since(p.startTime),
	}

	p.running[ProfileTypeCPU] = false
	p.results = append(p.results, *result)

	return result, nil
}

// CaptureHeapProfile 捕获堆内存剖析
func (p *PProfManager) CaptureHeapProfile() (*PProfResult, error) {
	return p.captureProfile("heap", ProfileTypeMemory)
}

// CaptureGoroutineProfile 捕获 Goroutine 剖析
func (p *PProfManager) CaptureGoroutineProfile() (*PProfResult, error) {
	return p.captureProfile("goroutine", ProfileTypeGoroutine)
}

// CaptureBlockProfile 捕获阻塞剖析
func (p *PProfManager) CaptureBlockProfile() (*PProfResult, error) {
	// 设置阻塞剖析采样频率
	if p.config.BlockProfileRate > 0 {
		runtime.SetBlockProfileRate(p.config.BlockProfileRate)
	}
	return p.captureProfile("block", ProfileTypeBlock)
}

// CaptureMutexProfile 捕获互斥锁剖析
func (p *PProfManager) CaptureMutexProfile() (*PProfResult, error) {
	// 设置互斥锁剖析采样比例
	if p.config.MutexProfileFraction > 0 {
		runtime.SetMutexProfileFraction(p.config.MutexProfileFraction)
	}
	return p.captureProfile("mutex", ProfileTypeMutex)
}

// CaptureThreadCreateProfile 捕获线程创建剖析
func (p *PProfManager) CaptureThreadCreateProfile() (*PProfResult, error) {
	return p.captureProfile("threadcreate", ProfileTypeThreadCreate)
}

// CaptureAllocsProfile 捕获分配剖析
func (p *PProfManager) CaptureAllocsProfile() (*PProfResult, error) {
	return p.captureProfile("allocs", ProfileTypeAllocs)
}

// captureProfile 通用剖析捕获方法
func (p *PProfManager) captureProfile(name string, profileType ProfileType) (*PProfResult, error) {
	p.mu.Lock()
	defer p.mu.Unlock()

	// 获取剖析数据
	profile := pprof.Lookup(name)
	if profile == nil {
		return nil, fmt.Errorf("profile %s not found", name)
	}

	// 写入缓冲区
	var buf bytes.Buffer
	startTime := time.Now()
	if err := profile.WriteTo(&buf, 0); err != nil {
		return nil, fmt.Errorf("failed to write %s profile: %w", profileType, err)
	}

	result := &PProfResult{
		Type:      profileType,
		Data:      buf.Bytes(),
		StartTime: startTime,
		EndTime:   time.Now(),
		Duration:  time.Since(startTime),
	}

	p.results = append(p.results, *result)

	return result, nil
}

// SaveProfile 保存剖析数据到文件
func (p *PProfManager) SaveProfile(result *PProfResult, filename string) error {
	if result.Error != nil {
		return result.Error
	}

	// 确保输出目录存在
	if err := os.MkdirAll(p.config.OutputDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	// 生成文件名
	if filename == "" {
		filename = fmt.Sprintf("%s_%d.prof", result.Type, time.Now().Unix())
	}
	filepath := filepath.Join(p.config.OutputDir, filename)

	// 写入文件
	file, err := os.Create(filepath)
	if err != nil {
		return fmt.Errorf("failed to create profile file: %w", err)
	}
	defer file.Close()

	if _, err := file.Write(result.Data); err != nil {
		return fmt.Errorf("failed to write profile data: %w", err)
	}

	result.FilePath = filepath
	return nil
}

// GetProfileData 获取指定类型的剖析数据
func (p *PProfManager) GetProfileData(profileType ProfileType, debug int) ([]byte, error) {
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
	case ProfileTypeAllocs:
		name = "allocs"
	default:
		return nil, fmt.Errorf("unsupported profile type: %s", profileType)
	}

	profile := pprof.Lookup(name)
	if profile == nil {
		return nil, fmt.Errorf("profile %s not found", name)
	}

	var buf bytes.Buffer
	if err := profile.WriteTo(&buf, debug); err != nil {
		return nil, err
	}

	return buf.Bytes(), nil
}

// IsRunning 检查指定类型的剖析是否正在运行
func (p *PProfManager) IsRunning(profileType ProfileType) bool {
	p.mu.RLock()
	defer p.mu.RUnlock()
	return p.running[profileType]
}

// GetResults 获取所有剖析结果
func (p *PProfManager) GetResults() []PProfResult {
	p.mu.RLock()
	defer p.mu.RUnlock()

	results := make([]PProfResult, len(p.results))
	copy(results, p.results)
	return results
}

// ClearResults 清除所有剖析结果
func (p *PProfManager) ClearResults() {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.results = make([]PProfResult, 0)
}

// Stop 停止所有剖析
func (p *PProfManager) Stop() []PProfResult {
	p.mu.Lock()
	defer p.mu.Unlock()

	select {
	case <-p.stopCh:
		// 已经停止
	default:
		close(p.stopCh)
	}

	// 停止正在运行的 CPU 剖析
	if p.running[ProfileTypeCPU] {
		pprof.StopCPUProfile()
		p.running[ProfileTypeCPU] = false
	}

	return p.results
}

// EnableRuntimeProfiling 启用所有运行时剖析
func EnableRuntimeProfiling(config *PProfConfig) error {
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

// DisableRuntimeProfiling 禁用所有运行时剖析
func DisableRuntimeProfiling() {
	runtime.SetBlockProfileRate(0)
	runtime.SetMutexProfileFraction(0)
}

// GetProfileStats 获取剖析统计信息
func GetProfileStats() map[string]interface{} {
	return map[string]interface{}{
		"cpu_profile_rate":       runtime.SetCPUProfileRate,
		"mem_profile_rate":       runtime.MemProfileRate,
		"block_profile_rate":     "use runtime.SetBlockProfileRate",
		"mutex_profile_fraction": "use runtime.SetMutexProfileFraction",
		"num_goroutine":          runtime.NumGoroutine(),
		"num_cpu":                runtime.NumCPU(),
	}
}

// LookupProfile 查找指定名称的 profile
func LookupProfile(name string) *pprof.Profile {
	return pprof.Lookup(name)
}

// Profiles 返回所有可用的 profiles
func Profiles() []*pprof.Profile {
	return pprof.Profiles()
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
	case ProfileTypeAllocs:
		name = "allocs"
	default:
		return fmt.Errorf("unsupported profile type: %s", profileType)
	}

	profile := pprof.Lookup(name)
	if profile == nil {
		return fmt.Errorf("profile %s not found", name)
	}

	return profile.WriteTo(w, debug)
}

// StartCPUProfileContext 带上下文的 CPU 剖析
func StartCPUProfileContext(ctx context.Context, config *PProfConfig) (*PProfManager, error) {
	manager := NewPProfManager(config)
	if err := manager.StartCPUProfile(); err != nil {
		return nil, err
	}

	go func() {
		select {
		case <-ctx.Done():
			manager.StopCPUProfile()
		case <-manager.stopCh:
		}
	}()

	return manager, nil
}

// SimpleProfile 简单的一次性剖析函数
func SimpleProfile(profileType ProfileType, duration time.Duration) (*PProfResult, error) {
	config := DefaultPProfConfig()
	if duration > 0 {
		config.Duration = duration
	}

	manager := NewPProfManager(config)

	switch profileType {
	case ProfileTypeCPU:
		if err := manager.StartCPUProfile(); err != nil {
			return nil, err
		}
		time.Sleep(config.Duration)
		return manager.StopCPUProfile()
	case ProfileTypeMemory:
		return manager.CaptureHeapProfile()
	case ProfileTypeGoroutine:
		return manager.CaptureGoroutineProfile()
	case ProfileTypeBlock:
		return manager.CaptureBlockProfile()
	case ProfileTypeMutex:
		return manager.CaptureMutexProfile()
	case ProfileTypeThreadCreate:
		return manager.CaptureThreadCreateProfile()
	case ProfileTypeAllocs:
		return manager.CaptureAllocsProfile()
	default:
		return nil, fmt.Errorf("unknown profile type: %s", profileType)
	}
}

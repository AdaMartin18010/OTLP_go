// Package profiling provides profiling and debugging utilities
// for the OTLP Go SDK.
//
// This file contains continuous profiling capabilities for
// long-running production services.
package profiling

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"time"
)

// ContinuousProfileType 持续剖析类型
type ContinuousProfileType string

const (
	// ContinuousCPU CPU 持续剖析
	ContinuousCPU ContinuousProfileType = "cpu"
	// ContinuousMemory 内存持续剖析
	ContinuousMemory ContinuousProfileType = "memory"
	// ContinuousGoroutine Goroutine 持续剖析
	ContinuousGoroutine ContinuousProfileType = "goroutine"
)

// ContinuousProfilerConfig 持续剖析配置
type ContinuousProfilerConfig struct {
	// Enabled 是否启用持续剖析
	Enabled bool
	// ProfileTypes 启用的剖析类型
	ProfileTypes []ContinuousProfileType
	// Interval 剖析间隔
	Interval time.Duration
	// Duration 每次剖析持续时间（仅对 CPU 有效）
	Duration time.Duration
	// OutputDir 输出目录
	OutputDir string
	// MaxAge 最大保留时间
	MaxAge time.Duration
	// MaxSize 最大磁盘使用（字节）
	MaxSize int64
	// Compress 是否压缩
	Compress bool
	// OnError 错误回调
	OnError func(error)
	// OnProfile 剖析完成回调
	OnProfile func(*PProfResult)
}

// DefaultContinuousProfilerConfig 返回默认配置
func DefaultContinuousProfilerConfig() *ContinuousProfilerConfig {
	return &ContinuousProfilerConfig{
		Enabled:      true,
		ProfileTypes: []ContinuousProfileType{ContinuousCPU, ContinuousMemory},
		Interval:     60 * time.Second,
		Duration:     10 * time.Second,
		OutputDir:    "./profiles/continuous",
		MaxAge:       7 * 24 * time.Hour, // 7 天
		MaxSize:      1 * 1024 * 1024 * 1024, // 1GB
		Compress:     true,
	}
}

// ContinuousProfiler 持续剖析器
type ContinuousProfiler struct {
	config      *ContinuousProfilerConfig
	pprofMgr    *PProfManager
	mu          sync.RWMutex
	running     bool
	stopCh      chan struct{}
	wg          sync.WaitGroup
	profileTimes map[ContinuousProfileType]time.Time
}

// NewContinuousProfiler 创建新的持续剖析器
func NewContinuousProfiler(config *ContinuousProfilerConfig) *ContinuousProfiler {
	if config == nil {
		config = DefaultContinuousProfilerConfig()
	}

	pprofConfig := &PProfConfig{
		CPUProfileRate: 100,
		MemProfileRate: 0,
		OutputDir:      config.OutputDir,
		Duration:       config.Duration,
	}

	return &ContinuousProfiler{
		config:       config,
		pprofMgr:     NewPProfManager(pprofConfig),
		stopCh:       make(chan struct{}),
		profileTimes: make(map[ContinuousProfileType]time.Time),
	}
}

// Start 启动持续剖析
func (cp *ContinuousProfiler) Start() error {
	cp.mu.Lock()
	defer cp.mu.Unlock()

	if cp.running {
		return fmt.Errorf("continuous profiler already running")
	}

	if !cp.config.Enabled {
		return fmt.Errorf("continuous profiler is disabled")
	}

	// 确保输出目录存在
	if err := os.MkdirAll(cp.config.OutputDir, 0755); err != nil {
		return fmt.Errorf("failed to create output directory: %w", err)
	}

	cp.running = true
	cp.stopCh = make(chan struct{})

	// 启动清理 goroutine
	cp.wg.Add(1)
	go cp.cleanupLoop()

	// 为每种类型启动剖析循环
	for _, profileType := range cp.config.ProfileTypes {
		switch profileType {
		case ContinuousCPU:
			cp.wg.Add(1)
			go cp.cpuProfileLoop()
		case ContinuousMemory:
			cp.wg.Add(1)
			go cp.memoryProfileLoop()
		case ContinuousGoroutine:
			cp.wg.Add(1)
			go cp.goroutineProfileLoop()
		}
	}

	return nil
}

// Stop 停止持续剖析
func (cp *ContinuousProfiler) Stop() error {
	cp.mu.Lock()
	if !cp.running {
		cp.mu.Unlock()
		return fmt.Errorf("continuous profiler not running")
	}
	cp.running = false
	close(cp.stopCh)
	cp.mu.Unlock()

	// 等待所有 goroutine 结束
	cp.wg.Wait()

	// 停止 pprof 管理器
	cp.pprofMgr.Stop()

	return nil
}

// IsRunning 检查是否正在运行
func (cp *ContinuousProfiler) IsRunning() bool {
	cp.mu.RLock()
	defer cp.mu.RUnlock()
	return cp.running
}

// cpuProfileLoop CPU 剖析循环
func (cp *ContinuousProfiler) cpuProfileLoop() {
	defer cp.wg.Done()

	ticker := time.NewTicker(cp.config.Interval)
	defer ticker.Stop()

	for {
		select {
		case <-cp.stopCh:
			return
		case <-ticker.C:
			if err := cp.captureCPUProfile(); err != nil {
				cp.handleError(err)
			}
		}
	}
}

// memoryProfileLoop 内存剖析循环
func (cp *ContinuousProfiler) memoryProfileLoop() {
	defer cp.wg.Done()

	ticker := time.NewTicker(cp.config.Interval)
	defer ticker.Stop()

	for {
		select {
		case <-cp.stopCh:
			return
		case <-ticker.C:
			if err := cp.captureMemoryProfile(); err != nil {
				cp.handleError(err)
			}
		}
	}
}

// goroutineProfileLoop Goroutine 剖析循环
func (cp *ContinuousProfiler) goroutineProfileLoop() {
	defer cp.wg.Done()

	ticker := time.NewTicker(cp.config.Interval)
	defer ticker.Stop()

	for {
		select {
		case <-cp.stopCh:
			return
		case <-ticker.C:
			if err := cp.captureGoroutineProfile(); err != nil {
				cp.handleError(err)
			}
		}
	}
}

// cleanupLoop 清理循环
func (cp *ContinuousProfiler) cleanupLoop() {
	defer cp.wg.Done()

	// 每小时执行一次清理
	ticker := time.NewTicker(1 * time.Hour)
	defer ticker.Stop()

	for {
		select {
		case <-cp.stopCh:
			return
		case <-ticker.C:
			if err := cp.cleanupOldProfiles(); err != nil {
				cp.handleError(err)
			}
		}
	}
}

// captureCPUProfile 捕获 CPU 剖析
func (cp *ContinuousProfiler) captureCPUProfile() error {
	if err := cp.pprofMgr.StartCPUProfile(); err != nil {
		return fmt.Errorf("failed to start CPU profile: %w", err)
	}

	// 等待持续时间
	time.Sleep(cp.config.Duration)

	result, err := cp.pprofMgr.StopCPUProfile()
	if err != nil {
		return fmt.Errorf("failed to stop CPU profile: %w", err)
	}

	// 保存到文件
	filename := fmt.Sprintf("cpu_%s.prof", time.Now().Format("20060102_150405"))
	if err := cp.pprofMgr.SaveProfile(result, filename); err != nil {
		return fmt.Errorf("failed to save CPU profile: %w", err)
	}

	// 更新记录时间
	cp.mu.Lock()
	cp.profileTimes[ContinuousCPU] = time.Now()
	cp.mu.Unlock()

	// 调用回调
	if cp.config.OnProfile != nil {
		cp.config.OnProfile(result)
	}

	return nil
}

// captureMemoryProfile 捕获内存剖析
func (cp *ContinuousProfiler) captureMemoryProfile() error {
	result, err := cp.pprofMgr.CaptureHeapProfile()
	if err != nil {
		return fmt.Errorf("failed to capture heap profile: %w", err)
	}

	// 保存到文件
	filename := fmt.Sprintf("memory_%s.prof", time.Now().Format("20060102_150405"))
	if err := cp.pprofMgr.SaveProfile(result, filename); err != nil {
		return fmt.Errorf("failed to save memory profile: %w", err)
	}

	// 更新记录时间
	cp.mu.Lock()
	cp.profileTimes[ContinuousMemory] = time.Now()
	cp.mu.Unlock()

	// 调用回调
	if cp.config.OnProfile != nil {
		cp.config.OnProfile(result)
	}

	return nil
}

// captureGoroutineProfile 捕获 Goroutine 剖析
func (cp *ContinuousProfiler) captureGoroutineProfile() error {
	result, err := cp.pprofMgr.CaptureGoroutineProfile()
	if err != nil {
		return fmt.Errorf("failed to capture goroutine profile: %w", err)
	}

	// 保存到文件
	filename := fmt.Sprintf("goroutine_%s.prof", time.Now().Format("20060102_150405"))
	if err := cp.pprofMgr.SaveProfile(result, filename); err != nil {
		return fmt.Errorf("failed to save goroutine profile: %w", err)
	}

	// 更新记录时间
	cp.mu.Lock()
	cp.profileTimes[ContinuousGoroutine] = time.Now()
	cp.mu.Unlock()

	// 调用回调
	if cp.config.OnProfile != nil {
		cp.config.OnProfile(result)
	}

	return nil
}

// cleanupOldProfiles 清理旧剖析文件
func (cp *ContinuousProfiler) cleanupOldProfiles() error {
	entries, err := os.ReadDir(cp.config.OutputDir)
	if err != nil {
		return fmt.Errorf("failed to read output directory: %w", err)
	}

	cutoff := time.Now().Add(-cp.config.MaxAge)
	var totalSize int64

	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}

		info, err := entry.Info()
		if err != nil {
			continue
		}

		// 检查文件年龄
		if info.ModTime().Before(cutoff) {
			path := filepath.Join(cp.config.OutputDir, entry.Name())
			if err := os.Remove(path); err != nil {
				cp.handleError(fmt.Errorf("failed to remove old profile %s: %w", path, err))
			}
			continue
		}

		totalSize += info.Size()
	}

	// 如果超过最大大小，删除最旧的文件
	if totalSize > cp.config.MaxSize {
		if err := cp.removeOldestFiles(totalSize - cp.config.MaxSize); err != nil {
			return err
		}
	}

	return nil
}

// removeOldestFiles 删除最旧的文件
func (cp *ContinuousProfiler) removeOldestFiles(needToFree int64) error {
	type fileInfo struct {
		path    string
		modTime time.Time
		size    int64
	}

	entries, err := os.ReadDir(cp.config.OutputDir)
	if err != nil {
		return err
	}

	var files []fileInfo
	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}

		info, err := entry.Info()
		if err != nil {
			continue
		}

		files = append(files, fileInfo{
			path:    filepath.Join(cp.config.OutputDir, entry.Name()),
			modTime: info.ModTime(),
			size:    info.Size(),
		})
	}

	// 按修改时间排序
	for i := 0; i < len(files)-1; i++ {
		for j := i + 1; j < len(files); j++ {
			if files[i].modTime.After(files[j].modTime) {
				files[i], files[j] = files[j], files[i]
			}
		}
	}

	// 删除文件直到释放足够空间
	var freed int64
	for _, file := range files {
		if freed >= needToFree {
			break
		}

		if err := os.Remove(file.path); err != nil {
			cp.handleError(fmt.Errorf("failed to remove file %s: %w", file.path, err))
		} else {
			freed += file.size
		}
	}

	return nil
}

// handleError 处理错误
func (cp *ContinuousProfiler) handleError(err error) {
	if cp.config.OnError != nil {
		cp.config.OnError(err)
	}
}

// GetLastProfileTime 获取最后剖析时间
func (cp *ContinuousProfiler) GetLastProfileTime(profileType ContinuousProfileType) time.Time {
	cp.mu.RLock()
	defer cp.mu.RUnlock()
	return cp.profileTimes[profileType]
}

// GetProfileFiles 获取所有剖析文件
func (cp *ContinuousProfiler) GetProfileFiles() ([]string, error) {
	entries, err := os.ReadDir(cp.config.OutputDir)
	if err != nil {
		return nil, err
	}

	var files []string
	for _, entry := range entries {
		if !entry.IsDir() {
			files = append(files, filepath.Join(cp.config.OutputDir, entry.Name()))
		}
	}

	return files, nil
}

// GetStats 获取统计信息
func (cp *ContinuousProfiler) GetStats() (map[string]interface{}, error) {
	entries, err := os.ReadDir(cp.config.OutputDir)
	if err != nil {
		return nil, err
	}

	var totalSize int64
	var fileCount int

	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}

		info, err := entry.Info()
		if err != nil {
			continue
		}

		totalSize += info.Size()
		fileCount++
	}

	cp.mu.RLock()
	lastTimes := make(map[ContinuousProfileType]time.Time)
	for k, v := range cp.profileTimes {
		lastTimes[k] = v
	}
	cp.mu.RUnlock()

	return map[string]interface{}{
		"running":           cp.IsRunning(),
		"output_dir":        cp.config.OutputDir,
		"interval":          cp.config.Interval.String(),
		"duration":          cp.config.Duration.String(),
		"file_count":        fileCount,
		"total_size":        totalSize,
		"max_age":           cp.config.MaxAge.String(),
		"max_size":          cp.config.MaxSize,
		"last_profile_times": lastTimes,
	}, nil
}

// StartContinuousProfiler 快速启动持续剖析
func StartContinuousProfiler(config *ContinuousProfilerConfig) (*ContinuousProfiler, error) {
	profiler := NewContinuousProfiler(config)
	if err := profiler.Start(); err != nil {
		return nil, err
	}
	return profiler, nil
}

// StartWithContext 使用上下文启动持续剖析
func StartWithContext(ctx context.Context, config *ContinuousProfilerConfig) (*ContinuousProfiler, error) {
	profiler := NewContinuousProfiler(config)
	if err := profiler.Start(); err != nil {
		return nil, err
	}

	go func() {
		<-ctx.Done()
		profiler.Stop()
	}()

	return profiler, nil
}

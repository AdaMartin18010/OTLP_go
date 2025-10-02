package profiling

import (
	"context"
	"fmt"
	"net/http"
	"net/http/pprof"
	"os"
	"path/filepath"
	"runtime"
	rtpprof "runtime/pprof"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// ProfileConfig 性能分析配置
type ProfileConfig struct {
	EnableCPU    bool
	EnableMemory bool
	EnableBlock  bool
	EnableMutex  bool
	OutputDir    string
	Duration     time.Duration
}

// DefaultProfileConfig 默认配置
func DefaultProfileConfig() *ProfileConfig {
	return &ProfileConfig{
		EnableCPU:    true,
		EnableMemory: true,
		EnableBlock:  false,
		EnableMutex:  false,
		OutputDir:    "./profiles",
		Duration:     30 * time.Second,
	}
}

// Profiler 性能分析器
type Profiler struct {
	config *ProfileConfig
	tracer trace.Tracer
}

// NewProfiler 创建性能分析器
func NewProfiler(config *ProfileConfig) *Profiler {
	if config == nil {
		config = DefaultProfileConfig()
	}

	// 确保输出目录存在
	os.MkdirAll(config.OutputDir, 0755)

	return &Profiler{
		config: config,
		tracer: otel.Tracer("profiling"),
	}
}

// StartCPUProfile 启动 CPU Profiling
func (p *Profiler) StartCPUProfile(ctx context.Context) (*os.File, error) {
	ctx, span := p.tracer.Start(ctx, "profiling.start_cpu")
	defer span.End()

	filename := filepath.Join(p.config.OutputDir,
		fmt.Sprintf("cpu_%s.prof", time.Now().Format("20060102_150405")))

	f, err := os.Create(filename)
	if err != nil {
		span.RecordError(err)
		return nil, err
	}

	if err := rtpprof.StartCPUProfile(f); err != nil {
		span.RecordError(err)
		f.Close()
		return nil, err
	}

	span.SetAttributes(
		attribute.String("profile.type", "cpu"),
		attribute.String("profile.file", filename),
	)

	return f, nil
}

// StopCPUProfile 停止 CPU Profiling
func (p *Profiler) StopCPUProfile(ctx context.Context, f *os.File) error {
	ctx, span := p.tracer.Start(ctx, "profiling.stop_cpu")
	defer span.End()

	rtpprof.StopCPUProfile()

	if err := f.Close(); err != nil {
		span.RecordError(err)
		return err
	}

	return nil
}

// WriteHeapProfile 写入堆内存快照
func (p *Profiler) WriteHeapProfile(ctx context.Context) error {
	ctx, span := p.tracer.Start(ctx, "profiling.write_heap")
	defer span.End()

	filename := filepath.Join(p.config.OutputDir,
		fmt.Sprintf("heap_%s.prof", time.Now().Format("20060102_150405")))

	f, err := os.Create(filename)
	if err != nil {
		span.RecordError(err)
		return err
	}
	defer f.Close()

	// 强制 GC，获取更准确的堆快照
	runtime.GC()

	if err := rtpprof.WriteHeapProfile(f); err != nil {
		span.RecordError(err)
		return err
	}

	span.SetAttributes(
		attribute.String("profile.type", "heap"),
		attribute.String("profile.file", filename),
	)

	return nil
}

// WriteProfile 写入指定类型的 Profile
func (p *Profiler) WriteProfile(ctx context.Context, name string) error {
	ctx, span := p.tracer.Start(ctx, "profiling.write_"+name)
	defer span.End()

	profile := rtpprof.Lookup(name)
	if profile == nil {
		err := fmt.Errorf("profile not found: %s", name)
		span.RecordError(err)
		return err
	}

	filename := filepath.Join(p.config.OutputDir,
		fmt.Sprintf("%s_%s.prof", name, time.Now().Format("20060102_150405")))

	f, err := os.Create(filename)
	if err != nil {
		span.RecordError(err)
		return err
	}
	defer f.Close()

	if err := profile.WriteTo(f, 0); err != nil {
		span.RecordError(err)
		return err
	}

	span.SetAttributes(
		attribute.String("profile.type", name),
		attribute.String("profile.file", filename),
	)

	return nil
}

// RunFullProfile 运行完整的性能分析
func (p *Profiler) RunFullProfile(ctx context.Context) error {
	ctx, span := p.tracer.Start(ctx, "profiling.run_full")
	defer span.End()

	span.SetAttributes(attribute.Int64("duration.seconds", int64(p.config.Duration.Seconds())))

	// CPU Profiling
	if p.config.EnableCPU {
		cpuFile, err := p.StartCPUProfile(ctx)
		if err != nil {
			span.RecordError(err)
			return err
		}

		// 等待指定时间
		time.Sleep(p.config.Duration)

		if err := p.StopCPUProfile(ctx, cpuFile); err != nil {
			span.RecordError(err)
			return err
		}
	}

	// 堆内存快照
	if p.config.EnableMemory {
		if err := p.WriteHeapProfile(ctx); err != nil {
			span.RecordError(err)
			return err
		}
	}

	// Block Profiling
	if p.config.EnableBlock {
		runtime.SetBlockProfileRate(1)
		if err := p.WriteProfile(ctx, "block"); err != nil {
			span.RecordError(err)
		}
		runtime.SetBlockProfileRate(0)
	}

	// Mutex Profiling
	if p.config.EnableMutex {
		runtime.SetMutexProfileFraction(1)
		if err := p.WriteProfile(ctx, "mutex"); err != nil {
			span.RecordError(err)
		}
		runtime.SetMutexProfileFraction(0)
	}

	// Goroutine Profile
	if err := p.WriteProfile(ctx, "goroutine"); err != nil {
		span.RecordError(err)
	}

	span.AddEvent("profiling.completed")
	return nil
}

// EnablePprofHTTP 启用 pprof HTTP 端点
func EnablePprofHTTP(addr string) error {
	mux := http.NewServeMux()

	// 注册 pprof handlers
	mux.HandleFunc("/debug/pprof/", pprof.Index)
	mux.HandleFunc("/debug/pprof/cmdline", pprof.Cmdline)
	mux.HandleFunc("/debug/pprof/profile", pprof.Profile)
	mux.HandleFunc("/debug/pprof/symbol", pprof.Symbol)
	mux.HandleFunc("/debug/pprof/trace", pprof.Trace)

	// 启动 HTTP 服务器
	server := &http.Server{
		Addr:         addr,
		Handler:      mux,
		ReadTimeout:  5 * time.Second,
		WriteTimeout: 10 * time.Second,
	}

	go func() {
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			fmt.Printf("pprof server error: %v\n", err)
		}
	}()

	fmt.Printf("pprof server listening on %s\n", addr)
	fmt.Printf("  CPU profile: http://%s/debug/pprof/profile?seconds=30\n", addr)
	fmt.Printf("  Heap profile: http://%s/debug/pprof/heap\n", addr)
	fmt.Printf("  Goroutine profile: http://%s/debug/pprof/goroutine\n", addr)

	return nil
}

// RuntimeStats 运行时统计
type RuntimeStats struct {
	Timestamp    time.Time
	NumGoroutine int
	NumCPU       int
	GOMAXPROCS   int
	MemAlloc     uint64
	TotalAlloc   uint64
	Sys          uint64
	NumGC        uint32
	PauseTotalNs uint64
	LastGCTime   time.Time
	HeapAlloc    uint64
	HeapInuse    uint64
	StackInuse   uint64
}

// GetRuntimeStats 获取运行时统计
func GetRuntimeStats() *RuntimeStats {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)

	return &RuntimeStats{
		Timestamp:    time.Now(),
		NumGoroutine: runtime.NumGoroutine(),
		NumCPU:       runtime.NumCPU(),
		GOMAXPROCS:   runtime.GOMAXPROCS(0),
		MemAlloc:     m.Alloc,
		TotalAlloc:   m.TotalAlloc,
		Sys:          m.Sys,
		NumGC:        m.NumGC,
		PauseTotalNs: m.PauseTotalNs,
		LastGCTime:   time.Unix(0, int64(m.LastGC)),
		HeapAlloc:    m.HeapAlloc,
		HeapInuse:    m.HeapInuse,
		StackInuse:   m.StackInuse,
	}
}

// RuntimeStatsCollector 运行时统计收集器
type RuntimeStatsCollector struct {
	interval time.Duration
	tracer   trace.Tracer
	stopCh   chan struct{}
}

// NewRuntimeStatsCollector 创建统计收集器
func NewRuntimeStatsCollector(interval time.Duration) *RuntimeStatsCollector {
	return &RuntimeStatsCollector{
		interval: interval,
		tracer:   otel.Tracer("profiling/stats"),
		stopCh:   make(chan struct{}),
	}
}

// Start 启动收集
func (rsc *RuntimeStatsCollector) Start(ctx context.Context) {
	ticker := time.NewTicker(rsc.interval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			rsc.collect(ctx)
		case <-rsc.stopCh:
			return
		}
	}
}

// collect 收集统计信息
func (rsc *RuntimeStatsCollector) collect(ctx context.Context) {
	ctx, span := rsc.tracer.Start(ctx, "stats.collect")
	defer span.End()

	stats := GetRuntimeStats()

	span.SetAttributes(
		attribute.Int("goroutines", stats.NumGoroutine),
		attribute.Int("gomaxprocs", stats.GOMAXPROCS),
		attribute.Int64("mem.alloc", int64(stats.MemAlloc)),
		attribute.Int64("mem.sys", int64(stats.Sys)),
		attribute.Int("gc.count", int(stats.NumGC)),
		attribute.Int64("gc.pause_total_ns", int64(stats.PauseTotalNs)),
	)
}

// Stop 停止收集
func (rsc *RuntimeStatsCollector) Stop() {
	close(rsc.stopCh)
}

// Example: 使用示例
func ExampleProfiler() {
	ctx := context.Background()

	// 创建性能分析器
	profiler := NewProfiler(DefaultProfileConfig())

	// 运行完整的性能分析（30秒）
	if err := profiler.RunFullProfile(ctx); err != nil {
		fmt.Printf("Profiling error: %v\n", err)
	}

	fmt.Println("Profiles saved to ./profiles/")
}

// Example: 启用 pprof HTTP 服务
func ExamplePprofHTTP() {
	// 启用 pprof HTTP 端点
	if err := EnablePprofHTTP(":6060"); err != nil {
		fmt.Printf("Failed to enable pprof: %v\n", err)
	}

	// 应用继续运行...
	select {}
}

// Example: 收集运行时统计
func ExampleRuntimeStats() {
	collector := NewRuntimeStatsCollector(10 * time.Second)

	ctx := context.Background()
	go collector.Start(ctx)

	// 运行一段时间后停止
	time.Sleep(1 * time.Minute)
	collector.Stop()
}

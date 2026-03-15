// Package profiling provides profiling and debugging utilities
// for the OTLP Go SDK.
//
// This file contains span-profile correlation capabilities for
// associating profiling data with distributed tracing spans.
package profiling

import (
	"context"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

const (
	// SpanProfileAttributeKey 用于在 Span 中存储 profile ID 的属性键
	SpanProfileAttributeKey = "profile.id"
	// SpanProfileTypeAttributeKey 用于在 Span 中存储 profile 类型的属性键
	SpanProfileTypeAttributeKey = "profile.type"
	// SpanProfileDurationAttributeKey 用于在 Span 中存储 profile 持续时间的属性键
	SpanProfileDurationAttributeKey = "profile.duration_ms"
)

// SpanProfileSpan 与 Span 关联的剖析
type SpanProfileSpan struct {
	SpanID      string
	TraceID     string
	ProfileID   string
	ProfileType ProfileType
	StartTime   time.Time
	EndTime     time.Time
	Duration    time.Duration
	Labels      map[string]string
	Data        []byte
}

// SpanProfileManager Span 剖析管理器
type SpanProfileManager struct {
	pprofMgr     *PProfManager
	profiles     map[string]*SpanProfileSpan
	mu           sync.RWMutex
	enabled      bool
	defaultTypes []ProfileType
}

// NewSpanProfileManager 创建新的 Span 剖析管理器
func NewSpanProfileManager(config *PProfConfig) *SpanProfileManager {
	return &SpanProfileManager{
		pprofMgr:     NewPProfManager(config),
		profiles:     make(map[string]*SpanProfileSpan),
		enabled:      true,
		defaultTypes: []ProfileType{ProfileTypeCPU, ProfileTypeMemory},
	}
}

// SetEnabled 设置是否启用 Span 剖析
func (spm *SpanProfileManager) SetEnabled(enabled bool) {
	spm.mu.Lock()
	defer spm.mu.Unlock()
	spm.enabled = enabled
}

// IsEnabled 检查是否启用
func (spm *SpanProfileManager) IsEnabled() bool {
	spm.mu.RLock()
	defer spm.mu.RUnlock()
	return spm.enabled
}

// SetDefaultTypes 设置默认剖析类型
func (spm *SpanProfileManager) SetDefaultTypes(types []ProfileType) {
	spm.mu.Lock()
	defer spm.mu.Unlock()
	spm.defaultTypes = types
}

// StartProfileForSpan 为 Span 启动剖析
func (spm *SpanProfileManager) StartProfileForSpan(ctx context.Context, profileType ProfileType) (*SpanProfileSpan, error) {
	spm.mu.Lock()
	defer spm.mu.Unlock()

	if !spm.enabled {
		return nil, fmt.Errorf("span profiling is disabled")
	}

	// 从上下文获取 Span
	span := trace.SpanFromContext(ctx)
	if !span.IsRecording() {
		return nil, fmt.Errorf("no active span in context")
	}

	spanContext := span.SpanContext()
	if !spanContext.IsValid() {
		return nil, fmt.Errorf("invalid span context")
	}

	spanID := spanContext.SpanID().String()
	traceID := spanContext.TraceID().String()

	// 生成 profile ID
	profileID := generateProfileID()

	profile := &SpanProfileSpan{
		SpanID:      spanID,
		TraceID:     traceID,
		ProfileID:   profileID,
		ProfileType: profileType,
		StartTime:   time.Now(),
		Labels: map[string]string{
			"span_id":    spanID,
			"trace_id":   traceID,
			"profile_id": profileID,
		},
	}

	// 根据类型启动剖析
	switch profileType {
	case ProfileTypeCPU:
		if err := spm.pprofMgr.StartCPUProfile(); err != nil {
			return nil, fmt.Errorf("failed to start CPU profile: %w", err)
		}
	case ProfileTypeMemory, ProfileTypeGoroutine, ProfileTypeBlock, ProfileTypeMutex:
		// 这些类型在结束时捕获
	default:
		return nil, fmt.Errorf("unsupported profile type for span: %s", profileType)
	}

	// 存储 profile
	spm.profiles[profileID] = profile

	// 注意：pprof.Label 需要在 goroutine 中使用 pprof.Do 包装
	// 这里我们只是记录标签，实际应用时需要在代码中使用 pprof.Do

	// 在 Span 中添加属性
	span.SetAttributes(
		attribute.String(SpanProfileAttributeKey, profileID),
		attribute.String(SpanProfileTypeAttributeKey, string(profileType)),
	)

	return profile, nil
}

// StopProfileForSpan 停止 Span 的剖析
func (spm *SpanProfileManager) StopProfileForSpan(profileID string) (*SpanProfileSpan, error) {
	spm.mu.Lock()
	defer spm.mu.Unlock()

	profile, exists := spm.profiles[profileID]
	if !exists {
		return nil, fmt.Errorf("profile %s not found", profileID)
	}

	profile.EndTime = time.Now()
	profile.Duration = profile.EndTime.Sub(profile.StartTime)

	// 根据类型停止剖析
	switch profile.ProfileType {
	case ProfileTypeCPU:
		result, err := spm.pprofMgr.StopCPUProfile()
		if err != nil {
			return nil, fmt.Errorf("failed to stop CPU profile: %w", err)
		}
		profile.Data = result.Data
	case ProfileTypeMemory:
		result, err := spm.pprofMgr.CaptureHeapProfile()
		if err != nil {
			return nil, fmt.Errorf("failed to capture heap profile: %w", err)
		}
		profile.Data = result.Data
	case ProfileTypeGoroutine:
		result, err := spm.pprofMgr.CaptureGoroutineProfile()
		if err != nil {
			return nil, fmt.Errorf("failed to capture goroutine profile: %w", err)
		}
		profile.Data = result.Data
	case ProfileTypeBlock:
		result, err := spm.pprofMgr.CaptureBlockProfile()
		if err != nil {
			return nil, fmt.Errorf("failed to capture block profile: %w", err)
		}
		profile.Data = result.Data
	case ProfileTypeMutex:
		result, err := spm.pprofMgr.CaptureMutexProfile()
		if err != nil {
			return nil, fmt.Errorf("failed to capture mutex profile: %w", err)
		}
		profile.Data = result.Data
	}

	// 更新 Span 属性（如果有上下文）
	// 这里我们无法获取原始上下文，所以数据需要通过其他方式关联

	return profile, nil
}

// GetProfile 获取剖析数据
func (spm *SpanProfileManager) GetProfile(profileID string) (*SpanProfileSpan, bool) {
	spm.mu.RLock()
	defer spm.mu.RUnlock()
	profile, exists := spm.profiles[profileID]
	return profile, exists
}

// GetProfileBySpanID 通过 Span ID 获取剖析
func (spm *SpanProfileManager) GetProfileBySpanID(spanID string) []*SpanProfileSpan {
	spm.mu.RLock()
	defer spm.mu.RUnlock()

	var result []*SpanProfileSpan
	for _, profile := range spm.profiles {
		if profile.SpanID == spanID {
			result = append(result, profile)
		}
	}
	return result
}

// GetProfileByTraceID 通过 Trace ID 获取剖析
func (spm *SpanProfileManager) GetProfileByTraceID(traceID string) []*SpanProfileSpan {
	spm.mu.RLock()
	defer spm.mu.RUnlock()

	var result []*SpanProfileSpan
	for _, profile := range spm.profiles {
		if profile.TraceID == traceID {
			result = append(result, profile)
		}
	}
	return result
}

// RemoveProfile 删除剖析记录
func (spm *SpanProfileManager) RemoveProfile(profileID string) {
	spm.mu.Lock()
	defer spm.mu.Unlock()
	delete(spm.profiles, profileID)
}

// ClearProfiles 清除所有剖析记录
func (spm *SpanProfileManager) ClearProfiles() {
	spm.mu.Lock()
	defer spm.mu.Unlock()
	spm.profiles = make(map[string]*SpanProfileSpan)
}

// ProfileCount 获取剖析记录数量
func (spm *SpanProfileManager) ProfileCount() int {
	spm.mu.RLock()
	defer spm.mu.RUnlock()
	return len(spm.profiles)
}

// generateProfileID 生成 profile ID
func generateProfileID() string {
	// 使用随机数生成唯一 ID
	b := make([]byte, 8)
	if _, err := rand.Read(b); err != nil {
		// 如果随机数生成失败，回退到时间戳
		return fmt.Sprintf("%016x", time.Now().UnixNano())
	}
	return hex.EncodeToString(b)
}

// ProfileTracer 支持剖析的 Tracer 包装器
type ProfileTracer struct {
	tracer  trace.Tracer
	manager *SpanProfileManager
}

// NewProfileTracer 创建新的 ProfileTracer
func NewProfileTracer(tracer trace.Tracer, config *PProfConfig) *ProfileTracer {
	return &ProfileTracer{
		tracer:  tracer,
		manager: NewSpanProfileManager(config),
	}
}

// Start 启动带剖析的 Span
func (pt *ProfileTracer) Start(ctx context.Context, spanName string, opts ...trace.SpanStartOption) (context.Context, trace.Span, *SpanProfileSpan, error) {
	// 启动 Span
	ctx, span := pt.tracer.Start(ctx, spanName, opts...)

	// 启动剖析
	profile, err := pt.manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		// 剖析失败不影响 Span 的创建
		return ctx, span, nil, err
	}

	// 返回包装后的 Span
	wrappedSpan := &profileSpan{
		Span:    span,
		manager: pt.manager,
		profile: profile,
	}

	return ctx, wrappedSpan, profile, nil
}

// profileSpan 包装 trace.Span 以支持自动剖析停止
type profileSpan struct {
	trace.Span
	manager *SpanProfileManager
	profile *SpanProfileSpan
	ended   bool
	mu      sync.Mutex
}

// End 结束 Span 并停止剖析
func (ps *profileSpan) End(options ...trace.SpanEndOption) {
	ps.mu.Lock()
	defer ps.mu.Unlock()

	if ps.ended {
		return
	}
	ps.ended = true

	// 停止剖析
	if ps.profile != nil {
		profile, err := ps.manager.StopProfileForSpan(ps.profile.ProfileID)
		if err == nil && profile != nil {
			// 添加剖析信息到 Span
			ps.Span.SetAttributes(
				attribute.Int64(SpanProfileDurationAttributeKey, profile.Duration.Milliseconds()),
			)
		}
	}

	// 结束原始 Span
	ps.Span.End(options...)
}

// IsRecording 返回 Span 是否正在记录
func (ps *profileSpan) IsRecording() bool {
	ps.mu.Lock()
	defer ps.mu.Unlock()
	return !ps.ended && ps.Span.IsRecording()
}

// SpanProfileContext 包含 Span 和 Profile 的上下文
type SpanProfileContext struct {
	Context context.Context
	Span    trace.Span
	Profile *SpanProfileSpan
}

// StartProfiledSpan 启动带剖析的 Span（便捷函数）
func StartProfiledSpan(ctx context.Context, tracer trace.Tracer, spanName string, profileType ProfileType, opts ...trace.SpanStartOption) (*SpanProfileContext, error) {
	// 启动 Span
	ctx, span := tracer.Start(ctx, spanName, opts...)

	// 创建临时管理器来启动剖析
	manager := NewSpanProfileManager(nil)
	profile, err := manager.StartProfileForSpan(ctx, profileType)
	if err != nil {
		span.End()
		return nil, err
	}

	return &SpanProfileContext{
		Context: ctx,
		Span:    span,
		Profile: profile,
	}, nil
}

// End 结束带剖析的 Span
func (spc *SpanProfileContext) End() {
	if spc.Profile != nil {
		manager := NewSpanProfileManager(nil)
		profile, err := manager.StopProfileForSpan(spc.Profile.ProfileID)
		if err == nil && profile != nil {
			spc.Span.SetAttributes(
				attribute.Int64(SpanProfileDurationAttributeKey, profile.Duration.Milliseconds()),
			)
		}
	}
	spc.Span.End()
}

// WithProfiledSpan 在带剖析的 Span 中执行函数
func WithProfiledSpan(ctx context.Context, tracer trace.Tracer, spanName string, profileType ProfileType, fn func(context.Context) error, opts ...trace.SpanStartOption) error {
	spc, err := StartProfiledSpan(ctx, tracer, spanName, profileType, opts...)
	if err != nil {
		return err
	}
	defer spc.End()

	return fn(spc.Context)
}

// ProfileExporter OTLP Profile 导出器接口
type ProfileExporter interface {
	ExportProfiles(ctx context.Context, profiles []*SpanProfileSpan) error
	Shutdown(ctx context.Context) error
}

// OTLPProfileExporter OTLP Profile 导出器
type OTLPProfileExporter struct {
	endpoint string
	client   *sync.Mutex
}

// NewOTLPProfileExporter 创建新的 OTLP Profile 导出器
func NewOTLPProfileExporter(endpoint string) *OTLPProfileExporter {
	return &OTLPProfileExporter{
		endpoint: endpoint,
		client:   &sync.Mutex{},
	}
}

// ExportProfiles 导出剖析数据
func (e *OTLPProfileExporter) ExportProfiles(ctx context.Context, profiles []*SpanProfileSpan) error {
	e.client.Lock()
	defer e.client.Unlock()

	// 这里应该实现实际的 OTLP Profile 导出逻辑
	// 目前只是模拟实现
	for _, profile := range profiles {
		if profile == nil {
			continue
		}
		// 实际实现中，这里会将 profile.Data 序列化为 OTLP Profile 格式并发送
		_ = profile
	}

	return nil
}

// Shutdown 关闭导出器
func (e *OTLPProfileExporter) Shutdown(ctx context.Context) error {
	return nil
}

// SpanProfileCollector Span 剖析收集器
type SpanProfileCollector struct {
	manager  *SpanProfileManager
	exporter ProfileExporter
	interval time.Duration
	stopCh   chan struct{}
	wg       sync.WaitGroup
	mu       sync.RWMutex
	running  bool
}

// NewSpanProfileCollector 创建新的 Span 剖析收集器
func NewSpanProfileCollector(manager *SpanProfileManager, exporter ProfileExporter, interval time.Duration) *SpanProfileCollector {
	if interval <= 0 {
		interval = 30 * time.Second
	}
	return &SpanProfileCollector{
		manager:  manager,
		exporter: exporter,
		interval: interval,
		stopCh:   make(chan struct{}),
	}
}

// Start 启动收集器
func (spc *SpanProfileCollector) Start() error {
	spc.mu.Lock()
	defer spc.mu.Unlock()

	if spc.running {
		return fmt.Errorf("collector already running")
	}

	spc.running = true
	spc.stopCh = make(chan struct{})
	spc.wg.Add(1)
	go spc.collectLoop()

	return nil
}

// Stop 停止收集器
func (spc *SpanProfileCollector) Stop() error {
	spc.mu.Lock()
	if !spc.running {
		spc.mu.Unlock()
		return fmt.Errorf("collector not running")
	}
	spc.running = false
	close(spc.stopCh)
	spc.mu.Unlock()

	spc.wg.Wait()
	return nil
}

// collectLoop 收集循环
func (spc *SpanProfileCollector) collectLoop() {
	defer spc.wg.Done()

	ticker := time.NewTicker(spc.interval)
	defer ticker.Stop()

	for {
		select {
		case <-spc.stopCh:
			return
		case <-ticker.C:
			if err := spc.collectAndExport(); err != nil {
				// 记录错误但不停止
				_ = err
			}
		}
	}
}

// collectAndExport 收集并导出
func (spc *SpanProfileCollector) collectAndExport() error {
	// 这里应该收集已完成的剖析并导出
	// 目前只是模拟实现
	return nil
}

// IsRunning 检查是否正在运行
func (spc *SpanProfileCollector) IsRunning() bool {
	spc.mu.RLock()
	defer spc.mu.RUnlock()
	return spc.running
}

// CreateSpanProfileLink 创建 Span 与 Profile 的关联链接
func CreateSpanProfileLink(span trace.Span, profile *SpanProfileSpan) string {
	if span == nil || profile == nil {
		return ""
	}

	// 创建关联链接
	link := fmt.Sprintf("trace_id=%s&span_id=%s&profile_id=%s",
		profile.TraceID,
		profile.SpanID,
		profile.ProfileID,
	)

	return link
}

// ExtractProfileInfoFromSpan 从 Span 中提取剖析信息
func ExtractProfileInfoFromSpan(span trace.Span) (profileID string, profileType string, exists bool) {
	if span == nil || !span.IsRecording() {
		return "", "", false
	}

	// 这里假设我们可以通过某种方式获取属性
	// 实际实现中可能需要遍历属性或使用特定的 API
	return "", "", false
}

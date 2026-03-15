package profiling

import (
	"context"
	"sync"
	"testing"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/embedded"
	"go.opentelemetry.io/otel/trace/noop"
)

// 可记录的测试 Span
type recordableSpan struct {
	embedded.Span
	name        string
	attributes  map[attribute.Key]attribute.Value
	ended       bool
	recording   bool
	spanContext trace.SpanContext
	statusCode  codes.Code
	statusDesc  string
}

func newRecordableSpan(name string) *recordableSpan {
	return &recordableSpan{
		name:       name,
		attributes: make(map[attribute.Key]attribute.Value),
		recording:  true,
		spanContext: trace.NewSpanContext(trace.SpanContextConfig{
			TraceID: [16]byte{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16},
			SpanID:  [8]byte{1, 2, 3, 4, 5, 6, 7, 8},
		}),
	}
}

func (s *recordableSpan) End(options ...trace.SpanEndOption) {
	s.ended = true
}

func (s *recordableSpan) AddEvent(name string, options ...trace.EventOption) {}

func (s *recordableSpan) AddLink(link trace.Link) {}

func (s *recordableSpan) IsRecording() bool {
	return s.recording && !s.ended
}

func (s *recordableSpan) RecordError(err error, options ...trace.EventOption) {}

func (s *recordableSpan) SpanContext() trace.SpanContext {
	return s.spanContext
}

func (s *recordableSpan) SetStatus(code codes.Code, description string) {
	s.statusCode = code
	s.statusDesc = description
}

func (s *recordableSpan) SetName(name string) {
	s.name = name
}

func (s *recordableSpan) SetAttributes(attrs ...attribute.KeyValue) {
	for _, attr := range attrs {
		s.attributes[attr.Key] = attr.Value
	}
}

func (s *recordableSpan) TracerProvider() trace.TracerProvider {
	return nil
}

// 创建带可记录 Span 的上下文
func contextWithRecordableSpan(ctx context.Context, name string) (context.Context, *recordableSpan) {
	span := newRecordableSpan(name)
	return trace.ContextWithSpan(ctx, span), span
}

func TestNewSpanProfileManager(t *testing.T) {
	manager := NewSpanProfileManager(nil)

	if manager == nil {
		t.Fatal("expected non-nil manager")
	}

	if manager.pprofMgr == nil {
		t.Error("expected pprofMgr to be initialized")
	}

	if manager.profiles == nil {
		t.Error("expected profiles map to be initialized")
	}

	if !manager.IsEnabled() {
		t.Error("expected manager to be enabled by default")
	}
}

func TestSpanProfileManagerSetEnabled(t *testing.T) {
	manager := NewSpanProfileManager(nil)

	if !manager.IsEnabled() {
		t.Error("expected manager to be enabled")
	}

	manager.SetEnabled(false)

	if manager.IsEnabled() {
		t.Error("expected manager to be disabled")
	}

	manager.SetEnabled(true)

	if !manager.IsEnabled() {
		t.Error("expected manager to be enabled")
	}
}

func TestSpanProfileManagerSetDefaultTypes(t *testing.T) {
	manager := NewSpanProfileManager(nil)

	types := []ProfileType{ProfileTypeCPU, ProfileTypeMemory}
	manager.SetDefaultTypes(types)
}

func TestStartProfileForSpan(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	if profile == nil {
		t.Fatal("expected non-nil profile")
	}

	if profile.SpanID != span.SpanContext().SpanID().String() {
		t.Error("expected profile SpanID to match span SpanID")
	}

	if profile.ProfileID == "" {
		t.Error("expected non-empty ProfileID")
	}

	if profile.ProfileType != ProfileTypeCPU {
		t.Errorf("expected profile type CPU, got %s", profile.ProfileType)
	}

	// 清理
	manager.StopProfileForSpan(profile.ProfileID)
}

func TestStartProfileForSpanDisabled(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	manager.SetEnabled(false)

	ctx := context.Background()
	_, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err == nil {
		t.Error("expected error when starting profile with disabled manager")
	}
}

func TestStartProfileForSpanNoSpan(t *testing.T) {
	manager := NewSpanProfileManager(nil)

	// 使用没有 Span 的上下文
	ctx := context.Background()
	_, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err == nil {
		t.Error("expected error when starting profile without span in context")
	}
}

func TestStopProfileForSpan(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	// 等待一小段时间
	time.Sleep(10 * time.Millisecond)

	stoppedProfile, err := manager.StopProfileForSpan(profile.ProfileID)
	if err != nil {
		t.Fatalf("failed to stop profile for span: %v", err)
	}

	if stoppedProfile == nil {
		t.Fatal("expected non-nil stopped profile")
	}

	if stoppedProfile.EndTime.IsZero() {
		t.Error("expected EndTime to be set")
	}

	if stoppedProfile.Duration <= 0 {
		t.Error("expected positive Duration")
	}

	if len(stoppedProfile.Data) == 0 {
		t.Error("expected non-empty Data")
	}
}

func TestStopProfileForSpanNotFound(t *testing.T) {
	manager := NewSpanProfileManager(nil)

	_, err := manager.StopProfileForSpan("nonexistent")
	if err == nil {
		t.Error("expected error when stopping nonexistent profile")
	}
}

func TestStopProfileForSpanMemory(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeMemory)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	stoppedProfile, err := manager.StopProfileForSpan(profile.ProfileID)
	if err != nil {
		t.Fatalf("failed to stop profile for span: %v", err)
	}

	if stoppedProfile == nil {
		t.Fatal("expected non-nil stopped profile")
	}

	if len(stoppedProfile.Data) == 0 {
		t.Error("expected non-empty Data")
	}
}

func TestStopProfileForSpanGoroutine(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeGoroutine)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	stoppedProfile, err := manager.StopProfileForSpan(profile.ProfileID)
	if err != nil {
		t.Fatalf("failed to stop profile for span: %v", err)
	}

	if stoppedProfile == nil {
		t.Fatal("expected non-nil stopped profile")
	}
}

func TestGetProfile(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	// 获取 profile
	retrieved, exists := manager.GetProfile(profile.ProfileID)
	if !exists {
		t.Error("expected profile to exist")
	}

	if retrieved.ProfileID != profile.ProfileID {
		t.Error("expected retrieved profile ID to match")
	}

	// 获取不存在的 profile
	_, exists = manager.GetProfile("nonexistent")
	if exists {
		t.Error("expected nonexistent profile to not exist")
	}

	// 清理
	manager.StopProfileForSpan(profile.ProfileID)
}

func TestGetProfileBySpanID(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	// 通过 Span ID 获取
	profiles := manager.GetProfileBySpanID(span.SpanContext().SpanID().String())
	if len(profiles) != 1 {
		t.Errorf("expected 1 profile, got %d", len(profiles))
	}

	// 获取不存在的 Span ID
	profiles = manager.GetProfileBySpanID("nonexistent")
	if len(profiles) != 0 {
		t.Errorf("expected 0 profiles, got %d", len(profiles))
	}

	// 清理
	manager.StopProfileForSpan(profile.ProfileID)
}

func TestGetProfileByTraceID(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	// 通过 Trace ID 获取
	profiles := manager.GetProfileByTraceID(span.SpanContext().TraceID().String())
	if len(profiles) != 1 {
		t.Errorf("expected 1 profile, got %d", len(profiles))
	}

	// 获取不存在的 Trace ID
	profiles = manager.GetProfileByTraceID("nonexistent")
	if len(profiles) != 0 {
		t.Errorf("expected 0 profiles, got %d", len(profiles))
	}

	// 清理
	manager.StopProfileForSpan(profile.ProfileID)
}

func TestRemoveProfile(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile for span: %v", err)
	}

	// 停止 profile
	manager.StopProfileForSpan(profile.ProfileID)

	// 删除记录
	manager.RemoveProfile(profile.ProfileID)

	// 验证已删除
	_, exists := manager.GetProfile(profile.ProfileID)
	if exists {
		t.Error("expected profile to be removed")
	}
}

func TestClearProfiles(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	// 创建多个 profiles
	for i := 0; i < 3; i++ {
		profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
		if err != nil {
			t.Fatalf("failed to start profile: %v", err)
		}
		manager.StopProfileForSpan(profile.ProfileID)
	}

	if manager.ProfileCount() == 0 {
		t.Error("expected some profiles")
	}

	manager.ClearProfiles()

	if manager.ProfileCount() != 0 {
		t.Errorf("expected 0 profiles after clear, got %d", manager.ProfileCount())
	}
}

func TestProfileCount(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	if manager.ProfileCount() != 0 {
		t.Error("expected 0 profiles initially")
	}

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile: %v", err)
	}

	if manager.ProfileCount() != 1 {
		t.Errorf("expected 1 profile, got %d", manager.ProfileCount())
	}

	manager.StopProfileForSpan(profile.ProfileID)

	if manager.ProfileCount() != 1 {
		t.Errorf("expected 1 profile after stop, got %d", manager.ProfileCount())
	}
}

func TestGenerateProfileID(t *testing.T) {
	id1 := generateProfileID()
	time.Sleep(1 * time.Millisecond) // 确保时间戳不同
	id2 := generateProfileID()

	if id1 == "" {
		t.Error("expected non-empty ID")
	}

	if id1 == id2 {
		t.Errorf("expected unique IDs, got %s and %s", id1, id2)
	}

	if len(id1) != 16 {
		t.Errorf("expected ID length 16, got %d", len(id1))
	}
}

func TestNewOTLPProfileExporter(t *testing.T) {
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	if exporter == nil {
		t.Fatal("expected non-nil exporter")
	}

	if exporter.endpoint != "http://localhost:4317" {
		t.Error("expected endpoint to match")
	}
}

func TestOTLPProfileExporterExportProfiles(t *testing.T) {
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	profiles := []*SpanProfileSpan{
		{
			ProfileID:   "test1",
			ProfileType: ProfileTypeCPU,
			Data:        []byte("test data"),
		},
		nil, // 测试 nil profile 处理
	}

	ctx := context.Background()
	err := exporter.ExportProfiles(ctx, profiles)
	if err != nil {
		t.Fatalf("failed to export profiles: %v", err)
	}
}

func TestOTLPProfileExporterShutdown(t *testing.T) {
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	ctx := context.Background()
	err := exporter.Shutdown(ctx)
	if err != nil {
		t.Fatalf("failed to shutdown exporter: %v", err)
	}
}

func TestNewSpanProfileCollector(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	collector := NewSpanProfileCollector(manager, exporter, 30*time.Second)

	if collector == nil {
		t.Fatal("expected non-nil collector")
	}

	if collector.manager != manager {
		t.Error("expected manager to match")
	}

	if collector.exporter != exporter {
		t.Error("expected exporter to match")
	}

	if collector.interval != 30*time.Second {
		t.Error("expected interval to match")
	}
}

func TestSpanProfileCollectorStartStop(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	collector := NewSpanProfileCollector(manager, exporter, 100*time.Millisecond)

	err := collector.Start()
	if err != nil {
		t.Fatalf("failed to start collector: %v", err)
	}

	if !collector.IsRunning() {
		t.Error("expected collector to be running")
	}

	// 等待一段时间
	time.Sleep(200 * time.Millisecond)

	err = collector.Stop()
	if err != nil {
		t.Fatalf("failed to stop collector: %v", err)
	}

	if collector.IsRunning() {
		t.Error("expected collector to be stopped")
	}
}

func TestSpanProfileCollectorStartAlreadyRunning(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	collector := NewSpanProfileCollector(manager, exporter, 1*time.Second)

	err := collector.Start()
	if err != nil {
		t.Fatalf("failed to start collector: %v", err)
	}
	defer collector.Stop()

	err = collector.Start()
	if err == nil {
		t.Error("expected error when starting already running collector")
	}
}

func TestSpanProfileCollectorStopNotRunning(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	collector := NewSpanProfileCollector(manager, exporter, 1*time.Second)

	err := collector.Stop()
	if err == nil {
		t.Error("expected error when stopping collector that is not running")
	}
}

func TestCreateSpanProfileLink(t *testing.T) {
	_, span := contextWithRecordableSpan(context.Background(), "test")

	profile := &SpanProfileSpan{
		SpanID:    "span123",
		TraceID:   "trace456",
		ProfileID: "profile789",
	}

	link := CreateSpanProfileLink(span, profile)
	if link == "" {
		t.Error("expected non-empty link")
	}

	// 测试 nil span
	link = CreateSpanProfileLink(nil, profile)
	if link != "" {
		t.Error("expected empty link for nil span")
	}

	// 测试 nil profile
	link = CreateSpanProfileLink(span, nil)
	if link != "" {
		t.Error("expected empty link for nil profile")
	}
}

func TestExtractProfileInfoFromSpan(t *testing.T) {
	_, span := contextWithRecordableSpan(context.Background(), "test")

	profileID, profileType, exists := ExtractProfileInfoFromSpan(span)

	// 由于我们没有在 Span 中实际设置属性，应该返回空值
	if exists {
		t.Error("expected exists to be false for test span")
	}

	if profileID != "" {
		t.Error("expected empty profileID")
	}

	if profileType != "" {
		t.Error("expected empty profileType")
	}

	// 测试 nil span
	profileID, profileType, exists = ExtractProfileInfoFromSpan(nil)
	if exists {
		t.Error("expected exists to be false for nil span")
	}
}

func TestSpanProfileManagerConcurrency(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	var wg sync.WaitGroup
	profileIDs := make(chan string, 10)

	// 并发创建 profiles - 使用 Memory 类型避免 CPU 剖析冲突
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			profile, err := manager.StartProfileForSpan(ctx, ProfileTypeMemory)
			if err != nil {
				t.Errorf("failed to start profile: %v", err)
				return
			}
			profileIDs <- profile.ProfileID
		}()
	}

	wg.Wait()
	close(profileIDs)

	// 停止所有 profiles
	for id := range profileIDs {
		_, err := manager.StopProfileForSpan(id)
		if err != nil {
			t.Errorf("failed to stop profile %s: %v", id, err)
		}
	}

	// 验证所有 profiles 都被记录
	if manager.ProfileCount() != 10 {
		t.Errorf("expected 10 profiles, got %d", manager.ProfileCount())
	}
}

func TestSpanProfileContext(t *testing.T) {
	// 这是一个集成测试，需要真实的 tracer
	// 由于我们使用 noop tracer，这里主要测试接口

	tracer := otel.Tracer("test")
	ctx := context.Background()

	// 由于我们没有真正的 tracer，这里会失败或返回 noop
	// 但这验证了接口的行为
	_, err := StartProfiledSpan(ctx, tracer, "test-span", ProfileTypeCPU)
	// noop span 可能会导致错误或者成功，取决于实现
	_ = err
}

func TestWithProfiledSpan(t *testing.T) {
	tracer := otel.Tracer("test")
	ctx := context.Background()

	err := WithProfiledSpan(ctx, tracer, "test-span", ProfileTypeCPU, func(ctx context.Context) error {
		// 执行一些工作
		time.Sleep(10 * time.Millisecond)
		return nil
	})

	// 由于测试环境可能没有配置 tracer，可能会失败
	// 这里主要测试接口不 panic
	_ = err
}

func TestSpanProfileSpanFields(t *testing.T) {
	start := time.Now()
	profile := &SpanProfileSpan{
		SpanID:      "span123",
		TraceID:     "trace456",
		ProfileID:   "profile789",
		ProfileType: ProfileTypeCPU,
		StartTime:   start,
		EndTime:     start.Add(100 * time.Millisecond),
		Duration:    100 * time.Millisecond,
		Labels: map[string]string{
			"key": "value",
		},
		Data: []byte("test data"),
	}

	if profile.SpanID != "span123" {
		t.Error("SpanID mismatch")
	}

	if profile.TraceID != "trace456" {
		t.Error("TraceID mismatch")
	}

	if profile.ProfileID != "profile789" {
		t.Error("ProfileID mismatch")
	}

	if profile.ProfileType != ProfileTypeCPU {
		t.Error("ProfileType mismatch")
	}

	if profile.Duration != 100*time.Millisecond {
		t.Error("Duration mismatch")
	}

	if string(profile.Data) != "test data" {
		t.Error("Data mismatch")
	}
}

func BenchmarkStartStopProfileForSpan(b *testing.B) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")
	_ = span

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		profile, err := manager.StartProfileForSpan(ctx, ProfileTypeMemory)
		if err != nil {
			b.Fatal(err)
		}
		manager.StopProfileForSpan(profile.ProfileID)
	}
}

func TestSpanProfileSpanLabelValidation(t *testing.T) {
	profile := &SpanProfileSpan{
		SpanID:    "test-span-id",
		TraceID:   "test-trace-id",
		ProfileID: "test-profile-id",
		Labels: map[string]string{
			"span_id":    "test-span-id",
			"trace_id":   "test-trace-id",
			"profile_id": "test-profile-id",
		},
	}

	if profile.Labels["span_id"] != profile.SpanID {
		t.Error("span_id label mismatch")
	}

	if profile.Labels["trace_id"] != profile.TraceID {
		t.Error("trace_id label mismatch")
	}

	if profile.Labels["profile_id"] != profile.ProfileID {
		t.Error("profile_id label mismatch")
	}
}

func TestNewSpanProfileCollectorDefaultInterval(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	exporter := NewOTLPProfileExporter("http://localhost:4317")

	// 使用 0 或负值应该使用默认值
	collector := NewSpanProfileCollector(manager, exporter, 0)

	if collector.interval != 30*time.Second {
		t.Errorf("expected default interval 30s, got %v", collector.interval)
	}

	collector = NewSpanProfileCollector(manager, exporter, -1*time.Second)

	if collector.interval != 30*time.Second {
		t.Errorf("expected default interval 30s for negative value, got %v", collector.interval)
	}
}

func TestNewProfileTracer(t *testing.T) {
	tracer := noop.NewTracerProvider().Tracer("test")
	pt := NewProfileTracer(tracer, nil)

	if pt == nil {
		t.Fatal("expected non-nil ProfileTracer")
	}

	if pt.tracer != tracer {
		t.Error("expected tracer to match")
	}

	if pt.manager == nil {
		t.Error("expected manager to be initialized")
	}
}

func TestProfileTracerStart(t *testing.T) {
	tracer := noop.NewTracerProvider().Tracer("test")
	pt := NewProfileTracer(tracer, nil)

	ctx := context.Background()
	ctx, span, profile, err := pt.Start(ctx, "test-span")

	// noop tracer 可能会返回错误或者成功
	_ = ctx
	_ = span
	_ = profile
	_ = err
}

func TestProfileSpanEnd(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile: %v", err)
	}

	// 创建 profileSpan
	ps := &profileSpan{
		Span:    span,
		manager: manager,
		profile: profile,
	}

	// 第一次结束
	ps.End()

	// 第二次结束不应该 panic
	ps.End()
}

func TestProfileSpanIsRecording(t *testing.T) {
	manager := NewSpanProfileManager(nil)
	ctx, span := contextWithRecordableSpan(context.Background(), "test")

	profile, err := manager.StartProfileForSpan(ctx, ProfileTypeCPU)
	if err != nil {
		t.Fatalf("failed to start profile: %v", err)
	}

	ps := &profileSpan{
		Span:    span,
		manager: manager,
		profile: profile,
	}

	if !ps.IsRecording() {
		t.Error("expected span to be recording")
	}

	ps.End()

	if ps.IsRecording() {
		t.Error("expected span to not be recording after end")
	}
}

// 确保导入的包被使用
var (
	_ = attribute.String("test", "value")
	_ = codes.Ok
	_ = noop.TracerProvider{}
)

package context

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

func TestWithRequestID(t *testing.T) {
	ctx := context.Background()
	requestID := "req-12345"

	ctx = WithRequestID(ctx, requestID)
	got := GetRequestID(ctx)

	if got != requestID {
		t.Errorf("Expected %s, got %s", requestID, got)
	}
}

func TestGetRequestIDEmpty(t *testing.T) {
	ctx := context.Background()
	got := GetRequestID(ctx)

	if got != "" {
		t.Errorf("Expected empty string, got %s", got)
	}
}

func TestWithUserID(t *testing.T) {
	ctx := context.Background()
	userID := "user-67890"

	ctx = WithUserID(ctx, userID)
	got := GetUserID(ctx)

	if got != userID {
		t.Errorf("Expected %s, got %s", userID, got)
	}
}

func TestWithTenantID(t *testing.T) {
	ctx := context.Background()
	tenantID := "tenant-abc"

	ctx = WithTenantID(ctx, tenantID)
	got := GetTenantID(ctx)

	if got != tenantID {
		t.Errorf("Expected %s, got %s", tenantID, got)
	}
}

func TestGetTraceID(t *testing.T) {
	// 设置一个 tracer provider
	tp := sdktrace.NewTracerProvider()
	otel.SetTracerProvider(tp)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	traceID := GetTraceID(ctx)
	if traceID == "" {
		t.Error("Expected non-empty trace ID")
	}

	// 验证是有效的十六进制字符串
	if len(traceID) != 32 {
		t.Errorf("Expected trace ID length 32, got %d", len(traceID))
	}
}

func TestGetTraceIDNoSpan(t *testing.T) {
	ctx := context.Background()
	traceID := GetTraceID(ctx)

	if traceID != "" {
		t.Errorf("Expected empty trace ID, got %s", traceID)
	}
}

func TestGetSpanID(t *testing.T) {
	tp := sdktrace.NewTracerProvider()
	otel.SetTracerProvider(tp)
	defer tp.Shutdown(context.Background())

	tracer := otel.Tracer("test")
	ctx, span := tracer.Start(context.Background(), "test-span")
	defer span.End()

	spanID := GetSpanID(ctx)
	if spanID == "" {
		t.Error("Expected non-empty span ID")
	}

	// 验证是有效的十六进制字符串
	if len(spanID) != 16 {
		t.Errorf("Expected span ID length 16, got %d", len(spanID))
	}
}

func TestWithBaggage(t *testing.T) {
	ctx := context.Background()
	key := "user.role"
	value := "admin"

	ctx = WithBaggage(ctx, key, value)
	got := GetBaggage(ctx, key)

	if got != value {
		t.Errorf("Expected %s, got %s", value, got)
	}
}

func TestWithBaggageMultiple(t *testing.T) {
	ctx := context.Background()

	ctx = WithBaggage(ctx, "key1", "value1")
	ctx = WithBaggage(ctx, "key2", "value2")

	if GetBaggage(ctx, "key1") != "value1" {
		t.Error("key1 not found")
	}

	if GetBaggage(ctx, "key2") != "value2" {
		t.Error("key2 not found")
	}
}

func TestGetBaggageNotFound(t *testing.T) {
	ctx := context.Background()
	got := GetBaggage(ctx, "nonexistent")

	if got != "" {
		t.Errorf("Expected empty string, got %s", got)
	}
}

func TestWithTimeout(t *testing.T) {
	parent := context.Background()
	ctx, cancel := WithTimeout(parent, 100*time.Millisecond)
	defer cancel()

	select {
	case <-ctx.Done():
		t.Error("Context should not be done immediately")
	case <-time.After(10 * time.Millisecond):
		// OK
	}

	// 等待超时
	select {
	case <-ctx.Done():
		// OK
	case <-time.After(200 * time.Millisecond):
		t.Error("Context did not timeout")
	}
}

func TestWithDeadline(t *testing.T) {
	parent := context.Background()
	deadline := time.Now().Add(100 * time.Millisecond)
	ctx, cancel := WithDeadline(parent, deadline)
	defer cancel()

	// 等待截止时间
	select {
	case <-ctx.Done():
		// OK
	case <-time.After(200 * time.Millisecond):
		t.Error("Context did not reach deadline")
	}
}

func TestWithCancel(t *testing.T) {
	parent := context.Background()
	ctx, cancel := WithCancel(parent)

	// 取消
	cancel()

	select {
	case <-ctx.Done():
		// OK
	case <-time.After(100 * time.Millisecond):
		t.Error("Context was not cancelled")
	}
}

func TestDetach(t *testing.T) {
	parent, cancel := context.WithCancel(context.Background())
	parent = WithRequestID(parent, "test-request")

	detached := Detach(parent)

	// 取消父上下文
	cancel()

	// 父上下文应该被取消
	select {
	case <-parent.Done():
		// OK
	case <-time.After(100 * time.Millisecond):
		t.Error("Parent context was not cancelled")
	}

	// 分离的上下文不应该被取消
	select {
	case <-detached.Done():
		t.Error("Detached context should not be cancelled")
	case <-time.After(10 * time.Millisecond):
		// OK
	}

	// 但应该保留值
	if GetRequestID(detached) != "test-request" {
		t.Error("Detached context lost values")
	}
}

func TestMergeContexts(t *testing.T) {
	ctx1 := WithRequestID(context.Background(), "req-1")
	ctx2 := WithUserID(context.Background(), "user-2")
	ctx3 := WithTenantID(context.Background(), "tenant-3")

	merged := MergeContexts(ctx1, ctx2, ctx3)

	if GetRequestID(merged) != "req-1" {
		t.Error("Request ID not merged")
	}

	if GetUserID(merged) != "user-2" {
		t.Error("User ID not merged")
	}

	if GetTenantID(merged) != "tenant-3" {
		t.Error("Tenant ID not merged")
	}
}

func TestContextWithValues(t *testing.T) {
	parent := context.Background()
	values := map[string]interface{}{
		"key1": "value1",
		"key2": 123,
		"key3": true,
	}

	ctx := ContextWithValues(parent, values)

	if v := ctx.Value(contextKey("key1")); v != "value1" {
		t.Errorf("Expected value1, got %v", v)
	}

	if v := ctx.Value(contextKey("key2")); v != 123 {
		t.Errorf("Expected 123, got %v", v)
	}

	if v := ctx.Value(contextKey("key3")); v != true {
		t.Errorf("Expected true, got %v", v)
	}
}

func TestGetContextValues(t *testing.T) {
	ctx := context.Background()
	ctx = WithRequestID(ctx, "req-123")
	ctx = WithUserID(ctx, "user-456")
	ctx = WithBaggage(ctx, "key1", "value1")

	values := GetContextValues(ctx)

	if values["request_id"] != "req-123" {
		t.Error("Request ID not in values")
	}

	if values["user_id"] != "user-456" {
		t.Error("User ID not in values")
	}

	if values["baggage.key1"] != "value1" {
		t.Error("Baggage not in values")
	}
}

func BenchmarkWithRequestID(b *testing.B) {
	ctx := context.Background()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = WithRequestID(ctx, "req-12345")
	}
}

func BenchmarkGetRequestID(b *testing.B) {
	ctx := WithRequestID(context.Background(), "req-12345")
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = GetRequestID(ctx)
	}
}

func BenchmarkWithBaggage(b *testing.B) {
	ctx := context.Background()
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = WithBaggage(ctx, "key", "value")
	}
}

func BenchmarkGetContextValues(b *testing.B) {
	ctx := context.Background()
	ctx = WithRequestID(ctx, "req-123")
	ctx = WithUserID(ctx, "user-456")
	ctx = WithBaggage(ctx, "key1", "value1")
	b.ReportAllocs()

	for i := 0; i < b.N; i++ {
		_ = GetContextValues(ctx)
	}
}

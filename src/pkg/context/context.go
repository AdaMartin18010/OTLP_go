package context

import (
	"context"
	"time"

	"go.opentelemetry.io/otel/baggage"
	"go.opentelemetry.io/otel/trace"
)

// contextKey 上下文键类型
type contextKey string

const (
	// RequestIDKey 请求 ID 键
	RequestIDKey contextKey = "request_id"
	// UserIDKey 用户 ID 键
	UserIDKey contextKey = "user_id"
	// TraceIDKey 追踪 ID 键
	TraceIDKey contextKey = "trace_id"
	// SpanIDKey Span ID 键
	SpanIDKey contextKey = "span_id"
	// TenantIDKey 租户 ID 键
	TenantIDKey contextKey = "tenant_id"
)

// WithRequestID 添加请求 ID 到上下文
func WithRequestID(ctx context.Context, requestID string) context.Context {
	return context.WithValue(ctx, RequestIDKey, requestID)
}

// GetRequestID 从上下文获取请求 ID
func GetRequestID(ctx context.Context) string {
	if v := ctx.Value(RequestIDKey); v != nil {
		if id, ok := v.(string); ok {
			return id
		}
	}
	return ""
}

// WithUserID 添加用户 ID 到上下文
func WithUserID(ctx context.Context, userID string) context.Context {
	return context.WithValue(ctx, UserIDKey, userID)
}

// GetUserID 从上下文获取用户 ID
func GetUserID(ctx context.Context) string {
	if v := ctx.Value(UserIDKey); v != nil {
		if id, ok := v.(string); ok {
			return id
		}
	}
	return ""
}

// WithTenantID 添加租户 ID 到上下文
func WithTenantID(ctx context.Context, tenantID string) context.Context {
	return context.WithValue(ctx, TenantIDKey, tenantID)
}

// GetTenantID 从上下文获取租户 ID
func GetTenantID(ctx context.Context) string {
	if v := ctx.Value(TenantIDKey); v != nil {
		if id, ok := v.(string); ok {
			return id
		}
	}
	return ""
}

// GetTraceID 从上下文获取追踪 ID
func GetTraceID(ctx context.Context) string {
	span := trace.SpanFromContext(ctx)
	if span.SpanContext().IsValid() {
		return span.SpanContext().TraceID().String()
	}
	return ""
}

// GetSpanID 从上下文获取 Span ID
func GetSpanID(ctx context.Context) string {
	span := trace.SpanFromContext(ctx)
	if span.SpanContext().IsValid() {
		return span.SpanContext().SpanID().String()
	}
	return ""
}

// WithBaggage 添加 Baggage 到上下文
func WithBaggage(ctx context.Context, key, value string) context.Context {
	member, _ := baggage.NewMember(key, value)
	bag, _ := baggage.New(member)

	// 合并现有 Baggage
	if existingBag := baggage.FromContext(ctx); len(existingBag.Members()) > 0 {
		for _, m := range existingBag.Members() {
			if m.Key() != key {
				bag, _ = bag.SetMember(m)
			}
		}
	}

	return baggage.ContextWithBaggage(ctx, bag)
}

// GetBaggage 从上下文获取 Baggage 值
func GetBaggage(ctx context.Context, key string) string {
	bag := baggage.FromContext(ctx)
	member := bag.Member(key)
	return member.Value()
}

// WithTimeout 创建带超时的上下文
func WithTimeout(parent context.Context, timeout time.Duration) (context.Context, context.CancelFunc) {
	return context.WithTimeout(parent, timeout)
}

// WithDeadline 创建带截止时间的上下文
func WithDeadline(parent context.Context, deadline time.Time) (context.Context, context.CancelFunc) {
	return context.WithDeadline(parent, deadline)
}

// WithCancel 创建可取消的上下文
func WithCancel(parent context.Context) (context.Context, context.CancelFunc) {
	return context.WithCancel(parent)
}

// Detach 创建独立的上下文（保留值但断开取消链）
func Detach(ctx context.Context) context.Context {
	return detachedContext{ctx}
}

type detachedContext struct {
	parent context.Context
}

func (d detachedContext) Deadline() (time.Time, bool) {
	return time.Time{}, false
}

func (d detachedContext) Done() <-chan struct{} {
	return nil
}

func (d detachedContext) Err() error {
	return nil
}

func (d detachedContext) Value(key interface{}) interface{} {
	return d.parent.Value(key)
}

// MergeContexts 合并多个上下文的值（使用第一个上下文的取消机制）
func MergeContexts(primary context.Context, others ...context.Context) context.Context {
	ctx := primary

	// 复制所有上下文的值
	for _, other := range others {
		// 简化实现：只能合并特定的已知键
		if requestID := GetRequestID(other); requestID != "" {
			ctx = WithRequestID(ctx, requestID)
		}
		if userID := GetUserID(other); userID != "" {
			ctx = WithUserID(ctx, userID)
		}
		if tenantID := GetTenantID(other); tenantID != "" {
			ctx = WithTenantID(ctx, tenantID)
		}

		// 合并 Baggage
		if bag := baggage.FromContext(other); len(bag.Members()) > 0 {
			ctx = baggage.ContextWithBaggage(ctx, bag)
		}
	}

	return ctx
}

// ContextWithValues 使用 map 批量设置上下文值
func ContextWithValues(parent context.Context, values map[string]interface{}) context.Context {
	ctx := parent
	for k, v := range values {
		ctx = context.WithValue(ctx, contextKey(k), v)
	}
	return ctx
}

// GetContextValues 获取所有已知的上下文值
func GetContextValues(ctx context.Context) map[string]string {
	values := make(map[string]string)

	if requestID := GetRequestID(ctx); requestID != "" {
		values["request_id"] = requestID
	}
	if userID := GetUserID(ctx); userID != "" {
		values["user_id"] = userID
	}
	if tenantID := GetTenantID(ctx); tenantID != "" {
		values["tenant_id"] = tenantID
	}
	if traceID := GetTraceID(ctx); traceID != "" {
		values["trace_id"] = traceID
	}
	if spanID := GetSpanID(ctx); spanID != "" {
		values["span_id"] = spanID
	}

	// 添加所有 Baggage
	bag := baggage.FromContext(ctx)
	for _, member := range bag.Members() {
		values["baggage."+member.Key()] = member.Value()
	}

	return values
}

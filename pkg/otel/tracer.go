// Package otel provides OpenTelemetry SDK initialization and management
// for the OTLP Go SDK.
package otel

import (
	"context"
	"fmt"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/trace"
)

// TracerWrapper 是对 OpenTelemetry Tracer 的包装，提供更便捷的 API
type TracerWrapper struct {
	tracer trace.Tracer
	name   string
}

// NewTracerWrapper 创建一个新的 TracerWrapper
func NewTracerWrapper(tp trace.TracerProvider, name string, opts ...trace.TracerOption) *TracerWrapper {
	return &TracerWrapper{
		tracer: tp.Tracer(name, opts...),
		name:   name,
	}
}

// Start 启动一个新的 Span
func (tw *TracerWrapper) Start(ctx context.Context, spanName string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	return tw.tracer.Start(ctx, spanName, opts...)
}

// SpanBuilder 用于构建和管理 Span
type SpanBuilder struct {
	tracer    *TracerWrapper
	name      string
	options   []trace.SpanStartOption
	attributes []attribute.KeyValue
	kind      trace.SpanKind
}

// NewSpanBuilder 创建一个新的 SpanBuilder
func (tw *TracerWrapper) NewSpanBuilder(name string) *SpanBuilder {
	return &SpanBuilder{
		tracer:     tw,
		name:       name,
		options:    make([]trace.SpanStartOption, 0),
		attributes: make([]attribute.KeyValue, 0),
		kind:       trace.SpanKindInternal,
	}
}

// WithKind 设置 Span 类型
func (sb *SpanBuilder) WithKind(kind trace.SpanKind) *SpanBuilder {
	sb.kind = kind
	return sb
}

// WithAttribute 添加单个属性
func (sb *SpanBuilder) WithAttribute(key string, value interface{}) *SpanBuilder {
	sb.attributes = append(sb.attributes, createAttribute(key, value))
	return sb
}

// WithAttributes 添加多个属性
func (sb *SpanBuilder) WithAttributes(attrs map[string]interface{}) *SpanBuilder {
	for k, v := range attrs {
		sb.attributes = append(sb.attributes, createAttribute(k, v))
	}
	return sb
}

// WithParent 设置父 Span
func (sb *SpanBuilder) WithParent(parent trace.SpanContext) *SpanBuilder {
	sb.options = append(sb.options, trace.WithLinks(trace.Link{SpanContext: parent}))
	return sb
}
}

// Start 启动 Span 并返回上下文
func (sb *SpanBuilder) Start(ctx context.Context) (context.Context, trace.Span) {
	opts := append(sb.options,
		trace.WithSpanKind(sb.kind),
		trace.WithAttributes(sb.attributes...),
	)
	return sb.tracer.Start(ctx, sb.name, opts...)
}

// Run 执行函数并在 Span 内追踪
func (sb *SpanBuilder) Run(ctx context.Context, fn func(context.Context) error) error {
	ctx, span := sb.Start(ctx)
	defer span.End()

	if err := fn(ctx); err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		return err
	}

	span.SetStatus(codes.Ok, "")
	return nil
}

// SpanContext 提供当前 Span 的便捷操作
type SpanContext struct {
	Span trace.Span
	Ctx  context.Context
}

// CurrentSpanContext 获取当前的 SpanContext
func CurrentSpanContext(ctx context.Context) *SpanContext {
	span := trace.SpanFromContext(ctx)
	return &SpanContext{
		Span: span,
		Ctx:  ctx,
	}
}

// SetAttribute 设置属性
func (sc *SpanContext) SetAttribute(key string, value interface{}) *SpanContext {
	if sc.Span != nil {
		sc.Span.SetAttributes(createAttribute(key, value))
	}
	return sc
}

// SetAttributes 设置多个属性
func (sc *SpanContext) SetAttributes(attrs map[string]interface{}) *SpanContext {
	if sc.Span != nil {
		for k, v := range attrs {
			sc.Span.SetAttributes(createAttribute(k, v))
		}
	}
	return sc
}

// AddEvent 添加事件
func (sc *SpanContext) AddEvent(name string, attrs ...attribute.KeyValue) *SpanContext {
	if sc.Span != nil {
		sc.Span.AddEvent(name, trace.WithAttributes(attrs...))
	}
	return sc
}

// RecordError 记录错误
func (sc *SpanContext) RecordError(err error, opts ...trace.EventOption) *SpanContext {
	if sc.Span != nil && err != nil {
		sc.Span.RecordError(err, opts...)
		sc.Span.SetStatus(codes.Error, err.Error())
	}
	return sc
}

// SetStatus 设置状态
func (sc *SpanContext) SetStatus(code codes.Code, description string) *SpanContext {
	if sc.Span != nil {
		sc.Span.SetStatus(code, description)
	}
	return sc
}

// End 结束 Span
func (sc *SpanContext) End() {
	if sc.Span != nil {
		sc.Span.End()
	}
}

// IsRecording 返回 Span 是否正在记录
func (sc *SpanContext) IsRecording() bool {
	return sc.Span != nil && sc.Span.IsRecording()
}

// TraceID 返回 TraceID
func (sc *SpanContext) TraceID() string {
	if sc.Span != nil {
		return sc.Span.SpanContext().TraceID().String()
	}
	return ""
}

// SpanID 返回 SpanID
func (sc *SpanContext) SpanID() string {
	if sc.Span != nil {
		return sc.Span.SpanContext().SpanID().String()
	}
	return ""
}

// TracingFunc 是一个可以被追踪的函数类型
type TracingFunc func(ctx context.Context) error

// TraceFunc 追踪一个函数的执行
func (tw *TracerWrapper) TraceFunc(ctx context.Context, spanName string, fn TracingFunc, opts ...trace.SpanStartOption) error {
	ctx, span := tw.Start(ctx, spanName, opts...)
	defer span.End()

	start := time.Now()
	err := fn(ctx)
	duration := time.Since(start)

	span.SetAttributes(
		attribute.String("function.duration", duration.String()),
		attribute.Int64("function.duration_ms", duration.Milliseconds()),
	)

	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		return err
	}

	span.SetStatus(codes.Ok, "")
	return nil
}

// TraceFuncWithResult 追踪一个带返回值的函数执行
func TraceFuncWithResult[T any](tw *TracerWrapper, ctx context.Context, spanName string, fn func(context.Context) (T, error), opts ...trace.SpanStartOption) (T, error) {
	ctx, span := tw.Start(ctx, spanName, opts...)
	defer span.End()

	start := time.Now()
	result, err := fn(ctx)
	duration := time.Since(start)

	span.SetAttributes(
		attribute.String("function.duration", duration.String()),
		attribute.Int64("function.duration_ms", duration.Milliseconds()),
	)

	if err != nil {
		span.RecordError(err)
		span.SetStatus(codes.Error, err.Error())
		var zero T
		return zero, err
	}

	span.SetStatus(codes.Ok, "")
	return result, nil
}

// SpanKind 辅助函数

// ServerSpan 创建服务器端 Span
func (tw *TracerWrapper) ServerSpan(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	opts = append(opts, trace.WithSpanKind(trace.SpanKindServer))
	return tw.Start(ctx, name, opts...)
}

// ClientSpan 创建客户端 Span
func (tw *TracerWrapper) ClientSpan(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	opts = append(opts, trace.WithSpanKind(trace.SpanKindClient))
	return tw.Start(ctx, name, opts...)
}

// ProducerSpan 创建生产者 Span
func (tw *TracerWrapper) ProducerSpan(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	opts = append(opts, trace.WithSpanKind(trace.SpanKindProducer))
	return tw.Start(ctx, name, opts...)
}

// ConsumerSpan 创建消费者 Span
func (tw *TracerWrapper) ConsumerSpan(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	opts = append(opts, trace.WithSpanKind(trace.SpanKindConsumer))
	return tw.Start(ctx, name, opts...)
}

// InternalSpan 创建内部 Span
func (tw *TracerWrapper) InternalSpan(ctx context.Context, name string, opts ...trace.SpanStartOption) (context.Context, trace.Span) {
	opts = append(opts, trace.WithSpanKind(trace.SpanKindInternal))
	return tw.Start(ctx, name, opts...)
}

// createAttribute 根据值类型创建属性
func createAttribute(key string, value interface{}) attribute.KeyValue {
	switch v := value.(type) {
	case string:
		return attribute.String(key, v)
	case int:
		return attribute.Int(key, v)
	case int64:
		return attribute.Int64(key, v)
	case float64:
		return attribute.Float64(key, v)
	case bool:
		return attribute.Bool(key, v)
	case []string:
		return attribute.StringSlice(key, v)
	case []int:
		return attribute.IntSlice(key, v)
	case []int64:
		return attribute.Int64Slice(key, v)
	case []float64:
		return attribute.Float64Slice(key, v)
	case []bool:
		return attribute.BoolSlice(key, v)
	case time.Duration:
		return attribute.String(key, v.String())
	case fmt.Stringer:
		return attribute.String(key, v.String())
	default:
		return attribute.String(key, fmt.Sprintf("%v", v))
	}
}

// TracerFromContext 从上下文获取 Tracer
func TracerFromContext(ctx context.Context, name string) trace.Tracer {
	provider, ok := ctx.Value(tracerProviderKey{}).(trace.TracerProvider)
	if !ok || provider == nil {
		return nil
	}
	return provider.Tracer(name)
}

type tracerProviderKey struct{}

// ContextWithTracerProvider 将 TracerProvider 存入上下文
func ContextWithTracerProvider(ctx context.Context, provider trace.TracerProvider) context.Context {
	return context.WithValue(ctx, tracerProviderKey{}, provider)
}

// SpanFromContext 从上下文获取 Span
func SpanFromContext(ctx context.Context) trace.Span {
	return trace.SpanFromContext(ctx)
}

// ContextWithSpan 将 Span 存入上下文
func ContextWithSpan(ctx context.Context, span trace.Span) context.Context {
	return trace.ContextWithSpan(ctx, span)
}

// ExtractSpanContext 从上下文提取 SpanContext
func ExtractSpanContext(ctx context.Context) trace.SpanContext {
	return trace.SpanFromContext(ctx).SpanContext()
}

// IsValidSpanContext 检查 SpanContext 是否有效
func IsValidSpanContext(ctx context.Context) bool {
	sc := ExtractSpanContext(ctx)
	return sc.IsValid()
}

// SpanKindString 将 SpanKind 转换为字符串
func SpanKindString(kind trace.SpanKind) string {
	switch kind {
	case trace.SpanKindInternal:
		return "internal"
	case trace.SpanKindServer:
		return "server"
	case trace.SpanKindClient:
		return "client"
	case trace.SpanKindProducer:
		return "producer"
	case trace.SpanKindConsumer:
		return "consumer"
	default:
		return "unspecified"
	}
}

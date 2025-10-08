package main

import (
	"context"
	"fmt"
	"log"
	"strings"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	"go.opentelemetry.io/otel/trace"
)

// ============================
// 1. 自定义 Exporter
// ============================

// FileExporter 文件导出器
type FileExporter struct {
	mu       sync.Mutex
	spans    []sdktrace.ReadOnlySpan
	maxSpans int
}

// NewFileExporter 创建文件导出器
func NewFileExporter(maxSpans int) *FileExporter {
	return &FileExporter{
		spans:    make([]sdktrace.ReadOnlySpan, 0, maxSpans),
		maxSpans: maxSpans,
	}
}

// ExportSpans 导出 Span
func (e *FileExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
	e.mu.Lock()
	defer e.mu.Unlock()

	log.Printf("📤 Exporting %d spans to file", len(spans))

	for _, span := range spans {
		e.spans = append(e.spans, span)

		// 打印 Span 信息
		log.Printf("  [%s] %s (Duration: %v)",
			span.SpanContext().TraceID().String()[:8],
			span.Name(),
			span.EndTime().Sub(span.StartTime()),
		)

		// 打印属性
		for _, attr := range span.Attributes() {
			log.Printf("    %s: %v", attr.Key, attr.Value.AsInterface())
		}

		// 如果达到最大数量,清空
		if len(e.spans) >= e.maxSpans {
			log.Printf("⚠️  Max spans reached, clearing buffer")
			e.spans = e.spans[:0]
		}
	}

	return nil
}

// Shutdown 关闭导出器
func (e *FileExporter) Shutdown(ctx context.Context) error {
	log.Printf("🔄 Shutting down FileExporter, exported %d spans", len(e.spans))
	return nil
}

// ============================
// 2. 自定义 Processor (过滤器)
// ============================

// FilterProcessor 过滤处理器
type FilterProcessor struct {
	next      sdktrace.SpanProcessor
	filterFn  func(sdktrace.ReadOnlySpan) bool
	filtered  int
	processed int
	mu        sync.Mutex
}

// NewFilterProcessor 创建过滤处理器
func NewFilterProcessor(next sdktrace.SpanProcessor, filterFn func(sdktrace.ReadOnlySpan) bool) *FilterProcessor {
	return &FilterProcessor{
		next:     next,
		filterFn: filterFn,
	}
}

// OnStart 处理 Span 开始
func (p *FilterProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	p.next.OnStart(parent, s)
}

// OnEnd 处理 Span 结束
func (p *FilterProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	p.mu.Lock()
	p.processed++
	p.mu.Unlock()

	// 应用过滤函数
	if !p.filterFn(s) {
		p.mu.Lock()
		p.filtered++
		p.mu.Unlock()
		log.Printf("🚫 Filtered span: %s", s.Name())
		return
	}

	p.next.OnEnd(s)
}

// Shutdown 关闭处理器
func (p *FilterProcessor) Shutdown(ctx context.Context) error {
	log.Printf("📊 Filter stats - Processed: %d, Filtered: %d, Passed: %d",
		p.processed, p.filtered, p.processed-p.filtered)
	return p.next.Shutdown(ctx)
}

// ForceFlush 强制刷新
func (p *FilterProcessor) ForceFlush(ctx context.Context) error {
	return p.next.ForceFlush(ctx)
}

// ============================
// 3. 数据脱敏 Processor
// ============================

// SanitizeProcessor 数据脱敏处理器
type SanitizeProcessor struct {
	next           sdktrace.SpanProcessor
	sensitiveKeys  []string
	sanitizedCount int
	mu             sync.Mutex
}

// NewSanitizeProcessor 创建脱敏处理器
func NewSanitizeProcessor(next sdktrace.SpanProcessor, sensitiveKeys []string) *SanitizeProcessor {
	return &SanitizeProcessor{
		next:          next,
		sensitiveKeys: sensitiveKeys,
	}
}

// OnStart 处理 Span 开始
func (p *SanitizeProcessor) OnStart(parent context.Context, s sdktrace.ReadWriteSpan) {
	// 脱敏属性
	for _, key := range p.sensitiveKeys {
		if s.Attributes() != nil {
			// 检查是否包含敏感属性
			for _, attr := range s.Attributes() {
				if string(attr.Key) == key {
					// 替换为脱敏值
					s.SetAttributes(attribute.String(key, "***REDACTED***"))
					p.mu.Lock()
					p.sanitizedCount++
					p.mu.Unlock()
					log.Printf("🔒 Sanitized attribute: %s", key)
				}
			}
		}
	}

	p.next.OnStart(parent, s)
}

// OnEnd 处理 Span 结束
func (p *SanitizeProcessor) OnEnd(s sdktrace.ReadOnlySpan) {
	p.next.OnEnd(s)
}

// Shutdown 关闭处理器
func (p *SanitizeProcessor) Shutdown(ctx context.Context) error {
	log.Printf("🔒 Sanitized %d attributes", p.sanitizedCount)
	return p.next.Shutdown(ctx)
}

// ForceFlush 强制刷新
func (p *SanitizeProcessor) ForceFlush(ctx context.Context) error {
	return p.next.ForceFlush(ctx)
}

// ============================
// 4. 自定义 Sampler (动态采样)
// ============================

// DynamicSampler 动态采样器
type DynamicSampler struct {
	samplingRate float64
	mu           sync.RWMutex
	sampled      int
	total        int
}

// NewDynamicSampler 创建动态采样器
func NewDynamicSampler(initialRate float64) *DynamicSampler {
	return &DynamicSampler{
		samplingRate: initialRate,
	}
}

// ShouldSample 判断是否应该采样
func (s *DynamicSampler) ShouldSample(parameters sdktrace.SamplingParameters) sdktrace.SamplingResult {
	s.mu.RLock()
	rate := s.samplingRate
	s.mu.RUnlock()

	s.mu.Lock()
	s.total++
	s.mu.Unlock()

	// 基于采样率决定
	traceID := parameters.TraceID
	threshold := uint64(rate * float64(^uint64(0)))

	// 将 TraceID 转换为 uint64
	var value uint64
	for i := 0; i < 8 && i < len(traceID); i++ {
		value = value<<8 | uint64(traceID[i])
	}

	shouldSample := value <= threshold

	if shouldSample {
		s.mu.Lock()
		s.sampled++
		s.mu.Unlock()

		return sdktrace.SamplingResult{
			Decision:   sdktrace.RecordAndSample,
			Attributes: []attribute.KeyValue{attribute.String("sampler", "dynamic")},
		}
	}

	return sdktrace.SamplingResult{
		Decision: sdktrace.Drop,
	}
}

// Description 返回采样器描述
func (s *DynamicSampler) Description() string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return fmt.Sprintf("DynamicSampler{rate=%.2f}", s.samplingRate)
}

// SetRate 设置采样率
func (s *DynamicSampler) SetRate(rate float64) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.samplingRate = rate
	log.Printf("📊 Sampling rate updated to %.2f", rate)
}

// GetStats 获取统计信息
func (s *DynamicSampler) GetStats() (total, sampled int, rate float64) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.total, s.sampled, s.samplingRate
}

// ============================
// 5. 基于规则的 Sampler
// ============================

// RuleBasedSampler 基于规则的采样器
type RuleBasedSampler struct {
	rules []SamplingRule
	mu    sync.RWMutex
}

// SamplingRule 采样规则
type SamplingRule struct {
	NamePattern string
	Rate        float64
	Priority    int
}

// NewRuleBasedSampler 创建基于规则的采样器
func NewRuleBasedSampler(rules []SamplingRule) *RuleBasedSampler {
	return &RuleBasedSampler{
		rules: rules,
	}
}

// ShouldSample 判断是否应该采样
func (s *RuleBasedSampler) ShouldSample(parameters sdktrace.SamplingParameters) sdktrace.SamplingResult {
	s.mu.RLock()
	defer s.mu.RUnlock()

	spanName := parameters.Name

	// 查找匹配的规则
	for _, rule := range s.rules {
		if strings.Contains(spanName, rule.NamePattern) {
			// 应用规则的采样率
			if rule.Rate >= 1.0 {
				return sdktrace.SamplingResult{
					Decision: sdktrace.RecordAndSample,
					Attributes: []attribute.KeyValue{
						attribute.String("sampler", "rule-based"),
						attribute.String("rule", rule.NamePattern),
					},
				}
			} else if rule.Rate <= 0.0 {
				return sdktrace.SamplingResult{
					Decision: sdktrace.Drop,
				}
			}

			// 部分采样
			traceID := parameters.TraceID
			threshold := uint64(rule.Rate * float64(^uint64(0)))
			var value uint64
			for i := 0; i < 8 && i < len(traceID); i++ {
				value = value<<8 | uint64(traceID[i])
			}

			if value <= threshold {
				return sdktrace.SamplingResult{
					Decision: sdktrace.RecordAndSample,
					Attributes: []attribute.KeyValue{
						attribute.String("sampler", "rule-based"),
						attribute.String("rule", rule.NamePattern),
					},
				}
			}
		}
	}

	// 默认不采样
	return sdktrace.SamplingResult{
		Decision: sdktrace.Drop,
	}
}

// Description 返回采样器描述
func (s *RuleBasedSampler) Description() string {
	return "RuleBasedSampler"
}

// ============================
// 演示函数
// ============================

// demonstrateCustomExporter 演示自定义导出器
func demonstrateCustomExporter(tracer trace.Tracer) {
	log.Println("\n--- Custom Exporter Demo ---")

	ctx := context.Background()
	for i := 0; i < 5; i++ {
		_, span := tracer.Start(ctx, fmt.Sprintf("operation-%d", i))
		span.SetAttributes(
			attribute.Int("iteration", i),
			attribute.String("type", "demo"),
		)
		time.Sleep(10 * time.Millisecond)
		span.End()
	}

	log.Println("✅ Custom exporter demo completed")
}

// demonstrateFilterProcessor 演示过滤处理器
func demonstrateFilterProcessor(tracer trace.Tracer) {
	log.Println("\n--- Filter Processor Demo ---")

	ctx := context.Background()

	// 创建多种类型的 Span
	operations := []struct {
		name   string
		status codes.Code
	}{
		{"normal-operation", codes.Ok},
		{"error-operation", codes.Error},
		{"slow-operation", codes.Ok},
		{"failed-operation", codes.Error},
	}

	for _, op := range operations {
		_, span := tracer.Start(ctx, op.name)
		span.SetStatus(op.status, "")

		if strings.Contains(op.name, "slow") {
			time.Sleep(100 * time.Millisecond)
		}

		span.End()
	}

	log.Println("✅ Filter processor demo completed")
}

// demonstrateSanitizeProcessor 演示脱敏处理器
func demonstrateSanitizeProcessor(tracer trace.Tracer) {
	log.Println("\n--- Sanitize Processor Demo ---")

	ctx := context.Background()

	_, span := tracer.Start(ctx, "user-login")
	span.SetAttributes(
		attribute.String("username", "alice"),
		attribute.String("password", "secret123"), // 将被脱敏
		attribute.String("email", "alice@example.com"),
		attribute.String("credit_card", "1234-5678-9012-3456"), // 将被脱敏
	)
	span.End()

	log.Println("✅ Sanitize processor demo completed")
}

// demonstrateDynamicSampler 演示动态采样器
func demonstrateDynamicSampler(tracer trace.Tracer, sampler *DynamicSampler) {
	log.Println("\n--- Dynamic Sampler Demo ---")

	ctx := context.Background()

	// 生成100个 Span
	for i := 0; i < 100; i++ {
		_, span := tracer.Start(ctx, fmt.Sprintf("sampled-operation-%d", i))
		span.End()
	}

	total, sampled, rate := sampler.GetStats()
	log.Printf("📊 Sampler stats - Total: %d, Sampled: %d, Rate: %.2f, Actual: %.2f\n",
		total, sampled, rate, float64(sampled)/float64(total))
}

// ============================
// Main
// ============================

func main() {
	log.Println("\n" + strings.Repeat("=", 80))
	log.Println("🚀 Custom Components Demo")
	log.Println(strings.Repeat("=", 80) + "\n")

	// 1. 设置自定义导出器
	exporter := NewFileExporter(20)

	// 2. 设置过滤处理器 (只保留错误 Span)
	filterProcessor := NewFilterProcessor(
		sdktrace.NewBatchSpanProcessor(exporter),
		func(span sdktrace.ReadOnlySpan) bool {
			// 保留所有 OK 状态的 Span 和所有错误
			return span.Status().Code == codes.Ok || span.Status().Code == codes.Error
		},
	)

	// 3. 设置脱敏处理器
	sanitizeProcessor := NewSanitizeProcessor(
		filterProcessor,
		[]string{"password", "credit_card", "ssn", "api_key"},
	)

	// 4. 设置动态采样器
	dynamicSampler := NewDynamicSampler(0.5) // 50% 采样率

	// 5. 设置资源
	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("custom-components-demo"),
			semconv.ServiceVersion("1.0.0"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	// 6. 创建 TracerProvider
	tp := sdktrace.NewTracerProvider(
		sdktrace.WithSpanProcessor(sanitizeProcessor),
		sdktrace.WithResource(res),
		sdktrace.WithSampler(dynamicSampler),
	)
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Fatalf("Failed to shutdown tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)
	tracer := tp.Tracer("custom-components")

	// 演示1: 自定义导出器
	demonstrateCustomExporter(tracer)

	// 演示2: 过滤处理器
	demonstrateFilterProcessor(tracer)

	// 演示3: 脱敏处理器
	demonstrateSanitizeProcessor(tracer)

	// 演示4: 动态采样器
	demonstrateDynamicSampler(tracer, dynamicSampler)

	// 动态调整采样率
	log.Println("\n--- Adjusting Sampling Rate ---")
	dynamicSampler.SetRate(0.8) // 调整到 80%

	// 再次测试
	ctx := context.Background()
	for i := 0; i < 50; i++ {
		_, span := tracer.Start(ctx, fmt.Sprintf("adjusted-operation-%d", i))
		span.End()
	}

	total, sampled, rate := dynamicSampler.GetStats()
	log.Printf("📊 Updated sampler stats - Total: %d, Sampled: %d, Rate: %.2f, Actual: %.2f\n",
		total, sampled, rate, float64(sampled)/float64(total))

	log.Println("\n" + strings.Repeat("=", 80))
	log.Println("✅ All demos completed successfully")
	log.Println(strings.Repeat("=", 80))
}

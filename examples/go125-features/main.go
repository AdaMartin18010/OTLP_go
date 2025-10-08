package main

import (
	"context"
	"errors"
	"fmt"
	"log"
	"strings"
	"sync"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/exporters/stdout/stdouttrace"
	"go.opentelemetry.io/otel/sdk/resource"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	semconv "go.opentelemetry.io/otel/semconv/v1.26.0"
	"go.opentelemetry.io/otel/trace"
)

// ============================
// 1. 泛型 Tracer 包装器
// ============================

// TracedResult 泛型追踪结果
type TracedResult[T any] struct {
	Value T
	Span  trace.Span
	Error error
}

// GenericTracer 泛型追踪器
type GenericTracer[T any] struct {
	tracer trace.Tracer
}

// NewGenericTracer 创建泛型追踪器
func NewGenericTracer[T any](tracer trace.Tracer) *GenericTracer[T] {
	return &GenericTracer[T]{tracer: tracer}
}

// Trace 执行带追踪的函数
func (g *GenericTracer[T]) Trace(ctx context.Context, spanName string, fn func(context.Context) (T, error)) TracedResult[T] {
	ctx, span := g.tracer.Start(ctx, spanName)
	defer span.End()

	value, err := fn(ctx)
	if err != nil {
		span.RecordError(err)
	}

	return TracedResult[T]{
		Value: value,
		Span:  span,
		Error: err,
	}
}

// ============================
// 2. Context 增强功能
// ============================

// demonstrateWithoutCancel 演示 WithoutCancel 用法
func demonstrateWithoutCancel(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-without-cancel")
	defer span.End()

	// 创建可取消的 Context
	parentCtx, cancel := context.WithTimeout(ctx, 100*time.Millisecond)
	defer cancel()

	// 使用 WithoutCancel 分离后台任务
	// 即使父 Context 被取消,后台任务仍继续执行
	backgroundCtx := context.WithoutCancel(parentCtx)

	// 启动后台任务(不受父 Context 取消影响)
	go func() {
		_, bgSpan := tracer.Start(backgroundCtx, "background-task")
		defer bgSpan.End()

		bgSpan.SetAttributes(attribute.Bool("detached", true))
		time.Sleep(200 * time.Millisecond) // 超过父 Context 超时时间
		bgSpan.AddEvent("Background task completed")
		log.Println("✅ Background task completed (not affected by parent cancellation)")
	}()

	// 主任务
	time.Sleep(50 * time.Millisecond)

	// 取消父 Context
	cancel()

	// 等待后台任务完成
	time.Sleep(250 * time.Millisecond)
	span.AddEvent("All tasks completed")
}

// demonstrateWithDeadlineCause 演示 WithDeadlineCause 用法
func demonstrateWithDeadlineCause(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-deadline-cause")
	defer span.End()

	// 创建带原因的超时 Context
	slaViolation := errors.New("SLA violation: response time > 100ms")
	deadlineCtx, cancel := context.WithDeadlineCause(
		ctx,
		time.Now().Add(100*time.Millisecond),
		slaViolation,
	)
	defer cancel()

	// 模拟慢操作
	_, opSpan := tracer.Start(deadlineCtx, "slow-operation")
	time.Sleep(150 * time.Millisecond)
	opSpan.End()

	// 检查超时原因
	if deadlineCtx.Err() != nil {
		cause := context.Cause(deadlineCtx)
		span.RecordError(cause)
		span.SetAttributes(
			attribute.String("timeout.reason", cause.Error()),
		)
		log.Printf("⚠️  Timeout cause: %v", cause)
	}
}

// demonstrateAfterFunc 演示 AfterFunc 用法
func demonstrateAfterFunc(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-after-func")
	defer span.End()

	// 创建带自动清理的 Context
	taskCtx, cancel := context.WithCancel(ctx)

	// 注册清理函数(Context 取消时自动执行)
	cleanupCalled := false
	stop := context.AfterFunc(taskCtx, func() {
		_, cleanSpan := tracer.Start(context.Background(), "auto-cleanup")
		defer cleanSpan.End()

		cleanupCalled = true
		cleanSpan.SetAttributes(attribute.Bool("auto_triggered", true))
		log.Println("🧹 Auto cleanup triggered")
	})
	defer stop() // 取消清理函数注册

	// 模拟任务执行
	time.Sleep(50 * time.Millisecond)
	cancel() // 触发清理

	// 等待清理完成
	time.Sleep(50 * time.Millisecond)

	if cleanupCalled {
		span.AddEvent("Cleanup completed successfully")
	}
}

// ============================
// 3. 新并发原语
// ============================

var (
	// 使用 sync.OnceFunc 确保初始化函数只执行一次
	initTracer = sync.OnceFunc(func() {
		log.Println("🔧 Initializing tracer (called once)")
	})

	// 使用 sync.OnceValue 确保值只计算一次
	getExpensiveValue = sync.OnceValue(func() string {
		log.Println("💰 Computing expensive value (called once)")
		time.Sleep(100 * time.Millisecond)
		return "expensive-result"
	})

	// 使用 sync.OnceValues 返回多个值
	getConfiguration = sync.OnceValues(func() (string, int) {
		log.Println("⚙️  Loading configuration (called once)")
		time.Sleep(50 * time.Millisecond)
		return "production", 8080
	})
)

// demonstrateSyncOnce 演示 sync.Once* 新原语
func demonstrateSyncOnce(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-sync-once")
	defer span.End()

	// 多次调用 OnceFunc,只执行一次
	var wg sync.WaitGroup
	for i := 0; i < 3; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			initTracer() // 只有第一次调用会执行
		}(i)
	}
	wg.Wait()

	// 多次调用 OnceValue,只计算一次
	for i := 0; i < 3; i++ {
		value := getExpensiveValue()
		log.Printf("📦 Got value: %s (call %d)", value, i+1)
	}

	// 多次调用 OnceValues,只计算一次
	for i := 0; i < 3; i++ {
		env, port := getConfiguration()
		log.Printf("🌍 Config: env=%s, port=%d (call %d)", env, port, i+1)
	}

	span.AddEvent("All sync.Once* calls completed")
}

// ============================
// 4. errors.Join 多错误合并
// ============================

// demonstrateErrorsJoin 演示 errors.Join 用法
func demonstrateErrorsJoin(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-errors-join")
	defer span.End()

	// 模拟多个并发操作,收集所有错误
	var wg sync.WaitGroup
	var mu sync.Mutex
	var errs []error

	operations := []struct {
		name    string
		failAt  int
		message string
	}{
		{"database-query", 1, "connection timeout"},
		{"cache-read", 2, "cache miss"},
		{"api-call", 3, "rate limit exceeded"},
	}

	for i, op := range operations {
		wg.Add(1)
		go func(id int, operation struct {
			name    string
			failAt  int
			message string
		}) {
			defer wg.Done()

			_, opSpan := tracer.Start(ctx, operation.name)
			defer opSpan.End()

			// 模拟操作失败
			if id == operation.failAt {
				err := fmt.Errorf("%s failed: %s", operation.name, operation.message)
				opSpan.RecordError(err)

				mu.Lock()
				errs = append(errs, err)
				mu.Unlock()
			}

			time.Sleep(50 * time.Millisecond)
		}(i, op)
	}

	wg.Wait()

	// 使用 errors.Join 合并所有错误
	if len(errs) > 0 {
		combinedErr := errors.Join(errs...)
		span.RecordError(combinedErr)
		span.SetAttributes(attribute.Int("error.count", len(errs)))

		log.Printf("❌ Multiple errors occurred:\n%v", combinedErr)
	} else {
		span.AddEvent("All operations succeeded")
	}
}

// ============================
// 5. 泛型 Exporter
// ============================

// GenericExporter 泛型导出器接口
type GenericExporter[T any] interface {
	Export(ctx context.Context, data []T) error
}

// ConsoleExporter 控制台导出器(泛型实现)
type ConsoleExporter[T any] struct {
	tracer trace.Tracer
}

func (c *ConsoleExporter[T]) Export(ctx context.Context, data []T) error {
	_, span := c.tracer.Start(ctx, "generic-export")
	defer span.End()

	span.SetAttributes(attribute.Int("export.count", len(data)))
	log.Printf("📤 Exporting %d items of type %T", len(data), *new(T))

	for i, item := range data {
		log.Printf("  [%d]: %+v", i, item)
	}

	return nil
}

// demonstrateGenericExporter 演示泛型导出器
func demonstrateGenericExporter(ctx context.Context, tracer trace.Tracer) {
	ctx, span := tracer.Start(ctx, "demonstrate-generic-exporter")
	defer span.End()

	// 字符串导出器
	stringExporter := &ConsoleExporter[string]{tracer: tracer}
	stringExporter.Export(ctx, []string{"trace-1", "trace-2", "trace-3"})

	// 整数导出器
	intExporter := &ConsoleExporter[int]{tracer: tracer}
	intExporter.Export(ctx, []int{100, 200, 300})

	// 结构体导出器
	type MetricData struct {
		Name  string
		Value float64
	}
	metricExporter := &ConsoleExporter[MetricData]{tracer: tracer}
	metricExporter.Export(ctx, []MetricData{
		{Name: "cpu.usage", Value: 45.2},
		{Name: "memory.used", Value: 1024.5},
	})

	span.AddEvent("Generic exporter demo completed")
}

// ============================
// Main
// ============================

func main() {
	// 初始化 TracerProvider
	exporter, err := stdouttrace.New(stdouttrace.WithPrettyPrint())
	if err != nil {
		log.Fatalf("Failed to create exporter: %v", err)
	}

	res, err := resource.New(context.Background(),
		resource.WithAttributes(
			semconv.ServiceName("go125-features-demo"),
			semconv.ServiceVersion("1.0.0"),
			attribute.String("go.version", "1.25.1"),
		),
	)
	if err != nil {
		log.Fatalf("Failed to create resource: %v", err)
	}

	tp := sdktrace.NewTracerProvider(
		sdktrace.WithBatcher(exporter),
		sdktrace.WithResource(res),
	)
	defer func() {
		if err := tp.Shutdown(context.Background()); err != nil {
			log.Fatalf("Failed to shutdown tracer provider: %v", err)
		}
	}()

	otel.SetTracerProvider(tp)
	tracer := tp.Tracer("go125-features")

	ctx := context.Background()

	log.Println("\n" + strings.Repeat("=", 80))
	log.Println("🚀 Go 1.25.1 Features with OTLP Demo")
	log.Println(strings.Repeat("=", 80) + "\n")

	// 1. 泛型 Tracer
	log.Println("--- 1. Generic Tracer Demo ---")
	genericTracer := NewGenericTracer[string](tracer)
	result := genericTracer.Trace(ctx, "generic-operation", func(ctx context.Context) (string, error) {
		time.Sleep(50 * time.Millisecond)
		return "success", nil
	})
	log.Printf("✅ Generic tracer result: %s\n\n", result.Value)

	// 2. Context 增强功能
	log.Println("--- 2. Context Enhancements ---")
	demonstrateWithoutCancel(ctx, tracer)
	time.Sleep(100 * time.Millisecond)
	demonstrateWithDeadlineCause(ctx, tracer)
	demonstrateAfterFunc(ctx, tracer)
	log.Println()

	// 3. 新并发原语
	log.Println("--- 3. New Concurrency Primitives ---")
	demonstrateSyncOnce(ctx, tracer)
	log.Println()

	// 4. errors.Join
	log.Println("--- 4. errors.Join Demo ---")
	demonstrateErrorsJoin(ctx, tracer)
	log.Println()

	// 5. 泛型 Exporter
	log.Println("--- 5. Generic Exporter Demo ---")
	demonstrateGenericExporter(ctx, tracer)
	log.Println()

	log.Println(strings.Repeat("=", 80))
	log.Println("✅ All demos completed successfully")
	log.Println(strings.Repeat("=", 80))
}

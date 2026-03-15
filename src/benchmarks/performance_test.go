package benchmarks

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/trace"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
)

// TestSpanCreationBasic tests basic span creation
func TestSpanCreationBasic(t *testing.T) {
	tp := trace.NewTracerProvider(
		trace.WithSpanProcessor(trace.NewSimpleSpanProcessor(&noopExporter{})),
	)
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	ctx := context.Background()

	_, span := tracer.Start(ctx, "test-operation")
	if span == nil {
		t.Error("Expected non-nil span")
	}
	span.End()
}

// TestSpanWithSampling tests span with sampling
func TestSpanWithSampling(t *testing.T) {
	tp := trace.NewTracerProvider(
		trace.WithSpanProcessor(trace.NewBatchSpanProcessor(&noopExporter{})),
		trace.WithSampler(trace.TraceIDRatioBased(0.5)),
	)
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	ctx := context.Background()

	for i := 0; i < 10; i++ {
		_, span := tracer.Start(ctx, "test-operation")
		span.End()
	}
}

// TestSpanAttributes tests span attributes
func TestSpanAttributes(t *testing.T) {
	tp := trace.NewTracerProvider(
		trace.WithSpanProcessor(trace.NewBatchSpanProcessor(&noopExporter{})),
	)
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	ctx := context.Background()

	_, span := tracer.Start(ctx, "test-operation")
	span.SetAttributes(
		attribute.String("http.method", "GET"),
		attribute.String("http.url", "/api/test"),
		attribute.Int("http.status_code", 200),
	)
	span.End()
}

// TestNestedSpanCreation tests nested spans
func TestNestedSpanCreation(t *testing.T) {
	tp := trace.NewTracerProvider()
	defer tp.Shutdown(context.Background())

	tracer := tp.Tracer("test")
	ctx := context.Background()

	ctx1, span1 := tracer.Start(ctx, "level-1")
	ctx2, span2 := tracer.Start(ctx1, "level-2")
	_, span3 := tracer.Start(ctx2, "level-3")
	span3.End()
	span2.End()
	span1.End()
}

// noopExporter is a no-op exporter for testing
type noopExporter struct{}

func (e *noopExporter) ExportSpans(ctx context.Context, spans []sdktrace.ReadOnlySpan) error {
	return nil
}

func (e *noopExporter) Shutdown(ctx context.Context) error {
	return nil
}

// BenchmarkSpanCreation Span 创建基准测试
func BenchmarkSpanCreation(b *testing.B) {
	ctx := context.Background()

	b.Run("NoInstrumentation", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = ctx
		}
	})

	b.Run("SimpleProcessor", func(b *testing.B) {
		tp := trace.NewTracerProvider(
			trace.WithSpanProcessor(trace.NewSimpleSpanProcessor(&noopExporter{})),
		)
		tracer := tp.Tracer("benchmark")

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.End()
		}
	})

	b.Run("BatchProcessor", func(b *testing.B) {
		tp := trace.NewTracerProvider(
			trace.WithSpanProcessor(trace.NewBatchSpanProcessor(&noopExporter{})),
		)
		tracer := tp.Tracer("benchmark")

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.End()
		}
	})

	b.Run("BatchProcessor-Sampled-10%", func(b *testing.B) {
		tp := trace.NewTracerProvider(
			trace.WithSpanProcessor(trace.NewBatchSpanProcessor(&noopExporter{})),
			trace.WithSampler(trace.TraceIDRatioBased(0.1)),
		)
		tracer := tp.Tracer("benchmark")

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.End()
		}
	})
}

// BenchmarkSpanAttributes 属性设置基准测试
func BenchmarkSpanAttributes(b *testing.B) {
	ctx := context.Background()
	tp := trace.NewTracerProvider(
		trace.WithSpanProcessor(trace.NewBatchSpanProcessor(&noopExporter{})),
	)
	tracer := tp.Tracer("benchmark")

	b.Run("NoAttributes", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.End()
		}
	})

	b.Run("5-Attributes", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.SetAttributes(
				attribute.String("key1", "value1"),
				attribute.Int("key2", 123),
				attribute.Bool("key3", true),
				attribute.Float64("key4", 3.14),
				attribute.String("key5", "value5"),
			)
			span.End()
		}
	})

	b.Run("10-Attributes", func(b *testing.B) {
		attrs := make([]attribute.KeyValue, 10)
		for i := range 10 {
			attrs[i] = attribute.Int("key", i)
		}

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.SetAttributes(attrs...)
			span.End()
		}
	})

	b.Run("20-Attributes", func(b *testing.B) {
		attrs := make([]attribute.KeyValue, 20)
		for i := range 20 {
			attrs[i] = attribute.Int("key", i)
		}

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			_, span := tracer.Start(ctx, "operation")
			span.SetAttributes(attrs...)
			span.End()
		}
	})
}

// BenchmarkChannelOperations Channel 操作基准测试
func BenchmarkChannelOperations(b *testing.B) {
	b.Run("Unbuffered", func(b *testing.B) {
		ch := make(chan int)

		b.RunParallel(func(pb *testing.PB) {
			go func() {
				for pb.Next() {
					ch <- 1
				}
			}()

			for pb.Next() {
				<-ch
			}
		})
	})

	b.Run("Buffered-10", func(b *testing.B) {
		ch := make(chan int, 10)

		b.RunParallel(func(pb *testing.PB) {
			go func() {
				for pb.Next() {
					ch <- 1
				}
			}()

			for pb.Next() {
				<-ch
			}
		})
	})

	b.Run("Buffered-100", func(b *testing.B) {
		ch := make(chan int, 100)

		b.RunParallel(func(pb *testing.PB) {
			go func() {
				for pb.Next() {
					ch <- 1
				}
			}()

			for pb.Next() {
				<-ch
			}
		})
	})

	b.Run("Buffered-1000", func(b *testing.B) {
		ch := make(chan int, 1000)

		b.RunParallel(func(pb *testing.PB) {
			go func() {
				for pb.Next() {
					ch <- 1
				}
			}()

			for pb.Next() {
				<-ch
			}
		})
	})
}

// BenchmarkGoroutineCreation Goroutine 创建基准测试
func BenchmarkGoroutineCreation(b *testing.B) {
	b.Run("Creation", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			done := make(chan struct{})
			go func() {
				close(done)
			}()
			<-done
		}
	})

	b.Run("WithWork", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			done := make(chan struct{})
			go func() {
				// 模拟一些工作
				time.Sleep(10 * time.Microsecond)
				close(done)
			}()
			<-done
		}
	})
}

// BenchmarkContextPropagation Context 传播基准测试
func BenchmarkContextPropagation(b *testing.B) {
	ctx := context.Background()
	tp := trace.NewTracerProvider()
	tracer := tp.Tracer("benchmark")

	b.Run("NoContext", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			processNoContext()
		}
	})

	b.Run("ContextOnly", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			processWithContext(ctx)
		}
	})

	b.Run("ContextWithSpan", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			ctx, span := tracer.Start(ctx, "operation")
			processWithContext(ctx)
			span.End()
		}
	})

	b.Run("NestedSpans-3-Levels", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			ctx, span1 := tracer.Start(ctx, "level-1")
			ctx, span2 := tracer.Start(ctx, "level-2")
			ctx, span3 := tracer.Start(ctx, "level-3")
			processWithContext(ctx)
			span3.End()
			span2.End()
			span1.End()
		}
	})
}

// BenchmarkSelectStatement Select 语句基准测试
func BenchmarkSelectStatement(b *testing.B) {
	ch1 := make(chan int, 1)
	ch2 := make(chan int, 1)

	b.Run("2-Way", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			select {
			case ch1 <- 1:
			case <-ch2:
			default:
			}
		}
	})

	b.Run("4-Way", func(b *testing.B) {
		ch3 := make(chan int, 1)
		ch4 := make(chan int, 1)

		for i := 0; i < b.N; i++ {
			select {
			case ch1 <- 1:
			case <-ch2:
			case ch3 <- 1:
			case <-ch4:
			default:
			}
		}
	})

	b.Run("8-Way", func(b *testing.B) {
		channels := make([]chan int, 8)
		for i := range channels {
			channels[i] = make(chan int, 1)
		}

		b.ResetTimer()
		for i := 0; i < b.N; i++ {
			select {
			case channels[0] <- 1:
			case <-channels[1]:
			case channels[2] <- 1:
			case <-channels[3]:
			case channels[4] <- 1:
			case <-channels[5]:
			case channels[6] <- 1:
			case <-channels[7]:
			default:
			}
		}
	})
}

// Helper functions
func processNoContext() {
	// 模拟处理
}

func processWithContext(ctx context.Context) {
	_ = ctx
}

// BenchmarkWorkerPool Worker Pool 基准测试
func BenchmarkWorkerPool(b *testing.B) {
	// 这里可以添加 Worker Pool 的基准测试
	// 参考 src/patterns/worker_pool.go
}

// BenchmarkPipeline Pipeline 基准测试
func BenchmarkPipeline(b *testing.B) {
	// 这里可以添加 Pipeline 的基准测试
	// 参考 src/patterns/pipeline_advanced.go
}

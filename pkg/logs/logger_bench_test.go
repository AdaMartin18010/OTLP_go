package logs

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

func BenchmarkLoggerEmit(b *testing.B) {
	exporter := NewConsoleExporter()
	processor := NewBatchProcessor(exporter, BatchProcessorOptions{
		MaxQueueSize:  10000,
		BatchSize:     1000,
		FlushInterval: 1 * time.Second,
	})
	provider := NewLoggerProvider(nil, processor, nil)
	logger := provider.GetLogger("benchmark")

	ctx := context.Background()
	attrs := []attribute.KeyValue{
		attribute.String("key1", "value1"),
		attribute.Int("key2", 42),
	}

	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			logger.Info(ctx, "benchmark message", attrs...)
		}
	})

	provider.Shutdown(ctx)
}

func BenchmarkLogRecordCreation(b *testing.B) {
	attrs := []attribute.KeyValue{
		attribute.String("service", "test"),
		attribute.String("environment", "prod"),
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = &LogRecord{
			Timestamp:  time.Now(),
			Severity:   SeverityInfo,
			Body:       "test message",
			Attributes: attrs,
		}
	}
}

func BenchmarkSeverityString(b *testing.B) {
	severities := []SeverityNumber{SeverityTrace, SeverityDebug, SeverityInfo, SeverityWarn, SeverityError, SeverityFatal}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = severities[i%len(severities)].String()
	}
}

package logs

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

// TestLoggerBasic tests basic logger functionality
func TestLoggerBasic(t *testing.T) {
	exporter := NewConsoleExporter()
	processor := NewBatchProcessor(exporter, BatchProcessorOptions{
		MaxQueueSize:  1000,
		BatchSize:     100,
		FlushInterval: 100 * time.Millisecond,
	})
	provider := NewLoggerProvider(nil, processor, nil)
	logger := provider.GetLogger("test")

	ctx := context.Background()
	logger.Info(ctx, "test message")

	err := provider.Shutdown(ctx)
	if err != nil {
		t.Errorf("Shutdown failed: %v", err)
	}
}

// TestLoggerWithAttributes tests logger with attributes
func TestLoggerWithAttributes(t *testing.T) {
	exporter := NewConsoleExporter()
	processor := NewBatchProcessor(exporter, BatchProcessorOptions{
		MaxQueueSize:  1000,
		BatchSize:     100,
		FlushInterval: 100 * time.Millisecond,
	})
	provider := NewLoggerProvider(nil, processor, nil)
	logger := provider.GetLogger("test")

	ctx := context.Background()
	attrs := []attribute.KeyValue{
		attribute.String("key1", "value1"),
		attribute.Int("key2", 42),
	}

	logger.Info(ctx, "test message with attributes", attrs...)

	err := provider.Shutdown(ctx)
	if err != nil {
		t.Errorf("Shutdown failed: %v", err)
	}
}

// TestLoggerSeverityLevels tests all severity levels
func TestLoggerSeverityLevels(t *testing.T) {
	exporter := NewConsoleExporter()
	processor := NewBatchProcessor(exporter, BatchProcessorOptions{
		MaxQueueSize:  1000,
		BatchSize:     100,
		FlushInterval: 100 * time.Millisecond,
	})
	provider := NewLoggerProvider(nil, processor, nil)
	logger := provider.GetLogger("test")

	ctx := context.Background()

	// Test all severity levels
	logger.Trace(ctx, "trace message")
	logger.Debug(ctx, "debug message")
	logger.Info(ctx, "info message")
	logger.Warn(ctx, "warn message")
	logger.Error(ctx, "error message")
	// Note: Fatal is not tested as it may exit the program

	err := provider.Shutdown(ctx)
	if err != nil {
		t.Errorf("Shutdown failed: %v", err)
	}
}

// TestLogRecord tests LogRecord creation
func TestLogRecord(t *testing.T) {
	attrs := []attribute.KeyValue{
		attribute.String("service", "test"),
		attribute.String("environment", "prod"),
	}

	record := &LogRecord{
		Timestamp:  time.Now(),
		Severity:   SeverityInfo,
		Body:       "test message",
		Attributes: attrs,
	}

	if record.Severity != SeverityInfo {
		t.Errorf("Expected severity %d, got %d", SeverityInfo, record.Severity)
	}

	if record.Body != "test message" {
		t.Errorf("Expected body 'test message', got '%s'", record.Body)
	}
}

// TestSeverityString tests severity string conversion
func TestSeverityString(t *testing.T) {
	testCases := []struct {
		severity SeverityNumber
		expected string
	}{
		{SeverityTrace, "TRACE"},
		{SeverityDebug, "DEBUG"},
		{SeverityInfo, "INFO"},
		{SeverityWarn, "WARN"},
		{SeverityError, "ERROR"},
		{SeverityFatal, "FATAL"},
		{SeverityNumber(999), "UNKNOWN"},
	}

	for _, tc := range testCases {
		result := tc.severity.String()
		if result != tc.expected {
			t.Errorf("Severity %d: expected '%s', got '%s'", tc.severity, tc.expected, result)
		}
	}
}

// BenchmarkLoggerEmit benchmarks logger emit
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

// BenchmarkLogRecordCreation benchmarks LogRecord creation
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

// BenchmarkSeverityString benchmarks severity string conversion
func BenchmarkSeverityString(b *testing.B) {
	severities := []SeverityNumber{SeverityTrace, SeverityDebug, SeverityInfo, SeverityWarn, SeverityError, SeverityFatal}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		_ = severities[i%len(severities)].String()
	}
}

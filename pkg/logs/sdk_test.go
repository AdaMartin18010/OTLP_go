package logs

import (
	"context"
	"sync"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

type testLogExporter struct {
	mu      sync.Mutex
	records []LogRecord
}

func (e *testLogExporter) Export(ctx context.Context, records []LogRecord) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.records = append(e.records, records...)
	return nil
}

func (e *testLogExporter) Shutdown(ctx context.Context) error {
	return nil
}

func (e *testLogExporter) Records() []LogRecord {
	e.mu.Lock()
	defer e.mu.Unlock()
	result := make([]LogRecord, len(e.records))
	copy(result, e.records)
	return result
}

func TestNewLoggerProvider(t *testing.T) {
	lp := NewLoggerProvider()
	if lp == nil {
		t.Fatal("NewLoggerProvider() returned nil")
	}

	logger := lp.Logger("test")
	if logger == nil {
		t.Fatal("Logger() returned nil")
	}

	// Same name should return same logger
	logger2 := lp.Logger("test")
	if logger != logger2 {
		t.Error("Logger should return cached logger")
	}

	// Different name should return different logger
	logger3 := lp.Logger("other")
	if logger == logger3 {
		t.Error("Logger should return different loggers for different names")
	}
}

func TestLoggerProvider_Shutdown(t *testing.T) {
	lp := NewLoggerProvider()
	ctx := context.Background()

	if err := lp.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown() error = %v", err)
	}

	// Double shutdown should be safe
	if err := lp.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown() second call error = %v", err)
	}
}

func TestLoggerProvider_ForceFlush(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewSimpleLogRecordProcessor(exporter)
	lp := NewLoggerProvider(WithProcessor(processor))
	ctx := context.Background()

	if err := lp.ForceFlush(ctx); err != nil {
		t.Errorf("ForceFlush() error = %v", err)
	}
}

func TestLoggerProvider_WithResource(t *testing.T) {
	lp := NewLoggerProvider(WithResource("test-resource"))
	if lp == nil {
		t.Fatal("NewLoggerProvider() returned nil")
	}
}

func TestSDKLogger_Emit(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewSimpleLogRecordProcessor(exporter)
	lp := NewLoggerProvider(WithProcessor(processor))
	logger := lp.Logger("test")

	record := LogRecord{
		Timestamp:      time.Now(),
		SeverityNumber: SeverityInfo,
		Body:           "test message",
		EventName:      "test.emit",
		Attributes:     []attribute.KeyValue{attribute.String("key", "value")},
	}
	logger.Emit(record)

	records := exporter.Records()
	if len(records) != 1 {
		t.Fatalf("expected 1 record, got %d", len(records))
	}
	if records[0].Body != "test message" {
		t.Errorf("Body = %v, want 'test message'", records[0].Body)
	}
	if records[0].EventName != "test.emit" {
		t.Errorf("EventName = %v, want 'test.emit'", records[0].EventName)
	}
}

func TestSDKLogger_Enabled(t *testing.T) {
	lp := NewLoggerProvider()
	logger := lp.Logger("test")
	ctx := context.Background()

	if !logger.Enabled(ctx, SeverityInfo) {
		t.Error("Enabled should return true for INFO")
	}
	if logger.Enabled(ctx, SeverityTrace) {
		t.Error("Enabled should return false for TRACE")
	}
}

func TestSimpleLogRecordProcessor(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewSimpleLogRecordProcessor(exporter)
	ctx := context.Background()

	record := LogRecord{
		Timestamp:      time.Now(),
		SeverityNumber: SeverityWarn,
		Body:           "warning",
	}

	if err := processor.OnEmit(ctx, record); err != nil {
		t.Errorf("OnEmit error = %v", err)
	}

	records := exporter.Records()
	if len(records) != 1 {
		t.Fatalf("expected 1 record, got %d", len(records))
	}
	if records[0].Body != "warning" {
		t.Errorf("Body = %v, want 'warning'", records[0].Body)
	}

	if err := processor.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown error = %v", err)
	}

	if err := processor.ForceFlush(ctx); err != nil {
		t.Errorf("ForceFlush error = %v", err)
	}
}

func TestBatchLogRecordProcessor(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewBatchLogRecordProcessor(
		exporter,
		WithMaxQueueSize(100),
		WithMaxBatchSize(2),
		WithBatchTimeout(100*time.Millisecond),
		WithExportTimeout(5*time.Second),
	)
	defer processor.Shutdown(context.Background())

	ctx := context.Background()
	for i := 0; i < 5; i++ {
		record := LogRecord{
			Timestamp:      time.Now(),
			SeverityNumber: SeverityInfo,
			Body:           i,
		}
		if err := processor.OnEmit(ctx, record); err != nil {
			t.Errorf("OnEmit error = %v", err)
		}
	}

	// Wait for batch timeout
	time.Sleep(200 * time.Millisecond)

	records := exporter.Records()
	if len(records) == 0 {
		t.Error("expected some records to be exported")
	}
}

func TestBatchLogRecordProcessor_ForceFlush(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewBatchLogRecordProcessor(exporter, WithMaxBatchSize(100))
	defer processor.Shutdown(context.Background())

	ctx := context.Background()
	record := LogRecord{
		Timestamp:      time.Now(),
		SeverityNumber: SeverityError,
		Body:           "error",
	}
	processor.OnEmit(ctx, record)

	if err := processor.ForceFlush(ctx); err != nil {
		t.Errorf("ForceFlush error = %v", err)
	}

	records := exporter.Records()
	if len(records) != 1 {
		t.Fatalf("expected 1 record after flush, got %d", len(records))
	}
}

func TestBatchLogRecordProcessor_QueueFull(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewBatchLogRecordProcessor(
		exporter,
		WithMaxQueueSize(1),
		WithBatchTimeout(10*time.Second),
	)
	defer processor.Shutdown(context.Background())

	ctx := context.Background()
	// Fill the queue
	processor.OnEmit(ctx, LogRecord{Body: "first"})

	// Next emit should fail since queue is full and we're not draining
	err := processor.OnEmit(ctx, LogRecord{Body: "second"})
	if err == nil {
		t.Error("expected error when queue is full")
	}
}

func TestBatchLogRecordProcessor_Shutdown(t *testing.T) {
	exporter := &testLogExporter{}
	processor := NewBatchLogRecordProcessor(exporter)
	ctx := context.Background()

	processor.OnEmit(ctx, LogRecord{Body: "before shutdown"})
	if err := processor.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown error = %v", err)
	}

	// Double shutdown should be safe
	if err := processor.Shutdown(ctx); err != nil {
		t.Errorf("Shutdown second call error = %v", err)
	}
}

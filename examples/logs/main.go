// OTLP Logs Signal Example
// 演示 OpenTelemetry Logs 信号的使用
// 遵循 OTLP v1.5.0 协议规范
package main

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"syscall"
	"time"

	"go.opentelemetry.io/otel/attribute"
)

// LogSeverity 日志严重级别 (OTLP v1.5.0 标准)
type LogSeverity int32

const (
	SeverityTrace LogSeverity = 1
	SeverityDebug LogSeverity = 5
	SeverityInfo  LogSeverity = 9
	SeverityWarn  LogSeverity = 13
	SeverityError LogSeverity = 17
	SeverityFatal LogSeverity = 21
)

func (s LogSeverity) String() string {
	switch {
	case s <= 4:
		return "TRACE"
	case s <= 8:
		return "DEBUG"
	case s <= 12:
		return "INFO"
	case s <= 16:
		return "WARN"
	case s <= 20:
		return "ERROR"
	default:
		return "FATAL"
	}
}

// LogRecord 日志记录
type LogRecord struct {
	Timestamp         time.Time
	ObservedTimestamp time.Time
	Severity          LogSeverity
	SeverityText      string
	Body              string
	Attributes        []attribute.KeyValue
	TraceID           string
	SpanID            string
}

// LogExporter 日志导出器接口
type LogExporter interface {
	Export(ctx context.Context, records []*LogRecord) error
	ForceFlush(ctx context.Context) error
	Shutdown(ctx context.Context) error
}

// ConsoleLogExporter 控制台导出器
type ConsoleLogExporter struct{}

func NewConsoleLogExporter() *ConsoleLogExporter {
	return &ConsoleLogExporter{}
}

func (e *ConsoleLogExporter) Export(ctx context.Context, records []*LogRecord) error {
	for _, r := range records {
		fmt.Printf("[%s] %-5s %s",
			r.Timestamp.Format("15:04:05.000"),
			r.SeverityText,
			r.Body)
		if len(r.Attributes) > 0 {
			fmt.Printf(" | attrs=%v", r.Attributes)
		}
		if r.TraceID != "" {
			fmt.Printf(" | trace=%s", r.TraceID[:8])
		}
		fmt.Println()
	}
	return nil
}

func (e *ConsoleLogExporter) ForceFlush(ctx context.Context) error { return nil }
func (e *ConsoleLogExporter) Shutdown(ctx context.Context) error   { return nil }

// BatchLogProcessor 批量处理器
type BatchLogProcessor struct {
	exporter      LogExporter
	maxQueueSize  int
	batchSize     int
	flushInterval time.Duration
	queue         []*LogRecord
	stopCh        chan struct{}
	doneCh        chan struct{}
}

func NewBatchLogProcessor(exporter LogExporter) *BatchLogProcessor {
	p := &BatchLogProcessor{
		exporter:      exporter,
		maxQueueSize:  2048,
		batchSize:     512,
		flushInterval: 5 * time.Second,
		queue:         make([]*LogRecord, 0, 2048),
		stopCh:        make(chan struct{}),
		doneCh:        make(chan struct{}),
	}
	go p.loop()
	return p
}

func (p *BatchLogProcessor) OnEmit(ctx context.Context, record *LogRecord) {
	p.queue = append(p.queue, record)
	if len(p.queue) >= p.batchSize {
		p.flush()
	}
}

func (p *BatchLogProcessor) loop() {
	ticker := time.NewTicker(p.flushInterval)
	defer ticker.Stop()
	defer close(p.doneCh)

	for {
		select {
		case <-ticker.C:
			p.flush()
		case <-p.stopCh:
			p.flush()
			return
		}
	}
}

func (p *BatchLogProcessor) flush() {
	if len(p.queue) == 0 {
		return
	}
	records := make([]*LogRecord, len(p.queue))
	copy(records, p.queue)
	p.queue = p.queue[:0]
	p.exporter.Export(context.Background(), records)
}

func (p *BatchLogProcessor) Shutdown(ctx context.Context) error {
	close(p.stopCh)
	<-p.doneCh
	return p.exporter.Shutdown(ctx)
}

// Logger 日志记录器
type Logger struct {
	name       string
	processor  *BatchLogProcessor
	attributes []attribute.KeyValue
}

func (l *Logger) Emit(ctx context.Context, severity LogSeverity, body string, attrs ...attribute.KeyValue) {
	now := time.Now()
	allAttrs := append(l.attributes, attrs...)

	record := &LogRecord{
		Timestamp:         now,
		ObservedTimestamp: now,
		Severity:          severity,
		SeverityText:      severity.String(),
		Body:              body,
		Attributes:        allAttrs,
	}
	l.processor.OnEmit(ctx, record)
}

func (l *Logger) Debug(ctx context.Context, msg string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityDebug, msg, attrs...)
}

func (l *Logger) Info(ctx context.Context, msg string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityInfo, msg, attrs...)
}

func (l *Logger) Warn(ctx context.Context, msg string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityWarn, msg, attrs...)
}

func (l *Logger) Error(ctx context.Context, msg string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityError, msg, attrs...)
}

// LoggerProvider 日志提供程序
type LoggerProvider struct {
	processor *BatchLogProcessor
}

func NewLoggerProvider(exporter LogExporter) *LoggerProvider {
	return &LoggerProvider{
		processor: NewBatchLogProcessor(exporter),
	}
}

func (p *LoggerProvider) GetLogger(name string) *Logger {
	return &Logger{
		name:      name,
		processor: p.processor,
	}
}

func (p *LoggerProvider) Shutdown(ctx context.Context) error {
	return p.processor.Shutdown(ctx)
}

func main() {
	ctx := context.Background()

	separator := "============================================================"
	fmt.Println(separator)
	fmt.Println("OTLP Logs Signal Demo")
	fmt.Println("OTLP Protocol v1.5.0 / SemConv v1.30.0")
	fmt.Println(separator)

	// 创建日志提供程序
	exporter := NewConsoleLogExporter()
	provider := NewLoggerProvider(exporter)
	defer provider.Shutdown(ctx)

	// 获取 Logger
	logger := provider.GetLogger("logs-demo")

	// 记录不同级别的日志
	logger.Info(ctx, "Application started",
		attribute.String("service", "logs-demo"),
		attribute.String("version", "1.0.0"))

	logger.Debug(ctx, "Initializing components",
		attribute.String("component", "database"))

	logger.Info(ctx, "Connected to database",
		attribute.String("host", "localhost"),
		attribute.Int("port", 5432))

	// 模拟业务操作日志
	for i := 1; i <= 5; i++ {
		logger.Info(ctx, "Processing request",
			attribute.Int("request_id", i),
			attribute.String("method", "GET"),
			attribute.String("path", "/api/users"))

		if i == 3 {
			logger.Warn(ctx, "High response time detected",
				attribute.Int("request_id", i),
				attribute.Float64("latency_ms", 1250.5))
		}

		time.Sleep(100 * time.Millisecond)
	}

	// 模拟错误日志
	logger.Error(ctx, "Failed to connect to cache",
		attribute.String("cache", "redis"),
		attribute.String("error", "connection refused"),
		attribute.Int("retry_count", 3))

	logger.Info(ctx, "Application shutting down",
		attribute.Int("uptime_seconds", 30))

	fmt.Println("\n" + separator)
	fmt.Println("Logs Demo Complete!")
	fmt.Println(separator)

	// 等待信号优雅退出
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)

	select {
	case <-sigCh:
		fmt.Println("\nReceived shutdown signal")
	case <-time.After(2 * time.Second):
	}
}

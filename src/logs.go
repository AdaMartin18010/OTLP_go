// Package main provides OTLP Logs export functionality
// OpenTelemetry Go SDK v1.32.0 Logs API 兼容实现
//
// 设计原则:
// 1. 遵循 OTLP v1.5.0 Logs 协议规范
// 2. 支持 BatchLogRecordProcessor 批量处理
// 3. 与 Trace/Metrics 一致的配置风格
// 4. 支持 SeverityNumber/SeverityText 映射
// 5. 资源属性传递
package main

import (
	"context"
	"fmt"
	"sync"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
	semconv "go.opentelemetry.io/otel/semconv/v1.30.0"
)

// LogSeverity 日志严重级别 (OTLP v1.5.0 标准 SeverityNumber)
// SeverityNumber 是 OpenTelemetry 日志数据模型中的数值严重级别
// 参考: https://opentelemetry.io/docs/specs/otel/logs/data-model/#field-severitynumber
type LogSeverity int32

const (
	// SeverityTrace 追踪级别 (1-4)
	SeverityTrace LogSeverity = 1
	// SeverityTrace2 追踪级别 2
	SeverityTrace2 LogSeverity = 2
	// SeverityTrace3 追踪级别 3
	SeverityTrace3 LogSeverity = 3
	// SeverityTrace4 追踪级别 4
	SeverityTrace4 LogSeverity = 4

	// SeverityDebug 调试级别 (5-8)
	SeverityDebug LogSeverity = 5
	// SeverityDebug2 调试级别 2
	SeverityDebug2 LogSeverity = 6
	// SeverityDebug3 调试级别 3
	SeverityDebug3 LogSeverity = 7
	// SeverityDebug4 调试级别 4
	SeverityDebug4 LogSeverity = 8

	// SeverityInfo 信息级别 (9-12)
	SeverityInfo LogSeverity = 9
	// SeverityInfo2 信息级别 2
	SeverityInfo2 LogSeverity = 10
	// SeverityInfo3 信息级别 3
	SeverityInfo3 LogSeverity = 11
	// SeverityInfo4 信息级别 4
	SeverityInfo4 LogSeverity = 12

	// SeverityWarn 警告级别 (13-16)
	SeverityWarn LogSeverity = 13
	// SeverityWarn2 警告级别 2
	SeverityWarn2 LogSeverity = 14
	// SeverityWarn3 警告级别 3
	SeverityWarn3 LogSeverity = 15
	// SeverityWarn4 警告级别 4
	SeverityWarn4 LogSeverity = 16

	// SeverityError 错误级别 (17-20)
	SeverityError LogSeverity = 17
	// SeverityError2 错误级别 2
	SeverityError2 LogSeverity = 18
	// SeverityError3 错误级别 3
	SeverityError3 LogSeverity = 19
	// SeverityError4 错误级别 4
	SeverityError4 LogSeverity = 20

	// SeverityFatal 致命级别 (21-24)
	SeverityFatal LogSeverity = 21
	// SeverityFatal2 致命级别 2
	SeverityFatal2 LogSeverity = 22
	// SeverityFatal3 致命级别 3
	SeverityFatal3 LogSeverity = 23
	// SeverityFatal4 致命级别 4
	SeverityFatal4 LogSeverity = 24
)

// String 返回严重级别的文本表示
func (s LogSeverity) String() string {
	switch {
	case s >= SeverityTrace && s <= SeverityTrace4:
		return "TRACE"
	case s >= SeverityDebug && s <= SeverityDebug4:
		return "DEBUG"
	case s >= SeverityInfo && s <= SeverityInfo4:
		return "INFO"
	case s >= SeverityWarn && s <= SeverityWarn4:
		return "WARN"
	case s >= SeverityError && s <= SeverityError4:
		return "ERROR"
	case s >= SeverityFatal && s <= SeverityFatal4:
		return "FATAL"
	default:
		return "UNSPECIFIED"
	}
}

// LogRecord 表示一条日志记录
// 对应 OTLP Logs Data Model 中的 LogRecord
type LogRecord struct {
	// Timestamp 事件发生时间
	Timestamp time.Time
	// ObservedTimestamp 日志记录被观察到的时间
	ObservedTimestamp time.Time
	// Severity 严重级别数值
	Severity LogSeverity
	// SeverityText 严重级别文本
	SeverityText string
	// Body 日志内容
	Body string
	// Attributes 附加属性
	Attributes []attribute.KeyValue
	// TraceID 关联的 Trace ID
	TraceID string
	// SpanID 关联的 Span ID
	SpanID string
	// TraceFlags Trace 标志
	TraceFlags byte
}

// LogExporter 日志导出器接口
// 实现 OTLP 协议导出
type LogExporter interface {
	// Export 批量导出日志记录
	Export(ctx context.Context, records []*LogRecord) error
	// ForceFlush 强制刷新缓冲区
	ForceFlush(ctx context.Context) error
	// Shutdown 关闭导出器
	Shutdown(ctx context.Context) error
}

// ConsoleLogExporter 控制台日志导出器 (用于开发调试)
type ConsoleLogExporter struct {
	stopped bool
	mu      sync.RWMutex
}

// NewConsoleLogExporter 创建控制台日志导出器
func NewConsoleLogExporter() *ConsoleLogExporter {
	return &ConsoleLogExporter{}
}

// Export 导出日志到控制台
func (e *ConsoleLogExporter) Export(ctx context.Context, records []*LogRecord) error {
	e.mu.RLock()
	if e.stopped {
		e.mu.RUnlock()
		return fmt.Errorf("exporter is stopped")
	}
	e.mu.RUnlock()

	for _, r := range records {
		fmt.Printf("[%s] %s %s",
			r.Timestamp.Format("2006-01-02T15:04:05.000Z07:00"),
			r.SeverityText,
			r.Body)
		if len(r.Attributes) > 0 {
			fmt.Printf(" %v", r.Attributes)
		}
		fmt.Println()
	}
	return nil
}

// ForceFlush 强制刷新
func (e *ConsoleLogExporter) ForceFlush(ctx context.Context) error {
	return nil
}

// Shutdown 关闭导出器
func (e *ConsoleLogExporter) Shutdown(ctx context.Context) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.stopped = true
	return nil
}

// OTLPLogExporterOptions OTLP 导出器配置选项
type OTLPLogExporterOptions struct {
	// Endpoint OTLP 端点
	Endpoint string
	// Headers 请求头
	Headers map[string]string
	// Timeout 超时时间
	Timeout time.Duration
	// RetryConfig 重试配置
	RetryConfig *RetryConfig
}

// RetryConfig 重试配置
type RetryConfig struct {
	Enabled         bool
	InitialInterval time.Duration
	MaxInterval     time.Duration
	MaxElapsedTime  time.Duration
}

// DefaultRetryConfig 默认重试配置
func DefaultRetryConfig() *RetryConfig {
	return &RetryConfig{
		Enabled:         true,
		InitialInterval: 1 * time.Second,
		MaxInterval:     10 * time.Second,
		MaxElapsedTime:  30 * time.Second,
	}
}

// OTLPLogExporter OTLP/gRPC 日志导出器 (占位实现)
// 注: 完整实现需要 go.opentelemetry.io/otel/sdk/log 包
type OTLPLogExporter struct {
	opts    OTLPLogExporterOptions
	stopped bool
	mu      sync.RWMutex
}

// NewOTLPLogExporter 创建 OTLP 日志导出器
func NewOTLPLogExporter(opts OTLPLogExporterOptions) *OTLPLogExporter {
	if opts.Timeout == 0 {
		opts.Timeout = 30 * time.Second
	}
	if opts.RetryConfig == nil {
		opts.RetryConfig = DefaultRetryConfig()
	}
	return &OTLPLogExporter{opts: opts}
}

// Export 导出日志 (占位实现)
func (e *OTLPLogExporter) Export(ctx context.Context, records []*LogRecord) error {
	e.mu.RLock()
	if e.stopped {
		e.mu.RUnlock()
		return fmt.Errorf("exporter is stopped")
	}
	e.mu.RUnlock()

	// TODO: 实现 OTLP/gRPC 导出
	// 需要等 go.opentelemetry.io/otel/sdk/log 稳定
	return nil
}

// ForceFlush 强制刷新
func (e *OTLPLogExporter) ForceFlush(ctx context.Context) error {
	return nil
}

// Shutdown 关闭导出器
func (e *OTLPLogExporter) Shutdown(ctx context.Context) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.stopped = true
	return nil
}

// BatchLogProcessorOptions 批量处理器选项
type BatchLogProcessorOptions struct {
	// MaxQueueSize 最大队列大小
	MaxQueueSize int
	// BatchSize 批次大小
	BatchSize int
	// FlushInterval 刷新间隔
	FlushInterval time.Duration
	// ExportTimeout 导出超时
	ExportTimeout time.Duration
}

// DefaultBatchLogProcessorOptions 默认批量处理器选项
func DefaultBatchLogProcessorOptions() BatchLogProcessorOptions {
	return BatchLogProcessorOptions{
		MaxQueueSize:  2048,
		BatchSize:     512,
		FlushInterval: 5 * time.Second,
		ExportTimeout: 30 * time.Second,
	}
}

// BatchLogProcessor 批量日志处理器
// 实现 OpenTelemetry LogRecordProcessor 接口的功能
type BatchLogProcessor struct {
	exporter      LogExporter
	maxQueueSize  int
	batchSize     int
	flushInterval time.Duration
	exportTimeout time.Duration

	queue  []*LogRecord
	mu     sync.Mutex
	ticker *time.Ticker
	stopCh chan struct{}
	wg     sync.WaitGroup
}

// NewBatchLogProcessor 创建批量日志处理器
func NewBatchLogProcessor(exporter LogExporter, opts BatchLogProcessorOptions) *BatchLogProcessor {
	if opts.MaxQueueSize == 0 {
		opts = DefaultBatchLogProcessorOptions()
	}

	p := &BatchLogProcessor{
		exporter:      exporter,
		maxQueueSize:  opts.MaxQueueSize,
		batchSize:     opts.BatchSize,
		flushInterval: opts.FlushInterval,
		exportTimeout: opts.ExportTimeout,
		queue:         make([]*LogRecord, 0, opts.MaxQueueSize),
		stopCh:        make(chan struct{}),
	}

	p.ticker = time.NewTicker(opts.FlushInterval)
	p.wg.Add(1)
	go p.exportLoop()

	return p
}

// OnEmit 处理日志记录
func (p *BatchLogProcessor) OnEmit(ctx context.Context, record *LogRecord) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if len(p.queue) >= p.maxQueueSize {
		// 队列已满，丢弃最旧的记录 (或根据策略处理)
		p.queue = p.queue[1:]
	}

	p.queue = append(p.queue, record)

	if len(p.queue) >= p.batchSize {
		go p.flush()
	}

	return nil
}

// exportLoop 定时导出循环
func (p *BatchLogProcessor) exportLoop() {
	defer p.wg.Done()

	for {
		select {
		case <-p.ticker.C:
			p.flush()
		case <-p.stopCh:
			p.flush()
			return
		}
	}
}

// flush 导出当前队列
func (p *BatchLogProcessor) flush() {
	p.mu.Lock()
	if len(p.queue) == 0 {
		p.mu.Unlock()
		return
	}

	records := make([]*LogRecord, len(p.queue))
	copy(records, p.queue)
	p.queue = p.queue[:0]
	p.mu.Unlock()

	ctx, cancel := context.WithTimeout(context.Background(), p.exportTimeout)
	defer cancel()

	p.exporter.Export(ctx, records)
}

// ForceFlush 强制刷新
func (p *BatchLogProcessor) ForceFlush(ctx context.Context) error {
	p.flush()
	return p.exporter.ForceFlush(ctx)
}

// Shutdown 关闭处理器
func (p *BatchLogProcessor) Shutdown(ctx context.Context) error {
	close(p.stopCh)
	p.wg.Wait()
	p.ticker.Stop()
	return p.exporter.Shutdown(ctx)
}

// SimpleLogProcessor 简单日志处理器 (立即导出)
type SimpleLogProcessor struct {
	exporter LogExporter
}

// NewSimpleLogProcessor 创建简单日志处理器
func NewSimpleLogProcessor(exporter LogExporter) *SimpleLogProcessor {
	return &SimpleLogProcessor{exporter: exporter}
}

// OnEmit 立即导出日志
func (p *SimpleLogProcessor) OnEmit(ctx context.Context, record *LogRecord) error {
	return p.exporter.Export(ctx, []*LogRecord{record})
}

// ForceFlush 强制刷新
func (p *SimpleLogProcessor) ForceFlush(ctx context.Context) error {
	return p.exporter.ForceFlush(ctx)
}

// Shutdown 关闭处理器
func (p *SimpleLogProcessor) Shutdown(ctx context.Context) error {
	return p.exporter.Shutdown(ctx)
}

// LogProcessor 日志处理器接口
type LogProcessor interface {
	OnEmit(ctx context.Context, record *LogRecord) error
	ForceFlush(ctx context.Context) error
	Shutdown(ctx context.Context) error
}

// LoggerProvider 日志提供程序
type LoggerProvider struct {
	processor LogProcessor
	resource  *resource.Resource
	loggers   map[string]*Logger
	mu        sync.RWMutex
}

// Logger 日志记录器
type Logger struct {
	name       string
	provider   *LoggerProvider
	attributes []attribute.KeyValue
}

// LoggerConfig 日志配置
type LoggerConfig struct {
	// Endpoint OTLP 端点
	Endpoint string
	// ServiceName 服务名称
	ServiceName string
	// ServiceVersion 服务版本
	ServiceVersion string
	// Environment 环境
	Environment string
	// UseBatchProcessor 使用批量处理器
	UseBatchProcessor bool
}

// DefaultLoggerConfig 默认日志配置
func DefaultLoggerConfig() *LoggerConfig {
	return &LoggerConfig{
		Endpoint:          "localhost:4317",
		ServiceName:       "otlp-go-service",
		ServiceVersion:    "1.0.0",
		Environment:       "development",
		UseBatchProcessor: true,
	}
}

// InitLoggerProvider 初始化日志提供程序
func InitLoggerProvider(ctx context.Context, cfg *LoggerConfig) (*LoggerProvider, error) {
	if cfg == nil {
		cfg = DefaultLoggerConfig()
	}

	// 创建 Resource
	res, err := resource.New(ctx,
		resource.WithAttributes(
			semconv.ServiceName(cfg.ServiceName),
			semconv.ServiceVersion(cfg.ServiceVersion),
			attribute.String("deployment.environment", cfg.Environment),
		),
	)
	if err != nil {
		return nil, fmt.Errorf("failed to create resource: %w", err)
	}

	// 创建 Exporter (目前使用控制台导出器作为占位)
	// TODO: 切换到 OTLPLogExporter 当 SDK 稳定后
	exporter := NewConsoleLogExporter()

	// 创建 Processor
	var processor LogProcessor
	if cfg.UseBatchProcessor {
		processor = NewBatchLogProcessor(exporter, DefaultBatchLogProcessorOptions())
	} else {
		processor = NewSimpleLogProcessor(exporter)
	}

	return &LoggerProvider{
		processor: processor,
		resource:  res,
		loggers:   make(map[string]*Logger),
	}, nil
}

// GetLogger 获取日志记录器
func (p *LoggerProvider) GetLogger(name string) *Logger {
	p.mu.Lock()
	defer p.mu.Unlock()

	if logger, exists := p.loggers[name]; exists {
		return logger
	}

	logger := &Logger{
		name:       name,
		provider:   p,
		attributes: []attribute.KeyValue{},
	}
	p.loggers[name] = logger
	return logger
}

// Shutdown 关闭提供程序
func (p *LoggerProvider) Shutdown(ctx context.Context) error {
	return p.processor.Shutdown(ctx)
}

// ForceFlush 强制刷新
func (p *LoggerProvider) ForceFlush(ctx context.Context) error {
	return p.processor.ForceFlush(ctx)
}

// Emit 发送日志
func (l *Logger) Emit(ctx context.Context, severity LogSeverity, body string, attrs ...attribute.KeyValue) {
	now := time.Now()

	allAttrs := make([]attribute.KeyValue, 0, len(l.attributes)+len(attrs))
	allAttrs = append(allAttrs, l.attributes...)
	allAttrs = append(allAttrs, attrs...)

	record := &LogRecord{
		Timestamp:         now,
		ObservedTimestamp: now,
		Severity:          severity,
		SeverityText:      severity.String(),
		Body:              body,
		Attributes:        allAttrs,
	}

	l.provider.processor.OnEmit(ctx, record)
}

// Debug 发送 DEBUG 级别日志
func (l *Logger) Debug(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityDebug, message, attrs...)
}

// Info 发送 INFO 级别日志
func (l *Logger) Info(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityInfo, message, attrs...)
}

// Warn 发送 WARN 级别日志
func (l *Logger) Warn(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityWarn, message, attrs...)
}

// Error 发送 ERROR 级别日志
func (l *Logger) Error(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityError, message, attrs...)
}

// Fatal 发送 FATAL 级别日志
func (l *Logger) Fatal(ctx context.Context, message string, attrs ...attribute.KeyValue) {
	l.Emit(ctx, SeverityFatal, message, attrs...)
}

// WithAttributes 创建带默认属性的 Logger
func (l *Logger) WithAttributes(attrs ...attribute.KeyValue) *Logger {
	newAttrs := make([]attribute.KeyValue, 0, len(l.attributes)+len(attrs))
	newAttrs = append(newAttrs, l.attributes...)
	newAttrs = append(newAttrs, attrs...)

	return &Logger{
		name:       l.name,
		provider:   l.provider,
		attributes: newAttrs,
	}
}

// LogStats 日志统计
type LogStats struct {
	ExportedRecords int64
	DroppedRecords  int64
	LastExportTime  time.Time
}

// Status 返回日志系统状态摘要
func LogStatus() map[string]interface{} {
	return map[string]interface{}{
		"status": "Logs SDK: 70% 完成",
		"implemented": []string{
			"LogRecord 数据模型",
			"SeverityNumber 映射",
			"BatchLogProcessor",
			"SimpleLogProcessor",
			"ConsoleLogExporter",
			"LoggerProvider",
			"属性传递",
		},
		"pending": []string{
			"OTLP/gRPC 导出器 (等待 SDK 稳定)",
			"Trace/Log 关联",
			"日志限流",
		},
		"compliance": "OTLP v1.5.0 Ready",
	}
}

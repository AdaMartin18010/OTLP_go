// Package logs provides OpenTelemetry Logs API implementation for the OTLP Go SDK.
//
// This file contains the SDK layer with LoggerProvider implementation,
// SimpleLogRecordProcessor, BatchLogRecordProcessor, and exporter interfaces.
package logs

import (
	"context"
	"fmt"
	"sync"
	"time"
)

// LogRecordProcessor processes log records.
type LogRecordProcessor interface {
	OnEmit(ctx context.Context, record LogRecord) error
	Shutdown(ctx context.Context) error
	ForceFlush(ctx context.Context) error
}

// LogRecordExporter exports log records.
type LogRecordExporter interface {
	Export(ctx context.Context, records []LogRecord) error
	Shutdown(ctx context.Context) error
}

// LoggerProviderOption configures a LoggerProvider.
type LoggerProviderOption func(*loggerProviderConfig)

type loggerProviderConfig struct {
	resource   interface{}
	processors []LogRecordProcessor
}

// WithResource sets the resource for the LoggerProvider.
func WithResource(resource interface{}) LoggerProviderOption {
	return func(cfg *loggerProviderConfig) {
		cfg.resource = resource
	}
}

// WithProcessor adds a processor to the LoggerProvider.
func WithProcessor(processor LogRecordProcessor) LoggerProviderOption {
	return func(cfg *loggerProviderConfig) {
		cfg.processors = append(cfg.processors, processor)
	}
}

// NewLoggerProvider creates a new LoggerProvider with the given options.
func NewLoggerProvider(opts ...LoggerProviderOption) *loggerProvider {
	cfg := &loggerProviderConfig{}
	for _, opt := range opts {
		opt(cfg)
	}
	return &loggerProvider{
		loggers:    make(map[string]*logger),
		processors: cfg.processors,
		resource:   cfg.resource,
	}
}

type loggerProvider struct {
	loggers    map[string]*logger
	processors []LogRecordProcessor
	resource   interface{}
	mu         sync.RWMutex
	stopped    bool
}

// Logger gets or creates a logger with the given name.
func (p *loggerProvider) Logger(name string) Logger {
	p.mu.RLock()
	if p.stopped {
		p.mu.RUnlock()
		return &logger{name: name, provider: p}
	}
	if l, ok := p.loggers[name]; ok {
		p.mu.RUnlock()
		return l
	}
	p.mu.RUnlock()

	p.mu.Lock()
	defer p.mu.Unlock()
	if l, ok := p.loggers[name]; ok {
		return l
	}
	l := &logger{
		name:     name,
		provider: p,
	}
	p.loggers[name] = l
	return l
}

// Shutdown shuts down the provider and all its processors.
func (p *loggerProvider) Shutdown(ctx context.Context) error {
	p.mu.Lock()
	if p.stopped {
		p.mu.Unlock()
		return nil
	}
	p.stopped = true
	p.mu.Unlock()

	var errs []error
	for _, proc := range p.processors {
		if err := proc.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	if len(errs) > 0 {
		return errs[0]
	}
	return nil
}

// ForceFlush flushes all processors.
func (p *loggerProvider) ForceFlush(ctx context.Context) error {
	p.mu.RLock()
	processors := make([]LogRecordProcessor, len(p.processors))
	copy(processors, p.processors)
	p.mu.RUnlock()

	var errs []error
	for _, proc := range processors {
		if err := proc.ForceFlush(ctx); err != nil {
			errs = append(errs, err)
		}
	}
	if len(errs) > 0 {
		return errs[0]
	}
	return nil
}

type logger struct {
	provider *loggerProvider
	name     string
}

// Emit emits a log record through all processors.
func (l *logger) Emit(record LogRecord) {
	if l.provider == nil {
		return
	}
	ctx := context.Background()
	l.provider.mu.RLock()
	processors := l.provider.processors
	l.provider.mu.RUnlock()

	for _, proc := range processors {
		_ = proc.OnEmit(ctx, record)
	}
}

// Enabled returns true if the given severity is enabled.
func (l *logger) Enabled(ctx context.Context, severity SeverityNumber) bool {
	return severity >= SeverityInfo
}

// SimpleLogRecordProcessor immediately exports each log record.
type SimpleLogRecordProcessor struct {
	exporter LogRecordExporter
}

// NewSimpleLogRecordProcessor creates a new SimpleLogRecordProcessor.
func NewSimpleLogRecordProcessor(exporter LogRecordExporter) *SimpleLogRecordProcessor {
	return &SimpleLogRecordProcessor{exporter: exporter}
}

// OnEmit exports a single log record immediately.
func (p *SimpleLogRecordProcessor) OnEmit(ctx context.Context, record LogRecord) error {
	return p.exporter.Export(ctx, []LogRecord{record})
}

// Shutdown shuts down the processor.
func (p *SimpleLogRecordProcessor) Shutdown(ctx context.Context) error {
	return p.exporter.Shutdown(ctx)
}

// ForceFlush is a no-op for SimpleLogRecordProcessor.
func (p *SimpleLogRecordProcessor) ForceFlush(ctx context.Context) error {
	return nil
}

// BatchLogRecordProcessor batches log records before exporting.
type BatchLogRecordProcessor struct {
	exporter      LogRecordExporter
	maxQueueSize  int
	maxBatchSize  int
	batchTimeout  time.Duration
	exportTimeout time.Duration
	queue         chan LogRecord
	batch         []LogRecord
	ticker        *time.Ticker
	done          chan struct{}
	wg            sync.WaitGroup
	mu            sync.Mutex
	stopped       bool
}

// BatchLogRecordProcessorOption configures a BatchLogRecordProcessor.
type BatchLogRecordProcessorOption func(*BatchLogRecordProcessor)

// WithMaxQueueSize sets the maximum queue size.
func WithMaxQueueSize(size int) BatchLogRecordProcessorOption {
	return func(b *BatchLogRecordProcessor) {
		b.maxQueueSize = size
	}
}

// WithMaxBatchSize sets the maximum batch size.
func WithMaxBatchSize(size int) BatchLogRecordProcessorOption {
	return func(b *BatchLogRecordProcessor) {
		b.maxBatchSize = size
	}
}

// WithBatchTimeout sets the batch timeout.
func WithBatchTimeout(timeout time.Duration) BatchLogRecordProcessorOption {
	return func(b *BatchLogRecordProcessor) {
		b.batchTimeout = timeout
	}
}

// WithExportTimeout sets the export timeout.
func WithExportTimeout(timeout time.Duration) BatchLogRecordProcessorOption {
	return func(b *BatchLogRecordProcessor) {
		b.exportTimeout = timeout
	}
}

// NewBatchLogRecordProcessor creates a new BatchLogRecordProcessor.
func NewBatchLogRecordProcessor(exporter LogRecordExporter, opts ...BatchLogRecordProcessorOption) *BatchLogRecordProcessor {
	b := &BatchLogRecordProcessor{
		exporter:      exporter,
		maxQueueSize:  2048,
		maxBatchSize:  512,
		batchTimeout:  5 * time.Second,
		exportTimeout: 30 * time.Second,
		queue:         make(chan LogRecord, 2048),
		done:          make(chan struct{}),
	}
	for _, opt := range opts {
		opt(b)
	}
	b.ticker = time.NewTicker(b.batchTimeout)
	b.wg.Add(1)
	go b.run()
	return b
}

// OnEmit adds a log record to the queue.
func (b *BatchLogRecordProcessor) OnEmit(ctx context.Context, record LogRecord) error {
	select {
	case b.queue <- record:
		return nil
	default:
		return fmt.Errorf("log record queue full (max %d)", b.maxQueueSize)
	}
}

// Shutdown shuts down the processor.
func (b *BatchLogRecordProcessor) Shutdown(ctx context.Context) error {
	b.mu.Lock()
	if b.stopped {
		b.mu.Unlock()
		return nil
	}
	b.stopped = true
	b.mu.Unlock()

	close(b.done)
	b.ticker.Stop()
	b.wg.Wait()
	return b.exporter.Shutdown(ctx)
}

// ForceFlush exports the current batch immediately.
func (b *BatchLogRecordProcessor) ForceFlush(ctx context.Context) error {
	b.mu.Lock()
	batch := make([]LogRecord, len(b.batch))
	copy(batch, b.batch)
	b.batch = b.batch[:0]
	b.mu.Unlock()

	if len(batch) > 0 {
		return b.exportBatch(ctx, batch)
	}
	return nil
}

func (b *BatchLogRecordProcessor) run() {
	defer b.wg.Done()
	for {
		select {
		case <-b.done:
			b.exportCurrentBatch()
			// drain remaining
			for {
				select {
				case record := <-b.queue:
					b.mu.Lock()
					b.batch = append(b.batch, record)
					b.mu.Unlock()
				default:
					b.exportCurrentBatch()
					return
				}
			}
		case record := <-b.queue:
			b.mu.Lock()
			b.batch = append(b.batch, record)
			shouldExport := len(b.batch) >= b.maxBatchSize
			b.mu.Unlock()
			if shouldExport {
				b.exportCurrentBatch()
			}
		case <-b.ticker.C:
			b.exportCurrentBatch()
		}
	}
}

func (b *BatchLogRecordProcessor) exportCurrentBatch() {
	b.mu.Lock()
	batch := make([]LogRecord, len(b.batch))
	copy(batch, b.batch)
	b.batch = b.batch[:0]
	b.mu.Unlock()

	if len(batch) == 0 {
		return
	}
	ctx, cancel := context.WithTimeout(context.Background(), b.exportTimeout)
	defer cancel()
	_ = b.exportBatch(ctx, batch)
}

func (b *BatchLogRecordProcessor) exportBatch(ctx context.Context, records []LogRecord) error {
	return b.exporter.Export(ctx, records)
}

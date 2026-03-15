package logs

import (
	"context"
	"sync"
	"time"
)

// BatchProcessor processes log records in batches
type BatchProcessor struct {
	exporter      LogExporter
	maxQueueSize  int
	batchSize     int
	flushInterval time.Duration
	exportTimeout time.Duration

	queue     []*LogRecord
	mu        sync.Mutex
	ticker    *time.Ticker
	stopCh    chan struct{}
	wg        sync.WaitGroup
}

// BatchProcessorOptions configures the batch processor
type BatchProcessorOptions struct {
	MaxQueueSize  int
	BatchSize     int
	FlushInterval time.Duration
	ExportTimeout time.Duration
}

// DefaultBatchProcessorOptions returns default options
func DefaultBatchProcessorOptions() BatchProcessorOptions {
	return BatchProcessorOptions{
		MaxQueueSize:  2048,
		BatchSize:     512,
		FlushInterval: 5 * time.Second,
		ExportTimeout: 30 * time.Second,
	}
}

// NewBatchProcessor creates a new BatchProcessor
func NewBatchProcessor(exporter LogExporter, opts BatchProcessorOptions) *BatchProcessor {
	if opts.MaxQueueSize == 0 {
		opts = DefaultBatchProcessorOptions()
	}

	p := &BatchProcessor{
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

// OnEmit processes a log record
func (p *BatchProcessor) OnEmit(ctx context.Context, record *LogRecord) error {
	p.mu.Lock()
	defer p.mu.Unlock()

	if len(p.queue) >= p.maxQueueSize {
		// Queue full, drop oldest
		p.queue = p.queue[1:]
	}

	p.queue = append(p.queue, record)

	if len(p.queue) >= p.batchSize {
		go p.flush()
	}

	return nil
}

// exportLoop runs the export loop
func (p *BatchProcessor) exportLoop() {
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

// flush exports the current queue
func (p *BatchProcessor) flush() {
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

// ForceFlush forces flush
func (p *BatchProcessor) ForceFlush(ctx context.Context) error {
	p.flush()
	return p.exporter.ForceFlush(ctx)
}

// Shutdown shuts down the processor
func (p *BatchProcessor) Shutdown(ctx context.Context) error {
	close(p.stopCh)
	p.wg.Wait()
	p.ticker.Stop()
	return p.exporter.Shutdown(ctx)
}

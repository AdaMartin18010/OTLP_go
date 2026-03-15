package logs

import (
	"context"
	"fmt"
	"sync"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/resource"
)

// ConsoleExporter exports log records to console
type ConsoleExporter struct {
	stopped bool
	mu      sync.RWMutex
}

// NewConsoleExporter creates a new ConsoleExporter
func NewConsoleExporter() *ConsoleExporter {
	return &ConsoleExporter{}
}

// Export exports log records to console
func (e *ConsoleExporter) Export(ctx context.Context, records []*LogRecord) error {
	e.mu.RLock()
	if e.stopped {
		e.mu.RUnlock()
		return fmt.Errorf("exporter is stopped")
	}
	e.mu.RUnlock()

	for _, r := range records {
		fmt.Printf("[%s] %-5s %s",
			r.Timestamp.Format("15:04:05.000"),
			r.SeverityText,
			r.Body)
		if len(r.Attributes) > 0 {
			fmt.Printf(" %v", r.Attributes)
		}
		fmt.Println()
	}
	return nil
}

// ForceFlush forces flush
func (e *ConsoleExporter) ForceFlush(ctx context.Context) error {
	return nil
}

// Shutdown shuts down the exporter
func (e *ConsoleExporter) Shutdown(ctx context.Context) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.stopped = true
	return nil
}

// SimpleProcessor is a simple synchronous processor
type SimpleProcessor struct {
	exporter LogExporter
}

// NewSimpleProcessor creates a new SimpleProcessor
func NewSimpleProcessor(exporter LogExporter) *SimpleProcessor {
	return &SimpleProcessor{exporter: exporter}
}

// OnEmit processes a log record immediately
func (p *SimpleProcessor) OnEmit(ctx context.Context, record *LogRecord) error {
	return p.exporter.Export(ctx, []*LogRecord{record})
}

// ForceFlush forces flush
func (p *SimpleProcessor) ForceFlush(ctx context.Context) error {
	return p.exporter.ForceFlush(ctx)
}

// Shutdown shuts down the processor
func (p *SimpleProcessor) Shutdown(ctx context.Context) error {
	return p.exporter.Shutdown(ctx)
}

// InitLoggerProvider initializes a LoggerProvider with console exporter
func InitLoggerProvider(cfg *LoggerConfig) (*LoggerProvider, error) {
	if cfg == nil {
		cfg = DefaultLoggerConfig()
	}

	// Create resource
	res, err := createResource(cfg)
	if err != nil {
		return nil, err
	}

	// Create exporter
	exporter := NewConsoleExporter()

	// Create processor
	processor := NewBatchProcessor(exporter, DefaultBatchProcessorOptions())

	// Create provider
	provider := NewLoggerProvider(cfg, processor, res)

	return provider, nil
}

// createResource creates a resource for logs
func createResource(cfg *LoggerConfig) (*resource.Resource, error) {
	return resource.New(context.Background(),
		resource.WithAttributes(
			attribute.String("service.name", cfg.ServiceName),
			attribute.String("service.version", cfg.ServiceVersion),
			attribute.String("deployment.environment", cfg.Environment),
		),
	)
}

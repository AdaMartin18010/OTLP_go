// Package tracer provides eBPF-based zero-intrusion tracing for Go applications.
// This package implements HTTP/gRPC request tracing without code modification.
package tracer

import (
	"context"
	"encoding/binary"
	"fmt"
	"net"
	"os"
	"sync"
	"time"

	"github.com/cilium/ebpf"
	"github.com/cilium/ebpf/link"
	"github.com/cilium/ebpf/perf"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
)

// EBPFTracer implements zero-intrusion tracing using eBPF uprobes
type EBPFTracer struct {
	// eBPF objects
	objs       *tracerObjects
	links      []link.Link
	reader     *perf.Reader
	
	// Configuration
	binaryPath string
	spec       *ebpf.CollectionSpec
	
	// Runtime
	mu        sync.RWMutex
	running   bool
	stopCh    chan struct{}
	wg        sync.WaitGroup
	
	// Tracer provider for creating spans
	tracer    trace.Tracer
	
	// Event handlers
	onHTTPRequest func(event *HTTPEvent)
}

// HTTPEvent represents a captured HTTP request
type HTTPEvent struct {
	Timestamp   uint64
	PID         uint32
	TID         uint32
	Method      [8]byte
	Path        [128]byte
	RemoteAddr  [64]byte
	DurationNs  uint64
	StatusCode  uint16
}

// Config holds tracer configuration
type Config struct {
	// BinaryPath is the path to the Go binary to trace
	BinaryPath string
	
	// Functions to trace
	HTTPFunctions []string
	
	// Buffer size for perf events
	BufferSize int
}

// DefaultConfig returns default configuration
func DefaultConfig(binaryPath string) *Config {
	return &Config{
		BinaryPath: binaryPath,
		HTTPFunctions: []string{
			"net/http.(*Server).ServeHTTP",
		},
		BufferSize: 4096,
	}
}

// New creates a new EBPF tracer
func New(cfg *Config, tracerProvider trace.TracerProvider) (*EBPFTracer, error) {
	if cfg == nil {
		return nil, fmt.Errorf("config is required")
	}
	
	if _, err := os.Stat(cfg.BinaryPath); err != nil {
		return nil, fmt.Errorf("binary not found: %w", err)
	}
	
	t := &EBPFTracer{
		binaryPath: cfg.BinaryPath,
		stopCh:     make(chan struct{}),
		links:      make([]link.Link, 0),
	}
	
	if tracerProvider != nil {
		t.tracer = tracerProvider.Tracer("ebpf-tracer")
	}
	
	return t, nil
}

// Load loads eBPF programs
func (t *EBPFTracer) Load() error {
	// Load pre-compiled eBPF programs
	// In production, these would be embedded using go:embed
	spec, err := loadTracerSpec()
	if err != nil {
		return fmt.Errorf("load spec: %w", err)
	}
	
	t.spec = spec
	
	// Load into kernel
	objs := &tracerObjects{}
	if err := spec.LoadAndAssign(objs, nil); err != nil {
		return fmt.Errorf("load objects: %w", err)
	}
	
	t.objs = objs
	return nil
}

// Attach attaches uprobes to target functions
func (t *EBPFTracer) Attach() error {
	// Open executable
	ex, err := link.OpenExecutable(t.binaryPath)
	if err != nil {
		return fmt.Errorf("open executable: %w", err)
	}
	
	// Attach uprobe to ServeHTTP entry
	l, err := ex.Uprobe("net/http.(*Server).ServeHTTP", t.objs.UprobeServeHTTP, nil)
	if err != nil {
		return fmt.Errorf("attach uprobe: %w", err)
	}
	t.links = append(t.links, l)
	
	// Attach uretprobe to ServeHTTP exit
	l, err = ex.Uretprobe("net/http.(*Server).ServeHTTP", t.objs.UretprobeServeHTTP, nil)
	if err != nil {
		return fmt.Errorf("attach uretprobe: %w", err)
	}
	t.links = append(t.links, l)
	
	return nil
}

// Start starts the event reader
func (t *EBPFTracer) Start(ctx context.Context) error {
	t.mu.Lock()
	defer t.mu.Unlock()
	
	if t.running {
		return nil
	}
	
	// Create perf event reader
	reader, err := perf.NewReader(t.objs.Events, 4096)
	if err != nil {
		return fmt.Errorf("create reader: %w", err)
	}
	t.reader = reader
	
	t.running = true
	t.wg.Add(1)
	go t.readEvents(ctx)
	
	return nil
}

// readEvents reads events from perf buffer
func (t *EBPFTracer) readEvents(ctx context.Context) {
	defer t.wg.Done()
	
	for {
		select {
		case <-ctx.Done():
			return
		case <-t.stopCh:
			return
		default:
		}
		
		record, err := t.reader.Read()
		if err != nil {
			if perf.IsClosed(err) {
				return
			}
			continue
		}
		
		// Parse event
		if len(record.RawSample) < int(unsafe.Sizeof(HTTPEvent{})) {
			continue
		}
		
		event := (*HTTPEvent)(unsafe.Pointer(&record.RawSample[0]))
		
		// Handle event
		if t.onHTTPRequest != nil {
			t.onHTTPRequest(event)
		}
		
		// Create OTel span
		t.createSpan(ctx, event)
	}
}

// createSpan creates an OpenTelemetry span from eBPF event
func (t *EBPFTracer) createSpan(ctx context.Context, event *HTTPEvent) {
	if t.tracer == nil {
		return
	}
	
	method := string(event.Method[:])
	path := string(event.Path[:])
	remoteAddr := string(event.RemoteAddr[:])
	
	// Start span
	_, span := t.tracer.Start(ctx, fmt.Sprintf("%s %s", method, path),
		trace.WithTimestamp(time.Unix(0, int64(event.Timestamp))),
		trace.WithAttributes(
			attribute.String("http.method", method),
			attribute.String("http.path", path),
			attribute.String("http.remote_addr", remoteAddr),
			attribute.Int("http.status_code", int(event.StatusCode)),
			attribute.Int64("http.duration_ns", int64(event.DurationNs)),
		),
	)
	
	// End span with recorded duration
	span.End(trace.WithTimestamp(time.Unix(0, int64(event.Timestamp+event.DurationNs))))
}

// SetHTTPHandler sets HTTP request handler
func (t *EBPFTracer) SetHTTPHandler(handler func(event *HTTPEvent)) {
	t.onHTTPRequest = handler
}

// Stop stops the tracer
func (t *EBPFTracer) Stop() error {
	t.mu.Lock()
	defer t.mu.Unlock()
	
	if !t.running {
		return nil
	}
	
	close(t.stopCh)
	
	// Close reader
	if t.reader != nil {
		t.reader.Close()
	}
	
	// Detach links
	for _, l := range t.links {
		l.Close()
	}
	
	// Wait for goroutine
	t.wg.Wait()
	
	// Close objects
	if t.objs != nil {
		t.objs.Close()
	}
	
	t.running = false
	return nil
}

// IsRunning returns running state
func (t *EBPFTracer) IsRunning() bool {
	t.mu.RLock()
	defer t.mu.RUnlock()
	return t.running
}

// Helper functions for loading eBPF spec
// In production, these would use go:embed for the compiled eBPF bytecode

func loadTracerSpec() (*ebpf.CollectionSpec, error) {
	// This is a placeholder - actual implementation would load from embedded bytecode
	// For now, return an error indicating the spec needs to be compiled
	return nil, fmt.Errorf("eBPF spec not compiled: run 'go generate' to compile eBPF programs")
}

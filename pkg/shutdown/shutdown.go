// Package shutdown provides graceful shutdown utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Shutdown manager for coordinating cleanup
//   - Multi-stage shutdown (PreShutdown, Shutdown, PostShutdown)
//   - Timeout handling
//   - Signal handling
//   - Resource cleanup ordering
//   - Graceful degradation
package shutdown

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"sync"
	"syscall"
	"time"
)

// Stage represents a shutdown stage.
type Stage int

const (
	// StagePreShutdown is the pre-shutdown stage for preparing resources.
	StagePreShutdown Stage = iota
	// StageShutdown is the main shutdown stage.
	StageShutdown
	// StagePostShutdown is the post-shutdown stage for cleanup.
	StagePostShutdown
)

// String returns the string representation of the stage.
func (s Stage) String() string {
	switch s {
	case StagePreShutdown:
		return "PRE_SHUTDOWN"
	case StageShutdown:
		return "SHUTDOWN"
	case StagePostShutdown:
		return "POST_SHUTDOWN"
	default:
		return "UNKNOWN"
	}
}

// ShutdownFunc is a function that performs shutdown operations.
type ShutdownFunc func(ctx context.Context) error

// StageHook represents a hook registered for a specific stage.
type StageHook struct {
	Name     string
	Stage    Stage
	Priority int
	Fn       ShutdownFunc
}

// Orchestrator coordinates multi-stage graceful shutdown.
type Orchestrator struct {
	hooks      []StageHook
	timeout    time.Duration
	mu         sync.RWMutex
	started    bool
	completed  bool
	onError    func(stage Stage, hook string, err error)
	onComplete func()
}

// OrchestratorOption configures the Orchestrator.
type OrchestratorOption func(*Orchestrator)

// WithTimeout sets the default timeout for shutdown operations.
func WithTimeout(timeout time.Duration) OrchestratorOption {
	return func(o *Orchestrator) {
		o.timeout = timeout
	}
}

// WithErrorHandler sets the error handler callback.
func WithErrorHandler(handler func(stage Stage, hook string, err error)) OrchestratorOption {
	return func(o *Orchestrator) {
		o.onError = handler
	}
}

// WithCompleteHandler sets the completion callback.
func WithCompleteHandler(handler func()) OrchestratorOption {
	return func(o *Orchestrator) {
		o.onComplete = handler
	}
}

// NewOrchestrator creates a new shutdown orchestrator.
func NewOrchestrator(opts ...OrchestratorOption) *Orchestrator {
	o := &Orchestrator{
		hooks:   make([]StageHook, 0),
		timeout: 30 * time.Second,
		onError: func(stage Stage, hook string, err error) {
			fmt.Fprintf(os.Stderr, "shutdown error in %s stage for hook %s: %v\n", stage, hook, err)
		},
		onComplete: func() {},
	}

	for _, opt := range opts {
		opt(o)
	}

	return o
}

// Register adds a shutdown hook for a specific stage.
// Lower priority values execute first within the same stage.
func (o *Orchestrator) Register(stage Stage, name string, priority int, fn ShutdownFunc) {
	o.mu.Lock()
	defer o.mu.Unlock()

	if o.started {
		panic("cannot register hooks after shutdown has started")
	}

	o.hooks = append(o.hooks, StageHook{
		Name:     name,
		Stage:    stage,
		Priority: priority,
		Fn:       fn,
	})
}

// RegisterPreShutdown adds a hook to the pre-shutdown stage.
func (o *Orchestrator) RegisterPreShutdown(name string, priority int, fn ShutdownFunc) {
	o.Register(StagePreShutdown, name, priority, fn)
}

// RegisterShutdown adds a hook to the main shutdown stage.
func (o *Orchestrator) RegisterShutdown(name string, priority int, fn ShutdownFunc) {
	o.Register(StageShutdown, name, priority, fn)
}

// RegisterPostShutdown adds a hook to the post-shutdown stage.
func (o *Orchestrator) RegisterPostShutdown(name string, priority int, fn ShutdownFunc) {
	o.Register(StagePostShutdown, name, priority, fn)
}

// Execute runs all shutdown hooks in order.
// Hooks are executed stage by stage, and within each stage by priority.
func (o *Orchestrator) Execute(ctx context.Context) error {
	o.mu.Lock()
	if o.started {
		o.mu.Unlock()
		return fmt.Errorf("shutdown already in progress")
	}
	o.started = true
	o.mu.Unlock()

	defer func() {
		o.mu.Lock()
		o.completed = true
		o.mu.Unlock()
		o.onComplete()
	}()

	// Create timeout context if not provided
	if _, hasDeadline := ctx.Deadline(); !hasDeadline {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, o.timeout)
		defer cancel()
	}

	// Execute each stage in order
	stages := []Stage{StagePreShutdown, StageShutdown, StagePostShutdown}
	for _, stage := range stages {
		if err := o.executeStage(ctx, stage); err != nil {
			return err
		}
	}

	return nil
}

// executeStage executes all hooks for a specific stage.
func (o *Orchestrator) executeStage(ctx context.Context, stage Stage) error {
	o.mu.RLock()
	hooks := make([]StageHook, 0, len(o.hooks))
	for _, h := range o.hooks {
		if h.Stage == stage {
			hooks = append(hooks, h)
		}
	}
	o.mu.RUnlock()

	// Sort by priority (lower first)
	for i := 0; i < len(hooks); i++ {
		for j := i + 1; j < len(hooks); j++ {
			if hooks[j].Priority < hooks[i].Priority {
				hooks[i], hooks[j] = hooks[j], hooks[i]
			}
		}
	}

	// Execute hooks sequentially within a stage
	for _, hook := range hooks {
		if err := o.executeHook(ctx, hook); err != nil {
			o.onError(stage, hook.Name, err)
			// Continue with other hooks even if one fails
		}
	}

	return nil
}

// executeHook executes a single hook with timeout handling.
func (o *Orchestrator) executeHook(ctx context.Context, hook StageHook) error {
	done := make(chan error, 1)

	go func() {
		done <- hook.Fn(ctx)
	}()

	select {
	case err := <-done:
		return err
	case <-ctx.Done():
		return fmt.Errorf("hook %s timed out: %w", hook.Name, ctx.Err())
	}
}

// IsStarted returns true if shutdown has started.
func (o *Orchestrator) IsStarted() bool {
	o.mu.RLock()
	defer o.mu.RUnlock()
	return o.started
}

// IsCompleted returns true if shutdown has completed.
func (o *Orchestrator) IsCompleted() bool {
	o.mu.RLock()
	defer o.mu.RUnlock()
	return o.completed
}

// Wait blocks until shutdown completes.
func (o *Orchestrator) Wait() {
	for {
		o.mu.RLock()
		completed := o.completed
		o.mu.RUnlock()
		if completed {
			return
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// SignalHandler handles OS signals for graceful shutdown.
type SignalHandler struct {
	signals      []os.Signal
	orchestrator *Orchestrator
	mu           sync.RWMutex
	active       bool
	stopCh       chan struct{}
}

// NewSignalHandler creates a new signal handler.
func NewSignalHandler(orch *Orchestrator, signals ...os.Signal) *SignalHandler {
	if len(signals) == 0 {
		signals = []os.Signal{syscall.SIGTERM, syscall.SIGINT}
	}

	return &SignalHandler{
		signals:      signals,
		orchestrator: orch,
		stopCh:       make(chan struct{}),
	}
}

// Start begins listening for signals.
func (sh *SignalHandler) Start() {
	sh.mu.Lock()
	defer sh.mu.Unlock()

	if sh.active {
		return
	}
	sh.active = true

	go sh.listen()
}

// Stop stops the signal handler.
func (sh *SignalHandler) Stop() {
	sh.mu.Lock()
	defer sh.mu.Unlock()

	if !sh.active {
		return
	}
	sh.active = false
	close(sh.stopCh)
}

// listen waits for signals and triggers shutdown.
func (sh *SignalHandler) listen() {
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, sh.signals...)
	defer signal.Stop(sigCh)

	select {
	case sig := <-sigCh:
		fmt.Fprintf(os.Stderr, "Received signal: %v, initiating graceful shutdown...\n", sig)
		ctx := context.Background()
		if err := sh.orchestrator.Execute(ctx); err != nil {
			fmt.Fprintf(os.Stderr, "Shutdown failed: %v\n", err)
			os.Exit(1)
		}
	case <-sh.stopCh:
		return
	}
}

// Shutdowner is the interface for components that need graceful shutdown.
type Shutdowner interface {
	Shutdown(ctx context.Context) error
}

// Registry maintains a list of components that need shutdown.
type Registry struct {
	components []Shutdowner
	mu         sync.RWMutex
}

// NewRegistry creates a new shutdown registry.
func NewRegistry() *Registry {
	return &Registry{
		components: make([]Shutdowner, 0),
	}
}

// Register adds a component to the registry.
func (r *Registry) Register(component Shutdowner) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.components = append(r.components, component)
}

// Shutdown shuts down all registered components.
func (r *Registry) Shutdown(ctx context.Context) error {
	r.mu.RLock()
	components := make([]Shutdowner, len(r.components))
	copy(components, r.components)
	r.mu.RUnlock()

	var errs []error
	for _, c := range components {
		if err := c.Shutdown(ctx); err != nil {
			errs = append(errs, err)
		}
	}

	if len(errs) > 0 {
		return fmt.Errorf("shutdown errors: %v", errs)
	}
	return nil
}

// Len returns the number of registered components.
func (r *Registry) Len() int {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return len(r.components)
}

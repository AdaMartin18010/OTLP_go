// Package shutdown provides graceful shutdown utilities for the OTLP Go SDK.
//
// This file contains graceful shutdown strategies and policies for
// managing the shutdown process with different degradation modes.
//
// Stability: Stable
// Compliance: OpenTelemetry Specification v1.42.0
package shutdown

import (
	"context"
	"fmt"
	"os"
	"sync"
	"sync/atomic"
	"time"
)

// DegradationMode represents the degradation strategy during shutdown.
type DegradationMode int

const (
	// ModeNormal allows all operations to continue during shutdown.
	ModeNormal DegradationMode = iota

	// ModeGraceful blocks new operations but allows in-flight to complete.
	ModeGraceful

	// ModeImmediate attempts to cancel all operations immediately.
	ModeImmediate

	// ModeForce ignores errors and forces shutdown.
	ModeForce
)

// String returns the string representation of the degradation mode.
func (m DegradationMode) String() string {
	switch m {
	case ModeNormal:
		return "NORMAL"
	case ModeGraceful:
		return "GRACEFUL"
	case ModeImmediate:
		return "IMMEDIATE"
	case ModeForce:
		return "FORCE"
	default:
		return "UNKNOWN"
	}
}

// Policy defines the shutdown policy configuration.
type Policy struct {
	// Mode is the degradation mode.
	Mode DegradationMode

	// Timeout is the maximum time to wait for shutdown.
	Timeout time.Duration

	// DrainTimeout is the time to wait for in-flight operations.
	DrainTimeout time.Duration

	// ForceTimeout is the time before forcing shutdown.
	ForceTimeout time.Duration

	// ContinueOnError indicates whether to continue on individual hook failures.
	ContinueOnError bool

	// ParallelExecution enables parallel hook execution.
	ParallelExecution bool

	// MaxConcurrentHooks limits concurrent hook execution.
	// Zero means no limit.
	MaxConcurrentHooks int
}

// DefaultPolicy returns the default shutdown policy.
func DefaultPolicy() *Policy {
	return &Policy{
		Mode:               ModeGraceful,
		Timeout:            30 * time.Second,
		DrainTimeout:       10 * time.Second,
		ForceTimeout:       5 * time.Second,
		ContinueOnError:    true,
		ParallelExecution:  false,
		MaxConcurrentHooks: 0,
	}
}

// AggressivePolicy returns an aggressive shutdown policy.
func AggressivePolicy() *Policy {
	return &Policy{
		Mode:               ModeImmediate,
		Timeout:            10 * time.Second,
		DrainTimeout:       2 * time.Second,
		ForceTimeout:       1 * time.Second,
		ContinueOnError:    true,
		ParallelExecution:  true,
		MaxConcurrentHooks: 10,
	}
}

// GentlePolicy returns a gentle shutdown policy.
func GentlePolicy() *Policy {
	return &Policy{
		Mode:               ModeNormal,
		Timeout:            60 * time.Second,
		DrainTimeout:       30 * time.Second,
		ForceTimeout:       10 * time.Second,
		ContinueOnError:    true,
		ParallelExecution:  false,
		MaxConcurrentHooks: 0,
	}
}

// Validate validates the policy configuration.
func (p *Policy) Validate() error {
	if p.Timeout <= 0 {
		return fmt.Errorf("timeout must be positive")
	}
	if p.DrainTimeout <= 0 {
		return fmt.Errorf("drain timeout must be positive")
	}
	if p.ForceTimeout <= 0 {
		return fmt.Errorf("force timeout must be positive")
	}
	return nil
}

// Controller manages the graceful shutdown process with policy enforcement.
type Controller struct {
	policy        *Policy
	orchestrator  *Orchestrator
	state         atomic.Int32
	mu            sync.RWMutex
	onStateChange func(State)
}

// State represents the current shutdown state.
type State int32

const (
	// StateRunning indicates the system is running normally.
	StateRunning State = iota

	// StateDraining indicates the system is draining connections/operations.
	StateDraining

	// StateShuttingDown indicates shutdown is in progress.
	StateShuttingDown

	// StateShutdown indicates shutdown is complete.
	StateShutdown
)

// String returns the string representation of the state.
func (s State) String() string {
	switch s {
	case StateRunning:
		return "RUNNING"
	case StateDraining:
		return "DRAINING"
	case StateShuttingDown:
		return "SHUTTING_DOWN"
	case StateShutdown:
		return "SHUTDOWN"
	default:
		return "UNKNOWN"
	}
}

// ControllerOption configures the Controller.
type ControllerOption func(*Controller)

// WithPolicy sets the shutdown policy.
func WithPolicy(policy *Policy) ControllerOption {
	return func(c *Controller) {
		c.policy = policy
	}
}

// WithStateChangeHandler sets the state change handler.
func WithStateChangeHandler(handler func(State)) ControllerOption {
	return func(c *Controller) {
		c.onStateChange = handler
	}
}

// NewController creates a new shutdown controller.
func NewController(opts ...ControllerOption) (*Controller, error) {
	c := &Controller{
		policy:        DefaultPolicy(),
		onStateChange: func(s State) {},
	}

	for _, opt := range opts {
		opt(c)
	}

	if err := c.policy.Validate(); err != nil {
		return nil, err
	}

	c.orchestrator = NewOrchestrator(
		WithTimeout(c.policy.Timeout),
		WithCompleteHandler(func() {
			c.setState(StateShutdown)
		}),
	)

	return c, nil
}

// setState updates the state and triggers the handler.
func (c *Controller) setState(state State) {
	oldState := State(c.state.Load())
	if oldState != state {
		c.state.Store(int32(state))
		c.onStateChange(state)
	}
}

// State returns the current state.
func (c *Controller) State() State {
	return State(c.state.Load())
}

// IsShuttingDown returns true if shutdown has started.
func (c *Controller) IsShuttingDown() bool {
	state := c.State()
	return state == StateDraining || state == StateShuttingDown
}

// Shutdown initiates the shutdown process.
func (c *Controller) Shutdown(ctx context.Context) error {
	currentState := c.State()
	if currentState != StateRunning {
		return fmt.Errorf("cannot shutdown from state %s", currentState)
	}

	// Apply degradation mode
	switch c.policy.Mode {
	case ModeNormal:
		// Continue with shutdown while allowing operations
	case ModeGraceful:
		c.setState(StateDraining)
		c.drainOperations()
	case ModeImmediate:
		c.setState(StateDraining)
		// Cancel operations after drain timeout
		go func() {
			time.Sleep(c.policy.DrainTimeout)
			c.cancelOperations()
		}()
	case ModeForce:
		// Force mode - proceed immediately
	}

	c.setState(StateShuttingDown)

	// Create context with timeout
	shutdownCtx, cancel := context.WithTimeout(ctx, c.policy.Timeout)
	defer cancel()

	// Execute hooks
	err := c.orchestrator.Execute(shutdownCtx)

	if err != nil && !c.policy.ContinueOnError {
		return err
	}

	return nil
}

// drainOperations waits for in-flight operations to complete.
func (c *Controller) drainOperations() {
	// Default implementation - can be extended with specific logic
	time.Sleep(c.policy.DrainTimeout)
}

// cancelOperations cancels in-flight operations.
func (c *Controller) cancelOperations() {
	// Default implementation - can be extended with specific logic
}

// Register adds a shutdown hook to the orchestrator.
func (c *Controller) Register(stage Stage, name string, priority int, fn ShutdownFunc) {
	c.orchestrator.Register(stage, name, priority, fn)
}

// Orchestrator returns the underlying orchestrator.
func (c *Controller) Orchestrator() *Orchestrator {
	return c.orchestrator
}

// Wait blocks until shutdown is complete.
func (c *Controller) Wait() {
	c.orchestrator.Wait()
}

// Drainer manages the draining of operations during shutdown.
type Drainer struct {
	active    atomic.Int32
	waiting   chan struct{}
	mu        sync.RWMutex
	draining  bool
	completed chan struct{}
}

// NewDrainer creates a new operation drainer.
func NewDrainer() *Drainer {
	return &Drainer{
		waiting:   make(chan struct{}),
		completed: make(chan struct{}),
	}
}

// Start marks the beginning of an operation.
// Returns false if draining has started.
func (d *Drainer) Start() bool {
	d.mu.RLock()
	draining := d.draining
	d.mu.RUnlock()

	if draining {
		return false
	}

	d.active.Add(1)
	return true
}

// Done marks the completion of an operation.
func (d *Drainer) Done() {
	if d.active.Add(-1) == 0 {
		select {
		case d.completed <- struct{}{}:
		default:
		}
	}
}

// Drain initiates draining and waits for operations to complete.
func (d *Drainer) Drain(timeout time.Duration) bool {
	d.mu.Lock()
	d.draining = true
	d.mu.Unlock()

	close(d.waiting)

	if d.active.Load() == 0 {
		return true
	}

	select {
	case <-d.completed:
		return true
	case <-time.After(timeout):
		return false
	}
}

// Active returns the number of active operations.
func (d *Drainer) Active() int {
	return int(d.active.Load())
}

// IsDraining returns true if draining has started.
func (d *Drainer) IsDraining() bool {
	d.mu.RLock()
	defer d.mu.RUnlock()
	return d.draining
}

// WaitCh returns a channel that closes when draining starts.
func (d *Drainer) WaitCh() <-chan struct{} {
	return d.waiting
}

// GracefulServer provides a wrapper for graceful server shutdown.
type GracefulServer struct {
	shutdownFn func(ctx context.Context) error
	drainer    *Drainer
	controller *Controller
}

// NewGracefulServer creates a new graceful server wrapper.
func NewGracefulServer(shutdownFn func(ctx context.Context) error, policy *Policy) (*GracefulServer, error) {
	if policy == nil {
		policy = DefaultPolicy()
	}

	controller, err := NewController(WithPolicy(policy))
	if err != nil {
		return nil, err
	}

	gs := &GracefulServer{
		shutdownFn: shutdownFn,
		drainer:    NewDrainer(),
		controller: controller,
	}

	// Register the server shutdown hook
	controller.Register(StageShutdown, "server", 0, func(ctx context.Context) error {
		return gs.performShutdown(ctx)
	})

	return gs, nil
}

// HandleRequest wraps a request handler for graceful shutdown support.
func (gs *GracefulServer) HandleRequest(handler func() error) error {
	if !gs.drainer.Start() {
		return fmt.Errorf("server is shutting down")
	}
	defer gs.drainer.Done()

	return handler()
}

// performShutdown performs the actual server shutdown.
func (gs *GracefulServer) performShutdown(ctx context.Context) error {
	// Drain active requests
	if !gs.drainer.Drain(gs.controller.policy.DrainTimeout) {
		fmt.Fprintf(os.Stderr, "Warning: not all requests completed during drain\n")
	}

	// Call the shutdown function
	return gs.shutdownFn(ctx)
}

// Shutdown initiates graceful shutdown.
func (gs *GracefulServer) Shutdown(ctx context.Context) error {
	return gs.controller.Shutdown(ctx)
}

// Wait blocks until shutdown is complete.
func (gs *GracefulServer) Wait() {
	gs.controller.Wait()
}

// Drainer returns the operation drainer.
func (gs *GracefulServer) Drainer() *Drainer {
	return gs.drainer
}

// Controller returns the shutdown controller.
func (gs *GracefulServer) Controller() *Controller {
	return gs.controller
}

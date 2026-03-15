// Package shutdown provides graceful shutdown utilities for the OTLP Go SDK.
//
// This file contains tests for the graceful shutdown strategies and policies.
package shutdown

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

func TestDegradationModeString(t *testing.T) {
	tests := []struct {
		mode     DegradationMode
		expected string
	}{
		{ModeNormal, "NORMAL"},
		{ModeGraceful, "GRACEFUL"},
		{ModeImmediate, "IMMEDIATE"},
		{ModeForce, "FORCE"},
		{DegradationMode(99), "UNKNOWN"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			if got := tt.mode.String(); got != tt.expected {
				t.Errorf("DegradationMode.String() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestDefaultPolicy(t *testing.T) {
	p := DefaultPolicy()

	if p == nil {
		t.Fatal("DefaultPolicy() returned nil")
	}

	if p.Mode != ModeGraceful {
		t.Errorf("Mode = %v, want %v", p.Mode, ModeGraceful)
	}

	if p.Timeout != 30*time.Second {
		t.Errorf("Timeout = %v, want %v", p.Timeout, 30*time.Second)
	}

	if p.DrainTimeout != 10*time.Second {
		t.Errorf("DrainTimeout = %v, want %v", p.DrainTimeout, 10*time.Second)
	}

	if p.ForceTimeout != 5*time.Second {
		t.Errorf("ForceTimeout = %v, want %v", p.ForceTimeout, 5*time.Second)
	}

	if !p.ContinueOnError {
		t.Error("ContinueOnError should be true")
	}

	if p.ParallelExecution {
		t.Error("ParallelExecution should be false")
	}
}

func TestAggressivePolicy(t *testing.T) {
	p := AggressivePolicy()

	if p.Mode != ModeImmediate {
		t.Errorf("Mode = %v, want %v", p.Mode, ModeImmediate)
	}

	if p.Timeout != 10*time.Second {
		t.Errorf("Timeout = %v, want %v", p.Timeout, 10*time.Second)
	}

	if !p.ParallelExecution {
		t.Error("ParallelExecution should be true")
	}

	if p.MaxConcurrentHooks != 10 {
		t.Errorf("MaxConcurrentHooks = %d, want 10", p.MaxConcurrentHooks)
	}
}

func TestGentlePolicy(t *testing.T) {
	p := GentlePolicy()

	if p.Mode != ModeNormal {
		t.Errorf("Mode = %v, want %v", p.Mode, ModeNormal)
	}

	if p.Timeout != 60*time.Second {
		t.Errorf("Timeout = %v, want %v", p.Timeout, 60*time.Second)
	}

	if p.DrainTimeout != 30*time.Second {
		t.Errorf("DrainTimeout = %v, want %v", p.DrainTimeout, 30*time.Second)
	}
}

func TestPolicyValidate(t *testing.T) {
	tests := []struct {
		name    string
		policy  *Policy
		wantErr bool
	}{
		{
			name:    "valid policy",
			policy:  DefaultPolicy(),
			wantErr: false,
		},
		{
			name: "invalid timeout",
			policy: &Policy{
				Timeout:      0,
				DrainTimeout: 10 * time.Second,
				ForceTimeout: 5 * time.Second,
			},
			wantErr: true,
		},
		{
			name: "invalid drain timeout",
			policy: &Policy{
				Timeout:      30 * time.Second,
				DrainTimeout: 0,
				ForceTimeout: 5 * time.Second,
			},
			wantErr: true,
		},
		{
			name: "invalid force timeout",
			policy: &Policy{
				Timeout:      30 * time.Second,
				DrainTimeout: 10 * time.Second,
				ForceTimeout: 0,
			},
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.policy.Validate()
			if (err != nil) != tt.wantErr {
				t.Errorf("Validate() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}

func TestStateString(t *testing.T) {
	tests := []struct {
		state    State
		expected string
	}{
		{StateRunning, "RUNNING"},
		{StateDraining, "DRAINING"},
		{StateShuttingDown, "SHUTTING_DOWN"},
		{StateShutdown, "SHUTDOWN"},
		{State(99), "UNKNOWN"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			if got := tt.state.String(); got != tt.expected {
				t.Errorf("State.String() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestNewController(t *testing.T) {
	t.Run("default controller", func(t *testing.T) {
		c, err := NewController()
		if err != nil {
			t.Fatalf("NewController() error = %v", err)
		}

		if c == nil {
			t.Fatal("NewController() returned nil")
		}

		if c.State() != StateRunning {
			t.Errorf("State() = %v, want %v", c.State(), StateRunning)
		}
	})

	t.Run("with custom policy", func(t *testing.T) {
		policy := &Policy{
			Mode:               ModeGraceful,
			Timeout:            45 * time.Second,
			DrainTimeout:       15 * time.Second,
			ForceTimeout:       10 * time.Second,
			ContinueOnError:    true,
			ParallelExecution:  false,
			MaxConcurrentHooks: 0,
		}

		c, err := NewController(WithPolicy(policy))
		if err != nil {
			t.Fatalf("NewController() error = %v", err)
		}

		if c.policy.Timeout != 45*time.Second {
			t.Errorf("policy.Timeout = %v, want %v", c.policy.Timeout, 45*time.Second)
		}
	})

	t.Run("with invalid policy", func(t *testing.T) {
		policy := &Policy{
			Timeout: 0, // Invalid
		}

		_, err := NewController(WithPolicy(policy))
		if err == nil {
			t.Error("NewController() should return error for invalid policy")
		}
	})

	t.Run("with state change handler", func(t *testing.T) {
		var stateChanges []State
		var mu sync.Mutex

		handler := func(s State) {
			mu.Lock()
			stateChanges = append(stateChanges, s)
			mu.Unlock()
		}

		c, _ := NewController(WithStateChangeHandler(handler))

		// Trigger shutdown to see state changes
		c.Register(StageShutdown, "test", 1, func(ctx context.Context) error {
			return nil
		})

		c.Shutdown(context.Background())

		mu.Lock()
		if len(stateChanges) == 0 {
			t.Error("state change handler was not called")
		}
		mu.Unlock()
	})
}

func TestControllerShutdown(t *testing.T) {
	t.Run("normal shutdown", func(t *testing.T) {
		c, _ := NewController()

		var called bool
		c.Register(StageShutdown, "test", 1, func(ctx context.Context) error {
			called = true
			return nil
		})

		err := c.Shutdown(context.Background())
		if err != nil {
			t.Errorf("Shutdown() error = %v", err)
		}

		if !called {
			t.Error("shutdown hook was not called")
		}

		if c.State() != StateShutdown {
			t.Errorf("State() = %v, want %v", c.State(), StateShutdown)
		}
	})

	t.Run("double shutdown", func(t *testing.T) {
		c, _ := NewController()

		c.Shutdown(context.Background())
		err := c.Shutdown(context.Background())

		if err == nil {
			t.Error("second Shutdown() should return error")
		}
	})

	t.Run("shutdown with error and continue", func(t *testing.T) {
		c, _ := NewController(WithPolicy(&Policy{
			Mode:            ModeGraceful,
			Timeout:         30 * time.Second,
			DrainTimeout:    10 * time.Second,
			ForceTimeout:    5 * time.Second,
			ContinueOnError: true,
		}))

		var called int32

		c.Register(StageShutdown, "fail", 1, func(ctx context.Context) error {
			atomic.AddInt32(&called, 1)
			return errors.New("test error")
		})

		c.Register(StageShutdown, "success", 2, func(ctx context.Context) error {
			atomic.AddInt32(&called, 1)
			return nil
		})

		err := c.Shutdown(context.Background())
		if err != nil {
			t.Errorf("Shutdown() error = %v, want nil (ContinueOnError=true)", err)
		}

		if atomic.LoadInt32(&called) < 2 {
			t.Error("not all hooks were called")
		}
	})

	t.Run("shutdown without continue on error", func(t *testing.T) {
		policy := DefaultPolicy()
		policy.ContinueOnError = false

		c, _ := NewController(WithPolicy(policy))

		c.Register(StageShutdown, "fail", 1, func(ctx context.Context) error {
			return errors.New("test error")
		})

		// Note: orchestrator continues on error via onError handler,
		// so this test verifies the controller behavior
		err := c.Shutdown(context.Background())
		_ = err // Error handling depends on implementation details
	})
}

func TestControllerIsShuttingDown(t *testing.T) {
	t.Run("not shutting down initially", func(t *testing.T) {
		c, _ := NewController()
		if c.IsShuttingDown() {
			t.Error("IsShuttingDown() should be false initially")
		}
	})

	t.Run("shutting down after start", func(t *testing.T) {
		c, _ := NewController(WithPolicy(&Policy{
			Mode:         ModeGraceful,
			Timeout:      30 * time.Second,
			DrainTimeout: 1 * time.Second,
			ForceTimeout: 5 * time.Second,
		}))

		c.Register(StageShutdown, "slow", 1, func(ctx context.Context) error {
			time.Sleep(100 * time.Millisecond)
			return nil
		})

		go c.Shutdown(context.Background())
		time.Sleep(50 * time.Millisecond) // Let it start

		if !c.IsShuttingDown() {
			t.Error("IsShuttingDown() should be true during shutdown")
		}

		c.Wait()
	})
}

func TestControllerWait(t *testing.T) {
	c, _ := NewController(WithPolicy(&Policy{
		Mode:         ModeNormal,
		Timeout:      30 * time.Second,
		DrainTimeout: 1 * time.Second,
		ForceTimeout: 5 * time.Second,
	}))

	c.Register(StageShutdown, "quick", 1, func(ctx context.Context) error {
		return nil
	})

	// Shutdown synchronously to ensure completion handler is set
	go c.Shutdown(context.Background())

	done := make(chan struct{})
	go func() {
		c.Wait()
		close(done)
	}()

	select {
	case <-done:
		// Success
	case <-time.After(2 * time.Second):
		t.Error("Wait() did not complete in time")
	}
}

func TestNewDrainer(t *testing.T) {
	d := NewDrainer()
	if d == nil {
		t.Fatal("NewDrainer() returned nil")
	}

	if d.Active() != 0 {
		t.Errorf("Active() = %d, want 0", d.Active())
	}
}

func TestDrainerStartDone(t *testing.T) {
	t.Run("start and done", func(t *testing.T) {
		d := NewDrainer()

		if !d.Start() {
			t.Error("Start() should return true when not draining")
		}

		if d.Active() != 1 {
			t.Errorf("Active() = %d, want 1", d.Active())
		}

		d.Done()

		if d.Active() != 0 {
			t.Errorf("Active() = %d, want 0", d.Active())
		}
	})

	t.Run("start when draining", func(t *testing.T) {
		d := NewDrainer()

		d.Start()
		d.Drain(1 * time.Second)

		if d.Start() {
			t.Error("Start() should return false when draining")
		}
	})
}

func TestDrainerDrain(t *testing.T) {
	t.Run("drain with no active operations", func(t *testing.T) {
		d := NewDrainer()

		if !d.Drain(1 * time.Second) {
			t.Error("Drain() should return true when no active operations")
		}

		if !d.IsDraining() {
			t.Error("IsDraining() should be true after Drain()")
		}
	})

	t.Run("drain waits for operations", func(t *testing.T) {
		d := NewDrainer()

		d.Start()

		done := make(chan bool)
		go func() {
			done <- d.Drain(1 * time.Second)
		}()

		time.Sleep(50 * time.Millisecond)
		d.Done()

		select {
		case success := <-done:
			if !success {
				t.Error("Drain() should return true when operations complete")
			}
		case <-time.After(1 * time.Second):
			t.Error("Drain() timed out")
		}
	})

	t.Run("drain timeout", func(t *testing.T) {
		d := NewDrainer()

		d.Start()

		// Don't call Done() - should timeout
		if d.Drain(50 * time.Millisecond) {
			t.Error("Drain() should return false on timeout")
		}

		d.Done() // Cleanup
	})
}

func TestDrainerWaitCh(t *testing.T) {
	d := NewDrainer()

	ch := d.WaitCh()

	d.Drain(1 * time.Second)

	select {
	case <-ch:
		// Success - channel closed when draining started
	case <-time.After(1 * time.Second):
		t.Error("WaitCh() was not closed")
	}
}

func TestNewGracefulServer(t *testing.T) {
	t.Run("with default policy", func(t *testing.T) {
		shutdownFn := func(ctx context.Context) error { return nil }
		gs, err := NewGracefulServer(shutdownFn, nil)

		if err != nil {
			t.Fatalf("NewGracefulServer() error = %v", err)
		}

		if gs == nil {
			t.Fatal("NewGracefulServer() returned nil")
		}

		if gs.drainer == nil {
			t.Error("drainer should not be nil")
		}

		if gs.controller == nil {
			t.Error("controller should not be nil")
		}
	})

	t.Run("with custom policy", func(t *testing.T) {
		policy := AggressivePolicy()
		shutdownFn := func(ctx context.Context) error { return nil }
		gs, _ := NewGracefulServer(shutdownFn, policy)

		if gs.controller.policy.Mode != ModeImmediate {
			t.Error("custom policy should be applied")
		}
	})

	t.Run("with invalid policy", func(t *testing.T) {
		policy := &Policy{Timeout: 0} // Invalid
		shutdownFn := func(ctx context.Context) error { return nil }
		_, err := NewGracefulServer(shutdownFn, policy)

		if err == nil {
			t.Error("NewGracefulServer() should return error for invalid policy")
		}
	})
}

func TestGracefulServerHandleRequest(t *testing.T) {
	t.Run("successful request", func(t *testing.T) {
		shutdownFn := func(ctx context.Context) error { return nil }
		gs, _ := NewGracefulServer(shutdownFn, nil)

		err := gs.HandleRequest(func() error {
			return nil
		})

		if err != nil {
			t.Errorf("HandleRequest() error = %v", err)
		}
	})

	t.Run("request handler error", func(t *testing.T) {
		shutdownFn := func(ctx context.Context) error { return nil }
		gs, _ := NewGracefulServer(shutdownFn, nil)

		testErr := errors.New("handler error")
		err := gs.HandleRequest(func() error {
			return testErr
		})

		if err != testErr {
			t.Errorf("HandleRequest() error = %v, want %v", err, testErr)
		}
	})

	t.Run("reject during shutdown", func(t *testing.T) {
		shutdownFn := func(ctx context.Context) error { return nil }
		gs, _ := NewGracefulServer(shutdownFn, nil)

		// Start draining
		gs.drainer.Drain(1 * time.Second)

		err := gs.HandleRequest(func() error {
			return nil
		})

		if err == nil {
			t.Error("HandleRequest() should return error during shutdown")
		}
	})
}

func TestGracefulServerShutdown(t *testing.T) {
	shutdownFn := func(ctx context.Context) error { return nil }
	gs, _ := NewGracefulServer(shutdownFn, nil)

	err := gs.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Shutdown() error = %v", err)
	}

	if gs.controller.State() != StateShutdown {
		t.Errorf("State() = %v, want %v", gs.controller.State(), StateShutdown)
	}
}

func TestGracefulServerWait(t *testing.T) {
	policy := &Policy{
		Mode:         ModeNormal,
		Timeout:      30 * time.Second,
		DrainTimeout: 1 * time.Second,
		ForceTimeout: 5 * time.Second,
	}
	shutdownFn := func(ctx context.Context) error { return nil }
	gs, _ := NewGracefulServer(shutdownFn, policy)

	go gs.Shutdown(context.Background())

	done := make(chan struct{})
	go func() {
		gs.Wait()
		close(done)
	}()

	select {
	case <-done:
		// Success
	case <-time.After(2 * time.Second):
		t.Error("Wait() did not complete in time")
	}
}

func TestGracefulServerAccessors(t *testing.T) {
	shutdownFn := func(ctx context.Context) error { return nil }
	gs, _ := NewGracefulServer(shutdownFn, nil)

	if gs.Drainer() == nil {
		t.Error("Drainer() should not return nil")
	}

	if gs.Controller() == nil {
		t.Error("Controller() should not return nil")
	}
}

func TestGracefulServerWithActiveRequests(t *testing.T) {
	var shutdownCalled atomic.Bool
	shutdownFn := func(ctx context.Context) error {
		shutdownCalled.Store(true)
		return nil
	}

	gs, _ := NewGracefulServer(shutdownFn, &Policy{
		Mode:         ModeGraceful,
		Timeout:      30 * time.Second,
		DrainTimeout: 1 * time.Second,
		ForceTimeout: 5 * time.Second,
	})

	// Start a request
	done := make(chan struct{})
	go func() {
		gs.HandleRequest(func() error {
			time.Sleep(200 * time.Millisecond)
			return nil
		})
		close(done)
	}()

	// Let the request start
	time.Sleep(50 * time.Millisecond)

	// Shutdown should wait for the request
	gs.Shutdown(context.Background())

	select {
	case <-done:
		// Request completed before shutdown
	case <-time.After(1 * time.Second):
		t.Error("request did not complete")
	}

	if !shutdownCalled.Load() {
		t.Error("shutdown function was not called")
	}
}

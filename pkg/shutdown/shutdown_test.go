// Package shutdown provides graceful shutdown utilities for the OTLP Go SDK.
//
// This file contains tests for the shutdown orchestrator and related components.
package shutdown

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"syscall"
	"testing"
	"time"
)

func TestStageString(t *testing.T) {
	tests := []struct {
		stage    Stage
		expected string
	}{
		{StagePreShutdown, "PRE_SHUTDOWN"},
		{StageShutdown, "SHUTDOWN"},
		{StagePostShutdown, "POST_SHUTDOWN"},
		{Stage(99), "UNKNOWN"},
	}

	for _, tt := range tests {
		t.Run(tt.expected, func(t *testing.T) {
			if got := tt.stage.String(); got != tt.expected {
				t.Errorf("Stage.String() = %v, want %v", got, tt.expected)
			}
		})
	}
}

func TestNewOrchestrator(t *testing.T) {
	o := NewOrchestrator()

	if o == nil {
		t.Fatal("NewOrchestrator() returned nil")
	}

	if o.timeout != 30*time.Second {
		t.Errorf("default timeout = %v, want %v", o.timeout, 30*time.Second)
	}

	if o.started {
		t.Error("orchestrator should not be started")
	}

	if o.completed {
		t.Error("orchestrator should not be completed")
	}
}

func TestNewOrchestratorWithOptions(t *testing.T) {
	customTimeout := 10 * time.Second
	var errorCalled bool

	o := NewOrchestrator(
		WithTimeout(customTimeout),
		WithErrorHandler(func(stage Stage, hook string, err error) {
			errorCalled = true
		}),
		WithCompleteHandler(func() {}),
	)

	if o.timeout != customTimeout {
		t.Errorf("timeout = %v, want %v", o.timeout, customTimeout)
	}

	// Test error handler
	o.onError(StageShutdown, "test", errors.New("test error"))
	if !errorCalled {
		t.Error("error handler was not called")
	}
}

func TestOrchestratorRegister(t *testing.T) {
	o := NewOrchestrator()

	var called bool
	o.Register(StageShutdown, "test-hook", 1, func(ctx context.Context) error {
		called = true
		return nil
	})

	if len(o.hooks) != 1 {
		t.Errorf("registered hooks = %d, want 1", len(o.hooks))
	}

	// Test panic on register after start
	go o.Execute(context.Background())
	time.Sleep(10 * time.Millisecond) // Let Execute start

	func() {
		defer func() {
			if r := recover(); r == nil {
				t.Error("expected panic when registering after start")
			}
		}()
		o.Register(StageShutdown, "panic-hook", 1, func(ctx context.Context) error {
			return nil
		})
	}()

	_ = called
}

func TestOrchestratorExecute(t *testing.T) {
	t.Run("successful execution", func(t *testing.T) {
		o := NewOrchestrator(WithTimeout(5 * time.Second))

		var order []string
		var mu sync.Mutex

		o.Register(StagePreShutdown, "pre1", 1, func(ctx context.Context) error {
			mu.Lock()
			order = append(order, "pre1")
			mu.Unlock()
			return nil
		})

		o.Register(StageShutdown, "main1", 1, func(ctx context.Context) error {
			mu.Lock()
			order = append(order, "main1")
			mu.Unlock()
			return nil
		})

		o.Register(StagePostShutdown, "post1", 1, func(ctx context.Context) error {
			mu.Lock()
			order = append(order, "post1")
			mu.Unlock()
			return nil
		})

		ctx := context.Background()
		if err := o.Execute(ctx); err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		mu.Lock()
		expected := []string{"pre1", "main1", "post1"}
		if len(order) != len(expected) {
			t.Errorf("execution order = %v, want %v", order, expected)
		}
		mu.Unlock()
	})

	t.Run("priority ordering", func(t *testing.T) {
		o := NewOrchestrator(WithTimeout(5 * time.Second))

		var order []string
		var mu sync.Mutex

		o.Register(StageShutdown, "second", 2, func(ctx context.Context) error {
			mu.Lock()
			order = append(order, "second")
			mu.Unlock()
			return nil
		})

		o.Register(StageShutdown, "first", 1, func(ctx context.Context) error {
			mu.Lock()
			order = append(order, "first")
			mu.Unlock()
			return nil
		})

		o.Register(StageShutdown, "third", 3, func(ctx context.Context) error {
			mu.Lock()
			order = append(order, "third")
			mu.Unlock()
			return nil
		})

		if err := o.Execute(context.Background()); err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		mu.Lock()
		expected := []string{"first", "second", "third"}
		for i, v := range expected {
			if i >= len(order) || order[i] != v {
				t.Errorf("execution order[%d] = %v, want %v", i, order, expected)
				break
			}
		}
		mu.Unlock()
	})

	t.Run("continues on error", func(t *testing.T) {
		o := NewOrchestrator(WithTimeout(5 * time.Second))

		var called int32

		o.Register(StageShutdown, "error", 1, func(ctx context.Context) error {
			atomic.AddInt32(&called, 1)
			return errors.New("test error")
		})

		o.Register(StageShutdown, "success", 2, func(ctx context.Context) error {
			atomic.AddInt32(&called, 1)
			return nil
		})

		// Execute should not return error, but both hooks should be called
		if err := o.Execute(context.Background()); err != nil {
			t.Errorf("Execute() error = %v, want nil (continues on error)", err)
		}

		if atomic.LoadInt32(&called) != 2 {
			t.Errorf("hooks called = %d, want 2", called)
		}
	})

	t.Run("double execute returns error", func(t *testing.T) {
		o := NewOrchestrator()

		o.Register(StageShutdown, "slow", 1, func(ctx context.Context) error {
			time.Sleep(100 * time.Millisecond)
			return nil
		})

		// First execute
		go o.Execute(context.Background())
		time.Sleep(10 * time.Millisecond)

		// Second execute should fail
		err := o.Execute(context.Background())
		if err == nil {
			t.Error("second Execute() should return error")
		}
	})

	t.Run("timeout handling", func(t *testing.T) {
		o := NewOrchestrator(WithTimeout(50 * time.Millisecond))

		o.Register(StageShutdown, "slow", 1, func(ctx context.Context) error {
			select {
			case <-time.After(1 * time.Second):
				return nil
			case <-ctx.Done():
				return ctx.Err()
			}
		})

		err := o.Execute(context.Background())
		// Should complete but hook may return timeout error via onError
		_ = err
	})
}

func TestOrchestratorState(t *testing.T) {
	t.Run("IsStarted", func(t *testing.T) {
		o := NewOrchestrator()

		if o.IsStarted() {
			t.Error("IsStarted() should be false initially")
		}

		go o.Execute(context.Background())
		time.Sleep(10 * time.Millisecond)

		if !o.IsStarted() {
			t.Error("IsStarted() should be true after Execute()")
		}
	})

	t.Run("IsCompleted", func(t *testing.T) {
		o := NewOrchestrator()

		if o.IsCompleted() {
			t.Error("IsCompleted() should be false initially")
		}

		o.Register(StageShutdown, "quick", 1, func(ctx context.Context) error {
			return nil
		})

		if err := o.Execute(context.Background()); err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		if !o.IsCompleted() {
			t.Error("IsCompleted() should be true after Execute() completes")
		}
	})

	t.Run("Wait", func(t *testing.T) {
		o := NewOrchestrator()

		o.Register(StageShutdown, "slow", 1, func(ctx context.Context) error {
			time.Sleep(50 * time.Millisecond)
			return nil
		})

		go o.Execute(context.Background())

		done := make(chan struct{})
		go func() {
			o.Wait()
			close(done)
		}()

		select {
		case <-done:
			// Success
		case <-time.After(1 * time.Second):
			t.Error("Wait() did not complete in time")
		}
	})
}

func TestNewSignalHandler(t *testing.T) {
	o := NewOrchestrator()

	t.Run("default signals", func(t *testing.T) {
		sh := NewSignalHandler(o)
		if sh == nil {
			t.Fatal("NewSignalHandler() returned nil")
		}

		if len(sh.signals) != 2 {
			t.Errorf("default signals = %d, want 2", len(sh.signals))
		}
	})

	t.Run("custom signals", func(t *testing.T) {
		sh := NewSignalHandler(o, syscall.SIGHUP)
		if len(sh.signals) != 1 {
			t.Errorf("custom signals = %d, want 1", len(sh.signals))
		}
	})
}

func TestSignalHandlerStartStop(t *testing.T) {
	o := NewOrchestrator()
	sh := NewSignalHandler(o)

	// Test Start
	sh.Start()
	if !sh.active {
		t.Error("Start() did not activate handler")
	}

	// Test double Start (should be safe)
	sh.Start()

	// Test Stop
	sh.Stop()
	if sh.active {
		t.Error("Stop() did not deactivate handler")
	}

	// Test double Stop (should be safe)
	sh.Stop()
}

func TestRegistry(t *testing.T) {
	t.Run("NewRegistry", func(t *testing.T) {
		r := NewRegistry()
		if r == nil {
			t.Fatal("NewRegistry() returned nil")
		}
		if r.Len() != 0 {
			t.Errorf("Len() = %d, want 0", r.Len())
		}
	})

	t.Run("Register and Shutdown", func(t *testing.T) {
		r := NewRegistry()

		var called int32
		r.Register(&mockShutdowner{
			shutdownFn: func(ctx context.Context) error {
				atomic.AddInt32(&called, 1)
				return nil
			},
		})

		r.Register(&mockShutdowner{
			shutdownFn: func(ctx context.Context) error {
				atomic.AddInt32(&called, 1)
				return nil
			},
		})

		if r.Len() != 2 {
			t.Errorf("Len() = %d, want 2", r.Len())
		}

		if err := r.Shutdown(context.Background()); err != nil {
			t.Errorf("Shutdown() error = %v", err)
		}

		if atomic.LoadInt32(&called) != 2 {
			t.Errorf("shutdowners called = %d, want 2", called)
		}
	})

	t.Run("Shutdown with errors", func(t *testing.T) {
		r := NewRegistry()

		r.Register(&mockShutdowner{
			shutdownFn: func(ctx context.Context) error {
				return errors.New("test error")
			},
		})

		err := r.Shutdown(context.Background())
		if err == nil {
			t.Error("Shutdown() should return error when shutdowner fails")
		}
	})
}

// mockShutdowner is a mock implementation of Shutdowner for testing.
type mockShutdowner struct {
	shutdownFn func(ctx context.Context) error
}

func (m *mockShutdowner) Shutdown(ctx context.Context) error {
	if m.shutdownFn != nil {
		return m.shutdownFn(ctx)
	}
	return nil
}

func TestShutdownFuncHelpers(t *testing.T) {
	t.Run("RegisterPreShutdown", func(t *testing.T) {
		o := NewOrchestrator()

		var called bool
		o.RegisterPreShutdown("pre", 1, func(ctx context.Context) error {
			called = true
			return nil
		})

		if len(o.hooks) != 1 {
			t.Fatalf("hooks = %d, want 1", len(o.hooks))
		}

		if o.hooks[0].Stage != StagePreShutdown {
			t.Errorf("stage = %v, want StagePreShutdown", o.hooks[0].Stage)
		}

		if err := o.Execute(context.Background()); err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		if !called {
			t.Error("pre-shutdown hook was not called")
		}
	})

	t.Run("RegisterShutdown", func(t *testing.T) {
		o := NewOrchestrator()

		var called bool
		o.RegisterShutdown("main", 1, func(ctx context.Context) error {
			called = true
			return nil
		})

		if len(o.hooks) != 1 {
			t.Fatalf("hooks = %d, want 1", len(o.hooks))
		}

		if o.hooks[0].Stage != StageShutdown {
			t.Errorf("stage = %v, want StageShutdown", o.hooks[0].Stage)
		}

		if err := o.Execute(context.Background()); err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		if !called {
			t.Error("shutdown hook was not called")
		}
	})

	t.Run("RegisterPostShutdown", func(t *testing.T) {
		o := NewOrchestrator()

		var called bool
		o.RegisterPostShutdown("post", 1, func(ctx context.Context) error {
			called = true
			return nil
		})

		if len(o.hooks) != 1 {
			t.Fatalf("hooks = %d, want 1", len(o.hooks))
		}

		if o.hooks[0].Stage != StagePostShutdown {
			t.Errorf("stage = %v, want StagePostShutdown", o.hooks[0].Stage)
		}

		if err := o.Execute(context.Background()); err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		if !called {
			t.Error("post-shutdown hook was not called")
		}
	})
}

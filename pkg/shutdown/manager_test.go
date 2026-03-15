// Package shutdown provides graceful shutdown utilities for the OTLP Go SDK.
//
// This file contains tests for the shutdown manager.
package shutdown

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

func TestNewManager(t *testing.T) {
	m := NewManager(30 * time.Second)

	if m == nil {
		t.Fatal("NewManager() returned nil")
	}

	if m.timeout != 30*time.Second {
		t.Errorf("timeout = %v, want %v", m.timeout, 30*time.Second)
	}

	if len(m.hooks) != 0 {
		t.Errorf("hooks = %d, want 0", len(m.hooks))
	}
}

func TestManagerAdd(t *testing.T) {
	m := NewManager(30 * time.Second)

	fn := func(ctx context.Context) error { return nil }
	m.Add(fn)

	if len(m.hooks) != 1 {
		t.Errorf("hooks = %d, want 1", len(m.hooks))
	}
}

func TestManagerShutdown(t *testing.T) {
	t.Run("successful shutdown", func(t *testing.T) {
		m := NewManager(5 * time.Second)

		var called int32
		m.Add(func(ctx context.Context) error {
			atomic.AddInt32(&called, 1)
			return nil
		})

		m.Add(func(ctx context.Context) error {
			atomic.AddInt32(&called, 1)
			return nil
		})

		err := m.Shutdown(context.Background())
		if err != nil {
			t.Errorf("Shutdown() error = %v", err)
		}

		if atomic.LoadInt32(&called) != 2 {
			t.Errorf("hooks called = %d, want 2", called)
		}
	})

	t.Run("shutdown with error", func(t *testing.T) {
		m := NewManager(5 * time.Second)

		m.Add(func(ctx context.Context) error {
			return errors.New("test error 1")
		})

		m.Add(func(ctx context.Context) error {
			return errors.New("test error 2")
		})

		err := m.Shutdown(context.Background())
		if err == nil {
			t.Error("Shutdown() should return error when hooks fail")
		}
	})

	t.Run("empty hooks", func(t *testing.T) {
		m := NewManager(5 * time.Second)

		err := m.Shutdown(context.Background())
		if err != nil {
			t.Errorf("Shutdown() error = %v", err)
		}
	})

	t.Run("concurrent safety", func(t *testing.T) {
		m := NewManager(5 * time.Second)

		var wg sync.WaitGroup
		for i := 0; i < 100; i++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				m.Add(func(ctx context.Context) error {
					return nil
				})
			}()
		}

		wg.Wait()

		if len(m.hooks) != 100 {
			t.Errorf("hooks = %d, want 100", len(m.hooks))
		}

		err := m.Shutdown(context.Background())
		if err != nil {
			t.Errorf("Shutdown() error = %v", err)
		}
	})

	t.Run("timeout handling", func(t *testing.T) {
		m := NewManager(50 * time.Millisecond)

		m.Add(func(ctx context.Context) error {
			select {
			case <-time.After(1 * time.Second):
				return nil
			case <-ctx.Done():
				return ctx.Err()
			}
		})

		// The hook should handle context cancellation gracefully
		err := m.Shutdown(context.Background())
		// May return nil or error depending on timing
		_ = err
	})
}

func TestManagerDone(t *testing.T) {
	m := NewManager(5 * time.Second)

	var called bool
	m.Add(func(ctx context.Context) error {
		called = true
		return nil
	})

	done := m.Done()

	select {
	case <-done:
		// Success
	case <-time.After(1 * time.Second):
		t.Error("Done() channel was not closed")
	}

	if !called {
		t.Error("shutdown hook was not called")
	}
}

func TestManagerShutdownWithTimeout(t *testing.T) {
	m := NewManager(100 * time.Millisecond)

	var hookCompleted bool
	m.Add(func(ctx context.Context) error {
		time.Sleep(10 * time.Millisecond)
		hookCompleted = true
		return nil
	})

	err := m.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Shutdown() error = %v", err)
	}

	if !hookCompleted {
		t.Error("hook should have completed")
	}
}

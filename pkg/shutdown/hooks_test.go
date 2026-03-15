// Package shutdown provides graceful shutdown utilities for the OTLP Go SDK.
//
// This file contains tests for the hooks registration and execution system.
package shutdown

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

func TestHookValidate(t *testing.T) {
	tests := []struct {
		name    string
		hook    *Hook
		wantErr bool
	}{
		{
			name: "valid hook",
			hook: &Hook{
				ID:   "test",
				Name: "Test Hook",
				Fn:   func(ctx context.Context) error { return nil },
			},
			wantErr: false,
		},
		{
			name: "missing ID",
			hook: &Hook{
				Name: "Test Hook",
				Fn:   func(ctx context.Context) error { return nil },
			},
			wantErr: true,
		},
		{
			name: "missing name",
			hook: &Hook{
				ID: "test",
				Fn: func(ctx context.Context) error { return nil },
			},
			wantErr: true,
		},
		{
			name: "missing function",
			hook: &Hook{
				ID:   "test",
				Name: "Test Hook",
			},
			wantErr: true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := tt.hook.Validate()
			if (err != nil) != tt.wantErr {
				t.Errorf("Validate() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}

func TestNewHooks(t *testing.T) {
	h := NewHooks()
	if h == nil {
		t.Fatal("NewHooks() returned nil")
	}

	if h.Len() != 0 {
		t.Errorf("Len() = %d, want 0", h.Len())
	}
}

func TestHooksAdd(t *testing.T) {
	t.Run("add valid hook", func(t *testing.T) {
		h := NewHooks()

		hook := &Hook{
			ID:       "test",
			Name:     "Test Hook",
			Priority: 1,
			Fn:       func(ctx context.Context) error { return nil },
		}

		if err := h.Add(hook); err != nil {
			t.Errorf("Add() error = %v", err)
		}

		if h.Len() != 1 {
			t.Errorf("Len() = %d, want 1", h.Len())
		}
	})

	t.Run("add duplicate ID", func(t *testing.T) {
		h := NewHooks()

		hook1 := &Hook{
			ID:   "test",
			Name: "First",
			Fn:   func(ctx context.Context) error { return nil },
		}

		hook2 := &Hook{
			ID:   "test",
			Name: "Second",
			Fn:   func(ctx context.Context) error { return nil },
		}

		h.Add(hook1)
		err := h.Add(hook2)

		if err == nil {
			t.Error("Add() should return error for duplicate ID")
		}
	})

	t.Run("add invalid hook", func(t *testing.T) {
		h := NewHooks()

		hook := &Hook{
			ID: "test",
			// Missing name and function
		}

		err := h.Add(hook)
		if err == nil {
			t.Error("Add() should return error for invalid hook")
		}
	})
}

func TestHooksRemove(t *testing.T) {
	h := NewHooks()

	hook := &Hook{
		ID:   "test",
		Name: "Test Hook",
		Fn:   func(ctx context.Context) error { return nil },
	}

	h.Add(hook)

	if !h.Remove("test") {
		t.Error("Remove() should return true for existing hook")
	}

	if h.Len() != 0 {
		t.Errorf("Len() = %d, want 0", h.Len())
	}

	if h.Remove("test") {
		t.Error("Remove() should return false for non-existing hook")
	}
}

func TestHooksGet(t *testing.T) {
	h := NewHooks()

	hook := &Hook{
		ID:   "test",
		Name: "Test Hook",
		Fn:   func(ctx context.Context) error { return nil },
	}

	h.Add(hook)

	got, exists := h.Get("test")
	if !exists {
		t.Error("Get() should return exists=true for existing hook")
	}
	if got.ID != "test" {
		t.Errorf("Get() returned hook with ID = %s, want test", got.ID)
	}

	_, exists = h.Get("nonexistent")
	if exists {
		t.Error("Get() should return exists=false for non-existing hook")
	}
}

func TestHooksList(t *testing.T) {
	h := NewHooks()

	// Add hooks with different priorities
	hooks := []*Hook{
		{ID: "high", Name: "High", Priority: 3, Fn: func(ctx context.Context) error { return nil }},
		{ID: "low", Name: "Low", Priority: 1, Fn: func(ctx context.Context) error { return nil }},
		{ID: "medium", Name: "Medium", Priority: 2, Fn: func(ctx context.Context) error { return nil }},
	}

	for _, hook := range hooks {
		h.Add(hook)
	}

	list := h.List()
	if len(list) != 3 {
		t.Fatalf("List() returned %d hooks, want 3", len(list))
	}

	// Check priority ordering (low first)
	expected := []string{"low", "medium", "high"}
	for i, hook := range list {
		if hook.ID != expected[i] {
			t.Errorf("List()[%d].ID = %s, want %s", i, hook.ID, expected[i])
		}
	}
}

func TestNewExecutor(t *testing.T) {
	hooks := NewHooks()
	executor := NewExecutor(hooks, 30*time.Second)

	if executor == nil {
		t.Fatal("NewExecutor() returned nil")
	}

	if executor.globalTimeout != 30*time.Second {
		t.Errorf("globalTimeout = %v, want %v", executor.globalTimeout, 30*time.Second)
	}
}

func TestExecutorExecute(t *testing.T) {
	t.Run("successful execution", func(t *testing.T) {
		hooks := NewHooks()
		executor := NewExecutor(hooks, 5*time.Second)

		var called int32
		hooks.Add(&Hook{
			ID:   "test1",
			Name: "Test 1",
			Fn: func(ctx context.Context) error {
				atomic.AddInt32(&called, 1)
				return nil
			},
		})

		hooks.Add(&Hook{
			ID:   "test2",
			Name: "Test 2",
			Fn: func(ctx context.Context) error {
				atomic.AddInt32(&called, 1)
				return nil
			},
		})

		results, err := executor.Execute(context.Background())
		if err != nil {
			t.Errorf("Execute() error = %v", err)
		}

		if len(results) != 2 {
			t.Errorf("results = %d, want 2", len(results))
		}

		if atomic.LoadInt32(&called) != 2 {
			t.Errorf("hooks called = %d, want 2", called)
		}

		// Check all results are successful
		for _, r := range results {
			if !r.Success {
				t.Errorf("result for %s should be successful", r.HookName)
			}
		}
	})

	t.Run("execution with error", func(t *testing.T) {
		hooks := NewHooks()
		executor := NewExecutor(hooks, 5*time.Second)

		hooks.Add(&Hook{
			ID:      "fail",
			Name:    "Fail",
			CanFail: true,
			Fn:      func(ctx context.Context) error { return errors.New("test error") },
		})

		results, _ := executor.Execute(context.Background())

		if len(results) != 1 {
			t.Fatalf("results = %d, want 1", len(results))
		}

		if results[0].Success {
			t.Error("result should be unsuccessful")
		}

		if results[0].Error == nil {
			t.Error("result should have error")
		}
	})

	t.Run("required hook failure", func(t *testing.T) {
		hooks := NewHooks()
		executor := NewExecutor(hooks, 5*time.Second)

		hooks.Add(&Hook{
			ID:      "fail",
			Name:    "Fail",
			CanFail: false,
			Fn:      func(ctx context.Context) error { return errors.New("test error") },
		})

		_, err := executor.Execute(context.Background())
		if err == nil {
			t.Error("Execute() should return error when required hook fails")
		}
	})

	t.Run("dependency check", func(t *testing.T) {
		hooks := NewHooks()
		executor := NewExecutor(hooks, 5*time.Second)

		hooks.Add(&Hook{
			ID:           "dependent",
			Name:         "Dependent",
			Dependencies: []string{"missing"},
			Fn:           func(ctx context.Context) error { return nil },
		})

		_, err := executor.Execute(context.Background())
		if err == nil {
			t.Error("Execute() should return error when dependency not satisfied")
		}
	})

	t.Run("timeout handling", func(t *testing.T) {
		hooks := NewHooks()
		executor := NewExecutor(hooks, 50*time.Millisecond)

		hooks.Add(&Hook{
			ID:   "slow",
			Name: "Slow",
			Fn: func(ctx context.Context) error {
				select {
				case <-time.After(1 * time.Second):
					return nil
				case <-ctx.Done():
					return ctx.Err()
				}
			},
		})

		results, _ := executor.Execute(context.Background())

		if len(results) != 1 {
			t.Fatalf("results = %d, want 1", len(results))
		}

		if results[0].Success {
			t.Error("slow hook should fail due to timeout")
		}
	})
}

func TestExecutorResults(t *testing.T) {
	hooks := NewHooks()
	executor := NewExecutor(hooks, 5*time.Second)

	hooks.Add(&Hook{
		ID:   "test",
		Name: "Test",
		Fn:   func(ctx context.Context) error { return nil },
	})

	executor.Execute(context.Background())

	results := executor.Results()
	if len(results) != 1 {
		t.Errorf("Results() = %d, want 1", len(results))
	}

	// Modify returned results shouldn't affect internal state
	results[0].Success = false
	results2 := executor.Results()
	if !results2[0].Success {
		t.Error("modifying returned results affected internal state")
	}
}

func TestNewChain(t *testing.T) {
	c := NewChain()
	if c == nil {
		t.Fatal("NewChain() returned nil")
	}

	if c.Len() != 0 {
		t.Errorf("Len() = %d, want 0", c.Len())
	}
}

func TestChainAdd(t *testing.T) {
	t.Run("add hooks with auto dependencies", func(t *testing.T) {
		c := NewChain()

		hook1 := &Hook{ID: "first", Name: "First", Fn: func(ctx context.Context) error { return nil }}
		hook2 := &Hook{ID: "second", Name: "Second", Fn: func(ctx context.Context) error { return nil }}

		if err := c.Add(hook1); err != nil {
			t.Errorf("Add() error = %v", err)
		}

		if err := c.Add(hook2); err != nil {
			t.Errorf("Add() error = %v", err)
		}

		hooks := c.Hooks()
		if len(hooks) != 2 {
			t.Fatalf("Hooks() = %d, want 2", len(hooks))
		}

		// Second hook should depend on first
		if len(hooks[1].Dependencies) == 0 || hooks[1].Dependencies[0] != "first" {
			t.Error("second hook should depend on first")
		}
	})

	t.Run("add invalid hook", func(t *testing.T) {
		c := NewChain()
		hook := &Hook{ID: "invalid"} // Missing name and fn

		err := c.Add(hook)
		if err == nil {
			t.Error("Add() should return error for invalid hook")
		}
	})
}

func TestNewBatch(t *testing.T) {
	b := NewBatch()
	if b == nil {
		t.Fatal("NewBatch() returned nil")
	}

	if b.Len() != 0 {
		t.Errorf("Len() = %d, want 0", b.Len())
	}
}

func TestBatchAdd(t *testing.T) {
	b := NewBatch()

	hook := &Hook{ID: "test", Name: "Test", Fn: func(ctx context.Context) error { return nil }}

	if err := b.Add(hook); err != nil {
		t.Errorf("Add() error = %v", err)
	}

	if b.Len() != 1 {
		t.Errorf("Len() = %d, want 1", b.Len())
	}
}

func TestBatchExecute(t *testing.T) {
	t.Run("concurrent execution", func(t *testing.T) {
		b := NewBatch()

		var mu sync.Mutex
		var order []string

		b.Add(&Hook{
			ID:   "a",
			Name: "A",
			Fn: func(ctx context.Context) error {
				mu.Lock()
				order = append(order, "a")
				mu.Unlock()
				time.Sleep(10 * time.Millisecond)
				return nil
			},
		})

		b.Add(&Hook{
			ID:   "b",
			Name: "B",
			Fn: func(ctx context.Context) error {
				mu.Lock()
				order = append(order, "b")
				mu.Unlock()
				time.Sleep(10 * time.Millisecond)
				return nil
			},
		})

		results := b.Execute(context.Background(), 5*time.Second)

		if len(results) != 2 {
			t.Errorf("results = %d, want 2", len(results))
		}

		// Both should succeed
		for _, r := range results {
			if !r.Success {
				t.Errorf("result for %s should be successful", r.HookName)
			}
		}
	})

	t.Run("partial failure", func(t *testing.T) {
		b := NewBatch()

		b.Add(&Hook{
			ID:   "success",
			Name: "Success",
			Fn:   func(ctx context.Context) error { return nil },
		})

		b.Add(&Hook{
			ID:   "fail",
			Name: "Fail",
			Fn:   func(ctx context.Context) error { return errors.New("test") },
		})

		results := b.Execute(context.Background(), 5*time.Second)

		var successCount, failCount int
		for _, r := range results {
			if r.Success {
				successCount++
			} else {
				failCount++
			}
		}

		if successCount != 1 || failCount != 1 {
			t.Errorf("results: success=%d, fail=%d, want 1,1", successCount, failCount)
		}
	})
}

func TestHooksSetErrorHandler(t *testing.T) {
	h := NewHooks()

	var called bool
	h.SetErrorHandler(func(hook *Hook, err error) {
		called = true
	})

	h.Add(&Hook{
		ID:      "fail",
		Name:    "Fail",
		CanFail: true,
		Fn:      func(ctx context.Context) error { return errors.New("test") },
	})

	executor := NewExecutor(h, 5*time.Second)
	executor.Execute(context.Background())

	if !called {
		t.Error("error handler was not called")
	}
}

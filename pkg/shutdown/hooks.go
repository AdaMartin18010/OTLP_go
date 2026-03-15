// Package shutdown provides graceful shutdown utilities for the OTLP Go SDK.
//
// This file contains the hooks registration system for managing
// shutdown callbacks with ordering and dependency support.
package shutdown

import (
	"context"
	"fmt"
	"sync"
	"time"
)

// Hook represents a shutdown hook with metadata.
type Hook struct {
	// ID is the unique identifier for this hook.
	ID string

	// Name is a human-readable name for the hook.
	Name string

	// Description provides additional context about what the hook does.
	Description string

	// Priority determines execution order (lower = earlier).
	Priority int

	// Timeout is the maximum time allowed for this hook to complete.
	// If zero, the global timeout is used.
	Timeout time.Duration

	// Fn is the shutdown function to execute.
	Fn ShutdownFunc

	// Dependencies are hook IDs that must complete before this hook runs.
	Dependencies []string

	// CanFail indicates whether the hook failure should stop shutdown.
	CanFail bool
}

// Validate validates the hook configuration.
func (h *Hook) Validate() error {
	if h.ID == "" {
		return fmt.Errorf("hook ID is required")
	}
	if h.Name == "" {
		return fmt.Errorf("hook name is required")
	}
	if h.Fn == nil {
		return fmt.Errorf("hook function is required")
	}
	return nil
}

// HookResult represents the result of a hook execution.
type HookResult struct {
	HookID    string
	HookName  string
	Success   bool
	Error     error
	Duration  time.Duration
	Timestamp time.Time
}

// Hooks is a collection of shutdown hooks.
type Hooks struct {
	hooks   map[string]*Hook
	mu      sync.RWMutex
	onError func(*Hook, error)
}

// NewHooks creates a new hooks collection.
func NewHooks() *Hooks {
	return &Hooks{
		hooks: make(map[string]*Hook),
		onError: func(h *Hook, err error) {
			// Default error handler does nothing
		},
	}
}

// Add adds a hook to the collection.
func (h *Hooks) Add(hook *Hook) error {
	if err := hook.Validate(); err != nil {
		return err
	}

	h.mu.Lock()
	defer h.mu.Unlock()

	if _, exists := h.hooks[hook.ID]; exists {
		return fmt.Errorf("hook with ID %q already exists", hook.ID)
	}

	h.hooks[hook.ID] = hook
	return nil
}

// Remove removes a hook by ID.
func (h *Hooks) Remove(id string) bool {
	h.mu.Lock()
	defer h.mu.Unlock()

	if _, exists := h.hooks[id]; !exists {
		return false
	}

	delete(h.hooks, id)
	return true
}

// Get retrieves a hook by ID.
func (h *Hooks) Get(id string) (*Hook, bool) {
	h.mu.RLock()
	defer h.mu.RUnlock()

	hook, exists := h.hooks[id]
	return hook, exists
}

// List returns all hooks sorted by priority.
func (h *Hooks) List() []*Hook {
	h.mu.RLock()
	defer h.mu.RUnlock()

	hooks := make([]*Hook, 0, len(h.hooks))
	for _, hook := range h.hooks {
		hooks = append(hooks, hook)
	}

	// Sort by priority (lower first)
	for i := 0; i < len(hooks); i++ {
		for j := i + 1; j < len(hooks); j++ {
			if hooks[j].Priority < hooks[i].Priority {
				hooks[i], hooks[j] = hooks[j], hooks[i]
			}
		}
	}

	return hooks
}

// Len returns the number of hooks.
func (h *Hooks) Len() int {
	h.mu.RLock()
	defer h.mu.RUnlock()
	return len(h.hooks)
}

// SetErrorHandler sets the error handler callback.
func (h *Hooks) SetErrorHandler(handler func(*Hook, error)) {
	h.mu.Lock()
	defer h.mu.Unlock()
	h.onError = handler
}

// Executor manages the execution of shutdown hooks.
type Executor struct {
	hooks         *Hooks
	globalTimeout time.Duration
	results       []HookResult
	mu            sync.RWMutex
}

// NewExecutor creates a new hook executor.
func NewExecutor(hooks *Hooks, timeout time.Duration) *Executor {
	return &Executor{
		hooks:         hooks,
		globalTimeout: timeout,
		results:       make([]HookResult, 0),
	}
}

// Execute runs all hooks in priority order.
func (e *Executor) Execute(ctx context.Context) ([]HookResult, error) {
	hooks := e.hooks.List()

	e.mu.Lock()
	e.results = make([]HookResult, 0, len(hooks))
	e.mu.Unlock()

	// Create timeout context if not provided
	if _, hasDeadline := ctx.Deadline(); !hasDeadline {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, e.globalTimeout)
		defer cancel()
	}

	completed := make(map[string]bool)

	for _, hook := range hooks {
		// Check dependencies
		for _, depID := range hook.Dependencies {
			if !completed[depID] {
				return e.results, fmt.Errorf("hook %q dependency %q not completed", hook.ID, depID)
			}
		}

		result := e.executeHook(ctx, hook)

		e.mu.Lock()
		e.results = append(e.results, result)
		e.mu.Unlock()

		completed[hook.ID] = result.Success

		if !result.Success && !hook.CanFail {
			return e.results, fmt.Errorf("required hook %q failed: %w", hook.ID, result.Error)
		}
	}

	return e.results, nil
}

// executeHook executes a single hook and records the result.
func (e *Executor) executeHook(ctx context.Context, hook *Hook) HookResult {
	start := time.Now()
	result := HookResult{
		HookID:    hook.ID,
		HookName:  hook.Name,
		Timestamp: start,
	}

	// Use hook-specific timeout if set
	hookCtx := ctx
	if hook.Timeout > 0 {
		var cancel context.CancelFunc
		hookCtx, cancel = context.WithTimeout(ctx, hook.Timeout)
		defer cancel()
	}

	done := make(chan error, 1)
	go func() {
		done <- hook.Fn(hookCtx)
	}()

	select {
	case err := <-done:
		result.Duration = time.Since(start)
		if err != nil {
			result.Error = err
			result.Success = false
			e.hooks.onError(hook, err)
		} else {
			result.Success = true
		}
	case <-hookCtx.Done():
		result.Duration = time.Since(start)
		result.Error = fmt.Errorf("hook timed out: %w", hookCtx.Err())
		result.Success = false
		e.hooks.onError(hook, result.Error)
	}

	return result
}

// Results returns the execution results.
func (e *Executor) Results() []HookResult {
	e.mu.RLock()
	defer e.mu.RUnlock()
	result := make([]HookResult, len(e.results))
	copy(result, e.results)
	return result
}

// Chain represents a chain of dependent hooks.
type Chain struct {
	hooks []*Hook
	mu    sync.RWMutex
}

// NewChain creates a new hook chain.
func NewChain() *Chain {
	return &Chain{
		hooks: make([]*Hook, 0),
	}
}

// Add adds a hook to the chain.
// Each hook automatically depends on the previous hook.
func (c *Chain) Add(hook *Hook) error {
	if err := hook.Validate(); err != nil {
		return err
	}

	c.mu.Lock()
	defer c.mu.Unlock()

	// Auto-set dependency on previous hook
	if len(c.hooks) > 0 {
		prevHook := c.hooks[len(c.hooks)-1]
		hook.Dependencies = append([]string{prevHook.ID}, hook.Dependencies...)
	}

	c.hooks = append(c.hooks, hook)
	return nil
}

// Hooks returns the hooks in the chain.
func (c *Chain) Hooks() []*Hook {
	c.mu.RLock()
	defer c.mu.RUnlock()
	result := make([]*Hook, len(c.hooks))
	copy(result, c.hooks)
	return result
}

// Len returns the number of hooks in the chain.
func (c *Chain) Len() int {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return len(c.hooks)
}

// Batch represents a group of hooks that can execute concurrently.
type Batch struct {
	hooks []*Hook
	mu    sync.RWMutex
}

// NewBatch creates a new hook batch.
func NewBatch() *Batch {
	return &Batch{
		hooks: make([]*Hook, 0),
	}
}

// Add adds a hook to the batch.
func (b *Batch) Add(hook *Hook) error {
	if err := hook.Validate(); err != nil {
		return err
	}

	b.mu.Lock()
	defer b.mu.Unlock()
	b.hooks = append(b.hooks, hook)
	return nil
}

// Execute runs all hooks in the batch concurrently.
func (b *Batch) Execute(ctx context.Context, timeout time.Duration) []HookResult {
	b.mu.RLock()
	hooks := make([]*Hook, len(b.hooks))
	copy(hooks, b.hooks)
	b.mu.RUnlock()

	if _, hasDeadline := ctx.Deadline(); !hasDeadline {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, timeout)
		defer cancel()
	}

	var wg sync.WaitGroup
	results := make([]HookResult, len(hooks))
	resultMu := sync.Mutex{}

	for i, hook := range hooks {
		wg.Add(1)
		go func(index int, h *Hook) {
			defer wg.Done()

			start := time.Now()
			result := HookResult{
				HookID:    h.ID,
				HookName:  h.Name,
				Timestamp: start,
			}

			err := h.Fn(ctx)
			result.Duration = time.Since(start)
			if err != nil {
				result.Error = err
				result.Success = false
			} else {
				result.Success = true
			}

			resultMu.Lock()
			results[index] = result
			resultMu.Unlock()
		}(i, hook)
	}

	wg.Wait()
	return results
}

// Hooks returns the hooks in the batch.
func (b *Batch) Hooks() []*Hook {
	b.mu.RLock()
	defer b.mu.RUnlock()
	result := make([]*Hook, len(b.hooks))
	copy(result, b.hooks)
	return result
}

// Len returns the number of hooks in the batch.
func (b *Batch) Len() int {
	b.mu.RLock()
	defer b.mu.RUnlock()
	return len(b.hooks)
}

// Package shutdown provides graceful shutdown utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Shutdown manager for coordinating cleanup
//   - Timeout handling
//   - Signal handling
//   - Resource cleanup ordering
package shutdown

import (
	"context"
	"sync"
	"time"
)

// Manager coordinates graceful shutdown.
type Manager struct {
	timeout time.Duration
	hooks   []func(context.Context) error
	mu      sync.RWMutex
}

// NewManager creates a new shutdown manager.
func NewManager(timeout time.Duration) *Manager {
	return &Manager{
		timeout: timeout,
		hooks:   make([]func(context.Context) error, 0),
	}
}

// Add adds a shutdown hook.
func (m *Manager) Add(hook func(context.Context) error) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.hooks = append(m.hooks, hook)
}

// Shutdown executes all shutdown hooks.
func (m *Manager) Shutdown(ctx context.Context) error {
	m.mu.RLock()
	hooks := make([]func(context.Context) error, len(m.hooks))
	copy(hooks, m.hooks)
	m.mu.RUnlock()

	ctx, cancel := context.WithTimeout(ctx, m.timeout)
	defer cancel()

	var wg sync.WaitGroup
	errCh := make(chan error, len(hooks))

	for _, hook := range hooks {
		wg.Add(1)
		go func(h func(context.Context) error) {
			defer wg.Done()
			if err := h(ctx); err != nil {
				errCh <- err
			}
		}(hook)
	}

	wg.Wait()
	close(errCh)

	var errs []error
	for err := range errCh {
		errs = append(errs, err)
	}

	if len(errs) > 0 {
		return errs[0]
	}
	return nil
}

// Done returns a channel that closes when shutdown completes.
func (m *Manager) Done() <-chan struct{} {
	done := make(chan struct{})
	go func() {
		ctx := context.Background()
		m.Shutdown(ctx)
		close(done)
	}()
	return done
}

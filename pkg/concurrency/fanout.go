// Package concurrency provides thread-safe primitives and utilities
// for concurrent programming in the OTLP Go SDK.
package concurrency

import (
	"context"
	"errors"
	"sync"
	"sync/atomic"
)

var (
	// ErrFanOutClosed is returned when operating on a closed fan-out.
	ErrFanOutClosed = errors.New("fan-out is closed")
	// ErrNoWorkers is returned when no workers are configured.
	ErrNoWorkers = errors.New("no workers configured")
)

// FanOut distributes tasks to multiple workers for parallel processing.
//
// FanOut implements the fan-out pattern where a single producer
// distributes work to multiple consumers running concurrently.
//
// Type parameter T represents the type of work items.
//
// Example usage:
//
//	fanout := concurrency.NewFanOut[int](10, 100)
//	defer fanout.Shutdown(context.Background())
//
//	// Set up worker
//	fanout.StartWorkers(func(ctx context.Context, item int) error {
//	    // Process item
//	    return nil
//	})
//
//	// Distribute work
//	for i := 0; i < 1000; i++ {
//	    fanout.Submit(ctx, i)
//	}
type FanOut[T any] struct {
	workers   int
	queueSize int

	input   chan T
	results chan FanOutResult
	errCh   chan error
	stopCh  chan struct{}
	doneCh  chan struct{}

	stopOnce sync.Once
	started  atomic.Bool
	closed   atomic.Bool

	wg      sync.WaitGroup
	ctx     context.Context
	cancel  context.CancelFunc
	mu      sync.RWMutex
	handler func(context.Context, T) error
}

// FanOutResult represents the result of a fan-out operation.
type FanOutResult struct {
	WorkerID int
	Item     any
	Error    error
}

// FanOutOption configures a FanOut.
type FanOutOption[T any] func(*FanOut[T])

// WithQueueSize sets the input queue size.
func WithFanOutQueueSize[T any](size int) FanOutOption[T] {
	return func(f *FanOut[T]) {
		f.queueSize = size
	}
}

// NewFanOut creates a new fan-out distributor.
//
// workers specifies the number of concurrent workers.
// Each worker processes items from the shared input queue.
func NewFanOut[T any](workers int, opts ...FanOutOption[T]) *FanOut[T] {
	if workers <= 0 {
		workers = 1
	}

	ctx, cancel := context.WithCancel(context.Background())

	f := &FanOut[T]{
		workers:   workers,
		queueSize: workers * 10,
		stopCh:    make(chan struct{}),
		doneCh:    make(chan struct{}),
		errCh:     make(chan error, workers*2),
		ctx:       ctx,
		cancel:    cancel,
	}

	for _, opt := range opts {
		opt(f)
	}

	f.input = make(chan T, f.queueSize)
	f.results = make(chan FanOutResult, f.queueSize)

	return f
}

// StartWorkers starts the fan-out workers with the given handler.
//
// The handler function is called for each work item received.
// It runs in a separate goroutine for each worker.
func (f *FanOut[T]) StartWorkers(handler func(context.Context, T) error) {
	if f.started.Load() {
		return
	}

	f.started.Store(true)
	f.handler = handler

	for i := 0; i < f.workers; i++ {
		f.wg.Add(1)
		go f.worker(i)
	}

	// Wait for completion in background
	go func() {
		f.wg.Wait()
		close(f.doneCh)
		close(f.results)
		close(f.errCh)
	}()
}

// worker is the main loop for each fan-out worker.
func (f *FanOut[T]) worker(id int) {
	defer f.wg.Done()

	for {
		select {
		case <-f.ctx.Done():
			return
		case <-f.stopCh:
			return
		case item, ok := <-f.input:
			if !ok {
				return
			}

			err := f.handler(f.ctx, item)

			if err != nil {
				select {
				case f.errCh <- err:
				case <-f.ctx.Done():
					return
				}
			}

			select {
			case f.results <- FanOutResult{WorkerID: id, Item: item, Error: err}:
			case <-f.ctx.Done():
				return
			}
		}
	}
}

// Submit submits an item to be processed.
//
// Returns ErrFanOutClosed if the fan-out has been shut down.
func (f *FanOut[T]) Submit(ctx context.Context, item T) error {
	if f.closed.Load() {
		return ErrFanOutClosed
	}

	if !f.started.Load() {
		return ErrNoWorkers
	}

	select {
	case f.input <- item:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	case <-f.stopCh:
		return ErrFanOutClosed
	}
}

// TrySubmit attempts to submit without blocking.
//
// Returns true if the item was submitted, false otherwise.
func (f *FanOut[T]) TrySubmit(item T) bool {
	if f.closed.Load() || !f.started.Load() {
		return false
	}

	select {
	case f.input <- item:
		return true
	default:
		return false
	}
}

// Results returns the results channel.
//
// This channel receives a result for each processed item.
func (f *FanOut[T]) Results() <-chan FanOutResult {
	return f.results
}

// Errors returns the error channel.
//
// This channel receives errors from worker handlers.
func (f *FanOut[T]) Errors() <-chan error {
	return f.errCh
}

// Done returns a channel that's closed when all workers complete.
func (f *FanOut[T]) Done() <-chan struct{} {
	return f.doneCh
}

// Shutdown gracefully shuts down the fan-out.
//
// This method:
// 1. Stops accepting new submissions
// 2. Waits for all queued items to be processed
// 3. Signals workers to stop
// 4. Waits for all workers to finish
func (f *FanOut[T]) Shutdown(ctx context.Context) error {
	f.stopOnce.Do(func() {
		f.closed.Store(true)
		f.cancel()
		close(f.stopCh)
		close(f.input)
	})

	// If workers were never started, close doneCh here
	if !f.started.Load() {
		close(f.doneCh)
		return nil
	}

	select {
	case <-f.doneCh:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// Stop immediately stops the fan-out.
//
// Any pending items in the queue will not be processed.
func (f *FanOut[T]) Stop() {
	f.stopOnce.Do(func() {
		f.closed.Store(true)
		f.cancel()
		close(f.stopCh)
		close(f.input)
	})

	f.wg.Wait()
}

// Stats returns current fan-out statistics.
type FanOutStats struct {
	Workers int
	Started bool
	Closed  bool
}

// Stats returns current statistics.
func (f *FanOut[T]) Stats() FanOutStats {
	return FanOutStats{
		Workers: f.workers,
		Started: f.started.Load(),
		Closed:  f.closed.Load(),
	}
}

// FanIn collects results from multiple input channels into a single output channel.
//
// This is the companion to FanOut, combining results from parallel workers.
//
// Type parameter T represents the type of items being collected.
//
// Example usage:
//
//	inputs := []<-chan int{ch1, ch2, ch3}
//	output := concurrency.FanIn(ctx, inputs...)
//
//	for result := range output {
//	    // Process result from any input channel
//	}
func FanIn[T any](ctx context.Context, inputs ...<-chan T) <-chan T {
	output := make(chan T)
	var wg sync.WaitGroup

	// Start a goroutine for each input channel
	for _, input := range inputs {
		wg.Add(1)
		go func(ch <-chan T) {
			defer wg.Done()
			for {
				select {
				case val, ok := <-ch:
					if !ok {
						return
					}
					select {
					case output <- val:
					case <-ctx.Done():
						return
					}
				case <-ctx.Done():
					return
				}
			}
		}(input)
	}

	// Close output when all inputs are done
	go func() {
		wg.Wait()
		close(output)
	}()

	return output
}

// FanOutFanIn combines fan-out and fan-in for parallel processing with result collection.
//
// This is a convenience function that creates a complete parallel processing pipeline.
//
// Example usage:
//
//	results, errors := concurrency.FanOutFanIn(ctx, items, 10, func(ctx context.Context, item int) (string, error) {
//	    return process(item)
//	})
//
//	for result := range results {
//	    // Handle result
//	}
func FanOutFanIn[I, O any](
	ctx context.Context,
	inputs []I,
	workers int,
	processor func(context.Context, I) (O, error),
) (<-chan O, <-chan error) {
	output := make(chan O, len(inputs))
	errCh := make(chan error, workers*2)

	var wg sync.WaitGroup
	sem := make(chan struct{}, workers)

	for _, input := range inputs {
		wg.Add(1)
		go func(item I) {
			defer wg.Done()

			sem <- struct{}{}
			defer func() { <-sem }()

			select {
			case <-ctx.Done():
				return
			default:
			}

			result, err := processor(ctx, item)
			if err != nil {
				select {
				case errCh <- err:
				case <-ctx.Done():
				}
				return
			}

			select {
			case output <- result:
			case <-ctx.Done():
				return
			}
		}(input)
	}

	go func() {
		wg.Wait()
		close(output)
		close(errCh)
	}()

	return output, errCh
}

// ScatterGather distributes work to workers and collects results.
//
// This is similar to FanOutFanIn but with a simpler API for
// cases where you want to wait for all results.
type ScatterGather[T, R any] struct {
	workers int
}

// NewScatterGather creates a new scatter-gather processor.
func NewScatterGather[T, R any](workers int) *ScatterGather[T, R] {
	if workers <= 0 {
		workers = 1
	}
	return &ScatterGather[T, R]{workers: workers}
}

// Process distributes items to workers and returns all results.
//
// Results are returned in the same order as inputs.
// If any processor returns an error, the operation stops and returns that error.
func (sg *ScatterGather[T, R]) Process(
	ctx context.Context,
	items []T,
	processor func(context.Context, T) (R, error),
) ([]R, error) {
	if len(items) == 0 {
		return []R{}, nil
	}

	results := make([]R, len(items))
	sem := make(chan struct{}, sg.workers)
	var wg sync.WaitGroup

	errCh := make(chan error, 1)
	var errOnce sync.Once

	for i, item := range items {
		wg.Add(1)
		go func(idx int, it T) {
			defer wg.Done()

			select {
			case <-ctx.Done():
				errOnce.Do(func() { <-errCh; errCh <- ctx.Err() })
				return
			case sem <- struct{}{}:
				defer func() { <-sem }()
			}

			result, err := processor(ctx, it)
			if err != nil {
				errOnce.Do(func() {
					select {
					case errCh <- err:
					default:
					}
				})
				return
			}

			results[idx] = result
		}(i, item)
	}

	wg.Wait()
	close(errCh)

	if err := <-errCh; err != nil {
		return nil, err
	}

	return results, nil
}

// Parallel executes functions in parallel and waits for all to complete.
//
// Returns a slice of errors corresponding to each function.
// The errors slice will be nil if all functions succeed.
func Parallel(ctx context.Context, fns ...func(context.Context) error) []error {
	if len(fns) == 0 {
		return nil
	}

	errors := make([]error, len(fns))
	var wg sync.WaitGroup

	for i, fn := range fns {
		wg.Add(1)
		go func(idx int, f func(context.Context) error) {
			defer wg.Done()
			errors[idx] = f(ctx)
		}(i, fn)
	}

	wg.Wait()

	// Check if any errors occurred
	hasErrors := false
	for _, err := range errors {
		if err != nil {
			hasErrors = true
			break
		}
	}

	if !hasErrors {
		return nil
	}

	return errors
}

// Race executes functions in parallel and returns the first successful result.
//
// If all functions fail, returns a combined error.
// The context is cancelled when the first successful result is received.
func Race[T any](ctx context.Context, fns ...func(context.Context) (T, error)) (T, error) {
	var zero T
	if len(fns) == 0 {
		return zero, ErrNoWorkers
	}

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	resultCh := make(chan T, 1)
	errCh := make(chan error, len(fns))
	var wg sync.WaitGroup

	for _, fn := range fns {
		wg.Add(1)
		go func(f func(context.Context) (T, error)) {
			defer wg.Done()

			result, err := f(ctx)
			if err != nil {
				select {
				case errCh <- err:
				case <-ctx.Done():
				}
				return
			}

			select {
			case resultCh <- result:
				cancel() // Cancel other goroutines
			case <-ctx.Done():
			}
		}(fn)
	}

	// Close channels when all goroutines complete
	go func() {
		wg.Wait()
		close(resultCh)
		close(errCh)
	}()

	var errs []error
	for {
		select {
		case result, ok := <-resultCh:
			if ok {
				return result, nil
			}
			// Channel closed without result
			return zero, errors.New("all racers failed")
		case err, ok := <-errCh:
			if ok {
				errs = append(errs, err)
			} else {
				errCh = nil
			}
		}

		if resultCh == nil && errCh == nil {
			break
		}
	}

	return zero, errors.New("all racers failed")
}

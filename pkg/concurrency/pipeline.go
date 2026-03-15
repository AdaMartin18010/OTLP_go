// Package concurrency provides thread-safe primitives and utilities
// for concurrent programming in the OTLP Go SDK.
package concurrency

import (
	"context"
	"errors"
	"sync"
)

var (
	// ErrPipelineClosed is returned when operating on a closed pipeline.
	ErrPipelineClosed = errors.New("pipeline is closed")
	// ErrStageError is returned when a pipeline stage encounters an error.
	ErrStageError = errors.New("pipeline stage error")
)

// Stage represents a single stage in a processing pipeline.
//
// A Stage transforms input of type I to output of type O.
// Implementations should be thread-safe and handle context cancellation.
type Stage[I, O any] interface {
	// Process transforms the input to output.
	Process(ctx context.Context, input I) (O, error)
}

// StageFunc is an adapter to allow the use of ordinary functions as Stage.
type StageFunc[I, O any] func(ctx context.Context, input I) (O, error)

// Process implements the Stage interface.
func (f StageFunc[I, O]) Process(ctx context.Context, input I) (O, error) {
	return f(ctx, input)
}

// Pipeline represents a multi-stage concurrent processing pipeline.
//
// A Pipeline processes data through a series of connected stages,
// where each stage can run concurrently. Data flows from the source
// through each stage to the sink.
//
// Type parameters:
//   - T: The input type from the source
//   - R: The output type to the sink
//
// Example usage:
//
//	pipeline := concurrency.NewPipeline[int, string](
//	    func(ctx context.Context, input int) (int, error) {
//	        return input * 2, nil
//	    },
//	    func(ctx context.Context, input int) (string, error) {
//	        return strconv.Itoa(input), nil
//	    },
//	)
//
//	pipeline.Start(ctx)
//	defer pipeline.Stop()
//
//	// Send data
//	pipeline.Send(ctx, 42)
//
//	// Receive results
//	result := <-pipeline.Receive()
type Pipeline[T, R any] struct {
	stages     []stageInfo
	bufferSize int

	input   chan T
	output  chan PipelineResult[R]
	errCh   chan error
	stopCh  chan struct{}
	stopOnce sync.Once

	wg     sync.WaitGroup
	ctx    context.Context
	cancel context.CancelFunc
	closed atomic.Bool
}

// stageInfo holds runtime information about a pipeline stage.
type stageInfo struct {
	fn      func(context.Context, any) (any, error)
	workers int
}

// PipelineResult wraps the pipeline output with potential errors.
type PipelineResult[R any] struct {
	Value R
	Error error
}

// PipelineOption configures a Pipeline.
type PipelineOption func(*Pipeline[any, any])

// WithBufferSize sets the channel buffer size for the pipeline.
func WithBufferSize(size int) PipelineOption {
	return func(p *Pipeline[any, any]) {
		p.bufferSize = size
	}
}

// NewPipeline creates a new pipeline with the given stages.
//
// Each stage function transforms input to output. The pipeline
// creates goroutines for each stage to enable concurrent processing.
//
// Type parameters flow through stages:
//   - T -> intermediate type 1 -> ... -> intermediate type N -> R
func NewPipeline[T, R any](
	firstStage StageFunc[T, any],
	stages ...StageFunc[any, any],
) *Pipeline[T, R] {
	ctx, cancel := context.WithCancel(context.Background())

	p := &Pipeline[T, R]{
		bufferSize: 100,
		errCh:      make(chan error, 10),
		stopCh:     make(chan struct{}),
		ctx:        ctx,
		cancel:     cancel,
	}

	// Build stage chain
	allStages := append([]StageFunc[any, any]{wrapStage(firstStage)}, stages...)

	for _, s := range allStages {
		p.stages = append(p.stages, stageInfo{
			fn:      s,
			workers: 1,
		})
	}

	return p
}

// wrapStage adapts the first stage to the common stage signature.
func wrapStage[T any](fn StageFunc[T, any]) StageFunc[any, any] {
	return func(ctx context.Context, input any) (any, error) {
		return fn(ctx, input.(T))
	}
}

// NewPipelineWithWorkers creates a pipeline with configurable workers per stage.
//
// workers specifies the number of goroutines for each stage.
// The length of workers must match the number of stages.
func NewPipelineWithWorkers[T, R any](
	workers []int,
	firstStage StageFunc[T, any],
	stages ...StageFunc[any, any],
) *Pipeline[T, R] {
	p := NewPipeline[T, R](firstStage, stages...)

	for i, w := range workers {
		if i < len(p.stages) && w > 0 {
			p.stages[i].workers = w
		}
	}

	return p
}

// Start starts the pipeline processing.
//
// This method must be called before sending data to the pipeline.
// It creates all the goroutines for each stage.
func (p *Pipeline[T, R]) Start(ctx context.Context) {
	p.ctx, p.cancel = context.WithCancel(ctx)

	p.input = make(chan T, p.bufferSize)
	p.output = make(chan PipelineResult[R], p.bufferSize)

	// Connect stages with channels
	currentInput := p.input

	for i, stage := range p.stages {
		var nextInput chan any
		isLastStage := i == len(p.stages)-1

		if isLastStage {
			nextInput = nil // Last stage outputs to p.output
		} else {
			nextInput = make(chan any, p.bufferSize)
		}

		// Start workers for this stage
		for w := 0; w < stage.workers; w++ {
			p.wg.Add(1)
			go p.runStage(stage.fn, currentInput, nextInput, isLastStage)
		}

		currentInput = nextInput
	}
}

// runStage runs a single pipeline stage worker.
func (p *Pipeline[T, R]) runStage(
	fn func(context.Context, any) (any, error),
	input <-chan any,
	output chan<- any,
	isLast bool,
) {
	defer p.wg.Done()

	for {
		select {
		case <-p.ctx.Done():
			return
		case <-p.stopCh:
			return
		case val, ok := <-input:
			if !ok {
				return
			}

			result, err := fn(p.ctx, val)
			if err != nil {
				select {
				case p.errCh <- err:
				case <-p.ctx.Done():
					return
				}
				continue
			}

			if isLast {
				// Last stage: send to output channel
				select {
				case p.output <- PipelineResult[R]{Value: result.(R)}:
				case <-p.ctx.Done():
					return
				}
			} else {
				// Intermediate stage: send to next stage
				select {
				case output <- result:
				case <-p.ctx.Done():
					return
				}
			}
		}
	}
}

// Send sends data into the pipeline.
//
// Returns ErrPipelineClosed if the pipeline has been stopped.
// The context controls the send timeout.
func (p *Pipeline[T, R]) Send(ctx context.Context, data T) error {
	if p.closed.Load() {
		return ErrPipelineClosed
	}

	select {
	case p.input <- data:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	case <-p.stopCh:
		return ErrPipelineClosed
	}
}

// Receive returns the output channel for receiving pipeline results.
//
// Users must read from this channel to prevent blocking.
// The channel is closed when the pipeline is stopped.
func (p *Pipeline[T, R]) Receive() <-chan PipelineResult[R] {
	return p.output
}

// Errors returns the error channel for receiving pipeline errors.
//
// Errors from any stage are sent to this channel.
func (p *Pipeline[T, R]) Errors() <-chan error {
	return p.errCh
}

// Stop gracefully stops the pipeline.
//
// This method:
// 1. Signals all stages to stop after processing current items
// 2. Closes the input channel
// 3. Waits for all stages to complete
// 4. Closes output channels
func (p *Pipeline[T, R]) Stop() {
	p.stopOnce.Do(func() {
		p.closed.Store(true)
		p.cancel()
		close(p.stopCh)
		close(p.input)
	})

	p.wg.Wait()

	close(p.output)
	close(p.errCh)
}

// StopContext stops the pipeline with context timeout.
//
// If the pipeline doesn't stop within the context deadline,
// it returns the context error.
func (p *Pipeline[T, R]) StopContext(ctx context.Context) error {
	done := make(chan struct{})
	go func() {
		p.Stop()
		close(done)
	}()

	select {
	case <-done:
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

// StageBuilder helps build pipelines with a fluent API.
type StageBuilder[T, R any] struct {
	stages []StageFunc[any, any]
}

// NewStageBuilder creates a new pipeline stage builder.
func NewStageBuilder[T any]() *StageBuilder[T, T] {
	return &StageBuilder[T, T]{}
}

// Then adds a stage to the pipeline.
func (b *StageBuilder[T, R]) Then(next StageFunc[R, any]) *StageBuilder[T, any] {
	return &StageBuilder[T, any]{
		stages: append(b.stages, wrapStageFunc(next)),
	}
}

// ThenTransform adds a typed stage to the pipeline.
func (b *StageBuilder[T, R]) ThenTransform(next StageFunc[R, R]) *StageBuilder[T, R] {
	return &StageBuilder[T, R]{
		stages: append(b.stages, wrapStageFunc(next)),
	}
}

// Build creates the pipeline.
func (b *StageBuilder[T, R]) Build() *Pipeline[T, R] {
	if len(b.stages) == 0 {
		return nil
	}
	return NewPipeline[T, R](
		StageFunc[T, any](b.stages[0]),
		b.stages[1:]...,
	)
}

// wrapStageFunc adapts a typed stage function to the generic signature.
func wrapStageFunc[T any](fn StageFunc[T, T]) StageFunc[any, any] {
	return func(ctx context.Context, input any) (any, error) {
		return fn(ctx, input.(T))
	}
}

// Map applies a transformation function to each element in a slice concurrently.
//
// The concurrency parameter controls how many goroutines are used.
// Results maintain the order of inputs.
func Map[I, O any](
	ctx context.Context,
	inputs []I,
	concurrency int,
	fn func(context.Context, I) (O, error),
) ([]O, error) {
	if concurrency <= 0 {
		concurrency = len(inputs)
	}
	if concurrency > len(inputs) {
		concurrency = len(inputs)
	}

	results := make([]O, len(inputs))
	var errOnce sync.Once
	var firstErr error

	sem := make(chan struct{}, concurrency)
	var wg sync.WaitGroup

	for i, input := range inputs {
		wg.Add(1)
		go func(idx int, in I) {
			defer wg.Done()

			sem <- struct{}{}
			defer func() { <-sem }()

			select {
			case <-ctx.Done():
				errOnce.Do(func() { firstErr = ctx.Err() })
				return
			default:
			}

			result, err := fn(ctx, in)
			if err != nil {
				errOnce.Do(func() { firstErr = err })
				return
			}
			results[idx] = result
		}(i, input)
	}

	wg.Wait()
	return results, firstErr
}

// Filter filters elements in a slice based on a predicate.
//
// The concurrency parameter controls how many goroutines are used.
// Results maintain the order of inputs.
func Filter[T any](
	ctx context.Context,
	inputs []T,
	concurrency int,
	predicate func(context.Context, T) (bool, error),
) ([]T, error) {
	type result struct {
		index   int
		value   T
		include bool
	}

	if concurrency <= 0 {
		concurrency = len(inputs)
	}

	results := make([]result, len(inputs))
	var errOnce sync.Once
	var firstErr error

	sem := make(chan struct{}, concurrency)
	var wg sync.WaitGroup

	for i, input := range inputs {
		wg.Add(1)
		go func(idx int, in T) {
			defer wg.Done()

			sem <- struct{}{}
			defer func() { <-sem }()

			select {
			case <-ctx.Done():
				errOnce.Do(func() { firstErr = ctx.Err() })
				return
			default:
			}

			include, err := predicate(ctx, in)
			if err != nil {
				errOnce.Do(func() { firstErr = err })
				return
			}

			results[idx] = result{index: idx, value: in, include: include}
		}(i, input)
	}

	wg.Wait()

	if firstErr != nil {
		return nil, firstErr
	}

	// Collect results in order
	filtered := make([]T, 0, len(inputs))
	for _, r := range results {
		if r.include {
			filtered = append(filtered, r.value)
		}
	}

	return filtered, nil
}

// Reduce reduces a slice to a single value using a reducer function.
//
// Note: This is not concurrent as reduction typically requires
// sequential processing. Use for associative operations only.
func Reduce[T, R any](
	ctx context.Context,
	inputs []T,
	initial R,
	reducer func(context.Context, R, T) (R, error),
) (R, error) {
	result := initial
	var err error

	for _, input := range inputs {
		select {
		case <-ctx.Done():
			return result, ctx.Err()
		default:
		}

		result, err = reducer(ctx, result, input)
		if err != nil {
			return result, err
		}
	}

	return result, nil
}

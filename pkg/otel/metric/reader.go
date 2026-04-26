package metric

import (
	"context"
	"fmt"
	"sync"
	"time"

	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/metric/metricdata"
)

// TemporalitySelector selects the temporality for a given instrument kind.
type TemporalitySelector func(InstrumentKind) metricdata.Temporality

// AggregationSelector selects the aggregation for a given instrument kind.
type AggregationSelector func(InstrumentKind) sdkmetric.Aggregation

// MetricReader is the interface for metric readers.
// It wraps the OpenTelemetry SDK reader and provides additional configuration.
type MetricReader interface {
	// RegisterProducer registers a producer to provide external metrics.
	RegisterProducer(producer sdkmetric.Producer)
	// Collect gathers metrics and stores them in rm.
	Collect(ctx context.Context, rm *metricdata.ResourceMetrics) error
	// ForceFlush flushes all pending metrics.
	ForceFlush(ctx context.Context) error
	// Shutdown shuts down the reader.
	Shutdown(ctx context.Context) error
	// Temporality returns the temporality for the given instrument kind.
	Temporality(kind InstrumentKind) metricdata.Temporality
	// Aggregation returns the aggregation for the given instrument kind.
	Aggregation(kind InstrumentKind) sdkmetric.Aggregation
	// SDKReader returns the underlying SDK reader.
	SDKReader() sdkmetric.Reader
}

// ReaderOptions configures a MetricReader.
type ReaderOptions struct {
	TemporalitySelector TemporalitySelector
	AggregationSelector AggregationSelector
}

// manualReader wraps sdkmetric.ManualReader.
type manualReader struct {
	reader      *sdkmetric.ManualReader
	temporality TemporalitySelector
	aggregation AggregationSelector
	producers   []sdkmetric.Producer
	mu          sync.RWMutex
}

// NewManualReader creates a new manual (pull-based) metric reader.
// Manual readers are typically used for testing or Prometheus-style scraping.
func NewManualReader(opts ReaderOptions) MetricReader {
	var sdkOpts []sdkmetric.ManualReaderOption

	if opts.TemporalitySelector != nil {
		sdkOpts = append(sdkOpts, sdkmetric.WithTemporalitySelector(
			wrapTemporalitySelector(opts.TemporalitySelector),
		))
	}
	if opts.AggregationSelector != nil {
		sdkOpts = append(sdkOpts, sdkmetric.WithAggregationSelector(
			wrapAggregationSelector(opts.AggregationSelector),
		))
	}

	reader := sdkmetric.NewManualReader(sdkOpts...)
	return &manualReader{
		reader:      reader,
		temporality: opts.TemporalitySelector,
		aggregation: opts.AggregationSelector,
		producers:   make([]sdkmetric.Producer, 0),
	}
}

func (r *manualReader) RegisterProducer(producer sdkmetric.Producer) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.producers = append(r.producers, producer)
}

func (r *manualReader) Collect(ctx context.Context, rm *metricdata.ResourceMetrics) error {
	if err := r.reader.Collect(ctx, rm); err != nil {
		return err
	}

	r.mu.RLock()
	producers := r.producers
	r.mu.RUnlock()

	for _, producer := range producers {
		externalMetrics, err := producer.Produce(ctx)
		if err != nil {
			return err
		}
		rm.ScopeMetrics = append(rm.ScopeMetrics, externalMetrics...)
	}

	return nil
}

func (r *manualReader) ForceFlush(ctx context.Context) error {
	// ManualReader does not support ForceFlush in this version.
	_ = ctx
	return nil
}

func (r *manualReader) Shutdown(ctx context.Context) error {
	return r.reader.Shutdown(ctx)
}

func (r *manualReader) Temporality(kind InstrumentKind) metricdata.Temporality {
	r.mu.RLock()
	defer r.mu.RUnlock()
	if r.temporality != nil {
		return r.temporality(kind)
	}
	return metricdata.CumulativeTemporality
}

func (r *manualReader) Aggregation(kind InstrumentKind) sdkmetric.Aggregation {
	r.mu.RLock()
	defer r.mu.RUnlock()
	if r.aggregation != nil {
		return r.aggregation(kind)
	}
	return defaultAggregation(kind)
}

func (r *manualReader) SDKReader() sdkmetric.Reader {
	return r.reader
}

// periodicExportingReader wraps sdkmetric.PeriodicReader.
type periodicExportingReader struct {
	reader      *sdkmetric.PeriodicReader
	temporality TemporalitySelector
	aggregation AggregationSelector
	producers   []sdkmetric.Producer
	mu          sync.RWMutex
}

// NewPeriodicExportingReader creates a new periodic exporting metric reader.
// Metrics are collected and exported at the specified interval.
func NewPeriodicExportingReader(exporter sdkmetric.Exporter, interval, timeout time.Duration, opts ReaderOptions) MetricReader {
	var sdkOpts []sdkmetric.PeriodicReaderOption
	if interval > 0 {
		sdkOpts = append(sdkOpts, sdkmetric.WithInterval(interval))
	}
	if timeout > 0 {
		sdkOpts = append(sdkOpts, sdkmetric.WithTimeout(timeout))
	}

	reader := sdkmetric.NewPeriodicReader(exporter, sdkOpts...)
	return &periodicExportingReader{
		reader:      reader,
		temporality: opts.TemporalitySelector,
		aggregation: opts.AggregationSelector,
		producers:   make([]sdkmetric.Producer, 0),
	}
}

func (r *periodicExportingReader) RegisterProducer(producer sdkmetric.Producer) {
	r.mu.Lock()
	defer r.mu.Unlock()
	r.producers = append(r.producers, producer)
}

func (r *periodicExportingReader) Collect(ctx context.Context, rm *metricdata.ResourceMetrics) error {
	if err := r.reader.Collect(ctx, rm); err != nil {
		return err
	}

	r.mu.RLock()
	producers := r.producers
	r.mu.RUnlock()

	for _, producer := range producers {
		externalMetrics, err := producer.Produce(ctx)
		if err != nil {
			return err
		}
		rm.ScopeMetrics = append(rm.ScopeMetrics, externalMetrics...)
	}

	return nil
}

func (r *periodicExportingReader) ForceFlush(ctx context.Context) error {
	return r.reader.ForceFlush(ctx)
}

func (r *periodicExportingReader) Shutdown(ctx context.Context) error {
	return r.reader.Shutdown(ctx)
}

func (r *periodicExportingReader) Temporality(kind InstrumentKind) metricdata.Temporality {
	r.mu.RLock()
	defer r.mu.RUnlock()
	if r.temporality != nil {
		return r.temporality(kind)
	}
	return metricdata.CumulativeTemporality
}

func (r *periodicExportingReader) Aggregation(kind InstrumentKind) sdkmetric.Aggregation {
	r.mu.RLock()
	defer r.mu.RUnlock()
	if r.aggregation != nil {
		return r.aggregation(kind)
	}
	return defaultAggregation(kind)
}

func (r *periodicExportingReader) SDKReader() sdkmetric.Reader {
	return r.reader
}

// wrapTemporalitySelector wraps our InstrumentKind selector to SDK's InstrumentKind selector.
func wrapTemporalitySelector(selector TemporalitySelector) sdkmetric.TemporalitySelector {
	return func(ik sdkmetric.InstrumentKind) metricdata.Temporality {
		return selector(convertSDKInstrumentKind(ik))
	}
}

// wrapAggregationSelector wraps our InstrumentKind selector to SDK's InstrumentKind selector.
func wrapAggregationSelector(selector AggregationSelector) sdkmetric.AggregationSelector {
	return func(ik sdkmetric.InstrumentKind) sdkmetric.Aggregation {
		return selector(convertSDKInstrumentKind(ik))
	}
}

// convertSDKInstrumentKind converts SDK instrument kind to our InstrumentKind.
func convertSDKInstrumentKind(ik sdkmetric.InstrumentKind) InstrumentKind {
	switch ik {
	case sdkmetric.InstrumentKindCounter:
		return InstrumentKindCounter
	case sdkmetric.InstrumentKindUpDownCounter:
		return InstrumentKindUpDownCounter
	case sdkmetric.InstrumentKindHistogram:
		return InstrumentKindHistogram
	case sdkmetric.InstrumentKindObservableCounter:
		return InstrumentKindObservableCounter
	case sdkmetric.InstrumentKindObservableUpDownCounter:
		return InstrumentKindObservableUpDownCounter
	case sdkmetric.InstrumentKindObservableGauge:
		return InstrumentKindObservableGauge
	case sdkmetric.InstrumentKindGauge:
		return InstrumentKindGauge
	default:
		return InstrumentKindCounter
	}
}

// defaultAggregation returns the default aggregation for an instrument kind.
func defaultAggregation(kind InstrumentKind) sdkmetric.Aggregation {
	switch kind {
	case InstrumentKindCounter, InstrumentKindUpDownCounter,
		InstrumentKindObservableCounter, InstrumentKindObservableUpDownCounter:
		return sdkmetric.AggregationSum{}
	case InstrumentKindHistogram:
		return sdkmetric.AggregationExplicitBucketHistogram{
			Boundaries: DefaultHistogramBoundaries(),
		}
	case InstrumentKindGauge, InstrumentKindObservableGauge:
		return sdkmetric.AggregationLastValue{}
	default:
		return sdkmetric.AggregationSum{}
	}
}

// Common temporality selectors

// DeltaTemporalitySelector returns delta temporality for all instruments.
func DeltaTemporalitySelector() TemporalitySelector {
	return func(_ InstrumentKind) metricdata.Temporality {
		return metricdata.DeltaTemporality
	}
}

// CumulativeTemporalitySelector returns cumulative temporality for all instruments.
func CumulativeTemporalitySelector() TemporalitySelector {
	return func(_ InstrumentKind) metricdata.Temporality {
		return metricdata.CumulativeTemporality
	}
}

// String returns a string representation of the reader.
func (r *manualReader) String() string {
	return fmt.Sprintf("ManualReader{temporality=%v, aggregation=%v}", r.temporality, r.aggregation)
}

// String returns a string representation of the reader.
func (r *periodicExportingReader) String() string {
	return fmt.Sprintf("PeriodicExportingReader{temporality=%v, aggregation=%v}", r.temporality, r.aggregation)
}

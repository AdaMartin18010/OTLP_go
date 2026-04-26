package metric

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/metric/metricdata"
)

func TestNewManualReader(t *testing.T) {
	r := NewManualReader(ReaderOptions{})
	require.NotNil(t, r)

	ctx := context.Background()
	var rm metricdata.ResourceMetrics
	// Collect returns "reader is not registered" when not attached to a MeterProvider.
	// This is expected behavior.
	_ = r.Collect(ctx, &rm)

	err := r.Shutdown(ctx)
	assert.NoError(t, err)
}

func TestNewManualReader_WithTemporality(t *testing.T) {
	r := NewManualReader(ReaderOptions{
		TemporalitySelector: DeltaTemporalitySelector(),
	})
	require.NotNil(t, r)

	assert.Equal(t, DeltaTemporalitySelector()(InstrumentKindCounter), r.Temporality(InstrumentKindCounter))
}

func TestNewManualReader_WithAggregation(t *testing.T) {
	r := NewManualReader(ReaderOptions{
		AggregationSelector: func(_ InstrumentKind) sdkmetric.Aggregation {
			return sdkmetric.AggregationDrop{}
		},
	})
	require.NotNil(t, r)

	assert.IsType(t, sdkmetric.AggregationDrop{}, r.Aggregation(InstrumentKindCounter))
}

func TestNewPeriodicExportingReader(t *testing.T) {
	exp := &noopExporter{}
	r := NewPeriodicExportingReader(exp, time.Second, 5*time.Second, ReaderOptions{})
	require.NotNil(t, r)

	ctx := context.Background()
	err := r.ForceFlush(ctx)
	assert.NoError(t, err)

	err = r.Shutdown(ctx)
	assert.NoError(t, err)
}

func TestDeltaTemporalitySelector(t *testing.T) {
	sel := DeltaTemporalitySelector()
	for _, kind := range []InstrumentKind{
		InstrumentKindCounter,
		InstrumentKindUpDownCounter,
		InstrumentKindHistogram,
		InstrumentKindGauge,
	} {
		assert.Equal(t, "DeltaTemporality", sel(kind).String())
	}
}

func TestCumulativeTemporalitySelector(t *testing.T) {
	sel := CumulativeTemporalitySelector()
	for _, kind := range []InstrumentKind{
		InstrumentKindCounter,
		InstrumentKindUpDownCounter,
		InstrumentKindHistogram,
		InstrumentKindGauge,
	} {
		assert.Equal(t, "CumulativeTemporality", sel(kind).String())
	}
}

func TestDefaultAggregation(t *testing.T) {
	assert.IsType(t, sdkmetric.AggregationSum{}, defaultAggregation(InstrumentKindCounter))
	assert.IsType(t, sdkmetric.AggregationSum{}, defaultAggregation(InstrumentKindUpDownCounter))
	assert.IsType(t, sdkmetric.AggregationExplicitBucketHistogram{}, defaultAggregation(InstrumentKindHistogram))
	assert.IsType(t, sdkmetric.AggregationLastValue{}, defaultAggregation(InstrumentKindGauge))
}

type noopExporter struct{}

func (n *noopExporter) Temporality(_ sdkmetric.InstrumentKind) metricdata.Temporality {
	return metricdata.CumulativeTemporality
}

func (n *noopExporter) Aggregation(_ sdkmetric.InstrumentKind) sdkmetric.Aggregation {
	return sdkmetric.AggregationDefault{}
}

func (n *noopExporter) Export(_ context.Context, _ *metricdata.ResourceMetrics) error { return nil }

func (n *noopExporter) ForceFlush(_ context.Context) error { return nil }

func (n *noopExporter) Shutdown(_ context.Context) error { return nil }

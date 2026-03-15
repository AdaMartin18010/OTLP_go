package types

import (
	"encoding/json"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestSpan(t *testing.T) {
	t.Run("IsRoot", func(t *testing.T) {
		root := &Span{SpanID: NewSpanID()}
		assert.True(t, root.IsRoot())

		child := &Span{SpanID: NewSpanID(), ParentSpanID: NewSpanID()}
		assert.False(t, child.IsRoot())
	})

	t.Run("IsEnded", func(t *testing.T) {
		active := &Span{StartTime: Now()}
		assert.False(t, active.IsEnded())

		ended := &Span{StartTime: Now(), EndTime: Now()}
		assert.True(t, ended.IsEnded())
	})

	t.Run("Duration", func(t *testing.T) {
		start := Now()
		end := start.Add(time.Second)

		span := &Span{StartTime: start, EndTime: end}
		assert.Equal(t, time.Second, span.Duration().Duration)

		active := &Span{StartTime: start}
		assert.Equal(t, time.Duration(0), active.Duration().Duration)
	})

	t.Run("End", func(t *testing.T) {
		start := Now()
		end := start.Add(time.Second)

		span := &Span{StartTime: start}
		span.End(end)

		assert.Equal(t, end, span.EndTime)
	})

	t.Run("EndNow", func(t *testing.T) {
		before := time.Now().UTC()
		span := &Span{StartTime: Now()}
		span.EndNow()
		after := time.Now().UTC()

		assert.False(t, span.EndTime.IsZero())
		assert.True(t, span.EndTime.Time.After(before) || span.EndTime.Time.Equal(before))
		assert.True(t, span.EndTime.Time.Before(after) || span.EndTime.Time.Equal(after))
	})

	t.Run("AddEvent", func(t *testing.T) {
		span := &Span{}
		span.AddEvent("test-event", Now(), NewAttribute("key", "value"))

		require.Len(t, span.Events, 1)
		assert.Equal(t, "test-event", span.Events[0].Name)
		assert.Equal(t, "value", span.Events[0].Attributes.StringValue("key"))
	})

	t.Run("AddLink", func(t *testing.T) {
		span := &Span{}
		traceID := NewTraceID()
		spanID := NewSpanID()

		span.AddLink(traceID, spanID, NewAttribute("key", "value"))

		require.Len(t, span.Links, 1)
		assert.Equal(t, traceID, span.Links[0].TraceID)
		assert.Equal(t, spanID, span.Links[0].SpanID)
		assert.Equal(t, "value", span.Links[0].Attributes.StringValue("key"))
	})

	t.Run("SetStatus", func(t *testing.T) {
		span := &Span{}
		span.SetStatus(StatusError, "something went wrong")

		assert.Equal(t, StatusError, span.Status.Code)
		assert.Equal(t, "something went wrong", span.Status.Description)
	})

	t.Run("SetError", func(t *testing.T) {
		span := &Span{}
		span.SetError("error occurred")

		assert.Equal(t, StatusError, span.Status.Code)
		assert.Equal(t, "error occurred", span.Status.Description)
	})
}

func TestSpanClone(t *testing.T) {
	original := &Span{
		TraceID:               NewTraceID(),
		SpanID:                NewSpanID(),
		ParentSpanID:          NewSpanID(),
		TraceState:            "vendor=value",
		Flags:                 FlagSampled,
		Name:                  "test-span",
		Kind:                  SpanKindServer,
		StartTime:             Now(),
		EndTime:               Now(),
		Attributes:            NewAttributes("key", "value"),
		DroppedAttributeCount: 1,
		Events: []Event{
			{Name: "event1", Timestamp: Now()},
		},
		DroppedEventCount: 2,
		Links: []Link{
			{TraceID: NewTraceID(), SpanID: NewSpanID()},
		},
		DroppedLinkCount:     3,
		Status:               Status{Code: StatusOK, Description: "ok"},
		Resource:             NewResource(NewAttribute("r", "v")),
		InstrumentationScope: InstrumentationScope{Name: "test", Version: "1.0"},
	}

	cloned := original.Clone()

	assert.Equal(t, original.TraceID, cloned.TraceID)
	assert.Equal(t, original.SpanID, cloned.SpanID)
	assert.Equal(t, original.Name, cloned.Name)
	assert.Equal(t, original.Attributes.StringValue("key"), cloned.Attributes.StringValue("key"))
	assert.Equal(t, len(original.Events), len(cloned.Events))
	assert.Equal(t, len(original.Links), len(cloned.Links))
	assert.Equal(t, original.Status.Code, cloned.Status.Code)
	assert.Equal(t, original.Resource.GetString("r"), cloned.Resource.GetString("r"))
	assert.Equal(t, original.InstrumentationScope.Name, cloned.InstrumentationScope.Name)
}

func TestSpanCloneNil(t *testing.T) {
	var span *Span
	cloned := span.Clone()
	assert.Nil(t, cloned)
}

func TestSpanJSON(t *testing.T) {
	traceID := TraceID{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}
	spanID := SpanID{1, 2, 3, 4, 5, 6, 7, 8}

	span := &Span{
		TraceID:   traceID,
		SpanID:    spanID,
		Name:      "test",
		Kind:      SpanKindServer,
		StartTime: Now(),
	}

	data, err := json.Marshal(span)
	require.NoError(t, err)

	var m map[string]any
	err = json.Unmarshal(data, &m)
	require.NoError(t, err)

	assert.Equal(t, traceID.String(), m["trace_id"])
	assert.Equal(t, spanID.String(), m["span_id"])
	assert.Equal(t, "test", m["name"])
	assert.Equal(t, float64(SpanKindServer), m["kind"])
}

func TestStatus(t *testing.T) {
	t.Run("IsError", func(t *testing.T) {
		assert.True(t, Status{Code: StatusError}.IsError())
		assert.False(t, Status{Code: StatusOK}.IsError())
		assert.False(t, Status{Code: StatusUnset}.IsError())
	})

	t.Run("IsOK", func(t *testing.T) {
		assert.True(t, Status{Code: StatusOK}.IsOK())
		assert.False(t, Status{Code: StatusError}.IsOK())
		assert.False(t, Status{Code: StatusUnset}.IsOK())
	})

	t.Run("IsUnset", func(t *testing.T) {
		assert.True(t, Status{Code: StatusUnset}.IsUnset())
		assert.False(t, Status{Code: StatusOK}.IsUnset())
		assert.False(t, Status{Code: StatusError}.IsUnset())
	})
}

func TestInstrumentationScope(t *testing.T) {
	t.Run("String with version", func(t *testing.T) {
		scope := InstrumentationScope{Name: "test-lib", Version: "1.0.0"}
		assert.Equal(t, "test-lib@1.0.0", scope.String())
	})

	t.Run("String without version", func(t *testing.T) {
		scope := InstrumentationScope{Name: "test-lib"}
		assert.Equal(t, "test-lib", scope.String())
	})

	t.Run("IsEmpty", func(t *testing.T) {
		assert.True(t, InstrumentationScope{}.IsEmpty())
		assert.False(t, InstrumentationScope{Name: "test"}.IsEmpty())
	})
}

func TestLogRecord(t *testing.T) {
	t.Run("NewLogRecord", func(t *testing.T) {
		log := NewLogRecord(LogLevelInfo, "test message")

		assert.Equal(t, LogLevelInfo, log.Severity)
		assert.Equal(t, "INFO", log.SeverityText)
		assert.Equal(t, "test message", log.Body.AsString())
		assert.False(t, log.Timestamp.IsZero())
		assert.False(t, log.ObservedTimestamp.IsZero())
	})

	t.Run("SetTraceContext", func(t *testing.T) {
		log := NewLogRecord(LogLevelInfo, "message")
		traceID := NewTraceID()
		spanID := NewSpanID()

		log.SetTraceContext(traceID, spanID, FlagSampled)

		assert.Equal(t, traceID, log.TraceID)
		assert.Equal(t, spanID, log.SpanID)
		assert.Equal(t, FlagSampled, log.TraceFlags)
	})

	t.Run("String", func(t *testing.T) {
		log := NewLogRecord(LogLevelInfo, "test message")
		assert.Equal(t, "test message", log.String())
	})
}

func TestMetricType(t *testing.T) {
	assert.Equal(t, "Gauge", MetricTypeGauge.String())
	assert.Equal(t, "Sum", MetricTypeSum.String())
	assert.Equal(t, "Histogram", MetricTypeHistogram.String())
	assert.Equal(t, "Summary", MetricTypeSummary.String())
	assert.Equal(t, "ExponentialHistogram", MetricTypeExponentialHistogram.String())
	assert.Equal(t, "MetricType(99)", MetricType(99).String())
}

func TestAggregationTemporality(t *testing.T) {
	assert.Equal(t, AggregationTemporality(0), AggregationTemporalityUnspecified)
	assert.Equal(t, AggregationTemporality(1), AggregationTemporalityDelta)
	assert.Equal(t, AggregationTemporality(2), AggregationTemporalityCumulative)
}

func TestExemplar(t *testing.T) {
	exemplar := Exemplar{
		Time:               Now(),
		Value:              IntValue(42),
		TraceID:            NewTraceID(),
		SpanID:             NewSpanID(),
		FilteredAttributes: NewAttributes("key", "value"),
	}

	assert.Equal(t, int64(42), exemplar.Value.AsInt())
	assert.True(t, exemplar.TraceID.IsValid())
	assert.True(t, exemplar.SpanID.IsValid())
}

func TestTracesData(t *testing.T) {
	traces := &TracesData{
		ResourceSpans: []ResourceSpans{
			{
				Resource: NewResource(NewAttribute("service.name", "test")),
				ScopeSpans: []ScopeSpans{
					{
						Scope: InstrumentationScope{Name: "test-lib"},
						Spans: []Span{
							{
								TraceID: NewTraceID(),
								SpanID:  NewSpanID(),
								Name:    "test-span",
							},
						},
					},
				},
			},
		},
	}

	assert.Len(t, traces.ResourceSpans, 1)
	assert.Equal(t, "test", traces.ResourceSpans[0].Resource.GetString("service.name"))
	assert.Len(t, traces.ResourceSpans[0].ScopeSpans, 1)
	assert.Len(t, traces.ResourceSpans[0].ScopeSpans[0].Spans, 1)
	assert.Equal(t, "test-span", traces.ResourceSpans[0].ScopeSpans[0].Spans[0].Name)
}

func TestMetricsData(t *testing.T) {
	metrics := &MetricsData{
		ResourceMetrics: []ResourceMetrics{
			{
				Resource: NewResource(NewAttribute("service.name", "test")),
				ScopeMetrics: []ScopeMetrics{
					{
						Scope: InstrumentationScope{Name: "test-lib"},
						Metrics: []Metric{
							{
								Name:        "test-metric",
								Type:        MetricTypeGauge,
								Description: "A test metric",
								Unit:        "bytes",
							},
						},
					},
				},
			},
		},
	}

	assert.Len(t, metrics.ResourceMetrics, 1)
	assert.Len(t, metrics.ResourceMetrics[0].ScopeMetrics, 1)
	assert.Len(t, metrics.ResourceMetrics[0].ScopeMetrics[0].Metrics, 1)
	assert.Equal(t, "test-metric", metrics.ResourceMetrics[0].ScopeMetrics[0].Metrics[0].Name)
}

func TestLogsData(t *testing.T) {
	logs := &LogsData{
		ResourceLogs: []ResourceLogs{
			{
				Resource: NewResource(NewAttribute("service.name", "test")),
				ScopeLogs: []ScopeLogs{
					{
						Scope: InstrumentationScope{Name: "test-lib"},
						LogRecords: []LogRecord{
							*NewLogRecord(LogLevelInfo, "test log"),
						},
					},
				},
			},
		},
	}

	assert.Len(t, logs.ResourceLogs, 1)
	assert.Len(t, logs.ResourceLogs[0].ScopeLogs, 1)
	assert.Len(t, logs.ResourceLogs[0].ScopeLogs[0].LogRecords, 1)
	assert.Equal(t, "test log", logs.ResourceLogs[0].ScopeLogs[0].LogRecords[0].Body.AsString())
}

func TestTelemetryBatch(t *testing.T) {
	t.Run("NewTelemetryBatch", func(t *testing.T) {
		batch := NewTelemetryBatch()
		assert.NotNil(t, batch)
		assert.Empty(t, batch.Spans)
		assert.Empty(t, batch.Logs)
		assert.Empty(t, batch.Metrics)
	})

	t.Run("AddSpan", func(t *testing.T) {
		batch := NewTelemetryBatch()
		span := &Span{Name: "test"}

		batch.AddSpan(span)

		assert.Equal(t, 1, batch.SpanCount())
	})

	t.Run("AddSpan nil", func(t *testing.T) {
		batch := NewTelemetryBatch()
		batch.AddSpan(nil)
		assert.Equal(t, 0, batch.SpanCount())
	})

	t.Run("AddLog", func(t *testing.T) {
		batch := NewTelemetryBatch()
		log := NewLogRecord(LogLevelInfo, "test")

		batch.AddLog(log)

		assert.Equal(t, 1, batch.LogCount())
	})

	t.Run("AddLog nil", func(t *testing.T) {
		batch := NewTelemetryBatch()
		batch.AddLog(nil)
		assert.Equal(t, 0, batch.LogCount())
	})

	t.Run("AddMetric", func(t *testing.T) {
		batch := NewTelemetryBatch()
		metric := &Metric{Name: "test"}

		batch.AddMetric(metric)

		assert.Equal(t, 1, batch.MetricCount())
	})

	t.Run("AddMetric nil", func(t *testing.T) {
		batch := NewTelemetryBatch()
		batch.AddMetric(nil)
		assert.Equal(t, 0, batch.MetricCount())
	})

	t.Run("IsEmpty", func(t *testing.T) {
		batch := NewTelemetryBatch()
		assert.True(t, batch.IsEmpty())

		batch.AddSpan(&Span{})
		assert.False(t, batch.IsEmpty())
	})

	t.Run("IsEmpty nil", func(t *testing.T) {
		var batch *TelemetryBatch
		assert.True(t, batch.IsEmpty())
	})

	t.Run("Clear", func(t *testing.T) {
		batch := NewTelemetryBatch()
		batch.AddSpan(&Span{})
		batch.AddLog(NewLogRecord(LogLevelInfo, "test"))
		batch.AddMetric(&Metric{})

		batch.Clear()

		assert.True(t, batch.IsEmpty())
	})

	t.Run("Clear nil", func(t *testing.T) {
		var batch *TelemetryBatch
		batch.Clear() // Should not panic
	})

	t.Run("Count methods with nil", func(t *testing.T) {
		var batch *TelemetryBatch
		assert.Equal(t, 0, batch.SpanCount())
		assert.Equal(t, 0, batch.LogCount())
		assert.Equal(t, 0, batch.MetricCount())
	})
}

func TestTelemetryBatchToTracesData(t *testing.T) {
	t.Run("Empty batch", func(t *testing.T) {
		batch := NewTelemetryBatch()
		traces := batch.ToTracesData()

		assert.NotNil(t, traces)
		assert.Empty(t, traces.ResourceSpans)
	})

	t.Run("Nil batch", func(t *testing.T) {
		var batch *TelemetryBatch
		traces := batch.ToTracesData()

		assert.NotNil(t, traces)
		assert.Empty(t, traces.ResourceSpans)
	})

	t.Run("Spans grouped by resource", func(t *testing.T) {
		batch := NewTelemetryBatch()

		resource1 := NewResource(NewAttribute("service.name", "service1"))
		resource2 := NewResource(NewAttribute("service.name", "service2"))

		batch.AddSpan(&Span{
			TraceID:              NewTraceID(),
			SpanID:               NewSpanID(),
			Name:                 "span1",
			Resource:             resource1,
			InstrumentationScope: InstrumentationScope{Name: "lib1"},
		})
		batch.AddSpan(&Span{
			TraceID:              NewTraceID(),
			SpanID:               NewSpanID(),
			Name:                 "span2",
			Resource:             resource1,
			InstrumentationScope: InstrumentationScope{Name: "lib1"},
		})
		batch.AddSpan(&Span{
			TraceID:              NewTraceID(),
			SpanID:               NewSpanID(),
			Name:                 "span3",
			Resource:             resource2,
			InstrumentationScope: InstrumentationScope{Name: "lib2"},
		})

		traces := batch.ToTracesData()

		assert.Len(t, traces.ResourceSpans, 2)

		// Find service1 spans
		var service1Spans, service2Spans []Span
		for _, rs := range traces.ResourceSpans {
			if rs.Resource.GetString("service.name") == "service1" {
				for _, ss := range rs.ScopeSpans {
					service1Spans = append(service1Spans, ss.Spans...)
				}
			}
			if rs.Resource.GetString("service.name") == "service2" {
				for _, ss := range rs.ScopeSpans {
					service2Spans = append(service2Spans, ss.Spans...)
				}
			}
		}

		assert.Len(t, service1Spans, 2)
		assert.Len(t, service2Spans, 1)
	})
}

func TestHistogramDataPoint(t *testing.T) {
	sum := 100.0
	min := 10.0
	max := 90.0

	dp := HistogramDataPoint{
		Attributes:     NewAttributes("key", "value"),
		StartTime:      Now(),
		Time:           Now(),
		Count:          10,
		Sum:            &sum,
		BucketCounts:   []uint64{1, 2, 3, 4},
		ExplicitBounds: []float64{10, 20, 30},
		Min:            &min,
		Max:            &max,
		Exemplars:      []Exemplar{{Value: IntValue(42)}},
	}

	assert.Equal(t, uint64(10), dp.Count)
	assert.Equal(t, 100.0, *dp.Sum)
	assert.Equal(t, 10.0, *dp.Min)
	assert.Equal(t, 90.0, *dp.Max)
}

func TestNumberDataPoint(t *testing.T) {
	dp := NumberDataPoint{
		Attributes: NewAttributes("metric", "value"),
		StartTime:  Now(),
		Time:       Now(),
		Value:      IntValue(42),
		Exemplars:  []Exemplar{{Value: IntValue(42)}},
	}

	assert.Equal(t, int64(42), dp.Value.AsInt())
}

func TestSumDataPoint(t *testing.T) {
	dp := SumDataPoint{
		NumberDataPoint: NumberDataPoint{
			Value: IntValue(100),
		},
		IsMonotonic:            true,
		AggregationTemporality: AggregationTemporalityCumulative,
	}

	assert.Equal(t, int64(100), dp.Value.AsInt())
	assert.True(t, dp.IsMonotonic)
	assert.Equal(t, AggregationTemporalityCumulative, dp.AggregationTemporality)
}

func TestMetricData(t *testing.T) {
	data := MetricData{
		GaugePoints: []NumberDataPoint{
			{Value: IntValue(42)},
		},
		SumPoints: []SumDataPoint{
			{IsMonotonic: true},
		},
		HistogramPoints: []HistogramDataPoint{
			{Count: 10},
		},
	}

	assert.Len(t, data.GaugePoints, 1)
	assert.Len(t, data.SumPoints, 1)
	assert.Len(t, data.HistogramPoints, 1)
}

func TestScopeSpans(t *testing.T) {
	ss := ScopeSpans{
		Scope:     InstrumentationScope{Name: "test-lib"},
		Spans:     []Span{{Name: "span1"}, {Name: "span2"}},
		SchemaURL: "https://opentelemetry.io/schemas/1.0.0",
	}

	assert.Equal(t, "test-lib", ss.Scope.Name)
	assert.Len(t, ss.Spans, 2)
	assert.Equal(t, "https://opentelemetry.io/schemas/1.0.0", ss.SchemaURL)
}

func TestScopeMetrics(t *testing.T) {
	sm := ScopeMetrics{
		Scope:     InstrumentationScope{Name: "test-lib"},
		Metrics:   []Metric{{Name: "metric1"}, {Name: "metric2"}},
		SchemaURL: "https://opentelemetry.io/schemas/1.0.0",
	}

	assert.Equal(t, "test-lib", sm.Scope.Name)
	assert.Len(t, sm.Metrics, 2)
}

func TestScopeLogs(t *testing.T) {
	sl := ScopeLogs{
		Scope:      InstrumentationScope{Name: "test-lib"},
		LogRecords: []LogRecord{*NewLogRecord(LogLevelInfo, "log1")},
		SchemaURL:  "https://opentelemetry.io/schemas/1.0.0",
	}

	assert.Equal(t, "test-lib", sl.Scope.Name)
	assert.Len(t, sl.LogRecords, 1)
}

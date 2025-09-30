package main

import (
	"context"
	"encoding/json"
	"net/http"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/attribute"
	metricapi "go.opentelemetry.io/otel/metric"
	"go.opentelemetry.io/otel/trace"
)

type task struct {
	ID   string `json:"id"`
	Body string `json:"body"`
}

type pipeline struct {
	in          chan task
	queueGauge  metricapi.Int64UpDownCounter
	latencyHist metricapi.Float64Histogram
	dropCounter metricapi.Int64Counter
}

func newPipeline(buffer int, workers int) *pipeline {
	m := otel.Meter("demo/pipeline")
	queueGauge, _ := m.Int64UpDownCounter("pipeline.queue.length")
	latencyHist, _ := m.Float64Histogram("pipeline.task.latency")
	dropCounter, _ := m.Int64Counter("pipeline.queue.drop")

	p := &pipeline{
		in:          make(chan task, buffer),
		queueGauge:  queueGauge,
		latencyHist: latencyHist,
		dropCounter: dropCounter,
	}

	// start workers
	for i := 0; i < workers; i++ {
		go p.worker(i)
	}
	return p
}

func (p *pipeline) enqueue(ctx context.Context, t task) bool {
	select {
	case p.in <- t:
		p.queueGauge.Add(context.Background(), 1)
		return true
	case <-ctx.Done():
		p.dropCounter.Add(context.Background(), 1, metricapi.WithAttributes(attribute.String("reason", "enqueue_ctx_cancel")))
		return false
	}
}

func (p *pipeline) worker(id int) {
	tr := otel.Tracer("demo/pipeline")
	for t := range p.in {
		start := time.Now()
		ctx, span := tr.Start(context.Background(), "pipeline.process")
		span.SetAttributes(attribute.String("worker.id", time.Now().Format("150405")))

		// simulate processing
		time.Sleep(50 * time.Millisecond)

		// record metrics and events
		p.queueGauge.Add(context.Background(), -1)
		p.latencyHist.Record(context.Background(), time.Since(start).Seconds(), metricapi.WithAttributes(attribute.String("stage", "process")))
		span.AddEvent("processed", trace.WithAttributes(attribute.String("task.id", t.ID)))
		span.End()
		_ = ctx
	}
}

func (p *pipeline) httpEnqueueHandler() http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		ctx, cancel := context.WithTimeout(r.Context(), 200*time.Millisecond)
		defer cancel()

		var t task
		if err := json.NewDecoder(r.Body).Decode(&t); err != nil {
			w.WriteHeader(http.StatusBadRequest)
			_, _ = w.Write([]byte("invalid json"))
			return
		}
		if t.ID == "" {
			t.ID = time.Now().Format(time.RFC3339Nano)
		}

		ok := p.enqueue(ctx, t)
		if !ok {
			w.WriteHeader(http.StatusTooManyRequests)
			_, _ = w.Write([]byte("queue full or canceled"))
			return
		}
		w.WriteHeader(http.StatusAccepted)
		_, _ = w.Write([]byte("enqueued"))
	}
}

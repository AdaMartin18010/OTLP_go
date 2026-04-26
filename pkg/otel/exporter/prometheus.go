package exporter

import (
	"context"
	"fmt"
	"math"
	"net/http"
	"sort"
	"strings"
	"sync"

	"go.opentelemetry.io/otel/attribute"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
	"go.opentelemetry.io/otel/sdk/metric/metricdata"
	"go.opentelemetry.io/otel/sdk/resource"
)

// PrometheusExporter is a Prometheus-compatible metrics exporter.
// It uses a ManualReader to collect metrics from the OpenTelemetry SDK
// and serves them in Prometheus text format via HTTP.
type PrometheusExporter struct {
	mu     sync.RWMutex
	reader *sdkmetric.ManualReader

	// resourceAttrs are cached resource attributes for target_info.
	resourceAttrs map[string]string
}

// NewPrometheusExporter creates a new Prometheus exporter.
func NewPrometheusExporter() *PrometheusExporter {
	return &PrometheusExporter{
		reader:        sdkmetric.NewManualReader(),
		resourceAttrs: make(map[string]string),
	}
}

// Reader returns the SDK metric reader that should be registered with MeterProvider.
func (p *PrometheusExporter) Reader() sdkmetric.Reader {
	return p.reader
}

// SetResourceAttributes sets the resource attributes for target_info.
func (p *PrometheusExporter) SetResourceAttributes(attrs map[string]string) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.resourceAttrs = attrs
}

// ServeHTTP implements http.Handler for the /metrics endpoint.
func (p *PrometheusExporter) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	var rm metricdata.ResourceMetrics
	if err := p.reader.Collect(ctx, &rm); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "text/plain; charset=utf-8")

	var b strings.Builder
	p.writeResourceMetrics(&b, rm)

	w.Write([]byte(b.String()))
}

// CollectAndFormat collects metrics and returns them as Prometheus text format.
func (p *PrometheusExporter) CollectAndFormat(ctx context.Context) (string, error) {
	var rm metricdata.ResourceMetrics
	if err := p.reader.Collect(ctx, &rm); err != nil {
		return "", err
	}

	var b strings.Builder
	p.writeResourceMetrics(&b, rm)
	return b.String(), nil
}

func (p *PrometheusExporter) writeResourceMetrics(b *strings.Builder, rm metricdata.ResourceMetrics) {
	// Extract resource attributes
	resourceAttrs := p.extractResourceAttributes(rm.Resource)
	p.mu.RLock()
	cachedAttrs := p.resourceAttrs
	p.mu.RUnlock()
	for k, v := range cachedAttrs {
		if _, exists := resourceAttrs[k]; !exists {
			resourceAttrs[k] = v
		}
	}

	// Write target_info if we have resource attributes
	if len(resourceAttrs) > 0 {
		writeTargetInfo(b, resourceAttrs)
	}

	// Write scope metrics
	for _, sm := range rm.ScopeMetrics {
		scopeAttrs := map[string]string{
			"otel_scope_name":    sm.Scope.Name,
			"otel_scope_version": sm.Scope.Version,
		}
		for _, attr := range sm.Scope.Attributes.ToSlice() {
			scopeAttrs[sanitizeLabelName(string(attr.Key))] = attr.Value.Emit()
		}
		writeScopeInfo(b, scopeAttrs)

		for _, m := range sm.Metrics {
			p.writeMetric(b, m, scopeAttrs)
		}
	}
}

func (p *PrometheusExporter) extractResourceAttributes(res *resource.Resource) map[string]string {
	attrs := make(map[string]string)
	if res == nil {
		return attrs
	}
	for _, attr := range res.Attributes() {
		attrs[sanitizeLabelName(string(attr.Key))] = attr.Value.Emit()
	}
	return attrs
}

func writeTargetInfo(b *strings.Builder, attrs map[string]string) {
	b.WriteString("# HELP target_info Target metadata\n")
	b.WriteString("# TYPE target_info gauge\n")
	b.WriteString("target_info")
	writeLabels(b, attrs)
	b.WriteString(" 1\n\n")
}

func writeScopeInfo(b *strings.Builder, attrs map[string]string) {
	b.WriteString("# HELP otel_scope_info Instrumentation Scope metadata\n")
	b.WriteString("# TYPE otel_scope_info gauge\n")
	b.WriteString("otel_scope_info")
	writeLabels(b, attrs)
	b.WriteString(" 1\n\n")
}

func (p *PrometheusExporter) writeMetric(b *strings.Builder, m metricdata.Metrics, scopeAttrs map[string]string) {
	name := sanitizeMetricName(m.Name)
	desc := m.Description
	if desc == "" {
		desc = m.Name
	}

	switch data := m.Data.(type) {
	case metricdata.Gauge[int64]:
		writeGaugeInt64(b, name, desc, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.Gauge[float64]:
		writeGaugeFloat64(b, name, desc, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.Sum[int64]:
		metricType := "counter"
		if !data.IsMonotonic {
			metricType = "gauge"
		}
		writeSumInt64(b, name, desc, metricType, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.Sum[float64]:
		metricType := "counter"
		if !data.IsMonotonic {
			metricType = "gauge"
		}
		writeSumFloat64(b, name, desc, metricType, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.Histogram[int64]:
		writeHistogramInt64(b, name, desc, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.Histogram[float64]:
		writeHistogramFloat64(b, name, desc, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.ExponentialHistogram[int64]:
		writeExponentialHistogramInt64(b, name, desc, data.DataPoints, scopeAttrs, p.attributesToMap)
	case metricdata.ExponentialHistogram[float64]:
		writeExponentialHistogramFloat64(b, name, desc, data.DataPoints, scopeAttrs, p.attributesToMap)
	}
}

func writeGaugeInt64(
	b *strings.Builder,
	name, desc string,
	points []metricdata.DataPoint[int64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s gauge\n", name))
	for _, dp := range points {
		b.WriteString(name)
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatInt64(dp.Value))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeGaugeFloat64(
	b *strings.Builder,
	name, desc string,
	points []metricdata.DataPoint[float64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s gauge\n", name))
	for _, dp := range points {
		b.WriteString(name)
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatFloat64(dp.Value))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeSumInt64(
	b *strings.Builder,
	name, desc, metricType string,
	points []metricdata.DataPoint[int64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s %s\n", name, metricType))
	for _, dp := range points {
		b.WriteString(name)
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatInt64(dp.Value))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeSumFloat64(
	b *strings.Builder,
	name, desc, metricType string,
	points []metricdata.DataPoint[float64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s %s\n", name, metricType))
	for _, dp := range points {
		b.WriteString(name)
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatFloat64(dp.Value))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeHistogramInt64(
	b *strings.Builder,
	name, desc string,
	points []metricdata.HistogramDataPoint[int64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s histogram\n", name))
	for _, dp := range points {
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)

		// Write bucket counts
		for i, bound := range dp.Bounds {
			b.WriteString(name + "_bucket")
			bucketAttrs := cloneMap(attrs)
			bucketAttrs["le"] = formatFloat64(bound)
			writeLabels(b, bucketAttrs)
			b.WriteString(" ")
			b.WriteString(fmt.Sprintf("%d", dp.BucketCounts[i]))
			b.WriteString("\n")
		}
		// +Inf bucket
		b.WriteString(name + "_bucket")
		infAttrs := cloneMap(attrs)
		infAttrs["le"] = "+Inf"
		writeLabels(b, infAttrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")

		// sum
		b.WriteString(name + "_sum")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatFloat64(float64(dp.Sum)))
		b.WriteString("\n")

		// count
		b.WriteString(name + "_count")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeHistogramFloat64(
	b *strings.Builder,
	name, desc string,
	points []metricdata.HistogramDataPoint[float64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s histogram\n", name))
	for _, dp := range points {
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)

		// Write bucket counts
		for i, bound := range dp.Bounds {
			b.WriteString(name + "_bucket")
			bucketAttrs := cloneMap(attrs)
			bucketAttrs["le"] = formatFloat64(bound)
			writeLabels(b, bucketAttrs)
			b.WriteString(" ")
			b.WriteString(fmt.Sprintf("%d", dp.BucketCounts[i]))
			b.WriteString("\n")
		}
		// +Inf bucket
		b.WriteString(name + "_bucket")
		infAttrs := cloneMap(attrs)
		infAttrs["le"] = "+Inf"
		writeLabels(b, infAttrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")

		// sum
		b.WriteString(name + "_sum")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatFloat64(float64(dp.Sum)))
		b.WriteString("\n")

		// count
		b.WriteString(name + "_count")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeExponentialHistogramInt64(
	b *strings.Builder,
	name, desc string,
	points []metricdata.ExponentialHistogramDataPoint[int64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s histogram\n", name))
	for _, dp := range points {
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)

		boundaries, counts := exponentialToExplicitBucketsInt64(dp)

		for i, bound := range boundaries {
			b.WriteString(name + "_bucket")
			bucketAttrs := cloneMap(attrs)
			bucketAttrs["le"] = formatFloat64(bound)
			writeLabels(b, bucketAttrs)
			b.WriteString(" ")
			b.WriteString(fmt.Sprintf("%d", counts[i]))
			b.WriteString("\n")
		}
		b.WriteString(name + "_bucket")
		infAttrs := cloneMap(attrs)
		infAttrs["le"] = "+Inf"
		writeLabels(b, infAttrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")

		b.WriteString(name + "_sum")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatFloat64(float64(dp.Sum)))
		b.WriteString("\n")

		b.WriteString(name + "_count")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func writeExponentialHistogramFloat64(
	b *strings.Builder,
	name, desc string,
	points []metricdata.ExponentialHistogramDataPoint[float64],
	scopeAttrs map[string]string,
	attrsFn func(attribute.Set) map[string]string,
) {
	b.WriteString(fmt.Sprintf("# HELP %s %s\n", name, desc))
	b.WriteString(fmt.Sprintf("# TYPE %s histogram\n", name))
	for _, dp := range points {
		attrs := attrsFn(dp.Attributes)
		mergeMaps(attrs, scopeAttrs)

		boundaries, counts := exponentialToExplicitBucketsFloat64(dp)

		for i, bound := range boundaries {
			b.WriteString(name + "_bucket")
			bucketAttrs := cloneMap(attrs)
			bucketAttrs["le"] = formatFloat64(bound)
			writeLabels(b, bucketAttrs)
			b.WriteString(" ")
			b.WriteString(fmt.Sprintf("%d", counts[i]))
			b.WriteString("\n")
		}
		b.WriteString(name + "_bucket")
		infAttrs := cloneMap(attrs)
		infAttrs["le"] = "+Inf"
		writeLabels(b, infAttrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")

		b.WriteString(name + "_sum")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(formatFloat64(dp.Sum))
		b.WriteString("\n")

		b.WriteString(name + "_count")
		writeLabels(b, attrs)
		b.WriteString(" ")
		b.WriteString(fmt.Sprintf("%d", dp.Count))
		b.WriteString("\n")
	}
	b.WriteString("\n")
}

func exponentialToExplicitBucketsInt64(
	dp metricdata.ExponentialHistogramDataPoint[int64],
) ([]float64, []uint64) {
	scale := dp.Scale
	base := math.Pow(2, math.Pow(2, float64(-scale)))

	var boundaries []float64
	var counts []uint64
	var cumulative uint64

	negBucket := dp.NegativeBucket
	for i := len(negBucket.Counts) - 1; i >= 0; i-- {
		idx := negBucket.Offset + int32(i)
		boundary := -math.Pow(base, float64(idx))
		cumulative += negBucket.Counts[i]
		boundaries = append(boundaries, boundary)
		counts = append(counts, cumulative)
	}

	if dp.ZeroCount > 0 {
		cumulative += dp.ZeroCount
		boundaries = append(boundaries, 0)
		counts = append(counts, cumulative)
	}

	posBucket := dp.PositiveBucket
	for i := 0; i < len(posBucket.Counts); i++ {
		idx := posBucket.Offset + int32(i)
		boundary := math.Pow(base, float64(idx+1))
		cumulative += posBucket.Counts[i]
		boundaries = append(boundaries, boundary)
		counts = append(counts, cumulative)
	}

	return boundaries, counts
}

func exponentialToExplicitBucketsFloat64(
	dp metricdata.ExponentialHistogramDataPoint[float64],
) ([]float64, []uint64) {
	scale := dp.Scale
	base := math.Pow(2, math.Pow(2, float64(-scale)))

	var boundaries []float64
	var counts []uint64
	var cumulative uint64

	negBucket := dp.NegativeBucket
	for i := len(negBucket.Counts) - 1; i >= 0; i-- {
		idx := negBucket.Offset + int32(i)
		boundary := -math.Pow(base, float64(idx))
		cumulative += negBucket.Counts[i]
		boundaries = append(boundaries, boundary)
		counts = append(counts, cumulative)
	}

	if dp.ZeroCount > 0 {
		cumulative += dp.ZeroCount
		boundaries = append(boundaries, 0)
		counts = append(counts, cumulative)
	}

	posBucket := dp.PositiveBucket
	for i := 0; i < len(posBucket.Counts); i++ {
		idx := posBucket.Offset + int32(i)
		boundary := math.Pow(base, float64(idx+1))
		cumulative += posBucket.Counts[i]
		boundaries = append(boundaries, boundary)
		counts = append(counts, cumulative)
	}

	return boundaries, counts
}

func (p *PrometheusExporter) attributesToMap(set attribute.Set) map[string]string {
	result := make(map[string]string)
	for _, kv := range set.ToSlice() {
		result[sanitizeLabelName(string(kv.Key))] = kv.Value.Emit()
	}
	return result
}

func writeLabels(b *strings.Builder, attrs map[string]string) {
	if len(attrs) == 0 {
		return
	}

	keys := make([]string, 0, len(attrs))
	for k := range attrs {
		keys = append(keys, k)
	}
	sort.Strings(keys)

	b.WriteString("{")
	for i, k := range keys {
		if i > 0 {
			b.WriteString(",")
		}
		b.WriteString(k)
		b.WriteString("=")
		b.WriteString(fmt.Sprintf("%q", attrs[k]))
	}
	b.WriteString("}")
}

func sanitizeMetricName(name string) string {
	// Replace dots and dashes with underscores
	name = strings.ReplaceAll(name, ".", "_")
	name = strings.ReplaceAll(name, "-", "_")
	name = strings.ReplaceAll(name, "/", "_")
	name = strings.ReplaceAll(name, ":", "_")
	return name
}

func sanitizeLabelName(name string) string {
	name = strings.ReplaceAll(name, ".", "_")
	name = strings.ReplaceAll(name, "-", "_")
	name = strings.ReplaceAll(name, "/", "_")
	name = strings.ReplaceAll(name, ":", "_")
	return name
}

func formatInt64(v int64) string {
	return fmt.Sprintf("%d", v)
}

func formatFloat64(v float64) string {
	if math.IsInf(v, 1) {
		return "+Inf"
	}
	if math.IsInf(v, -1) {
		return "-Inf"
	}
	if math.IsNaN(v) {
		return "NaN"
	}
	return fmt.Sprintf("%g", v)
}

func mergeMaps(dst, src map[string]string) {
	for k, v := range src {
		if _, exists := dst[k]; !exists {
			dst[k] = v
		}
	}
}

func cloneMap(m map[string]string) map[string]string {
	result := make(map[string]string, len(m))
	for k, v := range m {
		result[k] = v
	}
	return result
}

// Handler returns an http.Handler for the /metrics endpoint.
func (p *PrometheusExporter) Handler() http.Handler {
	return http.HandlerFunc(p.ServeHTTP)
}

// Shutdown shuts down the exporter.
func (p *PrometheusExporter) Shutdown(ctx context.Context) error {
	return p.reader.Shutdown(ctx)
}

// ForceFlush forces a flush of the exporter.
func (p *PrometheusExporter) ForceFlush(ctx context.Context) error {
	// ManualReader does not support ForceFlush in this version.
	_ = ctx
	return nil
}

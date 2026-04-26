package exporter

import (
	"context"
	"math"
	"net/http"
	"net/http/httptest"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/sdk/metric/metricdata"
	"go.opentelemetry.io/otel/sdk/resource"
)

func TestNewPrometheusExporter(t *testing.T) {
	exp := NewPrometheusExporter()
	require.NotNil(t, exp)
	assert.NotNil(t, exp.Reader())
}

func TestPrometheusExporter_Handler(t *testing.T) {
	exp := NewPrometheusExporter()
	require.NotNil(t, exp)

	handler := exp.Handler()
	require.NotNil(t, handler)

	req := httptest.NewRequest(http.MethodGet, "/metrics", nil)
	rec := httptest.NewRecorder()
	handler.ServeHTTP(rec, req)

	assert.Equal(t, http.StatusOK, rec.Code)
	assert.Contains(t, rec.Body.String(), "# HELP")
}

func TestPrometheusExporter_SetResourceAttributes(t *testing.T) {
	exp := NewPrometheusExporter()
	exp.SetResourceAttributes(map[string]string{
		"service.name": "test-service",
	})

	assert.NotNil(t, exp)
}

func TestPrometheusExporter_CollectAndFormat(t *testing.T) {
	exp := NewPrometheusExporter()
	ctx := context.Background()

	str, err := exp.CollectAndFormat(ctx)
	assert.NoError(t, err)
	assert.NotEmpty(t, str)
}

func TestPrometheusExporter_Shutdown(t *testing.T) {
	exp := NewPrometheusExporter()
	ctx := context.Background()

	err := exp.Shutdown(ctx)
	assert.NoError(t, err)
}

func TestSanitizeMetricName(t *testing.T) {
	assert.Equal(t, "http_requests_total", sanitizeMetricName("http.requests.total"))
	assert.Equal(t, "http_requests_total", sanitizeMetricName("http-requests-total"))
	assert.Equal(t, "http_requests_total", sanitizeMetricName("http/requests:total"))
}

func TestSanitizeLabelName(t *testing.T) {
	assert.Equal(t, "http_method", sanitizeLabelName("http.method"))
}

func TestFormatFloat64(t *testing.T) {
	assert.Equal(t, "3.14", formatFloat64(3.14))
	assert.Equal(t, "+Inf", formatFloat64(math.Inf(1)))
	assert.Equal(t, "-Inf", formatFloat64(math.Inf(-1)))
	assert.Equal(t, "NaN", formatFloat64(math.NaN()))
}

func TestWriteTargetInfo(t *testing.T) {
	exp := NewPrometheusExporter()
	_, _ = resource.New(context.Background(),
		resource.WithAttributes(attribute.String("service.name", "test")),
	)
	exp.SetResourceAttributes(map[string]string{
		"service_name": "test",
	})

	var rm metricdata.ResourceMetrics
	err := exp.Reader().Collect(context.Background(), &rm)
	assert.NoError(t, err)
}

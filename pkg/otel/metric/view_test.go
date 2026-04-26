package metric

import (
	"testing"

	"github.com/stretchr/testify/assert"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
)

func TestView_Matches_Name(t *testing.T) {
	v := NewView(ViewCriteria{Name: "requests"}, ViewTransform{})
	assert.True(t, v.Matches("requests", InstrumentKindCounter, "", ""))
	assert.False(t, v.Matches("errors", InstrumentKindCounter, "", ""))
}

func TestView_Matches_Wildcard(t *testing.T) {
	v := NewView(ViewCriteria{NameWildcard: "http.*"}, ViewTransform{})
	assert.True(t, v.Matches("http.requests", InstrumentKindCounter, "", ""))
	assert.False(t, v.Matches("grpc.requests", InstrumentKindCounter, "", ""))
}

func TestView_Matches_InstrumentKind(t *testing.T) {
	v := NewView(ViewCriteria{InstrumentKind: InstrumentKindHistogram}, ViewTransform{})
	assert.True(t, v.Matches("latency", InstrumentKindHistogram, "", ""))
	assert.False(t, v.Matches("requests", InstrumentKindCounter, "", ""))
}

func TestView_ToSDKView(t *testing.T) {
	v := NewView(
		ViewCriteria{Name: "requests"},
		ViewTransform{
			Description: "HTTP request count",
			Aggregation: sdkmetric.AggregationSum{},
		},
	)

	view := v.ToSDKView()
	assert.NotNil(t, view)
}

func TestViewsToSDK(t *testing.T) {
	views := []View{
		NewView(ViewCriteria{NameWildcard: "*"}, ViewTransform{}),
	}
	sdkViews := ViewsToSDK(views)
	assert.Len(t, sdkViews, 1)
}

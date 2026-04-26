package metric

import (
	"path"

	"go.opentelemetry.io/otel/attribute"
	sdkmetric "go.opentelemetry.io/otel/sdk/metric"
)

// InstrumentKind represents the kind of instrument.
type InstrumentKind int32

const (
	// InstrumentKindCounter is a counter instrument.
	InstrumentKindCounter InstrumentKind = iota
	// InstrumentKindUpDownCounter is an up-down counter instrument.
	InstrumentKindUpDownCounter
	// InstrumentKindHistogram is a histogram instrument.
	InstrumentKindHistogram
	// InstrumentKindObservableCounter is an observable counter instrument.
	InstrumentKindObservableCounter
	// InstrumentKindObservableUpDownCounter is an observable up-down counter instrument.
	InstrumentKindObservableUpDownCounter
	// InstrumentKindObservableGauge is an observable gauge instrument.
	InstrumentKindObservableGauge
	// InstrumentKindGauge is a gauge instrument.
	InstrumentKindGauge
)

// String returns the string representation of InstrumentKind.
func (ik InstrumentKind) String() string {
	switch ik {
	case InstrumentKindCounter:
		return "Counter"
	case InstrumentKindUpDownCounter:
		return "UpDownCounter"
	case InstrumentKindHistogram:
		return "Histogram"
	case InstrumentKindObservableCounter:
		return "ObservableCounter"
	case InstrumentKindObservableUpDownCounter:
		return "ObservableUpDownCounter"
	case InstrumentKindObservableGauge:
		return "ObservableGauge"
	case InstrumentKindGauge:
		return "Gauge"
	default:
		return "Unknown"
	}
}

// ViewCriteria defines criteria for matching instruments.
type ViewCriteria struct {
	// Name matches instruments with exactly this name.
	Name string
	// NameWildcard matches instrument names using glob patterns.
	// Supports * to match any sequence of characters and ? to match a single character.
	NameWildcard string
	// InstrumentKind matches instruments of this kind. Zero value matches all kinds.
	InstrumentKind InstrumentKind
	// Unit matches instruments with this unit. Empty string matches all units.
	Unit string
	// MeterName matches instruments from meters with this name. Empty string matches all.
	MeterName string
	// MeterVersion matches instruments from meters with this version. Empty string matches all.
	MeterVersion string
}

// ViewTransform defines transformations to apply to matched instruments.
type ViewTransform struct {
	// AttributeFilter filters attributes. Use attribute.NewAllowKeysFilter to
	// create a filter that only allows specific keys.
	// If nil, all attributes are kept.
	AttributeFilter attribute.Filter
	// Aggregation overrides the aggregation for matched instruments.
	// If nil, the default aggregation is used.
	Aggregation sdkmetric.Aggregation
	// Description overrides the instrument description.
	// If empty, the original description is kept.
	Description string
	// Unit overrides the instrument unit.
	// If empty, the original unit is kept.
	Unit string
}

// View combines criteria and transform for instrument customization.
type View struct {
	criteria  ViewCriteria
	transform ViewTransform
}

// NewView creates a new View with the given criteria and transform.
func NewView(criteria ViewCriteria, transform ViewTransform) View {
	return View{
		criteria:  criteria,
		transform: transform,
	}
}

// Criteria returns the view's criteria.
func (v View) Criteria() ViewCriteria {
	return v.criteria
}

// Transform returns the view's transform.
func (v View) Transform() ViewTransform {
	return v.transform
}

// matchGlob reports whether name matches the glob pattern.
func matchGlob(pattern, name string) bool {
	if pattern == "" {
		return true
	}
	if pattern == "*" {
		return true
	}
	matched, _ := path.Match(pattern, name)
	return matched
}

// Matches checks if an instrument matches the view criteria.
func (v View) Matches(name string, kind InstrumentKind, meterName, meterVersion string) bool {
	c := v.criteria

	// Check name criteria
	if c.Name != "" && c.Name != name {
		return false
	}
	if c.NameWildcard != "" && !matchGlob(c.NameWildcard, name) {
		return false
	}

	// Check instrument kind
	if c.InstrumentKind != 0 && c.InstrumentKind != kind {
		return false
	}

	// Check meter scope
	if c.MeterName != "" && c.MeterName != meterName {
		return false
	}
	if c.MeterVersion != "" && c.MeterVersion != meterVersion {
		return false
	}

	return true
}

// ToSDKView converts the custom View to an OpenTelemetry SDK View function.
func (v View) ToSDKView() sdkmetric.View {
	return func(i sdkmetric.Instrument) (sdkmetric.Stream, bool) {
		var kind InstrumentKind
		switch i.Kind {
		case sdkmetric.InstrumentKindCounter:
			kind = InstrumentKindCounter
		case sdkmetric.InstrumentKindUpDownCounter:
			kind = InstrumentKindUpDownCounter
		case sdkmetric.InstrumentKindHistogram:
			kind = InstrumentKindHistogram
		case sdkmetric.InstrumentKindObservableCounter:
			kind = InstrumentKindObservableCounter
		case sdkmetric.InstrumentKindObservableUpDownCounter:
			kind = InstrumentKindObservableUpDownCounter
		case sdkmetric.InstrumentKindObservableGauge:
			kind = InstrumentKindObservableGauge
		case sdkmetric.InstrumentKindGauge:
			kind = InstrumentKindGauge
		}

		if !v.Matches(i.Name, kind, i.Scope.Name, i.Scope.Version) {
			return sdkmetric.Stream{}, false
		}

		stream := sdkmetric.Stream{
			Name:        i.Name,
			Description: i.Description,
			Unit:        i.Unit,
		}

		t := v.transform
		if t.Description != "" {
			stream.Description = t.Description
		}
		if t.Unit != "" {
			stream.Unit = t.Unit
		}
		if t.Aggregation != nil {
			stream.Aggregation = t.Aggregation
		}
		if t.AttributeFilter != nil {
			stream.AttributeFilter = t.AttributeFilter
		}

		return stream, true
	}
}

// ViewsToSDK converts a slice of custom Views to SDK View functions.
func ViewsToSDK(views []View) []sdkmetric.View {
	if len(views) == 0 {
		return nil
	}
	result := make([]sdkmetric.View, len(views))
	for i, v := range views {
		result[i] = v.ToSDKView()
	}
	return result
}

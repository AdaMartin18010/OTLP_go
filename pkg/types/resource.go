// Package types provides resource types for OpenTelemetry compatible telemetry data.
package types

import (
	"encoding/json"
	"fmt"
	"sync"
)

// Resource represents an entity that produces telemetry data.
// Resources capture identifying information about the entities for which
// telemetry is recorded (e.g., a service, host, or container).
//
// Example:
//
//	resource := types.NewResource(
//	    types.NewAttribute("service.name", "my-service"),
//	    types.NewAttribute("service.version", "1.0.0"),
//	    types.NewAttribute("host.name", "server-01"),
//	)
//
//	// Or using the builder
//	resource := types.NewResourceBuilder().
//	    WithService("my-service", "1.0.0").
//	    WithHost("server-01").
//	    Build()
type Resource struct {
	// Attributes describing the resource.
	Attributes Attributes `json:"attributes"`

	// DroppedAttributeCount is the number of dropped attributes due to limits.
	DroppedAttributeCount uint32 `json:"dropped_attribute_count,omitempty"`

	// cachedHash is computed lazily for map keys.
	cachedHash string
	hashOnce   sync.Once
}

// NewResource creates a new Resource from the given attributes.
// Duplicate keys are deduplicated (last one wins).
func NewResource(attrs ...Attribute) *Resource {
	r := &Resource{
		Attributes: make(Attributes, 0, len(attrs)),
	}

	// Deduplicate keys (last one wins)
	seen := make(map[string]int)
	for _, attr := range attrs {
		if idx, exists := seen[attr.Key]; exists {
			r.Attributes[idx] = attr
		} else {
			seen[attr.Key] = len(r.Attributes)
			r.Attributes = append(r.Attributes, attr)
		}
	}

	return r
}

// NewResourceFromMap creates a Resource from a map of strings to values.
func NewResourceFromMap(m map[string]any) *Resource {
	attrs := make(Attributes, 0, len(m))
	for k, v := range m {
		var value Value
		switch val := v.(type) {
		case string:
			value = StringValue(val)
		case int:
			value = IntValue(int64(val))
		case int64:
			value = IntValue(val)
		case float64:
			value = DoubleValue(val)
		case bool:
			value = BoolValue(val)
		case []byte:
			value = BytesValue(val)
		default:
			value = StringValue(fmt.Sprintf("%v", v))
		}
		attrs = append(attrs, Attribute{Key: k, Value: value})
	}
	return NewResource(attrs...)
}

// EmptyResource returns an empty resource.
func EmptyResource() *Resource {
	return &Resource{
		Attributes: Attributes{},
	}
}

// Get returns the attribute value for the given key.
func (r *Resource) Get(key string) (Value, bool) {
	if r == nil {
		return Value{}, false
	}
	if attr, ok := r.Attributes.Get(key); ok {
		return attr.Value, true
	}
	return Value{}, false
}

// GetString returns the string value for the given key.
func (r *Resource) GetString(key string) string {
	v, _ := r.Get(key)
	return v.AsString()
}

// GetInt returns the int64 value for the given key.
func (r *Resource) GetInt(key string) int64 {
	v, _ := r.Get(key)
	return v.AsInt()
}

// GetFloat returns the float64 value for the given key.
func (r *Resource) GetFloat(key string) float64 {
	v, _ := r.Get(key)
	return v.AsFloat()
}

// GetBool returns the bool value for the given key.
func (r *Resource) GetBool(key string) bool {
	v, _ := r.Get(key)
	return v.AsBool()
}

// Set adds or updates an attribute.
func (r *Resource) Set(key string, value Value) {
	if r == nil {
		return
	}
	// Invalidate cached hash
	r.cachedHash = ""
	r.hashOnce = sync.Once{}

	for i, attr := range r.Attributes {
		if attr.Key == key {
			r.Attributes[i].Value = value
			return
		}
	}
	r.Attributes = append(r.Attributes, Attribute{Key: key, Value: value})
}

// SetString adds or updates a string attribute.
func (r *Resource) SetString(key, value string) {
	r.Set(key, StringValue(value))
}

// SetInt adds or updates an int64 attribute.
func (r *Resource) SetInt(key string, value int64) {
	r.Set(key, IntValue(value))
}

// SetFloat adds or updates a float64 attribute.
func (r *Resource) SetFloat(key string, value float64) {
	r.Set(key, DoubleValue(value))
}

// SetBool adds or updates a bool attribute.
func (r *Resource) SetBool(key string, value bool) {
	r.Set(key, BoolValue(value))
}

// Merge combines this resource with another. Values from 'other' take precedence.
func (r *Resource) Merge(other *Resource) *Resource {
	if r == nil {
		return other
	}
	if other == nil {
		return r
	}

	return &Resource{
		Attributes:            r.Attributes.Merge(other.Attributes),
		DroppedAttributeCount: r.DroppedAttributeCount + other.DroppedAttributeCount,
	}
}

// Clone creates a deep copy of the resource.
func (r *Resource) Clone() *Resource {
	if r == nil {
		return nil
	}

	return &Resource{
		Attributes:            r.Attributes.Clone(),
		DroppedAttributeCount: r.DroppedAttributeCount,
	}
}

// Equal compares two resources for equality.
func (r *Resource) Equal(other *Resource) bool {
	if r == nil && other == nil {
		return true
	}
	if r == nil || other == nil {
		return false
	}

	if r.DroppedAttributeCount != other.DroppedAttributeCount {
		return false
	}

	if len(r.Attributes) != len(other.Attributes) {
		return false
	}

	for _, attr := range r.Attributes {
		otherVal, ok := other.Get(attr.Key)
		if !ok || !attr.Value.Equal(otherVal) {
			return false
		}
	}

	return true
}

// IsEmpty returns true if the resource has no attributes.
func (r *Resource) IsEmpty() bool {
	return r == nil || len(r.Attributes) == 0
}

// AttributeCount returns the number of attributes.
func (r *Resource) AttributeCount() int {
	if r == nil {
		return 0
	}
	return len(r.Attributes)
}

// String returns a string representation of the resource.
func (r *Resource) String() string {
	if r == nil {
		return "Resource(nil)"
	}

	data, _ := json.Marshal(r.Attributes.ToMap())
	return fmt.Sprintf("Resource%s", string(data))
}

// Hash returns a hash string suitable for use as a map key.
func (r *Resource) Hash() string {
	if r == nil {
		return ""
	}

	r.hashOnce.Do(func() {
		// Simple hash based on sorted attributes
		data, _ := json.Marshal(r.Attributes.ToMap())
		r.cachedHash = string(data)
	})

	return r.cachedHash
}

// Validate checks if the resource is valid.
func (r *Resource) Validate() error {
	if r == nil {
		return ErrNilResource
	}
	return r.Attributes.Validate()
}

// MarshalJSON implements json.Marshaler.
func (r *Resource) MarshalJSON() ([]byte, error) {
	if r == nil {
		return []byte("null"), nil
	}

	type resourceJSON struct {
		Attributes            map[string]Value `json:"attributes"`
		DroppedAttributeCount uint32           `json:"dropped_attribute_count,omitempty"`
	}

	return json.Marshal(resourceJSON{
		Attributes:            r.Attributes.ToMap(),
		DroppedAttributeCount: r.DroppedAttributeCount,
	})
}

// UnmarshalJSON implements json.Unmarshaler.
func (r *Resource) UnmarshalJSON(data []byte) error {
	type resourceJSON struct {
		Attributes            map[string]Value `json:"attributes"`
		DroppedAttributeCount uint32           `json:"dropped_attribute_count,omitempty"`
	}

	var temp resourceJSON
	if err := json.Unmarshal(data, &temp); err != nil {
		return err
	}

	attrs := make(Attributes, 0, len(temp.Attributes))
	for k, v := range temp.Attributes {
		attrs = append(attrs, Attribute{Key: k, Value: v})
	}

	r.Attributes = attrs
	r.DroppedAttributeCount = temp.DroppedAttributeCount
	r.cachedHash = ""
	r.hashOnce = sync.Once{}

	return nil
}

// ResourceBuilder provides a fluent API for building resources.
type ResourceBuilder struct {
	attrs []Attribute
}

// NewResourceBuilder creates a new ResourceBuilder.
func NewResourceBuilder() *ResourceBuilder {
	return &ResourceBuilder{
		attrs: make([]Attribute, 0),
	}
}

// WithAttribute adds a generic attribute.
func (b *ResourceBuilder) WithAttribute(key string, value Value) *ResourceBuilder {
	b.attrs = append(b.attrs, Attribute{Key: key, Value: value})
	return b
}

// WithString adds a string attribute.
func (b *ResourceBuilder) WithString(key, value string) *ResourceBuilder {
	return b.WithAttribute(key, StringValue(value))
}

// WithInt adds an int64 attribute.
func (b *ResourceBuilder) WithInt(key string, value int64) *ResourceBuilder {
	return b.WithAttribute(key, IntValue(value))
}

// WithFloat adds a float64 attribute.
func (b *ResourceBuilder) WithFloat(key string, value float64) *ResourceBuilder {
	return b.WithAttribute(key, DoubleValue(value))
}

// WithBool adds a bool attribute.
func (b *ResourceBuilder) WithBool(key string, value bool) *ResourceBuilder {
	return b.WithAttribute(key, BoolValue(value))
}

// WithService adds standard service attributes.
func (b *ResourceBuilder) WithService(name, version string) *ResourceBuilder {
	return b.WithString("service.name", name).
		WithString("service.version", version)
}

// WithServiceNamespace adds the service namespace attribute.
func (b *ResourceBuilder) WithServiceNamespace(namespace string) *ResourceBuilder {
	return b.WithString("service.namespace", namespace)
}

// WithServiceInstance adds the service instance ID attribute.
func (b *ResourceBuilder) WithServiceInstance(instanceID string) *ResourceBuilder {
	return b.WithString("service.instance.id", instanceID)
}

// WithHost adds standard host attributes.
func (b *ResourceBuilder) WithHost(hostname string) *ResourceBuilder {
	return b.WithString("host.name", hostname)
}

// WithHostID adds the host ID attribute.
func (b *ResourceBuilder) WithHostID(hostID string) *ResourceBuilder {
	return b.WithString("host.id", hostID)
}

// WithHostType adds the host type attribute.
func (b *ResourceBuilder) WithHostType(hostType string) *ResourceBuilder {
	return b.WithString("host.type", hostType)
}

// WithOS adds standard OS attributes.
func (b *ResourceBuilder) WithOS(name, version string) *ResourceBuilder {
	return b.WithString("os.type", name).
		WithString("os.version", version)
}

// WithContainer adds standard container attributes.
func (b *ResourceBuilder) WithContainer(id, name, image string) *ResourceBuilder {
	b.WithString("container.id", id)
	if name != "" {
		b.WithString("container.name", name)
	}
	if image != "" {
		b.WithString("container.image.name", image)
	}
	return b
}

// WithK8sPod adds standard Kubernetes pod attributes.
func (b *ResourceBuilder) WithK8sPod(name, namespace, uid string) *ResourceBuilder {
	b.WithString("k8s.pod.name", name)
	if namespace != "" {
		b.WithString("k8s.namespace.name", namespace)
	}
	if uid != "" {
		b.WithString("k8s.pod.uid", uid)
	}
	return b
}

// WithK8sDeployment adds standard Kubernetes deployment attributes.
func (b *ResourceBuilder) WithK8sDeployment(name, namespace string) *ResourceBuilder {
	b.WithString("k8s.deployment.name", name)
	if namespace != "" {
		b.WithString("k8s.namespace.name", namespace)
	}
	return b
}

// WithCloudProvider adds standard cloud provider attributes.
func (b *ResourceBuilder) WithCloudProvider(provider, region, zone string) *ResourceBuilder {
	b.WithString("cloud.provider", provider)
	if region != "" {
		b.WithString("cloud.region", region)
	}
	if zone != "" {
		b.WithString("cloud.availability_zone", zone)
	}
	return b
}

// WithTelemetrySDK adds standard telemetry SDK attributes.
func (b *ResourceBuilder) WithTelemetrySDK(name, version, language string) *ResourceBuilder {
	b.WithString("telemetry.sdk.name", name).
		WithString("telemetry.sdk.version", version)
	if language != "" {
		b.WithString("telemetry.sdk.language", language)
	}
	return b
}

// Build creates the Resource.
func (b *ResourceBuilder) Build() *Resource {
	return NewResource(b.attrs...)
}

// ResourceDetector is a function that detects resource attributes from the environment.
type ResourceDetector func() (*Resource, error)

// DetectResources runs multiple detectors and merges their results.
func DetectResources(detectors ...ResourceDetector) (*Resource, error) {
	var result *Resource

	for _, detector := range detectors {
		resource, err := detector()
		if err != nil {
			continue // Skip failed detectors
		}
		result = result.Merge(resource)
	}

	if result == nil {
		return EmptyResource(), nil
	}

	return result, nil
}

// DefaultResource returns a resource with default telemetry SDK attributes.
func DefaultResource() *Resource {
	return NewResourceBuilder().
		WithTelemetrySDK("OTLP_go", "1.0.0", "go").
		Build()
}

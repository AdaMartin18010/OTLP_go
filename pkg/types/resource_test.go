package types

import (
	"encoding/json"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNewResource(t *testing.T) {
	t.Run("With attributes", func(t *testing.T) {
		r := NewResource(
			NewAttribute("service.name", "my-service"),
			NewAttribute("service.version", "1.0.0"),
		)

		assert.Equal(t, "my-service", r.GetString("service.name"))
		assert.Equal(t, "1.0.0", r.GetString("service.version"))
	})

	t.Run("Deduplicates keys", func(t *testing.T) {
		r := NewResource(
			NewAttribute("key", "value1"),
			NewAttribute("key", "value2"),
		)

		assert.Equal(t, "value2", r.GetString("key"))
		assert.Equal(t, 1, r.AttributeCount())
	})

	t.Run("Empty resource", func(t *testing.T) {
		r := NewResource()
		assert.NotNil(t, r)
		assert.True(t, r.IsEmpty())
	})
}

func TestNewResourceFromMap(t *testing.T) {
	t.Run("With various types", func(t *testing.T) {
		m := map[string]any{
			"str":   "value",
			"int":   42,
			"int64": int64(64),
			"float": 3.14,
			"bool":  true,
			"bytes": []byte{0x01, 0x02},
		}

		r := NewResourceFromMap(m)

		assert.Equal(t, "value", r.GetString("str"))
		assert.Equal(t, int64(42), r.GetInt("int"))
		assert.Equal(t, int64(64), r.GetInt("int64"))
		assert.Equal(t, 3.14, r.GetFloat("float"))
		assert.True(t, r.GetBool("bool"))
	})

	t.Run("Unknown type", func(t *testing.T) {
		m := map[string]any{
			"unknown": struct{ X int }{X: 1},
		}

		r := NewResourceFromMap(m)
		assert.Equal(t, "{1}", r.GetString("unknown"))
	})
}

func TestEmptyResource(t *testing.T) {
	r := EmptyResource()
	assert.NotNil(t, r)
	assert.True(t, r.IsEmpty())
}

func TestResourceGet(t *testing.T) {
	r := NewResource(
		NewAttribute("str", "value"),
		NewIntAttribute("int", 42),
		NewFloatAttribute("float", 3.14),
		NewBoolAttribute("bool", true),
	)

	t.Run("GetString", func(t *testing.T) {
		assert.Equal(t, "value", r.GetString("str"))
		assert.Equal(t, "", r.GetString("nonexistent"))
	})

	t.Run("GetInt", func(t *testing.T) {
		assert.Equal(t, int64(42), r.GetInt("int"))
		assert.Equal(t, int64(0), r.GetInt("nonexistent"))
	})

	t.Run("GetFloat", func(t *testing.T) {
		assert.Equal(t, 3.14, r.GetFloat("float"))
		assert.Equal(t, 0.0, r.GetFloat("nonexistent"))
	})

	t.Run("GetBool", func(t *testing.T) {
		assert.True(t, r.GetBool("bool"))
		assert.False(t, r.GetBool("nonexistent"))
	})

	t.Run("Get", func(t *testing.T) {
		v, ok := r.Get("str")
		assert.True(t, ok)
		assert.Equal(t, "value", v.AsString())

		_, ok = r.Get("nonexistent")
		assert.False(t, ok)
	})
}

func TestResourceGetNil(t *testing.T) {
	var r *Resource
	assert.Equal(t, "", r.GetString("key"))
	assert.Equal(t, int64(0), r.GetInt("key"))
	assert.Equal(t, 0.0, r.GetFloat("key"))
	assert.False(t, r.GetBool("key"))

	_, ok := r.Get("key")
	assert.False(t, ok)
}

func TestResourceSet(t *testing.T) {
	t.Run("Add new attribute", func(t *testing.T) {
		r := NewResource()
		r.Set("key", StringValue("value"))

		assert.Equal(t, "value", r.GetString("key"))
	})

	t.Run("Update existing attribute", func(t *testing.T) {
		r := NewResource(NewAttribute("key", "old"))
		r.Set("key", StringValue("new"))

		assert.Equal(t, "new", r.GetString("key"))
	})

	t.Run("Set on nil resource", func(t *testing.T) {
		var r *Resource
		r.Set("key", StringValue("value")) // Should not panic
	})

	t.Run("SetString", func(t *testing.T) {
		r := NewResource()
		r.SetString("key", "value")
		assert.Equal(t, "value", r.GetString("key"))
	})

	t.Run("SetInt", func(t *testing.T) {
		r := NewResource()
		r.SetInt("key", 42)
		assert.Equal(t, int64(42), r.GetInt("key"))
	})

	t.Run("SetFloat", func(t *testing.T) {
		r := NewResource()
		r.SetFloat("key", 3.14)
		assert.Equal(t, 3.14, r.GetFloat("key"))
	})

	t.Run("SetBool", func(t *testing.T) {
		r := NewResource()
		r.SetBool("key", true)
		assert.True(t, r.GetBool("key"))
	})
}

func TestResourceMerge(t *testing.T) {
	t.Run("Both non-nil", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key1", "a"), NewAttribute("shared", "a"))
		r2 := NewResource(NewAttribute("key2", "b"), NewAttribute("shared", "b"))

		merged := r1.Merge(r2)

		assert.Equal(t, "a", merged.GetString("key1"))
		assert.Equal(t, "b", merged.GetString("key2"))
		assert.Equal(t, "b", merged.GetString("shared")) // r2 takes precedence
	})

	t.Run("Nil receiver", func(t *testing.T) {
		r2 := NewResource(NewAttribute("key", "value"))
		var r1 *Resource

		merged := r1.Merge(r2)
		assert.Equal(t, "value", merged.GetString("key"))
	})

	t.Run("Nil argument", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key", "value"))
		var r2 *Resource

		merged := r1.Merge(r2)
		assert.Equal(t, "value", merged.GetString("key"))
	})

	t.Run("Accumulates dropped count", func(t *testing.T) {
		r1 := &Resource{DroppedAttributeCount: 5}
		r2 := &Resource{DroppedAttributeCount: 3}

		merged := r1.Merge(r2)
		assert.Equal(t, uint32(8), merged.DroppedAttributeCount)
	})
}

func TestResourceClone(t *testing.T) {
	t.Run("Non-nil", func(t *testing.T) {
		r := NewResource(NewAttribute("key", "value"))
		cloned := r.Clone()

		assert.Equal(t, r.GetString("key"), cloned.GetString("key"))
		assert.Equal(t, r.AttributeCount(), cloned.AttributeCount())
	})

	t.Run("Nil", func(t *testing.T) {
		var r *Resource
		cloned := r.Clone()
		assert.Nil(t, cloned)
	})

	t.Run("Empty", func(t *testing.T) {
		r := EmptyResource()
		cloned := r.Clone()

		assert.True(t, cloned.IsEmpty())
	})
}

func TestResourceEqual(t *testing.T) {
	t.Run("Both nil", func(t *testing.T) {
		var r1, r2 *Resource
		assert.True(t, r1.Equal(r2))
	})

	t.Run("One nil", func(t *testing.T) {
		r1 := NewResource()
		var r2 *Resource
		assert.False(t, r1.Equal(r2))
		assert.False(t, r2.Equal(r1))
	})

	t.Run("Same attributes", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key", "value"))
		r2 := NewResource(NewAttribute("key", "value"))
		assert.True(t, r1.Equal(r2))
	})

	t.Run("Different values", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key", "value1"))
		r2 := NewResource(NewAttribute("key", "value2"))
		assert.False(t, r1.Equal(r2))
	})

	t.Run("Different keys", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key1", "value"))
		r2 := NewResource(NewAttribute("key2", "value"))
		assert.False(t, r1.Equal(r2))
	})

	t.Run("Different dropped count", func(t *testing.T) {
		r1 := &Resource{DroppedAttributeCount: 1}
		r2 := &Resource{DroppedAttributeCount: 2}
		assert.False(t, r1.Equal(r2))
	})
}

func TestResourceIsEmpty(t *testing.T) {
	t.Run("Empty", func(t *testing.T) {
		r := NewResource()
		assert.True(t, r.IsEmpty())
	})

	t.Run("Non-empty", func(t *testing.T) {
		r := NewResource(NewAttribute("key", "value"))
		assert.False(t, r.IsEmpty())
	})

	t.Run("Nil", func(t *testing.T) {
		var r *Resource
		assert.True(t, r.IsEmpty())
	})
}

func TestResourceAttributeCount(t *testing.T) {
	t.Run("Nil", func(t *testing.T) {
		var r *Resource
		assert.Equal(t, 0, r.AttributeCount())
	})

	t.Run("Empty", func(t *testing.T) {
		r := NewResource()
		assert.Equal(t, 0, r.AttributeCount())
	})

	t.Run("Non-empty", func(t *testing.T) {
		r := NewResource(
			NewAttribute("key1", "value1"),
			NewAttribute("key2", "value2"),
		)
		assert.Equal(t, 2, r.AttributeCount())
	})
}

func TestResourceString(t *testing.T) {
	t.Run("Non-nil", func(t *testing.T) {
		r := NewResource(NewAttribute("key", "value"))
		s := r.String()
		assert.Contains(t, s, "Resource")
		assert.Contains(t, s, "key")
		assert.Contains(t, s, "value")
	})

	t.Run("Nil", func(t *testing.T) {
		var r *Resource
		assert.Equal(t, "Resource(nil)", r.String())
	})
}

func TestResourceHash(t *testing.T) {
	t.Run("Consistent", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key", "value"))
		r2 := NewResource(NewAttribute("key", "value"))

		assert.Equal(t, r1.Hash(), r2.Hash())
	})

	t.Run("Different resources", func(t *testing.T) {
		r1 := NewResource(NewAttribute("key", "value1"))
		r2 := NewResource(NewAttribute("key", "value2"))

		assert.NotEqual(t, r1.Hash(), r2.Hash())
	})

	t.Run("Nil", func(t *testing.T) {
		var r *Resource
		assert.Equal(t, "", r.Hash())
	})
}

func TestResourceValidate(t *testing.T) {
	t.Run("Valid", func(t *testing.T) {
		r := NewResource(NewAttribute("key", "value"))
		assert.NoError(t, r.Validate())
	})

	t.Run("Nil", func(t *testing.T) {
		var r *Resource
		assert.ErrorIs(t, r.Validate(), ErrNilResource)
	})

	t.Run("Invalid attribute", func(t *testing.T) {
		r := NewResource(NewAttribute("", "value"))
		assert.ErrorIs(t, r.Validate(), ErrInvalidAttribute)
	})
}

func TestResourceJSON(t *testing.T) {
	t.Run("Marshal", func(t *testing.T) {
		r := NewResource(NewAttribute("key", "value"))
		data, err := json.Marshal(r)
		require.NoError(t, err)

		var m map[string]map[string]any
		err = json.Unmarshal(data, &m)
		require.NoError(t, err)

		attrs, ok := m["attributes"]
		require.True(t, ok)
		keyVal, ok := attrs["key"].(map[string]any)
		require.True(t, ok)
		assert.Equal(t, "value", keyVal["string_val"])
	})

	t.Run("Marshal nil", func(t *testing.T) {
		var r *Resource
		data, err := json.Marshal(r)
		require.NoError(t, err)
		assert.Equal(t, "null", string(data))
	})

	t.Run("Unmarshal with Value objects", func(t *testing.T) {
		// JSON with proper Value structure
		data := []byte(`{"attributes":{"key":{"type":1,"string_val":"value"}},"dropped_attribute_count":5}`)
		var r Resource
		err := json.Unmarshal(data, &r)
		require.NoError(t, err)

		assert.Equal(t, "value", r.GetString("key"))
		assert.Equal(t, uint32(5), r.DroppedAttributeCount)
	})
}

func TestResourceBuilder(t *testing.T) {
	t.Run("Basic builder", func(t *testing.T) {
		r := NewResourceBuilder().
			WithAttribute("custom", StringValue("value")).
			WithString("str", "value").
			WithInt("int", 42).
			WithFloat("float", 3.14).
			WithBool("bool", true).
			Build()

		assert.Equal(t, "value", r.GetString("custom"))
		assert.Equal(t, "value", r.GetString("str"))
		assert.Equal(t, int64(42), r.GetInt("int"))
		assert.Equal(t, 3.14, r.GetFloat("float"))
		assert.True(t, r.GetBool("bool"))
	})

	t.Run("Service attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithService("my-service", "1.0.0").
			WithServiceNamespace("production").
			WithServiceInstance("instance-1").
			Build()

		assert.Equal(t, "my-service", r.GetString("service.name"))
		assert.Equal(t, "1.0.0", r.GetString("service.version"))
		assert.Equal(t, "production", r.GetString("service.namespace"))
		assert.Equal(t, "instance-1", r.GetString("service.instance.id"))
	})

	t.Run("Host attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithHost("server-01").
			WithHostID("host-123").
			WithHostType("vm").
			Build()

		assert.Equal(t, "server-01", r.GetString("host.name"))
		assert.Equal(t, "host-123", r.GetString("host.id"))
		assert.Equal(t, "vm", r.GetString("host.type"))
	})

	t.Run("OS attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithOS("linux", "5.10").
			Build()

		assert.Equal(t, "linux", r.GetString("os.type"))
		assert.Equal(t, "5.10", r.GetString("os.version"))
	})

	t.Run("Container attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithContainer("abc123", "my-container", "my-image:latest").
			Build()

		assert.Equal(t, "abc123", r.GetString("container.id"))
		assert.Equal(t, "my-container", r.GetString("container.name"))
		assert.Equal(t, "my-image:latest", r.GetString("container.image.name"))
	})

	t.Run("K8s pod attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithK8sPod("my-pod", "default", "pod-123").
			Build()

		assert.Equal(t, "my-pod", r.GetString("k8s.pod.name"))
		assert.Equal(t, "default", r.GetString("k8s.namespace.name"))
		assert.Equal(t, "pod-123", r.GetString("k8s.pod.uid"))
	})

	t.Run("K8s deployment attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithK8sDeployment("my-deployment", "production").
			Build()

		assert.Equal(t, "my-deployment", r.GetString("k8s.deployment.name"))
		assert.Equal(t, "production", r.GetString("k8s.namespace.name"))
	})

	t.Run("Cloud provider attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithCloudProvider("aws", "us-east-1", "us-east-1a").
			Build()

		assert.Equal(t, "aws", r.GetString("cloud.provider"))
		assert.Equal(t, "us-east-1", r.GetString("cloud.region"))
		assert.Equal(t, "us-east-1a", r.GetString("cloud.availability_zone"))
	})

	t.Run("Telemetry SDK attributes", func(t *testing.T) {
		r := NewResourceBuilder().
			WithTelemetrySDK("OTLP_go", "1.0.0", "go").
			Build()

		assert.Equal(t, "OTLP_go", r.GetString("telemetry.sdk.name"))
		assert.Equal(t, "1.0.0", r.GetString("telemetry.sdk.version"))
		assert.Equal(t, "go", r.GetString("telemetry.sdk.language"))
	})
}

func TestDetectResources(t *testing.T) {
	t.Run("Multiple detectors", func(t *testing.T) {
		detector1 := func() (*Resource, error) {
			return NewResource(NewAttribute("key1", "value1")), nil
		}
		detector2 := func() (*Resource, error) {
			return NewResource(NewAttribute("key2", "value2")), nil
		}

		r, err := DetectResources(detector1, detector2)
		require.NoError(t, err)

		assert.Equal(t, "value1", r.GetString("key1"))
		assert.Equal(t, "value2", r.GetString("key2"))
	})

	t.Run("Failed detector skipped", func(t *testing.T) {
		detector1 := func() (*Resource, error) {
			return NewResource(NewAttribute("key1", "value1")), nil
		}
		detector2 := func() (*Resource, error) {
			return nil, assert.AnError
		}

		r, err := DetectResources(detector1, detector2)
		require.NoError(t, err)

		assert.Equal(t, "value1", r.GetString("key1"))
	})

	t.Run("No detectors", func(t *testing.T) {
		r, err := DetectResources()
		require.NoError(t, err)
		assert.True(t, r.IsEmpty())
	})
}

func TestDefaultResource(t *testing.T) {
	r := DefaultResource()

	assert.Equal(t, "OTLP_go", r.GetString("telemetry.sdk.name"))
	assert.Equal(t, "1.0.0", r.GetString("telemetry.sdk.version"))
	assert.Equal(t, "go", r.GetString("telemetry.sdk.language"))
}

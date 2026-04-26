package semconv

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestServiceName(t *testing.T) {
	kv := ServiceName("my-service")
	assert.Equal(t, string(AttributeKeyServiceName), string(kv.Key))
	assert.Equal(t, "my-service", kv.Value.AsString())
}

func TestServiceNamespace(t *testing.T) {
	kv := ServiceNamespace("acme")
	assert.Equal(t, string(AttributeKeyServiceNamespace), string(kv.Key))
	assert.Equal(t, "acme", kv.Value.AsString())
}

func TestServiceInstanceID(t *testing.T) {
	kv := ServiceInstanceID("instance-1")
	assert.Equal(t, string(AttributeKeyServiceInstanceID), string(kv.Key))
	assert.Equal(t, "instance-1", kv.Value.AsString())
}

func TestServiceVersion(t *testing.T) {
	kv := ServiceVersion("1.0.0")
	assert.Equal(t, string(AttributeKeyServiceVersion), string(kv.Key))
	assert.Equal(t, "1.0.0", kv.Value.AsString())
}

func TestDeploymentEnvironment(t *testing.T) {
	kv := DeploymentEnvironment("production")
	assert.Equal(t, string(AttributeKeyDeploymentEnvironment), string(kv.Key))
	assert.Equal(t, "production", kv.Value.AsString())
}

func TestResourceAttributes(t *testing.T) {
	t.Run("all fields", func(t *testing.T) {
		attrs := ResourceAttributes("svc", "ns", "1.0")
		assert.Len(t, attrs, 3)
	})

	t.Run("minimal fields", func(t *testing.T) {
		attrs := ResourceAttributes("svc", "", "")
		assert.Len(t, attrs, 1)
		assert.Equal(t, "svc", attrs[0].Value.AsString())
	})

	t.Run("partial fields", func(t *testing.T) {
		attrs := ResourceAttributes("svc", "ns", "")
		assert.Len(t, attrs, 2)
	})
}

func TestResourceConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("service.name"), AttributeKeyServiceName)
	assert.Equal(t, attribute.Key("service.namespace"), AttributeKeyServiceNamespace)
	assert.Equal(t, attribute.Key("service.instance.id"), AttributeKeyServiceInstanceID)
	assert.Equal(t, attribute.Key("service.version"), AttributeKeyServiceVersion)
	assert.Equal(t, attribute.Key("deployment.environment"), AttributeKeyDeploymentEnvironment)
}

package semconv

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestMessagingSystem(t *testing.T) {
	kv := MessagingSystem("kafka")
	assert.Equal(t, string(AttributeKeyMessagingSystem), string(kv.Key))
	assert.Equal(t, "kafka", kv.Value.AsString())
}

func TestMessagingDestinationName(t *testing.T) {
	kv := MessagingDestinationName("orders")
	assert.Equal(t, string(AttributeKeyMessagingDestinationName), string(kv.Key))
	assert.Equal(t, "orders", kv.Value.AsString())
}

func TestMessagingOperationType(t *testing.T) {
	kv := MessagingOperationType("publish")
	assert.Equal(t, string(AttributeKeyMessagingOperationType), string(kv.Key))
	assert.Equal(t, "publish", kv.Value.AsString())
}

func TestMessagingMessageID(t *testing.T) {
	kv := MessagingMessageID("msg-123")
	assert.Equal(t, string(AttributeKeyMessagingMessageID), string(kv.Key))
	assert.Equal(t, "msg-123", kv.Value.AsString())
}

func TestMessagingClientID(t *testing.T) {
	kv := MessagingClientID("client-1")
	assert.Equal(t, string(AttributeKeyMessagingClientID), string(kv.Key))
	assert.Equal(t, "client-1", kv.Value.AsString())
}

func TestMessagingDestinationKind(t *testing.T) {
	kv := MessagingDestinationKind("topic")
	assert.Equal(t, string(AttributeKeyMessagingDestinationKind), string(kv.Key))
	assert.Equal(t, "topic", kv.Value.AsString())
}

func TestMessagingAttributes(t *testing.T) {
	t.Run("all fields", func(t *testing.T) {
		attrs := MessagingAttributes("rabbitmq", "queue1", "receive")
		assert.Len(t, attrs, 3)
	})

	t.Run("empty fields", func(t *testing.T) {
		attrs := MessagingAttributes("sns", "", "")
		assert.Len(t, attrs, 1)
		assert.Equal(t, "sns", attrs[0].Value.AsString())
	})
}

func TestMessagingConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("messaging.system"), AttributeKeyMessagingSystem)
	assert.Equal(t, attribute.Key("messaging.destination.name"), AttributeKeyMessagingDestinationName)
	assert.Equal(t, attribute.Key("messaging.operation.type"), AttributeKeyMessagingOperationType)
}

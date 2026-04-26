package semconv

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestRPCSystem(t *testing.T) {
	kv := RPCSystem("grpc")
	assert.Equal(t, string(AttributeKeyRPCSystem), string(kv.Key))
	assert.Equal(t, "grpc", kv.Value.AsString())
}

func TestRPCService(t *testing.T) {
	kv := RPCService("UserService")
	assert.Equal(t, string(AttributeKeyRPCService), string(kv.Key))
	assert.Equal(t, "UserService", kv.Value.AsString())
}

func TestRPCMethod(t *testing.T) {
	kv := RPCMethod("GetUser")
	assert.Equal(t, string(AttributeKeyRPCMethod), string(kv.Key))
	assert.Equal(t, "GetUser", kv.Value.AsString())
}

func TestRPCGRPCStatusCode(t *testing.T) {
	kv := RPCGRPCStatusCode(0)
	assert.Equal(t, string(AttributeKeyRPCGRPCStatusCode), string(kv.Key))
	assert.Equal(t, int64(0), kv.Value.AsInt64())
}

func TestRPCAttributes(t *testing.T) {
	t.Run("all fields", func(t *testing.T) {
		attrs := RPCAttributes("grpc", "UserService", "GetUser")
		assert.Len(t, attrs, 3)
	})

	t.Run("minimal fields", func(t *testing.T) {
		attrs := RPCAttributes("json-rpc", "", "")
		assert.Len(t, attrs, 1)
	})
}

func TestRPCConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("rpc.system"), AttributeKeyRPCSystem)
	assert.Equal(t, attribute.Key("rpc.service"), AttributeKeyRPCService)
	assert.Equal(t, attribute.Key("rpc.method"), AttributeKeyRPCMethod)
	assert.Equal(t, attribute.Key("rpc.grpc.status_code"), AttributeKeyRPCGRPCStatusCode)
}

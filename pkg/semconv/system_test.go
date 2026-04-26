package semconv

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"go.opentelemetry.io/otel/attribute"
)

func TestSystemCPUTime(t *testing.T) {
	kv := SystemCPUTime(1.5)
	assert.Equal(t, string(AttributeKeySystemCPUTime), string(kv.Key))
	assert.InDelta(t, 1.5, kv.Value.AsFloat64(), 0.001)
}

func TestSystemMemoryUsage(t *testing.T) {
	kv := SystemMemoryUsage(1024000)
	assert.Equal(t, string(AttributeKeySystemMemoryUsage), string(kv.Key))
	assert.Equal(t, int64(1024000), kv.Value.AsInt64())
}

func TestSystemDiskIO(t *testing.T) {
	kv := SystemDiskIO(2048)
	assert.Equal(t, string(AttributeKeySystemDiskIO), string(kv.Key))
	assert.Equal(t, int64(2048), kv.Value.AsInt64())
}

func TestSystemNetworkIO(t *testing.T) {
	kv := SystemNetworkIO(4096)
	assert.Equal(t, string(AttributeKeySystemNetworkIO), string(kv.Key))
	assert.Equal(t, int64(4096), kv.Value.AsInt64())
}

func TestUCUMUnits(t *testing.T) {
	assert.Equal(t, "s", UnitSecond)
	assert.Equal(t, "By", UnitByte)
	assert.Equal(t, "bit", UnitBit)
	assert.Equal(t, "%", UnitPercent)
}

func TestSystemConstants(t *testing.T) {
	assert.Equal(t, attribute.Key("system.cpu.time"), AttributeKeySystemCPUTime)
	assert.Equal(t, attribute.Key("system.memory.usage"), AttributeKeySystemMemoryUsage)
	assert.Equal(t, attribute.Key("system.disk.io"), AttributeKeySystemDiskIO)
	assert.Equal(t, attribute.Key("system.network.io"), AttributeKeySystemNetworkIO)
}

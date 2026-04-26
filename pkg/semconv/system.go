package semconv

import "go.opentelemetry.io/otel/attribute"

// UCUM units for system metrics.
const (
	UnitSecond  = "s"
	UnitByte    = "By"
	UnitBit     = "bit"
	UnitPercent = "%"
)

// System semantic convention attribute keys.
const (
	AttributeKeySystemCPUTime     = attribute.Key("system.cpu.time")
	AttributeKeySystemMemoryUsage = attribute.Key("system.memory.usage")
	AttributeKeySystemDiskIO      = attribute.Key("system.disk.io")
	AttributeKeySystemNetworkIO   = attribute.Key("system.network.io")
)

// SystemCPUTime returns an attribute KeyValue conforming to the
// "system.cpu.time" semantic convention.
func SystemCPUTime(val float64) attribute.KeyValue {
	return AttributeKeySystemCPUTime.Float64(val)
}

// SystemMemoryUsage returns an attribute KeyValue conforming to the
// "system.memory.usage" semantic convention.
func SystemMemoryUsage(val int64) attribute.KeyValue {
	return AttributeKeySystemMemoryUsage.Int64(val)
}

// SystemDiskIO returns an attribute KeyValue conforming to the
// "system.disk.io" semantic convention.
func SystemDiskIO(val int64) attribute.KeyValue {
	return AttributeKeySystemDiskIO.Int64(val)
}

// SystemNetworkIO returns an attribute KeyValue conforming to the
// "system.network.io" semantic convention.
func SystemNetworkIO(val int64) attribute.KeyValue {
	return AttributeKeySystemNetworkIO.Int64(val)
}

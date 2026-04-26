package semconv

import "go.opentelemetry.io/otel/attribute"

// RPC semantic convention attribute keys.
const (
	AttributeKeyRPCSystem         = attribute.Key("rpc.system")
	AttributeKeyRPCService        = attribute.Key("rpc.service")
	AttributeKeyRPCMethod         = attribute.Key("rpc.method")
	AttributeKeyRPCGRPCStatusCode = attribute.Key("rpc.grpc.status_code")
)

// RPCSystem returns an attribute KeyValue conforming to the
// "rpc.system" semantic convention.
func RPCSystem(val string) attribute.KeyValue {
	return AttributeKeyRPCSystem.String(val)
}

// RPCService returns an attribute KeyValue conforming to the
// "rpc.service" semantic convention.
func RPCService(val string) attribute.KeyValue {
	return AttributeKeyRPCService.String(val)
}

// RPCMethod returns an attribute KeyValue conforming to the
// "rpc.method" semantic convention.
func RPCMethod(val string) attribute.KeyValue {
	return AttributeKeyRPCMethod.String(val)
}

// RPCGRPCStatusCode returns an attribute KeyValue conforming to the
// "rpc.grpc.status_code" semantic convention.
func RPCGRPCStatusCode(val int) attribute.KeyValue {
	return AttributeKeyRPCGRPCStatusCode.Int(val)
}

// RPCAttributes returns RPC attributes for the given system, service, and method.
func RPCAttributes(system, service, method string) []attribute.KeyValue {
	attrs := []attribute.KeyValue{
		RPCSystem(system),
	}
	if service != "" {
		attrs = append(attrs, RPCService(service))
	}
	if method != "" {
		attrs = append(attrs, RPCMethod(method))
	}
	return attrs
}

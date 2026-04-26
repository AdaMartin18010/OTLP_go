package semconv

import "go.opentelemetry.io/otel/attribute"

// Resource semantic convention attribute keys.
const (
	AttributeKeyServiceName           = attribute.Key("service.name")
	AttributeKeyServiceNamespace      = attribute.Key("service.namespace")
	AttributeKeyServiceInstanceID     = attribute.Key("service.instance.id")
	AttributeKeyServiceVersion        = attribute.Key("service.version")
	AttributeKeyDeploymentEnvironment = attribute.Key("deployment.environment")
)

// ServiceName returns an attribute KeyValue conforming to the
// "service.name" semantic convention.
func ServiceName(val string) attribute.KeyValue {
	return AttributeKeyServiceName.String(val)
}

// ServiceNamespace returns an attribute KeyValue conforming to the
// "service.namespace" semantic convention.
func ServiceNamespace(val string) attribute.KeyValue {
	return AttributeKeyServiceNamespace.String(val)
}

// ServiceInstanceID returns an attribute KeyValue conforming to the
// "service.instance.id" semantic convention.
func ServiceInstanceID(val string) attribute.KeyValue {
	return AttributeKeyServiceInstanceID.String(val)
}

// ServiceVersion returns an attribute KeyValue conforming to the
// "service.version" semantic convention.
func ServiceVersion(val string) attribute.KeyValue {
	return AttributeKeyServiceVersion.String(val)
}

// DeploymentEnvironment returns an attribute KeyValue conforming to the
// "deployment.environment" semantic convention.
func DeploymentEnvironment(val string) attribute.KeyValue {
	return AttributeKeyDeploymentEnvironment.String(val)
}

// ResourceAttributes returns resource attributes for the given service metadata.
func ResourceAttributes(serviceName, namespace, version string) []attribute.KeyValue {
	attrs := []attribute.KeyValue{
		ServiceName(serviceName),
	}
	if namespace != "" {
		attrs = append(attrs, ServiceNamespace(namespace))
	}
	if version != "" {
		attrs = append(attrs, ServiceVersion(version))
	}
	return attrs
}

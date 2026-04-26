package semconv

import "go.opentelemetry.io/otel/attribute"

// Messaging semantic convention attribute keys.
const (
	AttributeKeyMessagingSystem          = attribute.Key("messaging.system")
	AttributeKeyMessagingDestinationName = attribute.Key("messaging.destination.name")
	AttributeKeyMessagingOperationType   = attribute.Key("messaging.operation.type")
	AttributeKeyMessagingMessageID       = attribute.Key("messaging.message.id")
	AttributeKeyMessagingClientID        = attribute.Key("messaging.client.id")
	AttributeKeyMessagingDestinationKind = attribute.Key("messaging.destination.kind")
)

// MessagingSystem returns an attribute KeyValue conforming to the
// "messaging.system" semantic convention.
func MessagingSystem(val string) attribute.KeyValue {
	return AttributeKeyMessagingSystem.String(val)
}

// MessagingDestinationName returns an attribute KeyValue conforming to the
// "messaging.destination.name" semantic convention.
func MessagingDestinationName(val string) attribute.KeyValue {
	return AttributeKeyMessagingDestinationName.String(val)
}

// MessagingOperationType returns an attribute KeyValue conforming to the
// "messaging.operation.type" semantic convention.
func MessagingOperationType(val string) attribute.KeyValue {
	return AttributeKeyMessagingOperationType.String(val)
}

// MessagingMessageID returns an attribute KeyValue conforming to the
// "messaging.message.id" semantic convention.
func MessagingMessageID(val string) attribute.KeyValue {
	return AttributeKeyMessagingMessageID.String(val)
}

// MessagingClientID returns an attribute KeyValue conforming to the
// "messaging.client.id" semantic convention.
func MessagingClientID(val string) attribute.KeyValue {
	return AttributeKeyMessagingClientID.String(val)
}

// MessagingDestinationKind returns an attribute KeyValue conforming to the
// "messaging.destination.kind" semantic convention.
func MessagingDestinationKind(val string) attribute.KeyValue {
	return AttributeKeyMessagingDestinationKind.String(val)
}

// MessagingAttributes returns messaging attributes for the given system, destination, and operation.
func MessagingAttributes(system, destination, operation string) []attribute.KeyValue {
	attrs := []attribute.KeyValue{
		MessagingSystem(system),
	}
	if destination != "" {
		attrs = append(attrs, MessagingDestinationName(destination))
	}
	if operation != "" {
		attrs = append(attrs, MessagingOperationType(operation))
	}
	return attrs
}

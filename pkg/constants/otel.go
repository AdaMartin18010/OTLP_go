// Package constants provides OpenTelemetry semantic convention constants.
//
// This file defines constants based on the OpenTelemetry Semantic Conventions:
// https://opentelemetry.io/docs/specs/semconv/
//
// These constants follow the OpenTelemetry specification for:
//   - Resource attributes
//   - Span attributes
//   - Metric attributes
//   - Log attributes
//   - Environment variable names
package constants

// ============================================================================
// Resource Attribute Keys (Semantic Conventions)
// ============================================================================

// Service attributes define the service producing telemetry.
const (
	// AttributeServiceName is the name of the service.
	// Examples: "shopping-cart", "payment-service"
	AttributeServiceName = "service.name"

	// AttributeServiceVersion is the version of the service.
	// Examples: "1.0.0", "2.3.1-beta"
	AttributeServiceVersion = "service.version"

	// AttributeServiceInstanceID is the unique instance ID of the service.
	// Examples: "service-01", "pod-abc-123"
	AttributeServiceInstanceID = "service.instance.id"

	// AttributeServiceNamespace is the namespace of the service.
	// Examples: "production", "staging"
	AttributeServiceNamespace = "service.namespace"

	// AttributeServiceHost is the host name of the service.
	AttributeServiceHost = "service.host"
)

// Telemetry SDK attributes define the SDK producing telemetry.
const (
	// AttributeTelemetrySDKName is the name of the telemetry SDK.
	// Examples: "opentelemetry", "OTLP_go"
	AttributeTelemetrySDKName = "telemetry.sdk.name"

	// AttributeTelemetrySDKLanguage is the language of the telemetry SDK.
	// Examples: "go", "java", "python"
	AttributeTelemetrySDKLanguage = "telemetry.sdk.language"

	// AttributeTelemetrySDKVersion is the version of the telemetry SDK.
	// Examples: "1.0.0", "2.3.1"
	AttributeTelemetrySDKVersion = "telemetry.sdk.version"
)

// Host attributes define the host machine.
const (
	// AttributeHostName is the host name.
	AttributeHostName = "host.name"

	// AttributeHostType is the host type.
	AttributeHostType = "host.type"

	// AttributeHostArch is the host architecture.
	// Examples: "x86_64", "arm64"
	AttributeHostArch = "host.arch"
)

// Process attributes define the process producing telemetry.
const (
	// AttributeProcessPID is the process ID.
	AttributeProcessPID = "process.pid"

	// AttributeProcessExecutableName is the executable name.
	AttributeProcessExecutableName = "process.executable.name"

	// AttributeProcessExecutablePath is the executable path.
	AttributeProcessExecutablePath = "process.executable.path"

	// AttributeProcessCommand is the full command.
	AttributeProcessCommand = "process.command"

	// AttributeProcessCommandLine is the command line.
	AttributeProcessCommandLine = "process.command_line"

	// AttributeProcessOwner is the process owner.
	AttributeProcessOwner = "process.owner"

	// AttributeProcessRuntimeName is the runtime name.
	// Examples: "go", "jvm"
	AttributeProcessRuntimeName = "process.runtime.name"

	// AttributeProcessRuntimeVersion is the runtime version.
	AttributeProcessRuntimeVersion = "process.runtime.version"

	// AttributeProcessRuntimeDescription is the runtime description.
	AttributeProcessRuntimeDescription = "process.runtime.description"
)

// Container attributes define the container environment.
const (
	// AttributeContainerID is the container ID.
	AttributeContainerID = "container.id"

	// AttributeContainerName is the container name.
	AttributeContainerName = "container.name"

	// AttributeContainerImageName is the container image name.
	AttributeContainerImageName = "container.image.name"

	// AttributeContainerImageTag is the container image tag.
	AttributeContainerImageTag = "container.image.tag"
)

// Kubernetes attributes define the Kubernetes environment.
const (
	// AttributeK8sClusterName is the Kubernetes cluster name.
	AttributeK8sClusterName = "k8s.cluster.name"

	// AttributeK8sNamespaceName is the Kubernetes namespace name.
	AttributeK8sNamespaceName = "k8s.namespace.name"

	// AttributeK8sPodName is the Kubernetes pod name.
	AttributeK8sPodName = "k8s.pod.name"

	// AttributeK8sPodUID is the Kubernetes pod UID.
	AttributeK8sPodUID = "k8s.pod.uid"

	// AttributeK8sDeploymentName is the Kubernetes deployment name.
	AttributeK8sDeploymentName = "k8s.deployment.name"

	// AttributeK8sNodeName is the Kubernetes node name.
	AttributeK8sNodeName = "k8s.node.name"
)

// Cloud attributes define the cloud provider environment.
const (
	// AttributeCloudProvider is the cloud provider.
	// Examples: "aws", "azure", "gcp"
	AttributeCloudProvider = "cloud.provider"

	// AttributeCloudAccountID is the cloud account ID.
	AttributeCloudAccountID = "cloud.account.id"

	// AttributeCloudRegion is the cloud region.
	// Examples: "us-east-1", "westeurope"
	AttributeCloudRegion = "cloud.region"

	// AttributeCloudAvailabilityZone is the cloud availability zone.
	AttributeCloudAvailabilityZone = "cloud.availability_zone"

	// AttributeCloudPlatform is the cloud platform.
	// Examples: "aws_ec2", "azure_vm", "gcp_compute_engine"
	AttributeCloudPlatform = "cloud.platform"
)

// ============================================================================
// HTTP Attributes
// ============================================================================

const (
	// AttributeHTTPMethod is the HTTP request method.
	// Examples: "GET", "POST", "PUT", "DELETE"
	AttributeHTTPMethod = "http.method"

	// AttributeHTTPURL is the full HTTP request URL.
	AttributeHTTPURL = "http.url"

	// AttributeHTTPHost is the HTTP host.
	AttributeHTTPHost = "http.host"

	// AttributeHTTPScheme is the HTTP scheme.
	// Examples: "http", "https"
	AttributeHTTPScheme = "http.scheme"

	// AttributeHTTPStatusCode is the HTTP response status code.
	AttributeHTTPStatusCode = "http.status_code"

	// AttributeHTTPRoute is the matched route template.
	// Examples: "/api/users/{id}"
	AttributeHTTPRoute = "http.route"

	// AttributeHTTPClientIP is the client IP address.
	AttributeHTTPClientIP = "http.client_ip"

	// AttributeHTTPUserAgent is the user agent string.
	AttributeHTTPUserAgent = "http.user_agent"

	// AttributeHTTPRequestContentLength is the request content length.
	AttributeHTTPRequestContentLength = "http.request_content_length"

	// AttributeHTTPResponseContentLength is the response content length.
	AttributeHTTPResponseContentLength = "http.response_content_length"

	// AttributeHTTPFlavor is the HTTP protocol version.
	// Examples: "1.1", "2.0"
	AttributeHTTPFlavor = "http.flavor"
)

// ============================================================================
// RPC Attributes
// ============================================================================

const (
	// AttributeRPCSystem is the RPC system.
	// Examples: "grpc", "java_rmi"
	AttributeRPCSystem = "rpc.system"

	// AttributeRPCService is the RPC service name.
	AttributeRPCService = "rpc.service"

	// AttributeRPCMethod is the RPC method name.
	AttributeRPCMethod = "rpc.method"

	// AttributeRPCGRPCStatusCode is the gRPC status code.
	AttributeRPCGRPCStatusCode = "rpc.grpc.status_code"
)

// ============================================================================
// Database Attributes
// ============================================================================

const (
	// AttributeDBSystem is the database system.
	// Examples: "mysql", "postgresql", "redis"
	AttributeDBSystem = "db.system"

	// AttributeDBConnectionString is the database connection string.
	AttributeDBConnectionString = "db.connection_string"

	// AttributeDBUser is the database user.
	AttributeDBUser = "db.user"

	// AttributeDBName is the database name.
	AttributeDBName = "db.name"

	// AttributeDBStatement is the database statement.
	AttributeDBStatement = "db.statement"

	// AttributeDBOperation is the database operation.
	// Examples: "SELECT", "INSERT", "UPDATE"
	AttributeDBOperation = "db.operation"
)

// ============================================================================
// Messaging Attributes
// ============================================================================

const (
	// AttributeMessagingSystem is the messaging system.
	// Examples: "kafka", "rabbitmq"
	AttributeMessagingSystem = "messaging.system"

	// AttributeMessagingDestination is the message destination name.
	AttributeMessagingDestination = "messaging.destination"

	// AttributeMessagingDestinationKind is the message destination kind.
	// Examples: "queue", "topic"
	AttributeMessagingDestinationKind = "messaging.destination_kind"

	// AttributeMessagingOperation is the messaging operation.
	// Examples: "publish", "receive", "process"
	AttributeMessagingOperation = "messaging.operation"

	// AttributeMessagingMessageID is the message ID.
	AttributeMessagingMessageID = "messaging.message_id"
)

// ============================================================================
// Span Kind Constants
// ============================================================================

// SpanKind represents the role of a span in a trace.
type SpanKind int

const (
	// SpanKindUnspecified indicates the span kind was not specified.
	SpanKindUnspecified SpanKind = 0

	// SpanKindInternal indicates an internal operation.
	SpanKindInternal SpanKind = 1

	// SpanKindServer indicates a server operation.
	SpanKindServer SpanKind = 2

	// SpanKindClient indicates a client operation.
	SpanKindClient SpanKind = 3

	// SpanKindProducer indicates a producer operation.
	SpanKindProducer SpanKind = 4

	// SpanKindConsumer indicates a consumer operation.
	SpanKindConsumer SpanKind = 5
)

// String returns the string representation of SpanKind.
func (k SpanKind) String() string {
	switch k {
	case SpanKindInternal:
		return "internal"
	case SpanKindServer:
		return "server"
	case SpanKindClient:
		return "client"
	case SpanKindProducer:
		return "producer"
	case SpanKindConsumer:
		return "consumer"
	default:
		return "unspecified"
	}
}

// ============================================================================
// Status Codes
// ============================================================================

// StatusCode represents the status of a span or operation.
type StatusCode int

const (
	// StatusCodeUnset indicates the status was not set.
	StatusCodeUnset StatusCode = 0

	// StatusCodeOK indicates the operation completed successfully.
	StatusCodeOK StatusCode = 1

	// StatusCodeError indicates an error occurred.
	StatusCodeError StatusCode = 2
)

// String returns the string representation of StatusCode.
func (c StatusCode) String() string {
	switch c {
	case StatusCodeOK:
		return "ok"
	case StatusCodeError:
		return "error"
	default:
		return "unset"
	}
}

// ============================================================================
// Severity Levels (Log)
// ============================================================================

// SeverityLevel represents the severity level of a log record.
type SeverityLevel int

const (
	// SeverityTrace represents TRACE level.
	SeverityTrace SeverityLevel = 1

	// SeverityDebug represents DEBUG level.
	SeverityDebug SeverityLevel = 5

	// SeverityInfo represents INFO level.
	SeverityInfo SeverityLevel = 9

	// SeverityWarn represents WARN level.
	SeverityWarn SeverityLevel = 13

	// SeverityError represents ERROR level.
	SeverityError SeverityLevel = 17

	// SeverityFatal represents FATAL level.
	SeverityFatal SeverityLevel = 21
)

// String returns the string representation of SeverityLevel.
func (s SeverityLevel) String() string {
	switch s {
	case SeverityTrace:
		return "TRACE"
	case SeverityDebug:
		return "DEBUG"
	case SeverityInfo:
		return "INFO"
	case SeverityWarn:
		return "WARN"
	case SeverityError:
		return "ERROR"
	case SeverityFatal:
		return "FATAL"
	default:
		return "UNKNOWN"
	}
}

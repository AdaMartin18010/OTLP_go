// Package constants provides default values for the OTLP Go SDK.
//
// This file defines default configuration values used throughout the SDK
// when explicit values are not provided.
//
// Usage:
//
//	timeout := config.Timeout
//	if timeout == 0 {
//	    timeout = constants.DefaultTimeout
//	}
package constants

import "time"

// ============================================================================
// SDK Default Values
// ============================================================================

const (
	// DefaultSDKName is the default name of the SDK.
	DefaultSDKName = SDKName

	// DefaultSDKVersion is the default version of the SDK.
	DefaultSDKVersion = SDKVersion

	// DefaultSDKLanguage is the default language of the SDK.
	DefaultSDKLanguage = SDKLanguage
)

// ============================================================================
// Exporter Default Values
// ============================================================================

const (
	// DefaultExporterProtocol is the default export protocol.
	DefaultExporterProtocol = OTLPProtocolGRPC

	// DefaultExporterEndpoint is the default export endpoint.
	DefaultExporterEndpoint = DefaultGRPCEndpoint

	// DefaultExporterCompression is the default compression type.
	DefaultExporterCompression = CompressionNone

	// DefaultExporterTimeout is the default export timeout.
	DefaultExporterTimeout = 10 * time.Second

	// DefaultExporterRetryEnabled is the default retry enabled state.
	DefaultExporterRetryEnabled = true
)

// ============================================================================
// Trace Default Values
// ============================================================================

const (
	// DefaultTracerName is the default tracer name.
	DefaultTracerName = "OTLP_go"

	// DefaultTracerVersion is the default tracer version.
	DefaultTracerVersion = SDKVersion

	// DefaultTracerSchemaURL is the default tracer schema URL.
	DefaultTracerSchemaURL = "https://opentelemetry.io/schemas/1.21.0"

	// DefaultSpanKind is the default span kind.
	DefaultSpanKind = SpanKindInternal

	// DefaultSpanStatus is the default span status.
	DefaultSpanStatus = StatusCodeUnset
)

// ============================================================================
// Metric Default Values
// ============================================================================

const (
	// DefaultMeterName is the default meter name.
	DefaultMeterName = "OTLP_go"

	// DefaultMeterVersion is the default meter version.
	DefaultMeterVersion = SDKVersion

	// DefaultMeterSchemaURL is the default meter schema URL.
	DefaultMeterSchemaURL = "https://opentelemetry.io/schemas/1.21.0"

	// DefaultMetricDescription is the default metric description.
	DefaultMetricDescription = ""

	// DefaultMetricUnit is the default metric unit.
	DefaultMetricUnit = "1"
)

// ============================================================================
// Log Default Values
// ============================================================================

const (
	// DefaultLoggerName is the default logger name.
	DefaultLoggerName = "OTLP_go"

	// DefaultLoggerVersion is the default logger version.
	DefaultLoggerVersion = SDKVersion

	// DefaultLoggerSchemaURL is the default logger schema URL.
	DefaultLoggerSchemaURL = "https://opentelemetry.io/schemas/1.21.0"

	// DefaultLogSeverity is the default log severity level.
	DefaultLogSeverity = SeverityInfo

	// DefaultLogBody is the default log body.
	DefaultLogBody = ""
)

// ============================================================================
// Resource Default Values
// ============================================================================

const (
	// DefaultResourceServiceName is the default service name.
	DefaultResourceServiceName = "unknown_service:go"

	// DefaultResourceServiceVersion is the default service version.
	DefaultResourceServiceVersion = "0.0.0"

	// DefaultResourceServiceNamespace is the default service namespace.
	DefaultResourceServiceNamespace = "default"

	// DefaultResourceServiceInstanceID is the default service instance ID.
	DefaultResourceServiceInstanceID = ""
)

// ============================================================================
// Batch Processor Default Values
// ============================================================================

const (
	// DefaultBatchQueueSize is the default batch queue size.
	DefaultBatchQueueSize = 2048

	// DefaultBatchExportTimeout is the default batch export timeout.
	DefaultBatchExportTimeout = 30 * time.Second
)

// ============================================================================
// Sampling Default Values
// ============================================================================

const (
	// DefaultSamplingRatio is the default sampling ratio (100%).
	DefaultSamplingRatio = 1.0

	// DefaultSamplingEnabled is the default sampling enabled state.
	DefaultSamplingEnabled = true
)

// ============================================================================
// Connection Default Values
// ============================================================================

const (
	// DefaultKeepAliveTime is the default keepalive time.
	DefaultKeepAliveTime = 10 * time.Second

	// DefaultKeepAliveTimeout is the default keepalive timeout.
	DefaultKeepAliveTimeout = 20 * time.Second

	// DefaultMaxIdleConns is the default maximum idle connections.
	DefaultMaxIdleConns = 100

	// DefaultMaxConnsPerHost is the default maximum connections per host.
	DefaultMaxConnsPerHost = 10

	// DefaultIdleConnTimeout is the default idle connection timeout.
	DefaultIdleConnTimeout = 90 * time.Second
)

// ============================================================================
// Retry Default Values
// ============================================================================

const (
	// DefaultRetryMaxAttempts is the default maximum retry attempts.
	DefaultRetryMaxAttempts = 3

	// DefaultRetryInitialBackoff is the default initial retry backoff.
	DefaultRetryInitialBackoff = 1 * time.Second

	// DefaultRetryMaxBackoff is the default maximum retry backoff.
	DefaultRetryMaxBackoff = 30 * time.Second

	// DefaultRetryBackoffMultiplier is the default retry backoff multiplier.
	DefaultRetryBackoffMultiplier = 2.0
)

// ============================================================================
// Security Default Values
// ============================================================================

const (
	// DefaultTLSEnabled is the default TLS enabled state.
	DefaultTLSEnabled = false

	// DefaultTLSSkipVerify is the default TLS skip verify state.
	DefaultTLSSkipVerify = false

	// DefaultTLSCertPath is the default TLS certificate path.
	DefaultTLSCertPath = ""

	// DefaultTLSKeyPath is the default TLS key path.
	DefaultTLSKeyPath = ""

	// DefaultTLSCAPath is the default TLS CA path.
	DefaultTLSCAPath = ""
)

// ============================================================================
// Attribute Default Values
// ============================================================================

const (
	// DefaultAttributeMaxCount is the default maximum number of attributes.
	DefaultAttributeMaxCount = 128

	// DefaultAttributeMaxKeyLength is the default maximum attribute key length.
	DefaultAttributeMaxKeyLength = 128

	// DefaultAttributeMaxValueLength is the default maximum attribute value length.
	DefaultAttributeMaxValueLength = 1024
)

// ============================================================================
// Event Default Values
// ============================================================================

const (
	// DefaultEventMaxCount is the default maximum number of events per span.
	DefaultEventMaxCount = 128

	// DefaultEventMaxAttributes is the default maximum event attributes.
	DefaultEventMaxAttributes = 128
)

// ============================================================================
// Link Default Values
// ============================================================================

const (
	// DefaultLinkMaxCount is the default maximum number of links per span.
	DefaultLinkMaxCount = 128

	// DefaultLinkMaxAttributes is the default maximum link attributes.
	DefaultLinkMaxAttributes = 128
)

// ============================================================================
// View Default Values
// ============================================================================

const (
	// DefaultViewAggregation is the default view aggregation.
	DefaultViewAggregation = "default"

	// DefaultViewTemporality is the default view temporality.
	DefaultViewTemporality = "cumulative"
)

// ============================================================================
// Propagator Default Values
// ============================================================================

const (
	// DefaultPropagatorTraceContext is the default trace context propagator.
	DefaultPropagatorTraceContext = "traceparent"

	// DefaultPropagatorBaggage is the default baggage propagator.
	DefaultPropagatorBaggage = "baggage"

	// DefaultPropagators is the list of default propagators.
	DefaultPropagators = "traceparent,baggage"
)

// ============================================================================
// Header Default Values
// ============================================================================

const (
	// DefaultUserAgent is the default user agent string.
	DefaultUserAgent = SDKName + "/" + SDKVersion

	// DefaultContentType is the default content type.
	DefaultContentType = ContentTypeProtobuf
)

// ============================================================================
// Schema Default Values
// ============================================================================

const (
	// DefaultSchemaURL is the default OpenTelemetry schema URL.
	DefaultSchemaURL = "https://opentelemetry.io/schemas/1.21.0"

	// DefaultSchemaVersion is the default schema version.
	DefaultSchemaVersion = "1.21.0"
)

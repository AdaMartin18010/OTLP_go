// Package constants provides commonly used constants for the OTLP Go SDK.
//
// This package defines:
//   - Default timeout values
//   - Header names
//   - Environment variable names
//   - Error codes
//
// Usage:
//
//	ctx, cancel := context.WithTimeout(ctx, constants.DefaultTimeout)
//	defer cancel()
//
// Stability: Stable
// Compliance: OpenTelemetry Specification v1.42.0
package constants

import "time"

// ============================================================================
// SDK Version and Metadata
// ============================================================================

const (
	// SDKName is the name of this SDK.
	SDKName = "OTLP_go"

	// SDKVersion is the current version of this SDK.
	SDKVersion = "1.0.0"

	// SDKLanguage is the programming language of this SDK.
	SDKLanguage = "go"
)

// ============================================================================
// Protocol and Content Type Constants
// ============================================================================

const (
	// ContentTypeJSON is the content type for JSON data.
	ContentTypeJSON = "application/json"

	// ContentTypeProtobuf is the content type for Protocol Buffers data.
	ContentTypeProtobuf = "application/x-protobuf"

	// ContentTypeGRPC is the content type for gRPC data.
	ContentTypeGRPC = "application/grpc"

	// ContentTypeOctetStream is the content type for binary data.
	ContentTypeOctetStream = "application/octet-stream"
)

// ============================================================================
// OTLP Protocol Constants
// ============================================================================

const (
	// OTLPProtocolGRPC is the gRPC protocol identifier.
	OTLPProtocolGRPC = "grpc"

	// OTLPProtocolHTTP is the HTTP protocol identifier.
	OTLPProtocolHTTP = "http"

	// OTLPProtocolHTTPProtobuf is the HTTP/Protobuf protocol identifier.
	OTLPProtocolHTTPProtobuf = "http/protobuf"
)

// ============================================================================
// Default Endpoint Constants
// ============================================================================

const (
	// DefaultGRPCPort is the default OTLP gRPC receiver port.
	DefaultGRPCPort = 4317

	// DefaultHTTPPort is the default OTLP HTTP receiver port.
	DefaultHTTPPort = 4318

	// DefaultGRPCEndpoint is the default OTLP gRPC endpoint.
	DefaultGRPCEndpoint = "localhost:4317"

	// DefaultHTTPEndpoint is the default OTLP HTTP endpoint.
	DefaultHTTPEndpoint = "localhost:4318"
)

// ============================================================================
// HTTP Header Constants
// ============================================================================

const (
	// HeaderContentType is the HTTP header for content type.
	HeaderContentType = "Content-Type"

	// HeaderAccept is the HTTP header for accept type.
	HeaderAccept = "Accept"

	// HeaderAuthorization is the HTTP header for authorization.
	HeaderAuthorization = "Authorization"

	// HeaderUserAgent is the HTTP header for user agent.
	HeaderUserAgent = "User-Agent"

	// HeaderXScopeOrgID is the HTTP header for multi-tenant organization ID.
	HeaderXScopeOrgID = "X-Scope-OrgID"
)

// ============================================================================
// Timeout and Duration Constants
// ============================================================================

const (
	// DefaultTimeout is the default timeout for operations.
	DefaultTimeout = 10 * time.Second

	// DefaultConnectTimeout is the default timeout for connection establishment.
	DefaultConnectTimeout = 5 * time.Second

	// DefaultExportTimeout is the default timeout for export operations.
	DefaultExportTimeout = 30 * time.Second

	// DefaultBatchTimeout is the default timeout for batch operations.
	DefaultBatchTimeout = time.Second

	// DefaultShutdownTimeout is the default timeout for shutdown operations.
	DefaultShutdownTimeout = 30 * time.Second

	// DefaultRetryDelay is the default delay between retries.
	DefaultRetryDelay = 1 * time.Second

	// DefaultMaxRetryDelay is the maximum delay between retries.
	DefaultMaxRetryDelay = 30 * time.Second
)

// ============================================================================
// Retry and Backoff Constants
// ============================================================================

const (
	// DefaultMaxRetries is the default maximum number of retries.
	DefaultMaxRetries = 3

	// DefaultBackoffMultiplier is the default multiplier for exponential backoff.
	DefaultBackoffMultiplier = 2.0

	// DefaultRetryableStatusCodes contains HTTP status codes that should trigger a retry.
	// These include: 429 (Too Many Requests), 502 (Bad Gateway), 503 (Service Unavailable), 504 (Gateway Timeout)
	DefaultRetryableStatusCodes = "429,502,503,504"
)

// ============================================================================
// Buffer and Batch Constants
// ============================================================================

const (
	// DefaultBatchSize is the default batch size for exports.
	DefaultBatchSize = 512

	// DefaultMaxQueueSize is the default maximum queue size.
	DefaultMaxQueueSize = 2048

	// DefaultMaxExportBatchSize is the default maximum export batch size.
	DefaultMaxExportBatchSize = 512

	// DefaultBufferSize is the default buffer size for operations.
	DefaultBufferSize = 4096
)

// ============================================================================
// Compression Constants
// ============================================================================

const (
	// CompressionNone represents no compression.
	CompressionNone = "none"

	// CompressionGzip represents gzip compression.
	CompressionGzip = "gzip"

	// CompressionZstd represents zstd compression.
	CompressionZstd = "zstd"
)

// ============================================================================
// Attribute and Metadata Limits
// ============================================================================

const (
	// DefaultMaxAttributes is the default maximum number of attributes.
	DefaultMaxAttributes = 128

	// DefaultMaxAttributeLength is the default maximum length of an attribute value.
	DefaultMaxAttributeLength = 1024

	// DefaultMaxAttributeKeyLength is the default maximum length of an attribute key.
	DefaultMaxAttributeKeyLength = 128

	// DefaultMaxEvents is the default maximum number of events per span.
	DefaultMaxEvents = 128

	// DefaultMaxLinks is the default maximum number of links per span.
	DefaultMaxLinks = 128

	// DefaultMaxEventAttributes is the default maximum number of attributes per event.
	DefaultMaxEventAttributes = 128

	// DefaultMaxLinkAttributes is the default maximum number of attributes per link.
	DefaultMaxLinkAttributes = 128
)

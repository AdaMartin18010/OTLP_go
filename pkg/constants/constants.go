// Package constants provides common constants used across the OTLP SDK.
package constants

import "time"

// Common timeout values
const (
	DefaultTimeout    = 30 * time.Second
	ShortTimeout      = 5 * time.Second
	ConnectionTimeout = 10 * time.Second
)

// Common sizes
const (
	DefaultBatchSize  = 512
	DefaultQueueSize  = 2048
	DefaultBufferSize = 1024
)

// Common retry settings
const (
	DefaultMaxRetries = 3
	DefaultRetryDelay = 1 * time.Second
	MaxRetryDelay     = 10 * time.Second
)

// Package security provides security-related utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - TLS configuration helpers
//   - Certificate management
//   - Authentication handlers
//   - Security header utilities
//
// Example usage:
//
//	tlsConfig, err := security.NewTLSConfig(
//	    security.WithCertFile("cert.pem"),
//	    security.WithKeyFile("key.pem"),
//	    security.WithCAFile("ca.pem"),
//	)
package security

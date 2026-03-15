// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"crypto/tls"
	"crypto/x509"
	"fmt"
	"os"
)

// TLSVersion represents the minimum TLS version to use.
type TLSVersion uint16

const (
	// TLSVersion1_2 is the minimum TLS 1.2 version.
	TLSVersion1_2 TLSVersion = tls.VersionTLS12
	// TLSVersion1_3 is the minimum TLS 1.3 version.
	TLSVersion1_3 TLSVersion = tls.VersionTLS13
)

// TLSConfig holds configuration options for TLS connections.
type TLSConfig struct {
	CertFile       string
	KeyFile        string
	CAFile         string
	MinVersion     TLSVersion
	InsecureSkip   bool
	ServerName     string
	CipherSuites   []uint16
}

// TLSOption is a functional option for configuring TLS.
type TLSOption func(*TLSConfig)

// WithCertFile sets the certificate file path.
func WithCertFile(path string) TLSOption {
	return func(c *TLSConfig) {
		c.CertFile = path
	}
}

// WithKeyFile sets the private key file path.
func WithKeyFile(path string) TLSOption {
	return func(c *TLSConfig) {
		c.KeyFile = path
	}
}

// WithCAFile sets the CA certificate file path.
func WithCAFile(path string) TLSOption {
	return func(c *TLSConfig) {
		c.CAFile = path
	}
}

// WithMinVersion sets the minimum TLS version.
func WithMinVersion(version TLSVersion) TLSOption {
	return func(c *TLSConfig) {
		c.MinVersion = version
	}
}

// WithInsecureSkipVerify controls whether certificate verification is skipped.
// This should only be used in development/testing environments.
func WithInsecureSkipVerify(skip bool) TLSOption {
	return func(c *TLSConfig) {
		c.InsecureSkip = skip
	}
}

// WithServerName sets the server name for SNI.
func WithServerName(name string) TLSOption {
	return func(c *TLSConfig) {
		c.ServerName = name
	}
}

// WithCipherSuites sets the allowed cipher suites.
func WithCipherSuites(suites []uint16) TLSOption {
	return func(c *TLSConfig) {
		c.CipherSuites = suites
	}
}

// NewTLSConfig creates a new TLS configuration with the provided options.
// By default, it enforces TLS 1.2 or higher for security.
//
// Example:
//
//	tlsConfig, err := security.NewTLSConfig(
//	    security.WithCertFile("client.crt"),
//	    security.WithKeyFile("client.key"),
//	    security.WithCAFile("ca.crt"),
//	    security.WithMinVersion(security.TLSVersion1_3),
//	)
//	if err != nil {
//	    log.Fatal(err)
//	}
func NewTLSConfig(opts ...TLSOption) (*tls.Config, error) {
	config := &TLSConfig{
		MinVersion: TLSVersion1_2,
	}

	for _, opt := range opts {
		opt(config)
	}

	tlsConfig := &tls.Config{
		MinVersion:         uint16(config.MinVersion),
		InsecureSkipVerify: config.InsecureSkip,
		ServerName:         config.ServerName,
	}

	// Set secure cipher suites if not provided and using TLS 1.2
	if config.MinVersion == TLSVersion1_2 && len(config.CipherSuites) == 0 {
		tlsConfig.CipherSuites = getSecureCipherSuites()
	}

	// Load client certificate if provided
	if config.CertFile != "" && config.KeyFile != "" {
		cert, err := tls.LoadX509KeyPair(config.CertFile, config.KeyFile)
		if err != nil {
			return nil, fmt.Errorf("failed to load client certificate: %w", err)
		}
		tlsConfig.Certificates = []tls.Certificate{cert}
	}

	// Load CA certificate if provided
	if config.CAFile != "" {
		caCert, err := os.ReadFile(config.CAFile)
		if err != nil {
			return nil, fmt.Errorf("failed to read CA file: %w", err)
		}

		caCertPool := x509.NewCertPool()
		if !caCertPool.AppendCertsFromPEM(caCert) {
			return nil, fmt.Errorf("failed to parse CA certificate")
		}
		tlsConfig.RootCAs = caCertPool
	}

	return tlsConfig, nil
}

// getSecureCipherSuites returns a list of secure cipher suites for TLS 1.2.
// These cipher suites provide forward secrecy and are considered secure.
func getSecureCipherSuites() []uint16 {
	return []uint16{
		tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
		tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
		tls.TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
		tls.TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
		tls.TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
		tls.TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
	}
}

// DefaultTLSConfig returns a default secure TLS configuration.
// This configuration enforces TLS 1.2 or higher with secure cipher suites.
//
// Example:
//
//	tlsConfig := security.DefaultTLSConfig()
//	// Use with HTTP client or gRPC connection
func DefaultTLSConfig() *tls.Config {
	return &tls.Config{
		MinVersion:   tls.VersionTLS12,
		CipherSuites: getSecureCipherSuites(),
	}
}

// ValidateTLSConfig validates that the TLS configuration meets security requirements.
// Returns an error if the configuration is insecure.
func ValidateTLSConfig(config *tls.Config) error {
	if config == nil {
		return fmt.Errorf("TLS config is nil")
	}

	if config.MinVersion < tls.VersionTLS12 {
		return fmt.Errorf("TLS version must be at least 1.2, got %d", config.MinVersion)
	}

	if config.InsecureSkipVerify {
		return fmt.Errorf("InsecureSkipVerify is enabled, which is not secure for production")
	}

	return nil
}

// IsSecure checks if the TLS configuration is considered secure.
func IsSecure(config *tls.Config) bool {
	return ValidateTLSConfig(config) == nil
}

// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"math/big"
	"net"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func generateTestCert(t *testing.T) (certFile, keyFile, caFile string) {
	t.Helper()

	tempDir := t.TempDir()

	// Generate CA key
	caKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)

	// Generate CA cert
	caTemplate := &x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject: pkix.Name{
			Organization: []string{"Test CA"},
		},
		NotBefore:             time.Now(),
		NotAfter:              time.Now().Add(24 * time.Hour),
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
		BasicConstraintsValid: true,
		IsCA:                  true,
	}

	caCertDER, err := x509.CreateCertificate(rand.Reader, caTemplate, caTemplate, &caKey.PublicKey, caKey)
	require.NoError(t, err)

	// Generate server key
	serverKey, err := rsa.GenerateKey(rand.Reader, 2048)
	require.NoError(t, err)

	// Generate server cert
	serverTemplate := &x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject: pkix.Name{
			Organization: []string{"Test Server"},
		},
		NotBefore:    time.Now(),
		NotAfter:     time.Now().Add(24 * time.Hour),
		KeyUsage:     x509.KeyUsageDigitalSignature | x509.KeyUsageKeyEncipherment,
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
		IPAddresses:  []net.IP{{127, 0, 0, 1}},
	}

	serverCertDER, err := x509.CreateCertificate(rand.Reader, serverTemplate, caTemplate, &serverKey.PublicKey, caKey)
	require.NoError(t, err)

	// Write files
	caFile = filepath.Join(tempDir, "ca.pem")
	caFileHandle, err := os.Create(caFile)
	require.NoError(t, err)
	defer caFileHandle.Close()
	err = pem.Encode(caFileHandle, &pem.Block{Type: "CERTIFICATE", Bytes: caCertDER})
	require.NoError(t, err)

	certFile = filepath.Join(tempDir, "server.crt")
	certFileHandle, err := os.Create(certFile)
	require.NoError(t, err)
	defer certFileHandle.Close()
	err = pem.Encode(certFileHandle, &pem.Block{Type: "CERTIFICATE", Bytes: serverCertDER})
	require.NoError(t, err)

	keyFile = filepath.Join(tempDir, "server.key")
	keyFileHandle, err := os.Create(keyFile)
	require.NoError(t, err)
	defer keyFileHandle.Close()
	err = pem.Encode(keyFileHandle, &pem.Block{Type: "RSA PRIVATE KEY", Bytes: x509.MarshalPKCS1PrivateKey(serverKey)})
	require.NoError(t, err)

	return certFile, keyFile, caFile
}

func TestNewTLSConfig(t *testing.T) {
	certFile, keyFile, caFile := generateTestCert(t)

	tests := []struct {
		name      string
		opts      []TLSOption
		wantErr   bool
		errMsg    string
		checkFunc func(t *testing.T, config *tls.Config)
	}{
		{
			name: "default config",
			opts: nil,
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.Equal(t, uint16(tls.VersionTLS12), config.MinVersion)
				assert.NotNil(t, config.CipherSuites)
			},
		},
		{
			name: "with TLS 1.3",
			opts: []TLSOption{WithMinVersion(TLSVersion1_3)},
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.Equal(t, uint16(tls.VersionTLS13), config.MinVersion)
			},
		},
		{
			name: "with certificate",
			opts: []TLSOption{
				WithCertFile(certFile),
				WithKeyFile(keyFile),
			},
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.Len(t, config.Certificates, 1)
			},
		},
		{
			name: "with CA",
			opts: []TLSOption{WithCAFile(caFile)},
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.NotNil(t, config.RootCAs)
			},
		},
		{
			name:    "with invalid cert file",
			opts:    []TLSOption{WithCertFile("nonexistent.crt"), WithKeyFile(keyFile)},
			wantErr: true,
			errMsg:  "failed to load client certificate",
		},
		{
			name:    "with invalid CA file",
			opts:    []TLSOption{WithCAFile("nonexistent.pem")},
			wantErr: true,
			errMsg:  "failed to read CA file",
		},
		{
			name: "with server name",
			opts: []TLSOption{WithServerName("example.com")},
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.Equal(t, "example.com", config.ServerName)
			},
		},
		{
			name: "with insecure skip",
			opts: []TLSOption{WithInsecureSkipVerify(true)},
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.True(t, config.InsecureSkipVerify)
			},
		},
		{
			name: "with custom cipher suites",
			opts: []TLSOption{
				WithMinVersion(TLSVersion1_2),
				WithCipherSuites([]uint16{tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384}),
			},
			checkFunc: func(t *testing.T, config *tls.Config) {
				assert.Equal(t, []uint16{tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384}, config.CipherSuites)
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			config, err := NewTLSConfig(tt.opts...)
			if tt.wantErr {
				assert.Error(t, err)
				if tt.errMsg != "" {
					assert.Contains(t, err.Error(), tt.errMsg)
				}
			} else {
				assert.NoError(t, err)
				assert.NotNil(t, config)
				if tt.checkFunc != nil {
					tt.checkFunc(t, config)
				}
			}
		})
	}
}

func TestDefaultTLSConfig(t *testing.T) {
	config := DefaultTLSConfig()

	assert.NotNil(t, config)
	assert.Equal(t, uint16(tls.VersionTLS12), config.MinVersion)
	assert.NotNil(t, config.CipherSuites)
	assert.Greater(t, len(config.CipherSuites), 0)
}

func TestValidateTLSConfig(t *testing.T) {
	tests := []struct {
		name    string
		config  *tls.Config
		wantErr bool
		errMsg  string
	}{
		{
			name:    "nil config",
			config:  nil,
			wantErr: true,
			errMsg:  "TLS config is nil",
		},
		{
			name: "valid TLS 1.2 config",
			config: &tls.Config{
				MinVersion:         tls.VersionTLS12,
				InsecureSkipVerify: false,
			},
			wantErr: false,
		},
		{
			name: "valid TLS 1.3 config",
			config: &tls.Config{
				MinVersion:         tls.VersionTLS13,
				InsecureSkipVerify: false,
			},
			wantErr: false,
		},
		{
			name: "insecure TLS 1.1",
			config: &tls.Config{
				MinVersion:         tls.VersionTLS11,
				InsecureSkipVerify: false,
			},
			wantErr: true,
			errMsg:  "TLS version must be at least 1.2",
		},
		{
			name: "insecure skip verify",
			config: &tls.Config{
				MinVersion:         tls.VersionTLS12,
				InsecureSkipVerify: true,
			},
			wantErr: true,
			errMsg:  "InsecureSkipVerify is enabled",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := ValidateTLSConfig(tt.config)
			if tt.wantErr {
				assert.Error(t, err)
				if tt.errMsg != "" {
					assert.Contains(t, err.Error(), tt.errMsg)
				}
			} else {
				assert.NoError(t, err)
			}
		})
	}
}

func TestIsSecure(t *testing.T) {
	tests := []struct {
		name   string
		config *tls.Config
		secure bool
	}{
		{
			name:   "nil config",
			config: nil,
			secure: false,
		},
		{
			name: "secure config",
			config: &tls.Config{
				MinVersion:         tls.VersionTLS12,
				InsecureSkipVerify: false,
			},
			secure: true,
		},
		{
			name: "insecure config",
			config: &tls.Config{
				MinVersion:         tls.VersionTLS11,
				InsecureSkipVerify: false,
			},
			secure: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equal(t, tt.secure, IsSecure(tt.config))
		})
	}
}

func TestGetSecureCipherSuites(t *testing.T) {
	suites := getSecureCipherSuites()

	assert.NotNil(t, suites)
	assert.Greater(t, len(suites), 0)

	// Verify all cipher suites are valid
	for _, suite := range suites {
		assert.Greater(t, suite, uint16(0))
	}
}

func TestTLSVersionConstantValues(t *testing.T) {
	assert.Equal(t, uint16(tls.VersionTLS12), uint16(TLSVersion1_2))
	assert.Equal(t, uint16(tls.VersionTLS13), uint16(TLSVersion1_3))
}

// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"context"
	"fmt"
	"net/http"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestSecureString(t *testing.T) {
	tests := []struct {
		name     string
		value    string
		expected string
	}{
		{
			name:     "normal value",
			value:    "secret-password-123",
			expected: "se****23",
		},
		{
			name:     "short value",
			value:    "ab",
			expected: "****",
		},
		{
			name:     "exactly 4 chars",
			value:    "abcd",
			expected: "****",
		},
		{
			name:     "5 chars",
			value:    "abcde",
			expected: "ab*de",
		},
		{
			name:     "empty value",
			value:    "",
			expected: "****",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ss := NewSecureString(tt.value)
			assert.Equal(t, tt.expected, ss.String())
			assert.Equal(t, tt.value, ss.Value())
			assert.Equal(t, tt.value == "", ss.IsEmpty())
		})
	}
}

func TestAPIKeyAuth(t *testing.T) {
	t.Run("valid credentials", func(t *testing.T) {
		auth := NewAPIKeyAuth("my-api-key-12345", "X-API-Key")

		header, err := auth.GetAuthHeader()
		require.NoError(t, err)
		assert.Equal(t, "my-api-key-12345", header)

		assert.Equal(t, AuthMethodAPIKey, auth.GetAuthMethod())
		assert.Equal(t, "X-API-Key", auth.GetHeaderKey())
		assert.NoError(t, auth.Validate())
	})

	t.Run("empty api key", func(t *testing.T) {
		auth := NewAPIKeyAuth("", "X-API-Key")

		_, err := auth.GetAuthHeader()
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "API key is empty")
		assert.Error(t, auth.Validate())
	})

	t.Run("empty header key", func(t *testing.T) {
		auth := NewAPIKeyAuth("my-api-key", "")

		assert.Error(t, auth.Validate())
	})
}

func TestBearerAuth(t *testing.T) {
	t.Run("valid static token", func(t *testing.T) {
		auth := NewBearerAuth("my-bearer-token")

		header, err := auth.GetAuthHeader()
		require.NoError(t, err)
		assert.Equal(t, "Bearer my-bearer-token", header)

		assert.Equal(t, AuthMethodBearer, auth.GetAuthMethod())
		assert.NoError(t, auth.Validate())
	})

	t.Run("empty token", func(t *testing.T) {
		auth := NewBearerAuth("")

		_, err := auth.GetAuthHeader()
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "bearer token is empty")
		assert.Error(t, auth.Validate())
	})

	t.Run("with provider", func(t *testing.T) {
		mockProvider := &mockTokenProvider{
			token: "dynamic-token",
		}
		auth := NewBearerAuthWithProvider(mockProvider)

		// Provider returns placeholder for static check
		assert.Equal(t, "<dynamic>", auth.getToken())
		assert.Equal(t, AuthMethodBearer, auth.GetAuthMethod())
	})

	t.Run("refresh token without provider", func(t *testing.T) {
		auth := NewBearerAuth("static-token")

		err := auth.RefreshToken(context.Background())
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "no token provider configured")
	})
}

type mockTokenProvider struct {
	token string
	err   error
}

func (m *mockTokenProvider) GetToken(ctx context.Context) (string, error) {
	return m.token, m.err
}

func (m *mockTokenProvider) RefreshToken(ctx context.Context) error {
	return m.err
}

func TestBasicAuth(t *testing.T) {
	tests := []struct {
		name     string
		username string
		password string
		wantErr  bool
		errMsg   string
	}{
		{
			name:     "valid credentials",
			username: "user",
			password: "pass",
			wantErr:  false,
		},
		{
			name:     "empty username",
			username: "",
			password: "pass",
			wantErr:  true,
			errMsg:   "username is empty",
		},
		{
			name:     "empty password",
			username: "user",
			password: "",
			wantErr:  false, // Basic auth doesn't fail on empty password
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			auth := NewBasicAuth(tt.username, tt.password)

			header, err := auth.GetAuthHeader()
			if tt.wantErr {
				assert.Error(t, err)
				if tt.errMsg != "" {
					assert.Contains(t, err.Error(), tt.errMsg)
				}
			} else {
				require.NoError(t, err)
				assert.Contains(t, header, "Basic ")
			}

			assert.Equal(t, AuthMethodBasic, auth.GetAuthMethod())
		})
	}
}

func TestBasicAuthValidate(t *testing.T) {
	tests := []struct {
		name     string
		username string
		password string
		wantErr  bool
	}{
		{
			name:     "valid",
			username: "user",
			password: "pass",
			wantErr:  false,
		},
		{
			name:     "empty username",
			username: "",
			password: "pass",
			wantErr:  true,
		},
		{
			name:     "empty password",
			username: "user",
			password: "",
			wantErr:  true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			auth := NewBasicAuth(tt.username, tt.password)
			err := auth.Validate()
			if tt.wantErr {
				assert.Error(t, err)
			} else {
				assert.NoError(t, err)
			}
		})
	}
}

func TestAuthInterceptor(t *testing.T) {
	t.Run("API key auth", func(t *testing.T) {
		auth := NewAPIKeyAuth("secret-key", "X-API-Key")
		interceptor := NewAuthInterceptor(auth)

		req, err := http.NewRequest("GET", "http://example.com", nil)
		require.NoError(t, err)

		err = interceptor.Intercept(req)
		require.NoError(t, err)

		assert.Equal(t, "secret-key", req.Header.Get("X-API-Key"))
	})

	t.Run("Bearer auth", func(t *testing.T) {
		auth := NewBearerAuth("my-token")
		interceptor := NewAuthInterceptor(auth)

		req, err := http.NewRequest("GET", "http://example.com", nil)
		require.NoError(t, err)

		err = interceptor.Intercept(req)
		require.NoError(t, err)

		assert.Equal(t, "Bearer my-token", req.Header.Get("Authorization"))
	})

	t.Run("Basic auth", func(t *testing.T) {
		auth := NewBasicAuth("user", "pass")
		interceptor := NewAuthInterceptor(auth)

		req, err := http.NewRequest("GET", "http://example.com", nil)
		require.NoError(t, err)

		err = interceptor.Intercept(req)
		require.NoError(t, err)

		authHeader := req.Header.Get("Authorization")
		assert.Contains(t, authHeader, "Basic ")
	})

	t.Run("nil provider", func(t *testing.T) {
		interceptor := NewAuthInterceptor(nil)

		req, err := http.NewRequest("GET", "http://example.com", nil)
		require.NoError(t, err)

		err = interceptor.Intercept(req)
		assert.NoError(t, err)
		assert.Empty(t, req.Header.Get("Authorization"))
	})

	t.Run("invalid credentials", func(t *testing.T) {
		auth := NewAPIKeyAuth("", "X-API-Key")
		interceptor := NewAuthInterceptor(auth)

		req, err := http.NewRequest("GET", "http://example.com", nil)
		require.NoError(t, err)

		err = interceptor.Intercept(req)
		assert.Error(t, err)
		assert.Contains(t, err.Error(), "invalid auth credentials")
	})
}

func TestHashString(t *testing.T) {
	input := "test-input"
	hash1 := HashString(input)
	hash2 := HashString(input)

	// Same input should produce same hash
	assert.Equal(t, hash1, hash2)
	assert.Len(t, hash1, 64) // SHA-256 hex is 64 chars

	// Different input should produce different hash
	hash3 := HashString("different-input")
	assert.NotEqual(t, hash1, hash3)
}

func TestHashStringWithSalt(t *testing.T) {
	input := "test-input"
	salt := "my-salt"

	hash1 := HashStringWithSalt(input, salt)
	hash2 := HashStringWithSalt(input, salt)

	// Same input and salt should produce same hash
	assert.Equal(t, hash1, hash2)

	// Different salt should produce different hash
	hash3 := HashStringWithSalt(input, "different-salt")
	assert.NotEqual(t, hash1, hash3)

	// Different input should produce different hash
	hash4 := HashStringWithSalt("different-input", salt)
	assert.NotEqual(t, hash1, hash4)
}

func TestGenerateSalt(t *testing.T) {
	salt1 := GenerateSalt()
	time.Sleep(1 * time.Nanosecond)
	salt2 := GenerateSalt()

	assert.NotEmpty(t, salt1)
	assert.NotEmpty(t, salt2)
	assert.NotEqual(t, salt1, salt2) // Should be unique due to timestamp
}

func TestValidateAPIKey(t *testing.T) {
	tests := []struct {
		name    string
		key     string
		wantErr bool
		errMsg  string
	}{
		{
			name:    "valid key",
			key:     "a-very-long-and-secure-api-key-123456",
			wantErr: false,
		},
		{
			name:    "empty key",
			key:     "",
			wantErr: true,
			errMsg:  "API key cannot be empty",
		},
		{
			name:    "short key",
			key:     "short",
			wantErr: true,
			errMsg:  "API key must be at least 16 characters long",
		},
		{
			name:    "weak pattern - 123",
			key:     "akeywith123init-abc123xyz",
			wantErr: true,
			errMsg:  "weak pattern",
		},
		{
			name:    "weak pattern - password",
			key:     "this-is-a-password-for-test",
			wantErr: true,
			errMsg:  "weak pattern",
		},
		{
			name:    "weak pattern - test",
			key:     "this-is-a-test-key-for-api",
			wantErr: true,
			errMsg:  "weak pattern",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			err := ValidateAPIKey(tt.key)
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

func TestSecureCompare(t *testing.T) {
	assert.True(t, SecureCompare("same", "same"))
	assert.False(t, SecureCompare("different", "values"))
	assert.True(t, SecureCompare("", ""))
	assert.False(t, SecureCompare("a", ""))
	assert.False(t, SecureCompare("", "a"))
}

func TestAuthMiddleware(t *testing.T) {
	auth := NewAPIKeyAuth("secret", "X-API-Key")
	middleware := AuthMiddleware(auth)

	handler := middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
	}))

	t.Run("valid auth", func(t *testing.T) {
		req, _ := http.NewRequest("GET", "/test", nil)
		rr := &mockResponseWriter{}
		handler.ServeHTTP(rr, req)
		assert.Equal(t, http.StatusOK, rr.statusCode)
	})

	t.Run("invalid auth", func(t *testing.T) {
		invalidAuth := NewAPIKeyAuth("", "X-API-Key")
		invalidMiddleware := AuthMiddleware(invalidAuth)
		invalidHandler := invalidMiddleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.WriteHeader(http.StatusOK)
		}))

		req, _ := http.NewRequest("GET", "/test", nil)
		rr := &mockResponseWriter{}
		invalidHandler.ServeHTTP(rr, req)
		assert.Equal(t, http.StatusUnauthorized, rr.statusCode)
	})
}

func TestAuthContext(t *testing.T) {
	ctx := context.Background()

	// No auth in context
	method, ok := GetAuthMethodFromContext(ctx)
	assert.False(t, ok)
	assert.Empty(t, method)

	// Add auth to context
	ctx = WithAuthContext(ctx, AuthMethodBearer)

	// Get auth from context
	method, ok = GetAuthMethodFromContext(ctx)
	assert.True(t, ok)
	assert.Equal(t, AuthMethodBearer, method)
}

type mockResponseWriter struct {
	header     http.Header
	statusCode int
	body       []byte
}

func (m *mockResponseWriter) Header() http.Header {
	if m.header == nil {
		m.header = make(http.Header)
	}
	return m.header
}

func (m *mockResponseWriter) Write(b []byte) (int, error) {
	m.body = append(m.body, b...)
	return len(b), nil
}

func (m *mockResponseWriter) WriteHeader(code int) {
	m.statusCode = code
}

// Note: Missing net import in test file, let's verify and fix
func init() {
	fmt.Println("auth_test initialized")
}

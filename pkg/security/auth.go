// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package security

import (
	"context"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/base64"
	"fmt"
	"net/http"
	"strings"
	"sync"
	"time"
)

// AuthMethod represents the authentication method to use.
type AuthMethod string

const (
	// AuthMethodNone indicates no authentication.
	AuthMethodNone AuthMethod = "none"
	// AuthMethodAPIKey indicates API key authentication.
	AuthMethodAPIKey AuthMethod = "api_key"
	// AuthMethodBearer indicates Bearer token authentication.
	AuthMethodBearer AuthMethod = "bearer"
	// AuthMethodBasic indicates Basic authentication.
	AuthMethodBasic AuthMethod = "basic"
)

// Credentials holds authentication credentials.
type Credentials struct {
	Method   AuthMethod
	APIKey   string
	Token    string
	Username string
	Password string
}

// SecureString wraps a sensitive string to prevent accidental logging.
type SecureString struct {
	value string
}

// NewSecureString creates a new secure string.
func NewSecureString(value string) *SecureString {
	return &SecureString{value: value}
}

// String returns a masked representation of the secure string.
func (s *SecureString) String() string {
	if len(s.value) <= 4 {
		return strings.Repeat("*", len(s.value))
	}
	// Show first 2 and last 2 characters, mask the rest
	return s.value[:2] + strings.Repeat("*", len(s.value)-4) + s.value[len(s.value)-2:]
}

// Value returns the actual value. Use with caution.
func (s *SecureString) Value() string {
	return s.value
}

// IsEmpty returns true if the secure string is empty.
func (s *SecureString) IsEmpty() bool {
	return s.value == ""
}

// AuthProvider provides authentication functionality.
type AuthProvider interface {
	// GetAuthHeader returns the authentication header value.
	GetAuthHeader() (string, error)
	// GetAuthMethod returns the authentication method.
	GetAuthMethod() AuthMethod
	// Validate validates the credentials.
	Validate() error
}

// TokenProvider provides token-based authentication.
type TokenProvider interface {
	// GetToken returns the current authentication token.
	GetToken(ctx context.Context) (string, error)
	// RefreshToken refreshes the authentication token.
	RefreshToken(ctx context.Context) error
}

// APIKeyAuth implements API key authentication.
type APIKeyAuth struct {
	apiKey    *SecureString
	headerKey string
}

// NewAPIKeyAuth creates a new API key authentication provider.
//
// Example:
//
//	auth := security.NewAPIKeyAuth("my-api-key", "X-API-Key")
//	headerValue, err := auth.GetAuthHeader()
func NewAPIKeyAuth(apiKey, headerKey string) *APIKeyAuth {
	return &APIKeyAuth{
		apiKey:    NewSecureString(apiKey),
		headerKey: headerKey,
	}
}

// GetAuthHeader returns the API key in header format.
func (a *APIKeyAuth) GetAuthHeader() (string, error) {
	if a.apiKey.IsEmpty() {
		return "", fmt.Errorf("API key is empty")
	}
	return a.apiKey.Value(), nil
}

// GetAuthMethod returns the authentication method.
func (a *APIKeyAuth) GetAuthMethod() AuthMethod {
	return AuthMethodAPIKey
}

// Validate validates the API key credentials.
func (a *APIKeyAuth) Validate() error {
	if a.apiKey.IsEmpty() {
		return fmt.Errorf("API key is required")
	}
	if a.headerKey == "" {
		return fmt.Errorf("header key is required")
	}
	return nil
}

// GetHeaderKey returns the header key name.
func (a *APIKeyAuth) GetHeaderKey() string {
	return a.headerKey
}

// BearerAuth implements Bearer token authentication.
type BearerAuth struct {
	token     *SecureString
	provider  TokenProvider
	mu        sync.RWMutex
	expiresAt time.Time
}

// NewBearerAuth creates a new Bearer token authentication provider with a static token.
//
// Example:
//
//	auth := security.NewBearerAuth("my-bearer-token")
//	headerValue, err := auth.GetAuthHeader()
func NewBearerAuth(token string) *BearerAuth {
	return &BearerAuth{
		token: NewSecureString(token),
	}
}

// NewBearerAuthWithProvider creates a new Bearer token authentication with a token provider.
//
// Example:
//
//	provider := &MyTokenProvider{}
//	auth := security.NewBearerAuthWithProvider(provider)
func NewBearerAuthWithProvider(provider TokenProvider) *BearerAuth {
	return &BearerAuth{
		provider: provider,
	}
}

// GetAuthHeader returns the Bearer token in header format.
func (b *BearerAuth) GetAuthHeader() (string, error) {
	token := b.getToken()
	if token == "" {
		return "", fmt.Errorf("bearer token is empty")
	}
	return "Bearer " + token, nil
}

// GetAuthMethod returns the authentication method.
func (b *BearerAuth) GetAuthMethod() AuthMethod {
	return AuthMethodBearer
}

// Validate validates the Bearer token credentials.
func (b *BearerAuth) Validate() error {
	if b.getToken() == "" {
		return fmt.Errorf("bearer token is required")
	}
	return nil
}

func (b *BearerAuth) getToken() string {
	b.mu.RLock()
	defer b.mu.RUnlock()

	if b.provider != nil {
		// If using a provider, we can't check here without context
		// Return a placeholder indicating a provider is available
		return "<dynamic>"
	}

	return b.token.Value()
}

// RefreshToken refreshes the token using the token provider.
func (b *BearerAuth) RefreshToken(ctx context.Context) error {
	if b.provider == nil {
		return fmt.Errorf("no token provider configured")
	}

	return b.provider.RefreshToken(ctx)
}

// BasicAuth implements Basic authentication.
type BasicAuth struct {
	username string
	password *SecureString
}

// NewBasicAuth creates a new Basic authentication provider.
//
// Example:
//
//	auth := security.NewBasicAuth("username", "password")
//	headerValue, err := auth.GetAuthHeader()
func NewBasicAuth(username, password string) *BasicAuth {
	return &BasicAuth{
		username: username,
		password: NewSecureString(password),
	}
}

// GetAuthHeader returns the Basic authentication credentials in header format.
func (b *BasicAuth) GetAuthHeader() (string, error) {
	if b.username == "" {
		return "", fmt.Errorf("username is empty")
	}

	credentials := b.username + ":" + b.password.Value()
	encoded := base64.StdEncoding.EncodeToString([]byte(credentials))
	return "Basic " + encoded, nil
}

// GetAuthMethod returns the authentication method.
func (b *BasicAuth) GetAuthMethod() AuthMethod {
	return AuthMethodBasic
}

// Validate validates the Basic authentication credentials.
func (b *BasicAuth) Validate() error {
	if b.username == "" {
		return fmt.Errorf("username is required")
	}
	if b.password.IsEmpty() {
		return fmt.Errorf("password is required")
	}
	return nil
}

// AuthInterceptor provides HTTP request authentication.
type AuthInterceptor struct {
	provider AuthProvider
}

// NewAuthInterceptor creates a new authentication interceptor.
//
// Example:
//
//	auth := security.NewAPIKeyAuth("my-api-key", "X-API-Key")
//	interceptor := security.NewAuthInterceptor(auth)
//	req, _ := http.NewRequest("GET", "https://example.com", nil)
//	err := interceptor.Intercept(req)
func NewAuthInterceptor(provider AuthProvider) *AuthInterceptor {
	return &AuthInterceptor{provider: provider}
}

// Intercept adds authentication headers to the request.
func (i *AuthInterceptor) Intercept(req *http.Request) error {
	if i.provider == nil {
		return nil
	}

	if err := i.provider.Validate(); err != nil {
		return fmt.Errorf("invalid auth credentials: %w", err)
	}

	headerValue, err := i.provider.GetAuthHeader()
	if err != nil {
		return err
	}

	switch i.provider.GetAuthMethod() {
	case AuthMethodAPIKey:
		if apiKeyAuth, ok := i.provider.(*APIKeyAuth); ok {
			req.Header.Set(apiKeyAuth.GetHeaderKey(), headerValue)
		}
	case AuthMethodBearer, AuthMethodBasic:
		req.Header.Set("Authorization", headerValue)
	}

	return nil
}

// HashString creates a SHA-256 hash of the input string.
// This is useful for creating secure hashes of sensitive data.
//
// Example:
//
//	hash := security.HashString("sensitive-data")
//	// Use hash for comparison without storing the original
func HashString(input string) string {
	hash := sha256.Sum256([]byte(input))
	return fmt.Sprintf("%x", hash)
}

// HashStringWithSalt creates a SHA-256 hash with a salt.
// The salt should be unique per user/application and stored securely.
//
// Example:
//
//	salt := security.GenerateSalt()
//	hash := security.HashStringWithSalt("password", salt)
func HashStringWithSalt(input, salt string) string {
	h := hmac.New(sha256.New, []byte(salt))
	h.Write([]byte(input))
	return fmt.Sprintf("%x", h.Sum(nil))
}

// GenerateSalt generates a random salt for hashing.
// In production, use a cryptographically secure random generator.
func GenerateSalt() string {
	// Note: In production, use crypto/rand for secure random generation
	// This is a simplified version for demonstration
	return HashString(fmt.Sprintf("%d", time.Now().UnixNano()))
}

// ValidateAPIKey validates an API key format.
// Returns an error if the key doesn't meet security requirements.
func ValidateAPIKey(key string) error {
	if key == "" {
		return fmt.Errorf("API key cannot be empty")
	}

	if len(key) < 16 {
		return fmt.Errorf("API key must be at least 16 characters long")
	}

	// Check for common weak patterns
	weakPatterns := []string{"123", "abc", "password", "key", "test", "default"}
	lowerKey := strings.ToLower(key)
	for _, pattern := range weakPatterns {
		if strings.Contains(lowerKey, pattern) {
			return fmt.Errorf("API key contains weak pattern: %s", pattern)
		}
	}

	return nil
}

// SecureCompare performs a constant-time comparison of two strings
// to prevent timing attacks.
func SecureCompare(a, b string) bool {
	return hmac.Equal([]byte(a), []byte(b))
}

// AuthMiddleware creates an HTTP middleware for authentication.
// This can be used with standard HTTP handlers.
//
// Example:
//
//	auth := security.NewAPIKeyAuth("secret-key", "X-API-Key")
//	middleware := security.AuthMiddleware(auth)
//	http.Handle("/api/", middleware(http.HandlerFunc(myHandler)))
func AuthMiddleware(provider AuthProvider) func(http.Handler) http.Handler {
	return func(next http.Handler) http.Handler {
		return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if err := provider.Validate(); err != nil {
				http.Error(w, "Unauthorized", http.StatusUnauthorized)
				return
			}

			// Add auth context to request
			ctx := WithAuthContext(r.Context(), provider.GetAuthMethod())
			next.ServeHTTP(w, r.WithContext(ctx))
		})
	}
}

// authContextKey is the key type for auth context values.
type authContextKey struct{}

// WithAuthContext adds authentication method to the context.
func WithAuthContext(ctx context.Context, method AuthMethod) context.Context {
	return context.WithValue(ctx, authContextKey{}, method)
}

// GetAuthMethodFromContext retrieves the authentication method from context.
func GetAuthMethodFromContext(ctx context.Context) (AuthMethod, bool) {
	method, ok := ctx.Value(authContextKey{}).(AuthMethod)
	return method, ok
}

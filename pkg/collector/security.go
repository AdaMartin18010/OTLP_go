package collector

import (
	"context"
	"crypto/tls"
	"crypto/x509"
	"fmt"
	"net/http"
	"os"
	"sync"
	"time"

	"go.uber.org/zap"
)

// TLSConfig holds complete TLS configuration.
type TLSConfig struct {
	CertFile       string        `yaml:"cert_file,omitempty"`
	KeyFile        string        `yaml:"key_file,omitempty"`
	CAFile         string        `yaml:"ca_file,omitempty"`
	ClientCAFile   string        `yaml:"client_ca_file,omitempty"`
	ReloadInterval time.Duration `yaml:"reload_interval,omitempty"`
	Insecure       bool          `yaml:"insecure,omitempty"`
	ServerName     string        `yaml:"server_name,omitempty"`
}

// Validate checks that the TLS config is well-formed.
func (t *TLSConfig) Validate() error {
	if t.Insecure {
		return nil
	}
	if t.CertFile != "" && t.KeyFile == "" {
		return fmt.Errorf("tls key_file is required when cert_file is set")
	}
	if t.KeyFile != "" && t.CertFile == "" {
		return fmt.Errorf("tls cert_file is required when key_file is set")
	}
	return nil
}

// LoadTLSConfig loads the TLS configuration.
func (t *TLSConfig) LoadTLSConfig() (*tls.Config, error) {
	if t.Insecure {
		return &tls.Config{InsecureSkipVerify: true}, nil
	}

	cfg := &tls.Config{
		ServerName: t.ServerName,
	}

	if t.CAFile != "" {
		caPEM, err := os.ReadFile(t.CAFile)
		if err != nil {
			return nil, fmt.Errorf("failed to read CA file %q: %w", t.CAFile, err)
		}
		pool := x509.NewCertPool()
		if !pool.AppendCertsFromPEM(caPEM) {
			return nil, fmt.Errorf("failed to parse CA certificate from %q", t.CAFile)
		}
		cfg.RootCAs = pool
	}

	if t.ClientCAFile != "" {
		clientCAPEM, err := os.ReadFile(t.ClientCAFile)
		if err != nil {
			return nil, fmt.Errorf("failed to read client CA file %q: %w", t.ClientCAFile, err)
		}
		pool := x509.NewCertPool()
		if !pool.AppendCertsFromPEM(clientCAPEM) {
			return nil, fmt.Errorf("failed to parse client CA certificate from %q", t.ClientCAFile)
		}
		cfg.ClientCAs = pool
		cfg.ClientAuth = tls.RequireAndVerifyClientCert
	}

	if t.CertFile != "" && t.KeyFile != "" {
		cert, err := tls.LoadX509KeyPair(t.CertFile, t.KeyFile)
		if err != nil {
			return nil, fmt.Errorf("failed to load TLS certificate from %q/%q: %w", t.CertFile, t.KeyFile, err)
		}
		cfg.Certificates = []tls.Certificate{cert}
	}

	return cfg, nil
}

// AutoReloadingTLSConfig reloads certificates at the configured interval.
type AutoReloadingTLSConfig struct {
	TLSConfig
	mu     sync.RWMutex
	active *tls.Config
	ticker *time.Ticker
	done   chan struct{}
}

// NewAutoReloadingTLSConfig creates a TLS config that supports auto-reload.
func NewAutoReloadingTLSConfig(cfg TLSConfig) (*AutoReloadingTLSConfig, error) {
	if cfg.ReloadInterval <= 0 {
		cfg.ReloadInterval = 1 * time.Hour
	}
	arc := &AutoReloadingTLSConfig{
		TLSConfig: cfg,
		done:      make(chan struct{}),
	}
	if err := arc.reload(); err != nil {
		return nil, err
	}
	if cfg.ReloadInterval > 0 {
		arc.ticker = time.NewTicker(cfg.ReloadInterval)
		go arc.loop()
	}
	return arc, nil
}

func (arc *AutoReloadingTLSConfig) loop() {
	for {
		select {
		case <-arc.ticker.C:
			_ = arc.reload()
		case <-arc.done:
			return
		}
	}
}

func (arc *AutoReloadingTLSConfig) reload() error {
	cfg, err := arc.TLSConfig.LoadTLSConfig()
	if err != nil {
		return err
	}
	arc.mu.Lock()
	arc.active = cfg
	arc.mu.Unlock()
	return nil
}

// GetConfig returns the current TLS configuration.
func (arc *AutoReloadingTLSConfig) GetConfig() *tls.Config {
	arc.mu.RLock()
	defer arc.mu.RUnlock()
	return arc.active.Clone()
}

// Stop stops the auto-reload goroutine.
func (arc *AutoReloadingTLSConfig) Stop() {
	close(arc.done)
	if arc.ticker != nil {
		arc.ticker.Stop()
	}
}

// oidcAuthExtension validates OpenID Connect tokens.
type oidcAuthExtension struct {
	id       ComponentID
	logger   *zap.Logger
	issuer   string
	audience string
	client   *http.Client
}

// OIDCAuthConfig configures the OIDC authentication extension.
type OIDCAuthConfig struct {
	IssuerURL string `yaml:"issuer_url"`
	Audience  string `yaml:"audience"`
}

// NewOIDCAuthExtension creates an OIDC token validation extension.
func NewOIDCAuthExtension(set CreateSettings, cfg OIDCAuthConfig) (Extension, error) {
	return &oidcAuthExtension{
		id:       set.ID,
		logger:   set.Logger,
		issuer:   cfg.IssuerURL,
		audience: cfg.Audience,
		client:   &http.Client{Timeout: 10 * time.Second},
	}, nil
}

func (e *oidcAuthExtension) Start(ctx context.Context) error {
	e.logger.Info("OIDC auth extension started", zap.String("issuer", e.issuer))
	return nil
}

func (e *oidcAuthExtension) Shutdown(ctx context.Context) error {
	e.logger.Info("OIDC auth extension shutdown")
	return nil
}

// ValidateToken performs a simplified token validation.
// In production, this would verify the JWT signature against the issuer's JWKS.
func (e *oidcAuthExtension) ValidateToken(token string) error {
	if token == "" {
		return fmt.Errorf("token is empty")
	}
	// Simplified validation: ensure token is non-empty and has three parts (header.payload.signature).
	parts := splitToken(token)
	if len(parts) != 3 {
		return fmt.Errorf("invalid token format")
	}
	return nil
}

func splitToken(token string) []string {
	var parts []string
	start := 0
	for i := 0; i < len(token); i++ {
		if token[i] == '.' {
			parts = append(parts, token[start:i])
			start = i + 1
		}
	}
	parts = append(parts, token[start:])
	return parts
}

// oauth2ClientExtension provides OAuth2 client authentication.
type oauth2ClientExtension struct {
	id           ComponentID
	logger       *zap.Logger
	clientID     string
	clientSecret string
	tokenURL     string
	scopes       []string
	mu           sync.RWMutex
	accessToken  string
	expiresAt    time.Time
	client       *http.Client
}

// OAuth2ClientConfig configures the OAuth2 client extension.
type OAuth2ClientConfig struct {
	ClientID     string   `yaml:"client_id"`
	ClientSecret string   `yaml:"client_secret"`
	TokenURL     string   `yaml:"token_url"`
	Scopes       []string `yaml:"scopes,omitempty"`
}

// NewOAuth2ClientExtension creates an OAuth2 client authentication extension.
func NewOAuth2ClientExtension(set CreateSettings, cfg OAuth2ClientConfig) (Extension, error) {
	return &oauth2ClientExtension{
		id:           set.ID,
		logger:       set.Logger,
		clientID:     cfg.ClientID,
		clientSecret: cfg.ClientSecret,
		tokenURL:     cfg.TokenURL,
		scopes:       cfg.Scopes,
		client:       &http.Client{Timeout: 10 * time.Second},
	}, nil
}

func (e *oauth2ClientExtension) Start(ctx context.Context) error {
	e.logger.Info("OAuth2 client extension started", zap.String("token_url", e.tokenURL))
	return nil
}

func (e *oauth2ClientExtension) Shutdown(ctx context.Context) error {
	e.logger.Info("OAuth2 client extension shutdown")
	return nil
}

// GetAccessToken returns the current access token, refreshing if necessary.
// This is a simplified implementation; production code would implement the full OAuth2 flow.
func (e *oauth2ClientExtension) GetAccessToken() string {
	e.mu.RLock()
	token := e.accessToken
	expiresAt := e.expiresAt
	e.mu.RUnlock()

	if token != "" && time.Now().Before(expiresAt) {
		return token
	}

	// In a real implementation, perform a token refresh here.
	// For this framework, we return the existing token or empty.
	return token
}

// SetAccessToken allows setting a token manually (e.g., after external refresh).
func (e *oauth2ClientExtension) SetAccessToken(token string, expiresIn time.Duration) {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.accessToken = token
	if expiresIn > 0 {
		e.expiresAt = time.Now().Add(expiresIn)
	} else {
		e.expiresAt = time.Now().Add(1 * time.Hour)
	}
}

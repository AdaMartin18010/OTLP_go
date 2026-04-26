package collector

import (
	"context"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"time"

	"gopkg.in/yaml.v3"
)

// ConfigProvider retrieves collector configuration from various sources.
type ConfigProvider interface {
	// Retrieve fetches the raw configuration bytes.
	Retrieve(ctx context.Context) ([]byte, error)
	// Scheme returns the URI scheme this provider handles.
	Scheme() string
}

// MergeStrategy defines how multiple configurations are combined.
type MergeStrategy int

const (
	// MergeStrategyOverlay overlays later configs onto earlier ones (deep merge).
	MergeStrategyOverlay MergeStrategy = iota
	// MergeStrategyReplace replaces the entire config with the last one.
	MergeStrategyReplace
)

// MultiConfigProvider merges configurations from multiple providers.
type MultiConfigProvider struct {
	providers []ConfigProvider
	strategy  MergeStrategy
}

// NewMultiConfigProvider creates a provider that merges multiple sources.
func NewMultiConfigProvider(strategy MergeStrategy, providers ...ConfigProvider) *MultiConfigProvider {
	return &MultiConfigProvider{
		providers: providers,
		strategy:  strategy,
	}
}

// Retrieve fetches and merges configurations from all providers.
func (m *MultiConfigProvider) Retrieve(ctx context.Context) ([]byte, error) {
	if len(m.providers) == 0 {
		return nil, fmt.Errorf("no config providers configured")
	}

	var merged map[string]interface{}
	for i, p := range m.providers {
		data, err := p.Retrieve(ctx)
		if err != nil {
			return nil, fmt.Errorf("provider %d (%s): %w", i, p.Scheme(), err)
		}

		var current map[string]interface{}
		if err := yaml.Unmarshal(data, &current); err != nil {
			return nil, fmt.Errorf("provider %d (%s): failed to parse YAML: %w", i, p.Scheme(), err)
		}

		if i == 0 || m.strategy == MergeStrategyReplace {
			merged = current
		} else {
			merged = deepMerge(merged, current)
		}
	}

	out, err := yaml.Marshal(merged)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal merged config: %w", err)
	}
	return out, nil
}

// Scheme returns the combined scheme identifier.
func (m *MultiConfigProvider) Scheme() string {
	schemes := make([]string, len(m.providers))
	for i, p := range m.providers {
		schemes[i] = p.Scheme()
	}
	return "multi:" + strings.Join(schemes, ",")
}

func deepMerge(base, overlay map[string]interface{}) map[string]interface{} {
	result := make(map[string]interface{}, len(base))
	for k, v := range base {
		result[k] = v
	}
	for k, v := range overlay {
		if existing, ok := result[k]; ok {
			if existingMap, ok1 := existing.(map[string]interface{}); ok1 {
				if vMap, ok2 := v.(map[string]interface{}); ok2 {
					result[k] = deepMerge(existingMap, vMap)
					continue
				}
			}
		}
		result[k] = v
	}
	return result
}

// FileProvider reads configuration from a local file.
type FileProvider struct {
	Path string
}

// NewFileProvider creates a file-based config provider.
func NewFileProvider(path string) *FileProvider {
	return &FileProvider{Path: path}
}

func (p *FileProvider) Retrieve(ctx context.Context) ([]byte, error) {
	path := filepath.Clean(p.Path)
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("failed to read file %q: %w", path, err)
	}
	return data, nil
}

func (p *FileProvider) Scheme() string { return "file" }

// EnvProvider reads configuration from an environment variable.
type EnvProvider struct {
	VarName string
}

// NewEnvProvider creates an environment-variable-based config provider.
func NewEnvProvider(varName string) *EnvProvider {
	return &EnvProvider{VarName: varName}
}

func (p *EnvProvider) Retrieve(ctx context.Context) ([]byte, error) {
	val := os.Getenv(p.VarName)
	if val == "" {
		return nil, fmt.Errorf("environment variable %q is not set or empty", p.VarName)
	}
	return []byte(val), nil
}

func (p *EnvProvider) Scheme() string { return "env" }

// HTTPProvider fetches configuration over HTTP.
type HTTPProvider struct {
	URL        string
	HTTPClient *http.Client
}

// NewHTTPProvider creates an HTTP-based config provider.
func NewHTTPProvider(rawURL string) (*HTTPProvider, error) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, fmt.Errorf("invalid URL %q: %w", rawURL, err)
	}
	if u.Scheme != "http" {
		return nil, fmt.Errorf("HTTPProvider requires http scheme, got %q", u.Scheme)
	}
	return &HTTPProvider{
		URL:        rawURL,
		HTTPClient: &http.Client{Timeout: 30 * time.Second},
	}, nil
}

func (p *HTTPProvider) Retrieve(ctx context.Context) ([]byte, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, p.URL, nil)
	if err != nil {
		return nil, err
	}
	resp, err := p.HTTPClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch config from %q: %w", p.URL, err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("config endpoint %q returned status %d", p.URL, resp.StatusCode)
	}

	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response from %q: %w", p.URL, err)
	}
	return data, nil
}

func (p *HTTPProvider) Scheme() string { return "http" }

// HTTPSProvider fetches configuration over HTTPS.
type HTTPSProvider struct {
	URL        string
	HTTPClient *http.Client
}

// NewHTTPSProvider creates an HTTPS-based config provider.
func NewHTTPSProvider(rawURL string) (*HTTPSProvider, error) {
	u, err := url.Parse(rawURL)
	if err != nil {
		return nil, fmt.Errorf("invalid URL %q: %w", rawURL, err)
	}
	if u.Scheme != "https" {
		return nil, fmt.Errorf("HTTPSProvider requires https scheme, got %q", u.Scheme)
	}
	return &HTTPSProvider{
		URL:        rawURL,
		HTTPClient: &http.Client{Timeout: 30 * time.Second},
	}, nil
}

func (p *HTTPSProvider) Retrieve(ctx context.Context) ([]byte, error) {
	req, err := http.NewRequestWithContext(ctx, http.MethodGet, p.URL, nil)
	if err != nil {
		return nil, err
	}
	resp, err := p.HTTPClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch config from %q: %w", p.URL, err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("config endpoint %q returned status %d", p.URL, resp.StatusCode)
	}

	data, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response from %q: %w", p.URL, err)
	}
	return data, nil
}

func (p *HTTPSProvider) Scheme() string { return "https" }

// ParseProviderURI creates the appropriate ConfigProvider from a URI string.
func ParseProviderURI(uri string) (ConfigProvider, error) {
	u, err := url.Parse(uri)
	if err != nil {
		return nil, fmt.Errorf("invalid provider URI %q: %w", uri, err)
	}

	switch u.Scheme {
	case "file":
		return NewFileProvider(u.Path), nil
	case "env":
		// env://ENV_VAR_NAME
		varName := u.Host
		if varName == "" {
			varName = u.Path
		}
		varName = strings.TrimPrefix(varName, "/")
		return NewEnvProvider(varName), nil
	case "http":
		return NewHTTPProvider(uri)
	case "https":
		return NewHTTPSProvider(uri)
	default:
		return nil, fmt.Errorf("unsupported provider scheme %q", u.Scheme)
	}
}

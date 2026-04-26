package collector

import (
	"context"
	"fmt"
	"net/http"
	"net/http/pprof"
	"sync/atomic"

	"go.uber.org/zap"
)

// Extension is a component that provides capabilities to the collector
// without directly participating in data pipelines.
type Extension interface {
	Component
}

// ExtensionFactory creates Extension instances.
type ExtensionFactory interface {
	Factory
	CreateExtension(ctx context.Context, set CreateSettings, cfg interface{}) (Extension, error)
}

// healthCheckExtension provides HTTP health endpoints.
type healthCheckExtension struct {
	id       ComponentID
	logger   *zap.Logger
	started  atomic.Bool
	server   *http.Server
	addr     string
	ready    atomic.Bool
}

// HealthCheckConfig configures the health check extension.
type HealthCheckConfig struct {
	Endpoint string `yaml:"endpoint,omitempty"`
}

// NewHealthCheckExtension creates a new health check extension.
func NewHealthCheckExtension(set CreateSettings, cfg HealthCheckConfig) (Extension, error) {
	if cfg.Endpoint == "" {
		cfg.Endpoint = ":13133"
	}
	return &healthCheckExtension{
		id:     set.ID,
		logger: set.Logger,
		addr:   cfg.Endpoint,
	}, nil
}

func (e *healthCheckExtension) Start(ctx context.Context) error {
	if !e.started.CompareAndSwap(false, true) {
		return fmt.Errorf("extension %q already started", e.id.String())
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/health", e.handleHealth)
	mux.HandleFunc("/health/ready", e.handleReady)
	mux.HandleFunc("/health/live", e.handleLive)

	e.server = &http.Server{
		Addr:    e.addr,
		Handler: mux,
	}
	e.ready.Store(true)

	e.logger.Info("health check extension starting", zap.String("endpoint", e.addr))
	go func() {
		if err := e.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			e.logger.Error("health check server error", zap.Error(err))
		}
	}()
	return nil
}

func (e *healthCheckExtension) Shutdown(ctx context.Context) error {
	if !e.started.CompareAndSwap(true, false) {
		return nil
	}
	e.ready.Store(false)
	if e.server != nil {
		return e.server.Shutdown(ctx)
	}
	return nil
}

func (e *healthCheckExtension) handleHealth(w http.ResponseWriter, r *http.Request) {
	if e.ready.Load() {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte(`{"status":"healthy"}`))
	} else {
		w.WriteHeader(http.StatusServiceUnavailable)
		_, _ = w.Write([]byte(`{"status":"unhealthy"}`))
	}
}

func (e *healthCheckExtension) handleReady(w http.ResponseWriter, r *http.Request) {
	if e.ready.Load() {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte(`{"ready":true}`))
	} else {
		w.WriteHeader(http.StatusServiceUnavailable)
		_, _ = w.Write([]byte(`{"ready":false}`))
	}
}

func (e *healthCheckExtension) handleLive(w http.ResponseWriter, r *http.Request) {
	// Liveness is based on whether the extension is started.
	if e.started.Load() {
		w.WriteHeader(http.StatusOK)
		_, _ = w.Write([]byte(`{"live":true}`))
	} else {
		w.WriteHeader(http.StatusServiceUnavailable)
		_, _ = w.Write([]byte(`{"live":false}`))
	}
}

// SetReady allows external control of the ready state.
func (e *healthCheckExtension) SetReady(ready bool) {
	e.ready.Store(ready)
}

// pprofExtension integrates Go pprof HTTP endpoints.
type pprofExtension struct {
	id      ComponentID
	logger  *zap.Logger
	started atomic.Bool
	server  *http.Server
	addr    string
}

// PprofConfig configures the pprof extension.
type PprofConfig struct {
	Endpoint string `yaml:"endpoint,omitempty"`
}

// NewPprofExtension creates a new pprof extension.
func NewPprofExtension(set CreateSettings, cfg PprofConfig) (Extension, error) {
	if cfg.Endpoint == "" {
		cfg.Endpoint = ":1777"
	}
	return &pprofExtension{
		id:     set.ID,
		logger: set.Logger,
		addr:   cfg.Endpoint,
	}, nil
}

func (e *pprofExtension) Start(ctx context.Context) error {
	if !e.started.CompareAndSwap(false, true) {
		return fmt.Errorf("extension %q already started", e.id.String())
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/debug/pprof/", pprof.Index)
	mux.HandleFunc("/debug/pprof/cmdline", pprof.Cmdline)
	mux.HandleFunc("/debug/pprof/profile", pprof.Profile)
	mux.HandleFunc("/debug/pprof/symbol", pprof.Symbol)
	mux.HandleFunc("/debug/pprof/trace", pprof.Trace)

	e.server = &http.Server{
		Addr:    e.addr,
		Handler: mux,
	}

	e.logger.Info("pprof extension starting", zap.String("endpoint", e.addr))
	go func() {
		if err := e.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			e.logger.Error("pprof server error", zap.Error(err))
		}
	}()
	return nil
}

func (e *pprofExtension) Shutdown(ctx context.Context) error {
	if !e.started.CompareAndSwap(true, false) {
		return nil
	}
	if e.server != nil {
		return e.server.Shutdown(ctx)
	}
	return nil
}

// zpagesExtension provides zpages diagnostic pages.
type zpagesExtension struct {
	id      ComponentID
	logger  *zap.Logger
	started atomic.Bool
	server  *http.Server
	addr    string
}

// ZPagesConfig configures the zpages extension.
type ZPagesConfig struct {
	Endpoint string `yaml:"endpoint,omitempty"`
}

// NewZPagesExtension creates a new zpages extension.
func NewZPagesExtension(set CreateSettings, cfg ZPagesConfig) (Extension, error) {
	if cfg.Endpoint == "" {
		cfg.Endpoint = ":55679"
	}
	return &zpagesExtension{
		id:     set.ID,
		logger: set.Logger,
		addr:   cfg.Endpoint,
	}, nil
}

func (e *zpagesExtension) Start(ctx context.Context) error {
	if !e.started.CompareAndSwap(false, true) {
		return fmt.Errorf("extension %q already started", e.id.String())
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/debug/tracez", e.handleTracez)
	mux.HandleFunc("/debug/rpcz", e.handleRPCz)
	mux.HandleFunc("/debug/statsz", e.handleStatsz)

	e.server = &http.Server{
		Addr:    e.addr,
		Handler: mux,
	}

	e.logger.Info("zpages extension starting", zap.String("endpoint", e.addr))
	go func() {
		if err := e.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			e.logger.Error("zpages server error", zap.Error(err))
		}
	}()
	return nil
}

func (e *zpagesExtension) Shutdown(ctx context.Context) error {
	if !e.started.CompareAndSwap(true, false) {
		return nil
	}
	if e.server != nil {
		return e.server.Shutdown(ctx)
	}
	return nil
}

func (e *zpagesExtension) handleTracez(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/html")
	_, _ = w.Write([]byte("<html><head><title>Tracez</title></head><body><h1>Tracez</h1><p>Trace information will be displayed here.</p></body></html>"))
}

func (e *zpagesExtension) handleRPCz(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/html")
	_, _ = w.Write([]byte("<html><head><title>RPCz</title></head><body><h1>RPCz</h1><p>RPC statistics will be displayed here.</p></body></html>"))
}

func (e *zpagesExtension) handleStatsz(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "text/html")
	_, _ = w.Write([]byte("<html><head><title>Statsz</title></head><body><h1>Statsz</h1><p>Component statistics will be displayed here.</p></body></html>"))
}

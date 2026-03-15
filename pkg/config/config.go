// Package config provides configuration management for the OTLP Go SDK.
//
// This package supports:
//   - Environment variable configuration
//   - File-based configuration (JSON, YAML)
//   - Dynamic configuration reloading
//   - Configuration validation
//
// Example usage:
//
//	cfg, err := config.Load("config.yaml")
//	if err != nil {
//	    log.Fatal(err)
//	}
//
//	endpoint := cfg.GetString("otel.endpoint")
//	timeout := cfg.GetDuration("otel.timeout")
package config

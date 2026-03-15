// Package shutdown provides graceful shutdown utilities
// for the OTLP Go SDK.
//
// This package includes:
//   - Shutdown manager for coordinating cleanup
//   - Timeout handling
//   - Signal handling
//   - Resource cleanup ordering
//
// Example usage:
//
//	manager := shutdown.NewManager(30 * time.Second)
//	manager.Add(exporter.Shutdown)
//	manager.Add(processor.Shutdown)
//	
//	<-manager.Done()


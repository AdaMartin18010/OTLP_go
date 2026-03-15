// Package types provides shared types and interfaces
// for the OTLP Go SDK.
//
// This package defines:
//   - Core SDK interfaces
//   - Type aliases for common patterns
//   - Generic type constraints
//   - Common data structures
//
// Example usage:
//
//	type MyProcessor struct {
//	    types.ProcessorBase
//	}
//	
//	func (p *MyProcessor) Process(data types.Processable) error {
//	    // Process data...
//	}
package types


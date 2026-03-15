// Package automation provides CI/CD automation utilities for the OTLP Go SDK.
//
// This package includes tools for:
//   - GitHub Actions workflow generation
//   - Build automation
//   - Deployment pipelines
//   - Health checks and monitoring
//
// Basic usage:
//
//	automation := automation.New("my-pipeline")
//	automation.AddStep(automation.BuildStep{
//	    Name: "Build",
//	    Command: "go build ./...",
//	})
//	if err := automation.Run(); err != nil {
//	    log.Fatal(err)
//	}
package automation

